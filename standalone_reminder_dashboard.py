"""
Standalone Tamil Voice Reminder Server & Dashboard (Firebase / Twilio)
======================================================================
A single, zero-external-dependency standalone Python application containing:
  1. Embedded Firebase Client (Firestore REST API + Firebase Auth)
     - Reads patient list from Firebase
     - Writes reminders ONLY to an isolated collection ('standalone_reminders')
     - Read-only on all parent collections ('patients', 'visits', 'prescriptions')
     - Graceful fallback cache if Firestore API is not enabled in Firebase project
  2. Twilio Voice REST client with Trial Account compliance (To, From, Url only)
  3. Built-in TwiML endpoint serving Tamil Google Text-to-Speech
  4. Embedded HTML5/Tailwind/Lucide web dashboard with real-time sync
  5. Built-in auto-tunneling via cloudflared for public TwiML delivery

Run with:
    python standalone_reminder_dashboard.py
Then open:
    http://localhost:8050
"""

import base64
import http.server
import json
import os
import re
import shutil
import subprocess
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import xml.sax.saxutils

# ===========================================================================
# 1. CONFIGURATION & CREDENTIALS
# ===========================================================================
# Twilio Voice credentials (reads from environment variables or .env file)
def _load_env_file():
    env_paths = [
        os.path.join(os.path.dirname(os.path.abspath(__file__)), ".env"),
        os.path.join(os.path.dirname(os.path.abspath(__file__)), "backend", ".env"),
    ]
    for p in env_paths:
        if os.path.exists(p):
            try:
                with open(p, "r", encoding="utf-8") as f:
                    for line in f:
                        line = line.strip()
                        if line and not line.startswith("#") and "=" in line:
                            k, v = line.split("=", 1)
                            k, v = k.strip(), v.strip().strip("'").strip('"')
                            if k and k not in os.environ:
                                os.environ[k] = v
            except Exception:
                pass

_load_env_file()

TWILIO_ACCOUNT_SID = os.getenv("TWILIO_ACCOUNT_SID", "")
TWILIO_AUTH_TOKEN = os.getenv("TWILIO_AUTH_TOKEN", "")
TWILIO_FROM_NUMBER = os.getenv("TWILIO_FROM_NUMBER", "+17372508034")
DEFAULT_TO_NUMBER = os.getenv("DEFAULT_TO_NUMBER", "+919994577702")
DEFAULT_TAMIL_VOICE = os.getenv("TWILIO_TAMIL_VOICE", "Google.ta-IN-Standard-A")
PORT = int(os.getenv("PORT", "8050"))

# Firebase credentials
FIREBASE_API_KEY = os.getenv("FIREBASE_API_KEY", "")
FIREBASE_PROJECT_ID = os.getenv("FIREBASE_PROJECT_ID", "selfehack")
# Isolated collection name so parent collections ('patients', 'visits', etc.) remain 100% untouched
FIREBASE_REMINDERS_COLLECTION = "standalone_reminders"

# Dedicated non-privileged Firebase Auth sync user
FIREBASE_SYNC_EMAIL = "standalone-sync@ruralcare.local"
FIREBASE_SYNC_PASS = "RuralCareSync2026!"

# Global state
PUBLIC_TUNNEL_URL = os.getenv("PUBLIC_TUNNEL_URL", "").rstrip("/")
TUNNEL_LOCK = threading.Lock()

# In-memory storage cache (replaces SQLite completely)
_MEM_CACHE = {
    "reminders": [],
    "firebase_token": None,
    "token_expires_at": 0,
    "firebase_status": "initializing",
    "firebase_last_error": None
}
_MEM_LOCK = threading.Lock()

# Pre-seeded fallback patients matching parent app schema (read-only reference)
DEFAULT_PATIENTS = [
    {
        "id": "PAT-1001",
        "name": "Lakshmi Devi",
        "phone": "+919994577702",
        "village": "Pollachi North",
        "condition": "Hypertension"
    },
    {
        "id": "PAT-1002",
        "name": "Muruganandam S.",
        "phone": "+919842210002",
        "village": "Negamam",
        "condition": "Type 2 Diabetes"
    },
    {
        "id": "PAT-1003",
        "name": "Kaviyarasi R.",
        "phone": "+919842210003",
        "village": "Anaimalai",
        "condition": "Antenatal Care"
    },
    {
        "id": "PAT-1004",
        "name": "Karthik V.",
        "phone": "+919842210004",
        "village": "Kinathukadavu",
        "condition": "General OPD"
    }
]

# ===========================================================================
# 2. FIREBASE REST CLIENT (NON-DESTRUCTIVE & ISOLATED)
# ===========================================================================
def firebase_get_id_token() -> str:
    """Authenticates with Firebase Identity Toolkit to get a scoped ID Token."""
    global _MEM_CACHE
    now = time.time()
    with _MEM_LOCK:
        if _MEM_CACHE["firebase_token"] and now < _MEM_CACHE["token_expires_at"]:
            return _MEM_CACHE["firebase_token"]

    login_url = f"https://identitytoolkit.googleapis.com/v1/accounts:signInWithPassword?key={FIREBASE_API_KEY}"
    payload = json.dumps({
        "email": FIREBASE_SYNC_EMAIL,
        "password": FIREBASE_SYNC_PASS,
        "returnSecureToken": True
    }).encode("utf-8")

    req = urllib.request.Request(login_url, data=payload, headers={"Content-Type": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=10) as resp:
            data = json.loads(resp.read().decode("utf-8"))
            token = data.get("idToken")
            expires_in = int(data.get("expiresIn", 3600))
            with _MEM_LOCK:
                _MEM_CACHE["firebase_token"] = token
                _MEM_CACHE["token_expires_at"] = now + expires_in - 120
                _MEM_CACHE["firebase_status"] = "authenticated"
            return token
    except urllib.error.HTTPError as e:
        err_msg = e.read().decode("utf-8")
        with _MEM_LOCK:
            _MEM_CACHE["firebase_status"] = "auth_failed"
            _MEM_CACHE["firebase_last_error"] = f"Auth error ({e.code}): {err_msg}"
        return ""
    except Exception as e:
        with _MEM_LOCK:
            _MEM_CACHE["firebase_status"] = "offline"
            _MEM_CACHE["firebase_last_error"] = str(e)
        return ""

def _firestore_value(val):
    if isinstance(val, bool):
        return {"booleanValue": val}
    elif isinstance(val, int):
        return {"integerValue": str(val)}
    elif isinstance(val, float):
        return {"doubleValue": val}
    elif isinstance(val, dict):
        return {"mapValue": {"fields": {k: _firestore_value(v) for k, v in val.items()}}}
    elif isinstance(val, list):
        return {"arrayValue": {"values": [_firestore_value(x) for x in val]}}
    elif val is None:
        return {"nullValue": None}
    return {"stringValue": str(val)}

def _firestore_unpack(fields_obj):
    out = {}
    for k, v in (fields_obj or {}).items():
        if "stringValue" in v:
            out[k] = v["stringValue"]
        elif "integerValue" in v:
            out[k] = int(v["integerValue"])
        elif "doubleValue" in v:
            out[k] = float(v["doubleValue"])
        elif "booleanValue" in v:
            out[k] = v["booleanValue"]
        elif "nullValue" in v:
            out[k] = None
        else:
            out[k] = v
    return out

def firebase_save_reminder(item: dict):
    """
    Saves reminder to memory cache, then syncs to Firestore collection 'standalone_reminders'.
    SAFETY GUARANTEE: Never writes to or modifies 'patients', 'visits', or 'prescriptions'.
    """
    with _MEM_LOCK:
        # Prepend to memory cache
        _MEM_CACHE["reminders"] = [r for r in _MEM_CACHE["reminders"] if r.get("id") != item.get("id")]
        _MEM_CACHE["reminders"].insert(0, item)

    token = firebase_get_id_token()
    if not token:
        return

    doc_id = item.get("id")
    url = f"https://firestore.googleapis.com/v1/projects/{FIREBASE_PROJECT_ID}/databases/(default)/documents/{FIREBASE_REMINDERS_COLLECTION}/{doc_id}"
    fields = {k: _firestore_value(v) for k, v in item.items()}
    body = json.dumps({"fields": fields}).encode("utf-8")

    req = urllib.request.Request(url, data=body, method="PATCH", headers={
        "Content-Type": "application/json",
        "Authorization": f"Bearer {token}"
    })
    try:
        with urllib.request.urlopen(req, timeout=8):
            with _MEM_LOCK:
                _MEM_CACHE["firebase_status"] = "synced"
                _MEM_CACHE["firebase_last_error"] = None
    except urllib.error.HTTPError as e:
        # If Firestore API is disabled in GCP Console, log gracefully and rely on memory cache
        with _MEM_LOCK:
            _MEM_CACHE["firebase_status"] = "firestore_api_disabled"
            _MEM_CACHE["firebase_last_error"] = f"HTTP {e.code}: Firestore API not enabled in Firebase Console (in-memory mode active)"
    except Exception as e:
        with _MEM_LOCK:
            _MEM_CACHE["firebase_last_error"] = str(e)

def firebase_get_reminders(limit=50):
    """
    Fetches reminders from isolated Firestore collection 'standalone_reminders',
    falling back to memory cache if network or API is disabled.
    """
    token = firebase_get_id_token()
    if token:
        url = f"https://firestore.googleapis.com/v1/projects/{FIREBASE_PROJECT_ID}/databases/(default)/documents/{FIREBASE_REMINDERS_COLLECTION}?pageSize={limit}"
        req = urllib.request.Request(url, method="GET", headers={"Authorization": f"Bearer {token}"})
        try:
            with urllib.request.urlopen(req, timeout=6) as resp:
                data = json.loads(resp.read().decode("utf-8"))
                docs = data.get("documents", [])
                items = [_firestore_unpack(d.get("fields", {})) for d in docs]
                if items:
                    with _MEM_LOCK:
                        _MEM_CACHE["reminders"] = items
                        _MEM_CACHE["firebase_status"] = "synced"
                    return items
        except Exception:
            pass

    with _MEM_LOCK:
        return list(_MEM_CACHE["reminders"])[:limit]

def firebase_read_patients_readonly():
    """
    Attempts a STRICT READ-ONLY fetch of patients from parent 'patients' collection.
    If unavailable, safely returns default reference patients without modifying anything.
    """
    token = firebase_get_id_token()
    if token:
        url = f"https://firestore.googleapis.com/v1/projects/{FIREBASE_PROJECT_ID}/databases/(default)/documents/patients?pageSize=20"
        req = urllib.request.Request(url, method="GET", headers={"Authorization": f"Bearer {token}"})
        try:
            with urllib.request.urlopen(req, timeout=5) as resp:
                data = json.loads(resp.read().decode("utf-8"))
                docs = data.get("documents", [])
                items = [_firestore_unpack(d.get("fields", {})) for d in docs]
                if items:
                    return items
        except Exception:
            pass
    return DEFAULT_PATIENTS

# ===========================================================================
# 3. CLOUDFLARED AUTO-TUNNEL
# ===========================================================================
def launch_cloudflared_tunnel(local_port):
    global PUBLIC_TUNNEL_URL
    cloudflared_bin = shutil.which("cloudflared")
    if not cloudflared_bin:
        standard_path = r"C:\Program Files (x86)\cloudflared\cloudflared.exe"
        if os.path.exists(standard_path):
            cloudflared_bin = standard_path

    if not cloudflared_bin:
        print("[Tunnel] cloudflared not found in PATH.")
        return

    def run_tunnel():
        global PUBLIC_TUNNEL_URL
        print(f"[Tunnel] Starting cloudflared tunnel on port {local_port}...")
        proc = subprocess.Popen(
            [cloudflared_bin, "tunnel", "--url", f"http://127.0.0.1:{local_port}"],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1
        )
        url_regex = re.compile(r"https://[a-zA-Z0-9\-]+\.trycloudflare\.com")
        for line in iter(proc.stdout.readline, ""):
            match = url_regex.search(line)
            if match and not PUBLIC_TUNNEL_URL:
                with TUNNEL_LOCK:
                    PUBLIC_TUNNEL_URL = match.group(0)
                print(f"[Tunnel] Public HTTPS Tunnel online: {PUBLIC_TUNNEL_URL}")

    t = threading.Thread(target=run_tunnel, daemon=True)
    t.start()

# ===========================================================================
# 4. TWILIO CALL TRIGGER (TRIAL COMPLIANT)
# ===========================================================================
def normalize_phone(phone: str) -> str:
    cleaned = re.sub(r"[\s\-()]+", "", (phone or "").strip())
    if re.fullmatch(r"\d{10}", cleaned):
        cleaned = "+91" + cleaned
    elif re.fullmatch(r"91\d{10}", cleaned):
        cleaned = "+" + cleaned
    return cleaned

def trigger_twilio_call(to_phone: str, message_ta: str, voice: str = DEFAULT_TAMIL_VOICE):
    clean_to = normalize_phone(to_phone)
    if not PUBLIC_TUNNEL_URL:
        return {
            "ok": False,
            "status": "failed",
            "message": "Public tunnel URL not ready yet. Please wait a few seconds.",
        }

    twiml_url = f"{PUBLIC_TUNNEL_URL}/twiml?{urllib.parse.urlencode({'msg': message_ta, 'voice': voice})}"
    twilio_endpoint = f"https://api.twilio.com/2010-04-01/Accounts/{TWILIO_ACCOUNT_SID}/Calls.json"
    
    # Strictly Trial Compliant: ONLY To, From, and Url
    data = urllib.parse.urlencode({
        "To": clean_to,
        "From": TWILIO_FROM_NUMBER,
        "Url": twiml_url,
    }).encode("utf-8")

    req = urllib.request.Request(twilio_endpoint, data=data, method="POST")
    auth_str = f"{TWILIO_ACCOUNT_SID}:{TWILIO_AUTH_TOKEN}"
    b64_auth = base64.b64encode(auth_str.encode("utf-8")).decode("ascii")
    req.add_header("Authorization", f"Basic {b64_auth}")
    req.add_header("Content-Type", "application/x-www-form-urlencoded")

    try:
        with urllib.request.urlopen(req, timeout=15) as resp:
            body = json.loads(resp.read().decode("utf-8"))
            return {
                "ok": True,
                "status": body.get("status", "queued"),
                "call_sid": body.get("sid"),
                "to_phone": clean_to,
                "from_phone": TWILIO_FROM_NUMBER,
                "message": f"Twilio call initiated (SID: {body.get('sid')})",
            }
    except urllib.error.HTTPError as err:
        try:
            err_body = json.loads(err.read().decode("utf-8"))
            err_msg = err_body.get("message") or str(err)
            err_code = err_body.get("code")
        except Exception:
            err_msg = str(err)
            err_code = err.code
        return {
            "ok": False,
            "status": "failed",
            "error_code": err_code,
            "error_detail": err_msg,
            "message": f"Twilio call failed: {err_msg}",
        }
    except Exception as exc:
        return {
            "ok": False,
            "status": "failed",
            "error_detail": str(exc),
            "message": f"Connection error: {exc}",
        }

def fetch_call_status(call_sid: str):
    if not call_sid or not call_sid.startswith("CA"):
        return {"status": "unknown"}
    twilio_endpoint = f"https://api.twilio.com/2010-04-01/Accounts/{TWILIO_ACCOUNT_SID}/Calls/{call_sid}.json"
    req = urllib.request.Request(twilio_endpoint, method="GET")
    auth_str = f"{TWILIO_ACCOUNT_SID}:{TWILIO_AUTH_TOKEN}"
    b64_auth = base64.b64encode(auth_str.encode("utf-8")).decode("ascii")
    req.add_header("Authorization", f"Basic {b64_auth}")
    try:
        with urllib.request.urlopen(req, timeout=10) as resp:
            return json.loads(resp.read().decode("utf-8"))
    except Exception:
        return {"status": "error"}

# ===========================================================================
# 5. HTTP SERVER & EMBEDDED DASHBOARD
# ===========================================================================
class StandaloneReminderHandler(http.server.BaseHTTPRequestHandler):
    def _send_json(self, data, code=200):
        body = json.dumps(data).encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_OPTIONS(self):
        self.send_response(200)
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.end_headers()

    def do_GET(self):
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path
        query = urllib.parse.parse_qs(parsed.query)

        # 1. TwiML Endpoint for Twilio to speak Tamil
        if path == "/twiml":
            msg = query.get("msg", ["வணக்கம், இது மருத்துவ நினைவூட்டல்."])[0]
            voice = query.get("voice", [DEFAULT_TAMIL_VOICE])[0]
            escaped = xml.sax.saxutils.escape(msg.strip())
            twiml = (
                '<?xml version="1.0" encoding="UTF-8"?>'
                '<Response>'
                '<Pause length="1"/>'
                f'<Say language="ta-IN" voice="{voice}">{escaped}</Say>'
                '</Response>'
            )
            body = twiml.encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "application/xml; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return

        # 2. System Status API
        if path == "/api/status":
            with _MEM_LOCK:
                fb_status = _MEM_CACHE["firebase_status"]
                fb_err = _MEM_CACHE["firebase_last_error"]
            self._send_json({
                "configured": bool(TWILIO_ACCOUNT_SID and TWILIO_AUTH_TOKEN and TWILIO_FROM_NUMBER),
                "account_sid_masked": TWILIO_ACCOUNT_SID[:6] + "..." + TWILIO_ACCOUNT_SID[-4:],
                "from_number": TWILIO_FROM_NUMBER,
                "default_to_number": DEFAULT_TO_NUMBER,
                "default_voice": DEFAULT_TAMIL_VOICE,
                "public_tunnel_url": PUBLIC_TUNNEL_URL or "Tunnel starting...",
                "port": PORT,
                "database_mode": "Firebase Firestore (Isolated / Zero SQL)",
                "firebase_project": FIREBASE_PROJECT_ID,
                "firebase_collection": FIREBASE_REMINDERS_COLLECTION,
                "firebase_status": fb_status,
                "firebase_note": fb_err or "Isolated collection active. Parent collections are strictly read-only."
            })
            return

        # 3. Read-only Patients API (from Firebase or default reference)
        if path == "/api/patients":
            pts = firebase_read_patients_readonly()
            self._send_json(pts)
            return

        # 4. Get Reminders History (from Firebase / Memory)
        if path == "/api/reminders":
            items = firebase_get_reminders(100)
            self._send_json(items)
            return

        # 5. Check Live Call Status
        if path.startswith("/api/call-status/"):
            sid = path.replace("/api/call-status/", "").strip()
            data = fetch_call_status(sid)
            self._send_json(data)
            return

        # 6. Embedded Single-Page Dashboard
        if path in ["/", "/index.html"]:
            html = HTML_DASHBOARD.encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(html)))
            self.end_headers()
            self.wfile.write(html)
            return

        self.send_response(404)
        self.end_headers()

    def do_POST(self):
        parsed = urllib.parse.urlparse(self.path)
        path = parsed.path

        if path == "/api/call":
            length = int(self.headers.get("Content-Length", 0))
            raw_body = self.rfile.read(length).decode("utf-8")
            try:
                data = json.loads(raw_body)
            except Exception:
                self._send_json({"ok": False, "message": "Invalid JSON"}, 400)
                return

            to_phone = data.get("to_phone") or DEFAULT_TO_NUMBER
            message_ta = data.get("message_ta", "").strip()
            patient_name = data.get("patient_name", "Patient").strip()
            voice = data.get("voice", DEFAULT_TAMIL_VOICE)

            if not message_ta:
                self._send_json({"ok": False, "message": "Tamil message cannot be empty"}, 400)
                return

            # Trigger Twilio Call
            res = trigger_twilio_call(to_phone, message_ta, voice)

            # Save strictly to isolated Firebase collection / memory
            record_id = f"REM-{int(time.time()*1000)}"
            record = {
                "id": record_id,
                "patient_name": patient_name,
                "to_phone": res.get("to_phone", to_phone),
                "message_ta": message_ta,
                "voice": voice,
                "status": res.get("status", "failed"),
                "call_sid": res.get("call_sid") or "",
                "error_detail": res.get("error_detail") or "",
                "created_at": time.strftime("%Y-%m-%d %H:%M:%S")
            }
            firebase_save_reminder(record)

            self._send_json(res)
            return

        self.send_response(404)
        self.end_headers()

# ===========================================================================
# 6. EMBEDDED DASHBOARD HTML
# ===========================================================================
HTML_DASHBOARD = r"""<!DOCTYPE html>
<html lang="ta">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>Tamil Voice Reminder Dashboard (Firebase & Twilio Standalone)</title>
  <script src="https://cdn.tailwindcss.com"></script>
  <style>
    @import url('https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700&display=swap');
    body { font-family: 'Inter', system-ui, sans-serif; }
  </style>
</head>
<body class="bg-slate-50 text-slate-800 min-h-screen">

  <!-- Header -->
  <header class="bg-white border-b border-slate-200 sticky top-0 z-20 shadow-xs">
    <div class="max-w-6xl mx-auto px-4 py-3 flex flex-wrap items-center justify-between gap-3">
      <div class="flex items-center gap-3">
        <div class="w-10 h-10 rounded-xl bg-teal-700 flex items-center justify-center text-white font-bold text-lg shadow-sm">
          📞
        </div>
        <div>
          <div class="flex items-center gap-2">
            <h1 class="text-lg font-bold text-slate-900 leading-tight">Tamil Voice Reminder Dashboard</h1>
            <span class="inline-flex items-center gap-1 rounded-full bg-amber-50 px-2 py-0.5 text-[11px] font-medium text-amber-800 border border-amber-200">
              🔥 Firebase Powered
            </span>
          </div>
          <p class="text-xs text-slate-500">Standalone Twilio Voice · Zero SQL · Parent App Safe</p>
        </div>
      </div>
      <div class="flex items-center gap-2 text-xs">
        <span id="fb-badge" class="px-2.5 py-1 rounded-full border border-slate-200 bg-slate-50 text-slate-700 font-medium">
          Firebase syncing...
        </span>
        <span id="tunnel-badge" class="px-2.5 py-1 rounded-full border border-amber-300 bg-amber-50 text-amber-800 font-medium">
          Tunnel connecting...
        </span>
        <button onclick="fetchStatus()" class="px-2.5 py-1 border border-slate-200 rounded-lg bg-slate-50 hover:bg-slate-100 font-semibold text-slate-600">
          🔄 Refresh
        </button>
      </div>
    </div>
  </header>

  <main class="max-w-6xl mx-auto px-4 py-6 space-y-6">

    <!-- Status Strip -->
    <div class="bg-white rounded-2xl border border-slate-200 p-4 shadow-xs grid grid-cols-1 sm:grid-cols-4 gap-3 text-xs">
      <div>
        <p class="text-slate-400 font-semibold uppercase">Database Engine</p>
        <p class="font-bold text-slate-800 mt-0.5">Firebase Firestore (No SQL)</p>
        <p class="text-[10px] text-slate-400">Target: standalone_reminders</p>
      </div>
      <div>
        <p class="text-slate-400 font-semibold uppercase">From Number</p>
        <p id="stat-from" class="font-mono font-bold text-slate-800 mt-0.5">+17372508034</p>
        <p class="text-[10px] text-slate-400">Twilio Trial Verified</p>
      </div>
      <div>
        <p class="text-slate-400 font-semibold uppercase">Destination Number</p>
        <p id="stat-to" class="font-mono font-bold text-emerald-700 mt-0.5">+919994577702</p>
        <p class="text-[10px] text-emerald-600">Verified Recipient</p>
      </div>
      <div>
        <p class="text-slate-400 font-semibold uppercase">Public TwiML URL</p>
        <p id="stat-tunnel" class="font-mono text-slate-700 truncate mt-0.5">Detecting...</p>
        <p class="text-[10px] text-slate-400">Cloudflare Tunnel</p>
      </div>
    </div>

    <!-- Main Workspace -->
    <div class="grid grid-cols-1 lg:grid-cols-12 gap-6">

      <!-- Left Column: Call Trigger Form -->
      <div class="lg:col-span-5 bg-white rounded-2xl border border-slate-200 p-5 shadow-sm space-y-4">
        <h2 class="text-base font-bold text-slate-900 flex items-center gap-2">
          <span>🔔</span> Place Outbound Voice Call
        </h2>

        <!-- Patient Selector from Firebase -->
        <div>
          <label class="block text-xs font-semibold text-slate-700 mb-1">Select Patient (Firebase Reference)</label>
          <select id="patient-select" onchange="onPatientSelect()" class="w-full rounded-lg border border-slate-300 p-2 text-sm bg-white focus:outline-teal-600">
            <option value="custom">Custom Recipient (+919994577702)</option>
          </select>
        </div>

        <!-- Template Selector -->
        <div>
          <label class="block text-xs font-semibold text-slate-700 mb-1">Select Tamil Template</label>
          <select id="template-select" onchange="applyTemplate()" class="w-full rounded-lg border border-slate-300 p-2 text-sm bg-white focus:outline-teal-600">
            <option value="pill">காலை மருந்து நினைவூட்டல் (Morning Pill)</option>
            <option value="phc">PHC மருத்துவமனை சந்திப்பு (Hospital Visit)</option>
            <option value="asha">ASHA பணியாளர் வருகை (BP / Sugar Check)</option>
            <option value="night">இரவு மருந்து நினைவூட்டல் (Night Pill)</option>
            <option value="custom">தனிப்பயன் செய்தி (Custom Text)</option>
          </select>
        </div>

        <div class="grid grid-cols-2 gap-3">
          <div>
            <label class="block text-xs font-semibold text-slate-700 mb-1">Recipient Name</label>
            <input type="text" id="patient-name" value="Patient" class="w-full rounded-lg border border-slate-300 p-2 text-sm focus:outline-teal-600">
          </div>
          <div>
            <label class="block text-xs font-semibold text-slate-700 mb-1">Phone Number (E.164)</label>
            <input type="text" id="to-phone" value="+919994577702" class="w-full rounded-lg border border-slate-300 p-2 text-sm font-mono focus:outline-teal-600">
          </div>
        </div>

        <div>
          <label class="block text-xs font-semibold text-slate-700 mb-1">Twilio Google Tamil Voice</label>
          <select id="voice-select" class="w-full rounded-lg border border-slate-300 p-2 text-sm bg-white focus:outline-teal-600">
            <option value="Google.ta-IN-Standard-A">Google.ta-IN-Standard-A (Female)</option>
            <option value="Google.ta-IN-Standard-B">Google.ta-IN-Standard-B (Male)</option>
            <option value="Google.ta-IN-Wavenet-A">Google.ta-IN-Wavenet-A (Natural)</option>
          </select>
        </div>

        <div>
          <div class="flex items-center justify-between mb-1">
            <label class="block text-xs font-semibold text-slate-700">Tamil Voice Text (தமிழ் உரை)</label>
            <button onclick="previewAudio()" type="button" class="text-xs text-teal-700 font-semibold hover:underline">
              🔊 Preview Audio
            </button>
          </div>
          <textarea id="message-ta" rows="4" class="w-full rounded-lg border border-slate-300 p-2.5 text-sm focus:outline-teal-600 leading-relaxed"></textarea>
        </div>

        <button id="call-btn" onclick="makeCall()" class="w-full py-2.5 px-4 rounded-xl bg-teal-700 hover:bg-teal-800 text-white font-semibold text-sm shadow-sm flex items-center justify-center gap-2 transition disabled:opacity-50">
          <span>📞</span> Call User Now (Tamil)
        </button>

        <div id="call-feedback" class="hidden p-3 rounded-xl border text-xs"></div>
      </div>

      <!-- Right Column: Call History Log (Firebase) -->
      <div class="lg:col-span-7 bg-white rounded-2xl border border-slate-200 p-5 shadow-sm space-y-3">
        <div class="flex items-center justify-between">
          <div class="flex items-center gap-2">
            <h2 class="text-base font-bold text-slate-900">Call History & Log</h2>
            <span class="text-[11px] font-semibold text-teal-700 bg-teal-50 px-2 py-0.5 rounded border border-teal-200">
              collection: standalone_reminders
            </span>
          </div>
          <button onclick="fetchReminders()" class="text-xs text-teal-700 font-semibold hover:underline">
            Refresh List
          </button>
        </div>

        <div id="history-list" class="space-y-2 max-h-[500px] overflow-y-auto pr-1">
          <p class="text-xs text-slate-400 p-4 text-center">Loading call records from Firebase...</p>
        </div>
      </div>

    </div>
  </main>

  <script>
    const TEMPLATES = {
      pill: "வணக்கம், இது RuralCare மருத்துவ நினைவூட்டல். தயவுசெய்து உணவுக்குப் பிறகு உங்கள் காலை மாத்திரையை எடுத்துக்கொள்ளவும். நன்றி.",
      phc: "வணக்கம், நாளை காலை 9 மணிக்கு ஆரம்ப சுகாதார நிலையத்தில் உங்கள் மருத்துவ பரிசோதனை உள்ளது. தயவுசெய்து தவறாமல் வரவும்.",
      asha: "வணக்கம், உங்கள் ரத்த அழுத்தம் மற்றும் சர்க்கரை அளவை பரிசோதிக்க இன்று ASHA பணியாளர் வருகை தருவார்.",
      night: "வணக்கம், இரவு உணவிற்குப் பின் உங்கள் இரவு மாத்திரையை எடுத்துக்கொள்ள மறக்காதீர்கள். நல்ல ஆரோக்கியம் பெற வாழ்த்துகள்.",
      custom: ""
    };

    let patientsCache = [];

    function applyTemplate() {
      const key = document.getElementById("template-select").value;
      if (key !== "custom") {
        document.getElementById("message-ta").value = TEMPLATES[key];
      }
    }

    function previewAudio() {
      const text = document.getElementById("message-ta").value;
      if (!text || !('speechSynthesis' in window)) return;
      window.speechSynthesis.cancel();
      const utter = new SpeechSynthesisUtterance(text);
      utter.lang = "ta-IN";
      window.speechSynthesis.speak(utter);
    }

    async function loadPatients() {
      try {
        const res = await fetch("/api/patients");
        patientsCache = await res.json();
        const sel = document.getElementById("patient-select");
        sel.innerHTML = '<option value="custom">Custom Recipient (+919994577702)</option>' +
          patientsCache.map(p => `<option value="${p.id}">${p.name} (${p.phone || '+91...'}) - ${p.village || 'Tamil Nadu'}</option>`).join("");
      } catch (err) {
        console.error(err);
      }
    }

    function onPatientSelect() {
      const val = document.getElementById("patient-select").value;
      if (val === "custom") {
        document.getElementById("patient-name").value = "Patient";
        document.getElementById("to-phone").value = "+919994577702";
      } else {
        const found = patientsCache.find(p => p.id === val);
        if (found) {
          document.getElementById("patient-name").value = found.name || "Patient";
          document.getElementById("to-phone").value = found.phone || "+919994577702";
        }
      }
    }

    async function fetchStatus() {
      try {
        const res = await fetch("/api/status");
        const data = await res.json();
        document.getElementById("stat-from").innerText = data.from_number;
        document.getElementById("stat-to").innerText = data.default_to_number;
        document.getElementById("stat-tunnel").innerText = data.public_tunnel_url;

        const fbBadge = document.getElementById("fb-badge");
        if (data.firebase_status === "synced" || data.firebase_status === "authenticated") {
          fbBadge.className = "px-2.5 py-1 rounded-full border border-emerald-300 bg-emerald-50 text-emerald-800 font-medium";
          fbBadge.innerText = "Firebase Active";
        } else {
          fbBadge.className = "px-2.5 py-1 rounded-full border border-amber-300 bg-amber-50 text-amber-800 font-medium";
          fbBadge.innerText = "Firebase Memory-Safe";
        }

        const tunBadge = document.getElementById("tunnel-badge");
        if (data.public_tunnel_url && data.public_tunnel_url.startsWith("https://")) {
          tunBadge.className = "px-2.5 py-1 rounded-full border border-emerald-300 bg-emerald-50 text-emerald-800 font-medium";
          tunBadge.innerText = "Tunnel Online";
        } else {
          tunBadge.className = "px-2.5 py-1 rounded-full border border-amber-300 bg-amber-50 text-amber-800 font-medium";
          tunBadge.innerText = "Tunnel Pending";
        }
      } catch (err) {
        console.error(err);
      }
    }

    async function fetchReminders() {
      try {
        const res = await fetch("/api/reminders");
        const list = await res.json();
        const container = document.getElementById("history-list");
        if (!list || list.length === 0) {
          container.innerHTML = '<p class="text-xs text-slate-400 p-4 text-center">No call records yet.</p>';
          return;
        }

        container.innerHTML = list.map(item => {
          const isSuccess = item.status === 'completed' || item.status === 'queued' || item.status === 'in-progress';
          const badgeClass = isSuccess 
            ? 'bg-emerald-50 text-emerald-700 border-emerald-200' 
            : 'bg-rose-50 text-rose-700 border-rose-200';
          return `
            <div class="border border-slate-200 rounded-xl p-3 bg-slate-50/70 text-xs space-y-1.5">
              <div class="flex items-center justify-between">
                <div>
                  <span class="font-bold text-slate-900">${item.patient_name || 'Patient'}</span>
                  <span class="font-mono text-slate-500 ml-2">${item.to_phone}</span>
                </div>
                <span class="px-2 py-0.5 rounded-full border text-[10px] uppercase font-bold ${badgeClass}">
                  ${item.status}
                </span>
              </div>
              <p class="text-slate-700 bg-white p-2 rounded border border-slate-200">${item.message_ta}</p>
              <div class="flex items-center justify-between text-[11px] text-slate-400 pt-1">
                <span>🕒 ${item.created_at}</span>
                ${item.call_sid ? `<span class="font-mono">SID: ${item.call_sid}</span>` : ''}
              </div>
            </div>
          `;
        }).join("");
      } catch (err) {
        console.error(err);
      }
    }

    async function makeCall() {
      const btn = document.getElementById("call-btn");
      const fb = document.getElementById("call-feedback");
      const to_phone = document.getElementById("to-phone").value.trim();
      const message_ta = document.getElementById("message-ta").value.trim();
      const patient_name = document.getElementById("patient-name").value.trim();
      const voice = document.getElementById("voice-select").value;

      if (!to_phone || !message_ta) {
        alert("Please enter both phone number and Tamil message.");
        return;
      }

      btn.disabled = true;
      btn.innerText = "Calling via Twilio...";
      fb.classList.add("hidden");

      try {
        const res = await fetch("/api/call", {
          method: "POST",
          headers: { "Content-Type": "application/json" },
          body: JSON.stringify({ to_phone, message_ta, patient_name, voice })
        });
        const data = await res.json();

        fb.classList.remove("hidden");
        if (data.ok) {
          fb.className = "p-3 rounded-xl border border-emerald-200 bg-emerald-50 text-emerald-900 text-xs";
          fb.innerHTML = `<strong>Success:</strong> ${data.message} (SID: ${data.call_sid || 'N/A'})`;
        } else {
          fb.className = "p-3 rounded-xl border border-rose-200 bg-rose-50 text-rose-900 text-xs";
          fb.innerHTML = `<strong>Failed:</strong> ${data.message}`;
        }
        fetchReminders();
      } catch (err) {
        fb.classList.remove("hidden");
        fb.className = "p-3 rounded-xl border border-rose-200 bg-rose-50 text-rose-900 text-xs";
        fb.innerHTML = `<strong>Error:</strong> ${err.message}`;
      } finally {
        btn.disabled = false;
        btn.innerHTML = "<span>📞</span> Call User Now (Tamil)";
      }
    }

    // Initialize
    applyTemplate();
    loadPatients();
    fetchStatus();
    fetchReminders();
    setInterval(fetchStatus, 6000);
    setInterval(fetchReminders, 8000);
  </script>
</body>
</html>
"""

# ===========================================================================
# 7. MAIN ENTRYPOINT
# ===========================================================================
def main():
    print("=" * 70)
    print("  Standalone Tamil Voice Reminder Server (Firebase & Twilio)")
    print("=" * 70)
    print(f" Database Mode      : Firebase Firestore (Collection: {FIREBASE_REMINDERS_COLLECTION})")
    print(f" Safety Guarantee   : Zero SQL. Parent collections are STRICTLY READ-ONLY.")
    print(f" Twilio Account SID : {TWILIO_ACCOUNT_SID[:6]}...{TWILIO_ACCOUNT_SID[-4:]}")
    print(f" From Number        : {TWILIO_FROM_NUMBER}")
    print(f" Destination Phone  : {DEFAULT_TO_NUMBER}")
    print(f" Local Port         : {PORT}")
    print("-" * 70)

    # Launch public HTTPS tunnel
    launch_cloudflared_tunnel(PORT)

    # Warm up Firebase Auth token in background
    threading.Thread(target=firebase_get_id_token, daemon=True).start()

    server = http.server.ThreadingHTTPServer(("0.0.0.0", PORT), StandaloneReminderHandler)
    print(f"[Dashboard Ready] Open in browser: http://localhost:{PORT}")
    print("=" * 70)

    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nStopping standalone server...")
        server.server_close()
        sys.exit(0)

if __name__ == "__main__":
    main()
