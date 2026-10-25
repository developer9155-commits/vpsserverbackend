"""TechBooster VPS Bot Manager - FastAPI backend.

Runs on Render. It never runs bots itself: it talks to a VPS (entered by the user) over an
SSH connection and manages bots as systemd *user* services.
All state (projects, venvs, logs) lives on the VPS, so Render restarts or
free-tier sleep lose nothing; the SSH link is re-opened lazily on demand.
"""
import base64
import hashlib
import hmac
import io
import ipaddress
import json
import os
import re
import secrets
import shlex
import socket
import tarfile
import tempfile
import threading
import time
import zipfile
from collections import defaultdict, deque
from datetime import datetime, timezone
from typing import Optional

import paramiko
from fastapi import Depends, FastAPI, File, Form, HTTPException, Query, Request, UploadFile
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import JSONResponse
from fastapi.security import HTTPAuthorizationCredentials, HTTPBearer
from pydantic import BaseModel, Field

# ----------------------------------------------------------------- config ---
API_TOKEN = os.environ.get("API_TOKEN", "")
ORIGINS = [o.strip().rstrip("/") for o in os.environ.get("FRONTEND_ORIGINS", "").split(",") if o.strip()]
MAX_UPLOAD = int(os.environ.get("MAX_UPLOAD_MB", "25")) * 1024 * 1024
MAX_UNZIPPED = int(os.environ.get("MAX_UNZIPPED_MB", "100")) * 1024 * 1024
MAX_FILES = 3000
ENABLE_DOCS = os.environ.get("ENABLE_DOCS", "true").lower() == "true"

ID_RE = re.compile(r"^[a-z0-9][a-z0-9-]{2,39}$")
NAME_RE = re.compile(r"^[\w .\-]{1,60}$")
MAIN_RE = re.compile(r"^(?!/)(?!.*\.\.)[A-Za-z0-9_][A-Za-z0-9_./\- ]{0,118}\.py$")
PATH_RE = re.compile(r"^[\w@%+=,.~ \-/]+$")
CURSOR_RE = re.compile(r"^[\w=;\-]{1,300}$")


def now_iso():
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


# ------------------------------------------------------- auth / throttling ---
bearer = HTTPBearer(auto_error=False, description="Private access token (API_TOKEN)")
_hits = defaultdict(deque)
_hits_lock = threading.Lock()


def client_ip(req: Request):
    fwd = req.headers.get("x-forwarded-for", "").split(",")[0].strip()
    return fwd or (req.client.host if req.client else "?")


def throttle(key, limit_n, window=60):
    now = time.time()
    with _hits_lock:
        q = _hits[key]
        while q and q[0] < now - window:
            q.popleft()
        if len(q) >= limit_n:
            raise HTTPException(429, "Too many requests. Slow down and retry shortly.")
        q.append(now)


def auth(req: Request, cred: Optional[HTTPAuthorizationCredentials] = Depends(bearer)):
    if len(API_TOKEN) < 24:
        raise HTTPException(503, "Backend misconfigured: API_TOKEN must be set (24+ characters).")
    ip = client_ip(req)
    ok = cred is not None and hmac.compare_digest(cred.credentials.encode(), API_TOKEN.encode())
    if not ok:
        throttle(("authfail", ip), 10)  # brute-force guard
        raise HTTPException(401, "Invalid or missing access token.")
    throttle(("all", ip), 300)


def limit(name, n):
    def dep(req: Request):
        throttle((name, client_ip(req)), n)
    return dep


# ----------------------------------------------------------- SSH to VPS ---
class VPSError(Exception):
    pass


class NotConnected(VPSError):
    pass


class VPS:
    def __init__(self):
        self.t = None
        self.params = None
        self.fp = None
        self.connected_at = None
        self.linger = None
        self.last_error = None
        self.manual_off = False
        self.lock = threading.RLock()


vps = VPS()

UNIT = """[Unit]
Description=TechBooster Telegram bot %i
After=network-online.target
StartLimitIntervalSec=120
StartLimitBurst=5

[Service]
Type=simple
WorkingDirectory=%h/techbooster/bots/%i/app
EnvironmentFile=%h/techbooster/bots/%i/env
Environment=PYTHONUNBUFFERED=1
ExecStart=%h/techbooster/bots/%i/venv/bin/python -u ${MAIN}
Restart=on-failure
RestartSec=5
NoNewPrivileges=true
PrivateTmp=true

[Install]
WantedBy=default.target
"""


def env_params():
    """Optional fallback VPS from backend env vars (users can instead send their own via /api/vps/connect)."""
    host = os.environ.get("VPS_HOST", "").strip()
    if not host:
        return None
    return {
        "host": host,
        "port": int(os.environ.get("VPS_PORT", "22") or 22),
        "username": os.environ.get("VPS_USER", "root").strip(),
        "password": os.environ.get("VPS_PASSWORD") or None,
        "key_pem": None,
        "key_pass": None,
        "fingerprint": None,
    }


def load_key(pem=None, pw=None):
    if not pem:
        b64 = os.environ.get("VPS_SSH_KEY_B64", "").strip()
        if not b64:
            return None
        try:
            pem = base64.b64decode(b64).decode()
        except Exception:
            raise VPSError("VPS_SSH_KEY_B64 is not valid base64. Use: base64 -w0 keyfile")
        pw = os.environ.get("VPS_SSH_KEY_PASSPHRASE") or None
    for cls in (paramiko.Ed25519Key, paramiko.RSAKey, paramiko.ECDSAKey):
        try:
            return cls.from_private_key(io.StringIO(pem), password=pw or None)
        except paramiko.SSHException:
            continue
    raise VPSError("Could not read the SSH private key (ed25519, RSA or ECDSA, correct passphrase).")


def check_host_allowed(host):
    """Block loopback / private / link-local targets so the API can't be used to probe internal networks."""
    if os.environ.get("ALLOW_PRIVATE_HOSTS", "false").lower() == "true":
        return
    try:
        infos = socket.getaddrinfo(host, None)
    except OSError:
        raise VPSError(f"Cannot resolve host '{host}'.")
    for info in infos:
        ip = ipaddress.ip_address(info[4][0].split("%")[0])
        if ip.is_private or ip.is_loopback or ip.is_link_local or ip.is_reserved or ip.is_multicast:
            raise VPSError("That host address is not allowed (private or local network).")


_seen_fp = {}  # trust-on-first-use memory (per host:port, lives until Render restarts)


def open_transport(p):
    host, port, username = p["host"], p["port"], p["username"]
    pinned = [x.strip() for x in (p.get("fingerprint") or os.environ.get("VPS_HOST_FINGERPRINT", "")).split(",") if x.strip()]
    password = p.get("password")
    key = None if password else load_key(p.get("key_pem"), p.get("key_pass"))
    if not password and key is None:
        raise VPSError("No SSH credentials. Send a password or private key with the connect request.")
    check_host_allowed(host)
    try:
        sock = socket.create_connection((host, port), timeout=10)
    except OSError as e:
        raise VPSError(f"Cannot reach {host}:{port} ({e}). Check the IP, port and VPS firewall.")
    t = paramiko.Transport(sock)
    try:
        t.start_client(timeout=15)
        rk = t.get_remote_server_key()
        fp = "SHA256:" + base64.b64encode(hashlib.sha256(rk.asbytes()).digest()).decode().rstrip("=")
        if pinned:
            # strict mode: fingerprint must match one you configured
            if not any(hmac.compare_digest(fp, p) for p in pinned):
                raise VPSError(f"HOST KEY MISMATCH: server presented {fp}. Connection refused (possible MITM).")
        else:
            # no fingerprint configured: trust on first use, then refuse if it ever changes
            known = _seen_fp.get((host, port))
            if known and not hmac.compare_digest(known, fp):
                raise VPSError(f"HOST KEY CHANGED since first connect: now {fp}. Connection refused.")
            _seen_fp[(host, port)] = fp
        if password:
            try:
                t.auth_password(username, password)
            except paramiko.BadAuthenticationType as e:
                # some servers only offer keyboard-interactive for passwords
                if "keyboard-interactive" in (e.allowed_types or []):
                    t.auth_interactive_dumb(username)
                else:
                    raise
            if not t.is_authenticated():
                raise paramiko.AuthenticationException("not authenticated")
        else:
            t.auth_publickey(username, key)
        t.set_keepalive(30)
        return t, fp
    except VPSError:
        t.close()
        raise
    except paramiko.AuthenticationException:
        t.close()
        method = "password" if password else "SSH key"
        raise VPSError(f"SSH {method} authentication rejected for user '{username}'. Check the username/password and that the VPS allows password login (PasswordAuthentication yes).")
    except Exception as e:
        t.close()
        raise VPSError(f"SSH error: {e}")


def do_connect(p):
    with vps.lock:
        if vps.t is not None:
            try:
                vps.t.close()
            except Exception:
                pass
            vps.t = None
        try:
            t, fp = open_transport(p)
        except VPSError as e:
            vps.last_error = str(e)
            raise
        vps.t, vps.params, vps.fp, vps.connected_at, vps.manual_off = t, p, fp, now_iso(), False
        try:
            vps.linger = ensure_setup()
        except VPSError as e:
            vps.last_error = str(e)
            t.close()
            vps.t = None
            raise
        vps.last_error = None


def get_transport():
    with vps.lock:
        if vps.t is not None and vps.t.is_active():
            return vps.t
        p = vps.params or env_params()
        if vps.manual_off or not p:
            raise NotConnected("VPS is not connected. Open the VPS page and press Connect.")
        do_connect(p)  # lazy reconnect after Render sleep/restart
        return vps.t


def run(cmd, stdin=None, timeout=60):
    t = get_transport()
    full = ('export XDG_RUNTIME_DIR=/run/user/$(id -u); '
            'export DBUS_SESSION_BUS_ADDRESS=unix:path=$XDG_RUNTIME_DIR/bus; ' + cmd)
    try:
        ch = t.open_session(timeout=15)
        ch.exec_command(full)
        if stdin is not None:
            ch.sendall(stdin if isinstance(stdin, bytes) else stdin.encode())
        ch.shutdown_write()
    except Exception as e:
        vps.t = None
        raise VPSError(f"SSH connection lost ({e}). Retry; the backend will reconnect.")
    out, err, end = bytearray(), bytearray(), time.time() + timeout
    while True:
        got = False
        while ch.recv_ready():
            out += ch.recv(65536)
            got = True
        while ch.recv_stderr_ready():
            err += ch.recv_stderr(65536)
            got = True
        if ch.exit_status_ready() and not ch.recv_ready() and not ch.recv_stderr_ready():
            break
        if time.time() > end:
            ch.close()
            raise VPSError("Command timed out on the VPS.")
        if not got:
            time.sleep(0.03)
    code = ch.recv_exit_status()
    ch.close()
    return code, out.decode(errors="replace"), err.decode(errors="replace")


def ensure_setup():
    code, out, err = run(
        'mkdir -p "$HOME/.config/systemd/user" "$HOME/techbooster/bots" && '
        'cat > "$HOME/.config/systemd/user/techbooster-bot@.service" && systemctl --user daemon-reload',
        stdin=UNIT,
    )
    if code != 0:
        raise VPSError("Could not prepare systemd user services. On the VPS run once: "
                       "sudo loginctl enable-linger <user>. Details: " + (err.strip() or out.strip())[:300])
    _, o, _ = run('loginctl show-user "$(id -un)" -p Linger --value 2>/dev/null')
    return o.strip() == "yes"


# ------------------------------------------------------------------- app ---
app = FastAPI(
    title="TechBooster VPS Bot Manager API",
    version="1.0.0",
    description="Manage Telegram bots on your VPS. All endpoints except /api/health need `Authorization: Bearer <API_TOKEN>`.",
    docs_url="/docs" if ENABLE_DOCS else None,
    redoc_url=None,
    openapi_url="/openapi.json" if ENABLE_DOCS else None,
)


@app.middleware("http")
async def size_guard(request: Request, call_next):
    cl = request.headers.get("content-length", "")
    if request.method == "POST" and cl.isdigit() and int(cl) > MAX_UPLOAD + 2 * 1048576:
        return JSONResponse({"detail": "Request too large."}, status_code=413)
    return await call_next(request)


app.add_middleware(  # added last => outermost, so CORS headers also cover errors
    CORSMiddleware,
    allow_origins=ORIGINS,
    # Local testing: any http://localhost:PORT or http://127.0.0.1:PORT page. Set ALLOW_LOCALHOST=false in production.
    allow_origin_regex=r"^http://(localhost|127\.0\.0\.1)(:\d+)?$" if os.environ.get("ALLOW_LOCALHOST", "true").lower() == "true" else None,
    allow_methods=["GET", "POST", "DELETE"],
    allow_headers=["Authorization", "Content-Type"],
    max_age=600,
)


@app.exception_handler(NotConnected)
async def _nc(_, e):
    return JSONResponse({"detail": str(e)}, status_code=409)


@app.exception_handler(VPSError)
async def _ve(_, e):
    return JSONResponse({"detail": str(e)}, status_code=502)


# ---------------------------------------------------------------- health ---
@app.get("/api/health", tags=["system"])
def health():
    """Unauthenticated liveness check (used by Render)."""
    alive = vps.t is not None and vps.t.is_active()
    return {"status": "ok", "vps_connected": alive, "time": now_iso()}


# ----------------------------------------------------------- VPS endpoints ---
class ConnectBody(BaseModel):
    host: Optional[str] = Field(None, max_length=253, pattern=r"^[A-Za-z0-9.:\-]+$")
    port: Optional[int] = Field(None, ge=1, le=65535)
    username: Optional[str] = Field(None, pattern=r"^[A-Za-z_][A-Za-z0-9_.-]{0,31}$")
    password: Optional[str] = Field(None, max_length=256, repr=False)
    private_key: Optional[str] = Field(None, max_length=20000, repr=False, description="PEM text, alternative to password")
    key_passphrase: Optional[str] = Field(None, max_length=256, repr=False)
    fingerprint: Optional[str] = Field(None, max_length=600, pattern=r"^[A-Za-z0-9:+/=,\s]+$",
                                       description="Optional SHA256:... host key fingerprint to enforce")


def vps_info(alive):
    p = vps.params or env_params() or {}
    return {
        "connected": alive,
        "host": p.get("host"),
        "port": p.get("port", 22),
        "username": p.get("username"),
        "fingerprint": vps.fp if alive else None,
        "connected_at": vps.connected_at if alive else None,
        "linger": vps.linger if alive else None,
        "auth_configured": bool(p.get("password") or p.get("key_pem") or os.environ.get("VPS_SSH_KEY_B64")),
        "fingerprint_pinned": bool(p.get("fingerprint") or os.environ.get("VPS_HOST_FINGERPRINT")),  # false = trust-on-first-use
        "last_error": vps.last_error,
    }  # secrets are never returned


@app.get("/api/vps/status", dependencies=[Depends(auth)], tags=["vps"])
def vps_status():
    """Connection state. Quietly re-connects (using env config) after Render wakes up."""
    alive = vps.t is not None and vps.t.is_active()
    if not alive and not vps.manual_off and (vps.params or env_params()):
        try:
            get_transport()
            alive = True
        except VPSError:
            pass
    return vps_info(alive)


@app.post("/api/vps/connect", dependencies=[Depends(auth), Depends(limit("connect", 10))], tags=["vps"])
def vps_connect(body: ConnectBody = ConnectBody()):
    """Connect to a VPS. Send host, port, username and password (or private_key) in the body.
    Credentials are kept in backend memory only (never stored on disk, never returned); after a
    Render restart/sleep, connect again. An empty body uses the optional VPS_* env fallback."""
    base = env_params()
    p = dict(base or {"host": None, "port": 22, "username": "root", "password": None,
                      "key_pem": None, "key_pass": None, "fingerprint": None})
    has_creds = bool(body.password or body.private_key)
    if body.host and not has_creds and (not base or body.host != base["host"]):
        raise HTTPException(422, "Send a password or private_key together with the host.")
    for k in ("host", "port", "username"):
        v = getattr(body, k)
        if v is not None:
            p[k] = v
    if body.password:
        p.update(password=body.password, key_pem=None, key_pass=None)
    elif body.private_key:
        p.update(password=None, key_pem=body.private_key, key_pass=body.key_passphrase)
    if body.fingerprint:
        p["fingerprint"] = body.fingerprint
    if not p.get("host"):
        raise HTTPException(422, "VPS host is required.")
    _seen_fp.pop((p["host"], p["port"]), None)  # explicit connect: re-learn host key (shown in response to verify)
    do_connect(p)
    return vps_info(True)


@app.post("/api/vps/disconnect", dependencies=[Depends(auth)], tags=["vps"])
def vps_disconnect():
    """Close SSH and forget the credentials held in memory."""
    with vps.lock:
        vps.manual_off = True
        if vps.t is not None:
            try:
                vps.t.close()
            except Exception:
                pass
        vps.t = None
        vps.params = None
        vps.fp = None
    return vps_info(False)


STATS_SH = r'''
a=$(head -1 /proc/stat); sleep 0.4; b=$(head -1 /proc/stat)
echo "cpu1 $a"; echo "cpu2 $b"
free -b | awk '/^Mem:/{print "mem",$2,($7==""?$4:$7)}'
df -B1 --output=size,used / | tail -1 | awk '{print "disk",$1,$2}'
echo "up $(cut -d' ' -f1 /proc/uptime)"
echo "cores $(nproc)"
echo "load $(cut -d' ' -f1-3 /proc/loadavg)"
echo "host $(hostname)"
'''


@app.get("/api/server/stats", dependencies=[Depends(auth)], tags=["system"])
def server_stats():
    """CPU, RAM, disk and uptime read from the VPS."""
    code, out, err = run("sh -s", stdin=STATS_SH)
    if code != 0:
        raise HTTPException(500, "Could not read server stats: " + err.strip()[:200])
    d = {}
    for line in out.splitlines():
        k, _, v = line.partition(" ")
        d[k] = v
    try:
        c1 = [int(x) for x in d["cpu1"].split()[1:9]]
        c2 = [int(x) for x in d["cpu2"].split()[1:9]]
        total, idle = sum(c2) - sum(c1), (c2[3] + c2[4]) - (c1[3] + c1[4])
        cpu = round(100 * (1 - idle / total), 1) if total > 0 else 0.0
        mt, ma = [int(x) for x in d["mem"].split()]
        dt, du = [int(x) for x in d["disk"].split()]
        return {
            "hostname": d.get("host", ""),
            "cpu_percent": cpu,
            "cpu_cores": int(d["cores"]),
            "load": d.get("load", ""),
            "ram": {"total": mt, "used": mt - ma, "percent": round(100 * (mt - ma) / mt, 1)},
            "disk": {"total": dt, "used": du, "percent": round(100 * du / dt, 1)},
            "uptime_seconds": int(float(d["up"])),
        }
    except (KeyError, ValueError, ZeroDivisionError):
        raise HTTPException(500, "Unexpected output while reading server stats.")


# ------------------------------------------------------------ bot helpers ---
LIST_PY = r'''
import json, os, subprocess
base = os.path.expanduser("~/techbooster/bots")
def sh(a):
    return subprocess.run(a, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL, universal_newlines=True).stdout
out = []
for bid in (sorted(os.listdir(base)) if os.path.isdir(base) else []):
    d = os.path.join(base, bid)
    try:
        meta = json.load(open(os.path.join(d, "meta.json")))
    except Exception:
        continue
    unit = "techbooster-bot@%s.service" % bid
    p = dict(l.split("=", 1) for l in sh(["systemctl", "--user", "show", unit, "-p", "ActiveState", "-p", "SubState",
        "-p", "MainPID", "-p", "ExecMainStartTimestamp", "-p", "Result", "-p", "ExecMainStatus"]).splitlines() if "=" in l)
    state, sub = p.get("ActiveState", ""), p.get("SubState", "")
    pid = int(p.get("MainPID") or 0)
    status = "running" if state == "active" else ("failed" if state == "failed" or sub == "auto-restart" else "stopped")
    cpu = mem = None
    if pid:
        q = sh(["ps", "-o", "%cpu=,rss=", "-p", str(pid)]).split()
        if len(q) == 2:
            cpu, mem = float(q[0]), int(q[1]) * 1024
    err = None
    if status == "failed":
        err = "%s (exit status %s)" % (p.get("Result", "failed"), p.get("ExecMainStatus", "?"))
    out.append({"id": bid, "name": meta.get("name", bid), "main": meta.get("main"), "dir": os.path.join(d, "app"),
        "created": meta.get("created"), "status": status, "pid": pid or None, "cpu_percent": cpu, "memory_bytes": mem,
        "last_start": p.get("ExecMainStartTimestamp") or None, "last_error": err,
        "installed": os.path.exists(os.path.join(d, "venv", "bin", "python"))})
print(json.dumps(out))
'''


def unit_of(bid):
    return f"techbooster-bot@{bid}.service"


def bot_dir(bid):
    """Validate the id (strict regex => no traversal) and make sure the project exists."""
    if not ID_RE.match(bid):
        raise HTTPException(404, "Unknown bot.")
    d = f'"$HOME/techbooster/bots/{bid}"'
    if run(f"test -f {d}/meta.json")[0] != 0:
        raise HTTPException(404, "Unknown bot.")
    return d


def make_id(name):
    slug = re.sub(r"[^a-z0-9]+", "-", name.lower()).strip("-")[:30].strip("-")
    if len(slug) < 3:
        slug = "bot"
    return f"{slug}-{secrets.token_hex(2)}"


@app.get("/api/bots", dependencies=[Depends(auth)], tags=["bots"])
def list_bots():
    code, out, err = run("python3 -", stdin=LIST_PY)
    if code != 0:
        raise HTTPException(500, "Could not list bots (is python3 installed on the VPS?): " + err.strip()[:200])
    bots = json.loads(out or "[]")
    counts = {s: sum(1 for b in bots if b["status"] == s) for s in ("running", "stopped", "failed")}
    return {"bots": bots, "total": len(bots), **counts}


# ---------------------------------------------------------------- upload ---
def save_limited(up: UploadFile, max_bytes):
    tmp = tempfile.NamedTemporaryFile(delete=False)
    size = 0
    try:
        while True:
            chunk = up.file.read(1024 * 1024)
            if not chunk:
                break
            size += len(chunk)
            if size > max_bytes:
                raise HTTPException(413, f"File too large (limit {max_bytes // 1048576} MB).")
            tmp.write(chunk)
        tmp.close()
        return tmp.name
    except Exception:
        tmp.close()
        os.unlink(tmp.name)
        raise


def safe_member(name):
    if "\\" in name or "\x00" in name or name.startswith("/") or not PATH_RE.match(name):
        raise HTTPException(400, f"Unsafe file name in archive: {name[:80]!r}")
    parts = name.split("/")
    if any(p in ("", ".", "..") for p in parts) or ":" in parts[0]:
        raise HTTPException(400, f"Unsafe path in archive: {name[:80]!r}")
    return name


def add_bytes(tar, arcname, data):
    ti = tarfile.TarInfo(arcname)
    ti.size, ti.mode, ti.mtime = len(data), 0o644, int(time.time())
    tar.addfile(ti, io.BytesIO(data))


def build_tar(src, kind, fname, req_bytes):
    """Validate the upload and repack it as a clean tar.gz (no symlinks, no traversal)."""
    out = tempfile.NamedTemporaryFile(suffix=".tgz", delete=False)
    files = []
    try:
        with tarfile.open(fileobj=out, mode="w:gz") as tar:
            if kind == "py":
                add_bytes(tar, fname, open(src, "rb").read())
                files.append(fname)
            else:
                try:
                    zf = zipfile.ZipFile(src)
                except zipfile.BadZipFile:
                    raise HTTPException(400, "That file is not a valid ZIP archive.")
                with zf:
                    items = [i for i in zf.infolist()
                             if not i.is_dir() and not i.filename.startswith("__MACOSX/") and not i.filename.endswith(".DS_Store")]
                    if not items:
                        raise HTTPException(400, "The ZIP archive is empty.")
                    if len(items) > MAX_FILES:
                        raise HTTPException(400, f"Too many files (limit {MAX_FILES}).")
                    if sum(i.file_size for i in items) > MAX_UNZIPPED:
                        raise HTTPException(400, f"Archive expands beyond {MAX_UNZIPPED // 1048576} MB.")
                    paths = []
                    for i in items:
                        if (i.external_attr >> 16) & 0o170000 == 0o120000:
                            raise HTTPException(400, f"Symlinks are not allowed ({i.filename[:80]!r}).")
                        if i.flag_bits & 1:
                            raise HTTPException(400, "Encrypted ZIP archives are not supported.")
                        paths.append(safe_member(i.filename))
                    tops = {p.split("/")[0] for p in paths}
                    if len(tops) == 1 and all("/" in p for p in paths):  # strip single wrapper folder
                        paths = [p.split("/", 1)[1] for p in paths]
                    if len(set(paths)) != len(paths):
                        raise HTTPException(400, "Archive contains duplicate file names.")
                    for i, p in zip(items, paths):
                        if req_bytes is not None and p == "requirements.txt":
                            continue
                        ti = tarfile.TarInfo(p)
                        ti.size, ti.mode, ti.mtime = i.file_size, 0o644, int(time.time())
                        with zf.open(i) as f:
                            tar.addfile(ti, f)
                        files.append(p)
            if req_bytes is not None:
                add_bytes(tar, "requirements.txt", req_bytes)
                files.append("requirements.txt")
        out.close()
        return out.name, files
    except Exception:
        out.close()
        os.unlink(out.name)
        raise


@app.post("/api/bots/upload", dependencies=[Depends(auth), Depends(limit("upload", 10))], tags=["bots"])
def upload_bot(
    name: str = Form(...),
    main: str = Form(""),
    file: UploadFile = File(..., description=".py or .zip"),
    requirements: Optional[UploadFile] = File(None, description="optional requirements.txt"),
):
    """Validate and copy a project to the VPS. Nothing is installed or started here."""
    name = name.strip()
    if not NAME_RE.match(name):
        raise HTTPException(422, "Project name: 1-60 characters (letters, numbers, space, . _ -).")
    fname = os.path.basename(file.filename or "")
    kind = fname.lower().rsplit(".", 1)[-1] if "." in fname else ""
    if kind not in ("py", "zip"):
        raise HTTPException(400, "Only .py and .zip files are accepted.")
    if kind == "py" and not re.fullmatch(r"[A-Za-z0-9_][A-Za-z0-9_.\-]{0,80}\.py", fname):
        raise HTTPException(400, "Python file name may only contain letters, numbers, _ . -")

    src = save_limited(file, MAX_UPLOAD)
    tar_path = None
    try:
        req_bytes = None
        if requirements is not None and requirements.filename:
            rp = save_limited(requirements, 1 << 20)
            try:
                req_bytes = open(rp, "rb").read()
            finally:
                os.unlink(rp)
            try:
                req_bytes.decode("utf-8")
            except UnicodeDecodeError:
                raise HTTPException(400, "requirements.txt must be UTF-8 text.")

        tar_path, files = build_tar(src, kind, fname, req_bytes)
        py_files = sorted(f for f in files if f.endswith(".py"))
        if kind == "py":
            main = fname
        else:
            main = main.strip() or next((c for c in ("main.py", "bot.py", "app.py") if c in files), "")
            if not MAIN_RE.match(main) or main not in files:
                raise HTTPException(422, {"message": "Choose the main Python file for this project.",
                                          "py_files": py_files[:200]})

        bid = make_id(name)
        d = f'"$HOME/techbooster/bots/{bid}"'
        home = run('printf %s "$HOME"')[1].strip()
        code, _, err = run(f"mkdir -p {d}/app")
        if code != 0:
            raise HTTPException(500, "Could not create project directory: " + err.strip()[:200])
        try:
            sftp = paramiko.SFTPClient.from_transport(get_transport())
            try:
                sftp.put(tar_path, f"{home}/techbooster/bots/{bid}/upload.tgz")
            finally:
                sftp.close()
            code, _, err = run(f"cd {d} && tar -xzf upload.tgz -C app --no-same-owner --no-same-permissions && rm -f upload.tgz")
            if code != 0:
                raise HTTPException(500, "Extraction on the VPS failed: " + err.strip()[:200])
            meta = {"id": bid, "name": name, "main": main, "created": now_iso()}
            run(f"cat > {d}/env", stdin=f"MAIN={main}\n")
            run(f"cat > {d}/meta.json", stdin=json.dumps(meta))
        except Exception:
            run(f"rm -rf {d}")
            raise
        return {"id": bid, "name": name, "main": main, "file_count": len(files),
                "has_requirements": "requirements.txt" in files, "installed": False,
                "message": "Uploaded. Install dependencies, then start the bot."}
    finally:
        os.unlink(src)
        if tar_path:
            os.unlink(tar_path)


# --------------------------------------------------- install / start / stop ---
@app.post("/api/bots/{bid}/install", dependencies=[Depends(auth), Depends(limit("install", 20))], tags=["bots"])
def install_deps(bid: str):
    """Create the project's virtualenv and pip-install requirements.txt (background job on the VPS)."""
    d = bot_dir(bid)
    busy = run(f'[ -f {d}/install.log ] && [ ! -f {d}/install.status ] && [ -n "$(find {d}/install.log -mmin -15)" ]')[0] == 0
    if busy:
        raise HTTPException(409, "An installation is already running for this bot.")
    job = ("python3 -m venv venv && { [ ! -f app/requirements.txt ] || "
           "venv/bin/pip install --disable-pip-version-check --no-input -r app/requirements.txt; }; echo $? > install.status")
    code, _, err = run(f"cd {d} && rm -f install.status && (setsid nohup sh -c {shlex.quote(job)} > install.log 2>&1 < /dev/null &)")
    if code != 0:
        raise HTTPException(500, "Could not start installation: " + err.strip()[:200])
    return {"state": "running"}


@app.get("/api/bots/{bid}/install", dependencies=[Depends(auth)], tags=["bots"])
def install_status(bid: str):
    d = bot_dir(bid)
    cmd = (f'cd {d} && if [ -f install.status ]; then echo "state:$(cat install.status)"; '
           f'elif [ -f install.log ]; then echo state:running; else echo state:none; fi; tail -n 60 install.log 2>/dev/null')
    _, out, _ = run(cmd)
    first, _, log = out.partition("\n")
    raw = first.split(":", 1)[-1].strip()
    state = {"running": "running", "none": "none", "0": "success"}.get(raw, "failed")
    return {"state": state, "log": log}


def _action(bid, cmd, ok_msg):
    code, _, err = run(cmd)
    if code != 0:
        raise HTTPException(500, err.strip()[:300] or "systemctl command failed.")
    return {"ok": True, "message": ok_msg}


@app.post("/api/bots/{bid}/start", dependencies=[Depends(auth), Depends(limit("action", 60))], tags=["bots"])
def start_bot(bid: str):
    d = bot_dir(bid)
    if run(f"test -x {d}/venv/bin/python")[0] != 0:
        raise HTTPException(409, "Dependencies are not installed yet. Install them first.")
    u = unit_of(bid)
    return _action(bid, f"systemctl --user reset-failed {u} 2>/dev/null; systemctl --user enable --now {u}", "Bot started.")


@app.post("/api/bots/{bid}/stop", dependencies=[Depends(auth), Depends(limit("action", 60))], tags=["bots"])
def stop_bot(bid: str):
    bot_dir(bid)
    u = unit_of(bid)
    return _action(bid, f"systemctl --user disable --now {u} 2>/dev/null; systemctl --user stop {u}; systemctl --user reset-failed {u} 2>/dev/null; true", "Bot stopped.")


@app.post("/api/bots/{bid}/restart", dependencies=[Depends(auth), Depends(limit("action", 60))], tags=["bots"])
def restart_bot(bid: str):
    d = bot_dir(bid)
    if run(f"test -x {d}/venv/bin/python")[0] != 0:
        raise HTTPException(409, "Dependencies are not installed yet. Install them first.")
    u = unit_of(bid)
    return _action(bid, f"systemctl --user reset-failed {u} 2>/dev/null; systemctl --user enable {u} 2>/dev/null; systemctl --user restart {u}", "Bot restarted.")


@app.delete("/api/bots/{bid}", dependencies=[Depends(auth), Depends(limit("action", 60))], tags=["bots"])
def delete_bot(bid: str):
    d = bot_dir(bid)
    u = unit_of(bid)
    run(f"systemctl --user disable --now {u} 2>/dev/null; systemctl --user stop {u} 2>/dev/null; systemctl --user reset-failed {u} 2>/dev/null; true")
    code, _, err = run(f"rm -rf {d}")
    if code != 0:
        raise HTTPException(500, "Could not delete project files: " + err.strip()[:200])
    return {"ok": True, "message": "Bot project deleted."}


# ------------------------------------------------------------------ logs ---
ERR_RE = re.compile(r"traceback|error|exception|critical|fatal", re.I)


@app.get("/api/bots/{bid}/logs", dependencies=[Depends(auth)], tags=["bots"])
def bot_logs(bid: str, lines: int = Query(200, ge=1, le=1000), cursor: Optional[str] = None):
    """Journal entries for a bot. Pass the returned `cursor` to fetch only newer lines (polling)."""
    bot_dir(bid)
    base = f"journalctl --user -u {unit_of(bid)} -o json --no-pager"
    if cursor:
        if not CURSOR_RE.match(cursor):
            raise HTTPException(422, "Invalid cursor.")
        cmd = f"{base} --after-cursor={shlex.quote(cursor)} | tail -n 1000"
    else:
        cmd = f"{base} -n {int(lines)}"
    code, out, err = run(cmd)
    if code != 0 and not out:
        raise HTTPException(502, "Could not read logs: " + (err.strip()[:200] or "journalctl failed"))
    entries, last = [], cursor
    for line in out.splitlines():
        try:
            j = json.loads(line)
        except ValueError:
            continue
        msg = j.get("MESSAGE", "")
        if isinstance(msg, list):
            msg = bytes(msg).decode(errors="replace")
        pri = int(j.get("PRIORITY", 6) or 6)
        stream = "stderr" if pri <= 3 or ERR_RE.search(msg) else "stdout"
        entries.append({"ts": int(j.get("__REALTIME_TIMESTAMP", 0)) / 1e6, "stream": stream, "msg": msg})
        last = j.get("__CURSOR", last)
    return {"entries": entries, "cursor": last}
