# -*- coding: utf-8 -*-
#  All rights reserved.
# ════════════════════════════════════════════════════════════════════════
import sys, os, json, time, uuid, random, asyncio, base64, struct, socket
import itertools, traceback, ssl, hmac, hashlib, string, re, subprocess, math, collections
import httpx
import aiohttp
import aiohttp.web
from datetime import datetime
from typing import Dict, List, Optional, Tuple, Any

if sys.platform == "win32":
    try:
        if hasattr(sys.stdout, 'reconfigure'):
            sys.stdout.reconfigure(encoding='utf-8', errors='replace')
            sys.stderr.reconfigure(encoding='utf-8', errors='replace')
    except Exception: pass

from google_play_scraper import app as play_scraper
from Crypto.Cipher import AES
from Crypto.Util.Padding import pad
from protobuf_decoder.protobuf_decoder import Parser
from message_ids import MESSAGE_ID_TO_NAME
import thunderFF_pb2

try:
    import StartMatch_pb2
except Exception:
    StartMatch_pb2 = None

try:
    import reqClan_pb2
    _CLAN_PB_AVAILABLE = True
except Exception:
    _CLAN_PB_AVAILABLE = False

# ==================== CONFIG ====================
WEB_HOST = "0.0.0.0"
WEB_PORT = 8080
ACCOUNTS_FILE = "accounts.json"
TOKEN_CACHE_FILE = "token_cache.json"
DEVICES_FILE = "devices.json"
TOKEN_CACHE_TTL = 1200
INDEX_HTML_PATH = "index.html"

START_MATCH_INTERVAL = 3.0
NEW_MATCH_DELAY = 2.0
MAX_MATCH_DURATION = 1500
MATCH_IDLE_TIMEOUT  = 35.0

NO_MATCH_RESTART_ENABLED  = False
NO_MATCH_RESTART_TIMEOUT  = 90.0
NO_MATCH_RESTART_GRACE    = 60.0

_accept_friend_request = True
DEBUG_ALL_PACKETS = False

TEAM_MODE = True  # Solo CS Ranked এর জন্য False | 4-Bot Squad CS Ranked এর জন্য True
TEAM_SIZE = 4
TEAM_READY_DELAY = 5.0
TEAM_INVITE_WAIT = 2.5
CLAN_ID_DEFAULT = "3087207343"
DEV_UID = ""

# ==================== CS MODE (CLASH SQUAD) ====================
# True  → matchmaking / team / UDP join use Clash Squad (mode 15)
# False → original Battle Royale flow
CS_MODE_ENABLED        = True
CS_RANKED_ENABLED      = True    # True = CS Ranked (mode 6) | False = CS Casual (mode 1)
CS_MODE_ID             = 15      # Clash Squad mode id (create_team field 2.3 + UDP 448 join)
CS_MAX_MATCH_DURATION  = 700     # safety limit for one CS match (seconds)
CS_MATCH_IDLE_TIMEOUT  = 10.0    # server silent this long after join → match finished
CS_TEAM_START_RETRY    = 90.0    # CS squad: send ready/start again only after this long without a match
CS_TEAM_LEADER_DELAY   = 2.0     # CS squad leader: after ready, before start
CS_TEAM_MEMBERS_START  = False   # CS squad members also send start_match_team (off = only the leader)

# ==================== MOVEMENT & GLORY CONFIG (from app.py) ====================
AUTO_MOVE_ENABLED         = True
AUTO_MOVE_START_DELAY     = 2.0
AUTO_MOVE_SPAWN_TIMEOUT   = 18.0
AUTO_MOVE_LAND_TIMEOUT    = 6.0
AUTO_MOVE_TICK_INTERVAL   = 0.1
AUTO_MOVE_WALK_SPEED      = 352
AUTO_MOVE_RUN_SPEED       = 546
AUTO_MOVE_RUN_CHANCE      = 0.6
AUTO_MOVE_RADIUS          = 6000
AUTO_MOVE_MIN_LEG         = 1500
AUTO_MOVE_TURN_PER_TICK   = 25.0
AUTO_MOVE_PAUSE_RANGE     = (0.6, 2.5)
AUTO_MOVE_RESYNC_DISTANCE = 2500
AUTO_MOVE_PIGGYBACK_ACK   = True
AUTO_MOVE_MSG_KEYS        = list(range(0x64, 0x6E))
AUTO_MOVE_DEFAULT_RTT     = 120
STRAIGHT_RUN_SEC          = 5.0         # ৫ সেকেন্ড শুধু সোজা সামনে
CIRCLE_MOVE_SEC           = 15.0        # ১৫ সেকেন্ড বর্তমান (circle/normal)

# ★ CUSTOM MOVEMENT CYCLE CONFIG ★
CUSTOM_CYCLE_ENABLED       = True   # False করলে পুরনো মুভমেন্ট সিস্টেমে ফিরে যাবে
CUSTOM_CYCLE_STEPS         = [
    ("run_1",         4.0),   # ৪.০ সেকেন্ড সোজা দৌড়াবে
    ("crouch_walk",   0.8),   # ০.৮ সেকেন্ড বসে সামনের দিকে হাঁটবে
    ("run_2",         0.5),   # ০.৫ সেকেন্ড আবার দৌড়াবে
    ("jump",          0.4),   # ০.৪ সেকেন্ড লাফ দেবে
    ("rotate_screen", 0.6),   # ০.৬ সেকেন্ড স্ক্রিন ঘোরাবে
    ("walk",          0.8),   # ০.৮ সেকেন্ড আবার হাঁটবে
    ("idle",          0.8),   # ০.৮ সেকেন্ড একটু থেমে থাকবে
]
CROUCH_WALK_SPEED          = 180    # বসে হাঁটার গতি
JUMP_MOVE_SPEED            = 420    # লাফ দেওয়ার সময় সামনের গতি
SCREEN_ROTATE_DEG_PER_SEC  = 180.0  # স্ক্রিন ঘোরার গতি (ডিগ্রি/সেকেন্ড)
CUSTOM_CYCLE_TICK_INTERVAL = 0.05   # 20Hz স্মুথ আপডেট
CUSTOM_CYCLE_LOG_STEPS     = True   # False করলে কনসোলে স্টেপ লগ দেখাবে না

# ★ GLORY BOOST CONFIG ★
GLORY_BOOST_ENABLED       = True
GLORY_TICK_INTERVAL       = 0.05        # 20Hz fast sync
GLORY_ACTION_EVERY        = 0.5         # fake shoot/loot action packet
GLORY_PING_EVERY          = 0.5         # extra ping packet
GLORY_MSG_KEYS            = list(range(0x64, 0x6E))

SQUAD_ARRIVAL_RADIUS  = 280.0
SQUAD_TARGET_TIMEOUT  = 22.0
SQUAD_ENEMY_TTL       = 7.0
STUCK_THRESHOLD       = 6.0
STUCK_LOG_COOLDOWN    = 3.0

# ==================== ANTI-AFK MOVEMENT (legacy) ====================
# Only used when AUTO_MOVE_ENABLED is False (both send 2001 packets, never run them together)
ANTI_AFK_ENABLED        = True
ANTI_AFK_TICK_HZ        = 6.0
ANTI_AFK_SPAWN_DELAY    = 3.0
ANTI_AFK_RADIUS         = 800
ANTI_AFK_SPEED          = 55
ANTI_AFK_SPRINT_SPEED   = 95
ANTI_AFK_IDLE_CHANCE    = 0.08
ANTI_AFK_SPRINT_CHANCE  = 0.35
ANTI_AFK_DECISION_SEC   = 2.5
ANTI_AFK_PING_EVERY     = 2.0
ANTI_AFK_JUMP_EVERY     = 20.0

ANALOG_DIRECTIONS = [
    (0.0,  1.0, "maju"), (0.0, -1.0, "mundur"),
    (-1.0, 0.0, "kiri"), (1.0,  0.0, "kanan"),
    (-0.7, 0.7, "maju-kiri"), (0.7,  0.7, "maju-kanan"),
    (-0.7,-0.7, "mundur-kiri"), (0.7, -0.7, "mundur-kanan"),
    (0.0,  0.0, "idle"),
]

ENABLE_SPEED_MOVEMENT       = True
MOVEMENT_SPEED_MIN          = 1.0
MOVEMENT_SPEED_MAX          = 1.4
MOVEMENT_PATTERN            = "circle"
MOVEMENT_TICK_MS            = 240
MOVEMENT_RADIUS             = 180
MOVEMENT_UPDATE_SPEED_EVERY = 4.0

MOVEMENT_STATE_IDLE_CHANCE   = 0.10
MOVEMENT_STATE_WALK_CHANCE   = 0.28
MOVEMENT_STATE_RUN_CHANCE    = 0.32
MOVEMENT_STATE_SPRINT_CHANCE = 0.10
MOVEMENT_STATE_JUMP_CHANCE   = 0.08
MOVEMENT_STATE_CROUCH_CHANCE = 0.06
MOVEMENT_STATE_PRONE_CHANCE  = 0.06

PLAYER_STATE_MAP = {"idle":0,"walk":1,"run":1,"sprint":1,"jump":2,"crouch":3,"prone":4}
MOVE_STATE_MAP   = {"idle":0,"walk":1,"run":2,"sprint":3,"jump":4,"crouch":1,"prone":1}
STATE_SPEED      = {"idle":0,"walk":45,"run":70,"sprint":95,"jump":55,"crouch":25,"prone":15}

ENABLE_NEWBIE_CHARACTER     = False
NEWBIE_SELECT_BEFORE_TEAM   = False
NEWBIE_SELECT_DELAY         = 1.5
NEWBIE_SELECT_RETRY         = 2
NEWBIE_SELECT_WAIT_AFTER    = 2.0
NEWBIE_ITEM_ID_1            = 102000011
NEWBIE_ITEM_ID_2            = 102000026
NEWBIE_ITEM_ID_3            = 102000037
NEWBIE_ITEM_ID_EXTRA        = 102000023
NEWBIE_SUB4_FIELD_3         = 50
NEWBIE_SUB4_FIELD_5_2       = 4806
NEWBIE_SUB4_FIELD_8         = 1
NEWBIE_SUB4_FIELD_11        = 11679599800712232

AES_KEY = bytes([89, 103, 38, 116, 99, 37, 68, 69, 117, 104, 54, 37, 90, 99, 94, 56])
AES_IV  = bytes([54, 111, 121, 90, 68, 114, 50, 50, 69, 51, 121, 99, 104, 106, 77, 37])
KEYSTREAM = bytes([0x30,0x30,0x30,0x32,0x30,0x31,0x37,0x30,0x30,0x30,0x30,0x30,0x32,0x30,0x31,0x37,0x30,0x30,0x30,0x30,0x30,0x32,0x30,0x31,0x37,0x30,0x30,0x30,0x30,0x30,0x32,0x30])
HEX_KEY = "2ee44819e9b4598845141067b281621874d0d5d7af9d8f7e00c1e54715b7d1e3"
API_KEY = HEX_KEY.encode()

REGION_LANG = {"ME":"ar","IND":"hi","ID":"id","VN":"vi","TH":"th","BD":"bn",
               "PK":"ur","TW":"zh","RU":"ru","SAC":"es","BR":"pt","NA":"pt",
               "SG":"pt","US":"pt"}

# ==================== HOMER SKILL IN-GAME (CMD 248) ====================
HOMER_SKILL_ENABLED  = True
HOMER_SKILL_ID       = 5506   # Homer Drone Skill
HOMER_SKILL_COOLDOWN = 90.0   # প্রতি ৩০ সেকেন্ড পর পর ফায়ার হবে

async def build_homer_skill_packet(key_bytes, mask, player_id, tick=0):
    """
    C2S_RUDP_UseActiveSkill_Req (Cmd 248):
    Body = player_id (uleb) + skill_id (5506 uleb) + tick (uleb) + 6 zero bytes
    """
    body = bytearray()
    body += await uleb_encode(int(player_id))
    body += await uleb_encode(int(HOMER_SKILL_ID))
    body += await uleb_encode(int(tick))
    body += b"\x00" * 6

    ru_layout = (await layouts_from_mask(mask))[0]  # RUDP Layout
    return await build_packet(0x5E, ru_layout, 2, 248, 0, 1, bytes(body), key_bytes, encrypted=True)

async def homer_skill_loop(sock, ip, port, key_bytes, mask, state, stop_event, label=""):
    loop = asyncio.get_event_loop()

    # ১. প্লেয়ার গেমের ভেতর স্পন হওয়া ও স্লট শনাক্ত হওয়ার অপেক্ষা
    while not stop_event.is_set():
        if state.slot is not None or getattr(state, "player_id", None) is not None:
            break
        try:
            await asyncio.wait_for(stop_event.wait(), timeout=0.5)
            return
        except asyncio.TimeoutError:
            pass

    # ২. ম্যাচ শুরু হওয়ার পর প্রথম ড্রোন ছাড়ার আগে ৭ সেকেন্ড অপেক্ষা (ফাইট শুরু হওয়া পর্যন্ত)
    try:
        await asyncio.wait_for(stop_event.wait(), timeout=7.0)
        return
    except asyncio.TimeoutError:
        pass

    # ৩. নিয়মিত কুলডাউন অনুযায়ী ড্রোন ফায়ার লুপ
    while not stop_event.is_set():
        now = time.time()
        pid = getattr(state, "player_id", None) or ((1 << 24) | int(state.slot if state.slot is not None else 1))
        tick = int((now - state.session_start) * 1000)

        try:
            pkt = await build_homer_skill_packet(key_bytes, mask, pid, tick)
            await loop.sock_sendto(sock, pkt, (ip, port))
            print_premium(f"{label} ⚡ Homer Drone Released! (Skill 5506 | PID 0x{pid:08X})",
                          color=PX.CYAN, icon=I["bolt"])
        except Exception as e:
            print_warning(f"[SKILL]{label} Homer cast error: {e}")

        # ৩০ সেকেন্ড কুলডাউন অপেক্ষা
        try:
            await asyncio.wait_for(stop_event.wait(), timeout=HOMER_SKILL_COOLDOWN)
        except asyncio.TimeoutError:
            pass

class PX:
    """Premium 256-color palette — unique, never-seen-before."""
    RESET   = "\033[0m"
    BOLD    = "\033[1m"
    DIM     = "\033[2m"
    ITALIC  = "\033[3m"
    UNDER   = "\033[4m"
    BLINK   = "\033[5m"

    GOLD    = "\033[38;5;220m"
    AMBER   = "\033[38;5;214m"
    ROSE    = "\033[38;5;204m"
    MAGENTA = "\033[38;5;200m"
    VIOLET  = "\033[38;5;135m"
    INDIGO  = "\033[38;5;99m"
    CYAN    = "\033[38;5;51m"
    TEAL    = "\033[38;5;44m"
    MINT    = "\033[38;5;121m"
    LIME    = "\033[38;5;118m"
    EMERALD = "\033[38;5;48m"
    SKY     = "\033[38;5;117m"
    SLATE   = "\033[38;5;245m"
    SILVER  = "\033[38;5;250m"
    WHITE   = "\033[38;5;255m"
    CRIMSON = "\033[38;5;197m"
    CORAL   = "\033[38;5;209m"
    PEACH   = "\033[38;5;216m"
    BG_DARK = "\033[48;5;236m"

I = {
    "ok":"◈","err":"◇","warn":"◉","info":"◎","star":"✦","spark":"✧",
    "dot":"•","arrow":"▸","check":"✔","cross":"✘","bolt":"⚡","flame":"🔥",
    "gem":"💎","crown":"👑","shield":"🛡","rocket":"🚀","target":"🎯","pulse":"◐",
}

def _ts(): return datetime.now().strftime("%H:%M:%S")

def _fmt(msg, color, icon, tag, level_style=""):
    ts    = f"{PX.SLATE}{_ts()}{PX.RESET}"
    badge = f"{color}{PX.BOLD}╭─{icon}─╮{PX.RESET}"
    label = f"{color}{PX.BOLD}{tag}{PX.RESET}"
    body  = f"{level_style}{PX.SILVER}{msg}{PX.RESET}"
    return f"{ts} {badge} {label} {PX.DIM}{PX.SLATE}▸{PX.RESET} {body}"

def print_success(t):
    print(_fmt(t, PX.EMERALD, I["ok"], "OK   "))
    try: bot_state.log(t, "success")
    except Exception: pass

def print_error(t):
    print(_fmt(t, PX.CRIMSON, I["err"], "FAIL "))
    try: bot_state.log(t, "error")
    except Exception: pass

def print_warning(t):
    print(_fmt(t, PX.AMBER, I["warn"], "WARN "))
    try: bot_state.log(t, "warning")
    except Exception: pass

def print_info(t):
    print(_fmt(t, PX.CYAN, I["info"], "INFO "))
    try: bot_state.log(t, "info")
    except Exception: pass

def print_premium(t, color=PX.GOLD, icon=I["star"], tag="EVENT"):
    print(_fmt(t, color, icon, f"{tag:<5}"))
    try: bot_state.log(t, "info")
    except Exception: pass

def print_rule(title="", width=72, color=PX.VIOLET):
    if title:
        pad = max(0, width - len(title) - 6)
        left = pad // 2; right = pad - left
        print(f"{color}{'═'*left}❰ {PX.BOLD}{title}{PX.RESET}{color} ❱{'═'*right}{PX.RESET}")
    else:
        print(f"{color}{'═'*width}{PX.RESET}")

def print_box(title, lines, color=PX.GOLD, width=68):
    print(f"{color}╔{'═'*(width-2)}╗{PX.RESET}")
    print(f"{color}║ {PX.BOLD}{title.center(width-4)}{PX.RESET}{color} ║{PX.RESET}")
    print(f"{color}╟{'─'*(width-2)}╢{PX.RESET}")
    for l in lines:
        body = str(l)[:width-4]
        print(f"{color}║{PX.RESET} {PX.SILVER}{body:<{width-4}}{PX.RESET} {color}║{PX.RESET}")
    print(f"{color}╚{'═'*(width-2)}╝{PX.RESET}")

def print_banner():
    R = PX.RESET; b = PX.BOLD
    gold, rose, cyan, violet, silver, teal = PX.GOLD, PX.ROSE, PX.CYAN, PX.VIOLET, PX.SILVER, PX.TEAL
    print()
    print(f"{violet}    ╔══════════════════════════════════════════════════════════╗{R}")
    print(f"{violet}    ║{R}   {gold}{b}✦  M A H I R   ✦{R}   {rose}{b}P R E M I U M{R}   {violet}║{R}")
    print(f"{violet}    ╠══════════════════════════════════════════════════════════╣{R}")
    print(f"{violet}    ║{R}   {cyan}▸ FREE FIRE 4-BOT SQUAD ENGINE{R}                          {violet}║{R}")
    print(f"{violet}    ║{R}   {silver}▸ Auto Create · Anti-AFK · Multi-Region · Team{R}          {violet}║{R}")
    print(f"{violet}    ║{R}   {teal}▸ Engine v2.0  ·  Python 3.10+{R}                         {violet}║{R}")
    print(f"{violet}    ╚══════════════════════════════════════════════════════════╝{R}")
    print(f"{PX.SLATE}            All rights reserved.{R}")
    print()

# ==================== STATE ====================
class BotState:
    def __init__(self):
        self.accounts: Dict[str, dict] = {}
        self.account_credentials: Dict[str, dict] = {}
        self.account_workers: Dict[str, asyncio.Task] = {}
        self.auth_to_game_id: Dict[str, str] = {}
        self.game_to_auth_id: Dict[str, str] = {}
        self.account_token_map: Dict[str, str] = {}
        self.paused: set = set()
        self.writers: Dict[str, list] = {}
        self.logs: List[dict] = []
        self.total_matches = 0
        self.matches_started = 0
        self.total_exp_gained = 0
        self.create_progress: List[str] = []
        self.creating = False
        self.start_time = time.time()
        self._writer_lock = asyncio.Lock()

    def log(self, msg, level="info"):
        try:
            t = datetime.now().strftime("%H:%M:%S")
            self.logs.append({"t": time.time(), "time": t, "message": str(msg), "level": level})
            if len(self.logs) > 500:
                self.logs = self.logs[-500:]
        except Exception: pass

    def register_account(self, uid, nickname, region="ID", level=1, exp=0,
                         likes=0, token=None, auth_uid=None, squad_id="A"):
        uid = str(uid)
        existing = self.accounts.get(uid, {})
        self.accounts[uid] = {
            "uid": uid, "nickname": nickname, "region": region,
            "level": level, "exp": exp, "likes": likes,
            "token": token, "auth_uid": auth_uid,
            "squad_id": (squad_id or "A").upper(),
            "status": "ONLINE", "current_exp": exp,
            "initial_exp": existing.get("initial_exp", exp),
            "gained_exp": existing.get("gained_exp", 0),
            "matches": existing.get("matches", 0),
            "active_matches": 0,
            "uptime_seconds": existing.get("uptime_seconds", 0),
            "last_match_time": existing.get("last_match_time", "Running..."),
            "is_paused": False,
        }

    def update_status(self, uid, status, matches=0):
        uid = str(uid)
        if uid in self.accounts:
            self.accounts[uid]["status"] = status
            self.accounts[uid]["active_matches"] = matches
            self.accounts[uid]["is_paused"] = (status == "PAUSED")

    def update_exp(self, uid, exp, level=None):
        uid = str(uid)
        if uid in self.accounts:
            a = self.accounts[uid]
            old = a.get("current_exp", 0)
            if exp > old:
                a["gained_exp"] = a.get("gained_exp", 0) + (exp - old)
                self.total_exp_gained += (exp - old)
            a["current_exp"] = exp; a["exp"] = exp
            if level: a["level"] = level

    def increment_match(self, uid):
        self.total_matches += 1
        uid = str(uid)
        if uid in self.accounts:
            self.accounts[uid]["matches"] = self.accounts[uid].get("matches", 0) + 1
            self.accounts[uid]["last_match_time"] = datetime.now().strftime("%H:%M:%S")

    def increment_match_started(self): self.matches_started += 1
    def register_writer(self, uid, w): self.writers.setdefault(str(uid), []).append(w)
    def unregister_writer(self, uid, w):
        try: self.writers.get(str(uid), []).remove(w)
        except Exception: pass
    def close_writers_for_account(self, uid):
        for w in list(self.writers.get(str(uid), [])):
            try: w.close()
            except Exception: pass
        self.writers[str(uid)] = []
    def is_paused(self, uid): return str(uid) in self.paused
    def toggle_pause(self, uid, state):
        uid = str(uid)
        if state:
            self.paused.add(uid)
            if uid in self.accounts:
                self.accounts[uid]["is_paused"] = True
                self.accounts[uid]["status"] = "PAUSED"
        else:
            self.paused.discard(uid)
            if uid in self.accounts:
                self.accounts[uid]["is_paused"] = False
                if self.accounts[uid].get("status") == "PAUSED":
                    self.accounts[uid]["status"] = "ONLINE"

bot_state = BotState()

# ==================== MULTI-SQUAD TEAM STATE ====================
_teams_state: Dict[str, dict] = {}

def _get_team(group_id: str = "A") -> dict:
    gid = str(group_id or "A").upper()
    if gid not in _teams_state:
        _teams_state[gid] = {
            "peers": {}, "leader_uid": None, "team_code": None,
            "lock": asyncio.Lock(),
            "triggered": False, "squad_id": gid,
        }
    return _teams_state[gid]

def _group_for_index(idx: int) -> str:
    """4 জন = Group A, 4 জন = Group B ..."""
    return chr(65 + (idx // TEAM_SIZE))

def _all_teams_snapshot() -> List[dict]:
    out = []
    for gid in sorted(_teams_state.keys()):
        t = _teams_state[gid]
        out.append({
            "group": gid, "size": len(t["peers"]),
            "leader_uid": t["leader_uid"], "team_code": t["team_code"],
            "members": list(t["peers"].keys()),
        })
    return out

def _assign_squad_for_new_account() -> str:
    """Smallest group letter with fewer than TEAM_SIZE accounts, else new group."""
    counts: Dict[str, int] = {}
    for a in bot_state.accounts.values():
        gid = str(a.get("squad_id", "A") or "A").upper()
        counts[gid] = counts.get(gid, 0) + 1
    for i in range(26):
        gid = chr(65 + i)
        if counts.get(gid, 0) < TEAM_SIZE:
            return gid
    return "A"


# --- Auto Equip Workflow (Bangladesh Server: clientbp.ppmainecoonghj.com) ---
async def send_debug_request_async(http_client, url, host_domain, jwt_token, hex_body, step_name,
                                   release_ver="OB55", hide_response=False):
    headers = {
        "Accept": "*/*",
        "Accept-Encoding": "deflate, gzip",
        "Authorization": f"Bearer {jwt_token.strip()}",
        "Content-Type": "application/x-www-form-urlencoded",
        "Host": host_domain,
        "ReleaseVersion": str(release_ver or "OB55"),
        "User-Agent": "UnityPlayer/2018.4.12f1 (UnityWebRequest/1.0, libcurl/8.5.0-DEV)",
        "X-GA": "v1 1",
        "X-GA-SV": str(int(time.time())),
        "X-Unity-Version": "2018.4.12f1",
    }
    try:
        body_bytes = bytes.fromhex(hex_body.replace(" ", ""))
        response = await http_client.post(url, headers=headers, content=body_bytes)
        if not hide_response:
            print_success(f"[EQUIP] '{step_name}' OK (Status: {response.status_code})")
    except Exception as e:
        print_error(f"[EQUIP] '{step_name}' failed: {e}")

async def run_equip_workflow(jwt_token: str, server_url: str = "https://clientbp.ppmainecoonghj.com",
                             release_ver: str = "OB55"):
    if not jwt_token:
        return
    print_info("[EQUIP] Starting automated equip & reward claims on BD server...")

    base_url = (server_url or "https://clientbp.ppmainecoonghj.com").rstrip("/")
    host_domain = base_url.replace("https://", "").replace("http://", "").split("/")[0]

    async with httpx.AsyncClient(verify=False, timeout=10.0) as http_client:
        tasks = [
            ("ClaimFreshSigninRewards", "E99FFFD90468992B08E3BFDB08D3B9B9", False),
            ("GetStore", "10 F8 74 30 DC 6A CA CA 32 FC 2B 44 79 72 3A 74", True),
            ("GiveAccountNewbieRoles", "EC 91 18 3D EF 30 AA 26 FA EF 2B BB EB 31 37 89", False),
            ("SelectPresetLoadout", "52 02 F0 D7 5C EC 74 F6 81 E1 F3 30 78 81 D2 72 58 D9 40 BB 98 81 E9 55 9B 4D 07 CA 4A A0 C5 D9 70 0A 7F C3 61 C0 A0 6E AF 6E 91 C0 E8 41 C0 C7 75 12 AC FF FC 25 04 77 99 08 77 26 B0 42 7A 88", False),
            ("ClaimAvatarProficiencyAward", "27D278C557914A29991290FC2DC8F6D2", False),
            ("ChooseHeadPic", "9BB7A317CD235254FED71EC2EBA1E718", False),
            ("ChooseEmote", "CAF683222A25C7BEFEB51F59544DB313", False),
            ("ClaimFreshActivityRewards", "ADC5827D0CA24022A802A9F2C529FD7D", False),
            ("ChooseBanner", "A230C31BDAD89C7AA0EF786068997E07", False),
        ]

        for step_name, hex_body, hide in tasks:
            target_url = f"{base_url}/{step_name}"
            await send_debug_request_async(
                http_client, target_url, host_domain, jwt_token, hex_body,
                step_name, release_ver=release_ver, hide_response=hide
            )
            await asyncio.sleep(0.3)

    print_success("[EQUIP] All equip tasks completed!")

# --- Homer Wire Builder ---
def _enc_vi(n: int) -> bytes:
    if n < 0: n = (1 << 64) + n
    r = bytearray()
    while n > 0x7F:
        r.append((n & 0x7F) | 0x80); n >>= 7
    r.append(n & 0x7F)
    return bytes(r)

def pb_v(f: int, v: int) -> bytes:
    return _enc_vi((f << 3) | 0) + _enc_vi(v)

def pb_l(f: int, v) -> bytes:
    if isinstance(v, str): v = v.encode()
    return _enc_vi((f << 3) | 2) + _enc_vi(len(v)) + v

def build_homer_wire(preset_id: int = 1, name: str = "MAHIR") -> bytes:
    char_id = 102000037  # Homer
    act_id = 5506        # Senses Shockwave
    passives = [706, 4806, 4106]  # Kelly, Chrono, D-Bee

    f1 = pb_v(1, char_id)
    f2 = bytearray()
    f2 += pb_v(1, char_id) + pb_l(2, b"".join(_enc_vi(i) for i in range(4)))
    sk = [act_id] + passives
    f2 += pb_l(3, b"".join(_enc_vi(s) for s in sk))
    f2 += pb_l(4, b"".join(_enc_vi(0) for _ in range(4)))

    en = bytearray()
    en += pb_v(1, preset_id) + pb_v(2, char_id)
    s0 = pb_v(2, act_id)
    en += pb_l(3, bytes(s0))
    for idx, s in enumerate(passives, 1):
        en += pb_l(3, bytes(pb_v(1, idx) + pb_v(2, s)))
    en += pb_l(6, name)

    root = bytearray()
    root += pb_l(1, bytes(f1)) + pb_l(2, bytes(f2))
    root += pb_l(6, pb_l(1, bytes(en))) + pb_v(11, 1)
    return bytes(root)

# --- Homer Equip Function ---
async def equip_homer_async(jwt_token: str, server_url: str, release_ver: str = "OB55") -> bool:
    if not jwt_token or not server_url: return False
    base_url = server_url.rstrip("/")
    host = base_url.replace("https://", "").replace("http://", "").split("/")[0]
    headers = {
        "User-Agent": "UnityPlayer/2018.4.12f1",
        "Connection": "Keep-Alive",
        "Content-Type": "application/x-www-form-urlencoded",
        "Authorization": f"Bearer {jwt_token.strip()}",
        "Host": host,
        "ReleaseVersion": release_ver,
        "X-GA": "v1 1",
        "X-GA-SV": str(int(time.time())),
        "Accept": "*/*",
    }
    ssl_ctx = ssl.create_default_context()
    ssl_ctx.check_hostname = False
    ssl_ctx.verify_mode = ssl.CERT_NONE

    async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=15)) as session:
        try:
            # Newbie Role Groups Unlock
            for g in [1, 2, 3, 4, 7, 8, 9, 10]:
                payload = bytes.fromhex(encrypt_aes(create_proto({1: g}).hex()))
                await session.post(f"{base_url}/GiveAccountNewbieRoles", headers=headers, data=payload, ssl=ssl_ctx)
                await asyncio.sleep(0.05)

            # Preset 1 & 50 তে Homer Equip করা
            for pid in (1, 50):
                wire = build_homer_wire(preset_id=pid)
                payload = bytes.fromhex(encrypt_aes(wire.hex()))
                await session.post(f"{base_url}/SelectPresetLoadout", headers=headers, data=payload, ssl=ssl_ctx)
                await asyncio.sleep(0.1)
            return True
        except Exception:
            return False

# --- Bio Change Functions ---
def create_bio_payload(bio_text):
    if not bio_text:
        bio_text = "[C][B]POWER OFF MAHIR"
    if len(bio_text) > 300:
        bio_text = bio_text[:300]
    fields = {5: "", 6: "", 8: bio_text, 9: 1, 11: "", 12: "", 16: ""}
    return bytes.fromhex(encrypt_aes(create_proto(fields).hex()))

async def change_bio(jwt_token, bio_text, server_url=None):
    if not jwt_token or not bio_text:
        return False
    base = (server_url or "https://clientbp.ppmainecoonghj.com").rstrip("/")
    url = f"{base}/UpdateSocialBasicInfo"
    host = base.replace("https://", "").replace("http://", "").split("/")[0]
    headers = {
        "Accept": "*/*",
        "Authorization": f"Bearer {jwt_token}",
        "Content-Type": "application/x-www-form-urlencoded",
        "ReleaseVersion": "OB55",
        "User-Agent": "UnityPlayer/2018.4.12f1",
        "Host": host,
        "X-GA": "v1 1",
        "X-GA-SV": str(int(time.time())),
        "X-Unity-Version": "2018.4.12f1",
    }
    try:
        payload = create_bio_payload(bio_text)
        ssl_ctx = ssl.create_default_context()
        ssl_ctx.check_hostname = False
        ssl_ctx.verify_mode = ssl.CERT_NONE
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=10)) as s:
            async with s.post(url, headers=headers, data=payload, ssl=ssl_ctx) as r:
                return r.status == 200
    except Exception:
        return False

_squad_restart_states: Dict[str, dict] = {}

def _get_squad_restart(group_id: str = "A") -> dict:
    gid = str(group_id or "A").upper()
    if gid not in _squad_restart_states:
        _squad_restart_states[gid] = {
            "lock": asyncio.Lock(),
            "finished_bots": set(),
            "target": None,
            "restarting": False,
            "seq": 0,
        }
    return _squad_restart_states[gid]

async def _schedule_squad_restart(group_id: str):
    gid = str(group_id or "A").upper()
    await asyncio.sleep(3.0)
    st = _get_squad_restart(gid)
    async with st["lock"]:
        st["seq"] += 1
        st["finished_bots"].clear()
        st["target"] = None
        st["restarting"] = False
    print_warning(f"[RESTART-{gid}] 🔄 Squad {gid} restarting now (other squads untouched)...")

async def _mark_bot_match_finished(account_id, squad_id: Optional[str] = None):
    uid_str = str(account_id)
    if not squad_id:
        acc = bot_state.accounts.get(uid_str, {})
        squad_id = acc.get("squad_id", "A")
    gid = str(squad_id or "A").upper()
    st = _get_squad_restart(gid)

    async with st["lock"]:
        if st["restarting"]:
            return
        st["finished_bots"].add(uid_str)
        n_done = len(st["finished_bots"])
        if st["target"] is None:
            active_ids = {
                uid for uid, a in bot_state.accounts.items()
                if str(a.get("squad_id", "A") or "A").upper() == gid
                and a.get("status") not in ("OFFLINE", "PAUSED")
            }
            st["target"] = max(1, min(TEAM_SIZE, len(active_ids))) if active_ids else TEAM_SIZE
        target = st["target"]
        print_success(f"[RESTART-{gid}] {uid_str} → {n_done}/{target}")
        if n_done >= target:
            st["restarting"] = True
            print_warning(f"[RESTART-{gid}] ✅ Squad {gid} ({target} bots) done! Restart in 3s...")
            asyncio.create_task(_schedule_squad_restart(gid))

_no_match_state = {"lock": asyncio.Lock(), "global_last_match": None, "restart_triggered": False}
async def _mark_match_found(account_id=None):
    async with _no_match_state["lock"]:
        _no_match_state["global_last_match"] = time.time()

_ALLOWED_RESTART_STATUSES = {"ONLINE", "SEARCHING"}
_team_stuck_state = {"lock": asyncio.Lock(), "in_team_since": {}, "triggered": False}

async def _mark_team_joined(uid, group_id="A"):
    uid = str(uid); gid = str(group_id or "A").upper()
    async with _team_stuck_state["lock"]:
        if uid not in _team_stuck_state["in_team_since"]:
            _team_stuck_state["in_team_since"][uid] = {"since": time.time(), "group": gid}
            print_info(f"[TEAM-STUCK-{gid}] {uid} JOINED")

async def _clear_team_joined(uid):
    uid = str(uid)
    async with _team_stuck_state["lock"]:
        if uid in _team_stuck_state["in_team_since"]:
            del _team_stuck_state["in_team_since"][uid]

async def _team_member_count(group_id=None) -> int:
    if group_id is None:
        return sum(len(t["peers"]) for t in _teams_state.values())
    t = _get_team(group_id)
    async with t["lock"]:
        return len(t["peers"])

def _all_bots_are_online_or_searching() -> bool:
    active_statuses = []
    for uid, acc in bot_state.accounts.items():
        status = str(acc.get("status", "")).upper().strip()
        if status in ("", "OFFLINE"): continue
        active_statuses.append(status)
    if not active_statuses: return False
    return all(st in _ALLOWED_RESTART_STATUSES for st in active_statuses)

def _any_bot_in_match() -> bool:
    for uid, acc in bot_state.accounts.items():
        if "IN_MATCH" in str(acc.get("status", "")).upper(): return True
    return False

async def _no_match_watchdog():
    if not NO_MATCH_RESTART_ENABLED: return
    await asyncio.sleep(NO_MATCH_RESTART_GRACE)
    async with _no_match_state["lock"]:
        if _no_match_state["global_last_match"] is None:
            _no_match_state["global_last_match"] = time.time()
    print_info(f"[NO-MATCH] watchdog aktif timeout={NO_MATCH_RESTART_TIMEOUT:.0f}s")
    while True:
        await asyncio.sleep(10.0)
        try:
            if any(s["restarting"] for s in _squad_restart_states.values()):
                continue
            if _no_match_state["restart_triggered"]: return
            if _any_bot_in_match():
                async with _no_match_state["lock"]:
                    _no_match_state["global_last_match"] = time.time()
                async with _team_stuck_state["lock"]:
                    now = time.time()
                    for info in _team_stuck_state["in_team_since"].values():
                        info["since"] = now
                continue
            now = time.time()
            # per-group stuck check
            for gid in list(_teams_state.keys()):
                team = _get_team(gid)
                async with team["lock"]:
                    if team["triggered"]: continue
                    if not team["peers"]: continue
                    stuck = sum(
                        1 for uid, info in _team_stuck_state["in_team_since"].items()
                        if info.get("group") == gid and uid in team["peers"]
                        and now - info["since"] >= NO_MATCH_RESTART_TIMEOUT
                    )
                    if stuck and len(team["peers"]) >= TEAM_SIZE:
                        team["triggered"] = True
                        msg = f"[TEAM-STUCK-{gid}] {stuck} bot no match ≥{NO_MATCH_RESTART_TIMEOUT:.0f}s"
                        print_warning(msg); bot_state.log(msg, "warning")
                        st = _get_squad_restart(gid)
                        async with st["lock"]:
                            if not st["restarting"]:
                                st["restarting"] = True
                                asyncio.create_task(_schedule_squad_restart(gid))
            if not _all_bots_are_online_or_searching():
                async with _no_match_state["lock"]:
                    _no_match_state["global_last_match"] = time.time()
                continue
            async with _no_match_state["lock"]:
                last = _no_match_state["global_last_match"] or 0
            elapsed = time.time() - last
            if elapsed >= NO_MATCH_RESTART_TIMEOUT:
                if not _all_bots_are_online_or_searching(): continue
                async with _no_match_state["lock"]:
                    if _no_match_state["restart_triggered"]: continue
                    _no_match_state["restart_triggered"] = True
                msg = f"[NO-MATCH] No match for {elapsed:.0f}s → restart stuck squads!"
                print_warning(msg); bot_state.log(msg, "warning")
                for gid in list(_teams_state.keys()):
                    st = _get_squad_restart(gid)
                    async with st["lock"]:
                        if not st["restarting"]:
                            st["restarting"] = True
                            asyncio.create_task(_schedule_squad_restart(gid))
                return
        except Exception as e:
            print_warning(f"[NO-MATCH] error: {e}")

async def _schedule_restart():
    await asyncio.sleep(3.0)
    print_warning("[RESTART] 🔄 Executing full process restart...")
    try: sys.stdout.flush(); sys.stderr.flush()
    except Exception: pass
    try: os.execv(sys.executable, [sys.executable] + sys.argv)
    except Exception as e:
        print_error(f"[RESTART] execv failed: {e}")
        try:
            subprocess.Popen([sys.executable] + sys.argv); os._exit(0)
        except Exception as e2:
            print_error(f"[RESTART] subprocess: {e2}"); os._exit(1)

# ── Backward-compat alias (পুরনো কোডে C.GREEN ইত্যাদি ব্যবহৃত হলে) ──
class C:
    GREEN=PX.EMERALD; FAIL=PX.CRIMSON; WARNING=PX.AMBER
    CYAN=PX.CYAN; MAGENTA=PX.MAGENTA; WHITE=PX.WHITE; ENDC=PX.RESET

GGRE_RAW = bytes.fromhex(
    "47475245010101006d020000b260ee08e1f86b4c57f9c70f86bba26ed5d1436bcf52e142db3249d905eded757764991ca31a8373cdd26eab91b80f3f1f6f262f4f10b895d7b6937ddba30a27197453890e9da49373f736c679b8254e2f8e1623e91084a5fdd5374fe478ff99e010834553fddeb0bec4018d142e49df9bb236675b67e852f92a43586f7a7d4d0d7a197a1d4da32714dab4d069ad53214e2c33b3877420a12459738c4c619cbd815fa878bbd104776bb3e1ac7818d5397b04a666ac57f682763ff2df31bc2f846ddc7904f3dce1bda0c4b01f9698e9166f98c84f92640abe3f6317834a42e5c12573b46842c1a6ea8fe6ca9c006dca48a2087e1f983dfb5692771e4a0b15b337ad669b1d08b40862b176bace5331b49a767375b1a8469012aa70a67b55fe71b72478201d0b3ac7269c064c960361e92ee7ba8a42cc6b582bf9b965fb388fa9172ad44c4b073ac23c02080a6bcd106b691ffdf4c7cf71e42f2063fcf196e9bddc5e85be1fe5048eb1b31b460efbb46d76195eef9904c4cba326f2e17ff51fec17dd965aa06dadd4ab07d6966e4a7c38e8afd66dfde56c872bb87516a8f7313c797e4d80e5ad4a5f7afad95c1e0449254adae052e71a3fb98399f93ab30848e0d23252dd45e6fd41bc5fa7303dfb846a8fd713a0032a0b0ae96dfba1bbe41d20abd8099e2cb7fccc329d25bd153029139ef05d090a5093ea557693c0a8d491395b8a23ca844b3887dd5dfc29ac06f4b9be87883a793211b973465e2644c4f5de02b8ab01571401203fc2740423826858cc6da0194c195d27aac4ec4b9d23d506c1501d06440aca3fc180926d75d4a004d3dff21eb4ea1e8c86e6c9627248eff953e1d192d5c8efc006a7e512388ef2ebdb72ee3ad42d719f28e8f994e12ebf4c79f2ffe3abd7408ccd2236a7b89b2606247a732c10c4"
)

def _encode_proto_std(fields):
    out = b""
    for f in sorted(fields.keys()):
        v = fields[f]
        if isinstance(v, bool):
            out += encode_varint((f << 3) | 0) + encode_varint(int(v))
        elif isinstance(v, int):
            out += encode_varint((f << 3) | 0) + encode_varint(v)
        elif isinstance(v, (str, bytes)):
            if isinstance(v, str): v = v.encode()
            out += encode_varint((f << 3) | 2) + encode_varint(len(v)) + v
    return out

# ==================== DEVICE ====================
def _generate_new_device() -> dict:
    device_list = [
        ("Samsung","SM-G998B","Adreno (TM) 660","Android OS 12 / API-31"),
        ("Xiaomi","2201122G","Adreno (TM) 730","Android OS 13 / API-33"),
        ("Realme","RMX3700","Mali-G710","Android OS 14 / API-34"),
        ("OnePlus","CPH2451","Adreno (TM) 740","Android OS 13 / API-33"),
        ("OPPO","CPH2611","Adreno (TM) 720","Android OS 14 / API-34"),
    ]
    brand, model, gpu, os_ver = random.choice(device_list)
    return {"unique_device_id":f"Google|{uuid.uuid4()}","brand":brand,"model":model,
            "gpu_renderer":gpu,"system_software":os_ver,
            "screen_width":random.choice([1080,1440,720]),
            "screen_height":random.choice([2400,3200,1600]),
            "screen_dpi":str(random.randint(300,420)),
            "memory":random.randint(2800,6500)}

def get_device_for_account(acc_key: str) -> dict:
    devices = {}
    if os.path.exists(DEVICES_FILE):
        try:
            with open(DEVICES_FILE,"r",encoding="utf-8") as f:
                devices = json.load(f)
                if not isinstance(devices, dict): devices = {}
        except Exception: devices = {}
    if acc_key in devices: return devices[acc_key]
    nd = _generate_new_device(); devices[acc_key] = nd
    try:
        with open(DEVICES_FILE,"w",encoding="utf-8") as f:
            json.dump(devices, f, indent=2)
    except Exception: pass
    return nd

def encode_f14(s):
    ks = [0x30,0x30,0x30,0x32,0x30,0x31,0x37,0x30,
          0x30,0x30,0x30,0x30,0x32,0x30,0x31,0x37,
          0x30,0x30,0x30,0x30,0x30,0x32,0x30,0x31,
          0x37,0x30,0x30,0x30,0x30,0x30,0x32,0x30]
    return bytes(ord(c) ^ ks[i % len(ks)] for i, c in enumerate(s))

# ==================== DNS ====================
_DNS_CACHE: Dict[str, Tuple[str,float]] = {}
_DNS_CACHE_TTL = 300.0

async def resolve_host_cloudflare(hostname: str) -> str:
    if not hostname: return hostname
    parts = hostname.split('.')
    if len(parts)==4 and all(p.isdigit() for p in parts): return hostname
    now = time.time()
    if hostname in _DNS_CACHE:
        ip, exp = _DNS_CACHE[hostname]
        if now < exp: return ip
    try:
        loop = asyncio.get_running_loop()
        info = await loop.getaddrinfo(hostname, None, family=socket.AF_INET)
        if info:
            ip = info[0][4][0]
            _DNS_CACHE[hostname] = (ip, now + _DNS_CACHE_TTL); return ip
    except Exception: pass
    return hostname

def optimize_tcp_socket(sock):
    try:
        sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_KEEPALIVE, 1)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 131072)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_SNDBUF, 131072)
    except Exception: pass

async def safe_close_writer(writer):
    if not writer: return
    try:
        if not writer.is_closing(): writer.close()
        await asyncio.wait_for(writer.wait_closed(), timeout=1.5)
    except Exception: pass

def optimize_udp_socket(sock):
    try:
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 131072)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_SNDBUF, 131072)
    except Exception: pass

client = httpx.AsyncClient(verify=False, timeout=15.0,
    limits=httpx.Limits(max_connections=300, max_keepalive_connections=150))
_LOGIN_SEMAPHORE = asyncio.Semaphore(4)

# ==================== CRYPTO ====================
CRC7_TABLE = bytes([
    0,9,18,27,36,45,54,63,72,65,90,83,108,101,126,119,
    25,16,11,2,61,52,47,38,81,88,67,74,117,124,103,110,
    50,59,32,41,22,31,4,13,122,115,104,97,94,87,76,69,
    43,34,57,48,15,6,29,20,99,106,113,120,71,78,85,92,
    100,109,118,127,64,73,82,91,44,37,62,55,8,1,26,19,
    125,116,111,102,89,80,75,66,53,60,39,46,17,24,3,10,
    86,95,68,77,114,123,96,105,30,23,12,5,58,51,40,33,
    79,70,93,84,107,98,121,112,7,14,21,28,35,42,49,56,
    65,72,83,90,101,108,119,126,9,0,27,18,45,36,63,54,
    88,81,74,67,124,117,110,103,16,25,2,11,52,61,38,47,
    115,122,97,104,87,94,69,76,59,50,41,32,31,22,13,4,
    106,99,120,113,78,71,92,85,34,43,48,57,6,15,20,29,
    37,44,55,62,1,8,19,26,109,100,127,118,73,64,91,82,
    60,53,46,39,24,17,10,3,116,125,102,111,80,89,66,75,
    23,30,5,12,51,58,33,40,95,86,77,68,123,114,105,96,
    14,7,28,21,42,35,56,49,70,79,84,93,98,107,112,121,
])
_DELTA = 0x9E3779B9
_ROUNDS = 16
_FIELD_SIZES = {0:1,1:2,2:2,3:1,4:2}
_FIELD_NAMES = {0:"sendOption",1:"cmd",2:"orderId",3:"flags",4:"length"}

def crc7_sync(data: bytes) -> int:
    c = 0
    for b in data:
        c = CRC7_TABLE[((2*(c & 0xFF)) ^ (b & 0xFF)) & 0xFF] & 0x7F
    return c & 0x7F

def encode_varint(n: int) -> bytes:
    out = bytearray()
    if n < 0: n &= 0xFFFFFFFFFFFFFFFF
    while True:
        b = n & 0x7F; n >>= 7
        if n: b |= 0x80
        out.append(b)
        if not n: break
    return bytes(out)

def _pb_varint(fn, val): return encode_varint((fn<<3)|0) + encode_varint(val)
def _pb_length(fn, val):
    enc = val.encode('utf-8') if isinstance(val,str) else val
    return encode_varint((fn<<3)|2) + encode_varint(len(enc)) + enc

def create_proto(fields) -> bytes:
    packet = bytearray()
    for field, value in fields.items():
        if isinstance(field, str): field = int(field)
        if isinstance(value, dict):
            packet.extend(_pb_length(field, bytes(create_proto(value))))
        elif isinstance(value, list):
            for item in value:
                if isinstance(item, dict):
                    packet.extend(_pb_length(field, bytes(create_proto(item))))
                elif isinstance(item, str):
                    packet.extend(_pb_length(field, item))
                elif isinstance(item, (bytes, bytearray)):
                    packet.extend(_pb_length(field, bytes(item)))
                elif isinstance(item, bool):
                    packet.extend(_pb_varint(field, 1 if item else 0))
                elif isinstance(item, int):
                    packet.extend(_pb_varint(field, item))
        elif isinstance(value, bool):
            packet.extend(_pb_varint(field, 1 if value else 0))
        elif isinstance(value, int):
            packet.extend(_pb_varint(field, value))
        elif isinstance(value, str):
            packet.extend(_pb_length(field, value))
        elif isinstance(value, (bytes, bytearray)):
            packet.extend(_pb_length(field, bytes(value)))
    return bytes(packet)

def encrypt_aes(hex_data: str) -> str:
    cipher = AES.new(AES_KEY, AES.MODE_CBC, AES_IV)
    return cipher.encrypt(pad(bytes.fromhex(hex_data), AES.block_size)).hex()

def decode_varint(data, offset):
    result = 0; shift = 0
    while offset < len(data):
        byte = data[offset]
        result |= (byte & 0x7F) << shift
        offset += 1
        if not (byte & 0x80): return result, offset
        shift += 7
    return None, offset

def decode_protobuf_2(data):
    result = {}; offset = 0; data_len = len(data)
    while offset < data_len:
        header, offset = decode_varint(data, offset)
        if header is None: break
        fn = header >> 3; wt = header & 0x7
        if wt == 0:
            v, offset = decode_varint(data, offset)
            if v is not None: result[fn] = v
        elif wt == 2:
            length, offset = decode_varint(data, offset)
            if length is None: break
            value = data[offset:offset+length]; offset += length
            try:
                s = value.decode('utf-8')
                result[fn] = s if s else value.hex()
            except UnicodeDecodeError:
                nested = decode_protobuf_2(value)
                result[fn] = nested if nested else value.hex()
        elif wt == 1: offset += 8
        elif wt == 3: offset += 4
        else: break
    return result

def extract_raw_fields(data: bytes) -> dict:
    result = {}; offset = 0; data_len = len(data)
    while offset < data_len:
        header, offset = decode_varint(data, offset)
        if header is None: break
        fn = header >> 3; wt = header & 0x7
        if wt == 0:
            v, offset = decode_varint(data, offset)
            if v is not None: result[fn] = v
        elif wt == 2:
            length, offset = decode_varint(data, offset)
            if length is None: break
            if offset + length > data_len: break
            result[fn] = bytes(data[offset:offset+length]); offset += length
        elif wt == 1: offset += 8
        elif wt == 3: offset += 4
        else: break
    return result

def _parse_results_sync(results):
    out = {}
    for r in results:
        fd = {"wire_type": r.wire_type}
        if r.wire_type == "varint": fd["data"] = r.data
        elif r.wire_type in ("string","bytes"): fd["data"] = r.data
        elif r.wire_type == "length_delimited":
            if hasattr(r.data, "results"): fd["data"] = _parse_results_sync(r.data.results)
            elif isinstance(r.data, list): fd["data"] = _parse_results_sync(r.data)
            else: fd["data"] = str(r.data)
        out[str(r.field)] = fd
    return out

def decode_protobuf_dict(data: bytes) -> dict:
    try:
        parsed = Parser().parse(data)
        return _parse_results_sync(parsed)
    except Exception: return {}

async def decode_protobuf_async(data):
    try:
        parsed = Parser().parse(data)
        return json.dumps(_parse_results_sync(parsed))
    except Exception: return "{}"

# ==================== ZIGZAG / ULEB ====================
async def has_ssan_zig(n: int) -> bytes:
    try: n = int(n)
    except Exception: n = 0
    z = (n << 1) & 0xFFFFFFFFFFFFFFFF
    out = bytearray()
    while z >= 0x80:
        out.append((z & 0x7F) | 0x80); z >>= 7
    out.append(z); return bytes(out)

async def uleb_encode(n: int) -> bytes:
    try: n = int(n)
    except Exception: n = 0
    if n < 0: n &= 0xFFFFFFFFFFFFFFFF
    out = bytearray()
    while True:
        b = n & 0x7F; n >>= 7
        if n: b |= 0x80
        out.append(b)
        if not n: break
    return bytes(out)

async def zigzag_encode_signed(n: int) -> bytes:
    try: n = int(n)
    except Exception: n = 0
    zz = (n << 1) ^ (n >> 63)
    if zz < 0: zz = -zz
    zz &= 0xFFFFFFFFFFFFFFFF
    out = bytearray()
    while True:
        b = zz & 0x7F; zz >>= 7
        if zz: b |= 0x80
        out.append(b)
        if not zz: break
    return bytes(out)

def create_packet(Pk, N, K, V):
    if isinstance(K, str): K = bytes.fromhex(K) if len(K)==32 else K.encode()
    if isinstance(V, str): V = bytes.fromhex(V) if len(V)==32 else V.encode()
    PkEnc = AES.new(K, AES.MODE_CBC, V).encrypt(pad(bytes.fromhex(Pk),16)).hex()
    L = len(PkEnc)//2
    hexlen = hex(L)[2:]
    if len(hexlen)%2 != 0: hexlen = '0'+hexlen
    total_pad = 12 - len(N) - len(hexlen)
    if total_pad < 0: total_pad = 0
    return bytes.fromhex(N + ('0'*total_pad) + hexlen + PkEnc)

# ==================== MOVEMENT ====================
async def build_movement_packet_2001(key_bytes, msg_key, player_state, x, y, z,
                                     tick, counter, move_state, account_uid,
                                     room_code, phase="game"):
    TAIL = (b"\x00"*7 + b"\x93\xca\xd5\xf9\x0b" +
            b"\x8e\xfe\xfc\xf7\x0b" +
            b"\xf4\xe0\xfe\xf7\x03" + b"\x00\x00")
    x_i = int(x); y_i = int(y); z_i = int(z)
    body = bytearray()
    body += await uleb_encode(int(account_uid))
    body += await uleb_encode(int(player_state))
    body += await zigzag_encode_signed(x_i)
    body += await zigzag_encode_signed(y_i)
    body += await zigzag_encode_signed(z_i)
    body += b"\x00"
    body += await uleb_encode(int(move_state))
    body += TAIL
    body += await uleb_encode(int(tick))
    body += b"\x00\x00\x00"
    body += await uleb_encode(int(counter))
    body = bytes(body)
    k = key_bytes[0]
    v80 = ((k << 8) | k) & 0xFFFF
    h = bytearray()
    h.append(msg_key & 0xFF); h.append(0x00); h.append(0x00 ^ k)
    h += ((2001 ^ v80) & 0xFFFF).to_bytes(2, "little")
    h += ((len(body) ^ v80) & 0xFFFF).to_bytes(2, "little")
    h.append(0x00 ^ k)
    h[1] = (await crc7_buff(0, bytes(h[2:]) + body)) & 0x7F
    return bytes(h) + body

async def send_newbie_character_tcp(writer, account_id, key, iv):
    if not ENABLE_NEWBIE_CHARACTER:
        return False
    print_info("[👤] Newbie select disabled")
    return False

# ==================== PER-ACCOUNT MOVEMENT STATE (from app.py) ====================
class AccountMoveState:
    def __init__(self, uid):
        self.uid = str(uid)
        self.target = None
        self.target_set_at = 0.0
        self.enemies = {}
        self.lock = asyncio.Lock()

_ACCOUNT_MOVE_STATES: Dict[str, AccountMoveState] = {}
_ACCOUNT_MOVE_LOCK = asyncio.Lock()

async def _get_account_move_state(uid):
    key = str(uid)
    async with _ACCOUNT_MOVE_LOCK:
        st = _ACCOUNT_MOVE_STATES.get(key)
        if st is None:
            st = AccountMoveState(key)
            _ACCOUNT_MOVE_STATES[key] = st
        return st

_enemy_bus = {"enemies": {}, "lock": asyncio.Lock()}

async def _enemy_bus_add(tag, pos):
    async with _enemy_bus["lock"]:
        _enemy_bus["enemies"][str(tag)] = {"pos": tuple(pos), "ts": time.time()}

async def _enemy_bus_snapshot():
    now = time.time()
    async with _enemy_bus["lock"]:
        fresh = {k: v for k, v in _enemy_bus["enemies"].items()
                 if now - v["ts"] < SQUAD_ENEMY_TTL}
        _enemy_bus["enemies"] = fresh
        return dict(fresh)

_account_slots = {"lock": asyncio.Lock(), "uid_to_slot": {}, "slots": set()}

async def _account_register_slot(uid, slot):
    if slot is None: return
    async with _account_slots["lock"]:
        _account_slots["uid_to_slot"][str(uid)] = int(slot)
        _account_slots["slots"].add(int(slot))

async def _account_is_teammate_slot(slot):
    if slot is None: return False
    async with _account_slots["lock"]:
        return int(slot) in _account_slots["slots"]

async def _account_set_target(uid, pos):
    st = await _get_account_move_state(uid)
    async with st.lock:
        st.target = tuple(pos)
        st.target_set_at = time.time()

async def _account_register_enemy(uid, tag, pos):
    st = await _get_account_move_state(uid)
    async with st.lock:
        st.enemies[str(tag)] = {"pos": tuple(pos), "ts": time.time()}
    await _enemy_bus_add(tag, pos)

async def _account_nearest_enemy(uid, from_pos):
    st = await _get_account_move_state(uid)
    now = time.time()
    own = {}
    async with st.lock:
        own = {k: v for k, v in st.enemies.items() if now - v["ts"] < SQUAD_ENEMY_TTL}
        st.enemies = own
    shared = await _enemy_bus_snapshot()
    merged = {**shared, **own}
    if not merged: return None
    best = None; best_d = float("inf")
    for _, v in merged.items():
        ex, _, ez = v["pos"]
        d = math.hypot(ex - from_pos[0], ez - from_pos[2])
        if d < best_d:
            best_d = d; best = v["pos"]
    return best

async def _account_get_target(uid):
    st = await _get_account_move_state(uid)
    async with st.lock:
        return st.target, st.target_set_at

async def _account_clear_target(uid, only_if=None):
    st = await _get_account_move_state(uid)
    async with st.lock:
        if only_if is None or st.target == only_if:
            st.target = None
            st.target_set_at = 0.0


# ==================== SIMPLE MOVEMENT (2001 PLAYER STATE SYNC - app.py) ====================
def read_varint(data: bytes, offset: int) -> Tuple[int, int]:
    r, s = 0, 0
    while True:
        if offset >= len(data):
            raise IndexError("offset out of bounds")
        b = data[offset]
        offset += 1
        r |= (b & 0x7F) << s
        if not (b & 0x80):
            break
        s += 7
    return r, offset


MSG_PLAYER_STATE_SYNC = next(
    (mid for mid, name in MESSAGE_ID_TO_NAME.items() if name == "UDP_PLAYER_STATE_SYNC"),
    2001,
)


async def zigzag_encode(n):
    z = ((n << 1) ^ (n >> 63)) & 0xFFFFFFFFFFFFFFFF
    return await uleb_encode(z)


def zigzag_decode(n):
    return (n >> 1) ^ -(n & 1)


def read_varints(buf):
    out = []
    off = 0
    while off < len(buf):
        v, off = read_varint(buf, off)
        out.append(v)
    return out


def float_to_u32(f):
    return struct.unpack("<I", struct.pack("<f", float(f) + 0.0))[0]


class MoveState:
    """Shared between play_game/play_game_cs receive loop and auto_move_loop."""

    def __init__(self):
        self.session_start = time.time()
        self.slot = None
        self.player_id = None
        self.server_pos = None
        self.server_physx_state = None
        self.server_vel_y = 0
        self.server_update_seq = 0
        self.pending_ack = None
        self.rtt_ms = None
        self.ping_sent = {}
        self.cmd_counts = collections.Counter()
        self.undecoded = 0
        self.last_2001_head = None
        self.owner_uid = None
        self.slot_registered = False
        self.enemy_positions = {}
        self.last_enemy_log = 0.0

    def diagnostics(self):
        top = ", ".join(f"{c}x{n}" for c, n in self.cmd_counts.most_common(10)) or "none"
        return (f"cmds[{top}] | undecoded {self.undecoded} | "
                f"2001 seq {self.server_update_seq} | slot {self.slot} | "
                f"enemies_known {len(self.enemy_positions)}")

    def on_server_frame(self, frame):
        self.cmd_counts[frame["cmd"]] += 1
        if frame.get("kind") == "RUDP" and frame.get("orderId") is not None:
            oid = frame["orderId"]
            if self.pending_ack is None or ((oid - self.pending_ack) & 0xFFFF) < 0x8000:
                self.pending_ack = oid

        # --- Cmd 101 থেকে Player ID পড়া (homer_skill_loop এর জন্য) ---
        if frame["cmd"] == 101:
            c = frame.get("content") or b""
            try:
                u_id, p = read_varint(c, 0)
                _samo, p = read_varint(c, p)
                self.player_id, p = read_varint(c, p)
            except Exception:
                pass

        if frame["cmd"] == MSG_PLAYER_STATE_SYNC:
            self._on_own_state(frame["content"] or b"")
        elif frame["cmd"] == 3:
            c = frame["content"] or b""
            if len(c) >= 4:
                sent = self.ping_sent.pop(struct.unpack_from("<I", c, 0)[0], None)
                if sent is not None:
                    self.rtt_ms = int((time.time() - sent) * 1000)

    def _on_own_state(self, content):
        try:
            v = read_varints(content)
        except Exception:
            self.last_2001_head = f"unparseable {content[:12].hex()}"
            return
        self.last_2001_head = v[:4]
        if len(v) < 16 or v[0] != 0 or v[1] != 2:
            return
        self.slot = v[2]
        self.server_pos = (zigzag_decode(v[3]), zigzag_decode(v[4]), zigzag_decode(v[5]))
        self.server_vel_y = zigzag_decode(v[12])
        self.server_physx_state = v[14]
        self.server_update_seq += 1
        if not self.slot_registered and self.owner_uid:
            self.slot_registered = True
            try:
                asyncio.create_task(_account_register_slot(self.owner_uid, self.slot))
            except Exception:
                pass
        try:
            self._try_parse_extra_players(v)
        except Exception:
            pass

    def _try_parse_extra_players(self, v):
        own = self.slot
        idx = 27
        hits = []
        while idx + 3 < len(v):
            slot = v[idx]
            if 1 <= slot <= 50 and slot != own:
                try:
                    px = zigzag_decode(v[idx+1])
                    py = zigzag_decode(v[idx+2])
                    pz = zigzag_decode(v[idx+3])
                    if (-10000 <= px <= 10000 and -2000 <= py <= 5000
                            and -10000 <= pz <= 10000):
                        hits.append((slot, (px, py, pz)))
                        idx += 4
                        continue
                except Exception:
                    pass
            idx += 1
        if hits:
            now = time.time()
            for slot, p in hits:
                self.enemy_positions[slot] = (p[0], p[1], p[2], now)
                try:
                    async def _push_if_enemy(s, pos):
                        if await _account_is_teammate_slot(s):
                            return
                        await _account_register_enemy(self.owner_uid, f"en{s}", pos)
                    asyncio.create_task(_push_if_enemy(slot, p))
                except Exception:
                    pass
            if now - self.last_enemy_log > 1.0:
                self.last_enemy_log = now
                print_info(f"[HUNT-PARSE {self.owner_uid}] {len(hits)} candidate(s) total={len(self.enemy_positions)}")


async def build_player_state_sync_2001(key_bytes, mask, msg_key, slot, pos, stick, move_input, vel,
                                     physx_state, physx_pose, facing, net_tick, counter_ms,
                                     ack_order=None):
    body = bytearray()
    body += await uleb_encode((1 << 24) | int(slot))
    for value in (*pos, *stick, *move_input, *vel):
        body += await zigzag_encode(int(round(value)))
    body += await uleb_encode(int(physx_state))
    body += await uleb_encode(int(physx_pose))
    for f in facing:
        body += await uleb_encode(float_to_u32(f))
    body += b"\x00\x00"
    body += await uleb_encode(int(net_tick))
    body += b"\x00\x00\x00"
    body += await uleb_encode(int(counter_ms))
    body = bytes(body)

    k = key_bytes[0]
    v80 = ((k << 8) | k) & 0xFFFF
    flags = 4 if ack_order is not None else 0
    nr = (await layouts_from_mask(mask))[1]
    hdr = bytearray([msg_key & 0xFF, 0])
    hdr += await encode_header(nr, 0, MSG_PLAYER_STATE_SYNC, None, flags, len(body), k, v80)
    if ack_order is not None:
        a = ((int(ack_order) & 0xFFFF) ^ v80) & 0xFFFF
        hdr += bytes([a & 0xFF, a >> 8, k])
    packet = bytearray(hdr + body)
    packet[1] = await crc7_buff(0, bytes(packet[2:])) & 0x7F
    return bytes(packet)


async def build_action_beacon_2002(key_bytes, mask, msg_key, slot, pos, action_type=1, ack_order=None):
    body = bytearray()
    body += await uleb_encode((2 << 24) | int(slot))
    body += await zigzag_encode(int(pos[0]))
    body += await zigzag_encode(int(pos[2]))
    body += await uleb_encode(int(action_type))
    body += b"\x00\x00"
    k = key_bytes[0]; v80 = ((k << 8) | k) & 0xFFFF
    nr = (await layouts_from_mask(mask))[1]
    hdr = bytearray([msg_key & 0xFF, 0])
    hdr += await encode_header(nr, 0, 2002, None, 4 if ack_order else 0, len(body), k, v80)
    if ack_order:
        a = ((int(ack_order) & 0xFFFF) ^ v80) & 0xFFFF
        hdr += bytes([a & 0xFF, a >> 8, k])
    pkt = bytearray(hdr + body)
    pkt[1] = await crc7_buff(0, bytes(pkt[2:])) & 0x7F
    return bytes(pkt)


async def build_position_heartbeat_2003(key_bytes, mask, msg_key, slot, pos, ack_order=None):
    body = bytearray()
    body += await uleb_encode((3 << 24) | int(slot))
    for v in (pos[0], pos[1], pos[2]):
        body += await zigzag_encode(int(v))
    body += b"\x00\x00\x00\x00"
    k = key_bytes[0]; v80 = ((k << 8) | k) & 0xFFFF
    nr = (await layouts_from_mask(mask))[1]
    hdr = bytearray([msg_key & 0xFF, 0])
    hdr += await encode_header(nr, 0, 2003, None, 4 if ack_order else 0, len(body), k, v80)
    if ack_order:
        a = ((int(ack_order) & 0xFFFF) ^ v80) & 0xFFFF
        hdr += bytes([a & 0xFF, a >> 8, k])
    pkt = bytearray(hdr + body)
    pkt[1] = await crc7_buff(0, bytes(pkt[2:])) & 0x7F
    return bytes(pkt)


async def build_extra_ping_cmd3(key_bytes, mask, msg_key, counter):
    body = struct.pack("<I", counter & 0xFFFFFFFF) + b"\x00\x00\x00"
    k = key_bytes[0]; v80 = ((k << 8) | k) & 0xFFFF
    nr = (await layouts_from_mask(mask))[1]
    hdr = bytearray([msg_key & 0xFF, 0])
    hdr += await encode_header(nr, 0, 3, None, 0, len(body), k, v80)
    pkt = bytearray(hdr + body)
    pkt[1] = await crc7_buff(0, bytes(pkt[2:])) & 0x7F
    return bytes(pkt)


async def auto_move_loop(sock, ip, port, key_bytes, mask, state, stop_event, label=""):
    loop = asyncio.get_event_loop()
    my_uid = state.owner_uid

    async def wait(seconds):
        try:
            await asyncio.wait_for(stop_event.wait(), timeout=seconds)
            return True
        except asyncio.TimeoutError:
            return False

    # ── Wait for spawn (own-state 2001 landed) ──
    next_report = time.time() + AUTO_MOVE_SPAWN_TIMEOUT
    landed_deadline = None
    force_started = False
    while True:
        if state.slot is not None and state.server_pos is not None:
            if landed_deadline is None:
                landed_deadline = time.time() + AUTO_MOVE_LAND_TIMEOUT
            if (state.server_physx_state == 0 and state.server_vel_y == 0) or time.time() > landed_deadline:
                break
        elif time.time() > next_report:
            if not force_started:
                force_started = True
                print_warning(f"[MOVE]{label} ⚠ own-state timeout — FORCE-START with synthetic spawn: {state.diagnostics()}")
                state.slot = state.slot or 1
                state.server_pos = state.server_pos or (0, 0, 0)
                state.server_physx_state = 0
                state.server_vel_y = 0
                break
        if await wait(0.2):
            return
    if await wait(AUTO_MOVE_START_DELAY):
        return

    if state.slot is None: state.slot = 1
    if state.server_pos is None: state.server_pos = (0, 0, 0)
    try:
        await _account_register_slot(my_uid, state.slot)
    except Exception:
        pass

    pos = list(state.server_pos)
    spawn_pos = tuple(pos)
    seen_seq = state.server_update_seq
    heading = random.uniform(-math.pi, math.pi)
    stick = (math.sin(heading) * 100, 0.0, math.cos(heading) * 100)
    last_send = time.time()
    last_pos = tuple(pos)
    stuck_timer = 0.0
    last_stuck_log = 0.0
    stuck_events = 0

    afk_decision_at  = time.time() + ANTI_AFK_DECISION_SEC
    afk_jump_at      = time.time() + ANTI_AFK_JUMP_EVERY
    cur_state        = "run"
    cur_speed_update = time.time()
    speed_mult       = 1.0
    circle_angle     = random.uniform(-math.pi, math.pi)
    circle_dir       = random.choice([-1, 1])

    # Glory Boost State
    last_glory_ping    = 0.0
    last_action_beacon = 0.0
    last_pos_hb        = 0.0

    # Custom Cycle & Legacy Cycle State
    custom_total_sec = sum(max(0.05, float(d)) for _, d in CUSTOM_CYCLE_STEPS) or 1.0
    last_custom_idx  = -1
    rot_dir          = 1

    cycle_len   = STRAIGHT_RUN_SEC + CIRCLE_MOVE_SEC
    cycle_start = time.time()
    last_phase  = None

    print_success(f"[XIRUS]{label} ONLINE uid={my_uid} slot={state.slot} spawn={[round(x) for x in pos]}")

    while not stop_event.is_set():
        now = time.time()
        dt_sec = min(0.25, max(0.001, now - last_send))
        dt_ms = dt_sec * 1000.0
        last_send = now

        if state.server_update_seq != seen_seq and state.server_pos:
            seen_seq = state.server_update_seq
            sx, sy, sz = state.server_pos
            if math.hypot(sx - pos[0], sz - pos[2]) > AUTO_MOVE_RESYNC_DISTANCE:
                print_info(f"[MOVE]{label} server-resync -> {state.server_pos}")
                pos = [sx, sy, sz]
                spawn_pos = (sx, sy, sz)
                cycle_start = now
                last_phase = None
                last_custom_idx = -1

        move_input = (0, 0)
        vel = (0, 0, 0)
        pose = 0
        is_straight_phase = False

        if CUSTOM_CYCLE_ENABLED and CUSTOM_CYCLE_STEPS:
            # ══ CUSTOM MOVEMENT CYCLE ══
            elapsed_in_cycle = (now - cycle_start) % custom_total_sec
            acc_t = 0.0
            step_idx = 0
            step_name = CUSTOM_CYCLE_STEPS[0][0]
            for idx_s, (s_name, s_dur) in enumerate(CUSTOM_CYCLE_STEPS):
                acc_t += max(0.05, float(s_dur))
                if elapsed_in_cycle < acc_t:
                    step_idx = idx_s
                    step_name = s_name
                    break

            if step_idx != last_custom_idx:
                last_custom_idx = step_idx
                if step_name == "rotate_screen":
                    rot_dir = random.choice([-1, 1])
                if CUSTOM_CYCLE_LOG_STEPS:
                    print_info(f"[MOVE]{label} ▸ Step [{step_idx+1}/{len(CUSTOM_CYCLE_STEPS)}]: {step_name}")

            # ম্যাপের বাইরে চলে গেলে ধীরে ভেতরের দিকে ঘুরিয়ে আনা
            dist_from_spawn = math.hypot(pos[0] - spawn_pos[0], pos[2] - spawn_pos[2])
            if dist_from_spawn > AUTO_MOVE_RADIUS * 0.85 and step_name != "rotate_screen":
                to_center = math.atan2(spawn_pos[0] - pos[0], spawn_pos[2] - pos[2])
                diff = (to_center - heading + math.pi) % (2 * math.pi) - math.pi
                heading += max(-math.radians(20), min(math.radians(20), diff))

            if step_name.startswith("run") or step_name == "sprint":
                speed = AUTO_MOVE_RUN_SPEED
                step = speed * dt_ms / 100.0
                ux, uz = math.sin(heading), math.cos(heading)
                stick = (ux * 100, 0.0, uz * 100)
                move_input = (stick[0], stick[2])
                vel = (ux * speed, 0, uz * speed)
                pose = MOVE_STATE_MAP.get("sprint" if step_name == "sprint" else "run", 2)
                pos[0] += ux * step
                pos[2] += uz * step

            elif step_name == "crouch_walk":
                speed = CROUCH_WALK_SPEED
                step = speed * dt_ms / 100.0
                ux, uz = math.sin(heading), math.cos(heading)
                stick = (ux * 100, 0.0, uz * 100)
                move_input = (stick[0], stick[2])
                vel = (ux * speed, 0, uz * speed)
                pose = PLAYER_STATE_MAP.get("crouch", 3)
                pos[0] += ux * step
                pos[2] += uz * step

            elif step_name == "walk":
                speed = AUTO_MOVE_WALK_SPEED
                step = speed * dt_ms / 100.0
                ux, uz = math.sin(heading), math.cos(heading)
                stick = (ux * 100, 0.0, uz * 100)
                move_input = (stick[0], stick[2])
                vel = (ux * speed, 0, uz * speed)
                pose = MOVE_STATE_MAP.get("walk", 1)
                pos[0] += ux * step
                pos[2] += uz * step

            elif step_name == "jump":
                speed = JUMP_MOVE_SPEED
                step = speed * dt_ms / 100.0
                ux, uz = math.sin(heading), math.cos(heading)
                stick = (ux * 100, 0.0, uz * 100)
                move_input = (stick[0], stick[2])
                vel = (ux * speed, 0, uz * speed)
                pose = PLAYER_STATE_MAP.get("jump", 2)
                pos[0] += ux * step
                pos[2] += uz * step

            elif step_name == "rotate_screen":
                heading += rot_dir * math.radians(SCREEN_ROTATE_DEG_PER_SEC) * dt_sec
                heading = (heading + math.pi) % (2 * math.pi) - math.pi
                stick = (0.0, 0.0, 0.0)
                move_input = (0, 0)
                vel = (0, 0, 0)
                pose = PLAYER_STATE_MAP.get("idle", 0)

            else:  # idle / fallback
                stick = (0.0, 0.0, 0.0)
                move_input = (0, 0)
                vel = (0, 0, 0)
                pose = PLAYER_STATE_MAP.get("idle", 0)

            last_pos = tuple(pos)
            stuck_timer = 0.0

        else:
            # ── Legacy Cycle Phase Check (5s straight -> 15s circle/normal) ──
            in_cycle = (now - cycle_start) % cycle_len
            is_straight_phase = in_cycle < STRAIGHT_RUN_SEC
            if is_straight_phase != last_phase:
                last_phase = is_straight_phase
                if is_straight_phase:
                    await _account_clear_target(my_uid)
                    print_info(f"[MOVE]{label} 🏃 Straight run ({STRAIGHT_RUN_SEC:.0f}s)")
                else:
                    print_info(f"[MOVE]{label} 🔄 Circle/normal move ({CIRCLE_MOVE_SEC:.0f}s)")

            if is_straight_phase:
                speed = AUTO_MOVE_RUN_SPEED
                step = speed * dt_ms / 100.0
                ux, uz = math.sin(heading), math.cos(heading)
                stick = (ux * 100, 0.0, uz * 100)
                move_input = (stick[0], stick[2])
                vel = (ux * speed, 0, uz * speed)
                pose = MOVE_STATE_MAP.get("run", 2)
                pos[0] += ux * step
                pos[2] += uz * step
                last_pos = tuple(pos)
                stuck_timer = 0.0
            else:
                moved = math.hypot(pos[0] - last_pos[0], pos[2] - last_pos[2])
                if moved < 4.0:
                    stuck_timer += AUTO_MOVE_TICK_INTERVAL
                else:
                    if stuck_timer > STUCK_THRESHOLD:
                        print_success(f"[STUCK]{label} escaped after {stuck_timer:.1f}s")
                        stuck_events += 1
                    stuck_timer = 0.0
                    last_pos = tuple(pos)
                if stuck_timer > STUCK_THRESHOLD and (now - last_stuck_log) > STUCK_LOG_COOLDOWN:
                    last_stuck_log = now
                    my_target = await _account_get_target(my_uid)
                    print_warning(
                        f"[STUCK]{label} STUCK {stuck_timer:.1f}s @ {[round(x) for x in pos]} "
                        f"| slot={state.slot} physx={state.server_physx_state} velY={state.server_vel_y} "
                        f"| target={my_target[0]} | stuck={stuck_events}")

                my_target, my_target_set_at = await _account_get_target(my_uid)
                target_age = (now - my_target_set_at) if my_target else 999

                nearest = await _account_nearest_enemy(my_uid, pos)
                if nearest is not None:
                    my_target = nearest
                    if target_age > 1.5:
                        print_info(f"[SQUAD]{label} enemy-lock {[round(x) for x in nearest]}")

                if my_target is None or (target_age > SQUAD_TARGET_TIMEOUT and nearest is None):
                    ang = random.uniform(-math.pi, math.pi)
                    dist = random.uniform(1200, AUTO_MOVE_RADIUS)
                    new_t = (pos[0] + math.sin(ang) * dist, pos[1],
                             pos[2] + math.cos(ang) * dist)
                    await _account_set_target(my_uid, new_t)
                    my_target = new_t
                    print_info(f"[SQUAD]{label} new target {[round(x) for x in new_t]}")

                if ENABLE_SPEED_MOVEMENT and (now - cur_speed_update) >= MOVEMENT_UPDATE_SPEED_EVERY:
                    cur_speed_update = now
                    speed_mult = random.uniform(MOVEMENT_SPEED_MIN, MOVEMENT_SPEED_MAX)

                if now >= afk_decision_at:
                    afk_decision_at = now + ANTI_AFK_DECISION_SEC
                    weights = [
                        ("idle",   MOVEMENT_STATE_IDLE_CHANCE),
                        ("walk",   MOVEMENT_STATE_WALK_CHANCE),
                        ("run",    MOVEMENT_STATE_RUN_CHANCE),
                        ("sprint", MOVEMENT_STATE_SPRINT_CHANCE),
                        ("jump",   MOVEMENT_STATE_JUMP_CHANCE),
                        ("crouch", MOVEMENT_STATE_CROUCH_CHANCE),
                        ("prone",  MOVEMENT_STATE_PRONE_CHANCE),
                    ]
                    total_w = sum(w for _, w in weights)
                    r = random.uniform(0, total_w)
                    acc = 0.0
                    cur_state = "run"
                    for name, w in weights:
                        acc += w
                        if r <= acc:
                            cur_state = name
                            break
                    if random.random() < ANTI_AFK_IDLE_CHANCE:
                        heading += random.uniform(-math.pi, math.pi)
                        stick = (math.sin(heading) * 100, 0.0, math.cos(heading) * 100)

                chasing = False

                if my_target is not None:
                    dx = my_target[0] - pos[0]; dz = my_target[2] - pos[2]
                    remain = math.hypot(dx, dz)
                    if remain < SQUAD_ARRIVAL_RADIUS:
                        await _account_clear_target(my_uid, only_if=my_target)
                        my_target = None
                    else:
                        chasing = True
                        speed = AUTO_MOVE_RUN_SPEED * speed_mult
                        step = speed * dt_ms / 100.0
                        want = math.atan2(dx, dz)
                        diff = (want - heading + math.pi) % (2 * math.pi) - math.pi
                        max_turn = math.radians(AUTO_MOVE_TURN_PER_TICK)
                        heading += max(-max_turn, min(max_turn, diff))
                        ux, uz = math.sin(heading), math.cos(heading)
                        stick = (ux * 100, 0.0, uz * 100)
                        move_input = (stick[0], stick[2])
                        vel = (ux * speed, 0, uz * speed)
                        pose = MOVE_STATE_MAP.get("run", 2)
                        pos[0] += ux * step
                        pos[2] += uz * step

                if not chasing:
                    if cur_state == "idle":
                        move_input = (0, 0)
                        vel = (0, 0, 0)
                        pose = PLAYER_STATE_MAP["idle"]
                    else:
                        if MOVEMENT_PATTERN == "circle":
                            circle_angle += circle_dir * (MOVEMENT_TICK_MS / 1000.0) * 1.2
                            radius = MOVEMENT_RADIUS
                            wander_x = pos[0] + math.sin(circle_angle) * radius
                            wander_z = pos[2] + math.cos(circle_angle) * radius
                        else:
                            if random.random() < 0.05:
                                heading += random.uniform(-math.pi / 3, math.pi / 3)
                            wander_x = pos[0] + math.sin(heading) * MOVEMENT_RADIUS
                            wander_z = pos[2] + math.cos(heading) * MOVEMENT_RADIUS

                        dx = wander_x - pos[0]; dz = wander_z - pos[2]
                        if abs(dx) + abs(dz) < 1.0:
                            dx, dz = math.sin(heading), math.cos(heading)
                        want = math.atan2(dx, dz)
                        diff = (want - heading + math.pi) % (2 * math.pi) - math.pi
                        heading += max(-math.radians(15), min(math.radians(15), diff))
                        ux, uz = math.sin(heading), math.cos(heading)

                        speed = STATE_SPEED.get(cur_state, 70) * speed_mult
                        step = speed * dt_ms / 100.0
                        stick = (ux * 100, 0.0, uz * 100)
                        move_input = (stick[0], stick[2])
                        vel = (ux * speed, 0, uz * speed)
                        pose = MOVE_STATE_MAP.get(cur_state, 1)
                        pos[0] += ux * step
                        pos[2] += uz * step

                    if now >= afk_jump_at:
                        afk_jump_at = now + ANTI_AFK_JUMP_EVERY
                        pose = PLAYER_STATE_MAP["jump"]

        facing = (math.sin(heading), 0.0, math.cos(heading))
        rtt = state.rtt_ms if state.rtt_ms is not None else AUTO_MOVE_DEFAULT_RTT
        ack = None
        if AUTO_MOVE_PIGGYBACK_ACK and state.pending_ack is not None:
            ack, state.pending_ack = state.pending_ack, None
        try:
            pkt = await build_player_state_sync_2001(
                key_bytes, mask, random.choice(AUTO_MOVE_MSG_KEYS), state.slot,
                pos, stick, move_input, vel, 0, pose, facing,
                max(1, min(1000, rtt)), int((now - state.session_start) * 1000), ack_order=ack
            )
            await loop.sock_sendto(sock, pkt, (ip, port))
        except Exception as e:
            print_warning(f"[MOVE]{label} send error: {e}")

        # ★★★ GLORY BOOST PACKETS ★★★
        if (CUSTOM_CYCLE_ENABLED or not is_straight_phase) and GLORY_BOOST_ENABLED:
            if now - last_glory_ping >= GLORY_PING_EVERY:
                last_glory_ping = now
                try:
                    p = await build_extra_ping_cmd3(
                        key_bytes, mask, random.choice(GLORY_MSG_KEYS),
                        int(now * 1000) & 0xFFFFFFFF)
                    await loop.sock_sendto(sock, p, (ip, port))
                except Exception:
                    pass

            if now - last_action_beacon >= GLORY_ACTION_EVERY:
                last_action_beacon = now
                try:
                    action_type = random.choice([1, 2, 3, 4])
                    b = await build_action_beacon_2002(
                        key_bytes, mask, random.choice(GLORY_MSG_KEYS),
                        state.slot, pos, action_type=action_type)
                    await loop.sock_sendto(sock, b, (ip, port))
                except Exception:
                    pass

            if now - last_pos_hb >= GLORY_ACTION_EVERY:
                last_pos_hb = now
                try:
                    hb = await build_position_heartbeat_2003(
                        key_bytes, mask, random.choice(GLORY_MSG_KEYS),
                        state.slot, pos)
                    await loop.sock_sendto(sock, hb, (ip, port))
                except Exception:
                    pass

        if CUSTOM_CYCLE_ENABLED:
            tick_wait = CUSTOM_CYCLE_TICK_INTERVAL
        elif is_straight_phase:
            tick_wait = AUTO_MOVE_TICK_INTERVAL
        else:
            tick_wait = GLORY_TICK_INTERVAL if GLORY_BOOST_ENABLED else AUTO_MOVE_TICK_INTERVAL

        if await wait(tick_wait):
            return

# ==================== MOVEMENT CONTROLLER ====================
class MovementController:
    def __init__(self, account_id, account_region, key, iv,
                 tcp_writer=None, udp_sock=None, udp_server=None,
                 udp_key_bytes=None, match_code=None):
        self.account_id = int(account_id) if str(account_id).isdigit() else 0
        self.region = str(account_region).upper()
        self.key = key; self.iv = iv
        self.tcp_writer = tcp_writer
        self.udp_sock = udp_sock
        self.udp_server = udp_server
        self.udp_key = udp_key_bytes
        self.match_code = match_code
        self.x = 0.0; self.y = 0.0; self.z = 0.0
        self.tick = 0; self.counter = 0
        self.angle = random.uniform(0, 6.28)
        self.analog_x = 0.0; self.analog_y = 0.0
        self.state = "walk"
        self.speed_mul = random.uniform(MOVEMENT_SPEED_MIN, MOVEMENT_SPEED_MAX)
        self._stop_evt = asyncio.Event()
        self._task = None
        self._last_decision = 0.0
        self._last_speed_change = 0.0
        self._last_ping_t = 0.0
        self._last_jump_t = 0.0

    def _pick_state(self) -> str:
        r = random.random(); c = MOVEMENT_STATE_IDLE_CHANCE
        if r < c: return "idle"
        c += MOVEMENT_STATE_WALK_CHANCE
        if r < c: return "walk"
        c += MOVEMENT_STATE_RUN_CHANCE
        if r < c: return "run"
        c += MOVEMENT_STATE_SPRINT_CHANCE
        if r < c: return "sprint"
        c += MOVEMENT_STATE_JUMP_CHANCE
        if r < c: return "jump"
        c += MOVEMENT_STATE_CROUCH_CHANCE
        if r < c: return "crouch"
        return "prone"

    def _update_circle_analog(self, dt):
        self.angle += (2.0 * math.pi / 6.0) * dt
        tx = 0.9 * math.cos(self.angle); ty = 0.9 * math.sin(self.angle)
        self.analog_x = max(-1.0, min(1.0, self.analog_x * 0.5 + tx * 0.5))
        self.analog_y = max(-1.0, min(1.0, self.analog_y * 0.5 + ty * 0.5))

    def _update_random_analog(self):
        ax, ay, _ = random.choice(ANALOG_DIRECTIONS[:-1])
        self.analog_x = ax * random.uniform(0.7, 1.0)
        self.analog_y = ay * random.uniform(0.7, 1.0)

    def _step_position(self, dt):
        base = STATE_SPEED.get(self.state, 40)
        speed = base * self.speed_mul
        if speed <= 0 or (self.analog_x == 0.0 and self.analog_y == 0.0): return
        mag = (self.analog_x ** 2 + self.analog_y ** 2) ** 0.5
        nx = self.analog_x / mag if mag > 0 else 0.0
        ny = self.analog_y / mag if mag > 0 else 0.0
        self.x += nx * speed * dt; self.y += ny * speed * dt
        dist = (self.x ** 2 + self.y ** 2) ** 0.5
        if dist > MOVEMENT_RADIUS:
            ratio = MOVEMENT_RADIUS / dist
            self.x *= ratio; self.y *= ratio

    async def _send_udp(self):
        if not self.udp_sock or not self.udp_server or not self.udp_key: return False
        try:
            loop = asyncio.get_running_loop()
            self.tick = (self.tick + 1) & 0xFFFF
            self.counter = (self.counter + 1) & 0xFFFF
            p_state = PLAYER_STATE_MAP.get(self.state, 1)
            m_state = MOVE_STATE_MAP.get(self.state, 1)
            pkt = await build_movement_packet_2001(
                self.udp_key, 0x6B, p_state,
                int(self.x), int(self.y), int(self.z),
                self.tick, self.counter, m_state,
                self.account_id, self.match_code or [], phase="game")
            await loop.sock_sendto(self.udp_sock, pkt, self.udp_server)
            return True
        except Exception: return False

    async def _send_ping(self):
        if not self.udp_sock or not self.udp_server or not self.udp_key: return
        try:
            loop = asyncio.get_running_loop()
            nr = (await layouts_from_mask(self.match_code or [1,3,4]))[1]
            ping_pkt = await build_packet(
                0x6D, nr, 0, 3, None, 0,
                struct.pack("<I", int(time.time()*1000) & 0xFFFFFFFF) + b"\x00\x00\x00",
                self.udp_key, encrypted=False)
            await loop.sock_sendto(self.udp_sock, ping_pkt, self.udp_server)
        except Exception: pass

    async def _do_jump(self):
        old = self.state
        self.state = "jump"
        try: await self._send_udp()
        finally: self.state = old

    async def _loop(self):
        await asyncio.sleep(ANTI_AFK_SPAWN_DELAY)
        print_premium(f"Anti-AFK START | uid={self.account_id} pattern={MOVEMENT_PATTERN}",
                      color=PX.MINT, icon=I["rocket"])
        interval = MOVEMENT_TICK_MS / 1000.0
        last_t = asyncio.get_event_loop().time()
        sent = 0; fail = 0
        while not self._stop_evt.is_set():
            now = asyncio.get_event_loop().time()
            dt = now - last_t; last_t = now
            if now - self._last_ping_t >= ANTI_AFK_PING_EVERY:
                self._last_ping_t = now; await self._send_ping()
            if now - self._last_jump_t >= ANTI_AFK_JUMP_EVERY:
                self._last_jump_t = now; await self._do_jump()
                print_info(f"jump (anti-AFK) uid={self.account_id}")
            if now - self._last_decision >= ANTI_AFK_DECISION_SEC:
                self.state = self._pick_state()
                self._last_decision = now
                print_info(f"state={self.state} speed_mul={self.speed_mul:.2f}")
            if now - self._last_speed_change >= MOVEMENT_UPDATE_SPEED_EVERY:
                self.speed_mul = random.uniform(MOVEMENT_SPEED_MIN, MOVEMENT_SPEED_MAX)
                self._last_speed_change = now
            if self.state not in ("idle","prone"):
                if MOVEMENT_PATTERN == "circle": self._update_circle_analog(dt)
                elif MOVEMENT_PATTERN == "zigzag":
                    if int(now) % 2 == 0:
                        self.analog_x = 0.8 * (1 if int(now) % 4 < 2 else -1)
                        self.analog_y = 0.9
                else:
                    if now - self._last_decision < 0.1: self._update_random_analog()
            else:
                self.analog_x = 0.0; self.analog_y = 0.0
            self._step_position(dt)
            self.z += random.uniform(-0.2, 0.2); self.z = max(-30, min(30, self.z))
            ok = await self._send_udp()
            if ok: sent += 1; fail = 0
            else:
                fail += 1
                if fail % 30 == 0: print_warning(f"UDP gagal x{fail}")
            try: await asyncio.wait_for(self._stop_evt.wait(), timeout=interval)
            except asyncio.TimeoutError: pass
        print_info(f"Anti-AFK STOP | sent={sent}")

    def start(self):
        if self._task and not self._task.done(): return
        self._stop_evt.clear()
        self._task = asyncio.create_task(self._loop())

    async def stop(self):
        self._stop_evt.set()
        if self._task:
            try: await asyncio.wait_for(self._task, timeout=3.0)
            except (asyncio.TimeoutError, asyncio.CancelledError):
                self._task.cancel()

# ==================== TEAM PACKETS ====================
def create_team(key, iv, region="ID", game_version="1.132.9", mode_id=1, sub_mode=1):
    region = (str(region).upper() if region else "ID")
    fields = {1: 1, 2: {2: bytes.fromhex("01"), 3: int(mode_id), 4: 3, 5: "en",
            8: {1: "IDC3", 2: 123, 3: region}, 9: int(sub_mode),
            10: bytes.fromhex("01090a0b1219202729"), 11: 2, 13: 1,
            14: {1: "08FBA33B4BABE2790205390333330000009700050092005F72697EB2134DCBB2467625142201040e38e848dc0e748c3f6aa04d81000000ff1113090dcacfa16d",
                2: 478, 3: "7e585d55", 4: "y[Z]", 6: 12, 7: "15686677735a7506101c",
                8: str(game_version), 9: 3, 10: 1, 11: "03626253513637754174"},
            19: 329, 21: bytes.fromhex("374f521955"),
            24: {1: 21}, 27: "a_6534489873065906362"}}
    return create_packet(create_proto(fields).hex(), "0515", key, iv)

def team_fresh(account_id, key, iv):
    return create_packet(create_proto({1: 72, 2: {1: int(account_id)}}).hex(), "0515", key, iv)

def invite_player_in_team(target_uid, key, iv, region="ID"):
    region = (str(region).upper() if region else "ID")
    return create_packet(create_proto({1: 2, 2: {1: int(target_uid), 2: region, 4: 1}}).hex(),
                         "0515", key, iv)

def accept_team_invite(target_uid, group_id, key, iv, region="ID", game_version="1.132.9"):
    region = (str(region).upper() if region else "ID")
    fields = {1: 4, 2: {1: int(target_uid), 3: int(target_uid),
        4: bytes.fromhex("0107090a0b120f19202729"), 8: 1,
        9: {1: "08FBA33B0522052002041B0222220007000C00010004000547E265AE1080779546762514110104076fa2e8770e748c3f6a68ed75000000ff08080500cacfa16d",
            2: 235, 3: {14: 80, 11: 86}, 4: "{Y\\R", 6: 13, 7: {2: 4},
            8: str(game_version), 9: 2, 10: 1, 11: "0362625351"},
        10: str(group_id), 11: {1: "IDC3", 2: 107, 3: region},
        13: "en", 16: "374f5219", 20: {1: 21}, 23: "a_6534489873065906362",
        24: "https://dl-sg-production.freefiremobile.com/", 27: {1: 2, 2: 4}}}
    return create_packet(create_proto(fields).hex(), "0515", key, iv)

def start_match_team(account_id, key, iv, region="ID"):
    region = (str(region).upper() if region else "ID")
    fields = {1: 9, 2: {1: int(account_id), 7: {1: "IDC3", 2: 410, 3: region}}}
    return create_packet(create_proto(fields).hex(), "0515", key, iv)

def ready_for_game(uid, key, iv):
    fields = {1: 15, 2: {1: uid, 2: 1}}
    return create_packet(create_proto(fields).hex(), "0519", key, iv)

# ==================== KEY EXTRACT ====================
class _Fixed64:
    __slots__ = ("value",)
    def __init__(self, value): self.value = int(value) & 0xFFFFFFFFFFFFFFFF

async def _cs_enc_varint(n): return encode_varint(int(n))

async def _cs_build_proto(fields):
    packet = bytearray()
    for field, value in fields.items():
        if isinstance(value, list):
            for item in value:
                if isinstance(item, dict):
                    nested = await _cs_build_proto(item)
                    packet.extend(await _cs_enc_varint((field << 3) | 2))
                    packet.extend(await _cs_enc_varint(len(nested)))
                    packet.extend(nested)
                elif isinstance(item, _Fixed64):
                    packet.extend(await _cs_enc_varint((field << 3) | 1))
                    packet.extend(struct.pack("<Q", item.value))
                elif isinstance(item, int):
                    packet.extend(await _cs_enc_varint((field << 3) | 0))
                    packet.extend(await _cs_enc_varint(item))
                elif isinstance(item, (str, bytes)):
                    enc_item = item.encode() if isinstance(item, str) else item
                    packet.extend(await _cs_enc_varint((field << 3) | 2))
                    packet.extend(await _cs_enc_varint(len(enc_item)))
                    packet.extend(enc_item)
        elif isinstance(value, dict):
            nested = await _cs_build_proto(value)
            packet.extend(await _cs_enc_varint((field << 3) | 2))
            packet.extend(await _cs_enc_varint(len(nested)))
            packet.extend(nested)
        elif isinstance(value, _Fixed64):
            packet.extend(await _cs_enc_varint((field << 3) | 1))
            packet.extend(struct.pack("<Q", value.value))
        elif isinstance(value, int):
            packet.extend(await _cs_enc_varint((field << 3) | 0))
            packet.extend(await _cs_enc_varint(value))
        elif isinstance(value, (str, bytes)):
            encoded = value.encode() if isinstance(value, str) else value
            packet.extend(await _cs_enc_varint((field << 3) | 2))
            packet.extend(await _cs_enc_varint(len(encoded)))
            packet.extend(encoded)
    return bytes(packet)

async def _cs_generate_packet(proto_hex, prefix, key, iv):
    cipher = AES.new(key, AES.MODE_CBC, iv)
    encrypted = cipher.encrypt(pad(bytes.fromhex(proto_hex), 16)).hex()
    length = len(encrypted) // 2
    length_hex = hex(length)[2:]
    if len(length_hex) == 2: header = prefix + "000000"
    elif len(length_hex) == 3: header = prefix + "00000"
    elif len(length_hex) == 4: header = prefix + "0000"
    elif len(length_hex) == 5: header = prefix + "000"
    else: raise ValueError(f"[CS] Unexpected length hex: {length_hex}")
    return bytes.fromhex(header + length_hex + encrypted)

def _extract_key_iv(res_json):
    if "__RAW_HEX__" in res_json and "__OFFSET__" in res_json:
        try:
            raw = bytes.fromhex(res_json["__RAW_HEX__"])
            off = int(res_json["__OFFSET__"])
            rf = extract_raw_fields(raw[off:])
            for kf, vf in [(22,23),(24,25),(6,7)]:
                k = rf.get(kf); v = rf.get(vf)
                if isinstance(k,(bytes,bytearray)) and len(k)==16 and \
                   isinstance(v,(bytes,bytearray)) and len(v)==16:
                    return bytes(k), bytes(v)
        except Exception: pass
    found = {}
    for k, v in res_json.items():
        if str(k).startswith("__"): continue
        if not isinstance(v, dict): continue
        data = v.get("data")
        if data is None: continue
        raw = None
        if isinstance(data, (bytes,bytearray)) and len(data)==16: raw = bytes(data)
        elif isinstance(data, str) and len(data)==32:
            try:
                c = bytes.fromhex(data)
                if len(c)==16: raw = c
            except Exception: pass
        if raw and len(raw)==16:
            try: found[int(k)] = raw
            except Exception: pass
    if len(found) < 2: return None, None
    for kf, vf in [(22,23),(24,25),(6,7)]:
        if kf in found and vf in found: return found[kf], found[vf]
    sk = sorted(found.keys())
    return found[sk[0]], found[sk[1]]

async def aes_encrypt(payload, key, iv):
    return AES.new(key, AES.MODE_CBC, iv).encrypt(pad(payload, AES.block_size))

# ==================== VERSION / LOGIN ====================
def get_app_version():
    try: return play_scraper('com.dts.freefireth').get('version')
    except Exception: return "1.132.9"

async def version_config(region="ID"):
    app_version = get_app_version()
    lang = REGION_LANG.get(region.upper(), "en")
    url = (f"https://version.ggwhitehawk.com/live/ver.php?version={app_version}"
           f"&lang={lang}&device=android&channel=android&appstore=googleplay"
           f"&region={region.upper()}&whitelist_version=1.3.0&whitelist_sp_version=1.0.0")
    try:
        r = await client.get(url)
        j = r.json()
        server_url = j.get("server_url")
        remote_version = j.get("remote_version")
        latest_release_version = j.get("latest_release_version")
        gops = [u.strip() for u in j.get("gop_url","").split(";") if u.strip()]
        gop_1 = gops[0] if gops else "https://ffmconnect.ppmainecoonghj.com"
        if not server_url: return None
        return latest_release_version, remote_version, server_url, gop_1, app_version
    except Exception as e:
        print_error(f"[VERCONFIG] {e}"); return None

async def get_access_token(uid, password):
    url = "https://100067.connect.garena.com/oauth/guest/token/grant"
    hdrs = {"Host":"100067.connect.garena.com",
        "User-Agent":"Dalvik/2.1.0 (Linux; U; Android 12; SM-G998B)",
        "Content-Type":"application/x-www-form-urlencoded",
        "Accept-Encoding":"gzip, deflate, br","Connection":"close"}
    data = {"uid":str(uid),"password":password,"response_type":"token","client_type":"2",
        "client_secret":HEX_KEY,"client_id":"100067"}
    for _ in range(4):
        try:
            r = await client.post(url, headers=hdrs, data=data)
            if r.status_code == 200:
                j = r.json()
                oid = j.get("open_id"); at = j.get("access_token"); pf = j.get("platform",4)
                if oid and at: return oid, at, pf
        except Exception: pass
        await asyncio.sleep(0.7)
    return None

def generate_signature(payload_str):
    return hmac.new(API_KEY, payload_str.encode(), hashlib.sha256).hexdigest()

async def register_account(password, gop_url, app_version):
    connector = aiohttp.TCPConnector(resolver=aiohttp.ThreadedResolver())
    rp = {"app_id":100067,"client_type":2,"password":password,"source":2}
    payload = json.dumps(rp, separators=(',',':'))
    sig = generate_signature(payload)
    headers = {
        "User-Agent": f"GarenaMSDK/4.0.44(SM-E135F ;Android 14;en;GB;app {app_version} 2019118525;)",
        "Authorization": f"Signature {sig}",
        "Accept": "application/json",
        "Content-Type": "application/json; charset=utf-8"}
    try:
        async with aiohttp.ClientSession(connector=connector) as s:
            async with s.post(f"{gop_url}/api/v2/oauth/guest:register",
                              headers=headers, data=payload,
                              timeout=aiohttp.ClientTimeout(total=15)) as resp:
                data = json.loads(await resp.text())
                if data.get("code") == 0: return data["data"]["uid"]
    except Exception as e: print_error(f"[REGISTER] {e}")
    return None

async def grant_token(uid, password, gop_url, app_version):
    connector = aiohttp.TCPConnector(resolver=aiohttp.ThreadedResolver())
    gp = {"client_id":100067,"client_secret":HEX_KEY,"client_type":2,
          "device_id":f"02-{uuid.uuid4()}","password":password,
          "response_type":"token","uid":int(uid)}
    payload = json.dumps(gp, separators=(',',':'))
    sig = generate_signature(payload)
    headers = {
        "User-Agent": f"GarenaMSDK/4.0.44(SM-E135F ;Android 14;en;GB;app {app_version} 2019118525;)",
        "Authorization": f"Signature {sig}",
        "Accept": "application/json",
        "Content-Type": "application/json; charset=utf-8"}
    try:
        async with aiohttp.ClientSession(connector=connector) as s:
            async with s.post(f"{gop_url}/api/v2/oauth/guest/token:grant",
                              headers=headers, data=payload,
                              timeout=aiohttp.ClientTimeout(total=15)) as resp:
                data = json.loads(await resp.text())
                if data.get("code") == 0: return data["data"]
    except Exception as e: print_error(f"[GRANT] {e}")
    return None

# ==================== PAYLOAD ====================
async def EncRypTMajoRLoGin(open_id: str, access_token: str, version: str) -> bytes:
    fields = {
        3: str(datetime.now())[:-7],
        4: "free fire",
        5: "1",
        7: str(version),
        8: "Android OS 15 / API-35 (AP3A.240905.015.A2/OS2.0.202.0.VGTIDXM)",
        9: "Handheld",
        10: "Telkomsel",
        11: "CarrierDataNetwork",
        12: "1639",
        13: "720",
        14: "320",
        15: "ARM64 FP ASIMD AES | 2000 | 8",
        16: "5653",
        17: "Mali-G52 MC2",
        18: "OpenGL ES 3.2 v1.r49p1-03bet0.19498e0ae1d5dac223383c39a2e58f04",
        19: "Google|3f10d414-be33-4ac3-b9fc-fcbf47c183b5",
        20: "182.5.135.225",
        21: "en",
        22: str(open_id),
        23: "4",
        24: "Handheld",
        25: "Xiaomi 2409BRN2CY",
        26: "ID",
        29: str(access_token),
        30: "1",
        41: "Telkomsel",
        42: "4G",
        57: "7428b253defc164018c604a1ebbfebdf",
        60: "109278",
        61: "55402",
        62: "868",
        64: "55927",
        65: "109278",
        66: "55927",
        67: "109278",
        73: "2",
        74: "/data/app/~~6Cw028g_ld-8Z0z2qhrOLA==/com.dts.freefireth-i3wiaEmpx8CbiRVhUMx_ag==/lib/arm64",
        76: "1",
        77: "b8e0cd5e295eee42f5860d3c86e483dd|/data/app/~~6Cw028g_ld-8Z0z2qhrOLA==/com.dts.freefireth-i3wiaEmpx8CbiRVhUMx_ag==/base.apk",
        78: "3",
        79: "2",
        81: "64",
        83: "2019121229",
        85: "3",
        86: "OpenGLES2",
        87: "8191",
        88: 4,
        90: "Cirebon",
        91: "JB",
        92: "14466",
        93: "android",
        94: "KqsHTyb7yHjsAiyNWUUZa0DSOD6U0AhDQ76smAo1WeHHHpSmJ8KMRyRrxb2ttgJqO9YOqO/K6AORAvDMAX/qBS8+JahIkrM7kHfzlfULbgRAoZ9r",
        95: "111207",
        96: '{"cur_rate":[60,90,120],"support_etc2":false}',
        97: "1",
        98: "1",
        98: 1,
        99: "4",
        102: "D]C\x15\x05T\x0eU3",
        103: "1",
        104: "52837",
        105: "1",
        106: "https://dl.gmc.freefiremobile.com/live/ABHotUpdates/|https://core-gmc.freefiremobile.com/live/ABHotUpdates/|211c933168f55902c7dfbfd8c4e2957d",
        107: "1.3fb8adbf45f44ce9"
    }

    proto_bytes = create_proto(fields)
    encrypted_hex = encrypt_aes(proto_bytes.hex())
    return bytes.fromhex(encrypted_hex)



async def get_payload(access_token, open_id, platform, version, lang_code="en"):
    payload = await EncRypTMajoRLoGin(open_id, access_token, version)
    return payload, payload

async def major_login(payload, login_url, release_version):
    url = f"{login_url.rstrip('/')}/MajorLogin"
    req_headers = {"Accept": "*/*", "Authorization": "Bearer ",
        "Content-Type": "application/x-www-form-urlencoded",
        "ReleaseVersion": f"{release_version}", "User-Agent": "UnityPlayer/2018.4.12f1",
        "X-GA": "v1 1", "X-GA-SV": str(int(time.time())), "X-Unity-Version": "2018.4.12f1"}
    try:
        ssl_context = ssl.create_default_context()
        ssl_context.check_hostname = False; ssl_context.verify_mode = ssl.CERT_NONE
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=15)) as session:
            async with session.post(url, headers=req_headers, data=payload, ssl=ssl_context) as response:
                response_content = await response.read()
                print_info(f"MAJOR-LOGIN status={response.status} len={len(response_content)}")
                if response.status != 200 or len(response_content) < 200: return None
                best = None; best_score = -1; best_off = 0
                for offset in [64, 0, 48, 32, 80, 16, 128, 8, 96, 60, 56, 40, 24, 20, 12, 4]:
                    if offset >= len(response_content): continue
                    cb = response_content[offset:]
                    cand = None
                    try: cand = decode_protobuf_dict(cb)
                    except Exception: cand = None
                    if not cand:
                        try:
                            c2 = decode_protobuf_2(cb)
                            if c2: cand = {str(k): {"data": v} for k, v in c2.items()}
                        except Exception: cand = None
                    if not cand: continue
                    keys = set(cand.keys())
                    has_jwt = ("8" in keys) or (8 in keys)
                    has_url = ("10" in keys) or (10 in keys)
                    score = len(cand) + (100 if has_jwt else 0) + (50 if has_url else 0)
                    if score > best_score:
                        best = cand; best_score = score; best_off = offset
                    if has_jwt and has_url: break
                if not best: return None
                if ("8" not in best) and (8 not in best): return None
                best["__RAW_HEX__"] = response_content.hex()
                best["__OFFSET__"] = best_off
                return best
    except Exception as e:
        print_error(f"MAJOR-LOGIN {e}"); return None

async def get_login_data(payload, jwt_token, server_url, release_version):
    url = f"{server_url.rstrip('/')}/GetLoginData"
    hdrs = {"Accept":"*/*","Authorization":f"Bearer {jwt_token}",
        "Content-Type":"application/x-www-form-urlencoded",
        "ReleaseVersion":f"{release_version}", "User-Agent":"UnityPlayer/2018.4.12f1",
        "X-GA":"v1 1","X-GA-SV":str(int(time.time())),"X-Unity-Version":"2018.4.12f1"}
    try:
        ssl_ctx = ssl.create_default_context()
        ssl_ctx.check_hostname = False; ssl_ctx.verify_mode = ssl.CERT_NONE
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=10)) as s:
            async with s.post(url, headers=hdrs, data=payload, ssl=ssl_ctx) as r:
                if r.status != 200: return None
                content = await r.read()
                for off in [0,64,48,32,80,16,128,8,96]:
                    if off >= len(content): continue
                    try:
                        c = decode_protobuf_dict(content[off:])
                        if c and len(c) >= 3: return c
                    except Exception: pass
                for off in [0,64,48,32,80]:
                    if off >= len(content): continue
                    c = decode_protobuf_2(content[off:])
                    if c and len(c) >= 3:
                        return {str(k):{"data":v} for k,v in c.items()}
        return None
    except Exception: return None

async def get_player_personal_show(target_uid, jwt_token, server_url, release_version):
    url = f"{server_url}/GetPlayerPersonalShow"
    payload = bytes.fromhex(encrypt_aes(create_proto({"1":int(target_uid)}).hex()))
    hdrs = {"authorization":f"Bearer {jwt_token}",
        "host":server_url.replace("https://","").split("/")[0],
        "x-ga":"v1 1","content-type":"application/x-www-form-urlencoded",
        "releaseversion":f"{release_version}",
        "user-agent":"UnityPlayer/2022.3.47f1","accept":"*/*",
        "x-unity-version":"2022.3.47f1"}
    try:
        ssl_ctx = ssl.create_default_context()
        ssl_ctx.check_hostname = False; ssl_ctx.verify_mode = ssl.CERT_NONE
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=8)) as s:
            async with s.post(url, headers=hdrs, data=payload, ssl=ssl_ctx) as r:
                if r.status != 200: return None
                return decode_protobuf_2(await r.read())
    except Exception: return None

# ==================== CLAN ====================
def _get_region_from_jwt(jwt_token):
    try:
        p = jwt_token.split('.')[1]
        p += '=' * (-len(p) % 4)
        d = json.loads(base64.urlsafe_b64decode(p))
        return (d.get('lock_region') or d.get('noti_region') or 'BD').upper()
    except Exception: return "ID"

def _get_region_url(region):
    region = region.upper()
    if region == "IND": return "https://client.ind.freefiremobile.com"
    if region in ["BR","US","NA"]: return "https://client.us.freefiremobile.com"
    return "https://clientbp.ppmainecoonghj.com"

def _create_clan_payload(clan_id):
    if not _CLAN_PB_AVAILABLE: return None
    try:
        msg = reqClan_pb2.MyMessage()
        msg.field_1 = int(clan_id)
        raw = msg.SerializeToString()
        return AES.new(AES_KEY, AES.MODE_CBC, AES_IV).encrypt(pad(raw, AES.block_size))
    except Exception as e:
        print_error(f"CLAN payload: {e}"); return None

async def join_clan(jwt_token, clan_id):
    if not _CLAN_PB_AVAILABLE: return False
    try:
        region = _get_region_from_jwt(jwt_token)
        base_url = _get_region_url(region)
        url = base_url.rstrip("/") + "/RequestJoinClan"
        host = base_url.replace("https://","")
        payload = _create_clan_payload(clan_id)
        if not payload: return False
        hdrs = {"Authorization":f"Bearer {jwt_token}",
            "X-Unity-Version":"2018.4.11f1","X-GA":"v1 1","ReleaseVersion":"OB55",
            "Content-Type":"application/octet-stream","Host":host,
            "Connection":"Keep-Alive","Accept-Encoding":"gzip"}
        ssl_ctx = ssl.create_default_context()
        ssl_ctx.check_hostname = False; ssl_ctx.verify_mode = ssl.CERT_NONE
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=15)) as s:
            async with s.post(url, headers=hdrs, data=payload, ssl=ssl_ctx) as r:
                if r.status == 200:
                    print_success(f"CLAN Join sent for {clan_id}"); return True
                print_warning(f"CLAN Join status {r.status}"); return False
    except Exception as e:
        print_error(f"CLAN {e}"); return False

# ==================== TCP ====================
async def build_tcp_startup_packet(account_id, token, server_time, key, iv, region="ID", typ='OnLine'):
    uid_hex = f"{int(account_id):016x}"
    ts_hex = f"{int(server_time):08x}"
    enc = (await aes_encrypt(token.encode(), key, iv)).hex()
    enc_len = f"{len(enc)//2:08x}"
    reg = str(region).upper() if region else "ID"
    if typ == 'OnLine':
        pfx = '7219' if reg == 'BD' else ('7214' if reg == 'IND' else '7215')
        return f"{pfx}{uid_hex}{ts_hex}00000000{enc_len}{enc}"
    pfx = '8119' if reg == 'BD' else ('8114' if reg == 'IND' else '8115')
    return f"{pfx}{uid_hex}{ts_hex}{enc_len}{enc}"

async def send_keep_alive(region="ID"):
    reg = str(region).upper() if region else "ID"
    return bytes.fromhex("0219" if reg == "ID" else ("0214" if reg == "IND" else "0215"))

async def start_game_battle_royale(region, client_version, writer, key, iv):
    packet = bytes.fromhex("0314000001e0a8c1becfcdd1a311df1b23e218f8b6ae1df958f76dfeb6bfd0399d153d1f9687174c189de3900d11f3eb8fd92cd831c482b06adec14632935703a0423b76051274d67f1381e5794cc6256079d1514ad9f9fa864733257d8e5910e9ba2f048dbe5008ba23d7e4db609ceb46ab823a50a15d0692d44c73d1f6c8e9ee33462952f2685ef8b32faea409a9b61ea091f3a36a727773dbb8316c01dfa6512dbe5b3a3ce6c8310783386c9c70c8fe143f6bc39854fdd1fffd157e52ef006a9e1e944b252a0072154aa34a45b7a5f080d7043eaf0ec6dd884b62b906781cdecca9d49f50f521c4a57dcefc4e5c274f242dcad6489dae6795c2173803fb1d343f64d47699164508e95709a43f018efca4eab791ff4010aab17d1926f7d5e11983249879940d90d5f257ad66dc0e193716addb278510de0afa48825d24ec20724382d731a2f2258ace8a4e614bfb620dc90ee9c3a87e5deaed1d44efdb561e320bc9faab91aea632d060f4ffa268067ab588edd6342c086059accb30d036b3cf766858f54b434d446935912e0e9c21b7e22ace9f17852366bd2390988f82545239e54baafcfd7bcd75d8a69a327019f8b608d80a49cbb6a65b31eec3fcab74afee3da4a9d59e367edd3f32d8eb0b8b516bcfbc1e104bd8c8bda5b76f8e5190ec1898d004dc")
    try:
        proto = thunderFF_pb2.StartMatch()
        proto.ParseFromString(packet)
        if hasattr(proto.main, 'region_list') and len(proto.main.region_list) > 0:
            proto.main.region_list[0].region = region
            if len(proto.main.region_list) > 1:
                proto.main.region_list[1].region = region
        if hasattr(proto.main, 'client_version'):
            proto.main.client_version.remote_version = client_version
        p = proto.SerializeToString()
    except Exception: p = packet
    raw_proto_hex = p.hex()
    reg = str(region).upper() if region else "BD"
    pkt_prefix = '0319' if reg == 'BD' else ('0314' if reg == 'IND' else '0315')
    packet_bytes = bytes.fromhex(raw_proto_hex)
    encrypted_packet = (await aes_encrypt(packet_bytes, key, iv)).hex()
    packet_length = len(encrypted_packet) // 2
    hex_length = f"{packet_length:08x}"
    writer.write(bytes.fromhex(pkt_prefix + hex_length + encrypted_packet))
    await writer.drain()
    print_premium(f"CS Match search sent ({packet_length}B)", color=PX.AMBER, icon=I["target"])

# ==================== CS MODE MATCHMAKING ====================
async def CS_Solo_Start_Matchmaking_Packet(key, iv, region="BD"):
    raw_proto_hex = (
            "080112f10a0a0101100f3a0d0a044944433210161a03494e443a0d0a0449444331103d1a03494e44"
            "40064a0901090a0b1219202729580162f0090a19494e4449415f4e4f54494e49543f313930393737"
            "3437383633101d1af7037e5e5852140800450407000152570f075b095a0307570b5556060e5d0809"
            "535253090e52005300081a00024a7d5a44434e110015001a15090548075177720a5e6b4762787e65"
            "4e4f726f5f7a720e710c627c0b79740c10074462045d615e56696757710d6e6e057f4f794c7e0642"
            "7e5c655474740d1a575c584c18677f1a7e4049034f6e55717c605d68466158635a50560456515107"
            "507e06077003027e0a1a010a4d1c7f175a607d610a090059417568030d755f780061637019540161"
            "0a14014c4d066319536466186d00744a6b594553457d5c4e127e125e4b45790a17054b4a600b7245"
            "754b765d62476e030e7866514b535e464177536c43540b1b0e485f180d55616606076c7f577c7f56"
            "7a544679754d4670665a1671600c1007004b5b5c6649066d7943654f6e7c4105411f7c7a746f7461"
            "705645687d0412004a567e7a4d07164a7e567b5d7e637c71447b7209425d74007851035404130d4d"
            "5e46407d4d514175687478555e5b6d6e61445f626c7603475a5b530a140b004552694e6a074d674d"
            "567c16616954697c766360485571624a4e096e0914024568577a61447907560e7a7d52127f7d4375"
            "4d61041c6c627d5a52060514034b665266487d1c0f797a50011c015e7d59727376444e406f5b084f"
            "5a0e150e4b7a0e7953515d6279664845016f4772060172550279700c7b6e6e0804220479565e5c30"
            "0e3a09120c555579797c141d4208322e3133332e3139480250025ab5050362625351363874734b77"
            "5978416456324b796f566c5556485166495a766c65756a59525745344d4450564f5570627279666a"
            "785148752f6c634b5464786465696b424a61454445694c6b4d734f63785049634e7636724346366d"
            "4c506964414732674e4f6a5839516631652f59724e506b53536b725a2f775635535a5a4c424f4b36"
            "4e766169424b636253562b4e65797264327342566356714a7876353253544a4f7368517562466f4c"
            "6a3732626c43344f4437786e51566d5867392f4a73676c443978466d314564303165737873347739"
            "75467a56706b66456d787741594646372b76683672417773556867424756326e7a794a7a5178754b"
            "42415a4f764b314a6141474365472b30527a7258666b394d426336566f5a6d6b6b6b674363573642"
            "6431466638532b6e596f46754a625762545237313575414a4f6e345378755236305a795265696a78"
            "42496a706b4e6e304d4b734a41666a4336446c565964424d4b70646c346e4d533163795072727568"
            "446f536f484d78304d41333568324d4c6d5241487653694965386244566a6b773768776d6c4d6e4f"
            "2b6d314f4a544c587a55357a554c5a6d656d4751694b524475547771796871636d68513156757568"
            "6c5241697a51484c72416d586e6736445952586d57736e4162556b767344483776633750686d6974"
            "47524b70535669326d676468586e76786e53456d775748656e78464e497652785366453461676673"
            "65587841452f50336671546d42587a5633774536482f656f4c4b58556f6432762b594d2f47677177"
            "3043416c4d49385a52586a76416f495176637a42597477493567344d7566435179614a39634f7655"
            "7451474d59594f482f6e32645642457667746a30372b72756e47754d6f785644586b4c3933723162"
            "71305a6f61694d66614d616b57796d6356457a524c6d372f6d39785037597834674b6e45714b7977"
            "3d3da20105080310f902a201050804108703a201050805109f01a20105081d10c801a20104081610"
            "5ca20105080e109001a201020815aa0115615f35353037313839393735323830313932373135"
    )
    reg = str(region).upper() if region else "BD"
    pkt_prefix = '0319' if reg == 'BD' else ('0314' if reg == 'IND' else '0315')
    packet_bytes = bytes.fromhex(raw_proto_hex)
    encrypted_packet = (await aes_encrypt(packet_bytes, key, iv)).hex()
    packet_length = len(encrypted_packet) // 2
    hex_length = f"{packet_length:08x}"
    return bytes.fromhex(pkt_prefix + hex_length + encrypted_packet)

# ==================== UDP HELPERS ====================
async def uleb_async(n): return await uleb_encode(n)

async def tea_enc(v0, v1, k0, k1, k2, k3):
    s = 0
    for _ in range(_ROUNDS):
        s = (s + _DELTA) & 0xFFFFFFFF
        v0 = (v0 + (((((v1<<4)&0xFFFFFFFF)+k0)&0xFFFFFFFF ^ ((v1+s)&0xFFFFFFFF) ^ (((v1>>5)+k1)&0xFFFFFFFF)))) & 0xFFFFFFFF
        v1 = (v1 + (((((v0<<4)&0xFFFFFFFF)+k2)&0xFFFFFFFF ^ ((v0+s)&0xFFFFFFFF) ^ (((v0>>5)+k3)&0xFFFFFFFF)))) & 0xFFFFFFFF
    return v0, v1

async def tea_dec(v0, v1, k0, k1, k2, k3):
    s = (_DELTA * _ROUNDS) & 0xFFFFFFFF
    for _ in range(_ROUNDS):
        v1 = (v1 - (((((v0<<4)&0xFFFFFFFF)+k2)&0xFFFFFFFF ^ ((v0+s)&0xFFFFFFFF) ^ (((v0>>5)+k3)&0xFFFFFFFF)))) & 0xFFFFFFFF
        v0 = (v0 - (((((v1<<4)&0xFFFFFFFF)+k0)&0xFFFFFFFF ^ ((v1+s)&0xFFFFFFFF) ^ (((v1>>5)+k1)&0xFFFFFFFF)))) & 0xFFFFFFFF
        s = (s - _DELTA) & 0xFFFFFFFF
    return v0, v1

async def tea_cbc_encrypt(padded, key_bytes):
    k0,k1,k2,k3 = (struct.unpack_from("<I", key_bytes, o)[0] for o in (0,4,8,12))
    out = bytearray(len(padded)); pc = bytearray(8); pi = bytearray(8)
    for i in range(0, len(padded), 8):
        x = bytearray(8)
        for j in range(8): x[j] = padded[i+j] ^ pc[j]
        e0,e1 = await tea_enc(struct.unpack_from("<I", x, 0)[0], struct.unpack_from("<I", x, 4)[0], k0,k1,k2,k3)
        enc = bytearray(8)
        struct.pack_into("<I", enc, 0, e0); struct.pack_into("<I", enc, 4, e1)
        for j in range(8): out[i+j] = enc[j] ^ pi[j]
        pc[:] = out[i:i+8]; pi[:] = x
    return bytes(out)

async def tea_cbc_decrypt(body, key_bytes):
    k0,k1,k2,k3 = (struct.unpack_from("<I", key_bytes, o)[0] for o in (0,4,8,12))
    out = bytearray(len(body)); pi = bytearray(8); pc = bytearray(8)
    x = bytearray(8); dec = bytearray(8)
    for i in range(0, len(body), 8):
        for j in range(8): x[j] = body[i+j] ^ pi[j]
        d0,d1 = await tea_dec(struct.unpack_from("<I", x, 0)[0], struct.unpack_from("<I", x, 4)[0], k0,k1,k2,k3)
        struct.pack_into("<I", dec, 0, d0); struct.pack_into("<I", dec, 4, d1)
        for j in range(8): out[i+j] = dec[j] ^ pc[j]
        pc[:] = body[i:i+8]; pi[:] = dec
    return bytes(out)

async def build_padded(content):
    pad_len = (8 - (len(content) + 10) % 8) % 8
    return bytes([pad_len,0,0]) + b"\x00"*pad_len + content + b"\x00"*7

async def encode_header(layout, so, cmd, oid, flags, length, k, v80):
    out = bytearray()
    for code in layout:
        val = {0:so,1:cmd,2:oid,3:flags,4:length}[code]
        if _FIELD_SIZES[code] == 1: out.append((val & 0xFF) ^ k)
        else:
            v = ((val & 0xFFFF) ^ v80) & 0xFFFF
            out.append(v & 0xFF); out.append((v >> 8) & 0xFF)
    return bytes(out)

async def crc7_buff(crc, buf):
    c = crc & 0x7F
    for b in buf: c = CRC7_TABLE[((2*(c & 0xFF)) ^ (b & 0xFF)) & 0xFF] & 0x7F
    return c & 0x7F

async def sv_frame(msg_key, layout, so, cmd, oid, flags, content, key, encrypted=True):
    k = key[0]; v80 = ((k<<8)|k) & 0xFFFF
    body = await tea_cbc_encrypt(await build_padded(content), key) if encrypted else content
    hdr = bytearray([msg_key,0]) + await encode_header(layout, so, cmd, oid, flags, len(body), k, v80)
    pkt = bytearray(hdr + body)
    pkt[1] = await crc7_buff(0, bytes(pkt[2:])) & 0x7F
    return bytes(pkt)

async def build_match_startup_packets(token, udp_key, match_code, account_id, block_val,
                                      server_ip="", region="ID", client_version="1.132.9",
                                      client_version_code="2019121229",
                                      access_token="", mode_id=1, map_id=1):
    token = token.strip()
    udp_key = bytes.fromhex(udp_key)
    match_code = [int(ch) for ch in str(match_code).strip()]
    thunder_jwt = token[:660] if len(token) > 660 else token
    sharma_jwt = token[660:] if len(token) > 660 else ""
    eth = thunder_jwt.encode() if isinstance(thunder_jwt, str) else thunder_jwt
    esh = sharma_jwt.encode() if isinstance(sharma_jwt, str) else sharma_jwt
    garena420 = await has_ssan_zig(len(eth)) + eth
    reg = str(region).upper() if region else "ID"
    csoversea_block = bytes.fromhex(
        "ca0163736f7665727365612e7374726f6e67686f6c642e66726565666972656d6f62696c652e636f6d"
        "3b302e302e302e303b33342e3132362e37362e34353b33342e38372e3137372e31343b33342e38372e"
        "3137302e3233303b33352e3138352e3138332e35370000000000000100000000000000000000000001"
        "00000800000100000000000100a8a2d7bebd8d8bdf110200")
    mid = bytes.fromhex('0000000001000102030101') + await has_ssan_zig(len(reg)) + reg.encode()
    mid += bytes.fromhex('0001030003000004')
    mid += await has_ssan_zig(len(client_version)) + client_version.encode()
    mid += await has_ssan_zig(len(client_version_code)) + client_version_code.encode()
    mid += csoversea_block
    clean_ip = server_ip.split(':')[0] if server_ip else "0.0.0.0"
    mid += await has_ssan_zig(len(clean_ip)) + clean_ip.encode()
    clean_acc_tok = access_token.strip() if access_token else ""
    if clean_acc_tok: mid += await has_ssan_zig(len(clean_acc_tok)) + clean_acc_tok.encode()
    mid += await has_ssan_zig(len(esh)) + esh
    tg = (await uleb_encode(int(account_id)) + await uleb_encode(int(block_val)) +
          await uleb_encode(1) + await uleb_encode(int(mode_id)) +
          await uleb_encode(int(block_val)) + await uleb_encode(int(map_id)) + mid)
    process = await sv_frame(0x5E, match_code, 2, 447, 0, 1, garena420, udp_key)
    loading = await sv_frame(0x5A, match_code, 2, 448, 1, 1, tg, udp_key)
    return process.hex(), loading.hex()

# ==================== CS (CLASH SQUAD) UDP JOIN PACKETS (from cs.py) ====================
async def build_cs_match_startup_packets(token, udp_key, match_code, account_id, block_val,
                                      server_ip="", region="BD", client_version="1.132.1",
                                      client_version_code="2019121227", access_token=""):
    token = token.strip()
    udp_key = bytes.fromhex(udp_key)
    match_code = [int(ch) for ch in str(match_code).strip()]
    encoded_token = token.encode() if isinstance(token, str) else token

    # Official Client Chunk Size = 1060 bytes
    CHUNK_SIZE = 1060
    chunks = [encoded_token[i:i + CHUNK_SIZE] for i in range(0, len(encoded_token), CHUNK_SIZE)] or [b""]
    if len(chunks) > 1:
        thunder_chunks = chunks[:-1]
        encoded_sharma_jwt = chunks[-1]
    else:
        thunder_chunks = chunks
        encoded_sharma_jwt = b""

    thunder_packets = []
    for idx, chunk in enumerate(thunder_chunks):
        garena420 = await has_ssan_zig(len(chunk)) + chunk
        process = await sv_frame(0x5E, match_code, 2, 447, idx, 1, garena420, udp_key)
        thunder_packets.append(process.hex())

    clean_ip = server_ip.split(':')[0] if server_ip else "0.0.0.0"
    clean_acc_tok = access_token.strip() if access_token else ""

    if CS_RANKED_ENABLED:
        # CS Ranked Auth 448 (mode_id = 6, flags_byte = 0x0F)
        M448_A = bytes.fromhex("01000000000000010202010104494e0002030001000004")
        M448_B_HEAD = bytes.fromhex("0000000000000001000000000000000000000000010000000000010000000003")
        M448_B_TAIL = b"\x02\x00"

        tg_garena420 = (
            await uleb_encode(int(account_id)) +
            await uleb_encode(int(block_val)) +
            bytes([0x01, 0x0F]) +
            await uleb_encode(int(block_val)) +
            M448_A +
            await has_ssan_zig(len(client_version)) + client_version.encode() +
            await has_ssan_zig(len(client_version_code)) + client_version_code.encode() +
            M448_B_HEAD +
            bytes([0x06, 0x00]) +          # mode_id = 6 (CS Ranked)
            await uleb_encode(0) +        # session = 0
            M448_B_TAIL +
            await has_ssan_zig(len(clean_ip)) + clean_ip.encode() +
            (await has_ssan_zig(len(clean_acc_tok)) + clean_acc_tok.encode() if clean_acc_tok else b"") +
            await has_ssan_zig(len(encoded_sharma_jwt)) + encoded_sharma_jwt
        )
    else:
        # CS Casual Auth 448
        reg = str(region).upper() if region else "BD"
        csoversea_block = bytes.fromhex(
            "ca0163736f7665727365612e7374726f6e67686f6c642e66726565666972656d6f62696c652e636f6d"
            "3b302e302e302e303b33342e3132362e37362e34353b33342e38372e3137372e31343b33342e38372e"
            "3137302e3233303b33352e3138352e3138332e35370000010000000100000000000000000000000001"
            "00000000000100010000030100b0e5e4a487da8cdf110200"
        )
        mid = bytes.fromhex('0000000000000101060101') + await has_ssan_zig(len(reg)) + reg.encode()
        mid += bytes.fromhex('0001030001000004')
        mid += await has_ssan_zig(len(client_version)) + client_version.encode()
        mid += await has_ssan_zig(len(client_version_code)) + client_version_code.encode()
        mid += csoversea_block
        mid += await has_ssan_zig(len(clean_ip)) + clean_ip.encode()
        if clean_acc_tok:
            mid += await has_ssan_zig(len(clean_acc_tok)) + clean_acc_tok.encode()
        mid += await has_ssan_zig(len(encoded_sharma_jwt)) + encoded_sharma_jwt

        tg_garena420 = (
            await uleb_encode(int(account_id)) +
            await uleb_encode(int(block_val)) +
            await uleb_encode(1) +
            await uleb_encode(15) +
            await uleb_encode(int(block_val)) +
            await uleb_encode(1) +
            mid
        )

    loading = await sv_frame(0x5A, match_code, 2, 448, len(thunder_packets), 1, tg_garena420, udp_key)
    return thunder_packets, loading.hex()

async def build_cs_hello_packet(text, key, layout):
    data = text.encode("utf-8")
    if len(data) > 25:
        data = data[:25]
    content = len(data).to_bytes(4, "little") + data + b"\x00" * (30 - 4 - len(data))
    k, v80 = await produce_xor_key(key)
    layout = await parse_layout(layout)
    padded = await build_padded(content)
    enc_body = await tea_cbc_encrypt(padded, key)
    header_bytes = await encode_header(layout, 1, 1, 0, 1, len(enc_body), k, v80)
    packet = bytearray([0x63, 0x00]) + header_bytes + enc_body
    packet[1] = await crc7_buff(0, packet[2:]) & 0x7F
    return bytes(packet).hex()

async def produce_xor_key(secret_key):
    k = secret_key[0] if secret_key and len(secret_key) > 0 else 10
    return k, ((k << 8) | k) & 0xFFFF

async def parse_layout(layout):
    if isinstance(layout, str):
        return [int(ch) for ch in layout.strip()]
    return list(layout)

async def build_hello_packet(text, key, layout):
    data = text.encode("utf-8")
    if len(data) > 25: raise ValueError("too long")
    content = b"\x10\x00\x00\x00" + data + b"\x00" * (29 - 4 - len(data))
    k = key[0]; v80 = ((k<<8)|k) & 0xFFFF
    layout = [int(c) for c in str(layout).strip()] if isinstance(layout, str) else list(layout)
    padded = await build_padded(content)
    enc_body = await tea_cbc_encrypt(padded, key)
    hbytes = await encode_header(layout, 1, 1, 0, 1, len(enc_body), k, v80)
    pkt = bytearray([0x63, 0x00]) + hbytes + enc_body
    pkt[1] = await crc7_buff(0, pkt[2:]) & 0x7F
    return bytes(pkt).hex()

async def classify(frame):
    cmd = frame["cmd"]
    msg_name = MESSAGE_ID_TO_NAME.get(cmd, f"UNKNOWN_{cmd}")
    if msg_name == "UDP_HELLO": return "HELLO"
    if msg_name == "UDP_ACK": return "ACK"
    if msg_name == "UDP_PING": return "PING"
    if msg_name == "RUDP_JOIN_MATCH": return "JOIN_MATCH"
    if msg_name.startswith("RUDP_"): return msg_name
    if msg_name.startswith("UDP_"): return msg_name
    return "DATA"

async def build_packet(msg_key, layout, so, cmd, oid, flags, content, key, encrypted=True):
    k = key[0]; v80 = ((k<<8)|k) & 0xFFFF
    body = await tea_cbc_encrypt(await build_padded(content), key) if encrypted else content
    hdr = bytearray([msg_key, 0])
    for code in layout:
        val = {0:so,1:cmd,2:oid,3:flags,4:len(body)}[code]
        if _FIELD_SIZES[code] == 1: hdr.append((val & 0xFF) ^ k)
        else:
            v = ((val & 0xFFFF) ^ v80) & 0xFFFF
            hdr.append(v & 0xFF); hdr.append((v >> 8) & 0xFF)
    pkt = bytearray(hdr + body)
    pkt[1] = await crc7_buff(0, bytes(pkt[2:])) & 0x7F
    return bytes(pkt)

async def layouts_from_mask(mask):
    ru = [int(c) for c in str(mask).strip()]
    nr = [c for c in ru if c != 2]
    return ru, nr

async def reply_for(frame, key, mask, ack_key=0x68, ping_key=0x6D, hello_key=0x5B, ack_style="short"):
    ru, nr = await layouts_from_mask(mask)
    typ = await classify(frame)
    if typ == "HELLO":
        if ack_style == "echo":
            content = frame["content"] if frame["content"] else b"\x10\x00\x00\x00"
            return typ, await build_packet(hello_key, nr, 1, 1, None, 1, content, key)
        return typ, await build_packet(ack_key, nr, 0, 2, None, 1, b"\x01\x00", key)
    if typ == "ACK":
        return typ, await build_packet(ack_key, nr, 0, 2, None, 1, frame["content"] or b"\x01\x00", key)
    if typ == "PING":
        c = frame["content"]
        counter = c[:4] if len(c) >= 4 else c
        return typ, await build_packet(ping_key, nr, 0, 3, None, 0, counter + b"\x00\x00\x00", key, encrypted=False)
    if typ == "JOIN_MATCH":
        return typ, await build_packet(ack_key, nr, 0, 2, None, 1, b"\x02\x00", key)
    return typ, None

async def keepalive_ping(sock, ip, port, key_bytes, mask, stop_event, move_state=None):
    nr = (await layouts_from_mask(mask))[1]
    ping_keys = [0x66, 0x6D, 0x69, 0x6C, 0x6B, 0x6E, 0x6F, 0x70]
    loop = asyncio.get_event_loop(); i = 0
    while not stop_event.is_set():
        pk = ping_keys[i % len(ping_keys)]
        counter = int(time.time() * 1000) & 0xFFFFFFFF
        pkt = await build_packet(pk, nr, 0, 3, None, 0,
                                 struct.pack("<I", counter) + b"\x00\x00\x00",
                                 key_bytes, encrypted=False)
        try:
            await loop.sock_sendto(sock, pkt, (ip, port))
            if move_state is not None:
                move_state.ping_sent = {c: t for c, t in move_state.ping_sent.items() if time.time() - t < 10}
                move_state.ping_sent[counter] = time.time()
        except Exception: pass
        i += 1
        try: await asyncio.wait_for(stop_event.wait(), timeout=3.0)
        except asyncio.TimeoutError: pass

async def try_header(buf, layout, k, v80):
    off = 2; out = {}
    for code in layout:
        size = _FIELD_SIZES[code]
        if off + size > len(buf): return None
        out[_FIELD_NAMES[code]] = (buf[off] ^ k) if size == 1 else \
            ((buf[off] | (buf[off+1] << 8)) ^ v80) & 0xFFFF
        off += size
    out["headerLen"] = off
    return out

async def oicq_unpad(padded):
    if not padded or len(padded) < 8: return None
    if not all(padded[-1-i] == 0 for i in range(7)): return None
    pad_len = padded[0] & 0x07
    s = 3 + pad_len; e = len(padded) - 7
    return padded[s:e] if s < e else b""

async def peek_reliable_order(packet, key, mask):
    """Order id of a reliable server packet from its (unencrypted) header alone; None if it is not one."""
    try:
        data = bytes(packet)
        if len(data) < 8:
            return None
        k = key[0]
        v80 = ((k << 8) | k) & 0xFFFF
        if (data[1] & 0x7F) != await crc7_buff(0, data[2:]):
            return None
        f = await try_header(data, (await layouts_from_mask(mask))[0], k, v80)
        if not f or f["flags"] > 7 or f["sendOption"] > 7 or f.get("orderId") is None:
            return None
        extra = 3 if (f["flags"] & 4) else 0
        if f["length"] != len(data) - f["headerLen"] - extra or not (f["flags"] & 1):
            return None
        return f["orderId"]
    except Exception:
        return None

async def decode_packet(packet, key, mask=None):
    data = bytes(packet) if isinstance(packet, bytes) else bytes.fromhex(packet)
    if len(data) < 8: return None
    k = key[0]; v80 = ((k<<8)|k) & 0xFFFF
    crc_ok = (data[1] & 0x7F) == await crc7_buff(0, data[2:])
    candidates = []
    if mask:
        ru, nr = await layouts_from_mask(mask)
        layouts = [("RUDP", ru), ("nonRUDP", nr)]
    else:
        layouts = [("RUDP", list(p)) for p in itertools.permutations([0,1,2,3,4])]
        layouts += [("nonRUDP", list(p)) for p in itertools.permutations([0,1,3,4])]
    for kind, layout in layouts:
        f = await try_header(data, layout, k, v80)
        if not f: continue
        if f["flags"] > 7 or f["sendOption"] > 7: continue
        # flags=4: 3 extra header bytes carry a piggybacked ack (u16 order id + 1 byte)
        extra = 3 if f["flags"] & 4 else 0
        if f["length"] != len(data) - f["headerLen"] - extra: continue
        ack_order = None
        if extra:
            ack_order = ((data[f["headerLen"]] | (data[f["headerLen"]+1] << 8)) ^ v80) & 0xFFFF
            f["headerLen"] += extra
        body = data[f["headerLen"]:f["headerLen"]+f["length"]]
        content = None; padded = None
        if f["flags"] & 1:
            if len(body) < 8 or len(body) % 8 != 0: continue
            padded = await tea_cbc_decrypt(body, key)
            content = await oicq_unpad(padded)
            if content is None: continue
        else: content = body
        score = (1 if crc_ok else 0) + (1 if content is not None else 0)
        candidates.append({"kind":kind, "layout":layout, "headerLen":f["headerLen"],
            "msgKey":data[0], "cmd":f["cmd"], "flags":f["flags"],
            "sendOption":f["sendOption"], "orderId":f.get("orderId"), "ackOrder":ack_order,
            "length":f["length"], "content":content, "crcOk":crc_ok, "score":score})
    if not candidates: return None
    candidates.sort(key=lambda c: c["score"], reverse=True)
    return candidates[0]

# ==================== MATCH COUNTERS ====================
_match_counters: Dict[str, int] = {}
_match_counter_lock = asyncio.Lock()

# ==================== ACCOUNTS FILE LOCK ====================
_accounts_file_lock = asyncio.Lock()

async def _read_accounts_file_unlocked() -> list:
    if not os.path.exists(ACCOUNTS_FILE):
        return []
    try:
        with open(ACCOUNTS_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, list) else []
    except Exception as e:
        print_warning(f"[ACCOUNTS] read {ACCOUNTS_FILE} failed: {e}")
        return []

async def _write_accounts_file_unlocked(accounts: list):
    tmp = ACCOUNTS_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(accounts, f, indent=2, ensure_ascii=False)
    os.replace(tmp, ACCOUNTS_FILE)

async def _remove_from_accounts_file(identifiers: set) -> list:
    removed = []
    if not identifiers: return removed
    if not os.path.exists(ACCOUNTS_FILE): return removed
    async with _accounts_file_lock:
        accs = await _read_accounts_file_unlocked()
        if not accs: return removed
        kept = []
        for a in accs:
            if not isinstance(a, dict):
                kept.append(a); continue
            auid = str(a.get("uid", "")).strip()
            atok = str(a.get("token", "")).strip()
            if (auid and auid in identifiers) or (atok and (atok in identifiers or f"tok_{atok[:20]}" in identifiers)):
                removed.append(a)
            else:
                kept.append(a)
        if removed:
            try:
                await _write_accounts_file_unlocked(kept)
            except Exception as e:
                print_error(f"[DELETE] save {ACCOUNTS_FILE} failed: {e}")
    return removed

async def _stop_and_cleanup_account(identifiers: set):
    resolved = {str(x).strip() for x in identifiers if str(x).strip()}
    for u in list(resolved):
        v = bot_state.game_to_auth_id.get(u)
        if v: resolved.add(str(v))
        v2 = bot_state.auth_to_game_id.get(u)
        if v2: resolved.add(str(v2))
    for u in list(resolved):
        acc = bot_state.accounts.get(u)
        if acc and acc.get("auth_uid"):
            resolved.add(str(acc["auth_uid"]))
    for gid, gacc in list(bot_state.accounts.items()):
        if str(gacc.get("auth_uid", "")) in resolved:
            resolved.add(str(gid))
    for u in list(resolved):
        cached = cache_get(u)
        if cached:
            try:
                if cached.get("account_id"): resolved.add(str(cached["account_id"]))
                if cached.get("auth_uid"): resolved.add(str(cached["auth_uid"]))
            except Exception: pass

    for u in resolved:
        if u in bot_state.account_workers:
            try: bot_state.account_workers[u].cancel()
            except Exception: pass
            bot_state.account_workers.pop(u, None)

    removed_memory = []
    for u in resolved:
        if u in bot_state.accounts:
            removed_memory.append(u)
            del bot_state.accounts[u]
        bot_state.paused.discard(u)
        bot_state.toggle_pause(u, False)
        bot_state.account_credentials.pop(u, None)
        bot_state.game_to_auth_id.pop(u, None)
        bot_state.auth_to_game_id.pop(u, None)
        try: cache_invalidate(u)
        except Exception: pass
        try: await _clear_team_joined(u)
        except Exception: pass
        for gid, t in list(_teams_state.items()):
            if u in t["peers"]:
                t["peers"].pop(u, None)
                if t["leader_uid"] == u:
                    t["leader_uid"] = None
                    t["team_code"] = None
    return resolved, removed_memory
    
async def _inc_match(uid):
    async with _match_counter_lock:
        _match_counters[uid] = _match_counters.get(uid, 0) + 1
        return _match_counters[uid]

async def _dec_match(uid):
    async with _match_counter_lock:
        if uid in _match_counters and _match_counters[uid] > 0:
            _match_counters[uid] -= 1
        return _match_counters.get(uid, 0)

# ==================== TOKEN CACHE ====================
_token_cache_memo: Dict[str, Any] = {}
_token_cache_memo_time: float = 0.0
_TOKEN_CACHE_MEMO_TTL = 5.0

def _json_serializer(obj):
    if isinstance(obj, (bytes, bytearray)): return {"__bytes_hex__": bytes(obj).hex()}
    raise TypeError(f"Type {type(obj)} not serializable")

def _json_deserializer(obj):
    if isinstance(obj, dict):
        if "__bytes_hex__" in obj and len(obj) == 1:
            try: return bytes.fromhex(obj["__bytes_hex__"])
            except Exception: return b""
        return {k: _json_deserializer(v) for k, v in obj.items()}
    if isinstance(obj, list): return [_json_deserializer(x) for x in obj]
    return obj

def _load_token_cache():
    global _token_cache_memo, _token_cache_memo_time
    now = time.time()
    if _token_cache_memo and (now - _token_cache_memo_time) < _TOKEN_CACHE_MEMO_TTL:
        return _token_cache_memo
    if not os.path.exists(TOKEN_CACHE_FILE): return {}
    try:
        with open(TOKEN_CACHE_FILE,"r",encoding="utf-8") as f: content = f.read().strip()
        if not content: return {}
        data = json.loads(content)
        parsed = _json_deserializer(data)
        _token_cache_memo = parsed; _token_cache_memo_time = now
        return parsed
    except Exception:
        try: os.remove(TOKEN_CACHE_FILE)
        except Exception: pass
        return {}

def _save_token_cache(cache):
    global _token_cache_memo, _token_cache_memo_time
    try:
        with open(TOKEN_CACHE_FILE,"w",encoding="utf-8") as f:
            json.dump(cache, f, indent=2, default=_json_serializer)
        _token_cache_memo = cache; _token_cache_memo_time = time.time()
    except Exception as e: print_error(f"Cache save: {e}")

def cache_get(uid):
    cache = _load_token_cache()
    e = cache.get(str(uid))
    if not e: return None
    if time.time() - e.get("cached_at",0) > TOKEN_CACHE_TTL:
        cache_invalidate(uid); return None
    if str(e.get("account_id","")).isdigit(): e["account_id"] = int(e["account_id"])
    if not isinstance(e.get("login_payload_data"), (bytes, bytearray)):
        cache_invalidate(uid); return None
    return e

def cache_set(uid, data):
    cache = _load_token_cache()
    e = dict(data); e["cached_at"] = time.time()
    cache[str(uid)] = e; _save_token_cache(cache)

def cache_invalidate(uid):
    cache = _load_token_cache()
    if str(uid) in cache:
        del cache[str(uid)]; _save_token_cache(cache)

# ==================== PLAY GAME ====================
async def play_game(server_ip_port, thunder, sharma, udp_key, match_code,
                    account_id, player_region, client_version, key, iv, match_index,
                    squad_id="A"):
    match_start_time = time.time()
    ping_task = None; sock = None
    ping_stop = asyncio.Event()
    movement_ctrl = None
    move_task = None
    force_move_task = None
    move_state = MoveState()
    uid_str = str(account_id)
    move_state.owner_uid = uid_str
    completed_cleanly = False
    try:
        ip, port = server_ip_port.split(":")
        port = int(port)
        resolved_ip = await resolve_host_cloudflare(ip)
        loop = asyncio.get_event_loop()
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        try: sock.bind(('0.0.0.0', 0))
        except Exception: pass
        optimize_udp_socket(sock); sock.setblocking(False)
        udp_key_bytes = bytes.fromhex(udp_key)
        hello_packet = await build_hello_packet(f"{account_id}_2585", udp_key_bytes, match_code)
        await loop.sock_sendto(sock, bytes.fromhex(hello_packet), (resolved_ip, port))
        ack_state = "waiting_for_hello_reply"
        thunder_sent = False
        join_match_received = False
        local_closed = False
        send_lock = asyncio.Lock()
        ping_task = asyncio.create_task(keepalive_ping(sock, resolved_ip, port, udp_key_bytes, match_code,
                                                       ping_stop, move_state))
        last_activity = time.time()
        if not AUTO_MOVE_ENABLED and ANTI_AFK_ENABLED:
            movement_ctrl = MovementController(
                account_id=account_id, account_region=player_region,
                key=key, iv=iv, tcp_writer=None,
                udp_sock=sock, udp_server=(resolved_ip, port),
                udp_key_bytes=udp_key_bytes, match_code=match_code)

        async def force_move_after_delay():
            nonlocal move_task
            await asyncio.sleep(10.0)
            if AUTO_MOVE_ENABLED and move_task is None:
                print_warning(f"[MOVE] #{match_index} FORCE-START (10s fallback) for UID:{uid_str}")
                move_task = asyncio.create_task(
                    auto_move_loop(sock, resolved_ip, port, udp_key_bytes, match_code,
                                   move_state, ping_stop, label=f"[MATCH #{match_index}]"))

        force_move_task = asyncio.create_task(force_move_after_delay())

        async def send_thunder_sharma_inline():
            nonlocal ack_state, thunder_sent, move_task
            if thunder_sent: return
            async with send_lock:
                if thunder_sent: return
                try:
                    await loop.sock_sendto(sock, bytes.fromhex(thunder), (resolved_ip, port))
                    thunder_sent = True
                    await asyncio.sleep(0.3)
                    prepare_ack = await build_packet(0x68, (await layouts_from_mask(match_code))[1],
                                                     0, 2, None, 1, b"\x01\x00", udp_key_bytes)
                    await loop.sock_sendto(sock, prepare_ack, (resolved_ip, port))
                    await asyncio.sleep(0.4)
                    await loop.sock_sendto(sock, bytes.fromhex(sharma), (resolved_ip, port))
                    ack_state = "thunder_sharma_sent"
                    print_premium(f"Match #{match_index} Playing in-game!",
                                  color=PX.LIME, icon=I["flame"])
                    if AUTO_MOVE_ENABLED and move_task is None:
                        move_task = asyncio.create_task(
                            auto_move_loop(sock, resolved_ip, port, udp_key_bytes, match_code,
                                           move_state, ping_stop, label=f"[MATCH #{match_index}]"))
                    elif movement_ctrl:
                        movement_ctrl.start()
                except Exception as e:
                    print_error(f"Match #{match_index} startup: {e}")

        while not local_closed:
            if time.time() - match_start_time > MAX_MATCH_DURATION:
                completed_cleanly = True; break
            try:
                response, server_addr = await asyncio.wait_for(loop.sock_recvfrom(sock, 65535), timeout=2.0)
                if response:
                    last_activity = time.time()
                    frame = await decode_packet(response, udp_key_bytes, match_code)
                    if not frame:
                        move_state.undecoded += 1
                    if frame:
                        move_state.on_server_frame(frame)
                        ptype = await classify(frame)
                        if frame['cmd'] in [103, 107]:
                            print_premium(f"Match #{match_index} END", color=PX.MAGENTA, icon=I["star"])
                            completed_cleanly = True; local_closed = True
                            continue
                        if frame['cmd'] == 101:
                            try:
                                ack = await build_packet(0x68, (await layouts_from_mask(match_code))[1],
                                                         0,2,None,1, b"\x01\x00", udp_key_bytes)
                                await loop.sock_sendto(sock, ack, server_addr)
                            except Exception: pass
                            continue
                        if ptype in ["ACK","PING","HELLO","JOIN_MATCH"]:
                            if ptype == "HELLO" and ack_state == "waiting_for_hello_reply":
                                typ, reply = await reply_for(frame, udp_key_bytes, match_code, ack_style="short")
                                if reply: await loop.sock_sendto(sock, reply, server_addr)
                                ack_state = "ack_sent_waiting"
                            elif ptype == "ACK":
                                if ack_state == "waiting_for_hello_reply":
                                    typ, reply = await reply_for(frame, udp_key_bytes, match_code)
                                    if reply: await loop.sock_sendto(sock, reply, server_addr)
                                    ack_state = "ready_to_send_thunder"
                                elif ack_state == "ack_sent_waiting": ack_state = "ready_to_send_thunder"
                                else:
                                    typ, reply = await reply_for(frame, udp_key_bytes, match_code)
                                    if reply: await loop.sock_sendto(sock, reply, server_addr)
                            elif ptype == "PING":
                                typ, reply = await reply_for(frame, udp_key_bytes, match_code)
                                if reply: await loop.sock_sendto(sock, reply, server_addr)
                            elif ptype == "JOIN_MATCH" and not join_match_received:
                                typ, reply = await reply_for(frame, udp_key_bytes, match_code)
                                if reply:
                                    await loop.sock_sendto(sock, reply, server_addr)
                                    join_match_received = True
            except asyncio.TimeoutError:
                if ack_state == "ready_to_send_thunder" and not thunder_sent:
                    await send_thunder_sharma_inline()
                elif ack_state == "waiting_for_hello_reply":
                    if (time.time() - last_activity) > 7.0:
                        try:
                            pkt = await build_hello_packet(f"{account_id}_2585", udp_key_bytes, match_code)
                            await loop.sock_sendto(sock, bytes.fromhex(pkt), (resolved_ip, port))
                        except Exception: pass
                        last_activity = time.time()
                    if (time.time() - match_start_time) > 25.0:
                        print_warning(f"Match #{match_index} Handshake timeout"); break
                elif ack_state == "thunder_sharma_sent":
                    if (time.time() - last_activity) > MATCH_IDLE_TIMEOUT:
                        completed_cleanly = True; break
            except (BlockingIOError, OSError):
                await asyncio.sleep(0.5); continue
            except Exception:
                await asyncio.sleep(0.5); continue
            if ack_state == "ready_to_send_thunder" and not thunder_sent:
                await send_thunder_sharma_inline()
        return f"match #{match_index} finished"
    except Exception as e:
        print_error(f"Match #{match_index} {e}")
        return f"match #{match_index} error"
    finally:
        if movement_ctrl:
            try: await movement_ctrl.stop()
            except Exception: pass
        ping_stop.set()
        if move_task:
            move_task.cancel()
            try: await move_task
            except asyncio.CancelledError: pass
            except Exception: pass

        if force_move_task:
            force_move_task.cancel()
            try: await force_move_task
            except asyncio.CancelledError: pass
            except Exception: pass

        if completed_cleanly:
            try:
                bot_state.increment_match(uid_str)
                print_premium(f"Match #{match_index} Complete | UID: {uid_str}",
                              color=PX.GOLD, icon=I["crown"])
                try: await _mark_bot_match_finished(uid_str, squad_id=squad_id)
                except Exception: pass
                async def _post_exp(uid):
                    try:
                        for wait in (5.0, 8.0, 12.0):
                            await asyncio.sleep(wait)
                            await refresh_account_profile(uid)
                    except Exception: pass
                asyncio.create_task(_post_exp(uid_str))
            except Exception: pass
        ping_stop.set()
        if ping_task:
            ping_task.cancel()
            try: await ping_task
            except asyncio.CancelledError: pass
        if sock:
            try: sock.close()
            except Exception: pass
        remaining = await _dec_match(uid_str)
        try: bot_state.update_status(uid_str, "ONLINE" if remaining == 0 else "IN_MATCH", remaining)
        except Exception: pass

# ==================== PLAY GAME (CS MODE) ====================
async def play_game_cs(server_ip_port, thunder, sharma, udp_key, match_code,
                       account_id, player_region, client_version, key, iv, match_index,
                       squad_id="A"):
    match_start_time = time.time()
    ping_task = None; move_task = None; skill_task = None; force_move_task = None; sock = None
    ping_stop = asyncio.Event()
    move_state = MoveState()
    uid_str = str(account_id)
    move_state.owner_uid = uid_str
    tag = f"CS #{match_index} · {uid_str}"
    completed_cleanly = False
    try:
        ip, port = server_ip_port.split(":")
        port = int(port)
        resolved_ip = await resolve_host_cloudflare(ip)
        loop = asyncio.get_event_loop()
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        try: sock.bind(('0.0.0.0', 0))
        except Exception: pass
        optimize_udp_socket(sock); sock.setblocking(False)
        udp_key_bytes = bytes.fromhex(udp_key)
        nr_layout = (await layouts_from_mask(match_code))[1]
        hello_packet = await build_cs_hello_packet(f"{account_id}_2585", udp_key_bytes, match_code)
        await loop.sock_sendto(sock, bytes.fromhex(hello_packet), (resolved_ip, port))
        ack_state = "waiting_for_hello_reply"
        thunder_sent = False
        local_closed = False
        send_lock = asyncio.Lock()
        ping_task = asyncio.create_task(keepalive_ping(sock, resolved_ip, port, udp_key_bytes, match_code,
                                                       ping_stop, move_state))
        last_activity = time.time()
        ack_top, ack_sent_at = None, 0.0
        blind_acks = 0
        print_premium(f"{tag} UDP session → {resolved_ip}:{port}", color=PX.CYAN, icon=I["target"])

        async def force_move_after_delay():
            nonlocal move_task
            await asyncio.sleep(10.0)
            if AUTO_MOVE_ENABLED and move_task is None:
                print_warning(f"[MOVE][{tag}] FORCE-START (10s fallback)")
                move_task = asyncio.create_task(
                    auto_move_loop(sock, resolved_ip, port, udp_key_bytes, match_code,
                                   move_state, ping_stop, label=f"[{tag}]"))

        force_move_task = asyncio.create_task(force_move_after_delay())

        async def send_thunder_sharma():
            nonlocal ack_state, thunder_sent, move_task, skill_task
            if thunder_sent: return
            async with send_lock:
                if thunder_sent: return
                try:
                    for t_pkt in thunder:
                        await loop.sock_sendto(sock, bytes.fromhex(t_pkt), (resolved_ip, port))
                        await asyncio.sleep(0.05)
                    thunder_sent = True
                    await asyncio.sleep(0.1)
                    prepare_ack = await build_packet(0x68, nr_layout, 0, 2, None, 1, b"\x01\x00", udp_key_bytes)
                    await loop.sock_sendto(sock, prepare_ack, (resolved_ip, port))
                    await asyncio.sleep(0.2)
                    await loop.sock_sendto(sock, bytes.fromhex(sharma), (resolved_ip, port))
                    ack_state = "thunder_sharma_sent"
                    print_premium(f"{tag} Thunder ({len(thunder)} parts) + Sharma sent → Playing CS!",
                                  color=PX.LIME, icon=I["flame"])
                    if AUTO_MOVE_ENABLED and move_task is None:
                        move_task = asyncio.create_task(
                            auto_move_loop(sock, resolved_ip, port, udp_key_bytes, match_code,
                                           move_state, ping_stop, label=f"[{tag}]"))

                    if HOMER_SKILL_ENABLED and skill_task is None:
                        skill_task = asyncio.create_task(
                            homer_skill_loop(sock, resolved_ip, port, udp_key_bytes, match_code,
                                             move_state, ping_stop, label=f"[{tag}]"))
                except Exception as e:
                    print_error(f"{tag} startup: {e}")

        while not local_closed:
            if time.time() - match_start_time > CS_MAX_MATCH_DURATION:
                completed_cleanly = True; break
            try:
                response, server_addr = await asyncio.wait_for(loop.sock_recvfrom(sock, 65535), timeout=1.5)
                if response:
                    last_activity = time.time()
                    frame = await decode_packet(response, udp_key_bytes, match_code)
                    if not frame:
                        move_state.undecoded += 1
                        oid = await peek_reliable_order(response, udp_key_bytes, match_code)
                        if oid is not None:
                            nxt = (oid + 1) & 0xFFFF
                            fresh_ack = ack_top is None or (((nxt - ack_top) & 0xFFFF) < 0x8000 and nxt != ack_top)
                            if fresh_ack or time.time() - ack_sent_at > 0.25:
                                try:
                                    top_ = nxt if fresh_ack else ack_top
                                    pkt_ = await build_packet(0x68, nr_layout, 0, 2, None, 1,
                                                              top_.to_bytes(2, "little"), udp_key_bytes)
                                    await loop.sock_sendto(sock, pkt_, server_addr)
                                    ack_top, ack_sent_at = top_, time.time()
                                    blind_acks += 1
                                    if blind_acks == 1:
                                        print_info(f"{tag} acking reliable packets we cannot decrypt (order id {oid})")
                                except Exception: pass
                    if frame:
                        move_state.on_server_frame(frame)
                        cmd = frame.get('cmd')
                        order_id = frame.get('orderId')
                        flags = frame.get('flags', 0)
                        if cmd in [103, 107]:
                            print_premium(f"{tag} END (cmd {cmd})", color=PX.MAGENTA, icon=I["star"])
                            completed_cleanly = True; local_closed = True
                            continue
                        if cmd == 130:
                            print_success(f"{tag} JOIN_MATCH_FINISHED — loaded into Clash Squad")
                            try:
                                next_id = ((order_id or 0) + 1) & 0xFFFF
                                fin_ack = await build_packet(0x68, nr_layout, 0, 2, None, 1,
                                                             next_id.to_bytes(2, "little"), udp_key_bytes)
                                await loop.sock_sendto(sock, fin_ack, server_addr)
                            except Exception: pass
                            continue
                        if (flags & 1) and order_id is not None:
                            try:
                                next_expected = (order_id + 1) & 0xFFFF
                                data_ack = await build_packet(0x68, nr_layout, 0, 2, None, 1,
                                                              next_expected.to_bytes(2, "little"), udp_key_bytes)
                                await loop.sock_sendto(sock, data_ack, server_addr)
                                if ack_top is None or ((next_expected - ack_top) & 0xFFFF) < 0x8000:
                                    ack_top, ack_sent_at = next_expected, time.time()
                            except Exception: pass
                        ptype = await classify(frame)
                        if ptype == "HELLO" and ack_state == "waiting_for_hello_reply":
                            _, reply = await reply_for(frame, udp_key_bytes, match_code, ack_style="short")
                            if reply: await loop.sock_sendto(sock, reply, server_addr)
                            ack_state = "ready_to_send_thunder"
                        elif ptype == "ACK":
                            if ack_state in ("waiting_for_hello_reply", "ack_sent_waiting"):
                                ack_state = "ready_to_send_thunder"
                        elif ptype == "PING":
                            _, reply = await reply_for(frame, udp_key_bytes, match_code)
                            if reply: await loop.sock_sendto(sock, reply, server_addr)
            except asyncio.TimeoutError:
                if ack_state == "ready_to_send_thunder" and not thunder_sent:
                    await send_thunder_sharma()
                elif ack_state == "waiting_for_hello_reply":
                    if (time.time() - last_activity) > 7.0:
                        try:
                            pkt = await build_cs_hello_packet(f"{account_id}_2585", udp_key_bytes, match_code)
                            await loop.sock_sendto(sock, bytes.fromhex(pkt), (resolved_ip, port))
                        except Exception: pass
                        last_activity = time.time()
                    if (time.time() - match_start_time) > 25.0:
                        print_warning(f"{tag} Handshake timeout"); break
                elif ack_state == "thunder_sharma_sent":
                    if (time.time() - last_activity) > CS_MATCH_IDLE_TIMEOUT:
                        print_success(f"{tag} finished naturally (server silent)")
                        completed_cleanly = True; break
                continue
            except (BlockingIOError, OSError):
                await asyncio.sleep(0.5); continue
            except Exception:
                await asyncio.sleep(0.5); continue
            if ack_state == "ready_to_send_thunder" and not thunder_sent:
                await send_thunder_sharma()
        return f"match #{match_index} finished"
    except asyncio.CancelledError:
        raise
    except Exception as e:
        print_error(f"{tag} {e}")
        return f"match #{match_index} error"
    finally:
        ping_stop.set()
        for t in (force_move_task, move_task, ping_task, skill_task):
            if t:
                t.cancel()
                try: await t
                except asyncio.CancelledError: pass
                except Exception: pass
        if sock:
            try: sock.close()
            except Exception: pass
        if completed_cleanly:
            try:
                bot_state.increment_match(uid_str)
                print_premium(f"{tag} Complete", color=PX.GOLD, icon=I["crown"])
                try: await _mark_bot_match_finished(uid_str, squad_id=squad_id)
                except Exception: pass
                async def _post_exp(uid):
                    try:
                        for wait in (5.0, 8.0, 12.0):
                            await asyncio.sleep(wait)
                            await refresh_account_profile(uid)
                    except Exception: pass
                asyncio.create_task(_post_exp(uid_str))
            except Exception: pass
        remaining = await _dec_match(uid_str)
        try: bot_state.update_status(uid_str, "ONLINE" if remaining == 0 else "IN_MATCH", remaining)
        except Exception: pass

# ==================== FUNCTIONAL LONE WOLF ====================
# ==================== FUNCTIONAL LONE WOLF ====================
async def functional_lone_wolf(addrs, starter_packet, account_region, client_version,
                                key, iv, account_id="", account_data=None, max_reconnects=10,
                                squad_id="A"):
    reconnects = 0
    ip, port = addrs.split(":")
    play_matches: List[asyncio.Task] = []
    no_response_count = 0
    search_attempts = 0
    last_start_time = 0.0
    uid_str = str(account_id)
    gid = str(squad_id or "A").upper()
    team_state = _get_team(gid)
    squad_restart = _get_squad_restart(gid)
    my_restart_seq = squad_restart["seq"]

    current_token = starter_packet
    current_key = key; current_iv = iv
    current_account_data = account_data
    _writer_ref = {"w": None}
    _team_active = {"flag": True}
    _match_played = {"flag": False}

    async def _process_social_packet(raw_bytes, tag="MAIN"):
        try:
            hex_data = raw_bytes.hex()
            candidates = []
            if len(raw_bytes) >= 6:
                plen = raw_bytes[4]
                if 0 < plen <= (len(raw_bytes) - 5):
                    try:
                        inner = bytes(raw_bytes[5:5 + plen])
                        d0 = decode_protobuf_dict(inner)
                        if not d0:
                            a0 = decode_protobuf_2(inner)
                            if a0: d0 = {str(k): {"data": v} for k, v in a0.items()}
                        if d0: candidates.append((5, d0))
                    except Exception: pass
            for off in [5, 6, 10, 8, 12, 14, 4, 16, 0]:
                if off >= len(hex_data): continue
                try: inner_bytes = bytes.fromhex(hex_data[off:])
                except Exception: continue
                decoded = None
                try:
                    d1 = decode_protobuf_dict(inner_bytes)
                    if d1: decoded = d1
                except Exception: pass
                if not decoded:
                    try:
                        d2 = decode_protobuf_2(inner_bytes)
                        if d2: decoded = {str(k): {"data": v} for k, v in d2.items()}
                    except Exception: pass
                if decoded: candidates.append((off, decoded))
            if not candidates: return
            def _score(item):
                _off, d = item
                s = len(d)
                if "0" in d or 0 in d: s -= 100
                if "5" in d: s += 6
                if "1" in d: s += 4
                if "2" in d: s += 2
                return s
            candidates.sort(key=_score, reverse=True)
            best_off, decoded = candidates[0]
            def _val(container, k):
                if not isinstance(container, dict): return None
                v = container.get(k) if k in container else container.get(str(k))
                if isinstance(v, dict) and "data" in v: return v["data"]
                return v
            f5wrap = decoded.get("5") or decoded.get(5)
            f5 = None
            if isinstance(f5wrap, dict) and "data" in f5wrap: f5 = f5wrap["data"]
            elif isinstance(f5wrap, dict): f5 = f5wrap
            target_uid = None
            if isinstance(f5, dict):
                for fk in [1,2,3,4,6]:
                    cand = _val(f5, fk)
                    if cand and str(cand).isdigit() and 6 <= len(str(cand)) <= 15:
                        target_uid = str(cand); break
            if not target_uid: return
            own_acc = None
            if current_account_data: own_acc = str(current_account_data.get('account_id', ''))
            if own_acc and target_uid == own_acc: return
            if not _accept_friend_request or not current_account_data: return
            jwt_l = current_account_data.get('token')
            srv_l = current_account_data.get('server_url')
            rel_l = current_account_data.get('release_version')
            own_id = current_account_data.get('account_id')
            if not (jwt_l and srv_l and rel_l and own_id): return
            url = f"{srv_l.rstrip('/')}/ConfirmFriendRequest"
            fields = {"1": int(DEV_UID), "2": int(own_id)}
            try:
                payload = bytes.fromhex(encrypt_aes(create_proto(fields).hex()))
                hdrs = {
                    "authorization": f"Bearer {jwt_l}",
                    "host": srv_l.replace("https://", "").replace("http://", "").split("/")[0],
                    "x-ga": "v1 1", "content-type": "application/x-www-form-urlencoded",
                    "accept-encoding": "deflate, gzip", "releaseversion": f"{rel_l}",
                    "user-agent": "UnityPlayer/2022.3.47f1",
                    "accept": "*/*", "x-unity-version": "2022.3.47f1",
                }
                ssl_ctx = ssl.create_default_context()
                ssl_ctx.check_hostname = False; ssl_ctx.verify_mode = ssl.CERT_NONE
                async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=8)) as s:
                    async with s.post(url, headers=hdrs, data=payload, ssl=ssl_ctx) as r:
                        body = await r.read()
                        if r.status == 200 and len(body) > 0:
                            print_success(f"FRIEND-{tag} Accepted {target_uid}")
            except Exception as e:
                print_warning(f"FRIEND-{tag} {type(e).__name__}: {e}")
        except Exception as e:
            print_warning(f"SOCIAL-{tag} exception: {type(e).__name__}: {e}")

    async def _team_coordinator():
        try:
            while True:
                if squad_restart["seq"] != my_restart_seq: return
                async with team_state["lock"]:
                    n = len(team_state["peers"])
                if n >= TEAM_SIZE: break
                if bot_state.is_paused(uid_str): return
                await asyncio.sleep(0.5)
            await asyncio.sleep(TEAM_READY_DELAY)
            async with team_state["lock"]:
                is_leader = (team_state["leader_uid"] == uid_str)
                peers_snapshot = dict(team_state["peers"])
            if not is_leader:
                print_info(f"TEAM[{gid}] {uid_str} waiting as member..."); return
            print_premium(f"TEAM[{gid}] {uid_str} — creating {'CS' if CS_MODE_ENABLED else 'BR'} squad region={account_region}",
                          color=PX.GOLD, icon=I["crown"])
            async with team_state["lock"]:
                team_state["team_code"] = None
            own_id_num = None
            if current_account_data: own_id_num = current_account_data.get('account_id')
            if not own_id_num:
                try: own_id_num = int(uid_str)
                except Exception: own_id_num = 0
            try:
                pkt = create_team(current_key, current_iv, region=account_region,
                                  game_version=client_version,
                                  mode_id=CS_MODE_ID if CS_MODE_ENABLED else 1,
                                  sub_mode=6 if (CS_MODE_ENABLED and CS_RANKED_ENABLED) else 1)
                if _writer_ref["w"] and not _writer_ref["w"].is_closing():
                    _writer_ref["w"].write(pkt); await _writer_ref["w"].drain()
                    print_info(f"TEAM[{gid}] create_team sent ({len(pkt)}B)")
            except Exception as e: print_error(f"TEAM[{gid}] create_team err: {e}")
            await asyncio.sleep(1.5)
            try:
                pkt = team_fresh(int(own_id_num), current_key, current_iv)
                if _writer_ref["w"] and not _writer_ref["w"].is_closing():
                    _writer_ref["w"].write(pkt); await _writer_ref["w"].drain()
                    print_success(f"TEAM[{gid}] team_fresh #1 sent")
            except Exception as e: print_warning(f"TEAM[{gid}] team_fresh err: {e}")
            await asyncio.sleep(1.0)
            async def _invite_uid(target_uid, label=""):
                for attempt in range(2):
                    try:
                        inv = invite_player_in_team(int(target_uid), current_key, current_iv,
                                                    region=account_region)
                        if _writer_ref["w"] and not _writer_ref["w"].is_closing():
                            _writer_ref["w"].write(inv); await _writer_ref["w"].drain()
                            print_info(f"TEAM[{gid}] invite{label} → {target_uid} #{attempt+1}")
                    except Exception as e: print_warning(f"TEAM[{gid}] invite err: {e}")
                    await asyncio.sleep(0.6)
            invite_count = 0
            for peer_uid, peer_info in peers_snapshot.items():
                if peer_uid == uid_str: continue
                peer_acc_id = None
                try: peer_acc_id = peer_info["data"].get("account_id")
                except Exception: pass
                if not peer_acc_id: peer_acc_id = peer_uid
                print_premium(f"TEAM[{gid}] Inviting bot{invite_count+2} {peer_acc_id}...",
                              color=PX.CYAN, icon=I["arrow"])
                await _invite_uid(int(peer_acc_id), f" bot{invite_count+2}")
                invite_count += 1
            await asyncio.sleep(TEAM_INVITE_WAIT + 3.0)
            try:
                pkt = team_fresh(int(own_id_num), current_key, current_iv)
                if _writer_ref["w"] and not _writer_ref["w"].is_closing():
                    _writer_ref["w"].write(pkt); await _writer_ref["w"].drain()
                    print_success(f"TEAM[{gid}] team_fresh #2 sent")
            except Exception as e: print_warning(f"TEAM[{gid}] team_fresh #2 err: {e}")
            await asyncio.sleep(1.0)
            print_premium(f"TEAM[{gid}] {uid_str} SQUAD READY → start match loop",
                          color=PX.EMERALD, icon=I["rocket"])
            try: bot_state.update_status(uid_str, "SEARCHING", 0)
            except Exception: pass
            while _team_active["flag"] and not _match_played["flag"] and squad_restart["seq"] == my_restart_seq:
                try:
                    if bot_state.is_paused(uid_str): break
                    async with team_state["lock"]:
                        if team_state["leader_uid"] != uid_str: break
                    own_id = current_account_data.get('account_id', own_id_num) if current_account_data else own_id_num
                    try:
                        rdy = ready_for_game(int(own_id), current_key, current_iv)
                        if _writer_ref["w"] and not _writer_ref["w"].is_closing():
                            _writer_ref["w"].write(rdy); await _writer_ref["w"].drain()
                    except Exception as e: print_warning(f"TEAM[{gid}] ready err: {e}")
                    await asyncio.sleep(CS_TEAM_LEADER_DELAY if CS_MODE_ENABLED else 1.0)
                    sm = start_match_team(int(own_id), current_key, current_iv, region=account_region)
                    if _writer_ref["w"] and not _writer_ref["w"].is_closing():
                        _writer_ref["w"].write(sm); await _writer_ref["w"].drain()
                        if CS_MODE_ENABLED:
                            print_info(f"TEAM[{gid}] CS leader {uid_str} start sent "
                                       f"(again after {CS_TEAM_START_RETRY:.0f}s without a match)")
                except Exception as e: print_warning(f"TEAM[{gid}] start_match err: {e}")
                if CS_MODE_ENABLED:
                    retry_at = time.time() + CS_TEAM_START_RETRY
                    while (time.time() < retry_at and _team_active["flag"] and not _match_played["flag"]
                           and squad_restart["seq"] == my_restart_seq and not bot_state.is_paused(uid_str)):
                        await asyncio.sleep(0.5)
                    continue
                try: await asyncio.wait_for(asyncio.sleep(5.0), timeout=5.5)
                except asyncio.TimeoutError: pass
        except asyncio.CancelledError: raise
        except Exception as e:
            print_error(f"TEAM[{gid}] coordinator error: {e}")

    async def _member_match_trigger():
        try:
            await asyncio.sleep(TEAM_READY_DELAY + 18.0)
            if squad_restart["seq"] != my_restart_seq: return
            async with team_state["lock"]:
                if team_state["leader_uid"] == uid_str: return
            print_premium(f"TEAM[{gid}] Member {uid_str} ready loop",
                          color=PX.SKY, icon=I["pulse"])
            try: bot_state.update_status(uid_str, "SEARCHING", 0)
            except Exception: pass
            my_id = current_account_data.get('account_id', uid_str) if current_account_data else uid_str
            while _team_active["flag"] and not _match_played["flag"] and squad_restart["seq"] == my_restart_seq:
                try:
                    if bot_state.is_paused(uid_str): break
                    if _writer_ref["w"] and not _writer_ref["w"].is_closing():
                        try:
                            rdy = ready_for_game(int(my_id), current_key, current_iv)
                            _writer_ref["w"].write(rdy); await _writer_ref["w"].drain()
                        except Exception as e: print_warning(f"TEAM[{gid}] member ready err: {e}")
                        await asyncio.sleep(1.0)
                        if not CS_MODE_ENABLED or CS_TEAM_MEMBERS_START:
                            sm = start_match_team(int(my_id), current_key, current_iv, region=account_region)
                            _writer_ref["w"].write(sm); await _writer_ref["w"].drain()
                except Exception as e: print_warning(f"TEAM[{gid}] member trigger: {e}")
                if CS_MODE_ENABLED:
                    retry_at = time.time() + CS_TEAM_START_RETRY
                    while (time.time() < retry_at and _team_active["flag"] and not _match_played["flag"]
                           and squad_restart["seq"] == my_restart_seq and not bot_state.is_paused(uid_str)):
                        await asyncio.sleep(0.5)
                    continue
                try: await asyncio.wait_for(asyncio.sleep(5.0), timeout=5.5)
                except asyncio.TimeoutError: pass
        except asyncio.CancelledError: raise
        except Exception as e:
            print_warning(f"TEAM[{gid}] member trigger outer: {e}")

    try:
        while True:
            if squad_restart["seq"] != my_restart_seq:
                print_warning(f"[RESTART-{gid}] {uid_str} restarting for Squad {gid}")
                try: bot_state.update_status(uid_str, "OFFLINE", 0)
                except Exception: pass
                return
            while bot_state.is_paused(uid_str):
                if squad_restart["seq"] != my_restart_seq:
                    return
                try: bot_state.update_status(uid_str, "PAUSED", 0)
                except Exception: pass
                await asyncio.sleep(1.0)
            writer = None; gateway_ping_task = None
            team_coord_task = None; member_trigger_task = None
            try:
                if current_account_data:
                    fresh = None
                    if current_account_data.get('auth_type') == 'guest' and current_account_data.get('auth_uid'):
                        fresh = cache_get(str(current_account_data['auth_uid']))
                    elif current_account_data.get('auth_type') == 'token' and current_account_data.get('auth_token'):
                        fresh = cache_get(f"tok_{current_account_data['auth_token'][:20]}")
                    if fresh:
                        current_account_data = fresh
                        current_key = fresh['aes_ak']; current_iv = fresh['iv_i']
                        current_token = await build_tcp_startup_packet(
                            fresh['account_id'], fresh['token'], fresh['server_time'],
                            current_key, current_iv,
                            region=fresh.get('region', account_region), typ='OnLine')
                    else: raise ConnectionError("Cache expired")
                resolved_ip = await resolve_host_cloudflare(ip)
                reader, writer = await asyncio.open_connection(resolved_ip, int(port))
                bot_state.register_writer(uid_str, writer)
                _writer_ref["w"] = writer
                raw_sock = writer.get_extra_info('socket')
                if raw_sock: optimize_tcp_socket(raw_sock)
                writer.write(bytes.fromhex(current_token)); await writer.drain()
                try:
                    init_ka = await send_keep_alive(account_region)
                    if init_ka and not writer.is_closing():
                        writer.write(init_ka)
                        await asyncio.wait_for(writer.drain(), timeout=3)
                except Exception: pass

                async def func_gateway_keepalive():
                    ka_bytes = await send_keep_alive(account_region)
                    while True:
                        await asyncio.sleep(5)
                        try:
                            if writer and not writer.is_closing():
                                writer.write(ka_bytes); await writer.drain()
                        except Exception: break

                gateway_ping_task = asyncio.create_task(func_gateway_keepalive())
                print_premium(f"TCP Gateway Connected | UID: {uid_str} | squad={gid} | region={account_region}",
                              color=PX.MINT, icon=I["check"])
                reconnects = 0; no_response_count = 0
                if ENABLE_NEWBIE_CHARACTER and NEWBIE_SELECT_BEFORE_TEAM:
                    print_warning("Newbie select diaktifkan — berisiko Connection lost!")
                async with team_state["lock"]:
                    team_state["peers"][uid_str] = {
                        "writer": writer, "data": current_account_data,
                        "key": current_key, "iv": current_iv}
                    if team_state["leader_uid"] is None:
                        team_state["leader_uid"] = uid_str
                        print_premium(f"TEAM[{gid}] {uid_str} is first peer (leader)",
                                      color=PX.GOLD, icon=I["crown"])
                try: await _mark_team_joined(uid_str, gid)
                except Exception: pass

                async def send_solo_start_match():
                    nonlocal search_attempts
                    search_attempts += 1
                    try:
                        try: bot_state.update_status(uid_str, "SEARCHING", 0)
                        except Exception: pass
                        await asyncio.sleep(random.uniform(0.2, 0.4))
                        try:
                            own_id = current_account_data.get('account_id') if current_account_data else uid_str
                            rdy = ready_for_game(int(own_id), current_key, current_iv)
                            if writer and not writer.is_closing():
                                writer.write(rdy); await writer.drain()
                        except Exception: pass
                        await asyncio.sleep(1.0)
                        if CS_MODE_ENABLED:
                            cs_pkt = await CS_Solo_Start_Matchmaking_Packet(current_key, current_iv,
                                                                            region=account_region)
                            if writer and not writer.is_closing():
                                writer.write(cs_pkt); await writer.drain()
                                print_premium(f"CS Solo matchmaking sent #{search_attempts} | squad={gid} | region={account_region}",
                                              color=PX.AMBER, icon=I["target"])
                        else:
                            await start_game_battle_royale(account_region, client_version, writer, current_key, current_iv)
                    except Exception as e: print_warning(f"Solo: {e}")

                if not _match_played["flag"]:
                    if not TEAM_MODE: await send_solo_start_match()
                    if TEAM_MODE:
                        team_coord_task = asyncio.create_task(_team_coordinator())
                        member_trigger_task = asyncio.create_task(_member_match_trigger())
                else:
                    print_info(f"IDLE {uid_str} resuming in idle mode")

                while True:
                    play_matches[:] = [m for m in play_matches if not m.done()]
                    if bot_state.is_paused(uid_str): break
                    if squad_restart["seq"] != my_restart_seq:
                        print_warning(f"[RESTART-{gid}] {uid_str} restarting for Squad {gid}")
                        try: bot_state.update_status(uid_str, "OFFLINE", 0)
                        except Exception: pass
                        return
                    if _match_played["flag"]:
                        try: data = await asyncio.wait_for(reader.read(8192), timeout=1.0)
                        except asyncio.TimeoutError: continue
                        if not data: raise ConnectionError("Connection closed")
                        if len(data) > 20 and data.hex().startswith("0600"):
                            await _process_social_packet(data, tag="IDLE")
                        continue
                    now = asyncio.get_running_loop().time()
                    if not TEAM_MODE and len(play_matches) == 0 and (now - last_start_time >= START_MATCH_INTERVAL):
                        await send_solo_start_match()
                        last_start_time = now
                    try: data = await asyncio.wait_for(reader.read(8192), timeout=0.5)
                    except asyncio.TimeoutError:
                        no_response_count += 1; continue
                    if not data: raise ConnectionError("Connection closed")
                    hex_data = data.hex(); packet_length = len(data)
                    no_response_count = 0
                    if hex_data.startswith("0600") and packet_length > 20:
                        await _process_social_packet(data, tag="MAIN"); continue
                    if hex_data.startswith("0500") and packet_length > 10:
                        try:
                            inner = bytes.fromhex(hex_data[10:])
                            dec = decode_protobuf_dict(inner)
                            if not dec:
                                alt = decode_protobuf_2(inner)
                                if alt: dec = {str(k): {"data": v} for k, v in alt.items()}
                            f5w = dec.get("5") or dec.get(5)
                            f5 = f5w.get("data") if isinstance(f5w, dict) and "data" in f5w else f5w
                            if not isinstance(f5, dict): f5 = dec
                            def _f5g(key):
                                if not isinstance(f5, dict): return None
                                v = f5.get(key) if key in f5 else f5.get(str(key))
                                if isinstance(v, dict) and "data" in v: return v["data"]
                                return v
                            tc = None
                            for fk in [11, 5, 1, 3]:
                                cand = _f5g(fk)
                                if cand and str(cand).isdigit() and len(str(cand)) == 7:
                                    tc = str(cand); break
                            if tc:
                                async with team_state["lock"]:
                                    team_state["team_code"] = tc
                                print_premium(f"TEAM[{gid}] Code: {tc}", color=PX.ROSE, icon=I["gem"])
                            group_id = _f5g(8)
                            if group_id and isinstance(group_id, str) and 20 <= len(group_id) <= 40: pass
                            else: group_id = None
                            own_acc = None
                            if current_account_data: own_acc = str(current_account_data.get('account_id'))
                            inviter = None
                            for fk in [1,2,3,4,6,7,13,15,20]:
                                cand = _f5g(fk)
                                if cand and str(cand).isdigit() and 6 <= len(str(cand)) <= 15:
                                    if str(cand) != uid_str and str(cand) != own_acc:
                                        inviter = cand; break
                            if inviter and group_id and team_state["leader_uid"] != uid_str:
                                print_premium(f"TEAM[{gid}] Invite from {inviter} → accept",
                                              color=PX.CYAN, icon=I["arrow"])
                                for _ in range(2):
                                    try:
                                        acc = accept_team_invite(int(inviter), group_id,
                                                                 current_key, current_iv,
                                                                 region=account_region,
                                                                 game_version=client_version)
                                        if writer and not writer.is_closing():
                                            writer.write(acc); await writer.drain()
                                    except Exception as e: print_warning(f"TEAM[{gid}] accept err: {e}")
                                    await asyncio.sleep(0.4)
                        except Exception as e: print_warning(f"TEAM[{gid}] 0500 parse: {e}")
                        continue
                    if hex_data.startswith("0300") and 10 < packet_length < 30: continue
                    if hex_data.startswith("0300") and packet_length >= 300:
                        print_premium(f"Match Found | UID: {uid_str} | squad={gid} | region={account_region}",
                                      color=PX.AMBER, icon=I["target"])
                        try: await _mark_match_found(uid_str)
                        except Exception: pass
                        try: await _clear_team_joined(uid_str)
                        except Exception: pass
                        for tk in (team_coord_task, member_trigger_task):
                            if tk and not tk.done(): tk.cancel()
                        team_coord_task = None; member_trigger_task = None
                        _team_active["flag"] = False
                        try:
                            res = json.loads(await decode_protobuf_async(hex_data[10:]))
                            token = udp_key = match_code = server_ip_port = None
                            match_account_id = block_val = None
                            if '42' in res and 'data' in res['42']: match_code = res['42']['data']
                            if '5' in res and 'data' in res['5']:
                                rf5 = res['5']['data']
                                server_ip_port = rf5.get('2', {}).get('data')
                                udp_key = rf5.get('3', {}).get('data')
                                token = rf5.get('4', {}).get('data')
                                if '42' in rf5: match_code = rf5['42']['data']
                            if '1' in res and 'data' in res['1']: match_account_id = res['1']['data']
                            if '5' in res and 'data' in res['5']:
                                block_val = res['5']['data'].get('1', {}).get('data')
                            effective_acc_id = match_account_id or account_id or "BD_BOT"
                            if token and udp_key and match_code and server_ip_port:
                                acc_tok = current_account_data.get('access_token', '') if current_account_data else ""
                                if CS_MODE_ENABLED:
                                    thunder, sharma = await build_cs_match_startup_packets(
                                        token, udp_key, match_code, effective_acc_id, block_val or 0,
                                        server_ip=server_ip_port, region=account_region,
                                        client_version=client_version, access_token=acc_tok)
                                else:
                                    thunder, sharma = await build_match_startup_packets(
                                        token, udp_key, match_code, effective_acc_id, block_val or 0,
                                        server_ip=server_ip_port, region=account_region,
                                        client_version=client_version, access_token=acc_tok,
                                        mode_id=1, map_id=1)
                                match_index = await _inc_match(uid_str)
                                print_info(f"{'CS ' if CS_MODE_ENABLED else ''}[{gid}] Match #{match_index} → {server_ip_port}")
                                try:
                                    bot_state.increment_match_started()
                                    bot_state.update_status(uid_str, "IN_MATCH (CS)" if CS_MODE_ENABLED
                                                            else "IN_MATCH (TEAM)", 1)
                                except Exception: pass
                                game_fn = play_game_cs if CS_MODE_ENABLED else play_game
                                new_match = asyncio.create_task(
                                    game_fn(server_ip_port, thunder, sharma, udp_key,
                                            match_code, effective_acc_id, "ID",
                                            client_version, current_key, current_iv,
                                            match_index=match_index, squad_id=gid))
                                play_matches.append(new_match)

                                async def drain_gw():
                                    while not new_match.done():
                                        try:
                                            dg = await asyncio.wait_for(reader.read(4096), timeout=1.0)
                                            if not dg: break
                                            gh = dg.hex()
                                            if gh.startswith("0600") and len(dg) > 20:
                                                await _process_social_packet(dg, tag="DRAIN")
                                        except asyncio.TimeoutError: continue
                                        except Exception: break
                                drain_task = asyncio.create_task(drain_gw())
                                try: await new_match
                                except Exception as e: print_error(f"Match #{match_index} {e}")
                                finally:
                                    drain_task.cancel()
                                    try: await drain_task
                                    except asyncio.CancelledError: pass
                                play_matches[:] = [m for m in play_matches if not m.done()]
                                _match_played["flag"] = True
                                print_premium(f"IDLE {uid_str} parked after match",
                                              color=PX.SLATE, icon=I["dot"])
                                continue
                        except Exception as e: print_warning(f"MATCH {e}"); continue
                    if 30 <= packet_length <= 40: continue
            except asyncio.CancelledError: raise
            except Exception as e:
                if "Cache expired" in str(e):
                    print_warning(f"Token expired {uid_str}"); break
                reconnects += 1
                if reconnects > max_reconnects:
                    if current_account_data:
                        try:
                            if current_account_data.get('auth_uid'):
                                cache_invalidate(str(current_account_data['auth_uid']))
                            if current_account_data.get('auth_token'):
                                cache_invalidate(f"tok_{current_account_data['auth_token'][:20]}")
                        except Exception: pass
                    reconnects = 0; break
                print_warning(f"{uid_str} Reconnect #{reconnects}: {e}")
                await asyncio.sleep(min(reconnects * 0.5, 2.0))
            finally:
                _team_active["flag"] = False
                async with team_state["lock"]:
                    team_state["peers"].pop(uid_str, None)
                    if team_state["leader_uid"] == uid_str:
                        team_state["leader_uid"] = None
                        team_state["team_code"] = None
                try: await _clear_team_joined(uid_str)
                except Exception: pass
                for tk in (team_coord_task, member_trigger_task):
                    if tk and not tk.done():
                        tk.cancel()
                        try: await tk
                        except asyncio.CancelledError: pass
                if gateway_ping_task: gateway_ping_task.cancel()
                if writer:
                    bot_state.unregister_writer(uid_str, writer)
                    await safe_close_writer(writer)
                if not _match_played["flag"]: _team_active["flag"] = True
    except asyncio.CancelledError:
        print_info(f"FUNCTIONAL Task cancelled for {uid_str}")
        raise
    finally:
        for m in play_matches:
            if not m.done(): m.cancel()

# ==================== INFORMATIONAL ====================
async def informational(addrs, starter_packet, key, iv, region="ID",
                        account_id="", max_reconnects=3, account_data=None):
    uid_str = str(account_id); reconnects = 0
    ip, port = addrs.split(":")
    while True:
        while uid_str and bot_state.is_paused(uid_str):
            await asyncio.sleep(1.0)
        writer = None; ping_task = None
        try:
            resolved_ip = await resolve_host_cloudflare(ip)
            reader, writer = await asyncio.open_connection(resolved_ip, int(port))
            if uid_str: bot_state.register_writer(uid_str, writer)
            raw_sock = writer.get_extra_info('socket')
            if raw_sock: optimize_tcp_socket(raw_sock)
            writer.write(bytes.fromhex(starter_packet)); await writer.drain()
            reconnects = 0
            try:
                init_ka = await send_keep_alive(region)
                if init_ka and not writer.is_closing():
                    writer.write(init_ka)
                    await asyncio.wait_for(writer.drain(), timeout=3)
            except Exception: pass
            async def info_ka():
                ka = await send_keep_alive(region)
                while True:
                    await asyncio.sleep(5)
                    try:
                        if writer and not writer.is_closing():
                            writer.write(ka); await writer.drain()
                    except Exception: break
            ping_task = asyncio.create_task(info_ka())
            print_premium(f"INFO Connected | UID: {uid_str} | region={region}",
                          color=PX.SKY, icon=I["dot"])
            while True:
                if uid_str and bot_state.is_paused(uid_str):
                    if ping_task: ping_task.cancel()
                    if uid_str: bot_state.unregister_writer(uid_str, writer)
                    await safe_close_writer(writer); writer = None
                    while bot_state.is_paused(uid_str): await asyncio.sleep(1.0)
                    break
                try: data = await asyncio.wait_for(reader.read(8192), timeout=1.0)
                except asyncio.TimeoutError: continue
                if not data: raise ConnectionError("closed")
        except asyncio.CancelledError:
            if ping_task: ping_task.cancel()
            if uid_str: bot_state.unregister_writer(uid_str, writer)
            await safe_close_writer(writer); raise
        except Exception:
            if ping_task: ping_task.cancel()
            if uid_str: bot_state.unregister_writer(uid_str, writer)
            await safe_close_writer(writer)
            reconnects += 1
            if reconnects > max_reconnects:
                await asyncio.sleep(3); reconnects = 0
            else: await asyncio.sleep(1)

# ==================== ACCOUNT HELPERS ====================
def _register_credentials(ad):
    try:
        bot_state.account_credentials[str(ad['account_id'])] = ad
        if ad.get('auth_uid'): bot_state.account_credentials[str(ad['auth_uid'])] = ad
    except Exception: pass

async def refresh_account_profile(ad_or_uid):
    try:
        if isinstance(ad_or_uid, str):
            uid = str(ad_or_uid); ad = bot_state.account_credentials.get(uid)
        else:
            ad = ad_or_uid; uid = str(ad.get('account_id'))
        if not ad: return
        token = ad.get('token'); acc_id = ad.get('account_id')
        srv = ad.get('server_url'); rel = ad.get('release_version')
        if not (token and acc_id and srv and rel): return
        data = await get_player_personal_show(int(acc_id), token, srv, rel)
        if not data: return
        pd = data.get(1, {}) if isinstance(data.get(1), dict) else {}
        nickname = pd.get(3); lvl = pd.get(6); exp = pd.get(7)
        if exp is None: return
        try:
            exp = int(exp); lvl = int(lvl) if lvl else 1
        except Exception: return
        aid = str(acc_id)
        if aid not in bot_state.accounts:
            bot_state.register_account(aid, nickname or f"Player_{aid}",
                region=ad.get('region','BD'), level=lvl, exp=exp,
                auth_uid=ad.get('auth_uid'), squad_id=ad.get('squad_id', 'A'))
            return
        old = bot_state.accounts[aid].get("current_exp", 0)
        bot_state.update_exp(aid, exp, lvl)
        if nickname: bot_state.accounts[aid]["nickname"] = nickname
        if exp > old:
            print_premium(f"+{exp-old:,} EXP | {aid}", color=PX.GOLD, icon=I["spark"])
    except Exception: pass

async def process_account_uid_pass(uid, password, region_override=None, squad_id="A"):
    squad = str(squad_id or "A").upper()
    cached = cache_get(uid)
    if cached:
        aid = str(cached['account_id'])
        nick = cached.get('nickname', f"Player_{aid}")
        lvl = cached.get('level', 1); expv = cached.get('exp', 0)
        print_premium(f"Online (cache): {aid} | {nick} | region={cached.get('region','BD')} | squad={squad}",
                      color=PX.MINT, icon=I["check"])
        bot_state.register_account(aid, nick, cached.get('region','BD'),
            lvl, expv, cached.get('likes',0), auth_uid=str(uid), squad_id=squad)
        cached['squad_id'] = squad
        _register_credentials(cached); return cached
    print_info(f"LOGIN UID: {uid} (squad={squad})")
    try:
        async with _LOGIN_SEMAPHORE:
            vc = await version_config(region_override or "ID")
            if not vc: return None
            release_version, client_version, server_url, gop_1, app_version = vc
            tg = await get_access_token(uid, password)
            if not tg: return None
            open_id, access_token, platform = tg
            major_payload, login_payload = await get_payload(
                access_token, open_id, platform, client_version)
            res_json = await major_login(major_payload, server_url, release_version)
            if not res_json: return None
            def _gd(k):
                v = res_json.get(str(k))
                if isinstance(v, dict) and "data" in v: return v["data"]
                if k in res_json and not isinstance(res_json[k], dict): return res_json[k]
                if isinstance(v, dict): return v.get("data")
                return None
            acc_id_raw = _gd(1); region_raw = _gd(2) or "ID"
            jwt_token = _gd(8); server_url_raw = _gd(10); server_time = _gd(21)
            aes_ak, iv_i = _extract_key_iv(res_json)
            if not jwt_token or not server_url_raw or not aes_ak: return None
            getlogin_json = await get_login_data(
                login_payload, jwt_token, server_url_raw, release_version)
            if not getlogin_json: return None
        def _gf(f, d=None):
            v = getlogin_json.get(str(f), {}).get("data")
            return v if v is not None else d
        level = int(_gf(6,1) or 1); exp = int(_gf(7,0) or 0)
        likes = int(_gf(8,0) or 0)
        nickname = _gf(4, f"Player_{acc_id_raw}") or f"Player_{acc_id_raw}"
        region = region_raw or _gf(3,"ID") or "ID"
        acc_id = str(acc_id_raw)
        bot_state.register_account(acc_id, nickname, region, level, exp, likes,
                                   auth_uid=str(uid), squad_id=squad)
        print_premium(f"Login: {acc_id} | {nickname} | Lvl {level} | region={region} | squad={squad}",
                      color=PX.GOLD, icon=I["gem"])
        ad = {'account_id':acc_id_raw,'nickname':nickname,'region':region,
            'level':level,'exp':exp,'likes':likes,'open_id':open_id,
            'access_token':access_token,'platform':str(platform),
            'token':jwt_token,'server_time':server_time,
            'aes_ak':aes_ak,'iv_i':iv_i,
            'functional_addrs':_gf(14),'informational_addrs':_gf(32),
            'release_version':release_version,'client_version':client_version,
            'server_url':server_url_raw,'login_payload_data':login_payload,
            'auth_type':'guest','auth_uid':uid,'auth_password':password,
            'squad_id': squad}
        _register_credentials(ad); cache_set(uid, ad); return ad
    except Exception as e:
        print_error(f"login err: {e}"); return None

async def run_account_worker(ad, label, region_override=None, clan_override=None, squad_id="A"):
    acc_id = str(ad['account_id'])
    squad = str(squad_id or ad.get('squad_id', 'A') or 'A').upper()
    ad['squad_id'] = squad
    info_task = None; exp_task = None
    try:
        reg = region_override or ad.get('region', 'BD')

        # -------------------------------------------------------------
        # ধাপ ১: প্রোফাইল কাস্টমাইজেশন (Equip, Homer, Bio, Clan)
        # -------------------------------------------------------------
        print_info(f"[{acc_id}][{squad}] Claiming Rewards & Equipping HeadPic/Banner...")
        await run_equip_workflow(ad['token'], ad['server_url'], ad.get('release_version', 'OB55'))
        await asyncio.sleep(1.0)

        print_info(f"[{acc_id}][{squad}] Setting up Homer & Skills...")
        await equip_homer_async(ad['token'], ad['server_url'], ad.get('release_version', 'OB55'))
        await asyncio.sleep(1.0)

        print_info(f"[{acc_id}][{squad}] Updating Bio...")
        await change_bio(ad['token'], "[C][B]POWER OFF MAHIR", ad['server_url'])
        await asyncio.sleep(1.0)

        if clan_override:
            print_info(f"[{acc_id}][{squad}] Joining Clan {clan_override}...")
            await join_clan(ad['token'], clan_override)
            await asyncio.sleep(1.0)

        # -------------------------------------------------------------
        # ধাপ ২: অফলাইনে যাওয়া (Offline Pause)
        # -------------------------------------------------------------
        print_warning(f"[{acc_id}][{squad}] Setup finished. Going OFFLINE for 3 seconds...")
        bot_state.update_status(acc_id, "OFFLINE")
        await asyncio.sleep(3.0)

        # -------------------------------------------------------------
        # ধাপ ৩: পুনরায় অনলাইনে আসা এবং আগের সব কাজ চালু করা
        # -------------------------------------------------------------
        print_success(f"[{acc_id}][{squad}] Back ONLINE! Starting TCP Gateway & Matchmaking...")
        bot_state.update_status(acc_id, "ONLINE")

        tcp_online = await build_tcp_startup_packet(
            ad['account_id'], ad['token'], ad['server_time'],
            ad['aes_ak'], ad['iv_i'], region=reg, typ='OnLine')
        tcp_chat = await build_tcp_startup_packet(
            ad['account_id'], ad['token'], ad['server_time'],
            ad['aes_ak'], ad['iv_i'], region=reg, typ='ChaT')

        info_task = asyncio.create_task(informational(
            ad['informational_addrs'], tcp_chat, ad['aes_ak'], ad['iv_i'],
            region=reg, account_id=acc_id, account_data=ad))

        async def exp_refresher():
            while True:
                await asyncio.sleep(90 + random.uniform(-10, 10))
                fresh = bot_state.account_credentials.get(acc_id)
                if fresh: await refresh_account_profile(fresh)
        exp_task = asyncio.create_task(exp_refresher())

        await functional_lone_wolf(
            ad['functional_addrs'], tcp_online, reg, ad['client_version'],
            ad['aes_ak'], ad['iv_i'], account_id=acc_id, account_data=ad,
            squad_id=squad)

    except asyncio.CancelledError:
        raise
    except Exception as e:
        print_error(f"worker err {label}: {e}")
    finally:
        for t in (info_task, exp_task):
            if t and not t.done(): t.cancel()
        for t in (info_task, exp_task):
            if t:
                try: await t
                except Exception: pass

async def account_loop_guest(uid, password, region_override=None, clan_override=None, squad_id="A"):
    uid_str = str(uid)
    squad = str(squad_id or "A").upper()
    bot_state.account_workers[uid_str] = asyncio.current_task()
    acc_id = None
    while True:
        try:
            bot_state.update_status(uid_str, "CONNECTING")
            ad = await process_account_uid_pass(uid_str, password, region_override, squad_id=squad)
            if not ad:
                print_error(f"Login failed {uid_str}. Retry 15s"); await asyncio.sleep(15); continue
            ad['squad_id'] = squad
            acc_id = str(ad['account_id'])
            if acc_id in bot_state.accounts:
                bot_state.accounts[acc_id]['squad_id'] = squad
            bot_state.account_workers[acc_id] = asyncio.current_task()
            bot_state.auth_to_game_id[uid_str] = acc_id
            bot_state.game_to_auth_id[acc_id] = uid_str
            await run_account_worker(ad, uid_str, region_override, clan_override, squad_id=squad)
            await asyncio.sleep(3)
        except asyncio.CancelledError:
            try:
                bot_state.update_status(uid_str, "OFFLINE")
                if acc_id: bot_state.update_status(acc_id, "OFFLINE")
            except Exception: pass
            try:
                await _clear_team_joined(uid_str)
                if acc_id: await _clear_team_joined(acc_id)
            except Exception: pass
            break
        except Exception as e:
            print_error(f"err {uid_str}: {e}"); await asyncio.sleep(10)

# ==================== CREATE ACCOUNTS ====================
def _gf_field(ld, key, default=None):
    if not ld: return default
    v = ld.get(str(key), {})
    if isinstance(v, dict): return v.get("data", default)
    return v if v is not None else default

async def choose_region(region, jwt_token, login_url, release_version):
    region_code = region.upper()
    url = f"{login_url.rstrip('/')}/ChooseRegion"
    proto = create_proto({1: region_code})
    payload = bytes.fromhex(encrypt_aes(proto.hex()))
    hdrs = {"Accept-Encoding": "gzip", "Authorization": f"Bearer {jwt_token}",
        "Connection": "Keep-Alive",
        "Content-Type": "application/x-www-form-urlencoded",
        "ReleaseVersion": f"{release_version}",
        "User-Agent": "UnityPlayer/2018.4.12f1",
        "X-GA": "v1 1", "X-GA-SV": str(int(time.time())),
        "X-Unity-Version": "2018.4.12f1"}
    try:
        ssl_ctx = ssl.create_default_context()
        ssl_ctx.check_hostname = False; ssl_ctx.verify_mode = ssl.CERT_NONE
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=15)) as s:
            async with s.post(url, data=payload, headers=hdrs, ssl=ssl_ctx) as r:
                print_info(f"CHOOSE-REGION {region} → HTTP {r.status}")
                return r.status
    except Exception as e:
        print_error(f"CHOOSE-REGION {e}"); return None

async def major_register(release_v, access_token, open_id, name, game_version,
                          login_url, lang_code="en"):
    try:
        field14 = bytes(ord(c) ^ KEYSTREAM[i % 32] for i, c in enumerate(open_id))
        fields = {1: name, 2: access_token, 3: open_id, 5: 102000007,
                  6: 4, 7: 1, 13: 1, 14: field14, 15: lang_code,
                  16: 2, 20: "2.132.4", 21: 1, 22: GGRE_RAW}
        proto = _encode_proto_std(fields)
        payload = AES.new(AES_KEY, AES.MODE_CBC, AES_IV).encrypt(pad(proto, 16))
        url = f"{login_url.rstrip('/')}/MajorRegister"
        hdrs = {"Accept": "*/*", "Accept-Encoding": "deflate, gzip",
            "Authorization": "Bearer",
            "Content-Type": "application/x-www-form-urlencoded",
            "ReleaseVersion": f"{release_v}",
            "User-Agent": "UnityPlayer/2018.4.12f1",
            "X-GA": "v1 1", "X-GA-SV": str(int(time.time())),
            "X-Unity-Version": "2018.4.12f1"}
        ssl_ctx = ssl.create_default_context()
        ssl_ctx.check_hostname = False; ssl_ctx.verify_mode = ssl.CERT_NONE
        async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=30)) as s:
            async with s.post(url, headers=hdrs, data=payload, ssl=ssl_ctx) as resp:
                content = await resp.read()
                if resp.status != 200 or not content: return None
                for off in [0,64,48,32,80,16,8,96,128]:
                    if off >= len(content): continue
                    try:
                        r = decode_protobuf_2(content[off:])
                        if r and 3 in r:
                            return {str(k): {"data": v} for k, v in r.items()}
                    except Exception: pass
                if len(content) % 16 == 0:
                    try:
                        pt = AES.new(AES_KEY, AES.MODE_CBC, AES_IV).decrypt(content)
                        pad_len = pt[-1]
                        if 1 <= pad_len <= 16 and all(b == pad_len for b in pt[-pad_len:]):
                            pt = pt[:-pad_len]
                        r = decode_protobuf_2(pt)
                        if r and 3 in r:
                            return {str(k): {"data": v} for k, v in r.items()}
                    except Exception: pass
                return None
    except Exception as e:
        print_error(f"MAJOR-REG {e}"); return None

async def create_four_accounts(region: str, clan_id: str, count: int = 4, password: str = "MAHIR"):
    bot_state.creating = True
    bot_state.create_progress = []
    def _prog(s):
        try:
            print_premium(s, color=PX.VIOLET, icon=I["bolt"], tag="CREATE")
        except Exception: pass
        bot_state.create_progress.append(s)
    try:
        print_rule(f"⚡ AUTO-CREATE {count} BOTS · {region}", color=PX.MAGENTA)
        _prog(f"Fetching version config for {region}...")
        vc = await version_config(region)
        if not vc:
            _prog("Version config failed, retrying..."); return []
        release_v, remote_v, login_url, gop_1, app_version = vc
        if not login_url.endswith("/"): login_url += "/"
        lang = REGION_LANG.get(region.upper(), "en")
        game_version = remote_v or app_version
        _prog(f"Version OK | release={release_v} | game={game_version}")

        # --- Compute next free group letter (A, B, C...) ---
        existing_groups = set()
        for uid, acc in bot_state.accounts.items():
            g = acc.get('squad_id')
            if g: existing_groups.add(str(g).upper())
        next_group_idx = 0
        while chr(65 + next_group_idx) in existing_groups:
            next_group_idx += 1
        num_squads = (count + TEAM_SIZE - 1) // TEAM_SIZE
        first_g = chr(65 + next_group_idx)
        last_g = chr(65 + next_group_idx + num_squads - 1)
        _prog(f"Splitting into {num_squads} squad(s) → Group {first_g}..{last_g}")

        created = []
        attempt = 0

        # যতগুলো অ্যাকাউন্ট বলা হয়েছে ঠিক ততগুলো সফলভাবে তৈরি না হওয়া পর্যন্ত লুপ চলবে
        while len(created) < count:
            attempt += 1
            idx = len(created) + 1
            squad_id = chr(65 + next_group_idx + ((idx - 1) // TEAM_SIZE))

            # ১. MAHIR_{RANDOM} ফরম্যাটে ৬ অক্ষরের র্যান্ডম পাসওয়ার্ড তৈরি
            rnd_suffix = "".join(random.choices(string.ascii_uppercase + string.digits, k=6))
            acc_password = f"MAHIR_{rnd_suffix}"

            _prog(f"Creating bot {idx}/{count} [Group {squad_id}] (Attempt #{attempt}) | Pass: {acc_password}...")
            try:
                # রেজিস্টার
                uid = await register_account(acc_password, gop_1, app_version)
                if not uid:
                    _prog(f"Bot {idx} failed at registration. Retrying in 3s...")
                    await asyncio.sleep(3.0)
                    continue

                # গ্রান্ট টোকেন
                tok = await grant_token(uid, acc_password, gop_1, app_version)
                if not tok:
                    _prog(f"Bot {idx} failed at grant token. Retrying in 3s...")
                    await asyncio.sleep(3.0)
                    continue

                open_id = tok["open_id"]
                access_token = tok["access_token"]
                platform = tok.get("platform", 4)
                
                major_payload, login_payload = await get_payload(
                    access_token, open_id, platform, game_version, lang)
                
                nickname_final = "MAHIR•" + "".join(
                    random.choices(string.ascii_uppercase + string.digits, k=5))
                
                # Major Register
                mr = await major_register(release_v, access_token, open_id,
                                          nickname_final, game_version, login_url, lang)
                if not mr:
                    _prog(f"Bot {idx} failed at MajorRegister. Retrying in 3s...")
                    await asyncio.sleep(3.0)
                    continue
                
                await asyncio.sleep(3.0)
                
                # Major Login #1
                res_json = None
                for _ in range(3):
                    mp, lp = await get_payload(
                        access_token, open_id, platform, game_version, lang)
                    res_json = await major_login(mp, login_url, release_v)
                    if res_json and (("8" in res_json) or (8 in res_json)):
                        login_payload = lp
                        break
                    res_json = None
                    await asyncio.sleep(2.0)
                
                if not res_json:
                    _prog(f"Bot {idx} failed at MajorLogin #1. Retrying in 3s...")
                    await asyncio.sleep(3.0)
                    continue

                def _gd(k):
                    v = res_json.get(str(k))
                    if isinstance(v, dict) and "data" in v: return v["data"]
                    if k in res_json and not isinstance(res_json[k], dict): return res_json[k]
                    if isinstance(v, dict): return v.get("data")
                    return None

                jwt_token = _gd(8)
                server_url_raw = _gd(10)
                server_time = _gd(21)
                acc_id_raw = _gd(1)

                if not jwt_token:
                    _prog(f"Bot {idx}: No JWT token received. Retrying in 3s...")
                    await asyncio.sleep(3.0)
                    continue

                # রিজিয়ন সিলেক্ট (প্রয়োজন হলে)
                if not server_url_raw:
                    _prog(f"   → ChooseRegion({region})...")
                    cr_status = await choose_region(region, jwt_token, login_url, release_v)
                    if cr_status != 200:
                        _prog(f"Bot {idx}: ChooseRegion failed. Retrying in 3s...")
                        await asyncio.sleep(3.0)
                        continue
                    
                    await asyncio.sleep(2.0)
                    res_json2 = None
                    for _ in range(3):
                        mp2, lp2 = await get_payload(
                            access_token, open_id, platform, game_version, lang)
                        res_json2 = await major_login(mp2, login_url, release_v)
                        if res_json2 and (("10" in res_json2) or (10 in res_json2)):
                            res_json = res_json2
                            login_payload = lp2
                            break
                        res_json2 = None
                        await asyncio.sleep(2.0)
                    
                    if not res_json2:
                        _prog(f"Bot {idx}: MajorLogin #2 failed. Retrying in 3s...")
                        await asyncio.sleep(3.0)
                        continue
                    
                    res_json = res_json2
                    jwt_token = _gd(8)
                    server_url_raw = _gd(10)
                    server_time = _gd(21)
                    acc_id_raw = _gd(1)

                aes_ak, iv_i = _extract_key_iv(res_json)
                if not aes_ak or not iv_i:
                    _prog(f"Bot {idx}: AES key/IV extraction failed. Retrying in 3s...")
                    await asyncio.sleep(3.0)
                    continue

                ld = await get_login_data(login_payload, jwt_token, server_url_raw, release_v)
                level, exp, likes = 1, 0, 0
                if ld:
                    def _gf(f, d=None):
                        v = ld.get(str(f), {}).get("data")
                        return v if v is not None else d
                    level = int(_gf(6, 1) or 1)
                    exp = int(_gf(7, 0) or 0)
                    likes = int(_gf(8, 0) or 0)
                    nickname_final = _gf(4, nickname_final) or nickname_final

                ad = {
                    'account_id': acc_id_raw, 'nickname': nickname_final,
                    'region': region, 'level': level, 'exp': exp, 'likes': likes,
                    'open_id': open_id, 'access_token': access_token,
                    'platform': str(platform), 'token': jwt_token,
                    'server_time': server_time, 'aes_ak': aes_ak, 'iv_i': iv_i,
                    'functional_addrs': _gf_field(ld, 14),
                    'informational_addrs': _gf_field(ld, 32),
                    'release_version': release_v, 'client_version': game_version,
                    'server_url': server_url_raw, 'login_payload_data': login_payload,
                    'auth_type': 'guest', 'auth_uid': uid, 'auth_password': acc_password,
                    'squad_id': squad_id,
                }
                _register_credentials(ad)
                cache_set(uid, ad)
                created.append(ad)
                
                _prog(f"✔ Bot {idx}/{count} [Group {squad_id}] Created: {nickname_final} | UID {acc_id_raw} | Pass: {acc_password}")
                await asyncio.sleep(1.0)

            except Exception as e:
                _prog(f"Bot {idx} Error: {e}. Retrying...")
                await asyncio.sleep(3.0)

        # সব অ্যাকাউন্ট সফলভাবে তৈরি হওয়ার পর ফাইলে সেভ করা
        if created:
            try:
                async with _accounts_file_lock:
                    existing = []
                    if os.path.exists(ACCOUNTS_FILE):
                        try:
                            with open(ACCOUNTS_FILE, "r", encoding="utf-8") as f:
                                existing = json.load(f) or []
                                if not isinstance(existing, list): existing = []
                        except Exception: existing = []
                    existing_uids = {str(a.get("uid")) for a in existing if isinstance(a, dict)}
                    for a in created:
                        u = str(a['auth_uid'])
                        if u not in existing_uids:
                            existing.append({
                                "uid": u,
                                "password": a['auth_password'],
                                "region": region,
                                "clan_id": clan_id,
                                "squad_id": a.get('squad_id', 'A'),
                            })
                    tmp = ACCOUNTS_FILE + ".tmp"
                    with open(tmp, "w", encoding="utf-8") as f:
                        json.dump(existing, f, indent=2, ensure_ascii=False)
                    os.replace(tmp, ACCOUNTS_FILE)
                _prog(f"All {len(created)} accounts saved to {ACCOUNTS_FILE}")
            except Exception as e:
                _prog(f"Save accounts error: {e}")

        # বট ওয়ার্কার চালু করা
        if created:
            _prog(f"Starting {len(created)} bot workers...")
            for i, a in enumerate(created):
                try:
                    squad_id = a.get('squad_id') or chr(65 + next_group_idx + (i // TEAM_SIZE))
                    a['squad_id'] = squad_id
                    task = asyncio.create_task(account_loop_guest(
                        str(a['auth_uid']), a['auth_password'],
                        region_override=region, clan_override=clan_id,
                        squad_id=squad_id))
                    bot_state.account_workers[str(a['auth_uid'])] = task
                    _prog(f"   → Worker {i+1}/{len(created)} [{squad_id}] started")
                    await asyncio.sleep(0.35)
                except Exception as e:
                    _prog(f"   Worker {i+1} start error: {e}")
            _prog(f"All {len(created)} bots launched successfully.")
        return created

    except Exception as e:
        _prog(f"create_four_accounts critical error: {e}")
        traceback.print_exc()
        return []
    finally:
        bot_state.creating = False
        print_rule(color=PX.MAGENTA)

# ==================== AUTO-LOAD ====================
async def _autoload_accounts():
    if not os.path.exists(ACCOUNTS_FILE):
        print_info("[BOOT] No accounts.json"); return
    try:
        with open(ACCOUNTS_FILE, "r", encoding="utf-8") as f:
            accounts = json.load(f) or []
    except Exception as e:
        print_error(f"[BOOT] Load fail: {e}"); return
    if not isinstance(accounts, list) or not accounts:
        print_info("[BOOT] accounts.json empty"); return
    print_premium(f"Auto-loading {len(accounts)} account(s)",
                  color=PX.GOLD, icon=I["star"], tag="BOOT")
    for i, a in enumerate(accounts):
        try:
            if not isinstance(a, dict): continue
            uid = str(a.get("uid", "")).strip()
            password = str(a.get("password", "")).strip()
            token = str(a.get("token", "")).strip()
            region = str(a.get("region", "")).strip() or None
            clan_id = str(a.get("clan_id", "")).strip() or CLAN_ID_DEFAULT
            squad_id = str(a.get("squad_id", "")).strip().upper() or _group_for_index(i)
            if token and not (uid and password):
                task = asyncio.create_task(account_loop_token(token, squad_id=squad_id))
                bot_state.account_workers[f"tok_{token[:20]}"] = task
                print_info(f"token worker ({i+1}/{len(accounts)}) squad={squad_id}")
            elif uid and password:
                task = asyncio.create_task(account_loop_guest(
                    uid, password, region_override=region,
                    clan_override=clan_id, squad_id=squad_id))
                bot_state.account_workers[uid] = task
                print_info(f"worker {uid} ({i+1}/{len(accounts)}) region={region} squad={squad_id}")
            await asyncio.sleep(0.5)
        except Exception as e:
            print_error(f"[BOOT] worker {i+1}: {e}")

# ==================== HTTP SERVER ====================
@aiohttp.web.middleware
async def _req_logger(request, handler):
    print(f"{PX.SLATE}[REQ]{PX.RESET} {PX.BOLD}{request.method}{PX.RESET} {PX.SKY}{request.path}{PX.RESET}")
    try:
        resp = await handler(request)
        print(f"{PX.SLATE}[RES]{PX.RESET} {PX.BOLD}{request.method}{PX.RESET} {PX.SKY}{request.path}{PX.RESET} {PX.DIM}→{PX.RESET} {PX.EMERALD}{resp.status}{PX.RESET}")
        return resp
    except aiohttp.web.HTTPException as e:
        if request.path.startswith("/api/"):
            return aiohttp.web.json_response(
                {"ok": False, "status": "error", "error": e.reason or str(e)},
                status=e.status)
        raise
    except Exception as e:
        traceback.print_exc()
        if request.path.startswith("/api/"):
            return aiohttp.web.json_response(
                {"ok": False, "status": "error", "error": str(e)}, status=500)
        raise

async def serve_index(request):
    for path in (INDEX_HTML_PATH, "index.html"):
        try:
            with open(path, "r", encoding="utf-8") as f:
                return aiohttp.web.Response(text=f.read(), content_type="text/html")
        except Exception: continue
    return aiohttp.web.Response(text="<h1> MAHIR free</h1>", content_type="text/html")

async def api_ping(request):
    return aiohttp.web.json_response({"pong": True, "app": "MAHIR FREE", "version": "2.0"})

async def api_stats(request):
    try:
        accs = list(bot_state.accounts.values())
        online = sum(1 for a in accs if a.get("status") in ("ONLINE","IN_MATCH","SEARCHING"))
        active_matches = sum(a.get("active_matches", 0) for a in accs)
        uptime = max(1, int(time.time() - bot_state.start_time))
        uptime_h = max(0.016, uptime / 3600.0)
        exp_rate = int(bot_state.total_exp_gained / uptime_h) if uptime_h > 0 else 0
        matches_rate = int(bot_state.matches_started / uptime_h) if uptime_h > 0 else 0
        logs_out = []
        for l in bot_state.logs[-200:]:
            try:
                logs_out.append({"time": str(l.get("time","")),
                                 "message": str(l.get("message","")),
                                 "level": str(l.get("level","info"))})
            except Exception: continue

        # ── Groups snapshot ──
        groups_map = {}
        for a in accs:
            gid = str(a.get('squad_id', 'A') or 'A').upper()
            if gid not in groups_map:
                t = _get_team(gid)
                groups_map[gid] = {
                    "group": gid,
                    "size": len(t["peers"]),
                    "leader_uid": t["leader_uid"],
                    "team_code": t["team_code"],
                    "members": list(t["peers"].keys()),
                    "account_count": 0,
                    "in_match_count": 0,
                }
            groups_map[gid]["account_count"] += 1
            if "IN_MATCH" in str(a.get("status", "")).upper():
                groups_map[gid]["in_match_count"] += 1

        teams_snap = _all_teams_snapshot()
        first_team_code = teams_snap[0]["team_code"] if teams_snap else None
        first_leader = teams_snap[0]["leader_uid"] if teams_snap else None

        data = {
            "accounts": accs, "logs": logs_out,
            "groups": sorted(groups_map.values(), key=lambda x: x["group"]),
            "total_accounts": len(accs), "total_online": online,
            "total_matches": bot_state.total_matches,
            "total_matches_started": bot_state.matches_started,
            "total_active_matches": active_matches,
            "total_gained_exp": bot_state.total_exp_gained,
            "uptime": uptime, "exp_per_hour": exp_rate,
            "matches_per_hour": matches_rate,
            "creating": bool(bot_state.creating),
            "create_progress": [str(x) for x in bot_state.create_progress[-40:]],
            "team_code": first_team_code,
            "leader_uid": first_leader,
            "team_size": sum(len(t["peers"]) for t in _teams_state.values()),
            "restart_finished": sum(len(s["finished_bots"]) for s in _squad_restart_states.values()),
            "restart_target": sum((s["target"] or 0) for s in _squad_restart_states.values()) or None,
            "restarting": any(s["restarting"] for s in _squad_restart_states.values()),
        }
        return aiohttp.web.Response(text=json.dumps(data, default=str, ensure_ascii=False),
                                    content_type="application/json", charset="utf-8")
    except Exception as e:
        traceback.print_exc()
        return aiohttp.web.Response(text=json.dumps({"error": str(e), "accounts": [],
            "logs": [], "groups": [], "create_progress": [], "creating": False,
            "total_accounts": 0, "total_matches_started": 0, "total_matches": 0,
            "total_active_matches": 0, "total_gained_exp": 0, "uptime": 1,
            "exp_per_hour": 0}), content_type="application/json", charset="utf-8")

async def api_state(request):
    try:
        return aiohttp.web.Response(text=json.dumps({
            "creating": bool(bot_state.creating),
            "create_progress": [str(x) for x in bot_state.create_progress[-40:]],
            "accounts": list(bot_state.accounts.values()),
            "groups": _all_teams_snapshot(),
            "team_size": sum(len(t["peers"]) for t in _teams_state.values()),
        }, default=str, ensure_ascii=False), content_type="application/json", charset="utf-8")
    except Exception as e:
        return aiohttp.web.Response(text=json.dumps({"error": str(e), "creating": False,
                                    "create_progress": []}),
                                    content_type="application/json", charset="utf-8")

async def api_progress(request):
    try:
        lines = [str(x) for x in bot_state.create_progress[-60:]]
        text = '{"creating":' + ("true" if bot_state.creating else "false") + \
               ',"create_progress":' + json.dumps(lines) + '}'
        return aiohttp.web.Response(text=text, content_type="application/json")
    except Exception:
        return aiohttp.web.Response(text='{"creating":false,"create_progress":[]}',
                                    content_type="application/json")

async def api_create_team(request):
    try:
        body = await request.json()
        region = str(body.get("region", "ID")).upper()
        clan_id = str(body.get("clan_id", "")).strip()
        count = int(body.get("count", 4))
        password = str(body.get("password", "MAHIR")).strip() or "MAHIR"
        if not clan_id:
            return aiohttp.web.json_response({"ok": False, "error": "clan_id required"})
        if bot_state.creating:
            return aiohttp.web.json_response({"ok": False, "error": "already creating"})
        count = max(1, min(16, count))
        asyncio.create_task(create_four_accounts(region, clan_id, count, password))
        squads = (count + TEAM_SIZE - 1) // TEAM_SIZE
        return aiohttp.web.json_response({"ok": True,
                                          "msg": f"creating {count} bots in {squads} squad(s)"})
    except Exception as e:
        traceback.print_exc()
        return aiohttp.web.json_response({"ok": False, "error": str(e)})

async def api_account_add(request):
    try:
        body = await request.json()
        squad_id = str(body.get("squad_id", "") or _assign_squad_for_new_account()).strip().upper()
        region = str(body.get("region", "BD") or "BD").strip().upper()
        clan_id = str(body.get("clan_id", "") or CLAN_ID_DEFAULT).strip()

        if body.get("token"):
            token = str(body["token"]).strip()
            if not token:
                return aiohttp.web.json_response({"status": "error", "error": "empty token"})
            async with _accounts_file_lock:
                accs = await _read_accounts_file_unlocked()
                if not any(isinstance(a, dict) and str(a.get("token", "")).strip() == token for a in accs):
                    accs.append({"token": token, "region": region, "clan_id": clan_id, "squad_id": squad_id})
                    await _write_accounts_file_unlocked(accs)
            asyncio.create_task(account_loop_token(token, squad_id=squad_id))
            return aiohttp.web.json_response({"status": "ok"})

        uid = str(body.get("uid", "")).strip()
        password = str(body.get("password", "")).strip()
        if not uid or not password:
            return aiohttp.web.json_response({"status": "error", "error": "uid/password required"})
        async with _accounts_file_lock:
            accs = await _read_accounts_file_unlocked()
            if not any(isinstance(a, dict) and str(a.get("uid", "")).strip() == uid for a in accs):
                accs.append({"uid": uid, "password": password, "region": region, "clan_id": clan_id, "squad_id": squad_id})
                await _write_accounts_file_unlocked(accs)
        asyncio.create_task(account_loop_guest(uid, password, region_override=region, clan_override=clan_id, squad_id=squad_id))
        return aiohttp.web.json_response({"status": "ok"})
    except Exception as e:
        return aiohttp.web.json_response({"status": "error", "error": str(e)})

async def api_account_delete(request):
    try:
        body = await request.json()
        uid = str(body.get("uid", "")).strip()
        auth_uid = str(body.get("auth_uid", "")).strip()

        # ── Build complete identifier set (game UID + guest auth UID + mappings) ──
        resolved = {x for x in (uid, auth_uid) if x}

        # Translate via live mappings
        for u in list(resolved):
            v = bot_state.game_to_auth_id.get(u)
            if v: resolved.add(str(v))
            v2 = bot_state.auth_to_game_id.get(u)
            if v2: resolved.add(str(v2))

        # Pull auth_uid from the live account record (most reliable source)
        for u in list(resolved):
            acc = bot_state.accounts.get(u)
            if acc and acc.get("auth_uid"):
                resolved.add(str(acc["auth_uid"]))
        # And reverse (auth_uid passed but only account_id known)
        if auth_uid:
            for gid, gacc in bot_state.accounts.items():
                if str(gacc.get("auth_uid", "")) == auth_uid:
                    resolved.add(str(gid))

        # Try cache lookup too (if the bot was never fully loaded)
        for u in list(resolved):
            cached = cache_get(u)
            if cached:
                try:
                    resolved.add(str(cached.get("account_id")))
                    if cached.get("auth_uid"):
                        resolved.add(str(cached["auth_uid"]))
                except Exception: pass

        if not resolved:
            return aiohttp.web.json_response(
                {"status": "error", "error": "uid or auth_uid required"})

        # ── 1) Cancel workers (both auth_uid and account_id task keys) ──
        for u in resolved:
            if u in bot_state.account_workers:
                try: bot_state.account_workers[u].cancel()
                except Exception: pass
                bot_state.account_workers.pop(u, None)

        # ── 2) Remove from in-memory state ──
        removed_memory = []
        for u in resolved:
            if u in bot_state.accounts:
                removed_memory.append(u)
                del bot_state.accounts[u]
            bot_state.paused.discard(u)
            bot_state.toggle_pause(u, False)
            bot_state.account_credentials.pop(u, None)
            bot_state.game_to_auth_id.pop(u, None)
            bot_state.auth_to_game_id.pop(u, None)

        # ── 3) Invalidate token cache ──
        for u in resolved:
            try: cache_invalidate(u)
            except Exception: pass

        # ── 4) Remove from accounts.json (permanent) ──
        removed_file = await _remove_from_accounts_file(resolved)

        # ── 5) Clean up team membership ──
        for u in resolved:
            try: await _clear_team_joined(u)
            except Exception: pass
            for gid, t in list(_teams_state.items()):
                if u in t["peers"]:
                    t["peers"].pop(u, None)
                    if t["leader_uid"] == u:
                        t["leader_uid"] = None
                        t["team_code"] = None

        # ── 6) Log result ──
        print_info(
            f"[DELETE] ids={sorted(resolved)} | "
            f"memory_removed={removed_memory} | "
            f"json_removed={len(removed_file)}")

        return aiohttp.web.json_response({
            "status": "ok",
            "removed_ids": sorted(resolved),
            "memory_removed": removed_memory,
            "json_removed": len(removed_file),
        })
    except Exception as e:
        traceback.print_exc()
        return aiohttp.web.json_response({"status": "error", "error": str(e)})

async def api_account_refresh(request):
    try:
        body = await request.json()
        uid = str(body.get("uid", "")).strip()
        asyncio.create_task(refresh_account_profile(uid))
        return aiohttp.web.json_response({"status": "ok"})
    except Exception as e:
        return aiohttp.web.json_response({"status": "error", "error": str(e)})

async def api_account_restart(request):
    try:
        body = await request.json()
        uid = str(body.get("uid", "")).strip()
        resolved = {uid}
        if uid in bot_state.game_to_auth_id: resolved.add(str(bot_state.game_to_auth_id[uid]))
        if uid in bot_state.auth_to_game_id: resolved.add(str(bot_state.auth_to_game_id[uid]))
        for u in resolved:
            if u in bot_state.account_workers:
                try: bot_state.account_workers[u].cancel()
                except Exception: pass
                bot_state.account_workers.pop(u, None)
        try:
            if os.path.exists(ACCOUNTS_FILE):
                with open(ACCOUNTS_FILE,"r",encoding="utf-8") as f:
                    accs = json.load(f)
                for a in accs:
                    if str(a.get("uid")) in resolved and a.get("password"):
                        squad_id = str(a.get("squad_id", "") or _assign_squad_for_new_account()).upper()
                        t = asyncio.create_task(account_loop_guest(
                            str(a["uid"]), a["password"], squad_id=squad_id))
                        bot_state.account_workers[str(a["uid"])] = t
                        break
        except Exception: pass
        return aiohttp.web.json_response({"status": "ok"})
    except Exception as e:
        return aiohttp.web.json_response({"status": "error", "error": str(e)})

async def api_account_pause(request):
    try:
        body = await request.json()
        uid = str(body.get("uid", "")).strip()
        new_state = not bot_state.is_paused(uid)
        bot_state.toggle_pause(uid, new_state)
        if new_state: bot_state.close_writers_for_account(uid)
        return aiohttp.web.json_response({"status": "ok", "is_paused": new_state})
    except Exception as e:
        return aiohttp.web.json_response({"status": "error", "error": str(e)})

async def api_account_pause_all(request):
    try:
        accs = list(bot_state.accounts.keys())
        if not accs:
            return aiohttp.web.json_response({"status": "ok", "all_paused": False})
        all_paused = all(bot_state.is_paused(u) for u in accs)
        new_state = not all_paused
        for u in accs:
            bot_state.toggle_pause(u, new_state)
            if new_state: bot_state.close_writers_for_account(u)
        return aiohttp.web.json_response({"status": "ok", "all_paused": new_state})
    except Exception as e:
        return aiohttp.web.json_response({"status": "error", "error": str(e)})

async def api_logs_clear(request):
    bot_state.logs = []
    return aiohttp.web.json_response({"status": "ok"})

async def api_get_raw_accounts(request):
    try:
        if os.path.exists(ACCOUNTS_FILE):
            with open(ACCOUNTS_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
            return aiohttp.web.json_response({"ok": True, "data": data})
        return aiohttp.web.json_response({"ok": True, "data": []})
    except Exception as e:
        return aiohttp.web.json_response({"ok": False, "error": str(e)}, status=500)

async def api_accounts_json_upsert(request):
    try:
        body = await request.json()
        old_uid = str(body.get("old_uid", "") or "").strip()
        old_index = body.get("old_index", None)
        uid = str(body.get("uid", "") or "").strip()
        password = str(body.get("password", "") or "").strip()
        token = str(body.get("token", "") or "").strip()
        region = str(body.get("region", "BD") or "BD").strip().upper()
        clan_id = str(body.get("clan_id", CLAN_ID_DEFAULT) or CLAN_ID_DEFAULT).strip()
        squad_id = str(body.get("squad_id", "") or _assign_squad_for_new_account()).strip().upper()
        apply_live = bool(body.get("apply_live", True))

        if token and not (uid and password):
            new_entry = {"token": token, "region": region, "clan_id": clan_id, "squad_id": squad_id}
        elif uid and password:
            new_entry = {"uid": uid, "password": password, "region": region, "clan_id": clan_id, "squad_id": squad_id}
        else:
            return aiohttp.web.json_response({"ok": False, "error": "UID ও Password (অথবা Token) দিতে হবে"}, status=400)

        async with _accounts_file_lock:
            accs = await _read_accounts_file_unlocked()
            is_edit = bool(old_uid) or (old_index is not None and isinstance(old_index, int) and 0 <= old_index < len(accs))
            if is_edit:
                target_idx = None
                if old_uid:
                    for i, a in enumerate(accs):
                        if isinstance(a, dict) and str(a.get("uid", "")).strip() == old_uid:
                            target_idx = i; break
                if target_idx is None and old_index is not None and 0 <= old_index < len(accs):
                    target_idx = old_index
                if target_idx is None:
                    return aiohttp.web.json_response({"ok": False, "error": "Account not found in accounts.json"}, status=404)
                if uid:
                    for i, a in enumerate(accs):
                        if i != target_idx and isinstance(a, dict) and str(a.get("uid", "")).strip() == uid:
                            return aiohttp.web.json_response({"ok": False, "error": f"UID {uid} already exists"}, status=400)
                accs[target_idx] = new_entry
            else:
                if uid and any(isinstance(a, dict) and str(a.get("uid", "")).strip() == uid for a in accs):
                    return aiohttp.web.json_response({"ok": False, "error": f"UID {uid} already exists"}, status=400)
                accs.append(new_entry)
            await _write_accounts_file_unlocked(accs)

        if apply_live:
            kill_ids = {x for x in (old_uid, uid) if x}
            if token: kill_ids.add(f"tok_{token[:20]}")
            await _stop_and_cleanup_account(kill_ids)
            await asyncio.sleep(0.3)
            if token and not (uid and password):
                t = asyncio.create_task(account_loop_token(token, squad_id=squad_id))
                bot_state.account_workers[f"tok_{token[:20]}"] = t
            else:
                t = asyncio.create_task(account_loop_guest(uid, password, region_override=region, clan_override=clan_id, squad_id=squad_id))
                bot_state.account_workers[uid] = t

        print_success(f"[ACCOUNTS-JSON] {'Updated' if is_edit else 'Added'} {uid or token[:12]} [Group {squad_id}]")
        return aiohttp.web.json_response({"ok": True, "data": accs})
    except Exception as e:
        traceback.print_exc()
        return aiohttp.web.json_response({"ok": False, "error": str(e)}, status=500)

async def api_accounts_json_delete(request):
    try:
        body = await request.json()
        uid = str(body.get("uid", "") or "").strip()
        index = body.get("index", None)
        stop_live = bool(body.get("stop_live", True))
        removed_entry = None

        async with _accounts_file_lock:
            accs = await _read_accounts_file_unlocked()
            if uid:
                kept = []
                for a in accs:
                    if isinstance(a, dict) and str(a.get("uid", "")).strip() == uid and removed_entry is None:
                        removed_entry = a
                    else:
                        kept.append(a)
                accs = kept
            elif index is not None and isinstance(index, int) and 0 <= index < len(accs):
                removed_entry = accs.pop(index)
            else:
                return aiohttp.web.json_response({"ok": False, "error": "uid or valid index required"}, status=400)
            await _write_accounts_file_unlocked(accs)

        if stop_live and isinstance(removed_entry, dict):
            kill_ids = set()
            if removed_entry.get("uid"): kill_ids.add(str(removed_entry["uid"]).strip())
            if removed_entry.get("token"):
                tok = str(removed_entry["token"]).strip()
                kill_ids.add(tok); kill_ids.add(f"tok_{tok[:20]}")
            if kill_ids:
                await _stop_and_cleanup_account(kill_ids)

        print_warning(f"[ACCOUNTS-JSON] Deleted account {uid or index}")
        return aiohttp.web.json_response({"ok": True, "data": accs})
    except Exception as e:
        traceback.print_exc()
        return aiohttp.web.json_response({"ok": False, "error": str(e)}, status=500)

async def api_save_raw_accounts(request):
    try:
        body = await request.json()
        raw_data = body.get("data")
        sync_live = bool(body.get("sync_live", False))
        if not isinstance(raw_data, list):
            return aiohttp.web.json_response({"ok": False, "error": "JSON must be an array [...]"}, status=400)

        cleaned = []
        seen_uids = set()
        seen_tokens = set()
        for idx, item in enumerate(raw_data):
            if not isinstance(item, dict):
                return aiohttp.web.json_response({"ok": False, "error": f"Item #{idx+1} must be an object {{...}}"}, status=400)
            uid = str(item.get("uid", "") or "").strip()
            password = str(item.get("password", "") or "").strip()
            token = str(item.get("token", "") or "").strip()
            if not token and not (uid and password):
                return aiohttp.web.json_response({"ok": False, "error": f"Item #{idx+1} requires uid+password or token"}, status=400)

            if uid and password:
                if uid in seen_uids:
                    return aiohttp.web.json_response({"ok": False, "error": f"Duplicate UID: {uid}"}, status=400)
                seen_uids.add(uid)
            elif token:
                if token in seen_tokens:
                    return aiohttp.web.json_response({"ok": False, "error": f"Duplicate Token at item #{idx+1}"}, status=400)
                seen_tokens.add(token)

            entry = dict(item)
            if uid: entry["uid"] = uid
            if password: entry["password"] = password
            if token: entry["token"] = token
            entry["region"] = str(item.get("region", "BD") or "BD").strip().upper()
            entry["clan_id"] = str(item.get("clan_id", CLAN_ID_DEFAULT) or CLAN_ID_DEFAULT).strip()
            entry["squad_id"] = str(item.get("squad_id", _group_for_index(idx)) or _group_for_index(idx)).strip().upper()
            cleaned.append(entry)

        async with _accounts_file_lock:
            old_accs = await _read_accounts_file_unlocked()
            await _write_accounts_file_unlocked(cleaned)

        if sync_live:
            def _key(a):
                if a.get("uid") and a.get("password"): return f"uid:{str(a['uid']).strip()}"
                if a.get("token"): return f"tok:{str(a['token']).strip()}"
                return None

            old_map = {_key(a): a for a in old_accs if isinstance(a, dict) and _key(a)}
            new_map = {_key(a): a for a in cleaned if _key(a)}

            # রিমুভ হওয়া অ্যাকাউন্ট বন্ধ করা
            for k, old_a in old_map.items():
                if k not in new_map:
                    kill_ids = set()
                    if old_a.get("uid"): kill_ids.add(str(old_a["uid"]).strip())
                    if old_a.get("token"):
                        tok = str(old_a["token"]).strip()
                        kill_ids.update({tok, f"tok_{tok[:20]}"})
                    await _stop_and_cleanup_account(kill_ids)

            # নতুন বা পরিবর্তিত অ্যাকাউন্ট চালু/রিস্টার্ট করা
            for k, new_a in new_map.items():
                old_a = old_map.get(k)
                changed = (old_a is None) or any(
                    str(old_a.get(f, "")) != str(new_a.get(f, ""))
                    for f in ("password", "token", "region", "clan_id", "squad_id")
                )
                u = new_a.get("uid")
                tok = new_a.get("token")
                worker_key = u if (u and new_a.get("password")) else f"tok_{tok[:20]}"

                if changed or worker_key not in bot_state.account_workers:
                    if old_a is not None:
                        kill_ids = set()
                        if u: kill_ids.add(u)
                        if tok: kill_ids.update({tok, f"tok_{tok[:20]}"})
                        await _stop_and_cleanup_account(kill_ids)
                        await asyncio.sleep(0.1)

                    if u and new_a.get("password"):
                        t = asyncio.create_task(account_loop_guest(
                            u, new_a["password"],
                            region_override=new_a["region"],
                            clan_override=new_a["clan_id"],
                            squad_id=new_a["squad_id"]
                        ))
                        bot_state.account_workers[u] = t
                    elif tok:
                        t = asyncio.create_task(account_loop_token(tok, squad_id=new_a["squad_id"]))
                        bot_state.account_workers[f"tok_{tok[:20]}"] = t

        print_success(f"[ACCOUNTS-JSON] Saved {len(cleaned)} account(s) (sync_live={sync_live})")
        return aiohttp.web.json_response({"ok": True, "data": cleaned})
    except Exception as e:
        traceback.print_exc()
        return aiohttp.web.json_response({"ok": False, "error": str(e)}, status=500)

async def account_loop_token(token, squad_id="A"):
    squad = str(squad_id or "A").upper()
    tok_key = f"tok_{token[:20]}"
    bot_state.account_workers[tok_key] = asyncio.current_task()
    acc_id_raw = None
    while True:
        try:
            print_info(f"TOKEN Login {token[:20]}... (squad={squad})")
            vc = await version_config("ID")
            if not vc:
                await asyncio.sleep(15); continue
            release_version, client_version, server_url, gop_1, app_version = vc
            url = f"https://100067.connect.garena.com/oauth/token/inspect?token={token}"
            hdrs = {"User-Agent":"GarenaMSDK/4.0.19P4(G011A ;Android 9;en;US;)"}
            r = await client.get(url, headers=hdrs)
            if r.status_code != 200:
                await asyncio.sleep(15); continue
            data = r.json()
            if 'error' in data:
                await asyncio.sleep(15); continue
            open_id = data.get('open_id'); platform = data.get('platform', 4)
            if not open_id:
                await asyncio.sleep(15); continue
            major_payload, login_payload = await get_payload(
                token, open_id, platform, client_version)
            res_json = await major_login(major_payload, server_url, release_version)
            if not res_json:
                await asyncio.sleep(15); continue
            def _gd(k):
                v = res_json.get(str(k))
                if isinstance(v, dict) and "data" in v: return v["data"]
                return v
            acc_id_raw = _gd(1); jwt_token = _gd(8)
            server_url_raw = _gd(10); server_time = _gd(21)
            region_raw = _gd(2) or "ID"
            aes_ak, iv_i = _extract_key_iv(res_json)
            if not (jwt_token and server_url_raw and aes_ak):
                await asyncio.sleep(15); continue
            ld = await get_login_data(login_payload, jwt_token, server_url_raw, release_version)
            def _gf(f, d=None):
                v = (ld or {}).get(str(f), {}).get("data")
                return v if v is not None else d
            level = int(_gf(6,1) or 1); exp = int(_gf(7,0) or 0)
            nickname = _gf(4, f"Player_{acc_id_raw}") or f"Player_{acc_id_raw}"
            ad = {'account_id':acc_id_raw,'nickname':nickname,'region':region_raw,
                'level':level,'exp':exp,'likes':int(_gf(8,0) or 0),
                'open_id':open_id,'access_token':token,'platform':str(platform),
                'token':jwt_token,'server_time':server_time,
                'aes_ak':aes_ak,'iv_i':iv_i,
                'functional_addrs':_gf_field(ld, 14),
                'informational_addrs':_gf_field(ld, 32),
                'release_version':release_version,'client_version':client_version,
                'server_url':server_url_raw,'login_payload_data':login_payload,
                'auth_type':'token','auth_token':token,
                'squad_id': squad}
            _register_credentials(ad)
            cache_set(tok_key, ad)
            bot_state.account_workers[str(acc_id_raw)] = asyncio.current_task()
            await run_account_worker(ad, str(acc_id_raw), squad_id=squad)
            await asyncio.sleep(3)
        except asyncio.CancelledError:
            try:
                if acc_id_raw:
                    bot_state.update_status(str(acc_id_raw), "OFFLINE")
                    await _clear_team_joined(str(acc_id_raw))
            except Exception: pass
            break
        except Exception as e:
            print_error(f"TOKEN {e}")
            await asyncio.sleep(10)

async def start_web_server():
    app = aiohttp.web.Application(middlewares=[_req_logger])
    app.router.add_get("/", serve_index)
    app.router.add_get("/index.html", serve_index)
    app.router.add_get("/api/ping", api_ping)
    app.router.add_get("/api/stats", api_stats)
    app.router.add_get("/api/state", api_state)
    app.router.add_post("/api/create_team", api_create_team)
    app.router.add_post("/api/account/add", api_account_add)
    app.router.add_post("/api/account/delete", api_account_delete)
    app.router.add_post("/api/account/refresh", api_account_refresh)
    app.router.add_post("/api/account/restart", api_account_restart)
    app.router.add_post("/api/account/pause", api_account_pause)
    app.router.add_post("/api/account/pause_all", api_account_pause_all)
    app.router.add_get("/api/accounts/raw", api_get_raw_accounts)
    app.router.add_post("/api/accounts/raw", api_save_raw_accounts)
    app.router.add_post("/api/accounts/json/upsert", api_accounts_json_upsert)
    app.router.add_post("/api/accounts/json/delete", api_accounts_json_delete)
    app.router.add_post("/api/logs/clear", api_logs_clear)
    app.router.add_get("/api/progress", api_progress)
    runner = aiohttp.web.AppRunner(app)
    await runner.setup()
    site = aiohttp.web.TCPSite(runner, WEB_HOST, WEB_PORT)
    await site.start()
    print_premium(f"Web Dashboard → http://localhost:{WEB_PORT}",
                  color=PX.CYAN, icon=I["rocket"], tag="WEB")
    return runner

# ==================== MAIN ====================
async def main():
    print_banner()
    try:
        await start_web_server()
    except Exception as e:
        print_error(f"WEB {e}"); return
    try:
        await _autoload_accounts()
    except Exception as e:
        print_error(f"BOOT autoload failed: {e}")
    asyncio.create_task(_no_match_watchdog())
    print_rule(" · Premium · All Systems Online", color=PX.EMERALD)
    try:
        while True:
            await asyncio.sleep(1)
    except (KeyboardInterrupt, asyncio.CancelledError):
        print_warning("Shutting down...")
        for t in list(bot_state.account_workers.values()):
            t.cancel()
        await asyncio.gather(*bot_state.account_workers.values(), return_exceptions=True)
        try: await client.aclose()
        except Exception: pass

if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        print_warning("stopped")