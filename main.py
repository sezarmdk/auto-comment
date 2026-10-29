import asyncio
import gc
import hashlib
import hmac
import html
import json
import os
import random
import re
import sys
import time
from collections import OrderedDict
from datetime import datetime, timedelta, timezone
from pathlib import Path
from urllib.parse import parse_qsl

import aiohttp
from aiohttp import web
from telethon import TelegramClient, events, utils
from telethon.errors import (
    FloodWaitError,
    MsgIdInvalidError,
    UserAlreadyParticipantError,
)
from telethon.network import ConnectionTcpAbridged
from telethon.sessions import StringSession
from telethon.tl import types
from telethon.tl.functions import PingRequest
from telethon.tl.functions.channels import (
    GetFullChannelRequest,
    JoinChannelRequest,
)
from telethon.tl.functions.messages import (
    EditMessageRequest,
    GetDiscussionMessageRequest,
    SendMessageRequest,
)
from telethon.tl.functions.updates import GetChannelDifferenceRequest

try:
    import uvloop
except ImportError:
    uvloop = None

# ================= ENV =================
API_ID = int(os.environ.get("API_ID", 0))
API_HASH = os.environ.get("API_HASH", "")
STRING_SESSION = os.environ.get("STRING_SESSION", "")
PORT = int(os.environ.get("PORT", 8080))
POLL_INTERVAL = float(os.environ.get("POLL_INTERVAL", "0"))
DATA_FILE = os.environ.get("DATA_FILE", "data.json")
BOT_TOKEN = os.environ.get("BOT_TOKEN", "")
OWNER_ID = int(os.environ.get("OWNER_ID", 0))
TZ = timezone(timedelta(hours=float(os.environ.get("TZ_OFFSET", "5"))))  # Toshkent
_ext = os.environ.get("RENDER_EXTERNAL_URL", "").rstrip("/")
WEBAPP_URL = os.environ.get("WEBAPP_URL") or (f"{_ext}/app" if _ext else "")

if not API_ID or not API_HASH or not STRING_SESSION:
    print("XATO: API_ID, API_HASH yoki STRING_SESSION kiritilmagan!")
    sys.exit(1)

WEBAPP_HTML = b""
_html_path = Path(__file__).with_name("webapp.html")
if _html_path.exists():
    WEBAPP_HTML = _html_path.read_bytes()


# ================= BAZA =================
def load_data():
    data = {}
    if os.path.exists(DATA_FILE):
        try:
            with open(DATA_FILE, "r", encoding="utf-8") as f:
                data = json.load(f)
        except Exception:
            data = {}
    ik = lambda d: {int(k): v for k, v in (d or {}).items()}
    chans = ik(data.get("channels"))
    old_edits = ik(data.get("edit_texts"))  # eski format
    for pid, c in chans.items():
        c.setdefault("username", "")
        c.setdefault("title", c["username"] or str(pid))
        c.setdefault("text", "...")
        c.setdefault("entities", [])
        if "edits" not in c:
            c["edits"] = [{"text": t, "entities": []} for t in old_edits.get(pid, [])]
        c.setdefault("idx", 0)
    return {
        "active": data.get("active", True),
        "delay": float(data.get("delay", 1.0)),
        "mode": data.get("mode", "navbat"),
        "report": data.get("report"),  # {"id","username","title"}
        "channels": chans,
        "stats": ik(data.get("stats")),
        "linked": ik(data.get("linked")),
    }


db = load_data()
_dirty = False
_save_lock = None


def _write_file():
    tmp = DATA_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(db, f, ensure_ascii=False, indent=2)
    os.replace(tmp, DATA_FILE)


async def async_save_data():
    global _dirty
    async with _save_lock:
        _dirty = False
        await asyncio.get_running_loop().run_in_executor(None, _write_file)


def mark_dirty():
    global _dirty
    _dirty = True


async def saver_loop():
    while True:
        await asyncio.sleep(5)
        if _dirty:
            try:
                await async_save_data()
            except Exception as e:
                print("save xato:", e)


client = TelegramClient(
    StringSession(STRING_SESSION),
    API_ID,
    API_HASH,
    connection=ConnectionTcpAbridged,
    connection_retries=None,
    retry_delay=1,
    auto_reconnect=True,
    request_retries=2,
)

username_to_id = {}
group_to_channel = {}
input_peers = {}
done = OrderedDict()
seen = OrderedDict()
texts = {}  # kanal_id -> (matn, entities) — oldindan tayyor


def _lru_add(od, key, limit=5000):
    if key in od:
        return False
    od[key] = None
    if len(od) > limit:
        od.popitem(last=False)
    return True


# ================= PREMIUM EMOJI / FORMAT =================
ENT_TYPES = {
    "MessageEntityBold", "MessageEntityItalic", "MessageEntityUnderline",
    "MessageEntityStrike", "MessageEntityCode", "MessageEntityPre",
    "MessageEntityTextUrl", "MessageEntityCustomEmoji", "MessageEntitySpoiler",
    "MessageEntityBlockquote",
}
_ENT_EXTRA = ("document_id", "url", "language", "collapsed")


def u16(s: str) -> int:
    return len(s.encode("utf-16-le")) // 2


def ser_entities(ents, start, end):
    out = []
    for e in ents or []:
        name = type(e).__name__
        if name not in ENT_TYPES:
            continue
        if e.offset < start or e.offset + e.length > end:
            continue
        d = {"t": name, "o": e.offset - start, "l": e.length}
        for k in _ENT_EXTRA:
            v = getattr(e, k, None)
            if v is not None:
                d[k] = v
        out.append(d)
    return out


def de_entities(lst):
    res = []
    for d in lst or []:
        cls = getattr(types, d.get("t", ""), None)
        if not cls:
            continue
        kw = {k: d[k] for k in _ENT_EXTRA if k in d}
        try:
            res.append(cls(offset=d["o"], length=d["l"], **kw))
        except Exception:
            pass
    return res or None


def has_premium(lst):
    return any(d.get("t") == "MessageEntityCustomEmoji" for d in lst or [])


def rebuild_texts():
    texts.clear()
    for pid, c in db["channels"].items():
        texts[pid] = (c.get("text") or "...", de_entities(c.get("entities")))


# ================= YORDAMCHI =================
def parse_target(s: str):
    s = s.strip()
    if re.fullmatch(r"-?\d+", s):
        return int(s)
    s = s.lower()
    for pre in ("https://t.me/", "http://t.me/", "t.me/"):
        if s.startswith(pre):
            s = s[len(pre):]
    s = s.strip("/")
    return s if s.startswith("@") else "@" + s


async def get_peer(pid):
    p = input_peers.get(pid)
    if p is None:
        p = input_peers[pid] = await client.get_input_entity(pid)
    return p


async def resolve_channel(target: str):
    """Kanal entity'sini qaytaradi; kanal bo'lmasa xato."""
    t = parse_target(target)
    entity = await client.get_entity(t)
    if not (isinstance(entity, types.Channel) and entity.broadcast):
        raise ValueError("Bu kanal emas (guruh yoki foydalanuvchi)")
    pid = utils.get_peer_id(entity)
    input_peers[pid] = utils.get_input_peer(entity)
    uname = f"@{entity.username.lower()}" if entity.username else ""
    if uname:
        username_to_id[uname] = pid
    return pid, entity, uname


async def resolve_pid(target: str) -> int:
    t = parse_target(target)
    if isinstance(t, int):
        return t
    if t in username_to_id:
        return username_to_id[t]
    for pid, c in db["channels"].items():
        if c.get("username") == t:
            return pid
    pid, _, _ = await resolve_channel(t)
    return pid


async def fetch_linked(ch_id):
    try:
        full = await client(GetFullChannelRequest(await get_peer(ch_id)))
        lid = full.full_chat.linked_chat_id
        if not lid:
            return None
        gid = int(f"-100{lid}")
        for chat in full.chats:
            if chat.id == lid:
                input_peers[gid] = utils.get_input_peer(chat)
        db["linked"][ch_id] = gid
        group_to_channel[gid] = ch_id
        return gid
    except Exception as e:
        print(f"linked xato {ch_id}: {e}")
        return None


def fmt_t(dt):
    if not dt:
        return "—"
    return dt.astimezone(TZ).strftime("%H:%M:%S")


def post_link(ch_id, post_id, comment_id=None):
    u = db["channels"].get(ch_id, {}).get("username", "")
    if u.startswith("@"):
        base = f"https://t.me/{u[1:]}/{post_id}"
    else:
        base = f"https://t.me/c/{str(ch_id)[4:]}/{post_id}"
    return base + (f"?comment={comment_id}" if comment_id else "")


def ch_title(ch_id):
    c = db["channels"].get(ch_id, {})
    return c.get("title") or c.get("username") or str(ch_id)


# ================= ⚡ HOT PATH =================
def set_stat(ch_id, post_id, speed, status, lag=None):
    db["stats"][ch_id] = {
        "msg_id": post_id, "speed": speed, "status": status, "lag": lag,
        "at": int(time.time()),
    }
    mark_dirty()


def _sent_info(result, rid):
    if isinstance(result, types.UpdateShortSentMessage):
        return result.id, result.date
    ups = getattr(result, "updates", []) or []
    mid = None
    for u in ups:
        if isinstance(u, types.UpdateMessageID) and u.random_id == rid:
            mid = u.id
    for u in ups:
        if isinstance(u, (types.UpdateNewChannelMessage, types.UpdateNewMessage)):
            if getattr(u.message, "id", None) == mid:
                return mid, u.message.date
    return mid, None


async def send_comment(ch_id, gpeer, reply_id, post_id, t0, post_date=None):
    if not _lru_add(done, (ch_id, post_id)):
        return
    rid = random.getrandbits(63)
    text, ents = texts.get(ch_id, ("...", None))
    try:
        result = await client(SendMessageRequest(
            peer=gpeer,
            message=text,
            random_id=rid,
            no_webpage=True,
            entities=ents,
            reply_to=types.InputReplyToMessage(reply_to_msg_id=reply_id),
        ))
        speed = time.perf_counter() - t0
        # qolgan hamma ish — fonda, izoh allaqachon ketgan
        asyncio.create_task(after_send(ch_id, gpeer, result, rid, post_id, post_date, speed))
    except FloodWaitError as e:
        fail(ch_id, post_id, f"FloodWait: {e.seconds} s", post_date)
    except Exception as e:
        fail(ch_id, post_id, str(e)[:200], post_date)


async def on_group_msg(gid, msg):
    """Muhokama guruhidagi avto-forward (faqat kanalning o'z posti)."""
    fwd = msg.fwd_from
    if not fwd:
        return
    ch_id = group_to_channel[gid]
    post_id = None
    sp = fwd.saved_from_peer
    if sp is not None and utils.get_peer_id(sp) == ch_id:
        post_id = fwd.saved_from_msg_id
    elif msg.from_id is not None and utils.get_peer_id(msg.from_id) == ch_id:
        post_id = fwd.channel_post  # kanal nomidan avto-forward
    if not post_id or (ch_id, post_id) in done:
        return
    t0 = time.perf_counter()
    await send_comment(ch_id, await get_peer(gid), msg.id, post_id, t0, fwd.date or msg.date)


async def on_channel_msg(ch_id, msg):
    """Zaxira yo'l: kanal posti (oddiy yoki uzatilgan) -> GetDiscussionMessage."""
    t0 = time.perf_counter()
    post_id = msg.id
    peer = await get_peer(ch_id)
    disc = None
    for _ in range(12):
        if (ch_id, post_id) in done:
            return
        try:
            disc = await client(GetDiscussionMessageRequest(peer=peer, msg_id=post_id))
            break
        except MsgIdInvalidError:
            await asyncio.sleep(0.025)
        except FloodWaitError as e:
            return fail(ch_id, post_id, f"FloodWait: {e.seconds} s", msg.date)
        except Exception as e:
            return fail(ch_id, post_id, str(e)[:200], msg.date)

    if not disc or not disc.messages:
        if (ch_id, post_id) not in done:
            _lru_add(done, (ch_id, post_id))
            fail(ch_id, post_id, "Muhokama posti topilmadi (izohlar yopiq bo'lishi mumkin)", msg.date)
        return
    m = disc.messages[0]
    gid = utils.get_peer_id(m.peer_id)
    if gid not in input_peers:
        for chat in disc.chats:
            if utils.get_peer_id(chat) == gid:
                input_peers[gid] = utils.get_input_peer(chat)
    if gid not in group_to_channel:
        group_to_channel[gid] = ch_id
        db["linked"][ch_id] = gid
    await send_comment(ch_id, await get_peer(gid), m.id, post_id, t0, msg.date)


async def dispatch(msg):
    if not db["active"] or not isinstance(msg, types.Message) or msg.out:
        return
    pid = utils.get_peer_id(msg.peer_id)
    if pid in group_to_channel:
        if _lru_add(seen, (pid, msg.id)):
            await on_group_msg(pid, msg)
    elif pid in texts:
        if _lru_add(seen, (pid, msg.id)):
            await on_channel_msg(pid, msg)


@client.on(events.Raw(types.UpdateNewChannelMessage))
async def on_raw(update):
    await dispatch(update.message)


# ================= FON: TAHRIR + HISOBOT =================
def pick_edit(ch):
    edits = ch.get("edits") or []
    if not edits:
        return None, None
    if db["mode"] == "random":
        i = random.randrange(len(edits))
    else:
        i = ch.get("idx", 0) % len(edits)
        ch["idx"] = i + 1
        mark_dirty()
    return i, edits[i]


async def send_report(text):
    rep = db.get("report")
    if not rep:
        return None
    try:
        peer = await get_peer(rep["id"])
        return await client.send_message(peer, text, parse_mode="html", link_preview=False)
    except FloodWaitError as e:
        await asyncio.sleep(e.seconds + 1)
        try:
            return await client.send_message(await get_peer(rep["id"]), text,
                                             parse_mode="html", link_preview=False)
        except Exception as ex:
            print("hisobot xato:", ex)
    except Exception as e:
        print("hisobot xato:", e)
    return None


def fail(ch_id, post_id, reason, post_date=None):
    set_stat(ch_id, post_id, 0, f"Xato: {reason[:60]}")
    c = db["channels"].get(ch_id, {})
    txt = (
        "❌ <b>Izoh yozilmadi</b>\n\n"
        f"📢 Kanal: <b>{html.escape(ch_title(ch_id))}</b> {html.escape(c.get('username', ''))}\n"
        f"🕒 Post: <code>{fmt_t(post_date)}</code>\n"
        f"⚠️ Sabab: <code>{html.escape(reason)}</code>\n"
        f"🔗 <a href=\"{post_link(ch_id, post_id)}\">Postni ochish</a>"
    )
    asyncio.create_task(send_report(txt))


async def after_send(ch_id, gpeer, result, rid, post_id, post_date, speed):
    try:
        cid, cdate = _sent_info(result, rid)
        diff = None
        if cdate and post_date:
            diff = round((cdate - post_date).total_seconds(), 2)
        set_stat(ch_id, post_id, speed, "Muvaffaqiyatli ✅", diff)

        c = db["channels"].get(ch_id, {})
        link = post_link(ch_id, post_id, cid)
        base = (
            "✅ <b>Izoh yozildi</b>\n\n"
            f"📢 Kanal: <b>{html.escape(ch_title(ch_id))}</b> {html.escape(c.get('username', ''))}\n"
            f"🕒 Post: <code>{fmt_t(post_date)}</code>\n"
            f"💬 Izoh: <code>{fmt_t(cdate)}</code>\n"
            f"⚡ Yuborish: <code>{speed * 1000:.1f} ms</code>\n"
            f"⏱ Server farqi: <code>{diff if diff is not None else '—'} s</code>\n"
            f"🔗 <a href=\"{link}\">Izohni ochish</a>"
        )
        report_task = asyncio.create_task(send_report(base))

        idx, edit = pick_edit(c) if c else (None, None)
        if edit is None or not cid:
            return
        await asyncio.sleep(max(0.0, db["delay"]))
        status = None
        for attempt in range(2):
            try:
                await client(EditMessageRequest(
                    peer=gpeer, id=cid, message=edit["text"],
                    entities=de_entities(edit.get("entities")), no_webpage=True))
                status = f"✏️ Tahrirlandi: <b>{idx + 1}-matn</b> ({db['delay']} s dan keyin)"
                break
            except FloodWaitError as fw:
                if attempt:
                    status = f"✏️ Tahrir xatosi: FloodWait {fw.seconds} s"
                else:
                    await asyncio.sleep(fw.seconds + 1)
            except Exception as e:
                status = f"✏️ Tahrir xatosi: <code>{html.escape(str(e)[:100])}</code>"
                break
        rep_msg = await report_task
        if rep_msg and status:
            try:
                await rep_msg.edit(base + "\n" + status, parse_mode="html", link_preview=False)
            except Exception:
                pass
    except Exception as e:
        print("after_send xato:", e)


# ================= POLLER =================
async def poll_group(gid):
    pts = None
    while True:
        try:
            if gid not in group_to_channel:
                return
            peer = await get_peer(gid)
            if pts is None:
                full = await client(GetFullChannelRequest(peer))
                pts = full.full_chat.pts
            res = await client(GetChannelDifferenceRequest(
                channel=peer, filter=types.ChannelMessagesFilterEmpty(),
                pts=pts, limit=100, force=True))
            if isinstance(res, types.updates.ChannelDifference):
                pts = res.pts
                for m in res.new_messages:
                    asyncio.create_task(dispatch(m))
            elif isinstance(res, types.updates.ChannelDifferenceEmpty):
                pts = res.pts
            else:
                pts = None
            await asyncio.sleep(POLL_INTERVAL)
        except FloodWaitError as e:
            await asyncio.sleep(e.seconds + 1)
        except Exception as e:
            print(f"poll xato {gid}: {e}")
            pts = None
            await asyncio.sleep(3)


pollers = {}


def ensure_pollers():
    if POLL_INTERVAL <= 0:
        return
    for gid in list(group_to_channel):
        if gid not in pollers or pollers[gid].done():
            pollers[gid] = asyncio.create_task(poll_group(gid))


# ================= UMUMIY AMALLAR (buyruq + mini app) =================
async def _join(entity):
    try:
        await client(JoinChannelRequest(entity))
        return None
    except UserAlreadyParticipantError:
        return None
    except Exception as e:
        return str(e)[:120]


async def op_add_channel(target, text, ents=None, keep_ents_if_same=False):
    pid, entity, uname = await resolve_channel(target)
    warns = []
    if getattr(entity, "left", False):
        e = await _join(entity)
        if e:
            warns.append(f"Kanalga a'zo bo'lib bo'lmadi: {e}")
    full = await client(GetFullChannelRequest(input_peers[pid]))
    lid = full.full_chat.linked_chat_id
    if not lid:
        warns.append("Izohlar yopiq: kanalga muhokama guruhi ulanmagan")
    else:
        gid = int(f"-100{lid}")
        chat = next((c for c in full.chats if c.id == lid), None)
        if chat is not None:
            input_peers[gid] = utils.get_input_peer(chat)
            if getattr(chat, "left", False):
                e = await _join(chat)
                if e:
                    warns.append(f"Izoh guruhiga a'zo bo'lib bo'lmadi: {e}")
            dbr = getattr(chat, "default_banned_rights", None)
            if dbr is not None and dbr.send_messages:
                warns.append("Izoh guruhida yozish taqiqlangan")
        db["linked"][pid] = gid
        group_to_channel[gid] = pid

    c = db["channels"].get(pid)
    if c:
        if not (keep_ents_if_same and c.get("text") == text):
            c["entities"] = ents or []
        c.update(text=text, username=uname, title=entity.title)
    else:
        db["channels"][pid] = {
            "username": uname, "title": entity.title, "text": text,
            "entities": ents or [], "edits": [], "idx": 0,
        }
    rebuild_texts()
    ensure_pollers()
    await async_save_data()
    return pid, warns


async def op_del_channel(pid):
    existed = db["channels"].pop(pid, None) is not None
    db["stats"].pop(pid, None)
    gid = db["linked"].pop(pid, None)
    group_to_channel.pop(gid, None)
    t = pollers.pop(gid, None)
    if t:
        t.cancel()
    rebuild_texts()
    await async_save_data()
    return existed


def _need_channel(pid):
    c = db["channels"].get(pid)
    if not c:
        raise ValueError("Kanal ro'yxatda yo'q. Avval .cadd bilan qo'shing")
    return c


async def op_add_edit(pid, text, ents=None):
    c = _need_channel(pid)
    c["edits"].append({"text": text, "entities": ents or []})
    await async_save_data()
    return len(c["edits"])


async def op_del_edit(pid, idx):
    c = _need_channel(pid)
    if not 0 <= idx < len(c["edits"]):
        return None
    removed = c["edits"].pop(idx)
    await async_save_data()
    return removed["text"]


async def op_toggle(state: bool):
    db["active"] = state
    await async_save_data()


async def op_set_delay(v: float):
    if v < 0 or v > 3600:
        raise ValueError("0 dan 3600 gacha bo'lsin")
    db["delay"] = round(v, 2)
    await async_save_data()


async def op_set_mode(m: str):
    m = m.lower()
    if m not in ("navbat", "random"):
        raise ValueError("faqat navbat yoki random")
    db["mode"] = m
    await async_save_data()


async def op_set_report(target):
    if target is None or str(target).strip().lower() in ("", "off", "o'chir"):
        db["report"] = None
        await async_save_data()
        return None
    t = parse_target(str(target))
    entity = await client.get_entity(t)
    if not isinstance(entity, types.Channel):
        raise ValueError("Hisobot uchun kanal kerak")
    if not (entity.creator or entity.admin_rights):
        raise ValueError("Bu kanalga yozish huquqingiz yo'q (egasi/admin emassiz)")
    pid = utils.get_peer_id(entity)
    input_peers[pid] = utils.get_input_peer(entity)
    db["report"] = {
        "id": pid,
        "username": f"@{entity.username}" if entity.username else "",
        "title": entity.title,
    }
    await async_save_data()
    return db["report"]


async def op_ping():
    res = []
    for _ in range(3):
        s = time.perf_counter()
        await client(PingRequest(ping_id=random.getrandbits(63)))
        res.append((time.perf_counter() - s) * 1000)
    return min(res), sum(res) / len(res)


def snapshot():
    chans = []
    for pid, c in db["channels"].items():
        n = len(c["edits"])
        chans.append({
            "id": str(pid),
            "username": c.get("username") or "",
            "title": c.get("title") or "",
            "text": c.get("text", ""),
            "premium": has_premium(c.get("entities")),
            "linked": pid in db["linked"],
            "edits": [{"text": e["text"], "premium": has_premium(e.get("entities"))}
                      for e in c["edits"]],
            "next": (c.get("idx", 0) % n) + 1 if n else None,
            "stat": db["stats"].get(pid),
        })
    return {
        "active": db["active"],
        "delay": db["delay"],
        "mode": db["mode"],
        "report": db["report"],
        "dc": client.session.dc_id,
        "poll": POLL_INTERVAL,
        "channels": chans,
    }


# ================= MINI APP API =================
def check_init_data(init_data: str) -> bool:
    if not BOT_TOKEN or not OWNER_ID or not init_data:
        return False
    try:
        pairs = dict(parse_qsl(init_data, keep_blank_values=True))
        h = pairs.pop("hash", "")
        dcs = "\n".join(f"{k}={v}" for k, v in sorted(pairs.items()))
        secret = hmac.new(b"WebAppData", BOT_TOKEN.encode(), hashlib.sha256).digest()
        calc = hmac.new(secret, dcs.encode(), hashlib.sha256).hexdigest()
        if not hmac.compare_digest(calc, h):
            return False
        if time.time() - int(pairs.get("auth_date", 0)) > 86400:
            return False
        return json.loads(pairs.get("user", "{}")).get("id") == OWNER_ID
    except Exception:
        return False


@web.middleware
async def auth_mw(request, handler):
    if request.path.startswith("/api/"):
        if not check_init_data(request.headers.get("X-Init-Data", "")):
            return web.json_response({"error": "Ruxsat yo'q"}, status=403)
        try:
            return await handler(request)
        except Exception as e:
            return web.json_response({"error": str(e)[:200]}, status=400)
    return await handler(request)


def ok(extra=None):
    d = snapshot()
    if extra:
        d.update(extra)
    return web.json_response(d)


async def _body(request):
    try:
        return await request.json()
    except Exception:
        return {}


async def api_state(request):
    return ok()


async def api_toggle(request):
    await op_toggle(bool((await _body(request)).get("active")))
    return ok()


async def api_settings(request):
    b = await _body(request)
    if "delay" in b:
        await op_set_delay(float(b["delay"]))
    if "mode" in b:
        await op_set_mode(str(b["mode"]))
    return ok()


async def api_report(request):
    await op_set_report((await _body(request)).get("target"))
    return ok()


async def api_add_channel(request):
    b = await _body(request)
    u, t = (b.get("username") or "").strip(), (b.get("text") or "").strip()
    if not u or not t:
        raise ValueError("Kanal va matnni kiriting")
    _, warns = await op_add_channel(u, t, None, keep_ents_if_same=True)
    return ok({"warn": "; ".join(warns) or None})


async def api_del_channel(request):
    await op_del_channel(int((await _body(request))["id"]))
    return ok()


async def api_add_edit(request):
    b = await _body(request)
    t = (b.get("text") or "").strip()
    if not t:
        raise ValueError("Matn bo'sh")
    await op_add_edit(int(b["id"]), t)
    return ok()


async def api_del_edit(request):
    b = await _body(request)
    await op_del_edit(int(b["id"]), int(b["index"]))
    return ok()


async def api_ping(request):
    mn, avg = await op_ping()
    return ok({"ping": {"min": round(mn, 1), "avg": round(avg, 1)}})


async def handle_root(request):
    return web.Response(text="Bot aktiv va ishlayapti!")


async def handle_app(request):
    if not WEBAPP_HTML:
        return web.Response(text="webapp.html topilmadi", status=404)
    return web.Response(body=WEBAPP_HTML, content_type="text/html", charset="utf-8")


async def start_web_server():
    app = web.Application(middlewares=[auth_mw])
    app.router.add_get("/", handle_root)
    app.router.add_get("/app", handle_app)
    app.router.add_get("/api/state", api_state)
    app.router.add_post("/api/toggle", api_toggle)
    app.router.add_post("/api/settings", api_settings)
    app.router.add_post("/api/report", api_report)
    app.router.add_post("/api/channel/add", api_add_channel)
    app.router.add_post("/api/channel/del", api_del_channel)
    app.router.add_post("/api/edit/add", api_add_edit)
    app.router.add_post("/api/edit/del", api_del_edit)
    app.router.add_get("/api/ping", api_ping)
    runner = web.AppRunner(app, access_log=None)
    await runner.setup()
    await web.TCPSite(runner, "0.0.0.0", PORT).start()


# ================= BOT (Bot API long-polling) =================
async def bot_loop():
    if not BOT_TOKEN:
        return
    base = f"https://api.telegram.org/bot{BOT_TOKEN}/"
    async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=70)) as s:
        try:
            await s.post(base + "deleteWebhook")
            if WEBAPP_URL:
                await s.post(base + "setChatMenuButton", json={"menu_button": {
                    "type": "web_app", "text": "Panel", "web_app": {"url": WEBAPP_URL}}})
                print(f">>> Mini app: {WEBAPP_URL}")
        except Exception as e:
            print("bot setup xato:", e)

        offset = 0
        while True:
            try:
                async with s.get(base + "getUpdates", params={
                    "timeout": 50, "offset": offset,
                    "allowed_updates": '["message"]'}) as r:
                    data = await r.json()
                for u in data.get("result", []):
                    offset = u["update_id"] + 1
                    uid = ((u.get("message") or {}).get("from") or {}).get("id")
                    if not uid:
                        continue
                    if uid != OWNER_ID:
                        await s.post(base + "sendMessage", json={
                            "chat_id": uid, "text": "⛔ Bu bot shaxsiy."})
                        continue
                    payload = {"chat_id": uid, "parse_mode": "HTML", "text":
                               "⚡ <b>Komment Pilot</b>\n\nHolat: "
                               + ("🟢 yoqilgan" if db["active"] else "🔴 o'chirilgan")
                               + f"\nKanallar: {len(db['channels'])}"}
                    if WEBAPP_URL:
                        payload["reply_markup"] = {"inline_keyboard": [[{
                            "text": "🎛 Panelni ochish", "web_app": {"url": WEBAPP_URL}}]]}
                    await s.post(base + "sendMessage", json=payload)
            except asyncio.CancelledError:
                raise
            except Exception as e:
                print("bot loop xato:", e)
                await asyncio.sleep(5)


# ================= MATNLI BUYRUQLAR =================
class Usage(Exception):
    pass


USAGE = {
    "help": ".help",
    "ping": ".ping",
    "cton": ".cton",
    "ctoff": ".ctoff",
    "cadd": ".cadd @kanal matn\nMisol: .cadd @texnoblog Birinchi! 🔥",
    "cdel": ".cdel @kanal",
    "clist": ".clist",
    "ce": ".ce @kanal matn\nMisol: .ce @texnoblog Zo'r post 👍",
    "cel": ".cel @kanal",
    "cedel": ".cedel @kanal N\nMisol: .cedel @texnoblog 2",
    "padd": ".padd @kanal   (o'chirish: .padd off)",
    "cdelay": ".cdelay N\nMisol: .cdelay 1.5",
    "ctime": ".ctime N\nMisol: .ctime 0.5",
    "cmode": ".cmode navbat | random",
}

RE_CH_TEXT = re.compile(r"[ \t]+(\S+)\s+(\S[\s\S]*)")
RE_CH = re.compile(r"\s+(\S+)\s*$")
RE_CH_N = re.compile(r"\s+(\S+)\s+(\d+)\s*$")
RE_NUM = re.compile(r"\s+(\d+(?:[.,]\d+)?)\s*$")
RE_WORD = re.compile(r"\s+(\S+)\s*$")


def need(rx, raw, pos):
    m = rx.match(raw, pos)
    if not m:
        raise Usage()
    return m


def no_args(raw, pos):
    if raw[pos:].strip():
        raise Usage()


def text_with_entities(event, raw, m, grp):
    s, e = m.span(grp)
    txt = raw[s:e].rstrip()
    e = s + len(txt)
    return txt, ser_entities(event.message.entities, u16(raw[:s]), u16(raw[:e]))


async def say(event, text):
    if len(text) > 4000:
        text = text[:4000] + "\n…"
    await event.edit(text, parse_mode="html", link_preview=False)


def esc(s):
    return html.escape(str(s))


async def c_help(ev, raw, pos):
    no_args(raw, pos)
    await say(ev,
        "⚡ <b>Komment Pilot — buyruqlar</b>\n\n"
        "<code>.ping</code> — javob tezligi (ms)\n"
        "<code>.cton</code> / <code>.ctoff</code> — avto-izohni yoqish / o'chirish\n\n"
        "<code>.cadd @kanal matn</code> — kanal qo'shish / matnni yangilash\n"
        "<code>.cdel @kanal</code> — kanalni o'chirish\n"
        "<code>.clist</code> — kanallar ro'yxati\n\n"
        "<code>.ce @kanal matn</code> — tahrir matni qo'shish\n"
        "<code>.cel @kanal</code> — tahrir matnlari ro'yxati\n"
        "<code>.cedel @kanal N</code> — N-tahrir matnini o'chirish\n\n"
        "<code>.padd @kanal</code> — hisobot kanalini belgilash\n"
        "<code>.cdelay N</code> / <code>.ctime N</code> — tahrirdan oldin kutish (s)\n"
        "<code>.cmode navbat|random</code> — tahrir matnini tanlash usuli\n\n"
        "✨ Matnlarda premium emoji va formatlash saqlanadi.")


async def c_ping(ev, raw, pos):
    no_args(raw, pos)
    mn, avg = await op_ping()
    await say(ev, f"🏓 <b>Pong!</b> min <code>{mn:.1f} ms</code> / o'rt <code>{avg:.1f} ms</code>\n"
                  f"DC: <code>{client.session.dc_id}</code> | Poll: <code>{POLL_INTERVAL or 'off'}</code>")


async def c_on(ev, raw, pos):
    no_args(raw, pos)
    await op_toggle(True)
    await say(ev, "🟢 Avto-izoh <b>yoqildi</b>")


async def c_off(ev, raw, pos):
    no_args(raw, pos)
    await op_toggle(False)
    await say(ev, "🔴 Avto-izoh <b>o'chirildi</b> (kanallar saqlanib qoldi)")


async def c_add(ev, raw, pos):
    m = need(RE_CH_TEXT, raw, pos)
    text, ents = text_with_entities(ev, raw, m, 2)
    pid, warns = await op_add_channel(m.group(1), text, ents)
    c = db["channels"][pid]
    msg = (f"✅ Qo'shildi: <b>{esc(c['title'])}</b> {esc(c['username'])}\n"
           f"💬 Matn: {esc(text)}"
           + (" ✨" if has_premium(ents) else "")
           + f"\n✏️ Tahrir matnlari: {len(c['edits'])}")
    if warns:
        msg += "\n\n⚠️ " + "\n⚠️ ".join(esc(w) for w in warns)
    await say(ev, msg)


async def c_del(ev, raw, pos):
    m = need(RE_CH, raw, pos)
    pid = await resolve_pid(m.group(1))
    title = ch_title(pid)
    if await op_del_channel(pid):
        await say(ev, f"🗑 <b>{esc(title)}</b> o'chirildi")
    else:
        await say(ev, "Kanal ro'yxatda topilmadi.")


async def c_list(ev, raw, pos):
    no_args(raw, pos)
    rep = db["report"]
    head = (f"📋 <b>Kuzatilayotgan kanallar</b>\n"
            f"Avto-izoh: {'🟢 yoqilgan' if db['active'] else '🔴 o' + chr(39) + 'chirilgan'}\n"
            f"⏱ Kutish: {db['delay']} s | 🔀 Usul: {db['mode']}\n"
            f"📊 Hisobot: {esc(rep['title']) if rep else 'belgilanmagan'}\n")
    if not db["channels"]:
        return await say(ev, head + "\nRo'yxat bo'sh.")
    lines = [head]
    for i, (pid, c) in enumerate(db["channels"].items(), 1):
        t = c["text"] if len(c["text"]) <= 120 else c["text"][:120] + "…"
        lines.append(
            f"<b>{i}. {esc(c['title'])}</b> {esc(c['username'] or pid)}\n"
            f"   💬 {esc(t)}{' ✨' if has_premium(c.get('entities')) else ''}\n"
            f"   ✏️ Tahrir matnlari: {len(c['edits'])} | 🔗 Guruh: "
            f"{'✅' if pid in db['linked'] else '❌'}")
    await say(ev, "\n".join(lines))


async def c_ce(ev, raw, pos):
    m = need(RE_CH_TEXT, raw, pos)
    text, ents = text_with_entities(ev, raw, m, 2)
    pid = await resolve_pid(m.group(1))
    n = await op_add_edit(pid, text, ents)
    await say(ev, f"✏️ <b>{esc(ch_title(pid))}</b> uchun {n}-tahrir matni qo'shildi"
                  f"{' ✨' if has_premium(ents) else ''}:\n{esc(text)}")


async def c_cel(ev, raw, pos):
    m = need(RE_CH, raw, pos)
    pid = await resolve_pid(m.group(1))
    c = _need_channel(pid)
    if not c["edits"]:
        return await say(ev, f"<b>{esc(c['title'])}</b> uchun tahrir matnlari yo'q.")
    lines = [f"✏️ <b>{esc(c['title'])}</b> — tahrir matnlari ({db['mode']}):"]
    for i, e in enumerate(c["edits"], 1):
        lines.append(f"{i}. {esc(e['text'])}{' ✨' if has_premium(e.get('entities')) else ''}")
    await say(ev, "\n".join(lines))


async def c_cedel(ev, raw, pos):
    m = need(RE_CH_N, raw, pos)
    pid = await resolve_pid(m.group(1))
    n = int(m.group(2))
    removed = await op_del_edit(pid, n - 1)
    if removed is None:
        cnt = len(_need_channel(pid)["edits"])
        return await say(ev, f"❗ Noto'g'ri raqam. Mavjud: 1–{cnt}" if cnt else "❗ Tahrir matnlari yo'q.")
    await say(ev, f"🗑 O'chirildi: {n}. {esc(removed)}")


async def c_padd(ev, raw, pos):
    m = need(RE_WORD, raw, pos)
    rep = await op_set_report(m.group(1))
    if rep is None:
        await say(ev, "📊 Hisobot o'chirildi")
    else:
        await say(ev, f"📊 Hisobot kanali: <b>{esc(rep['title'])}</b> {esc(rep['username'])}")


async def c_delay(ev, raw, pos):
    m = need(RE_NUM, raw, pos)
    await op_set_delay(float(m.group(1).replace(",", ".")))
    await say(ev, f"⏱ Tahrirdan oldin kutish: <b>{db['delay']} s</b>")


async def c_mode(ev, raw, pos):
    m = need(RE_WORD, raw, pos)
    if m.group(1).lower() not in ("navbat", "random"):
        raise Usage()
    await op_set_mode(m.group(1))
    await say(ev, f"🔀 Tahrir usuli: <b>{db['mode']}</b>")


COMMANDS = {
    "help": c_help, "ping": c_ping, "cton": c_on, "ctoff": c_off,
    "cadd": c_add, "cdel": c_del, "clist": c_list,
    "ce": c_ce, "cel": c_cel, "cedel": c_cedel,
    "padd": c_padd, "cdelay": c_delay, "ctime": c_delay, "cmode": c_mode,
}
RE_CMD = re.compile(r"^\.([a-zA-Z]+)")


@client.on(events.NewMessage(outgoing=True, pattern=r"^\.[a-zA-Z]+"))
async def on_command(event):
    raw = event.message.message or ""
    m = RE_CMD.match(raw)
    cmd = m.group(1).lower()
    h = COMMANDS.get(cmd)
    if not h:
        return
    try:
        await h(event, raw, m.end())
    except Usage:
        try:
            await say(event, f"❗ Noto'g'ri yozildi.\nTo'g'ri yozilishi:\n<code>{esc(USAGE[cmd])}</code>")
        except Exception:
            pass
    except Exception as e:
        try:
            await say(event, f"⚠️ Xato: <code>{esc(str(e)[:300])}</code>\n\nNamuna:\n<code>{esc(USAGE[cmd])}</code>")
        except Exception:
            pass


# ================= ISHGA TUSHIRISH =================
async def warmup():
    await client.get_dialogs()
    for pid, c in db["channels"].items():
        if c.get("username"):
            username_to_id[c["username"]] = pid
        try:
            await get_peer(pid)
        except Exception:
            pass
        await fetch_linked(pid)
    if db["report"]:
        try:
            await get_peer(db["report"]["id"])
        except Exception:
            pass
    rebuild_texts()
    await async_save_data()
    ensure_pollers()
    print(f">>> {len(texts)} kanal, {len(group_to_channel)} guruh tayyor")


async def main():
    global _save_lock
    _save_lock = asyncio.Lock()
    await start_web_server()
    await client.start()
    await warmup()
    asyncio.create_task(saver_loop())
    asyncio.create_task(bot_loop())
    gc.collect()
    gc.freeze()
    print(">>> Bot maksimal tezlikda ishga tushdi!")
    await client.run_until_disconnected()


if __name__ == "__main__":
    if uvloop:
        uvloop.run(main())
    else:
        asyncio.run(main())
