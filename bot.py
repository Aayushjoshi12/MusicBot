"""
Discord Music Bot — Gemini AI + Advanced Playback (v4 — "Hydra-class")
=========================================================================================
Single, de-duplicated source file. Requires discord.py 2.x.

SETUP
-----
1. Create a `.env` file next to this script (never commit it):

    DISCORD_TOKEN=your_discord_bot_token
    GEMINI_API_KEY=your_gemini_api_key
    GENIUS_TOKEN=your_genius_token          # optional — falls back to hardcoded token
    OWNER_IDS=123456789012345678,987654321098765432
    YTDLP_COOKIES_FILE=cookies.txt          # optional, helps with age/bot-check blocks

2. pip install -U discord.py yt-dlp PyNaCl aiohttp python-dotenv google-generativeai cachetools lyricsgenius
3. Install ffmpeg and make sure it's on PATH.
4. python musicbot.py

WHAT'S NEW IN v4
----------------
Every v3 feature is preserved (seek, download, 8D, playnext, add-all, progress bar).
Added, without breaking anything:

  INSTANT PLAY   !play now plays the first result immediately and offers a
                 "🔍 Wrong Song" button that reuses the *cached* 6 results —
                 no second YouTube call.
  !search        Old picker behaviour: search + dropdown, never auto-plays.
  PERFORMANCE    Search cache 2h, stream cache 6h, background preload of the
                 next queue track so Skip is near-instant. All yt-dlp stays
                 inside run_in_executor — never blocks the event loop.
  QUEUE TOOLS    !previous !jump !move !swap "!queue search" !dedupe !clearhistory
  PLAYLISTS      !playlist create|save|load|delete|rename|list  (SQLite)
  FAVORITES      !favorite remove, !favorites clear|export|import  (+ existing)
  SPOTIFY        Spotify track/album/playlist links -> metadata -> YouTube match
  MULTI-SOURCE   ytsearch / ytmsearch / scsearch / bandcamp / URL passthrough
  NOW PLAYING    Full button deck: ⏮ ⏸ ▶ ⏭ 🔀 🔁 ❤️ ⬇ 🎤 🔍 📜 + volume,
                 plus a live-updating progress bar.
  AUDIO          Equalizer presets (rock/pop/bass/edm/jazz/classical), custom EQ,
                 loudness normalization.
  LYRICS         Cached Genius searches + lyric text; translate & explain.
  SMART / STATS  Most-played, top listeners, recently played, autoplay recs.
  DJ             Vote-skip, DJ role, queue lock, requester-only skip, admin override.
  SLASH          Hybrid commands: !play and /play both work, with autocomplete.
"""

# =========================
# IMPORTS
# =========================
import asyncio
import io
import json
import logging
import os
import platform
import random
import re
import shutil
import signal
import sqlite3
import sys
import tempfile
import time
from functools import partial

import aiohttp
import discord
import lyricsgenius
import yt_dlp
from cachetools import TTLCache
from discord import app_commands
from discord.ext import commands, tasks
from dotenv import load_dotenv
import google.generativeai as genai

# =========================
# LOGGING
# =========================
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(name)s: %(message)s",
)
log = logging.getLogger("musicbot")

BOT_VERSION = "4.2.0"
BOT_START_TIME = time.time()

# =========================
# CONFIG (env vars only — no hardcoded secrets except the Genius fallback)
# =========================
load_dotenv()

TOKEN = os.getenv("DISCORD_TOKEN")
GEMINI_KEY = os.getenv("GEMINI_API_KEY")
GEMINI_MODEL = os.getenv("GEMINI_MODEL", "gemini-2.5-flash")
COOKIES_FILE = os.getenv("YTDLP_COOKIES_FILE")

OWNER_IDS = {
    int(uid.strip())
    for uid in os.getenv("OWNER_IDS", "").split(",")
    if uid.strip().isdigit()
}

_GENIUS_TOKEN_FALLBACK = "hVNOXC5Jzc0tUpVf1HHf4vStB6WrjhmSvZjx7Hu-ETPRKGF6SBL1dCJYb-0a8LGc"
GENIUS_TOKEN = os.getenv("GENIUS_TOKEN", _GENIUS_TOKEN_FALLBACK)

genius = lyricsgenius.Genius(GENIUS_TOKEN)
genius.verbose = False
genius.remove_section_headers = True
genius.skip_non_songs = True
genius.excluded_terms = ["(Remix)", "(Live)"]

if not TOKEN:
    raise SystemExit("DISCORD_TOKEN is not set. Put it in your environment or a .env file.")

if GEMINI_KEY:
    genai.configure(api_key=GEMINI_KEY)
    ai_model = genai.GenerativeModel(GEMINI_MODEL)
    log.info("Gemini model initialised: %s", GEMINI_MODEL)
else:
    ai_model = None
    log.warning("GEMINI_API_KEY not set — AI commands will report an error until configured.")

intents = discord.Intents.default()
intents.message_content = True
intents.voice_states = True
intents.members = True

bot = commands.Bot(command_prefix="!", intents=intents, help_command=None)


class MusicError(Exception):
    """Raised for user-facing music/playback problems."""


# =========================
# DATABASE (SQLite)
# All existing tables preserved; new tables added with IF NOT EXISTS.
# =========================
conn = sqlite3.connect("musicbot.db")
conn.execute("PRAGMA journal_mode=WAL")
conn.execute("PRAGMA synchronous=NORMAL")  # faster writes, still crash-safe with WAL
cur = conn.cursor()

cur.executescript("""
CREATE TABLE IF NOT EXISTS guild_settings (
    guild_id INTEGER PRIMARY KEY,
    volume REAL DEFAULT 0.5,
    prefix TEXT DEFAULT '!'
);
CREATE TABLE IF NOT EXISTS playlists (
    guild_id INTEGER PRIMARY KEY,
    name TEXT,
    data TEXT
);
CREATE TABLE IF NOT EXISTS user_favorites (
    user_id INTEGER,
    url TEXT,
    title TEXT,
    UNIQUE(user_id, url)
);
CREATE TABLE IF NOT EXISTS stats (
    user_id INTEGER,
    guild_id INTEGER,
    songs_played INTEGER DEFAULT 0,
    UNIQUE(user_id, guild_id)
);

-- v4 additions --
CREATE TABLE IF NOT EXISTS named_playlists (
    guild_id INTEGER,
    name TEXT,
    data TEXT,
    owner_id INTEGER,
    UNIQUE(guild_id, name)
);
CREATE TABLE IF NOT EXISTS play_counts (
    guild_id INTEGER,
    url TEXT,
    title TEXT,
    plays INTEGER DEFAULT 0,
    UNIQUE(guild_id, url)
);
CREATE TABLE IF NOT EXISTS dj_settings (
    guild_id INTEGER PRIMARY KEY,
    dj_role_id INTEGER,
    queue_locked INTEGER DEFAULT 0,
    requester_only_skip INTEGER DEFAULT 0
);

-- v4.1 additions --
CREATE TABLE IF NOT EXISTS artist_counts (
    guild_id INTEGER,
    artist TEXT,
    plays INTEGER DEFAULT 0,
    UNIQUE(guild_id, artist)
);
""")
conn.commit()

# Backward-compatible column migration for listening time.
try:
    cur.execute("ALTER TABLE stats ADD COLUMN listen_seconds INTEGER DEFAULT 0")
    conn.commit()
except Exception:
    pass  # column already exists

# =========================
# GLOBAL STATE
# =========================
queues = {}              # guild_id -> list[song]
now_playing = {}         # guild_id -> song | None
repeat_mode = {}         # guild_id -> "off" | "song" | "queue"
autoplay_enabled = {}    # guild_id -> bool
audio_filters = {}       # guild_id -> dict of active filters
song_history = {}        # guild_id -> list[song]  (max 50)
last_requester = {}      # guild_id -> user_id who last queued a track
seek_positions = {}      # guild_id -> int seconds to seek when next song starts
song_start_times = {}    # guild_id -> float playback start (adjusted for seeks)
search_results_cache = {}  # guild_id -> list[song]  (last 6 results, for "Wrong Song")
np_messages = {}         # guild_id -> discord.Message (current now-playing msg, for live bar)
np_channels = {}         # guild_id -> channel (where to send now-playing)
vote_skips = {}          # guild_id -> set[user_id]
queue_snapshots = {}     # guild_id -> named saved queue: {name: list[song]}
queue_undo = {}          # guild_id -> list[list[song]]  (undo stack, max 10)

MAX_HISTORY = 50
MAX_UNDO = 10


def get_queue(guild_id):
    return queues.setdefault(guild_id, [])


def save_guild_queue(guild_id):
    """Persist a single guild's queue immediately (called after every mutation)."""
    try:
        cur.execute(
            """INSERT INTO playlists (guild_id, name, data) VALUES (?, 'autosave', ?)
               ON CONFLICT(guild_id) DO UPDATE SET data=excluded.data""",
            (guild_id, json.dumps(queues.get(guild_id, []))),
        )
        conn.commit()
    except Exception:
        log.exception("Failed to autosave queue for guild %s", guild_id)


# =========================
# YT-DLP
# =========================
_UA = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/124.0 Safari/537.36"
)


def _base_opts():
    opts = {
        "quiet": True,
        "no_warnings": True,
        "nocheckcertificate": True,
        "geo_bypass": True,
        "socket_timeout": 15,
        "retries": 3,
        "fragment_retries": 3,
        "extractor_retries": 2,
        "extractor_args": {"youtube": {"player_client": ["android", "web"]}},
        "http_headers": {"User-Agent": _UA},
    }
    if COOKIES_FILE:
        opts["cookiefile"] = COOKIES_FILE
    return opts


def _flat_opts():
    opts = {
        "quiet": True,
        "no_warnings": True,
        "nocheckcertificate": True,
        "geo_bypass": True,
        "socket_timeout": 8,
        "retries": 1,
        "extractor_retries": 0,
        "format": "bestaudio/best",
        "noplaylist": False,
        "default_search": "ytsearch",
        "ignoreerrors": True,
        "extract_flat": "in_playlist",
        "skip_download": True,
        "http_headers": {"User-Agent": _UA},
    }
    if COOKIES_FILE:
        opts["cookiefile"] = COOKIES_FILE
    return opts


RESOLVE_FORMAT_CHAIN = [
    "bestaudio[acodec!=none]/best[acodec!=none]",
    "bestaudio/best",
    "best",
]

FFMPEG_BASE_BEFORE = "-reconnect 1 -reconnect_streamed 1 -reconnect_delay_max 5"

# Bigger caches per the performance brief: search 2h, stream 6h.
SEARCH_CACHE = TTLCache(maxsize=1000, ttl=7200)    # 2 hours
STREAM_CACHE = TTLCache(maxsize=800, ttl=21600)    # 6 hours
LYRICS_CACHE = TTLCache(maxsize=300, ttl=21600)    # 6 hours

# Prefix -> yt-dlp search provider, for multi-source search.
SEARCH_PROVIDERS = {
    "yt": "ytsearch",
    "ytm": "https://music.youtube.com/search?q=",  # handled specially below
    "sc": "scsearch",
    "soundcloud": "scsearch",
}


def is_url(text):
    t = text.strip().lower()
    return t.startswith("http://") or t.startswith("https://")


def _extract_info_sync(query, opts):
    with yt_dlp.YoutubeDL(opts) as ydl:
        return ydl.extract_info(query, download=False)


async def _run_extract(query, opts):
    """Run blocking yt-dlp in a thread so the event loop is never blocked."""
    loop = asyncio.get_running_loop()
    return await loop.run_in_executor(None, partial(_extract_info_sync, query, opts))


def _stub_from_entry(entry):
    return {
        "title": entry.get("title") or "Unknown title",
        "webpage_url": entry.get("webpage_url") or entry.get("url"),
        "thumbnail": entry.get("thumbnail"),
        "duration": entry.get("duration"),
        "uploader": entry.get("uploader") or entry.get("channel"),
    }


def _apply_search_prefix(query, limit):
    """
    Translate optional source prefixes into a yt-dlp query.
    Examples: "sc: lofi" -> soundcloud, "ytm: drake" -> yt music, else ytsearch.
    Returns (query_for_ytdlp, default_search_or_None).
    """
    m = re.match(r"^(yt|ytm|sc|soundcloud)\s*:\s*(.+)$", query, re.IGNORECASE)
    if not m:
        return query, f"ytsearch{limit}"
    prefix, term = m.group(1).lower(), m.group(2).strip()
    if prefix in ("sc", "soundcloud"):
        return term, f"scsearch{limit}"
    if prefix == "ytm":
        # YouTube Music search via URL — yt-dlp understands the search page.
        return f"https://music.youtube.com/search?q={term}", None
    return term, f"ytsearch{limit}"


async def resolve_query(query, limit=6):
    """
    Fast, metadata-only resolution (never resolves a playable stream here).
    Supports YouTube, YouTube Music, SoundCloud, Bandcamp/other URLs, playlists.
    Returns a list of song stubs. Cached for 2 hours.
    """
    cache_key = (query, limit)
    if cache_key in SEARCH_CACHE:
        return SEARCH_CACHE[cache_key]

    opts = _flat_opts()
    if is_url(query):
        target = query
    else:
        target, default_search = _apply_search_prefix(query, limit)
        if default_search:
            opts["default_search"] = default_search

    try:
        data = await _run_extract(target, opts)
    except yt_dlp.utils.DownloadError as e:
        raise MusicError(f"Couldn't find that: {e}") from e
    except Exception as e:
        raise MusicError(f"Unexpected error resolving track: {e}") from e

    if not data:
        raise MusicError("No results found.")

    if "entries" in data:
        def _flatten(entries):
            for e in entries:
                if not e:
                    continue
                if "entries" in e:
                    yield from _flatten(e["entries"])
                else:
                    yield e

        entries = list(_flatten(data["entries"]))
        if not entries:
            raise MusicError("No playable results found (playlist may be empty or private).")
        stubs = [_stub_from_entry(e) for e in entries[:limit] if e.get("webpage_url") or e.get("url")]
        if not stubs:
            raise MusicError("No playable results found.")
    else:
        stubs = [_stub_from_entry(data)]

    SEARCH_CACHE[cache_key] = stubs
    return stubs


def _classify_download_error(e):
    msg = str(e).lower()
    if "private video" in msg:
        return "that video is private."
    if "video unavailable" in msg or "has been removed" in msg:
        return "the video was removed or is unavailable."
    if "sign in to confirm" in msg or ("bot" in msg and "confirm" in msg):
        return "YouTube is rate-limiting/bot-checking (try again shortly, or set YTDLP_COOKIES_FILE)."
    if "geo" in msg or "not available in your country" in msg:
        return "that video is region-locked."
    if "age" in msg and "restrict" in msg:
        return "that video is age-restricted (set YTDLP_COOKIES_FILE to allow it)."
    if "timed out" in msg or "timeout" in msg:
        return "the request timed out — YouTube may be slow right now."
    return str(e)


async def _resolve_one(webpage_url):
    last_err = None
    for fmt in RESOLVE_FORMAT_CHAIN:
        opts = _base_opts()
        opts.update({
            "format": fmt,
            "noplaylist": True,
            "ignoreerrors": False,
            "skip_download": True,
        })
        for attempt in range(2):
            try:
                data = await _run_extract(webpage_url, opts)
                if data:
                    url = data.get("url")
                    if not url and data.get("requested_formats"):
                        url = data["requested_formats"][0].get("url")
                    if url:
                        return url
            except yt_dlp.utils.DownloadError as e:
                last_err = e
                low = str(e).lower()
                if "private" in low or "unavailable" in low or "removed" in low:
                    raise MusicError(f"Couldn't stream — {_classify_download_error(e)}") from e
                await asyncio.sleep(1.5 * (attempt + 1))
                continue
            except Exception as e:
                last_err = e
                await asyncio.sleep(1.0)
                continue
    if last_err:
        raise MusicError(f"Couldn't stream — {_classify_download_error(last_err)}")
    raise MusicError("Couldn't resolve a playable stream for that track.")


async def get_stream_url(song):
    """Lazily resolve the audio stream URL, cached 6h, with title-search fallback."""
    webpage = song.get("webpage_url")
    if not webpage:
        raise MusicError("This track has no source URL.")

    if webpage in STREAM_CACHE:
        return STREAM_CACHE[webpage]

    try:
        stream_url = await _resolve_one(webpage)
    except MusicError:
        title = song.get("title")
        if not title or title == "Unknown title":
            raise
        try:
            alts = await resolve_query(title, limit=3)
        except MusicError:
            raise
        for alt in alts:
            if alt.get("webpage_url") == webpage:
                continue
            try:
                stream_url = await _resolve_one(alt["webpage_url"])
                song["webpage_url"] = alt["webpage_url"]
                song["title"] = alt["title"]
                break
            except MusicError:
                continue
        else:
            raise

    STREAM_CACHE[webpage] = stream_url
    STREAM_CACHE[song.get("webpage_url", webpage)] = stream_url
    return stream_url


async def preload_next(guild_id):
    """
    Background: resolve the stream URL of the next queued track so Skip is
    near-instant. Fire-and-forget; failures are ignored (they'll be retried
    for real when the track actually plays).
    """
    queue = get_queue(guild_id)
    if not queue:
        return
    nxt = queue[0]
    url = nxt.get("webpage_url")
    if not url or url in STREAM_CACHE:
        return
    try:
        await get_stream_url(nxt)
        log.debug("Preloaded next track in guild %s", guild_id)
    except MusicError:
        pass


# =========================
# SPOTIFY (metadata only — search YouTube for the match)
# Uses the public oEmbed endpoint so no Spotify API credentials are needed.
# =========================
SPOTIFY_RE = re.compile(r"open\.spotify\.com/(track|album|playlist)/([A-Za-z0-9]+)")


async def spotify_to_queries(url):
    """
    Turn a Spotify track/album/playlist link into a list of search strings.
    We can't stream Spotify; we extract a human-readable title and search YT.

    oEmbed returns the *title* of the resource (track name, or album/playlist
    name). For albums/playlists that single title is used as one search — good
    enough to surface the album on YouTube, which usually has a full upload.
    """
    m = SPOTIFY_RE.search(url)
    if not m:
        return []
    try:
        async with aiohttp.ClientSession() as session:
            async with session.get(
                "https://open.spotify.com/oembed", params={"url": url}, timeout=10
            ) as r:
                if r.status != 200:
                    return []
                data = await r.json()
    except (aiohttp.ClientError, asyncio.TimeoutError):
        return []
    title = data.get("title")
    if not title:
        return []
    return [title]


# =========================
# VOLUME (persisted per guild)
# =========================
def get_volume(guild_id):
    cur.execute("SELECT volume FROM guild_settings WHERE guild_id=?", (guild_id,))
    row = cur.fetchone()
    return row[0] if row else 0.5


def set_volume(guild_id, vol):
    vol = max(0.0, min(2.0, vol))
    cur.execute(
        """INSERT INTO guild_settings (guild_id, volume) VALUES (?, ?)
           ON CONFLICT(guild_id) DO UPDATE SET volume=excluded.volume""",
        (guild_id, vol),
    )
    conn.commit()
    return vol


# =========================
# AUDIO FILTERS + EQUALIZER
# =========================
FILTER_PRESETS = {
    "bassboost": "bass=g=12",
    "treble": "treble=g=8",
    "echo": "aecho=0.8:0.9:1000:0.3",
    "karaoke": "pan=stereo|c0=c0-c1|c1=c1-c0",
    "8d": "apulsator=hz=0.09",
    "normalize": "loudnorm=I=-16:TP=-1.5:LRA=11",  # loudness normalization / ReplayGain-style
}

# Equalizer presets built on ffmpeg's `equalizer` filter (per-band gain in dB).
EQ_PRESETS = {
    "rock": "equalizer=f=60:t=q:w=1:g=5,equalizer=f=1000:t=q:w=1:g=-2,equalizer=f=8000:t=q:w=1:g=4",
    "pop": "equalizer=f=100:t=q:w=1:g=2,equalizer=f=2000:t=q:w=1:g=3,equalizer=f=8000:t=q:w=1:g=2",
    "bass": "equalizer=f=60:t=q:w=1:g=8,equalizer=f=120:t=q:w=1:g=5",
    "edm": "equalizer=f=50:t=q:w=1:g=6,equalizer=f=200:t=q:w=1:g=2,equalizer=f=10000:t=q:w=1:g=5",
    "jazz": "equalizer=f=200:t=q:w=1:g=2,equalizer=f=1000:t=q:w=1:g=1,equalizer=f=6000:t=q:w=1:g=3",
    "classical": "equalizer=f=100:t=q:w=1:g=-1,equalizer=f=4000:t=q:w=1:g=2,equalizer=f=12000:t=q:w=1:g=3",
    "flat": None,
}


def build_filter_chain(guild_id):
    f = audio_filters.get(guild_id, {})
    parts = []
    if f.get("speed"):
        parts.append(f"atempo={f['speed']}")
    if f.get("pitch"):
        parts.append(f"asetrate=44100*{f['pitch']},aresample=44100")
    # Equalizer preset or custom EQ string.
    if f.get("eq"):
        parts.append(f["eq"])
    for key, chain in FILTER_PRESETS.items():
        if f.get(key):
            parts.append(chain)
    return ",".join(parts) if parts else None


def create_source(url, guild_id, seek=0):
    """FFmpegPCMAudio source with optional seek (-ss) and the active filter chain."""
    chain = build_filter_chain(guild_id)
    before_opts = FFMPEG_BASE_BEFORE
    if seek > 0:
        before_opts = f"-ss {int(seek)} " + before_opts
    ffmpeg_opts = {
        "before_options": before_opts,
        "options": f"-vn -af {chain}" if chain else "-vn",
    }
    return discord.FFmpegPCMAudio(url, **ffmpeg_opts)


def set_filter(guild_id, **kwargs):
    audio_filters.setdefault(guild_id, {}).update(kwargs)


def reset_filters(guild_id):
    audio_filters[guild_id] = {}


# =========================
# DJ / PERMISSIONS
# =========================
def get_dj_settings(guild_id):
    cur.execute(
        "SELECT dj_role_id, queue_locked, requester_only_skip FROM dj_settings WHERE guild_id=?",
        (guild_id,),
    )
    row = cur.fetchone()
    if not row:
        return {"dj_role_id": None, "queue_locked": 0, "requester_only_skip": 0}
    return {"dj_role_id": row[0], "queue_locked": row[1], "requester_only_skip": row[2]}


def set_dj_setting(guild_id, **kwargs):
    settings = get_dj_settings(guild_id)
    settings.update(kwargs)
    cur.execute(
        """INSERT INTO dj_settings (guild_id, dj_role_id, queue_locked, requester_only_skip)
           VALUES (?, ?, ?, ?)
           ON CONFLICT(guild_id) DO UPDATE SET
             dj_role_id=excluded.dj_role_id,
             queue_locked=excluded.queue_locked,
             requester_only_skip=excluded.requester_only_skip""",
        (guild_id, settings["dj_role_id"], settings["queue_locked"], settings["requester_only_skip"]),
    )
    conn.commit()


def is_dj(member):
    """A member is a DJ if owner, has Manage Guild, or holds the DJ role."""
    if member.id in OWNER_IDS:
        return True
    if member.guild_permissions.manage_guild:
        return True
    settings = get_dj_settings(member.guild.id)
    if settings["dj_role_id"]:
        return any(r.id == settings["dj_role_id"] for r in member.roles)
    # No DJ role configured -> everyone can DJ (default open behaviour).
    return settings["dj_role_id"] is None


def queue_locked(guild_id):
    return bool(get_dj_settings(guild_id)["queue_locked"])


# =========================
# VOICE HELPERS
# =========================
async def connect_vc(ctx):
    if ctx.voice_client:
        return ctx.voice_client
    if ctx.author.voice:
        try:
            return await ctx.author.voice.channel.connect(reconnect=True, timeout=15)
        except discord.ClientException as e:
            await ctx.send(f"❌ Couldn't join voice: {e}")
            return None
        except asyncio.TimeoutError:
            await ctx.send("❌ Timed out connecting to voice.")
            return None
    await ctx.send("❌ Join a voice channel first!")
    return None


# =========================
# PLAYBACK CORE
# =========================
def format_duration(seconds):
    if not seconds or seconds < 0:
        return "?:??"
    seconds = int(seconds)
    mins, secs = divmod(seconds, 60)
    hrs, mins = divmod(mins, 60)
    if hrs:
        return f"{hrs}:{mins:02d}:{secs:02d}"
    return f"{mins}:{secs:02d}"


def progress_bar(elapsed, total, width=16):
    if not total or total <= 0:
        return f"`{'─' * width}` {format_duration(elapsed)} / ?:??"
    ratio = max(0.0, min(1.0, elapsed / total))
    filled = int(ratio * width)
    filled = max(0, min(width - 1, filled))
    bar = "▬" * filled + "🔘" + "▬" * (width - filled - 1)
    return f"{bar}\n`{format_duration(elapsed)} / {format_duration(total)}`"


async def autoplay_fill(guild_id):
    last = now_playing.get(guild_id)
    if not last:
        return
    try:
        results = await resolve_query(last["title"], limit=5)
        candidates = [r for r in results if r.get("webpage_url") != last.get("webpage_url")]
        if candidates:
            get_queue(guild_id).append(random.choice(candidates))
    except MusicError:
        pass


def add_history(guild_id, song):
    hist = song_history.setdefault(guild_id, [])
    hist.append(song)
    if len(hist) > MAX_HISTORY:
        hist.pop(0)


def record_stat(user_id, guild_id, listen_seconds=0):
    if not user_id:
        return
    cur.execute(
        """INSERT INTO stats (user_id, guild_id, songs_played, listen_seconds)
           VALUES (?, ?, 1, ?)
           ON CONFLICT(user_id, guild_id) DO UPDATE SET
               songs_played = songs_played + 1,
               listen_seconds = listen_seconds + excluded.listen_seconds""",
        (user_id, guild_id, int(listen_seconds or 0)),
    )
    conn.commit()


def record_play_count(guild_id, song):
    """Track most-played songs and artists per guild for statistics."""
    url = song.get("webpage_url")
    if not url:
        return
    cur.execute(
        """INSERT INTO play_counts (guild_id, url, title, plays) VALUES (?, ?, ?, 1)
           ON CONFLICT(guild_id, url) DO UPDATE SET plays = plays + 1, title = excluded.title""",
        (guild_id, url, song.get("title", "Unknown")),
    )
    artist = (song.get("uploader") or "").strip()
    if artist:
        cur.execute(
            """INSERT INTO artist_counts (guild_id, artist, plays) VALUES (?, ?, 1)
               ON CONFLICT(guild_id, artist) DO UPDATE SET plays = plays + 1""",
            (guild_id, artist),
        )
    conn.commit()


_consecutive_failures = {}
MAX_CONSECUTIVE_FAILURES = 3

# =========================
# UNIFIED PLAYBACK CONTROLLER
# One asyncio.Lock per guild guarantees only one vc.play() transition can run at
# a time, so two commands (or a command + the after-callback) can never start
# playback simultaneously. Every transition — skip, previous, autoplay, repeat,
# filters, seek, wrong song, playlist play, queue restore, play, playnext, and
# the after-callback — funnels through play_next(), the ONLY caller of vc.play().
# =========================
_playback_locks = {}


def playback_lock(guild_id):
    return _playback_locks.setdefault(guild_id, asyncio.Lock())


async def play_next(channel, guild):
    """
    Core playback transition — the single source of truth for starting audio.
    Serialized per-guild by a lock, and it NEVER starts a second stream while one
    is already active. It advances through unplayable tracks with a loop (no
    recursion) and, on a hard vc.play() failure, restores the song and returns
    safely instead of recursing.
    """
    guild_id = guild.id

    async with playback_lock(guild_id):
        vc = guild.voice_client
        if not vc:
            return

        # HARD GUARD: never call vc.play() while audio is already active. If a
        # transition is in flight (e.g. a command called vc.stop() and its after
        # callback is about to fire), we bail out — the after callback will drive
        # the next track. This is what prevents "Already playing audio".
        if vc.is_playing() or vc.is_paused():
            log.debug("play_next: audio already active in guild %s — skipping", guild_id)
            return

        np_channels[guild_id] = channel
        vote_skips.pop(guild_id, None)  # reset votes each track
        queue = get_queue(guild_id)

        # Repeat handling — done once, before we start pulling candidates.
        if repeat_mode.get(guild_id) == "song" and now_playing.get(guild_id):
            queue.insert(0, now_playing[guild_id])
        elif repeat_mode.get(guild_id) == "queue" and now_playing.get(guild_id):
            queue.append(now_playing[guild_id])

        # A pending seek only applies to the FIRST candidate we try.
        seek_secs = seek_positions.pop(guild_id, 0)

        song = None
        stream_url = None
        while True:
            if not queue and autoplay_enabled.get(guild_id):
                await autoplay_fill(guild_id)
            if not queue:
                now_playing[guild_id] = None
                return

            candidate = queue.pop(0)
            try:
                stream_url = await get_stream_url(candidate)
            except MusicError as e:
                await channel.send(f"❌ Skipping **{candidate['title']}** — {e}")
                _consecutive_failures[guild_id] = _consecutive_failures.get(guild_id, 0) + 1
                if _consecutive_failures[guild_id] >= MAX_CONSECUTIVE_FAILURES:
                    _consecutive_failures[guild_id] = 0
                    now_playing[guild_id] = None
                    await channel.send(
                        "⚠️ Multiple tracks failed in a row — pausing. Try `!play` again."
                    )
                    return
                seek_secs = 0  # the seek was meant for the intended first song only
                continue
            song = candidate
            break

        _consecutive_failures[guild_id] = 0
        now_playing[guild_id] = song
        add_history(guild_id, song)
        record_play_count(guild_id, song)
        song_start_times[guild_id] = time.time() - seek_secs

        def after(err):
            if err:
                log.warning("Playback error in guild %s: %s", guild_id, err)
            # Schedule the next transition on the event loop. play_next re-acquires
            # the lock, so concurrent after callbacks can never overlap.
            asyncio.run_coroutine_threadsafe(play_next(channel, guild), bot.loop)

        try:
            source = create_source(stream_url, guild_id, seek=seek_secs)
            source = discord.PCMVolumeTransformer(source, volume=get_volume(guild_id))
            vc.play(source, after=after)
        except Exception as e:
            # Do NOT recurse. Restore the song to the front and return safely so the
            # user can retry; a recursive call here is exactly what desynced skip.
            log.exception("Failed to start playback in guild %s", guild_id)
            queue.insert(0, song)
            now_playing[guild_id] = None
            await channel.send(f"❌ Couldn't play **{song['title']}**: {e}")
            return

        try:
            record_stat(
                last_requester.get(guild_id, 0),
                guild_id,
                listen_seconds=song.get("duration") or 0,
            )
        except Exception:
            pass

    # Outside the lock: UI + preload (no vc.play() here, safe to run unlocked).
    await send_now_playing(channel, guild)
    asyncio.create_task(preload_next(guild_id))


async def start_if_idle(channel, guild):
    """Start playback only if nothing is currently playing/paused."""
    vc = guild.voice_client
    if vc and not vc.is_playing() and not vc.is_paused():
        await play_next(channel, guild)


async def transition_now(channel, guild):
    """
    Force a transition to whatever is at the front of the queue. If audio is
    active, stop it once and let the after-callback start the next track; if idle,
    start immediately. Callers must set up the queue/seek/now_playing state first.
    """
    vc = guild.voice_client
    if not vc:
        return
    np_channels[guild.id] = channel
    if vc.is_playing() or vc.is_paused():
        vc.stop()  # after() -> play_next starts the front-of-queue track
    else:
        await play_next(channel, guild)


def build_now_playing_embed(guild):
    guild_id = guild.id
    song = now_playing.get(guild_id)
    if not song:
        return None
    elapsed = time.time() - song_start_times.get(guild_id, time.time())
    duration = song.get("duration")

    embed = discord.Embed(
        title="🎵 Now Playing",
        description=f"**[{song['title']}]({song.get('webpage_url', '')})**",
        color=discord.Color.from_rgb(88, 101, 242),
    )
    embed.add_field(name="​", value=progress_bar(elapsed, duration), inline=False)
    embed.add_field(name="Repeat", value=repeat_mode.get(guild_id, "off"), inline=True)
    embed.add_field(name="Autoplay", value="on" if autoplay_enabled.get(guild_id) else "off", inline=True)
    embed.add_field(name="Volume", value=f"{int(get_volume(guild_id) * 100)}%", inline=True)
    queued = len(get_queue(guild_id))
    embed.add_field(name="Up Next", value=f"{queued} track(s)" if queued else "Queue empty", inline=True)
    if song.get("uploader"):
        embed.add_field(name="Artist", value=song["uploader"][:40], inline=True)
    active = [k for k, v in audio_filters.get(guild_id, {}).items() if v]
    if active:
        embed.add_field(name="Filters", value=", ".join(active)[:60], inline=True)
    if song.get("thumbnail"):
        embed.set_thumbnail(url=song["thumbnail"])
    return embed


async def send_now_playing(channel, guild):
    guild_id = guild.id
    if not now_playing.get(guild_id):
        return
    embed = build_now_playing_embed(guild)
    if not embed:
        return
    msg = await channel.send(embed=embed, view=MusicPanel())
    np_messages[guild_id] = msg


@tasks.loop(seconds=12)
async def live_progress_updater():
    """Edit each guild's now-playing message so the progress bar advances live."""
    for guild_id, msg in list(np_messages.items()):
        guild = bot.get_guild(guild_id)
        if not guild or not now_playing.get(guild_id):
            continue
        vc = guild.voice_client
        if not vc or not (vc.is_playing() or vc.is_paused()):
            continue
        embed = build_now_playing_embed(guild)
        if not embed:
            continue
        try:
            await msg.edit(embed=embed, view=MusicPanel())
        except discord.HTTPException:
            np_messages.pop(guild_id, None)


# =========================
# DOWNLOAD HELPER
# =========================
async def _do_download(target, song):
    async def _send(content=None, file=None):
        if isinstance(target, discord.Interaction):
            if file:
                await target.followup.send(file=file, ephemeral=True)
            else:
                await target.followup.send(content, ephemeral=True)
        else:
            if file:
                await target.send(file=file)
            else:
                await target.send(content)

    webpage_url = song.get("webpage_url")
    if not webpage_url:
        return await _send("❌ No URL available for this track.")

    safe_title = "".join(
        c for c in song.get("title", "audio") if c.isalnum() or c in " -_"
    ).strip()[:50] or "audio"

    tmpdir = tempfile.mkdtemp()
    output_tpl = os.path.join(tmpdir, f"{safe_title}.%(ext)s")

    opts = {
        "quiet": True,
        "no_warnings": True,
        "format": "bestaudio[ext=webm]/bestaudio[ext=m4a]/bestaudio/best",
        "outtmpl": output_tpl,
        "noplaylist": True,
        "nocheckcertificate": True,
        "geo_bypass": True,
        "socket_timeout": 30,
        "retries": 2,
    }
    if COOKIES_FILE:
        opts["cookiefile"] = COOKIES_FILE

    loop = asyncio.get_running_loop()
    try:
        def _dl():
            with yt_dlp.YoutubeDL(opts) as ydl:
                info = ydl.extract_info(webpage_url, download=True)
                return ydl.prepare_filename(info)

        filepath = await loop.run_in_executor(None, _dl)

        if not os.path.exists(filepath):
            candidates = [os.path.join(tmpdir, f) for f in os.listdir(tmpdir)]
            if not candidates:
                return await _send("❌ Download produced no file.")
            filepath = max(candidates, key=os.path.getsize)

        size = os.path.getsize(filepath)
        limit_bytes = 8 * 1024 * 1024
        if size > limit_bytes:
            return await _send(
                f"❌ File is **{size // 1024 // 1024} MB** — too large for Discord (8 MB limit).\n"
                f"Stream it here instead: <{webpage_url}>"
            )

        discord_file = discord.File(filepath, filename=os.path.basename(filepath))
        await _send(file=discord_file)
    except Exception as e:
        log.exception("Download failed for %s", webpage_url)
        await _send(f"❌ Download failed: {e}\nTry streaming here: <{webpage_url}>")
    finally:
        shutil.rmtree(tmpdir, ignore_errors=True)


# =========================
# LYRICS HELPER (multi-provider + cache)
# Provider priority: LRCLIB -> Genius -> Lyrics.ovh -> Gemini AI fallback.
# =========================
def _split_artist_title(query):
    """Best-effort split of 'Artist - Title' into (artist, title)."""
    if " - " in query:
        artist, title = query.split(" - ", 1)
        return artist.strip(), title.strip()
    return "", query.strip()


async def _lyrics_from_lrclib(query):
    """LRCLIB — free, no key, supports synced (LRC) lyrics."""
    artist, title = _split_artist_title(query)
    params = {"q": query} if not artist else {"artist_name": artist, "track_name": title}
    url = "https://lrclib.net/api/search" if not artist else "https://lrclib.net/api/get"
    try:
        async with aiohttp.ClientSession() as session:
            async with session.get(url, params=params, timeout=10) as resp:
                if resp.status != 200:
                    return None
                data = await resp.json()
        entry = data[0] if isinstance(data, list) and data else (data if isinstance(data, dict) else None)
        if not entry:
            return None
        plain = entry.get("plainLyrics")
        synced = entry.get("syncedLyrics")
        if not (plain or synced):
            return None
        return {
            "title": entry.get("trackName") or title or query,
            "artist": entry.get("artistName") or artist or "Unknown",
            "lyrics": plain or synced,
            "synced": synced,
            "art": None,
            "source": "LRCLIB",
        }
    except Exception:
        log.debug("LRCLIB lookup failed for %s", query, exc_info=True)
        return None


async def _lyrics_from_genius(query):
    try:
        result = await asyncio.to_thread(genius.search_song, query)
    except Exception:
        log.debug("Genius lookup failed for %s", query, exc_info=True)
        return None
    if not result:
        return None
    return {
        "title": result.title,
        "artist": result.artist,
        "lyrics": result.lyrics,
        "synced": None,
        "art": result.song_art_image_url,
        "source": "Genius",
    }


async def _lyrics_from_ovh(query):
    """Lyrics.ovh — free, no key. Requires an artist/title split."""
    artist, title = _split_artist_title(query)
    if not artist or not title:
        return None
    try:
        async with aiohttp.ClientSession() as session:
            async with session.get(
                f"https://api.lyrics.ovh/v1/{artist}/{title}", timeout=10
            ) as resp:
                if resp.status != 200:
                    return None
                data = await resp.json()
        lyrics = (data or {}).get("lyrics")
        if not lyrics:
            return None
        return {
            "title": title,
            "artist": artist,
            "lyrics": lyrics,
            "synced": None,
            "art": None,
            "source": "Lyrics.ovh",
        }
    except Exception:
        log.debug("Lyrics.ovh lookup failed for %s", query, exc_info=True)
        return None


async def _normalize_query_with_ai(query):
    """Ask Gemini to correct spelling/artist and return a clean 'Artist - Title'."""
    if not ai_model:
        return None
    try:
        prompt = (
            "You normalize song search queries. Given a possibly misspelled or messy "
            "song reference, reply with ONLY the corrected 'Artist - Title' string, "
            "nothing else. If unsure, give your best guess.\n\nQuery: " + query
        )
        resp = await asyncio.to_thread(ai_model.generate_content, prompt)
        text = (resp.text or "").strip().splitlines()[0].strip()
        return text or None
    except Exception:
        log.debug("AI query normalization failed", exc_info=True)
        return None


async def fetch_lyrics(song_name):
    """Return {title, artist, lyrics, synced, art, source} or None. Cached."""
    if song_name in LYRICS_CACHE:
        return LYRICS_CACHE[song_name]

    providers = (_lyrics_from_lrclib, _lyrics_from_genius, _lyrics_from_ovh)
    for provider in providers:
        payload = await provider(song_name)
        if payload and payload.get("lyrics"):
            LYRICS_CACHE[song_name] = payload
            return payload

    # AI-assisted retry: normalize the query, then try providers once more.
    normalized = await _normalize_query_with_ai(song_name)
    if normalized and normalized.lower() != song_name.lower():
        for provider in providers:
            payload = await provider(normalized)
            if payload and payload.get("lyrics"):
                LYRICS_CACHE[song_name] = payload
                return payload

    LYRICS_CACHE[song_name] = None
    return None


# =========================
# PERSISTENT NOW-PLAYING PANEL
# =========================
class MusicPanel(discord.ui.View):
    def __init__(self):
        super().__init__(timeout=None)

    async def _check_dj(self, interaction):
        """Return True if user may control playback (respects requester-only + DJ)."""
        gid = interaction.guild.id
        settings = get_dj_settings(gid)
        if is_dj(interaction.user):
            return True
        if settings["requester_only_skip"] and last_requester.get(gid) == interaction.user.id:
            return True
        if not settings["requester_only_skip"]:
            return True
        await interaction.response.send_message(
            "❌ Only the requester or a DJ can do that.", ephemeral=True
        )
        return False

    @discord.ui.button(label="⏮", style=discord.ButtonStyle.gray, custom_id="panel:previous", row=0)
    async def previous(self, interaction: discord.Interaction, button):
        if not await self._check_dj(interaction):
            return
        await _play_previous(interaction.guild, interaction.channel)
        await interaction.response.send_message("⏮ Playing previous track", ephemeral=True)

    @discord.ui.button(label="⏪ 10", style=discord.ButtonStyle.gray, custom_id="panel:rewind", row=0)
    async def rewind(self, interaction: discord.Interaction, button):
        if not now_playing.get(interaction.guild.id):
            return await interaction.response.send_message("Nothing is playing.", ephemeral=True)
        target = max(0, current_elapsed(interaction.guild.id) - 10)
        try:
            await do_seek(interaction.guild, interaction.channel, target)
        except MusicError as e:
            return await interaction.response.send_message(f"❌ {e}", ephemeral=True)
        await interaction.response.send_message(f"⏪ {format_duration(target)}", ephemeral=True)

    @discord.ui.button(label="⏸", style=discord.ButtonStyle.gray, custom_id="panel:pause", row=0)
    async def pause(self, interaction: discord.Interaction, button):
        vc = interaction.guild.voice_client
        if vc and vc.is_playing():
            vc.pause()
        await interaction.response.send_message("⏸ Paused", ephemeral=True)

    @discord.ui.button(label="▶", style=discord.ButtonStyle.green, custom_id="panel:resume", row=0)
    async def resume(self, interaction: discord.Interaction, button):
        vc = interaction.guild.voice_client
        if vc and vc.is_paused():
            vc.resume()
        await interaction.response.send_message("▶ Resumed", ephemeral=True)

    @discord.ui.button(label="⏩ 10", style=discord.ButtonStyle.gray, custom_id="panel:forward", row=0)
    async def forward(self, interaction: discord.Interaction, button):
        if not now_playing.get(interaction.guild.id):
            return await interaction.response.send_message("Nothing is playing.", ephemeral=True)
        target = current_elapsed(interaction.guild.id) + 10
        try:
            target = await do_seek(interaction.guild, interaction.channel, target)
        except MusicError as e:
            return await interaction.response.send_message(f"❌ {e}", ephemeral=True)
        await interaction.response.send_message(f"⏩ {format_duration(target)}", ephemeral=True)

    @discord.ui.button(label="⏭", style=discord.ButtonStyle.blurple, custom_id="panel:skip", row=1)
    async def skip(self, interaction: discord.Interaction, button):
        if not await self._check_dj(interaction):
            return
        vc = interaction.guild.voice_client
        if vc and (vc.is_playing() or vc.is_paused()):
            vc.stop()
        await interaction.response.send_message("⏭ Skipped", ephemeral=True)

    @discord.ui.button(label="⏹", style=discord.ButtonStyle.red, custom_id="panel:stop", row=1)
    async def stop(self, interaction: discord.Interaction, button):
        if not await self._check_dj(interaction):
            return
        vc = interaction.guild.voice_client
        if vc:
            get_queue(interaction.guild.id).clear()
            save_guild_queue(interaction.guild.id)
            vc.stop()
        await interaction.response.send_message("⏹ Stopped", ephemeral=True)

    @discord.ui.button(label="🎚 Seek", style=discord.ButtonStyle.gray, custom_id="panel:seekmodal", row=1)
    async def seek_modal(self, interaction: discord.Interaction, button):
        if not now_playing.get(interaction.guild.id):
            return await interaction.response.send_message("Nothing is playing.", ephemeral=True)
        await interaction.response.send_modal(SeekModal())

    @discord.ui.button(label="🔀", style=discord.ButtonStyle.gray, custom_id="panel:shuffle", row=1)
    async def shuffle(self, interaction: discord.Interaction, button):
        random.shuffle(get_queue(interaction.guild.id))
        await interaction.response.send_message("🔀 Queue shuffled", ephemeral=True)

    @discord.ui.button(label="🔁", style=discord.ButtonStyle.gray, custom_id="panel:repeat", row=1)
    async def repeat(self, interaction: discord.Interaction, button):
        gid = interaction.guild.id
        order = ["off", "song", "queue"]
        current = repeat_mode.get(gid, "off")
        repeat_mode[gid] = order[(order.index(current) + 1) % len(order)]
        await interaction.response.send_message(f"🔁 Repeat: {repeat_mode[gid]}", ephemeral=True)

    @discord.ui.button(label="❤️", style=discord.ButtonStyle.red, custom_id="panel:favorite", row=2)
    async def favorite(self, interaction: discord.Interaction, button):
        song = now_playing.get(interaction.guild.id)
        if not song:
            return await interaction.response.send_message("Nothing is playing.", ephemeral=True)
        cur.execute(
            "INSERT OR IGNORE INTO user_favorites (user_id, url, title) VALUES (?, ?, ?)",
            (interaction.user.id, song["webpage_url"], song["title"]),
        )
        conn.commit()
        await interaction.response.send_message("❤️ Added to your favorites", ephemeral=True)

    @discord.ui.button(label="⬇", style=discord.ButtonStyle.gray, custom_id="panel:download", row=2)
    async def download(self, interaction: discord.Interaction, button):
        song = now_playing.get(interaction.guild.id)
        if not song:
            return await interaction.response.send_message("Nothing is playing.", ephemeral=True)
        await interaction.response.send_message("⏳ Preparing download…", ephemeral=True)
        await _do_download(interaction, song)

    @discord.ui.button(label="🎤 Lyrics", style=discord.ButtonStyle.gray, custom_id="panel:lyrics", row=2)
    async def lyrics_btn(self, interaction: discord.Interaction, button):
        song = now_playing.get(interaction.guild.id)
        if not song:
            return await interaction.response.send_message("Nothing is playing.", ephemeral=True)
        await interaction.response.defer(ephemeral=True)
        try:
            data = await fetch_lyrics(song["title"])
        except Exception as e:
            return await interaction.followup.send(f"❌ Lyrics error: {e}", ephemeral=True)
        if not data:
            return await interaction.followup.send("❌ Lyrics not found.", ephemeral=True)
        text = data["lyrics"][:3900]
        embed = discord.Embed(title=data["title"], description=f"```{text}```",
                              color=discord.Color.orange())
        embed.set_author(name=data["artist"])
        await interaction.followup.send(embed=embed, ephemeral=True)

    @discord.ui.button(label="🔍 Wrong Song", style=discord.ButtonStyle.gray,
                       custom_id="panel:wrongsong", row=2)
    async def wrong_song(self, interaction: discord.Interaction, button):
        """Reuse the cached 6 search results — never re-searches YouTube."""
        results = search_results_cache.get(interaction.guild.id)
        if not results or len(results) < 2:
            return await interaction.response.send_message(
                "No alternate results cached for the current song.", ephemeral=True
            )
        view = SearchView(results, interaction.user.id, mode="replace")
        await interaction.response.send_message(
            "🔍 Pick the correct song — it will replace what's playing:",
            view=view, ephemeral=True,
        )

    @discord.ui.button(label="📜 Queue", style=discord.ButtonStyle.gray, custom_id="panel:queue", row=2)
    async def queue_btn(self, interaction: discord.Interaction, button):
        view = QueueView(interaction.guild.id)
        await interaction.response.send_message(embed=view.render(), view=view, ephemeral=True)

    @discord.ui.button(label="🔉", style=discord.ButtonStyle.gray, custom_id="panel:voldown", row=3)
    async def vol_down(self, interaction: discord.Interaction, button):
        vol = set_volume(interaction.guild.id, get_volume(interaction.guild.id) - 0.1)
        vc = interaction.guild.voice_client
        if vc and vc.source:
            vc.source.volume = vol
        await interaction.response.send_message(f"🔉 {int(vol * 100)}%", ephemeral=True)

    @discord.ui.button(label="🔊", style=discord.ButtonStyle.gray, custom_id="panel:volup", row=3)
    async def vol_up(self, interaction: discord.Interaction, button):
        vol = set_volume(interaction.guild.id, get_volume(interaction.guild.id) + 0.1)
        vc = interaction.guild.voice_client
        if vc and vc.source:
            vc.source.volume = vol
        await interaction.response.send_message(f"🔊 {int(vol * 100)}%", ephemeral=True)

    @discord.ui.button(label="⏪ 30", style=discord.ButtonStyle.gray, custom_id="panel:rewind30", row=3)
    async def rewind30(self, interaction: discord.Interaction, button):
        if not now_playing.get(interaction.guild.id):
            return await interaction.response.send_message("Nothing is playing.", ephemeral=True)
        target = max(0, current_elapsed(interaction.guild.id) - 30)
        try:
            await do_seek(interaction.guild, interaction.channel, target)
        except MusicError as e:
            return await interaction.response.send_message(f"❌ {e}", ephemeral=True)
        await interaction.response.send_message(f"⏪ {format_duration(target)}", ephemeral=True)

    @discord.ui.button(label="⏩ 30", style=discord.ButtonStyle.gray, custom_id="panel:forward30", row=3)
    async def forward30(self, interaction: discord.Interaction, button):
        if not now_playing.get(interaction.guild.id):
            return await interaction.response.send_message("Nothing is playing.", ephemeral=True)
        target = current_elapsed(interaction.guild.id) + 30
        try:
            target = await do_seek(interaction.guild, interaction.channel, target)
        except MusicError as e:
            return await interaction.response.send_message(f"❌ {e}", ephemeral=True)
        await interaction.response.send_message(f"⏩ {format_duration(target)}", ephemeral=True)

    @discord.ui.button(label="⚙ Filters", style=discord.ButtonStyle.blurple,
                       custom_id="panel:filters", row=3)
    async def filters_btn(self, interaction: discord.Interaction, button):
        await interaction.response.send_message(
            "⚙ **Filters** — pick a preset or reset. Position is preserved.",
            view=FilterPanelView(), ephemeral=True,
        )


# =========================
# FILTER PANEL (⚙ button)
# =========================
class FilterPanelView(discord.ui.View):
    """Ephemeral filter picker used by the player's ⚙ Filters button."""

    def __init__(self):
        super().__init__(timeout=120)

    @discord.ui.select(
        placeholder="Toggle a filter / EQ preset…",
        options=[
            discord.SelectOption(label="Bass Boost", value="bassboost", emoji="🔊"),
            discord.SelectOption(label="Treble", value="treble", emoji="🎻"),
            discord.SelectOption(label="Echo", value="echo", emoji="🎧"),
            discord.SelectOption(label="Karaoke", value="karaoke", emoji="🎤"),
            discord.SelectOption(label="8D Audio", value="8d", emoji="🌀"),
            discord.SelectOption(label="Nightcore", value="nightcore", emoji="⚡"),
            discord.SelectOption(label="Vaporwave", value="vaporwave", emoji="🌴"),
            discord.SelectOption(label="Normalize", value="normalize", emoji="📈"),
            discord.SelectOption(label="EQ: Rock", value="eq:rock"),
            discord.SelectOption(label="EQ: Pop", value="eq:pop"),
            discord.SelectOption(label="EQ: Bass", value="eq:bass"),
            discord.SelectOption(label="EQ: EDM", value="eq:edm"),
            discord.SelectOption(label="EQ: Jazz", value="eq:jazz"),
            discord.SelectOption(label="EQ: Classical", value="eq:classical"),
            discord.SelectOption(label="Reset All Filters", value="reset", emoji="🧹"),
        ],
    )
    async def choose(self, interaction: discord.Interaction, select: discord.ui.Select):
        gid = interaction.guild.id
        value = select.values[0]
        if not now_playing.get(gid):
            return await interaction.response.send_message("Nothing is playing.", ephemeral=True)

        if value == "reset":
            reset_filters(gid)
            label = "🧹 Filters cleared"
        elif value == "normalize":
            f = audio_filters.setdefault(gid, {})
            f["normalize"] = not f.get("normalize")
            label = f"📈 Normalization: {'on' if f['normalize'] else 'off'}"
        elif value == "nightcore":
            set_filter(gid, speed=1.25, pitch=1.25)
            label = "⚡ Nightcore enabled"
        elif value == "vaporwave":
            set_filter(gid, speed=0.8, pitch=0.8)
            label = "🌴 Vaporwave enabled"
        elif value.startswith("eq:"):
            preset = value.split(":", 1)[1]
            set_filter(gid, eq=EQ_PRESETS[preset])
            label = f"🎚 EQ preset: {preset}"
        else:
            # Simple toggle filters (bassboost/treble/echo/karaoke/8d).
            f = audio_filters.setdefault(gid, {})
            f[value] = not f.get(value)
            label = f"✅ {value}: {'on' if f[value] else 'off'}"

        await _restart_current_guild(interaction.guild)
        await interaction.response.send_message(f"{label} — position preserved.", ephemeral=True)


# =========================
# PREVIOUS-TRACK HELPER
# =========================
async def _play_previous(guild, channel):
    """Replay the previous track from history."""
    gid = guild.id
    hist = song_history.get(gid, [])
    # hist[-1] is the current song; the previous is hist[-2].
    if len(hist) < 2:
        return await channel.send("No previous track in history.")
    prev = hist[-2]
    get_queue(gid).insert(0, dict(prev))
    now_playing[gid] = None  # prevent repeat mode from re-adding the current song
    await transition_now(channel, guild)


# =========================
# SEEK CORE (single source of truth — used by !seek, buttons, and the modal)
# =========================
def current_elapsed(guild_id):
    """Seconds elapsed in the currently playing track."""
    return max(0, int(time.time() - song_start_times.get(guild_id, time.time())))


def parse_timestamp(text):
    """
    Parse "1:35", "1:02:03" or "95" into seconds. Returns None if invalid.
    """
    text = (text or "").strip()
    if not text:
        return None
    if ":" in text:
        parts = text.split(":")
        try:
            nums = [int(p) for p in parts]
        except ValueError:
            return None
        if any(n < 0 for n in nums):
            return None
        if len(parts) == 2:
            m, s = nums
            return m * 60 + s
        if len(parts) == 3:
            h, m, s = nums
            return h * 3600 + m * 60 + s
        return None
    if text.isdigit():
        return int(text)
    return None


async def do_seek(guild, channel, seconds):
    """
    Seek the current track to `seconds`. Reinserts the song at the front with a
    seek offset and restarts playback via FFmpeg -ss. Returns the clamped target.
    Raises MusicError if nothing is playing.
    """
    gid = guild.id
    vc = guild.voice_client
    song = now_playing.get(gid)
    if not vc or not song or not (vc.is_playing() or vc.is_paused()):
        raise MusicError("Nothing is playing.")

    seconds = max(0, int(seconds))
    duration = song.get("duration")
    if duration:
        seconds = min(seconds, max(0, int(duration) - 1))

    np_channels[gid] = channel
    seek_positions[gid] = seconds
    get_queue(gid).insert(0, song)
    now_playing[gid] = None  # prevent repeat mode from double-adding it
    vc.stop()  # after() -> play_next picks up seek_positions
    return seconds


class SeekModal(discord.ui.Modal, title="Seek to position"):
    position = discord.ui.TextInput(
        label="Timestamp",
        placeholder="e.g. 1:35 or 95",
        required=True,
        max_length=10,
    )

    async def on_submit(self, interaction: discord.Interaction):
        secs = parse_timestamp(str(self.position))
        if secs is None:
            return await interaction.response.send_message(
                "❌ Invalid timestamp. Use `1:35` or `95`.", ephemeral=True
            )
        song = now_playing.get(interaction.guild.id)
        if song and song.get("duration") and secs > int(song["duration"]):
            return await interaction.response.send_message(
                f"❌ Song is only {format_duration(song['duration'])} long.", ephemeral=True
            )
        try:
            target = await do_seek(interaction.guild, interaction.channel, secs)
        except MusicError as e:
            return await interaction.response.send_message(f"❌ {e}", ephemeral=True)
        await interaction.response.send_message(
            f"⏩ Seeked to **{format_duration(target)}**", ephemeral=True
        )


# =========================
# POST-SELECTION ACTION VIEW
# =========================
class SongActionView(discord.ui.View):
    def __init__(self, song, requester_id):
        super().__init__(timeout=60)
        self.song = song
        self.requester_id = requester_id

    @discord.ui.button(label="⬇️ Download", style=discord.ButtonStyle.blurple)
    async def download(self, interaction: discord.Interaction, button):
        if interaction.user.id != self.requester_id:
            return await interaction.response.send_message("This isn't yours.", ephemeral=True)
        await interaction.response.send_message("⏳ Preparing download…", ephemeral=True)
        await _do_download(interaction, self.song)

    @discord.ui.button(label="🔗 Link", style=discord.ButtonStyle.gray)
    async def link(self, interaction: discord.Interaction, button):
        await interaction.response.send_message(
            self.song.get("webpage_url", "No URL available"), ephemeral=True
        )


# =========================
# SEARCH RESULTS UI
# mode="append"  -> add to end of queue
# mode="next"    -> insert at front
# mode="replace" -> replace currently playing (Wrong Song)
# =========================
class SearchView(discord.ui.View):
    def __init__(self, results, requester_id, mode="append"):
        super().__init__(timeout=60)
        self.results = results
        self.requester_id = requester_id
        self.mode = mode

        options = [
            discord.SelectOption(
                label=r["title"][:100],
                description=(format_duration(r.get("duration")) if r.get("duration") else None),
                value=str(i),
            )
            for i, r in enumerate(results)
        ]
        self.song_select.options = options

        if mode in ("next", "replace"):
            self.remove_item(self.add_all_btn)

    @discord.ui.select(placeholder="Choose a song…")
    async def song_select(self, interaction: discord.Interaction, select: discord.ui.Select):
        if interaction.user.id != self.requester_id:
            return await interaction.response.send_message("This search isn't yours.", ephemeral=True)

        song = self.results[int(select.values[0])]
        gid = interaction.guild.id

        if self.mode == "replace":
            # Wrong Song: stop current, play the chosen alt immediately.
            get_queue(gid).insert(0, song)
            now_playing[gid] = None
            await interaction.response.edit_message(
                content=f"🔁 Replacing with **{song['title']}**", view=None
            )
            await transition_now(interaction.channel, interaction.guild)
            return

        if self.mode == "next":
            get_queue(gid).insert(0, song)
            status = f"⏩ Playing next: **{song['title']}**"
        else:
            get_queue(gid).append(song)
            status = f"➕ **{song['title']}** added — position #{len(get_queue(gid))}"

        await interaction.response.edit_message(
            content=status, embed=None, view=SongActionView(song, interaction.user.id)
        )
        await start_if_idle(interaction.channel, interaction.guild)

    @discord.ui.button(label="➕ Add All to Queue", style=discord.ButtonStyle.green)
    async def add_all_btn(self, interaction: discord.Interaction, button):
        if interaction.user.id != self.requester_id:
            return await interaction.response.send_message("This search isn't yours.", ephemeral=True)
        for song in self.results:
            get_queue(interaction.guild.id).append(song)
        await interaction.response.edit_message(
            content=f"➕ Added all **{len(self.results)}** results to queue", embed=None, view=None
        )
        await start_if_idle(interaction.channel, interaction.guild)


# =========================
# QUEUE PAGINATION UI
# =========================
class QueueView(discord.ui.View):
    PAGE_SIZE = 5

    def __init__(self, guild_id):
        super().__init__(timeout=120)
        self.guild_id = guild_id
        self.page = 0

    def max_page(self):
        total = len(get_queue(self.guild_id))
        return max(0, (total - 1) // self.PAGE_SIZE)

    def render(self):
        q = get_queue(self.guild_id)
        start = self.page * self.PAGE_SIZE
        chunk = q[start:start + self.PAGE_SIZE]
        cur_song = now_playing.get(self.guild_id)
        header = f"**▶ Now:** {cur_song['title']}\n\n" if cur_song else ""
        lines = "\n".join(
            f"`{start + i + 1}.` {s['title']} `{format_duration(s.get('duration'))}`"
            for i, s in enumerate(chunk)
        ) or "Queue is empty"
        embed = discord.Embed(
            title=f"📜 Queue (page {self.page + 1}/{self.max_page() + 1})",
            description=header + lines,
            color=discord.Color.purple(),
        )
        total_dur = sum(s.get("duration") or 0 for s in q)
        embed.set_footer(text=f"{len(q)} track(s) • {format_duration(total_dur)} total")
        return embed

    @discord.ui.button(label="⬅ Prev", style=discord.ButtonStyle.gray)
    async def prev(self, interaction: discord.Interaction, button):
        self.page = max(0, self.page - 1)
        await interaction.response.edit_message(embed=self.render(), view=self)

    @discord.ui.button(label="Next ➡", style=discord.ButtonStyle.gray)
    async def next(self, interaction: discord.Interaction, button):
        self.page = min(self.max_page(), self.page + 1)
        await interaction.response.edit_message(embed=self.render(), view=self)


# =========================
# VOLUME CONTROL UI
# =========================
class VolumeView(discord.ui.View):
    def __init__(self):
        super().__init__(timeout=120)

    def _apply(self, guild, vol):
        vol = set_volume(guild.id, vol)
        vc = guild.voice_client
        if vc and vc.source:
            vc.source.volume = vol
        return vol

    @discord.ui.button(label="-10%", style=discord.ButtonStyle.gray)
    async def down(self, interaction: discord.Interaction, button):
        vol = self._apply(interaction.guild, get_volume(interaction.guild.id) - 0.1)
        await interaction.response.send_message(f"🔉 {int(vol * 100)}%", ephemeral=True)

    @discord.ui.button(label="+10%", style=discord.ButtonStyle.gray)
    async def up(self, interaction: discord.Interaction, button):
        vol = self._apply(interaction.guild, get_volume(interaction.guild.id) + 0.1)
        await interaction.response.send_message(f"🔊 {int(vol * 100)}%", ephemeral=True)

    @discord.ui.button(label="Mute", style=discord.ButtonStyle.red)
    async def mute(self, interaction: discord.Interaction, button):
        self._apply(interaction.guild, 0)
        await interaction.response.send_message("🔇 Muted", ephemeral=True)

    @discord.ui.button(label="Reset (50%)", style=discord.ButtonStyle.green)
    async def reset(self, interaction: discord.Interaction, button):
        self._apply(interaction.guild, 0.5)
        await interaction.response.send_message("🔊 50%", ephemeral=True)


# =========================
# HELP UI (professional, categorized, per-command detail)
# Each entry: (command signature, aliases list, description, example)
# =========================
HELP_CATEGORIES = {
    "🎵 Music": [
        ("!play <song/url>", ["/play"], "Instantly plays the best result (or a URL/Spotify link).", "!play believer"),
        ("!search <song>", ["/search"], "Search and pick from a dropdown — never auto-plays.", "!search believer"),
        ("!playnext <song>", ["!pn"], "Queue a song to play right after the current one.", "!playnext bohemian rhapsody"),
        ("!previous", [], "Replay the previous track from history.", "!previous"),
        ("!seek <time>", [], "Jump to a position (seconds or M:SS).", "!seek 1:30"),
        ("!skip / !pause / !resume / !stop", [], "Standard playback controls.", "!skip"),
        ("!leave", ["!disconnect"], "Leave voice and clear the queue.", "!leave"),
        ("!nowplaying", ["!np"], "Show the live now-playing panel.", "!np"),
        ("!volume <0-200>", [], "Set playback volume.", "!volume 80"),
        ("!loop <song|queue|off>", [], "Set repeat mode.", "!loop queue"),
        ("!autoplay [on|off]", [], "Auto-queue related tracks when empty.", "!autoplay on"),
        ("!download [song]", [], "Download the current or a searched song.", "!download"),
    ],
    "📜 Queue": [
        ("!queue", [], "Show the paginated queue.", "!queue"),
        ("!queue search <keyword>", [], "Find tracks within the queue.", "!queue search drake"),
        ("!jump <#>", [], "Jump directly to a queued position.", "!jump 4"),
        ("!move <from> <to>", [], "Move a track to a new position.", "!move 5 1"),
        ("!swap <a> <b>", [], "Swap two tracks.", "!swap 2 6"),
        ("!remove <#>", [], "Remove a track by position.", "!remove 3"),
        ("!shuffle", [], "Shuffle the queue.", "!shuffle"),
        ("!dedupe", [], "Remove duplicate tracks.", "!dedupe"),
        ("!clearqueue", ["!cq"], "Clear the queue (current keeps playing).", "!cq"),
        ("!insert <#> <song>", [], "Insert a searched song at a position.", "!insert 2 believer"),
        ("!undo", [], "Undo the last queue change.", "!undo"),
        ("!snapshot <name>", [], "Save the queue under a name.", "!snapshot chill"),
        ("!restore <name>", [], "Restore a saved snapshot.", "!restore chill"),
        ("!history / !recent", [], "Show recently played tracks.", "!history"),
        ("!clearhistory", [], "Clear playback history.", "!clearhistory"),
    ],
    "🎼 Playlists": [
        ("!playlist create <name>", ["save"], "Save the current queue as a playlist.", "!playlist create Chill"),
        ("!playlist add <name> <song>", [], "Search & add a song (no queue needed).", "!playlist add Favorites believer"),
        ("!playlist remove <name> <#>", [], "Remove a track from a playlist.", "!playlist remove Favorites 2"),
        ("!playlist show <name>", [], "List a playlist's tracks.", "!playlist show Chill"),
        ("!playlist play <name>", [], "Replace the queue and play a playlist.", "!playlist play Chill"),
        ("!playlist append <name>", [], "Add a playlist to the end of the queue.", "!playlist append Chill"),
        ("!playlist shuffle <name>", [], "Shuffle a stored playlist.", "!playlist shuffle Chill"),
        ("!playlist rename <old> <new>", [], "Rename a playlist.", "!playlist rename Chill Relax"),
        ("!playlist delete/clear <name>", [], "Delete a playlist, or empty it.", "!playlist delete Chill"),
        ("!playlist export/import <name>", [], "Export/import a playlist as JSON.", "!playlist export Chill"),
        ("!playlist list", [], "List all saved playlists.", "!playlist list"),
    ],
    "🎚 Filters": [
        ("!bassboost / !treble / !echo / !karaoke", [], "Toggle audio effects (keeps position).", "!bassboost"),
        ("!eightd", [], "8D rotating spatial audio.", "!eightd"),
        ("!nightcore / !vaporwave", [], "Speed+pitch presets.", "!nightcore"),
        ("!speed <0.5-2>", [], "Change playback speed.", "!speed 1.25"),
        ("!pitch <0.5-2>", [], "Change pitch.", "!pitch 0.9"),
        ("!eq <preset>", [], "Equalizer: rock/pop/bass/edm/jazz/classical/flat.", "!eq rock"),
        ("!customeq <string>", [], "Apply a custom ffmpeg EQ string.", "!customeq equalizer=f=1000:t=q:w=1:g=5"),
        ("!normalize", [], "Toggle loudness normalization.", "!normalize"),
        ("!resetfilters", [], "Clear all filters.", "!resetfilters"),
    ],
    "❤️ Favorites": [
        ("!favorite", [], "Save the current song.", "!favorite"),
        ("!favorite remove <#>", [], "Remove a favorite.", "!favorite remove 2"),
        ("!favorites", [], "List your favorites.", "!favorites"),
        ("!favorites clear", [], "Remove all favorites.", "!favorites clear"),
        ("!favorites export/import", [], "Export/import favorites as JSON.", "!favorites export"),
    ],
    "🎤 Lyrics": [
        ("!lyrics <song>", [], "Cached Genius lyrics.", "!lyrics believer"),
        ("!translatelyrics <lang> | <song>", [], "AI-translated lyrics.", "!translatelyrics spanish | believer"),
        ("!explainlyrics <song>", [], "Themes/meaning summary (no quoting).", "!explainlyrics believer"),
    ],
    "🤖 AI": [
        ("!ai <prompt>", ["!chat", "!ask"], "General Gemini chat.", "!ai write a haiku"),
        ("!summarize <text/reply>", [], "Summarize text.", "!summarize <reply>"),
        ("!translate <lang> | <text>", [], "Translate text.", "!translate french | hello"),
        ("!code <request>", [], "Generate code.", "!code python quicksort"),
        ("!review <code/reply>", [], "Review code.", "!review <reply>"),
        ("!explain <topic>", [], "Explain a topic.", "!explain recursion"),
        ("!recommend <mood>", [], "AI song suggestions.", "!recommend rainy day"),
    ],
    "📊 Statistics": [
        ("!mostplayed", [], "Top songs in this server.", "!mostplayed"),
        ("!topartists", ["!mostplayedartists"], "Most played artists.", "!topartists"),
        ("!toplisteners", [], "Most active listeners.", "!toplisteners"),
        ("!listeningtime", ["!listentime"], "Listening time leaderboard.", "!listeningtime"),
        ("!recent", [], "Recently played tracks.", "!recent"),
        ("!stats [member]", [], "A member's play count & listening time.", "!stats @user"),
    ],
    "👤 Profile": [
        ("!profile [member]", ["!me"], "Listening profile: hours, top artists, badges.", "!profile"),
        ("!achievements [member]", ["!badges"], "Unlocked achievements & progress.", "!achievements"),
    ],
    "🛡 DJ": [
        ("!voteskip", ["!vs"], "Vote to skip (>50% of listeners).", "!voteskip"),
        ("!djrole <@role>", [], "Set the DJ role (Manage Server).", "!djrole @DJ"),
        ("!queuelock <on|off>", [], "Lock the queue to DJs.", "!queuelock on"),
        ("!requesterskip <on|off>", [], "Only requester/DJ can skip.", "!requesterskip on"),
    ],
    "⚙ Utility": [
        ("!ping", [], "Show bot latency.", "!ping"),
        ("!avatar [member]", [], "Show an avatar.", "!avatar @user"),
        ("!serverinfo", [], "Server information.", "!serverinfo"),
        ("!github <user>", [], "GitHub profile lookup.", "!github torvalds"),
        ("!weather <city>", [], "Current weather.", "!weather tokyo"),
        ("!volumeui", [], "Interactive volume controls.", "!volumeui"),
    ],
    "🔨 Moderation": [
        ("!kick <member> [reason]", [], "Kick a member.", "!kick @user spam"),
        ("!ban <member> [reason]", [], "Ban a member.", "!ban @user"),
        ("!clear <amount>", [], "Bulk-delete messages.", "!clear 20"),
        ("!warn <member> [reason]", [], "Warn a member.", "!warn @user rule 3"),
    ],
    "🎉 Fun & System": [
        ("!coinflip / !dice", [], "Flip a coin / roll a die.", "!dice"),
        ("!eightball <question>", [], "Magic 8-ball.", "!eightball will it rain?"),
        ("!maintenance <on|off>", [], "Owner-only maintenance mode.", "!maintenance on"),
        ("!restart", [], "Owner-only restart.", "!restart"),
    ],
}

HELP_FOOTER_BANNER = (
    "━━━━━━━━━━━━━━━━━━━━\n"
    "Made with ❤️ by **Aayush Joshi** • Discord Music Bot\n"
    "━━━━━━━━━━━━━━━━━━━━"
)


def _total_command_count():
    return len(set(bot.walk_commands()))


def _format_uptime():
    secs = int(time.time() - BOT_START_TIME)
    d, rem = divmod(secs, 86400)
    h, rem = divmod(rem, 3600)
    m, s = divmod(rem, 60)
    parts = []
    if d:
        parts.append(f"{d}d")
    if h:
        parts.append(f"{h}h")
    if m:
        parts.append(f"{m}m")
    parts.append(f"{s}s")
    return " ".join(parts)


def _apply_help_footer(embed):
    embed.add_field(name="​", value=HELP_FOOTER_BANNER, inline=False)
    gemini = GEMINI_MODEL if ai_model else "disabled"
    embed.set_footer(
        text=(
            f"v{BOT_VERSION} • Python {platform.python_version()} • "
            f"discord.py {discord.__version__} • Gemini {gemini} • "
            f"{round(bot.latency * 1000)}ms • up {_format_uptime()} • "
            f"{_total_command_count()} commands"
        )
    )
    return embed


def build_help_overview():
    embed = discord.Embed(
        title="🎧 Discord Music Bot — Help",
        description=(
            "A premium-grade music bot with instant play, live controls, "
            "playlists, filters, lyrics, AI and more.\n\n"
            "**Select a category below** to see every command, its aliases, "
            "a description, and an example."
        ),
        color=discord.Color.from_rgb(88, 101, 242),
    )
    embed.add_field(
        name="Categories",
        value="  ".join(HELP_CATEGORIES.keys()),
        inline=False,
    )
    return _apply_help_footer(embed)


def build_help_category(name):
    embed = discord.Embed(title=f"📖 {name} Commands", color=discord.Color.gold())
    for sig, aliases, desc, example in HELP_CATEGORIES[name]:
        alias_txt = f"  *(aliases: {', '.join(aliases)})*" if aliases else ""
        embed.add_field(
            name=f"`{sig}`{alias_txt}",
            value=f"{desc}\n> Example: `{example}`",
            inline=False,
        )
    return _apply_help_footer(embed)


def search_help(term):
    """Return an embed of commands matching `term` across all categories."""
    term = term.lower().strip()
    hits = []
    for cat, entries in HELP_CATEGORIES.items():
        for sig, aliases, desc, example in entries:
            haystack = f"{sig} {' '.join(aliases)} {desc}".lower()
            if term in haystack:
                hits.append((cat, sig, desc, example))
    embed = discord.Embed(
        title=f"🔍 Help search — “{term}”",
        color=discord.Color.gold(),
        description=f"{len(hits)} match(es)." if hits else "No matches.",
    )
    for cat, sig, desc, example in hits[:20]:
        embed.add_field(name=f"`{sig}`", value=f"{desc}\n> `{example}` • {cat}", inline=False)
    return _apply_help_footer(embed)


class HelpSearchModal(discord.ui.Modal, title="Search commands"):
    term = discord.ui.TextInput(label="Keyword", placeholder="e.g. playlist, seek, bass")

    async def on_submit(self, interaction: discord.Interaction):
        await interaction.response.edit_message(embed=search_help(str(self.term)), view=HelpView())


class HelpView(discord.ui.View):
    """Interactive help: category dropdown + Home/Search buttons."""

    def __init__(self):
        super().__init__(timeout=180)

    @discord.ui.select(
        placeholder="📚 Choose a category…",
        options=[discord.SelectOption(label=k, value=k) for k in HELP_CATEGORIES],
    )
    async def menu(self, interaction: discord.Interaction, select: discord.ui.Select):
        await interaction.response.edit_message(
            embed=build_help_category(select.values[0]), view=self
        )

    @discord.ui.button(label="🏠 Home", style=discord.ButtonStyle.gray, row=1)
    async def home(self, interaction: discord.Interaction, button):
        await interaction.response.edit_message(embed=build_help_overview(), view=self)

    @discord.ui.button(label="🔍 Search", style=discord.ButtonStyle.blurple, row=1)
    async def search_btn(self, interaction: discord.Interaction, button):
        await interaction.response.send_modal(HelpSearchModal())


# =========================
# SHARED PLAY LOGIC (used by !play and /play)
# =========================
async def _do_play(ctx_or_inter, query, *, guild, channel, author, voice_channel, send):
    """
    Instant-play core, shared by prefix and slash commands.
    `send(content=None, embed=None, view=None)` is an async callable adapter.
    """
    gid = guild.id

    # Ensure connected.
    vc = guild.voice_client
    if not vc:
        if not voice_channel:
            return await send("❌ Join a voice channel first!")
        try:
            vc = await voice_channel.connect(reconnect=True, timeout=15)
        except (discord.ClientException, asyncio.TimeoutError) as e:
            return await send(f"❌ Couldn't join voice: {e}")

    # Spotify -> metadata -> YouTube.
    queries = [query]
    if "spotify.com" in query.lower():
        sp = await spotify_to_queries(query)
        if not sp:
            return await send("❌ Couldn't read that Spotify link.")
        queries = sp

    all_results = []
    for q in queries:
        try:
            all_results.extend(await resolve_query(q, limit=6))
        except MusicError as e:
            if len(queries) == 1:
                return await send(f"❌ {e}")

    if not all_results:
        return await send("❌ No results found.")

    last_requester[gid] = author.id

    if is_url(query) and "spotify.com" not in query.lower():
        # Direct URL / playlist -> queue everything.
        for song in all_results:
            get_queue(gid).append(song)
        if len(all_results) == 1:
            await send(f"➕ Added: **{all_results[0]['title']}**")
        else:
            await send(f"➕ Added **{len(all_results)}** tracks")
    else:
        # INSTANT PLAY: take the first result, cache all 6 for "Wrong Song".
        search_results_cache[gid] = all_results[:6]
        first = all_results[0]
        get_queue(gid).append(first)
        await send(f"▶ Playing **{first['title']}** — press 🔍 Wrong Song if this isn't right.")

    await start_if_idle(channel, guild)


# =========================
# MUSIC COMMANDS
# =========================
@bot.hybrid_command(description="Play a song instantly (search, URL, or Spotify link).")
@app_commands.describe(query="Song name, URL, or Spotify link")
@commands.cooldown(1, 3, commands.BucketType.user)
async def play(ctx, *, query: str):
    if queue_locked(ctx.guild.id) and not is_dj(ctx.author):
        return await ctx.send("🔒 The queue is locked — only DJs can add songs.")

    async def send(content=None, embed=None, view=None):
        await ctx.send(content=content, embed=embed, view=view)

    async with ctx.typing():
        await _do_play(
            ctx, query,
            guild=ctx.guild, channel=ctx.channel, author=ctx.author,
            voice_channel=(ctx.author.voice.channel if ctx.author.voice else None),
            send=send,
        )


@bot.hybrid_command(description="Search for a song and pick from a dropdown (no autoplay).")
@app_commands.describe(query="What to search for")
@commands.cooldown(1, 3, commands.BucketType.user)
async def search(ctx, *, query: str):
    """Old !play search behaviour — shows the picker, never auto-plays."""
    vc = await connect_vc(ctx)
    if not vc:
        return
    if "spotify.com" in query.lower():
        sp = await spotify_to_queries(query)
        query = sp[0] if sp else query
    async with ctx.typing():
        try:
            results = await resolve_query(query, limit=6)
        except MusicError as e:
            return await ctx.send(f"❌ {e}")
    if not results:
        return await ctx.send("❌ No results found.")
    search_results_cache[ctx.guild.id] = results
    embed = discord.Embed(
        title="🔎 Search Results",
        description="Pick a song to queue it, or **Add All**.",
        color=discord.Color.blue(),
    )
    await ctx.send(embed=embed, view=SearchView(results, ctx.author.id, mode="append"))


@bot.hybrid_command(name="playnext", aliases=["pn"])
@commands.cooldown(1, 3, commands.BucketType.user)
async def play_next_cmd(ctx, *, query):
    """Queue a song to play immediately after the current track."""
    vc = await connect_vc(ctx)
    if not vc:
        return
    if "spotify.com" in query.lower():
        sp = await spotify_to_queries(query)
        query = sp[0] if sp else query
    async with ctx.typing():
        try:
            results = await resolve_query(query, limit=6)
        except MusicError as e:
            return await ctx.send(f"❌ {e}")
    if not results:
        return await ctx.send("❌ No results found.")
    last_requester[ctx.guild.id] = ctx.author.id
    if is_url(query) or len(results) == 1:
        song = results[0]
        get_queue(ctx.guild.id).insert(0, song)
        await ctx.send(f"⏩ Playing next: **{song['title']}**")
    else:
        search_results_cache[ctx.guild.id] = results
        embed = discord.Embed(title="🔎 Play Next — Select a song",
                              description="Inserted right after the current track.",
                              color=discord.Color.blue())
        return await ctx.send(embed=embed, view=SearchView(results, ctx.author.id, mode="next"))
    await start_if_idle(ctx.channel, ctx.guild)


@bot.hybrid_command()
async def previous(ctx):
    """Replay the previous track."""
    await _play_previous(ctx.guild, ctx.channel)


@bot.hybrid_command()
async def seek(ctx, *, position: str):
    """Jump to a position. Usage: !seek 90  or  !seek 1:30"""
    secs = parse_timestamp(position)
    if secs is None:
        return await ctx.send("❌ Invalid timestamp. Use `!seek 90` or `!seek 1:30`.")
    song = now_playing.get(ctx.guild.id)
    if song and song.get("duration") and secs > int(song["duration"]):
        return await ctx.send(f"❌ Must be within the song's duration ({format_duration(song['duration'])}).")
    try:
        target = await do_seek(ctx.guild, ctx.channel, secs)
    except MusicError as e:
        return await ctx.send(f"❌ {e}")
    await ctx.send(f"⏩ Seeking to **{format_duration(target)}**…")


@bot.hybrid_command()
async def download(ctx, *, query=None):
    """Download the current or a searched song as a file. Files >8 MB get a link."""
    if query:
        async with ctx.typing():
            try:
                results = await resolve_query(query, limit=1)
            except MusicError as e:
                return await ctx.send(f"❌ {e}")
        if not results:
            return await ctx.send("❌ No results found.")
        song = results[0]
    else:
        song = now_playing.get(ctx.guild.id)
        if not song:
            return await ctx.send("❌ Nothing playing and no query. Usage: `!download <song>`")
    msg = await ctx.send(f"⏳ Downloading **{song['title']}**…")
    await _do_download(ctx, song)
    try:
        await msg.delete()
    except discord.HTTPException:
        pass


@bot.hybrid_command()
async def skip(ctx):
    vc = ctx.voice_client
    if vc and (vc.is_playing() or vc.is_paused()):
        vc.stop()
        await ctx.send("⏭ Skipped")
    else:
        await ctx.send("Nothing is playing.")


@bot.hybrid_command()
async def stop(ctx):
    vc = ctx.voice_client
    if vc:
        get_queue(ctx.guild.id).clear()
        vc.stop()
        await ctx.send("⏹ Stopped and cleared queue")
    else:
        await ctx.send("Not connected.")


@bot.hybrid_command(name="leave", aliases=["disconnect"])
async def leave(ctx):
    vc = ctx.voice_client
    if not vc:
        return await ctx.send("Not connected to a voice channel.")
    get_queue(ctx.guild.id).clear()
    now_playing[ctx.guild.id] = None
    np_messages.pop(ctx.guild.id, None)
    await vc.disconnect()
    await ctx.send("👋 Disconnected and cleared the queue.")


@bot.hybrid_command()
async def pause(ctx):
    vc = ctx.voice_client
    if vc and vc.is_playing():
        vc.pause()
        await ctx.send("⏸ Paused")
    else:
        await ctx.send("Nothing is playing.")


@bot.hybrid_command()
async def resume(ctx):
    vc = ctx.voice_client
    if vc and vc.is_paused():
        vc.resume()
        await ctx.send("▶ Resumed")
    else:
        await ctx.send("Nothing is paused.")


@bot.hybrid_group(invoke_without_command=True, description="Show the queue (or use /queue subcommands).")
async def queue(ctx, *, args: str = None):
    """View the queue, or `!queue search <keyword>` to search within it."""
    q = get_queue(ctx.guild.id)
    if args and args.lower().startswith("search "):
        keyword = args[7:].strip().lower()
        matches = [(i + 1, s) for i, s in enumerate(q) if keyword in s["title"].lower()]
        if not matches:
            return await ctx.send(f"🔍 No queued tracks match **{keyword}**.")
        desc = "\n".join(f"`{pos}.` {s['title']}" for pos, s in matches[:20])
        embed = discord.Embed(title=f"🔍 Queue matches for “{keyword}”",
                              description=desc, color=discord.Color.blue())
        return await ctx.send(embed=embed)
    if not q:
        return await ctx.send("Queue is empty.")
    view = QueueView(ctx.guild.id)
    await ctx.send(embed=view.render(), view=view)


@bot.hybrid_command()
async def jump(ctx, position: int):
    """Jump directly to a queued position (drops everything before it)."""
    q = get_queue(ctx.guild.id)
    if not 1 <= position <= len(q):
        return await ctx.send(f"❌ Give a number between 1 and {len(q)}.")
    del q[:position - 1]  # discard tracks before the target
    save_guild_queue(ctx.guild.id)
    target = q[0]
    now_playing[ctx.guild.id] = None  # prevent repeat mode from re-adding current
    await transition_now(ctx.channel, ctx.guild)
    await ctx.send(f"⏩ Jumping to **{target['title']}**")


@bot.hybrid_command()
async def move(ctx, from_pos: int, to_pos: int):
    """Move a track within the queue."""
    q = get_queue(ctx.guild.id)
    if not (1 <= from_pos <= len(q) and 1 <= to_pos <= len(q)):
        return await ctx.send(f"❌ Positions must be between 1 and {len(q)}.")
    _push_undo(ctx.guild.id)
    song = q.pop(from_pos - 1)
    q.insert(to_pos - 1, song)
    save_guild_queue(ctx.guild.id)
    await ctx.send(f"↕ Moved **{song['title']}** to position #{to_pos}")


@bot.hybrid_command()
async def swap(ctx, a: int, b: int):
    """Swap two tracks in the queue."""
    q = get_queue(ctx.guild.id)
    if not (1 <= a <= len(q) and 1 <= b <= len(q)):
        return await ctx.send(f"❌ Positions must be between 1 and {len(q)}.")
    _push_undo(ctx.guild.id)
    q[a - 1], q[b - 1] = q[b - 1], q[a - 1]
    save_guild_queue(ctx.guild.id)
    await ctx.send(f"🔃 Swapped #{a} and #{b}")


@bot.hybrid_command()
async def dedupe(ctx):
    """Remove duplicate songs from the queue (keeps first occurrence)."""
    q = get_queue(ctx.guild.id)
    _push_undo(ctx.guild.id)
    seen = set()
    deduped = []
    for s in q:
        key = s.get("webpage_url") or s.get("title")
        if key not in seen:
            seen.add(key)
            deduped.append(s)
    removed = len(q) - len(deduped)
    queues[ctx.guild.id] = deduped
    save_guild_queue(ctx.guild.id)
    await ctx.send(f"🧹 Removed **{removed}** duplicate(s).")


@bot.hybrid_command()
async def shuffle(ctx):
    q = get_queue(ctx.guild.id)
    if len(q) < 2:
        return await ctx.send("Not enough songs in queue to shuffle.")
    _push_undo(ctx.guild.id)
    random.shuffle(q)
    save_guild_queue(ctx.guild.id)
    await ctx.send("🔀 Queue shuffled")


@bot.hybrid_command()
async def remove(ctx, index: int):
    q = get_queue(ctx.guild.id)
    if not 1 <= index <= len(q):
        return await ctx.send(f"❌ Give a number between 1 and {len(q)}.")
    _push_undo(ctx.guild.id)
    removed = q.pop(index - 1)
    save_guild_queue(ctx.guild.id)
    await ctx.send(f"🗑 Removed: **{removed['title']}**")


@bot.hybrid_command(name="clearqueue", aliases=["cq"])
async def clear_queue(ctx):
    _push_undo(ctx.guild.id)
    get_queue(ctx.guild.id).clear()
    save_guild_queue(ctx.guild.id)
    await ctx.send("🧹 Queue cleared (current song keeps playing).")


@bot.hybrid_command(name="clearhistory")
async def clear_history(ctx):
    song_history[ctx.guild.id] = []
    await ctx.send("🧹 Playback history cleared.")


def _push_undo(guild_id):
    """Save the current queue state so it can be restored with !undo."""
    stack = queue_undo.setdefault(guild_id, [])
    stack.append([dict(s) for s in get_queue(guild_id)])
    if len(stack) > MAX_UNDO:
        stack.pop(0)


@bot.hybrid_command()
async def insert(ctx, position: int, *, query: str):
    """Insert a searched song at a specific queue position (1-based)."""
    q = get_queue(ctx.guild.id)
    pos = max(1, min(position, len(q) + 1))
    async with ctx.typing():
        try:
            results = await resolve_query(query)
        except MusicError as e:
            return await ctx.send(f"❌ {e}")
    if not results:
        return await ctx.send("❌ Nothing found.")
    _push_undo(ctx.guild.id)
    song = results[0]
    last_requester[ctx.guild.id] = ctx.author.id
    q.insert(pos - 1, dict(song))
    save_guild_queue(ctx.guild.id)
    await ctx.send(f"➕ Inserted **{song['title']}** at position **{pos}**.")
    await start_if_idle(ctx.channel, ctx.guild)


@bot.hybrid_command()
async def undo(ctx):
    """Undo the last queue modification (move/swap/remove/insert/dedupe/shuffle/clear)."""
    stack = queue_undo.get(ctx.guild.id)
    if not stack:
        return await ctx.send("Nothing to undo.")
    queues[ctx.guild.id] = stack.pop()
    save_guild_queue(ctx.guild.id)
    await ctx.send("↩️ Restored the previous queue state.")


@bot.hybrid_command()
async def snapshot(ctx, *, name: str = "default"):
    """Save the current queue under a name: `!snapshot chill`."""
    queue_snapshots.setdefault(ctx.guild.id, {})[name] = [
        dict(s) for s in get_queue(ctx.guild.id)
    ]
    await ctx.send(f"📸 Saved queue snapshot **{name}** ({len(get_queue(ctx.guild.id))} tracks).")


@bot.hybrid_command()
async def restore(ctx, *, name: str = "default"):
    """Restore a previously saved snapshot: `!restore chill`."""
    snaps = queue_snapshots.get(ctx.guild.id, {})
    if name not in snaps:
        available = ", ".join(snaps) or "none"
        return await ctx.send(f"❌ No snapshot **{name}**. Available: {available}")
    _push_undo(ctx.guild.id)
    queues[ctx.guild.id] = [dict(s) for s in snaps[name]]
    save_guild_queue(ctx.guild.id)
    await ctx.send(f"📂 Restored snapshot **{name}** ({len(snaps[name])} tracks).")
    await start_if_idle(ctx.channel, ctx.guild)


@bot.hybrid_command(name="loop")
async def loop_cmd(ctx, mode: str):
    mode = mode.lower()
    if mode not in ("song", "queue", "off"):
        return await ctx.send("Usage: `!loop song|queue|off`")
    repeat_mode[ctx.guild.id] = mode
    await ctx.send(f"🔁 Repeat mode: **{mode}**")


@bot.hybrid_command(name="autoplay")
async def autoplay_cmd(ctx, mode: str = None):
    gid = ctx.guild.id
    if mode is None:
        autoplay_enabled[gid] = not autoplay_enabled.get(gid, False)
    else:
        autoplay_enabled[gid] = mode.lower() in ("on", "true", "yes", "1")
    await ctx.send(f"🎶 Autoplay: **{'on' if autoplay_enabled[gid] else 'off'}**")


@bot.hybrid_command()
async def history(ctx):
    hist = song_history.get(ctx.guild.id, [])
    if not hist:
        return await ctx.send("No history yet.")
    msg = "\n".join(s["title"] for s in hist[-10:])
    await ctx.send(f"📜 Recently played:\n{msg}")


@bot.hybrid_command(name="nowplaying", aliases=["np"])
async def now_playing_cmd(ctx):
    if not now_playing.get(ctx.guild.id):
        return await ctx.send("Nothing is playing right now.")
    await send_now_playing(ctx.channel, ctx.guild)


# =========================
# VOLUME
# =========================
@bot.hybrid_command()
async def volume(ctx, value: int):
    if not 0 <= value <= 200:
        return await ctx.send("❌ Range: 0–200")
    vol = set_volume(ctx.guild.id, value / 100)
    if ctx.voice_client and ctx.voice_client.source:
        ctx.voice_client.source.volume = vol
    await ctx.send(f"🔊 Volume set to **{value}%**")


@bot.hybrid_command()
async def volumeui(ctx):
    await ctx.send("🎚 Volume Control", view=VolumeView())


# =========================
# AUDIO FILTERS + EQ
# =========================
async def _restart_current_guild(guild):
    """
    Restart the current track so a new filter chain applies — but PRESERVE the
    playback position. We capture the elapsed time, reinsert the song at the
    front with that seek offset, then stop; play_next resumes from the same spot
    via FFmpeg's -ss. The listener barely notices the restart.
    """
    gid = guild.id
    vc = guild.voice_client
    if vc and (vc.is_playing() or vc.is_paused()):
        song = now_playing.get(gid)
        if song:
            elapsed = current_elapsed(gid)
            duration = song.get("duration")
            if duration:
                elapsed = min(elapsed, max(0, int(duration) - 1))
            seek_positions[gid] = max(0, elapsed)
            get_queue(gid).insert(0, song)
        now_playing[gid] = None  # stop repeat mode from double-adding it
        vc.stop()


async def _restart_current(ctx):
    """Backward-compatible wrapper used by all filter commands."""
    await _restart_current_guild(ctx.guild)


@bot.hybrid_command()
async def bassboost(ctx):
    set_filter(ctx.guild.id, bassboost=True)
    await ctx.send("🔊 Bass boost enabled")
    await _restart_current(ctx)


@bot.hybrid_command()
async def treble(ctx):
    set_filter(ctx.guild.id, treble=True)
    await ctx.send("🎻 Treble boost enabled")
    await _restart_current(ctx)


@bot.hybrid_command()
async def echo(ctx):
    set_filter(ctx.guild.id, echo=True)
    await ctx.send("🎧 Echo enabled")
    await _restart_current(ctx)


@bot.hybrid_command()
async def karaoke(ctx):
    set_filter(ctx.guild.id, karaoke=True)
    await ctx.send("🎤 Karaoke (vocal reduction) enabled")
    await _restart_current(ctx)


@bot.hybrid_command(name="eightd")
async def eight_d(ctx):
    """8D audio — apulsator rotates sound between channels."""
    set_filter(ctx.guild.id, **{"8d": True})
    await ctx.send("🌀 8D audio enabled")
    await _restart_current(ctx)


@bot.hybrid_command()
async def nightcore(ctx):
    set_filter(ctx.guild.id, speed=1.25, pitch=1.25)
    await ctx.send("⚡ Nightcore enabled")
    await _restart_current(ctx)


@bot.hybrid_command()
async def vaporwave(ctx):
    set_filter(ctx.guild.id, speed=0.8, pitch=0.8)
    await ctx.send("🌴 Vaporwave enabled")
    await _restart_current(ctx)


@bot.hybrid_command()
async def speed(ctx, value: float):
    if not 0.5 <= value <= 2.0:
        return await ctx.send("Range: 0.5–2.0")
    set_filter(ctx.guild.id, speed=value)
    await ctx.send(f"⏩ Speed set to {value}")
    await _restart_current(ctx)


@bot.hybrid_command()
async def pitch(ctx, value: float):
    if not 0.5 <= value <= 2.0:
        return await ctx.send("Range: 0.5–2.0")
    set_filter(ctx.guild.id, pitch=value)
    await ctx.send(f"🎵 Pitch set to {value}")
    await _restart_current(ctx)


@bot.hybrid_command()
async def eq(ctx, preset: str = None):
    """Apply an equalizer preset: rock, pop, bass, edm, jazz, classical, flat."""
    if not preset or preset.lower() not in EQ_PRESETS:
        return await ctx.send(f"Presets: {', '.join(EQ_PRESETS)}")
    chain = EQ_PRESETS[preset.lower()]
    if chain is None:
        audio_filters.setdefault(ctx.guild.id, {}).pop("eq", None)
        await ctx.send("🎚 EQ set to **flat**")
    else:
        set_filter(ctx.guild.id, eq=chain)
        await ctx.send(f"🎚 EQ preset: **{preset.lower()}**")
    await _restart_current(ctx)


@bot.hybrid_command(name="customeq")
async def custom_eq(ctx, *, eq_string):
    """Apply a custom ffmpeg equalizer string, e.g. `equalizer=f=1000:t=q:w=1:g=5`."""
    set_filter(ctx.guild.id, eq=eq_string)
    await ctx.send(f"🎚 Custom EQ applied: `{eq_string}`")
    await _restart_current(ctx)


@bot.hybrid_command()
async def normalize(ctx):
    """Toggle loudness normalization (ReplayGain-style)."""
    f = audio_filters.setdefault(ctx.guild.id, {})
    f["normalize"] = not f.get("normalize")
    await ctx.send(f"🔊 Normalization: **{'on' if f['normalize'] else 'off'}**")
    await _restart_current(ctx)


@bot.hybrid_command()
async def resetfilters(ctx):
    reset_filters(ctx.guild.id)
    await ctx.send("🧹 Filters cleared")
    await _restart_current(ctx)


# =========================
# FAVORITES (SQLite-backed)
# =========================
@bot.hybrid_command()
async def favorite(ctx, action: str = None, index: int = None):
    """!favorite (save current) · !favorite remove <#>"""
    if action and action.lower() == "remove":
        cur.execute("SELECT url, title FROM user_favorites WHERE user_id=? LIMIT 100", (ctx.author.id,))
        rows = cur.fetchall()
        if not index or not 1 <= index <= len(rows):
            return await ctx.send(f"❌ Usage: `!favorite remove <1-{len(rows)}>`")
        url, title = rows[index - 1]
        cur.execute("DELETE FROM user_favorites WHERE user_id=? AND url=?", (ctx.author.id, url))
        conn.commit()
        return await ctx.send(f"🗑 Removed favorite: **{title}**")

    song = now_playing.get(ctx.guild.id)
    if not song:
        return await ctx.send("Nothing is playing.")
    cur.execute(
        "INSERT OR IGNORE INTO user_favorites (user_id, url, title) VALUES (?, ?, ?)",
        (ctx.author.id, song["webpage_url"], song["title"]),
    )
    conn.commit()
    await ctx.send("❤️ Added to favorites")


@bot.hybrid_group(invoke_without_command=True, description="List your favorites (or use /favorites subcommands).")
async def favorites(ctx, action: str = None):
    """!favorites (list) · clear · export · import (attach a JSON file)"""
    if action and action.lower() == "clear":
        cur.execute("DELETE FROM user_favorites WHERE user_id=?", (ctx.author.id,))
        conn.commit()
        return await ctx.send("🧹 Favorites cleared.")

    if action and action.lower() == "export":
        cur.execute("SELECT url, title FROM user_favorites WHERE user_id=?", (ctx.author.id,))
        rows = cur.fetchall()
        payload = json.dumps([{"url": u, "title": t} for u, t in rows], indent=2)
        buf = io.BytesIO(payload.encode("utf-8"))
        return await ctx.send("📤 Your favorites:",
                              file=discord.File(buf, filename="favorites.json"))

    if action and action.lower() == "import":
        if not ctx.message.attachments:
            return await ctx.send("Attach a `favorites.json` file with the `!favorites import` command.")
        try:
            raw = await ctx.message.attachments[0].read()
            data = json.loads(raw.decode("utf-8"))
            count = 0
            for item in data:
                if item.get("url") and item.get("title"):
                    cur.execute(
                        "INSERT OR IGNORE INTO user_favorites (user_id, url, title) VALUES (?, ?, ?)",
                        (ctx.author.id, item["url"], item["title"]),
                    )
                    count += 1
            conn.commit()
            return await ctx.send(f"📥 Imported **{count}** favorites.")
        except Exception as e:
            return await ctx.send(f"❌ Import failed: {e}")

    cur.execute("SELECT title, url FROM user_favorites WHERE user_id=? LIMIT 25", (ctx.author.id,))
    rows = cur.fetchall()
    if not rows:
        return await ctx.send("No favorites yet. Use `!favorite` or the ❤️ button.")
    lines = [f"`{i + 1}.` [{r[0]}](<{r[1]}>)" for i, r in enumerate(rows)]
    embed = discord.Embed(title="❤️ Your Favorites", description="\n".join(lines),
                          color=discord.Color.red())
    await ctx.send(embed=embed)


# =========================
# NAMED PLAYLISTS (SQLite)
# =========================
def _pl_load(gid, name):
    """Return the list of songs for a named playlist, or None if missing/corrupt."""
    cur.execute("SELECT data FROM named_playlists WHERE guild_id=? AND name=?", (gid, name))
    row = cur.fetchone()
    if not row:
        return None
    try:
        return json.loads(row[0])
    except (json.JSONDecodeError, TypeError):
        return []


def _pl_store(gid, name, songs, owner_id):
    """Create or overwrite a named playlist."""
    cur.execute(
        """INSERT INTO named_playlists (guild_id, name, data, owner_id) VALUES (?, ?, ?, ?)
           ON CONFLICT(guild_id, name) DO UPDATE SET data=excluded.data""",
        (gid, name, json.dumps(songs), owner_id),
    )
    conn.commit()


@bot.hybrid_group(invoke_without_command=True, description="Manage playlists (use /playlist subcommands).")
async def playlist(ctx, action: str = None, *, args: str = None):
    """
    Named playlists (stored in SQLite):
      !playlist create <name>            save current queue as a new playlist
      !playlist save <name>              alias of create (overwrites)
      !playlist add <name> <song>        search & add a song (no queue needed)
      !playlist remove <name> <#>        remove a track by position
      !playlist show <name>              list a playlist's tracks
      !playlist play <name>              replace queue with the playlist and play
      !playlist append <name>            add the playlist to the end of the queue
      !playlist shuffle <name>           shuffle the stored playlist
      !playlist rename <old> <new>       rename
      !playlist delete <name>            delete
      !playlist clear <name>             empty a playlist (keeps the name)
      !playlist export <name>            export as a JSON file
      !playlist import <name>            import (attach a JSON file)
      !playlist list                     list all playlists
    """
    gid = ctx.guild.id
    action = (action or "").lower()

    def split_name_rest(text):
        """First whitespace-token is the name, the remainder is the payload."""
        text = (text or "").strip()
        if not text:
            return None, None
        parts = text.split(None, 1)
        return parts[0], (parts[1] if len(parts) > 1 else None)

    if action in ("create", "save"):
        if not args:
            return await ctx.send("Usage: `!playlist create <name>`")
        name = args.strip()
        q = list(get_queue(gid))
        cur_song = now_playing.get(gid)
        if cur_song:
            q.insert(0, cur_song)
        if not q:
            return await ctx.send("❌ Nothing in the queue to save.")
        _pl_store(gid, name, q, ctx.author.id)
        return await ctx.send(f"💾 Saved playlist **{name}** ({len(q)} tracks).")

    if action == "add":
        name, song_query = split_name_rest(args)
        if not name or not song_query:
            return await ctx.send("Usage: `!playlist add <name> <song>`")
        songs = _pl_load(gid, name)
        if songs is None:
            songs = []  # create on first add
        async with ctx.typing():
            try:
                results = await resolve_query(song_query, limit=1)
            except MusicError as e:
                return await ctx.send(f"❌ {e}")
        if not results:
            return await ctx.send("❌ No results found.")
        songs.append(results[0])
        _pl_store(gid, name, songs, ctx.author.id)
        return await ctx.send(f"➕ Added **{results[0]['title']}** to playlist **{name}** ({len(songs)} tracks).")

    if action == "remove":
        name, idx_str = split_name_rest(args)
        songs = _pl_load(gid, name) if name else None
        if songs is None:
            return await ctx.send("Usage: `!playlist remove <name> <#>`")
        try:
            idx = int((idx_str or "").strip())
        except ValueError:
            return await ctx.send("Usage: `!playlist remove <name> <#>`")
        if not 1 <= idx <= len(songs):
            return await ctx.send(f"❌ Give a number between 1 and {len(songs)}.")
        removed = songs.pop(idx - 1)
        _pl_store(gid, name, songs, ctx.author.id)
        return await ctx.send(f"🗑 Removed **{removed['title']}** from **{name}**.")

    if action == "show":
        if not args:
            return await ctx.send("Usage: `!playlist show <name>`")
        songs = _pl_load(gid, args.strip())
        if songs is None:
            return await ctx.send(f"❌ No playlist named **{args.strip()}**.")
        if not songs:
            return await ctx.send(f"Playlist **{args.strip()}** is empty.")
        lines = "\n".join(f"`{i + 1}.` {s['title']}" for i, s in enumerate(songs[:25]))
        embed = discord.Embed(title=f"🎼 {args.strip()}", description=lines, color=discord.Color.teal())
        embed.set_footer(text=f"{len(songs)} track(s)")
        return await ctx.send(embed=embed)

    if action in ("load", "append", "play"):
        if not args:
            return await ctx.send(f"Usage: `!playlist {action} <name>`")
        songs = _pl_load(gid, args.strip())
        if songs is None:
            return await ctx.send(f"❌ No playlist named **{args.strip()}**.")
        vc = await connect_vc(ctx)
        if not vc:
            return
        if action == "play":
            # Replace the queue, then perform exactly ONE transition. If audio is
            # active we stop once and the after-callback starts the first track —
            # we must NOT also call play_next (that double-start was the bug).
            get_queue(gid).clear()
            for s in songs:
                get_queue(gid).append(dict(s))
            save_guild_queue(gid)
            now_playing[gid] = None  # prevent repeat mode from re-adding old song
            await ctx.send(f"▶️ Playing **{len(songs)}** tracks from **{args.strip()}**.")
            await transition_now(ctx.channel, ctx.guild)
            return

        # load / append: add to the end and only start if idle.
        for s in songs:
            get_queue(gid).append(dict(s))
        save_guild_queue(gid)
        await ctx.send(f"📥 Queued **{len(songs)}** tracks from **{args.strip()}**.")
        await start_if_idle(ctx.channel, ctx.guild)
        return

    if action == "shuffle":
        if not args:
            return await ctx.send("Usage: `!playlist shuffle <name>`")
        songs = _pl_load(gid, args.strip())
        if songs is None:
            return await ctx.send(f"❌ No playlist named **{args.strip()}**.")
        random.shuffle(songs)
        _pl_store(gid, args.strip(), songs, ctx.author.id)
        return await ctx.send(f"🔀 Shuffled playlist **{args.strip()}**.")

    if action == "clear":
        if not args:
            return await ctx.send("Usage: `!playlist clear <name>`")
        if _pl_load(gid, args.strip()) is None:
            return await ctx.send(f"❌ No playlist named **{args.strip()}**.")
        _pl_store(gid, args.strip(), [], ctx.author.id)
        return await ctx.send(f"🧹 Cleared playlist **{args.strip()}**.")

    if action == "delete":
        if not args:
            return await ctx.send("Usage: `!playlist delete <name>`")
        cur.execute("DELETE FROM named_playlists WHERE guild_id=? AND name=?", (gid, args.strip()))
        conn.commit()
        return await ctx.send(f"🗑 Deleted playlist **{args.strip()}** (if it existed).")

    if action == "rename":
        parts = (args or "").split()
        if len(parts) < 2:
            return await ctx.send("Usage: `!playlist rename <old> <new>`")
        old, new = parts[0], " ".join(parts[1:])
        cur.execute("UPDATE named_playlists SET name=? WHERE guild_id=? AND name=?", (new, gid, old))
        conn.commit()
        return await ctx.send(f"✏ Renamed **{old}** → **{new}**.")

    if action == "export":
        if not args:
            return await ctx.send("Usage: `!playlist export <name>`")
        songs = _pl_load(gid, args.strip())
        if songs is None:
            return await ctx.send(f"❌ No playlist named **{args.strip()}**.")
        buf = io.BytesIO(json.dumps(songs, indent=2).encode("utf-8"))
        return await ctx.send(
            f"📤 Playlist **{args.strip()}**:",
            file=discord.File(buf, filename=f"{args.strip()}.json"),
        )

    if action == "import":
        if not args:
            return await ctx.send("Usage: `!playlist import <name>` (attach a JSON file)")
        if not ctx.message.attachments:
            return await ctx.send("❌ Attach a JSON file with `!playlist import <name>`.")
        try:
            raw = await ctx.message.attachments[0].read()
            data = json.loads(raw.decode("utf-8"))
            if not isinstance(data, list):
                raise ValueError("JSON must be a list of songs.")
            _pl_store(gid, args.strip(), data, ctx.author.id)
            return await ctx.send(f"📥 Imported **{len(data)}** tracks into **{args.strip()}**.")
        except Exception as e:
            return await ctx.send(f"❌ Import failed: {e}")

    if action == "list":
        cur.execute("SELECT name, data FROM named_playlists WHERE guild_id=?", (gid,))
        rows = cur.fetchall()
        if not rows:
            return await ctx.send("No saved playlists. Create one with `!playlist create <name>`.")
        lines = []
        for name, data in rows:
            try:
                count = len(json.loads(data))
            except (json.JSONDecodeError, TypeError):
                count = 0
            lines.append(f"• **{name}** — {count} tracks")
        embed = discord.Embed(title="🎼 Saved Playlists", description="\n".join(lines),
                              color=discord.Color.teal())
        return await ctx.send(embed=embed)

    await ctx.send(
        "Usage: `!playlist create|save|add|remove|show|play|append|shuffle|"
        "rename|delete|clear|export|import|list`"
    )


# =========================
# SMART / STATS
# =========================
def _format_duration_long(seconds):
    seconds = int(seconds or 0)
    h, rem = divmod(seconds, 3600)
    m, s = divmod(rem, 60)
    if h:
        return f"{h}h {m}m"
    if m:
        return f"{m}m {s}s"
    return f"{s}s"


@bot.hybrid_command()
async def stats(ctx, member: discord.Member = None):
    member = member or ctx.author
    cur.execute("SELECT songs_played, listen_seconds FROM stats WHERE user_id=? AND guild_id=?",
                (member.id, ctx.guild.id))
    row = cur.fetchone()
    played = row[0] if row else 0
    listened = row[1] if row and len(row) > 1 else 0
    embed = discord.Embed(title=f"🎧 Stats — {member.display_name}",
                          color=discord.Color.blurple())
    embed.add_field(name="Songs Played", value=str(played), inline=True)
    embed.add_field(name="Listening Time",
                    value=_format_duration_long(listened), inline=True)
    if member.display_avatar:
        embed.set_thumbnail(url=member.display_avatar.url)
    await ctx.send(embed=embed)


@bot.hybrid_command(name="topartists", aliases=["mostplayedartists"])
async def top_artists(ctx):
    cur.execute(
        "SELECT artist, plays FROM artist_counts WHERE guild_id=? ORDER BY plays DESC LIMIT 10",
        (ctx.guild.id,),
    )
    rows = cur.fetchall()
    if not rows:
        return await ctx.send("No artist data yet.")
    lines = [f"`{i + 1}.` {a} — **{p}** plays" for i, (a, p) in enumerate(rows)]
    embed = discord.Embed(title="🎤 Most Played Artists", description="\n".join(lines),
                          color=discord.Color.purple())
    await ctx.send(embed=embed)


@bot.hybrid_command(name="listeningtime", aliases=["listentime"])
async def listening_time(ctx):
    cur.execute(
        "SELECT user_id, listen_seconds FROM stats WHERE guild_id=? "
        "ORDER BY listen_seconds DESC LIMIT 10",
        (ctx.guild.id,),
    )
    rows = cur.fetchall()
    if not rows:
        return await ctx.send("No listening data yet.")
    lines = []
    for i, (uid, secs) in enumerate(rows):
        member = ctx.guild.get_member(uid)
        name = member.display_name if member else f"User {uid}"
        lines.append(f"`{i + 1}.` {name} — **{_format_duration_long(secs)}**")
    embed = discord.Embed(title="⏱ Listening Time Leaderboard",
                          description="\n".join(lines), color=discord.Color.green())
    await ctx.send(embed=embed)


@bot.hybrid_command(name="mostplayed")
async def most_played(ctx):
    cur.execute(
        "SELECT title, plays FROM play_counts WHERE guild_id=? ORDER BY plays DESC LIMIT 10",
        (ctx.guild.id,),
    )
    rows = cur.fetchall()
    if not rows:
        return await ctx.send("No play data yet.")
    lines = [f"`{i + 1}.` {t} — **{p}** plays" for i, (t, p) in enumerate(rows)]
    embed = discord.Embed(title="🔥 Most Played", description="\n".join(lines),
                          color=discord.Color.orange())
    await ctx.send(embed=embed)


@bot.hybrid_command(name="toplisteners")
async def top_listeners(ctx):
    cur.execute(
        "SELECT user_id, songs_played FROM stats WHERE guild_id=? ORDER BY songs_played DESC LIMIT 10",
        (ctx.guild.id,),
    )
    rows = cur.fetchall()
    if not rows:
        return await ctx.send("No listener data yet.")
    lines = []
    for i, (uid, plays) in enumerate(rows):
        member = ctx.guild.get_member(uid)
        name = member.display_name if member else f"User {uid}"
        lines.append(f"`{i + 1}.` {name} — **{plays}** songs")
    embed = discord.Embed(title="🏆 Top Listeners", description="\n".join(lines),
                          color=discord.Color.gold())
    await ctx.send(embed=embed)


@bot.hybrid_command()
async def recent(ctx):
    hist = song_history.get(ctx.guild.id, [])
    if not hist:
        return await ctx.send("No recently played tracks.")
    lines = [f"`{i + 1}.` {s['title']}" for i, s in enumerate(reversed(hist[-10:]))]
    embed = discord.Embed(title="🕒 Recently Played", description="\n".join(lines),
                          color=discord.Color.blurple())
    await ctx.send(embed=embed)


# =========================
# PROFILE & ACHIEVEMENTS
# =========================
# (threshold, name, emoji, description)
ACHIEVEMENTS = [
    (1, "First Track", "🎵", "Played your first song."),
    (100, "Century", "💯", "Played 100 songs."),
    (500, "Audiophile", "🎧", "Played 500 songs."),
    (1000, "Legend", "🏆", "Played 1000 songs."),
]


def _unlocked_achievements(songs_played):
    return [a for a in ACHIEVEMENTS if songs_played >= a[0]]


def _next_achievement(songs_played):
    for a in ACHIEVEMENTS:
        if songs_played < a[0]:
            return a
    return None


def _member_music_summary(guild_id, user_id):
    cur.execute(
        "SELECT songs_played, listen_seconds FROM stats WHERE user_id=? AND guild_id=?",
        (user_id, guild_id),
    )
    row = cur.fetchone()
    played = row[0] if row else 0
    listened = row[1] if row and len(row) > 1 else 0
    return played, (listened or 0)


@bot.hybrid_command(aliases=["me"])
async def profile(ctx, member: discord.Member = None):
    member = member or ctx.author
    played, listened = _member_music_summary(ctx.guild.id, member.id)
    unlocked = _unlocked_achievements(played)

    # Top artists this guild (global to guild, best-effort personalization not tracked per-user).
    cur.execute(
        "SELECT artist, plays FROM artist_counts WHERE guild_id=? ORDER BY plays DESC LIMIT 5",
        (ctx.guild.id,),
    )
    artists = cur.fetchall()

    embed = discord.Embed(title=f"👤 {member.display_name}'s Profile",
                          color=discord.Color.from_rgb(88, 101, 242))
    if member.display_avatar:
        embed.set_thumbnail(url=member.display_avatar.url)
    embed.add_field(name="🎵 Songs Played", value=str(played), inline=True)
    embed.add_field(name="⏱ Listening Time",
                    value=_format_duration_long(listened), inline=True)
    embed.add_field(name="🏅 Badges", value=str(len(unlocked)), inline=True)
    if artists:
        embed.add_field(
            name="🎤 Server Top Artists",
            value="\n".join(f"`{i+1}.` {a} — {p}" for i, (a, p) in enumerate(artists)),
            inline=False,
        )
    if unlocked:
        embed.add_field(
            name="🏅 Achievements",
            value=" ".join(f"{a[2]}" for a in unlocked),
            inline=False,
        )
    nxt = _next_achievement(played)
    if nxt:
        embed.add_field(
            name="🎯 Next Goal",
            value=f"{nxt[2]} **{nxt[1]}** — {nxt[0] - played} more songs",
            inline=False,
        )
    await ctx.send(embed=embed)


@bot.hybrid_command(aliases=["badges"])
async def achievements(ctx, member: discord.Member = None):
    member = member or ctx.author
    played, _ = _member_music_summary(ctx.guild.id, member.id)
    lines = []
    for threshold, name, emoji, desc in ACHIEVEMENTS:
        mark = "✅" if played >= threshold else "🔒"
        lines.append(f"{mark} {emoji} **{name}** — {desc}")
    embed = discord.Embed(title=f"🏅 {member.display_name}'s Achievements",
                          description="\n".join(lines), color=discord.Color.gold())
    embed.set_footer(text=f"{len(_unlocked_achievements(played))}/{len(ACHIEVEMENTS)} unlocked")
    await ctx.send(embed=embed)


# =========================
# DJ FEATURES
# =========================
@bot.hybrid_command(name="voteskip", aliases=["vs"])
async def vote_skip(ctx):
    """Vote to skip the current track. Skips at >50% of listeners."""
    vc = ctx.voice_client
    if not vc or not (vc.is_playing() or vc.is_paused()):
        return await ctx.send("Nothing is playing.")
    gid = ctx.guild.id
    listeners = [m for m in vc.channel.members if not m.bot]
    needed = max(1, len(listeners) // 2 + 1)
    votes = vote_skips.setdefault(gid, set())
    votes.add(ctx.author.id)
    if len(votes) >= needed or is_dj(ctx.author):
        vc.stop()
        vote_skips.pop(gid, None)
        return await ctx.send("🗳 Vote passed — skipping ⏭")
    await ctx.send(f"🗳 Vote to skip: **{len(votes)}/{needed}**")


@bot.hybrid_command(name="djrole")
@commands.has_permissions(manage_guild=True)
async def dj_role(ctx, role: discord.Role = None):
    set_dj_setting(ctx.guild.id, dj_role_id=(role.id if role else None))
    if role:
        await ctx.send(f"🎧 DJ role set to **{role.name}**.")
    else:
        await ctx.send("🎧 DJ role cleared — everyone can DJ.")


@bot.hybrid_command(name="queuelock")
async def queue_lock_cmd(ctx, mode: str = None):
    if not is_dj(ctx.author):
        return await ctx.send("❌ DJ only.")
    locked = (mode or "").lower() in ("on", "true", "yes", "1")
    set_dj_setting(ctx.guild.id, queue_locked=1 if locked else 0)
    await ctx.send(f"🔒 Queue lock: **{'on' if locked else 'off'}**")


@bot.hybrid_command(name="requesterskip")
async def requester_skip_cmd(ctx, mode: str = None):
    if not is_dj(ctx.author):
        return await ctx.send("❌ DJ only.")
    on = (mode or "").lower() in ("on", "true", "yes", "1")
    set_dj_setting(ctx.guild.id, requester_only_skip=1 if on else 0)
    await ctx.send(f"🎚 Requester-only skip: **{'on' if on else 'off'}**")


# =========================
# GEMINI AI COMMANDS
# =========================
async def ask_gemini(prompt):
    if not ai_model:
        raise MusicError("Gemini isn't configured (missing GEMINI_API_KEY).")
    loop = asyncio.get_running_loop()
    try:
        response = await loop.run_in_executor(None, ai_model.generate_content, prompt)
        return response.text
    except Exception as e:
        raise MusicError(f"Gemini error: {e}") from e


async def _ai_reply(ctx, prompt):
    async with ctx.typing():
        try:
            text = await ask_gemini(prompt)
        except MusicError as e:
            return await ctx.send(f"❌ {e}")
    for i in range(0, len(text), 2000):
        await ctx.send(text[i:i + 2000])


@bot.hybrid_group(name="ai", aliases=["chat", "ask"], invoke_without_command=True,
                  description="Chat with Gemini AI (or use /ai subcommands).")
@commands.cooldown(1, 5, commands.BucketType.user)
async def ai_cmd(ctx, *, prompt: str = None):
    if prompt is None:
        return await ctx.send("Usage: `/ai <prompt>` or a subcommand: recommend, playlist, explain, translate, assistant.")
    await _ai_reply(ctx, prompt)


@bot.hybrid_command()
async def summarize(ctx, *, text=None):
    if not text and ctx.message.reference:
        ref = await ctx.channel.fetch_message(ctx.message.reference.message_id)
        text = ref.content
    if not text:
        return await ctx.send("Provide text, or reply to a message with `!summarize`.")
    await _ai_reply(ctx, f"Summarize the following concisely:\n\n{text}")


@bot.hybrid_command()
async def translate(ctx, *, payload):
    if "|" not in payload:
        return await ctx.send("Usage: `!translate <language> | <text>`")
    lang, text = payload.split("|", 1)
    await _ai_reply(ctx, f"Translate the following text to {lang.strip()}:\n\n{text.strip()}")


@bot.hybrid_command(name="code")
async def code_cmd(ctx, *, request):
    await _ai_reply(ctx, f"Write code for this request. Include a brief explanation:\n\n{request}")


@bot.hybrid_command()
async def review(ctx, *, code=None):
    if not code and ctx.message.reference:
        ref = await ctx.channel.fetch_message(ctx.message.reference.message_id)
        code = ref.content
    if not code:
        return await ctx.send("Provide code, or reply to a code message with `!review`.")
    await _ai_reply(ctx, f"Review this code for bugs and improvements:\n\n{code}")


@bot.hybrid_command()
async def explain(ctx, *, topic=None):
    if not topic and ctx.message.reference:
        ref = await ctx.channel.fetch_message(ctx.message.reference.message_id)
        topic = ref.content
    if not topic:
        return await ctx.send("Provide a topic, or reply to a message with `!explain`.")
    await _ai_reply(ctx, f"Explain this clearly and simply:\n\n{topic}")


@bot.hybrid_command(name="explainlyrics")
async def explain_lyrics(ctx, *, song=None):
    song = song or (now_playing.get(ctx.guild.id) or {}).get("title")
    if not song:
        return await ctx.send("No song specified and nothing is playing.")
    await _ai_reply(
        ctx,
        f"Give a general, non-verbatim explanation of the themes and meaning of the song "
        f"'{song}'. Do not quote lyrics directly.",
    )


@bot.hybrid_command()
async def recommend(ctx, *, mood):
    await _ai_reply(
        ctx,
        f"Suggest 8 songs (title + artist) that fit this mood/genre: {mood}. "
        "Format as a simple numbered list.",
    )


# =========================
# LYRICS (cached Genius + AI translate)
# =========================
@bot.hybrid_command()
async def lyrics(ctx, *, song=None):
    song = song or (now_playing.get(ctx.guild.id) or {}).get("title")
    if not song:
        return await ctx.send("❌ No song specified and nothing is playing.")
    async with ctx.typing():
        try:
            data = await fetch_lyrics(song)
        except Exception as e:
            return await ctx.send(f"❌ Error fetching lyrics:\n`{e}`")
    if not data:
        return await ctx.send("❌ Lyrics not found.")
    text = data["lyrics"]
    chunks = [text[i:i + 3900] for i in range(0, len(text), 3900)]
    for i, chunk in enumerate(chunks):
        embed = discord.Embed(title=data["title"], description=f"```{chunk}```",
                              color=discord.Color.orange())
        embed.set_author(name=data["artist"])
        if data.get("art"):
            embed.set_thumbnail(url=data["art"])
        src = data.get("source", "Unknown")
        synced_tag = " • 🎼 synced" if data.get("synced") else ""
        embed.set_footer(text=f"Page {i + 1}/{len(chunks)} • Source: {src}{synced_tag}")
        await ctx.send(embed=embed)


@bot.hybrid_command(name="translatelyrics")
async def translate_lyrics(ctx, *, payload):
    """!translatelyrics <language> | <song>"""
    if "|" not in payload:
        return await ctx.send("Usage: `!translatelyrics <language> | <song>`")
    lang, song = payload.split("|", 1)
    song = song.strip() or (now_playing.get(ctx.guild.id) or {}).get("title")
    if not song:
        return await ctx.send("❌ No song specified.")
    async with ctx.typing():
        try:
            data = await fetch_lyrics(song)
        except Exception as e:
            return await ctx.send(f"❌ Error: {e}")
    if not data:
        return await ctx.send("❌ Lyrics not found.")
    await _ai_reply(
        ctx,
        f"Translate these song lyrics to {lang.strip()}. Keep it line-by-line:\n\n{data['lyrics'][:4000]}",
    )


# =========================
# MODERATION
# =========================
@bot.hybrid_command()
@commands.has_permissions(kick_members=True)
async def kick(ctx, member: discord.Member, *, reason=None):
    await member.kick(reason=reason)
    await ctx.send(f"👢 Kicked {member}")


@bot.hybrid_command()
@commands.has_permissions(ban_members=True)
async def ban(ctx, member: discord.Member, *, reason=None):
    await member.ban(reason=reason)
    await ctx.send(f"🔨 Banned {member}")


@bot.hybrid_command()
@commands.has_permissions(manage_messages=True)
async def clear(ctx, amount: int):
    deleted = await ctx.channel.purge(limit=amount)
    await ctx.send(f"🧹 Deleted {len(deleted)} messages", delete_after=3)


@bot.hybrid_command()
@commands.has_permissions(moderate_members=True)
async def warn(ctx, member: discord.Member, *, reason="No reason given"):
    await ctx.send(f"⚠️ {member.mention} warned: {reason}")


# =========================
# UTILITY
# =========================
@bot.hybrid_command()
async def ping(ctx):
    await ctx.send(f"🏓 Pong: {round(bot.latency * 1000)}ms")


@bot.hybrid_command()
async def avatar(ctx, member: discord.Member = None):
    member = member or ctx.author
    await ctx.send(member.display_avatar.url)


@bot.hybrid_command()
async def serverinfo(ctx):
    guild = ctx.guild
    embed = discord.Embed(title=guild.name, color=discord.Color.blurple())
    embed.add_field(name="Members", value=guild.member_count)
    embed.add_field(name="Owner", value=str(guild.owner))
    embed.add_field(name="Created", value=discord.utils.format_dt(guild.created_at, "D"))
    await ctx.send(embed=embed)


@bot.hybrid_command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def github(ctx, user):
    async with aiohttp.ClientSession() as session:
        async with session.get(f"https://api.github.com/users/{user}") as r:
            if r.status != 200:
                return await ctx.send("❌ User not found.")
            data = await r.json()
    embed = discord.Embed(title=data.get("login"), url=data.get("html_url"),
                          color=discord.Color.dark_grey())
    embed.add_field(name="Repos", value=data.get("public_repos"))
    embed.add_field(name="Followers", value=data.get("followers"))
    await ctx.send(embed=embed)


@bot.hybrid_command()
@commands.cooldown(1, 10, commands.BucketType.user)
async def weather(ctx, *, city):
    async with aiohttp.ClientSession() as session:
        async with session.get(f"https://wttr.in/{city}?format=3") as r:
            data = await r.text()
    await ctx.send(f"🌤 {data.strip()}")


# =========================
# FUN
# =========================
@bot.hybrid_command()
async def coinflip(ctx):
    await ctx.send(random.choice(["🪙 Heads", "🪙 Tails"]))


@bot.hybrid_command()
async def dice(ctx):
    await ctx.send(f"🎲 {random.randint(1, 6)}")


@bot.hybrid_command()
async def eightball(ctx, *, question):
    responses = ["Yes", "No", "Maybe", "Absolutely", "Never", "Ask again later"]
    await ctx.send(f"🎱 {random.choice(responses)}")


# =========================
# HELP
# =========================
@bot.hybrid_command()
async def help(ctx):
    await ctx.send(embed=build_help_overview(), view=HelpView())


# =========================
# OWNER / MAINTENANCE
# =========================
def is_owner(ctx):
    return ctx.author.id in OWNER_IDS


@bot.check
async def global_maintenance_check(ctx):
    if getattr(bot, "maintenance", False):
        return is_owner(ctx)
    return True


@bot.hybrid_command()
async def maintenance(ctx, mode: str):
    if not is_owner(ctx):
        return await ctx.send("Owner only.")
    bot.maintenance = mode.lower() == "on"
    await ctx.send(f"🔧 Maintenance mode: {mode}")


@bot.hybrid_command()
async def restart(ctx):
    if not is_owner(ctx):
        return await ctx.send("Owner only.")
    await ctx.send("♻ Restarting…")
    save_all_queues()
    os._exit(0)


# =========================
# PERSISTENCE (JSON, not eval)
# =========================
def save_all_queues():
    for guild_id, q in queues.items():
        cur.execute(
            """INSERT INTO playlists (guild_id, name, data) VALUES (?, 'autosave', ?)
               ON CONFLICT(guild_id) DO UPDATE SET data=excluded.data""",
            (guild_id, json.dumps(q)),
        )
    conn.commit()


def load_queue(guild_id):
    cur.execute("SELECT data FROM playlists WHERE guild_id=?", (guild_id,))
    row = cur.fetchone()
    if row:
        try:
            queues[guild_id] = json.loads(row[0])
        except (json.JSONDecodeError, TypeError):
            queues[guild_id] = []


@tasks.loop(minutes=2)
async def autosave():
    save_all_queues()


# =========================
# SLASH AUTOCOMPLETE
# =========================
async def _query_autocomplete(interaction: discord.Interaction, current: str):
    """
    Lightweight, non-blocking autocomplete: suggests the typed text plus a few
    recently played titles. Deliberately does NOT hit YouTube per keystroke.
    """
    choices = []
    if current:
        choices.append(app_commands.Choice(name=current[:100], value=current[:100]))
    gid = interaction.guild.id if interaction.guild else None
    if gid:
        for s in reversed(song_history.get(gid, [])[-10:]):
            title = s.get("title", "")
            if not current or current.lower() in title.lower():
                choices.append(app_commands.Choice(name=title[:100], value=title[:100]))
            if len(choices) >= 8:
                break
    return choices[:8]


# Attach autocomplete to the hybrid commands that carry a `query` param.
play.autocomplete("query")(_query_autocomplete)
search.autocomplete("query")(_query_autocomplete)


async def _playlist_autocomplete(interaction: discord.Interaction, current: str):
    """Suggest this guild's saved playlist names."""
    gid = interaction.guild.id if interaction.guild else None
    if not gid:
        return []
    cur.execute("SELECT name FROM named_playlists WHERE guild_id=? LIMIT 25", (gid,))
    names = [r[0] for r in cur.fetchall()]
    cur_l = (current or "").lower()
    return [
        app_commands.Choice(name=n[:100], value=n[:100])
        for n in names if cur_l in n.lower()
    ][:25]


async def _filter_autocomplete(interaction: discord.Interaction, current: str):
    """Suggest available audio filters / EQ presets."""
    names = ["bassboost", "treble", "echo", "karaoke", "8d", "nightcore",
             "vaporwave", "normalize", "reset"] + [f"eq:{p}" for p in EQ_PRESETS]
    cur_l = (current or "").lower()
    return [
        app_commands.Choice(name=n, value=n)
        for n in names if cur_l in n.lower()
    ][:25]


async def _favorite_autocomplete(interaction: discord.Interaction, current: str):
    """Suggest the invoking user's saved favorite titles (value = 1-based index)."""
    cur.execute(
        "SELECT title FROM user_favorites WHERE user_id=? LIMIT 25",
        (interaction.user.id,),
    )
    rows = cur.fetchall()
    cur_l = (current or "").lower()
    out = []
    for i, (title,) in enumerate(rows, start=1):
        if cur_l in (title or "").lower():
            out.append(app_commands.Choice(name=f"{i}. {title}"[:100], value=i))
    return out[:25]


# =========================
# SLASH MODALS (playlist create / rename)
# =========================
class PlaylistCreateModal(discord.ui.Modal, title="Create playlist"):
    name = discord.ui.TextInput(label="Playlist name", placeholder="e.g. Chill", max_length=60)

    async def on_submit(self, interaction: discord.Interaction):
        ctx = await bot.get_context(interaction)
        await playlist.callback(ctx, "create", args=str(self.name).strip())


class PlaylistRenameModal(discord.ui.Modal, title="Rename playlist"):
    old = discord.ui.TextInput(label="Current name", max_length=60)
    new = discord.ui.TextInput(label="New name", max_length=60)

    async def on_submit(self, interaction: discord.Interaction):
        ctx = await bot.get_context(interaction)
        await playlist.callback(ctx, "rename", args=f"{str(self.old).strip()} {str(self.new).strip()}")


# =========================
# /playlist SUBCOMMANDS  (reuse the playlist root callback — no duplicate logic)
# =========================
@playlist.command(name="create", description="Save the current queue as a playlist.")
@app_commands.describe(name="New playlist name (leave blank on slash for a popup)")
async def playlist_create(ctx, *, name: str = None):
    if name is None:
        if ctx.interaction:
            return await ctx.interaction.response.send_modal(PlaylistCreateModal())
        return await ctx.send("Usage: `!playlist create <name>`")
    await playlist.callback(ctx, "create", args=name)


@playlist.command(name="play", description="Replace the queue and play a saved playlist.")
@app_commands.describe(name="Playlist to play")
async def playlist_play(ctx, *, name: str):
    await playlist.callback(ctx, "play", args=name)


@playlist.command(name="append", description="Add a saved playlist to the end of the queue.")
async def playlist_append(ctx, *, name: str):
    await playlist.callback(ctx, "append", args=name)


@playlist.command(name="add", description="Search and add a song to a playlist.")
@app_commands.describe(name="Playlist name", song="Song to search & add")
async def playlist_add(ctx, name: str, *, song: str):
    await playlist.callback(ctx, "add", args=f"{name} {song}")


@playlist.command(name="remove", description="Remove a track from a playlist by number.")
@app_commands.describe(name="Playlist name", index="Track number to remove")
async def playlist_remove(ctx, name: str, index: int):
    await playlist.callback(ctx, "remove", args=f"{name} {index}")


@playlist.command(name="show", description="List a playlist's tracks.")
async def playlist_show(ctx, *, name: str):
    await playlist.callback(ctx, "show", args=name)


@playlist.command(name="shuffle", description="Shuffle a stored playlist.")
async def playlist_shuffle(ctx, *, name: str):
    await playlist.callback(ctx, "shuffle", args=name)


@playlist.command(name="rename", description="Rename a playlist.")
@app_commands.describe(old="Current name", new="New name")
async def playlist_rename(ctx, old: str = None, *, new: str = None):
    if old is None or new is None:
        if ctx.interaction:
            return await ctx.interaction.response.send_modal(PlaylistRenameModal())
        return await ctx.send("Usage: `!playlist rename <old> <new>`")
    await playlist.callback(ctx, "rename", args=f"{old} {new}")


@playlist.command(name="delete", description="Delete a playlist.")
async def playlist_delete(ctx, *, name: str):
    await playlist.callback(ctx, "delete", args=name)


@playlist.command(name="cleanup", description="Empty a playlist (keeps the name).")
async def playlist_cleanup(ctx, *, name: str):
    await playlist.callback(ctx, "clear", args=name)


@playlist.command(name="export", description="Export a playlist as JSON.")
async def playlist_export(ctx, *, name: str):
    await playlist.callback(ctx, "export", args=name)


@playlist.command(name="import", description="Import a playlist from an attached JSON file.")
async def playlist_import(ctx, *, name: str):
    await playlist.callback(ctx, "import", args=name)


@playlist.command(name="list", description="List all saved playlists.")
async def playlist_list(ctx):
    await playlist.callback(ctx, "list")


@playlist.command(name="ai", description="Generate a brand-new playlist with AI and save it.")
@app_commands.describe(name="Name to save under", prompt="Describe the vibe, e.g. 'lofi study'")
async def playlist_ai(ctx, name: str, *, prompt: str):
    """AI-generated playlist: ask Gemini for songs, resolve them, save under `name`."""
    async with ctx.typing():
        try:
            raw = await ask_gemini(
                f"List 10 real songs for this request: {prompt}. "
                "Reply with ONLY 'Title - Artist' lines, no numbering, no extra text."
            )
        except MusicError as e:
            return await ctx.send(f"❌ {e}")
        titles = [ln.strip("-• ").strip() for ln in raw.splitlines() if ln.strip()][:10]
        songs = []
        for t in titles:
            try:
                res = await resolve_query(t, limit=1)
                if res:
                    songs.append(res[0])
            except MusicError:
                continue
    if not songs:
        return await ctx.send("❌ Couldn't build that playlist.")
    _pl_store(ctx.guild.id, name, songs, ctx.author.id)
    await ctx.send(f"🤖 Created AI playlist **{name}** with **{len(songs)}** tracks.")


@playlist.command(name="expand", description="Add AI-recommended similar songs to a playlist.")
@app_commands.describe(name="Existing playlist to expand", count="How many songs to add")
async def playlist_expand(ctx, name: str, count: int = 5):
    songs = _pl_load(ctx.guild.id, name)
    if songs is None:
        return await ctx.send(f"❌ No playlist named **{name}**.")
    seed = ", ".join(s.get("title", "") for s in songs[:5]) or name
    count = max(1, min(15, count))
    async with ctx.typing():
        try:
            raw = await ask_gemini(
                f"Suggest {count} songs similar to these: {seed}. "
                "Reply with ONLY 'Title - Artist' lines."
            )
        except MusicError as e:
            return await ctx.send(f"❌ {e}")
        added = 0
        for t in [ln.strip("-• ").strip() for ln in raw.splitlines() if ln.strip()][:count]:
            try:
                res = await resolve_query(t, limit=1)
                if res:
                    songs.append(res[0])
                    added += 1
            except MusicError:
                continue
    _pl_store(ctx.guild.id, name, songs, ctx.author.id)
    await ctx.send(f"➕ Added **{added}** AI-picked track(s) to **{name}**.")


@playlist.command(name="improve", description="Ask AI how to improve a playlist's flow.")
async def playlist_improve(ctx, *, name: str):
    songs = _pl_load(ctx.guild.id, name)
    if songs is None:
        return await ctx.send(f"❌ No playlist named **{name}**.")
    listing = "\n".join(s.get("title", "") for s in songs[:30])
    await _ai_reply(ctx, f"Here is a playlist:\n{listing}\n\nSuggest ordering/pacing improvements and songs to add.")


# Autocomplete for playlist names on the relevant subcommands.
for _sub in (playlist_play, playlist_append, playlist_show, playlist_shuffle,
             playlist_delete, playlist_cleanup, playlist_export, playlist_expand,
             playlist_improve):
    _sub.autocomplete("name")(_playlist_autocomplete)
playlist_add.autocomplete("name")(_playlist_autocomplete)
playlist_remove.autocomplete("name")(_playlist_autocomplete)
playlist_add.autocomplete("song")(_query_autocomplete)


# =========================
# /queue SUBCOMMANDS  (reuse existing command callbacks)
# =========================
@queue.command(name="show", description="Show the paginated queue.")
async def queue_show(ctx):
    await queue.callback(ctx, args=None)


@queue.command(name="clear", description="Clear the queue (current song keeps playing).")
async def queue_clear(ctx):
    await clear_queue.callback(ctx)


@queue.command(name="shuffle", description="Shuffle the queue.")
async def queue_shuffle(ctx):
    await shuffle.callback(ctx)


@queue.command(name="move", description="Move a track to a new position.")
@app_commands.describe(from_pos="Current position", to_pos="New position")
async def queue_move(ctx, from_pos: int, to_pos: int):
    await move.callback(ctx, from_pos, to_pos)


@queue.command(name="swap", description="Swap two tracks.")
async def queue_swap(ctx, a: int, b: int):
    await swap.callback(ctx, a, b)


@queue.command(name="remove", description="Remove a track by position.")
async def queue_remove(ctx, index: int):
    await remove.callback(ctx, index)


@queue.command(name="history", description="Show recently played tracks.")
async def queue_history(ctx):
    await history.callback(ctx)


@queue.command(name="restore", description="Restore a saved queue snapshot.")
async def queue_restore(ctx, *, name: str = "default"):
    await restore.callback(ctx, name=name)


# =========================
# /favorites SUBCOMMANDS  (reuse existing callbacks)
# =========================
@favorites.command(name="clear", description="Remove all your favorites.")
async def favorites_clear(ctx):
    await favorites.callback(ctx, action="clear")


@favorites.command(name="export", description="Export your favorites as JSON.")
async def favorites_export(ctx):
    await favorites.callback(ctx, action="export")


@favorites.command(name="import", description="Import favorites from an attached JSON file.")
async def favorites_import(ctx):
    await favorites.callback(ctx, action="import")


@favorites.command(name="remove", description="Remove one of your favorites.")
@app_commands.describe(index="The favorite to remove")
async def favorites_remove(ctx, index: int):
    await favorite.callback(ctx, action="remove", index=index)


favorites_remove.autocomplete("index")(_favorite_autocomplete)


# =========================
# /filter GROUP  (reuse existing filter command callbacks)
# =========================
@bot.hybrid_group(name="filter", invoke_without_command=True,
                  description="Audio filters & EQ (use /filter subcommands).")
async def filter_group(ctx):
    active = [k for k, v in audio_filters.get(ctx.guild.id, {}).items() if v]
    await ctx.send(f"🎚 Active filters: {', '.join(active) if active else 'none'}")


@filter_group.command(name="bassboost", description="Toggle bass boost.")
async def filter_bassboost(ctx):
    await bassboost.callback(ctx)


@filter_group.command(name="treble", description="Toggle treble boost.")
async def filter_treble(ctx):
    await treble.callback(ctx)


@filter_group.command(name="echo", description="Toggle echo.")
async def filter_echo(ctx):
    await echo.callback(ctx)


@filter_group.command(name="karaoke", description="Toggle karaoke (vocal reduction).")
async def filter_karaoke(ctx):
    await karaoke.callback(ctx)


@filter_group.command(name="eightd", description="Toggle 8D spatial audio.")
async def filter_eightd(ctx):
    await eight_d.callback(ctx)


@filter_group.command(name="nightcore", description="Nightcore (faster + higher).")
async def filter_nightcore(ctx):
    await nightcore.callback(ctx)


@filter_group.command(name="vaporwave", description="Vaporwave (slower + lower).")
async def filter_vaporwave(ctx):
    await vaporwave.callback(ctx)


@filter_group.command(name="speed", description="Set playback speed (0.5–2.0).")
async def filter_speed(ctx, value: float):
    await speed.callback(ctx, value)


@filter_group.command(name="pitch", description="Set pitch (0.5–2.0).")
async def filter_pitch(ctx, value: float):
    await pitch.callback(ctx, value)


@filter_group.command(name="equalizer", description="Apply an EQ preset.")
@app_commands.describe(preset="rock, pop, bass, edm, jazz, classical, flat")
async def filter_equalizer(ctx, preset: str):
    await eq.callback(ctx, preset)


@filter_group.command(name="custom", description="Apply a custom ffmpeg EQ string.")
async def filter_custom(ctx, *, eq_string: str):
    await custom_eq.callback(ctx, eq_string=eq_string)


@filter_group.command(name="normalize", description="Toggle loudness normalization.")
async def filter_normalize(ctx):
    await normalize.callback(ctx)


@filter_group.command(name="reset", description="Clear all filters.")
async def filter_reset(ctx):
    await resetfilters.callback(ctx)


async def _eq_preset_autocomplete(interaction: discord.Interaction, current: str):
    cur_l = (current or "").lower()
    return [app_commands.Choice(name=p, value=p) for p in EQ_PRESETS if cur_l in p][:25]


filter_equalizer.autocomplete("preset")(_eq_preset_autocomplete)


# =========================
# /ai SUBCOMMANDS  (reuse existing AI callbacks)
# =========================
@ai_cmd.command(name="recommend", description="Get AI song recommendations for a mood/genre.")
async def ai_recommend(ctx, *, mood: str):
    await recommend.callback(ctx, mood=mood)


@ai_cmd.command(name="explain", description="Explain a song's themes/meaning.")
async def ai_explain(ctx, *, song: str = None):
    await explain_lyrics.callback(ctx, song=song)


@ai_cmd.command(name="translate", description="AI-translate text to another language.")
@app_commands.describe(language="Target language", text="Text to translate")
async def ai_translate(ctx, language: str, *, text: str):
    await translate.callback(ctx, payload=f"{language} | {text}")


@ai_cmd.command(name="playlist", description="Generate & save an AI playlist.")
@app_commands.describe(name="Name to save under", prompt="Describe the vibe")
async def ai_playlist(ctx, name: str, *, prompt: str):
    await playlist_ai.callback(ctx, name, prompt=prompt)


# =========================
# /assistant  — natural language → action
# =========================
async def _run_assistant(ctx, request):
    """Ask Gemini to map a natural-language request to a bot action, then run it."""
    if not ai_model:
        return await ctx.send("❌ Gemini isn't configured (missing GEMINI_API_KEY).")
    prompt = (
        "You are a Discord music bot controller. Map the user's request to ONE JSON "
        "object with keys 'action' and 'arg'. Valid actions: play, recommend, "
        "make_playlist, skip, stop, pause, resume, shuffle. "
        "For play/recommend/make_playlist put the search text or mood in 'arg'. "
        "For make_playlist, 'arg' is the vibe. Reply with ONLY the JSON.\n\n"
        f"Request: {request}"
    )
    async with ctx.typing():
        try:
            raw = await ask_gemini(prompt)
        except MusicError as e:
            return await ctx.send(f"❌ {e}")
    m = re.search(r"\{.*\}", raw, re.DOTALL)
    if not m:
        return await _ai_reply(ctx, request)  # fall back to plain chat
    try:
        plan = json.loads(m.group(0))
    except json.JSONDecodeError:
        return await _ai_reply(ctx, request)
    action = (plan.get("action") or "").lower()
    arg = plan.get("arg") or ""

    if action == "play" and arg:
        return await play.callback(ctx, query=arg)
    if action == "recommend" and arg:
        return await recommend.callback(ctx, mood=arg)
    if action == "make_playlist" and arg:
        return await playlist_ai.callback(ctx, "AI Mix", prompt=arg)
    if action == "skip":
        return await skip.callback(ctx)
    if action == "stop":
        return await stop.callback(ctx)
    if action == "pause":
        return await pause.callback(ctx)
    if action == "resume":
        return await resume.callback(ctx)
    if action == "shuffle":
        return await shuffle.callback(ctx)
    await _ai_reply(ctx, request)


@bot.hybrid_command(name="assistant", description="Ask in plain English; the bot does it.")
@app_commands.describe(request="e.g. 'play relaxing Nepali songs' or 'make a gym playlist'")
@commands.cooldown(1, 5, commands.BucketType.user)
async def assistant(ctx, *, request: str):
    await _run_assistant(ctx, request)


@ai_cmd.command(name="assistant", description="Ask in plain English; the bot does it.")
async def ai_assistant(ctx, *, request: str):
    await _run_assistant(ctx, request)


# =========================
# SLASH-SIDE ERROR HANDLER (prevents "Interaction Failed")
# =========================
@bot.tree.error
async def on_app_command_error(interaction: discord.Interaction, error):
    msg = "❌ Something went wrong."
    if isinstance(error, app_commands.CommandOnCooldown):
        msg = f"⏳ Slow down — try again in {error.retry_after:.1f}s"
    elif isinstance(error, app_commands.MissingPermissions):
        msg = "❌ You don't have permission to do that."
    else:
        log.exception("App command error", exc_info=error)
        msg = f"❌ Error: {error}"
    try:
        if interaction.response.is_done():
            await interaction.followup.send(msg, ephemeral=True)
        else:
            await interaction.response.send_message(msg, ephemeral=True)
    except discord.HTTPException:
        pass


# =========================
# EVENTS
# =========================
@bot.event
async def on_ready():
    log.info("Logged in as %s (%s guilds)", bot.user, len(bot.guilds))
    bot.add_view(MusicPanel())  # re-register persistent view after restart
    for guild in bot.guilds:
        load_queue(guild.id)
    if not autosave.is_running():
        autosave.start()
    if not live_progress_updater.is_running():
        live_progress_updater.start()
    try:
        synced = await bot.tree.sync()
        log.info("Synced %d slash command(s).", len(synced))
    except Exception:
        log.exception("Slash command sync failed")


@bot.event
async def on_voice_state_update(member, before, after):
    if member.id == bot.user.id:
        return
    vc = member.guild.voice_client
    if vc and vc.channel and len(vc.channel.members) == 1:
        await asyncio.sleep(30)
        vc = member.guild.voice_client
        if vc and vc.channel and len(vc.channel.members) == 1:
            get_queue(member.guild.id).clear()
            np_messages.pop(member.guild.id, None)
            await vc.disconnect()


@bot.event
async def on_command_error(ctx, error):
    if isinstance(error, commands.CommandOnCooldown):
        return await ctx.send(f"⏳ Slow down — try again in {error.retry_after:.1f}s")
    if isinstance(error, commands.MissingPermissions):
        return await ctx.send("❌ You don't have permission to do that.")
    if isinstance(error, commands.MissingRequiredArgument):
        return await ctx.send(f"❌ Missing argument: `{error.param.name}`")
    if isinstance(error, commands.BadArgument):
        return await ctx.send(f"❌ Bad argument: {error}")
    if isinstance(error, commands.CommandNotFound):
        return
    log.exception("Unhandled command error in %s", ctx.command, exc_info=error)
    await ctx.send(f"❌ Error: {error}")


# =========================
# SAFE SHUTDOWN
# =========================
def _shutdown(*_):
    log.info("Saving state before shutdown…")
    save_all_queues()
    conn.close()
    os._exit(0)


signal.signal(signal.SIGINT, _shutdown)
signal.signal(signal.SIGTERM, _shutdown)


# =========================
# ENTRYPOINT
# =========================
if __name__ == "__main__":
    bot.run(TOKEN)
