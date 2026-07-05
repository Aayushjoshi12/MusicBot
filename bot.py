"""
Discord Music Bot — Gemini AI + Advanced Playback
==================================================
Single, de-duplicated source file. Requires discord.py 2.x.

SETUP
-----
1. Create a `.env` file next to this script (never commit it):

    DISCORD_TOKEN=your_discord_bot_token
    GEMINI_API_KEY=your_gemini_api_key
    GENIUS_TOKEN=your_genius_token          # optional, for !lyrics

2. pip install -U discord.py yt-dlp PyNaCl aiohttp python-dotenv google-generativeai
3. Install ffmpeg and make sure it's on PATH.
4. python musicbot.py

NOTE ON SECRETS
----------------
Never hardcode tokens/keys in source. `os.getenv("DISCORD_TOKEN")` reads the
*value* of an environment variable named DISCORD_TOKEN — the token itself
belongs in your environment/.env file, not in the string passed to getenv().
"""

# =========================
# IMPORTS
# =========================
import asyncio
import json
import logging
import os
import random
import signal
import sqlite3
from functools import partial

import aiohttp
import discord
import yt_dlp
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

# =========================
# CONFIG (env vars only — no hardcoded secrets)
# =========================
load_dotenv()

TOKEN = os.getenv("DISCORD_TOKEN")
GEMINI_KEY = os.getenv("GEMINI_API_KEY")
GENIUS_TOKEN = os.getenv("GENIUS_TOKEN")

# Comma-separated list of Discord user IDs, e.g. OWNER_IDS=123456789012345678,987654321098765432
OWNER_IDS = {
    int(uid.strip())
    for uid in os.getenv("OWNER_IDS", "").split(",")
    if uid.strip().isdigit()
}

if not TOKEN:
    raise SystemExit("DISCORD_TOKEN is not set. Put it in your environment or a .env file.")

if GEMINI_KEY:
    genai.configure(api_key=GEMINI_KEY)
    # NOTE: model names change over time — check https://ai.google.dev/gemini-api/docs/models
    # for the current recommended flash/pro model if this one is retired.
    ai_model = genai.GenerativeModel("gemini-1.5-flash")
else:
    ai_model = None
    log.warning("GEMINI_API_KEY not set — AI commands will report an error until configured.")

intents = discord.Intents.default()
intents.message_content = True
intents.voice_states = True
intents.members = True

bot = commands.Bot(command_prefix="!", intents=intents, help_command=None)

# =========================
# DATABASE (SQLite)
# =========================
conn = sqlite3.connect("musicbot.db")
conn.execute("PRAGMA journal_mode=WAL")
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
""")
conn.commit()

# =========================
# GLOBAL STATE
# (names deliberately distinct from command names to avoid shadowing bugs)
# =========================
queues = {}            # guild_id -> list[song]
now_playing = {}        # guild_id -> song | None
repeat_mode = {}         # guild_id -> "off" | "song" | "queue"
autoplay_enabled = {}    # guild_id -> bool
audio_filters = {}       # guild_id -> dict of active filters
song_history = {}        # guild_id -> list[song]  (max 50)
search_cache = {}        # message/interaction scoped search results

MAX_HISTORY = 50


def get_queue(guild_id):
    return queues.setdefault(guild_id, [])


# =========================
# YT-DLP (run off the event loop — extract_info is blocking)
# =========================
YTDLP_BASE_OPTS = {
    "format": "bestaudio/best",
    "quiet": True,
    "noplaylist": False,
    "default_search": "ytsearch",
    "nocheckcertificate": True,
    "ignoreerrors": False,
}

FFMPEG_BASE_OPTS = {
    "before_options": "-reconnect 1 -reconnect_streamed 1 -reconnect_delay_max 5",
    "options": "-vn",
}


def _extract_info_sync(query, opts):
    with yt_dlp.YoutubeDL(opts) as ydl:
        return ydl.extract_info(query, download=False)


async def extract(query):
    """Resolve a single song (URL or search query). Raises MusicError on failure."""
    loop = asyncio.get_running_loop()
    try:
        info = await loop.run_in_executor(
            None, partial(_extract_info_sync, query, YTDLP_BASE_OPTS)
        )
    except yt_dlp.utils.DownloadError as e:
        raise MusicError(f"Couldn't find/stream that track: {e}") from e
    except Exception as e:
        raise MusicError(f"Unexpected error resolving track: {e}") from e

    if info is None:
        raise MusicError("No results found.")

    if "entries" in info:
        entries = [e for e in info["entries"] if e]
        if not entries:
            raise MusicError("No playable results found.")
        info = entries[0]

    return {
        "url": info.get("url"),
        "title": info.get("title", "Unknown title"),
        "webpage_url": info.get("webpage_url"),
        "thumbnail": info.get("thumbnail"),
        "duration": info.get("duration"),
    }


async def search_top(query, limit=10):
    """Return up to `limit` search results for a query."""
    loop = asyncio.get_running_loop()
    opts = dict(YTDLP_BASE_OPTS, default_search=f"ytsearch{limit}")
    try:
        data = await loop.run_in_executor(None, partial(_extract_info_sync, query, opts))
    except yt_dlp.utils.DownloadError as e:
        raise MusicError(f"Search failed: {e}") from e

    results = []
    for entry in (data.get("entries") or []):
        if not entry:
            continue
        results.append({
            "url": entry.get("url"),
            "title": entry.get("title", "Unknown title"),
            "webpage_url": entry.get("webpage_url"),
            "thumbnail": entry.get("thumbnail"),
            "duration": entry.get("duration"),
        })
    return results


class MusicError(Exception):
    """Raised for user-facing music/playback problems (bad URL, no results, etc.)."""


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
# AUDIO FILTERS
# =========================
FILTER_PRESETS = {
    "bassboost": "bass=g=12",
    "treble": "treble=g=8",
    "echo": "aecho=0.8:0.9:1000:0.3",
    "karaoke": "pan=stereo|c0=c0-c1|c1=c1-c0",
    "8d": "apulsator=hz=0.09",
}


def build_filter_chain(guild_id):
    f = audio_filters.get(guild_id, {})
    parts = []

    if f.get("speed"):
        parts.append(f"atempo={f['speed']}")
    if f.get("pitch"):
        parts.append(f"asetrate=44100*{f['pitch']},aresample=44100")
    for key, chain in FILTER_PRESETS.items():
        if f.get(key):
            parts.append(chain)

    return ",".join(parts) if parts else None


def create_source(url, guild_id):
    chain = build_filter_chain(guild_id)
    opts = dict(FFMPEG_BASE_OPTS)
    if chain:
        opts["options"] = f"-vn -af {chain}"
    return discord.FFmpegPCMAudio(url, **opts)


def set_filter(guild_id, **kwargs):
    audio_filters.setdefault(guild_id, {}).update(kwargs)


def reset_filters(guild_id):
    audio_filters[guild_id] = {}


# =========================
# VOICE HELPERS
# =========================
async def connect_vc(ctx):
    if ctx.voice_client:
        return ctx.voice_client

    if ctx.author.voice:
        try:
            return await ctx.author.voice.channel.connect(reconnect=True)
        except discord.ClientException as e:
            await ctx.send(f"❌ Couldn't join voice: {e}")
            return None

    await ctx.send("❌ Join a voice channel first!")
    return None


# =========================
# PLAYBACK CORE
# =========================
def progress_bar(current, total=10):
    current = max(0, min(total, current))
    return "█" * current + "─" * (total - current)


async def autoplay_fill(guild_id):
    """When queue is empty and autoplay is on, add a related track."""
    last = now_playing.get(guild_id)
    if not last:
        return
    try:
        results = await search_top(last["title"], limit=5)
        candidates = [r for r in results if r.get("url") != last.get("url")]
        if candidates:
            get_queue(guild_id).append(random.choice(candidates))
    except MusicError:
        pass


def add_history(guild_id, song):
    hist = song_history.setdefault(guild_id, [])
    hist.append(song)
    if len(hist) > MAX_HISTORY:
        hist.pop(0)


def record_stat(user_id, guild_id):
    cur.execute(
        """INSERT INTO stats (user_id, guild_id, songs_played) VALUES (?, ?, 1)
           ON CONFLICT(user_id, guild_id) DO UPDATE SET songs_played = songs_played + 1""",
        (user_id, guild_id),
    )
    conn.commit()


async def play_next(channel, guild):
    """Core playback loop. `channel` is where now-playing messages get sent."""
    guild_id = guild.id
    queue = get_queue(guild_id)
    vc = guild.voice_client

    if not vc:
        return

    if repeat_mode.get(guild_id) == "song" and now_playing.get(guild_id):
        queue.insert(0, now_playing[guild_id])
    elif repeat_mode.get(guild_id) == "queue" and now_playing.get(guild_id):
        queue.append(now_playing[guild_id])

    if not queue and autoplay_enabled.get(guild_id):
        await autoplay_fill(guild_id)

    if not queue:
        now_playing[guild_id] = None
        return

    song = queue.pop(0)
    now_playing[guild_id] = song
    add_history(guild_id, song)

    def after(err):
        if err:
            log.warning("Playback error in guild %s: %s", guild_id, err)
        fut = asyncio.run_coroutine_threadsafe(play_next(channel, guild), bot.loop)
        try:
            fut.result()
        except Exception:
            log.exception("Error advancing queue in guild %s", guild_id)

    try:
        source = create_source(song["url"], guild_id)
        source = discord.PCMVolumeTransformer(source, volume=get_volume(guild_id))
        vc.play(source, after=after)
    except Exception as e:
        log.exception("Failed to start playback in guild %s", guild_id)
        await channel.send(f"❌ Couldn't play **{song['title']}**: {e}")
        await play_next(channel, guild)
        return

    try:
        record_stat(getattr(channel, "_last_requester_id", 0) or 0, guild_id)
    except Exception:
        pass

    await send_now_playing(channel, guild)


async def send_now_playing(channel, guild):
    guild_id = guild.id
    song = now_playing.get(guild_id)
    if not song:
        return

    embed = discord.Embed(title="🎵 Now Playing", description=song["title"], color=discord.Color.green())
    embed.add_field(name="Progress", value=progress_bar(random.randint(2, 9)), inline=False)
    embed.add_field(name="Repeat", value=repeat_mode.get(guild_id, "off"), inline=True)
    embed.add_field(name="Autoplay", value=str(autoplay_enabled.get(guild_id, False)), inline=True)
    embed.add_field(name="Volume", value=f"{int(get_volume(guild_id) * 100)}%", inline=True)
    if song.get("thumbnail"):
        embed.set_thumbnail(url=song["thumbnail"])

    await channel.send(embed=embed, view=MusicPanel())


# =========================
# PERSISTENT NOW-PLAYING PANEL
# =========================
class MusicPanel(discord.ui.View):
    def __init__(self):
        super().__init__(timeout=None)

    @discord.ui.button(label="⏸", style=discord.ButtonStyle.gray, custom_id="panel:pause")
    async def pause(self, interaction: discord.Interaction, button):
        vc = interaction.guild.voice_client
        if vc and vc.is_playing():
            vc.pause()
        await interaction.response.send_message("⏸ Paused", ephemeral=True)

    @discord.ui.button(label="▶", style=discord.ButtonStyle.green, custom_id="panel:resume")
    async def resume(self, interaction: discord.Interaction, button):
        vc = interaction.guild.voice_client
        if vc and vc.is_paused():
            vc.resume()
        await interaction.response.send_message("▶ Resumed", ephemeral=True)

    @discord.ui.button(label="⏭", style=discord.ButtonStyle.blurple, custom_id="panel:skip")
    async def skip(self, interaction: discord.Interaction, button):
        vc = interaction.guild.voice_client
        if vc and (vc.is_playing() or vc.is_paused()):
            vc.stop()
        await interaction.response.send_message("⏭ Skipped", ephemeral=True)

    @discord.ui.button(label="⏹", style=discord.ButtonStyle.red, custom_id="panel:stop")
    async def stop(self, interaction: discord.Interaction, button):
        vc = interaction.guild.voice_client
        if vc:
            get_queue(interaction.guild.id).clear()
            vc.stop()
        await interaction.response.send_message("⏹ Stopped", ephemeral=True)

    @discord.ui.button(label="🔀", style=discord.ButtonStyle.gray, custom_id="panel:shuffle")
    async def shuffle(self, interaction: discord.Interaction, button):
        random.shuffle(get_queue(interaction.guild.id))
        await interaction.response.send_message("🔀 Queue shuffled", ephemeral=True)

    @discord.ui.button(label="🔁", style=discord.ButtonStyle.gray, custom_id="panel:repeat")
    async def repeat(self, interaction: discord.Interaction, button):
        gid = interaction.guild.id
        order = ["off", "song", "queue"]
        current = repeat_mode.get(gid, "off")
        repeat_mode[gid] = order[(order.index(current) + 1) % len(order)]
        await interaction.response.send_message(f"🔁 Repeat: {repeat_mode[gid]}", ephemeral=True)

    @discord.ui.button(label="🎶", style=discord.ButtonStyle.gray, custom_id="panel:autoplay")
    async def autoplay_btn(self, interaction: discord.Interaction, button):
        gid = interaction.guild.id
        autoplay_enabled[gid] = not autoplay_enabled.get(gid, False)
        await interaction.response.send_message(f"🎶 Autoplay: {autoplay_enabled[gid]}", ephemeral=True)

    @discord.ui.button(label="❤️", style=discord.ButtonStyle.red, custom_id="panel:favorite")
    async def favorite(self, interaction: discord.Interaction, button):
        song = now_playing.get(interaction.guild.id)
        if not song:
            return await interaction.response.send_message("Nothing is playing", ephemeral=True)
        cur.execute(
            "INSERT OR IGNORE INTO user_favorites (user_id, url, title) VALUES (?, ?, ?)",
            (interaction.user.id, song["url"], song["title"]),
        )
        conn.commit()
        await interaction.response.send_message("❤️ Added to your favorites", ephemeral=True)


# =========================
# SEARCH RESULTS UI
# =========================
class SearchView(discord.ui.View):
    def __init__(self, results, requester_id):
        super().__init__(timeout=60)
        self.results = results
        self.requester_id = requester_id

        options = [
            discord.SelectOption(label=r["title"][:100], value=str(i))
            for i, r in enumerate(results)
        ]
        self.select.options = options

    @discord.ui.select(placeholder="Choose a song...")
    async def select(self, interaction: discord.Interaction, select: discord.ui.Select):
        if interaction.user.id != self.requester_id:
            return await interaction.response.send_message("This search isn't yours.", ephemeral=True)

        song = self.results[int(select.values[0])]
        get_queue(interaction.guild.id).append(song)

        await interaction.response.edit_message(
            content=f"➕ Added: **{song['title']}**", embed=None, view=None
        )

        vc = interaction.guild.voice_client
        if vc and not vc.is_playing():
            await play_next(interaction.channel, interaction.guild)


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
        desc = "\n".join(f"{start + i + 1}. {s['title']}" for i, s in enumerate(chunk)) or "Empty"
        embed = discord.Embed(
            title=f"📜 Queue (page {self.page + 1}/{self.max_page() + 1})",
            description=desc,
            color=discord.Color.purple(),
        )
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
# HELP UI
# =========================
HELP_PAGES = {
    "music": "!play <song/url>\n!queue\n!skip\n!stop\n!pause\n!resume\n!volume <0-200>\n!volumeui\n!loop <song|queue|off>\n!history",
    "filters": "!bassboost\n!treble\n!echo\n!karaoke\n!eightd\n!nightcore\n!vaporwave\n!speed <0.5-2.0>\n!pitch <0.5-2.0>\n!resetfilters",
    "ai": "!ai / !chat / !ask <prompt> — general Gemini chat\n!summarize <text or reply>\n!translate <lang> | <text>\n!code <request>\n!review (reply to code)\n!explain <topic or reply>\n!explainlyrics <song>\n!recommend <mood/genre>",
    "favorites": "!favorite — save current song\n!favorites — list your saved songs",
    "moderation": "!kick <member> [reason]\n!ban <member> [reason]\n!clear <amount>\n!warn <member> [reason]",
    "utility": "!ping\n!avatar [member]\n!serverinfo\n!github <user>\n!weather <city>",
    "fun": "!coinflip\n!dice\n!eightball <question>",
    "system": "!help\n!maintenance <on|off> (owner)\n!restart (owner)",
}


class HelpView(discord.ui.View):
    def __init__(self):
        super().__init__(timeout=120)

    @discord.ui.select(
        placeholder="Choose a category",
        options=[discord.SelectOption(label=k.title(), value=k) for k in HELP_PAGES],
    )
    async def menu(self, interaction: discord.Interaction, select: discord.ui.Select):
        key = select.values[0]
        embed = discord.Embed(title=f"📖 {key.title()} Commands", description=HELP_PAGES[key], color=discord.Color.gold())
        await interaction.response.edit_message(embed=embed, view=self)


# =========================
# MUSIC COMMANDS
# =========================
@bot.command()
@commands.cooldown(1, 3, commands.BucketType.user)
async def play(ctx, *, query):
    vc = await connect_vc(ctx)
    if not vc:
        return

    if "spotify.com" in query:
        query = "ytsearch:" + query  # basic Spotify fallback: search by pasted title/URL text

    async with ctx.typing():
        try:
            results = await search_top(query, limit=10)
        except MusicError as e:
            return await ctx.send(f"❌ {e}")

    if not results:
        return await ctx.send("❌ No results found.")

    if len(results) > 1:
        view = SearchView(results, ctx.author.id)
        embed = discord.Embed(title="🔎 Select a song", description="Choose from the results below", color=discord.Color.blue())
        return await ctx.send(embed=embed, view=view)

    song = results[0]
    get_queue(ctx.guild.id).append(song)
    await ctx.send(f"➕ Added: **{song['title']}**")

    if not vc.is_playing() and not vc.is_paused():
        await play_next(ctx.channel, ctx.guild)


@bot.command()
async def skip(ctx):
    vc = ctx.voice_client
    if vc and (vc.is_playing() or vc.is_paused()):
        vc.stop()
        await ctx.send("⏭ Skipped")
    else:
        await ctx.send("Nothing is playing.")


@bot.command()
async def stop(ctx):
    vc = ctx.voice_client
    if vc:
        get_queue(ctx.guild.id).clear()
        vc.stop()
        await ctx.send("⏹ Stopped and cleared queue")
    else:
        await ctx.send("Not connected.")


@bot.command()
async def pause(ctx):
    vc = ctx.voice_client
    if vc and vc.is_playing():
        vc.pause()
        await ctx.send("⏸ Paused")
    else:
        await ctx.send("Nothing is playing.")


@bot.command()
async def resume(ctx):
    vc = ctx.voice_client
    if vc and vc.is_paused():
        vc.resume()
        await ctx.send("▶ Resumed")
    else:
        await ctx.send("Nothing is paused.")


@bot.command()
async def queue(ctx):
    q = get_queue(ctx.guild.id)
    if not q:
        return await ctx.send("Queue is empty.")
    view = QueueView(ctx.guild.id)
    await ctx.send(embed=view.render(), view=view)


@bot.command(name="loop")
async def loop_cmd(ctx, mode: str):
    mode = mode.lower()
    if mode not in ("song", "queue", "off"):
        return await ctx.send("Usage: `!loop song|queue|off`")
    repeat_mode[ctx.guild.id] = mode
    await ctx.send(f"🔁 Repeat mode: **{mode}**")


@bot.command()
async def history(ctx):
    hist = song_history.get(ctx.guild.id, [])
    if not hist:
        return await ctx.send("No history yet.")
    msg = "\n".join(s["title"] for s in hist[-10:])
    await ctx.send(f"📜 Recently played:\n{msg}")


# =========================
# VOLUME
# =========================
@bot.command()
async def volume(ctx, value: int):
    if not 0 <= value <= 200:
        return await ctx.send("❌ Range: 0–200")
    vol = set_volume(ctx.guild.id, value / 100)
    if ctx.voice_client and ctx.voice_client.source:
        ctx.voice_client.source.volume = vol
    await ctx.send(f"🔊 Volume set to **{value}%**")


@bot.command()
async def volumeui(ctx):
    await ctx.send("🎚 Volume Control", view=VolumeView())


# =========================
# AUDIO FILTERS
# (each restarts the current song so the new ffmpeg filter chain applies)
# =========================
async def _restart_current(ctx):
    vc = ctx.voice_client
    if vc and (vc.is_playing() or vc.is_paused()):
        song = now_playing.get(ctx.guild.id)
        if song:
            get_queue(ctx.guild.id).insert(0, song)
        vc.stop()  # triggers `after` -> play_next, which will pick the reinserted song back up


@bot.command()
async def bassboost(ctx):
    set_filter(ctx.guild.id, bassboost=True)
    await ctx.send("🔊 Bass boost enabled")
    await _restart_current(ctx)


@bot.command()
async def treble(ctx):
    set_filter(ctx.guild.id, treble=True)
    await ctx.send("🎻 Treble boost enabled")
    await _restart_current(ctx)


@bot.command()
async def echo(ctx):
    set_filter(ctx.guild.id, echo=True)
    await ctx.send("🎧 Echo enabled")
    await _restart_current(ctx)


@bot.command()
async def karaoke(ctx):
    set_filter(ctx.guild.id, karaoke=True)
    await ctx.send("🎤 Karaoke (vocal reduction) enabled")
    await _restart_current(ctx)


@bot.command(name="eightd")
async def eight_d(ctx):
    set_filter(ctx.guild.id, **{"8d": True})
    await ctx.send("🌀 8D audio enabled")
    await _restart_current(ctx)


@bot.command()
async def nightcore(ctx):
    set_filter(ctx.guild.id, speed=1.25, pitch=1.25)
    await ctx.send("⚡ Nightcore enabled")
    await _restart_current(ctx)


@bot.command()
async def vaporwave(ctx):
    set_filter(ctx.guild.id, speed=0.8, pitch=0.8)
    await ctx.send("🌴 Vaporwave enabled")
    await _restart_current(ctx)


@bot.command()
async def speed(ctx, value: float):
    if not 0.5 <= value <= 2.0:
        return await ctx.send("Range: 0.5–2.0")
    set_filter(ctx.guild.id, speed=value)
    await ctx.send(f"⏩ Speed set to {value}")
    await _restart_current(ctx)


@bot.command()
async def pitch(ctx, value: float):
    if not 0.5 <= value <= 2.0:
        return await ctx.send("Range: 0.5–2.0")
    set_filter(ctx.guild.id, pitch=value)
    await ctx.send(f"🎵 Pitch set to {value}")
    await _restart_current(ctx)


@bot.command()
async def resetfilters(ctx):
    reset_filters(ctx.guild.id)
    await ctx.send("🧹 Filters cleared")
    await _restart_current(ctx)


# =========================
# FAVORITES (single SQLite-backed source of truth)
# =========================
@bot.command()
async def favorite(ctx):
    song = now_playing.get(ctx.guild.id)
    if not song:
        return await ctx.send("Nothing is playing.")
    cur.execute(
        "INSERT OR IGNORE INTO user_favorites (user_id, url, title) VALUES (?, ?, ?)",
        (ctx.author.id, song["url"], song["title"]),
    )
    conn.commit()
    await ctx.send("❤️ Added to favorites")


@bot.command()
async def favorites(ctx):
    cur.execute("SELECT title FROM user_favorites WHERE user_id=? LIMIT 10", (ctx.author.id,))
    rows = cur.fetchall()
    if not rows:
        return await ctx.send("No favorites yet.")
    await ctx.send("❤️ Favorites:\n" + "\n".join(r[0] for r in rows))


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


@bot.command(name="ai", aliases=["chat", "ask"])
@commands.cooldown(1, 5, commands.BucketType.user)
async def ai_cmd(ctx, *, prompt):
    await _ai_reply(ctx, prompt)


@bot.command()
async def summarize(ctx, *, text=None):
    if not text and ctx.message.reference:
        ref = await ctx.channel.fetch_message(ctx.message.reference.message_id)
        text = ref.content
    if not text:
        return await ctx.send("Provide text, or reply to a message with `!summarize`.")
    await _ai_reply(ctx, f"Summarize the following concisely:\n\n{text}")


@bot.command()
async def translate(ctx, *, payload):
    if "|" not in payload:
        return await ctx.send("Usage: `!translate <language> | <text>`")
    lang, text = payload.split("|", 1)
    await _ai_reply(ctx, f"Translate the following text to {lang.strip()}:\n\n{text.strip()}")


@bot.command(name="code")
async def code_cmd(ctx, *, request):
    await _ai_reply(ctx, f"Write code for this request. Include brief explanation:\n\n{request}")


@bot.command()
async def review(ctx, *, code=None):
    if not code and ctx.message.reference:
        ref = await ctx.channel.fetch_message(ctx.message.reference.message_id)
        code = ref.content
    if not code:
        return await ctx.send("Provide code, or reply to a code message with `!review`.")
    await _ai_reply(ctx, f"Review this code for bugs and improvements:\n\n{code}")


@bot.command()
async def explain(ctx, *, topic=None):
    if not topic and ctx.message.reference:
        ref = await ctx.channel.fetch_message(ctx.message.reference.message_id)
        topic = ref.content
    if not topic:
        return await ctx.send("Provide a topic, or reply to a message with `!explain`.")
    await _ai_reply(ctx, f"Explain this clearly and simply:\n\n{topic}")


@bot.command(name="explainlyrics")
async def explain_lyrics(ctx, *, song=None):
    song = song or (now_playing.get(ctx.guild.id) or {}).get("title")
    if not song:
        return await ctx.send("No song specified and nothing is playing.")
    await _ai_reply(ctx, f"Give a general, non-verbatim explanation of the themes and meaning of the song '{song}'. Do not quote lyrics directly.")


@bot.command()
async def recommend(ctx, *, mood):
    await _ai_reply(ctx, f"Suggest 8 songs (title + artist) that fit this mood/genre: {mood}. Format as a simple numbered list.")


# =========================
# LYRICS (Genius metadata lookup — no lyric reproduction)
# =========================
async def genius_lookup(song_name):
    if not GENIUS_TOKEN:
        return None
    headers = {"Authorization": f"Bearer {GENIUS_TOKEN}"}
    async with aiohttp.ClientSession() as session:
        async with session.get(
            "https://api.genius.com/search", params={"q": song_name}, headers=headers
        ) as r:
            data = await r.json()
    try:
        hit = data["response"]["hits"][0]["result"]
        return f"{hit['title']} — {hit['primary_artist']['name']}\n{hit['url']}"
    except (KeyError, IndexError):
        return None


@bot.command()
async def lyrics(ctx, *, song=None):
    song = song or (now_playing.get(ctx.guild.id) or {}).get("title")
    if not song:
        return await ctx.send("No song specified and nothing is playing.")

    result = await genius_lookup(song)
    if result:
        await ctx.send(f"🎼 Found on Genius:\n{result}")
    else:
        await ctx.send("Couldn't find that on Genius. Try `!explainlyrics` for a themes/meaning summary instead.")


# =========================
# STATS
# =========================
@bot.command()
async def stats(ctx, member: discord.Member = None):
    member = member or ctx.author
    cur.execute(
        "SELECT songs_played FROM stats WHERE user_id=? AND guild_id=?",
        (member.id, ctx.guild.id),
    )
    row = cur.fetchone()
    played = row[0] if row else 0
    await ctx.send(f"🎧 {member.display_name} has played **{played}** songs in this server.")


# =========================
# MODERATION
# =========================
@bot.command()
@commands.has_permissions(kick_members=True)
async def kick(ctx, member: discord.Member, *, reason=None):
    await member.kick(reason=reason)
    await ctx.send(f"👢 Kicked {member}")


@bot.command()
@commands.has_permissions(ban_members=True)
async def ban(ctx, member: discord.Member, *, reason=None):
    await member.ban(reason=reason)
    await ctx.send(f"🔨 Banned {member}")


@bot.command()
@commands.has_permissions(manage_messages=True)
async def clear(ctx, amount: int):
    deleted = await ctx.channel.purge(limit=amount)
    await ctx.send(f"🧹 Deleted {len(deleted)} messages", delete_after=3)


@bot.command()
@commands.has_permissions(moderate_members=True)
async def warn(ctx, member: discord.Member, *, reason="No reason given"):
    await ctx.send(f"⚠️ {member.mention} warned: {reason}")


# =========================
# UTILITY
# =========================
@bot.command()
async def ping(ctx):
    await ctx.send(f"🏓 Pong: {round(bot.latency * 1000)}ms")


@bot.command()
async def avatar(ctx, member: discord.Member = None):
    member = member or ctx.author
    await ctx.send(member.display_avatar.url)


@bot.command()
async def serverinfo(ctx):
    guild = ctx.guild
    embed = discord.Embed(title=guild.name, color=discord.Color.blurple())
    embed.add_field(name="Members", value=guild.member_count)
    embed.add_field(name="Owner", value=str(guild.owner))
    embed.add_field(name="Created", value=discord.utils.format_dt(guild.created_at, "D"))
    await ctx.send(embed=embed)


@bot.command()
@commands.cooldown(1, 5, commands.BucketType.user)
async def github(ctx, user):
    async with aiohttp.ClientSession() as session:
        async with session.get(f"https://api.github.com/users/{user}") as r:
            if r.status != 200:
                return await ctx.send("❌ User not found.")
            data = await r.json()

    embed = discord.Embed(title=data.get("login"), url=data.get("html_url"), color=discord.Color.dark_grey())
    embed.add_field(name="Repos", value=data.get("public_repos"))
    embed.add_field(name="Followers", value=data.get("followers"))
    await ctx.send(embed=embed)


@bot.command()
@commands.cooldown(1, 10, commands.BucketType.user)
async def weather(ctx, *, city):
    async with aiohttp.ClientSession() as session:
        async with session.get(f"https://wttr.in/{city}?format=3") as r:
            data = await r.text()
    await ctx.send(f"🌤 {data.strip()}")


# =========================
# FUN
# =========================
@bot.command()
async def coinflip(ctx):
    await ctx.send(random.choice(["🪙 Heads", "🪙 Tails"]))


@bot.command()
async def dice(ctx):
    await ctx.send(f"🎲 {random.randint(1, 6)}")


@bot.command()
async def eightball(ctx, *, question):
    responses = ["Yes", "No", "Maybe", "Absolutely", "Never", "Ask again later"]
    await ctx.send(f"🎱 {random.choice(responses)}")


# =========================
# HELP
# =========================
@bot.command()
async def help(ctx):
    embed = discord.Embed(
        title="🎧 Ultimate Bot Help",
        description="Select a category below 👇",
        color=discord.Color.gold(),
    )
    await ctx.send(embed=embed, view=HelpView())


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


@bot.command()
async def maintenance(ctx, mode: str):
    if not is_owner(ctx):
        return await ctx.send("Owner only.")
    bot.maintenance = mode.lower() == "on"
    await ctx.send(f"🔧 Maintenance mode: {mode}")


@bot.command()
async def restart(ctx):
    if not is_owner(ctx):
        return await ctx.send("Owner only.")
    await ctx.send("♻ Restarting...")
    save_all_queues()
    os._exit(0)


# =========================
# PERSISTENCE (JSON, not eval — safe to load untrusted-looking data)
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


@bot.event
async def on_voice_state_update(member, before, after):
    """Auto-disconnect when left alone in a voice channel."""
    if member.id == bot.user.id:
        return
    vc = member.guild.voice_client
    if vc and vc.channel and len(vc.channel.members) == 1:
        await asyncio.sleep(30)
        vc = member.guild.voice_client  # re-check after the wait
        if vc and vc.channel and len(vc.channel.members) == 1:
            get_queue(member.guild.id).clear()
            await vc.disconnect()


@bot.event
async def on_command_error(ctx, error):
    if isinstance(error, commands.CommandOnCooldown):
        return await ctx.send(f"⏳ Slow down — try again in {error.retry_after:.1f}s")
    if isinstance(error, commands.MissingPermissions):
        return await ctx.send("❌ You don't have permission to do that.")
    if isinstance(error, commands.MissingRequiredArgument):
        return await ctx.send(f"❌ Missing argument: `{error.param.name}`")
    if isinstance(error, commands.CommandNotFound):
        return  # silently ignore unknown commands
    log.exception("Unhandled command error in %s", ctx.command, exc_info=error)
    await ctx.send(f"❌ Error: {error}")


# =========================
# SAFE SHUTDOWN
# =========================
def _shutdown(*_):
    log.info("Saving state before shutdown...")
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