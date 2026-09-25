# MusicBot

Advanced Discord music bot with slash commands, queue controls, saved playlists, audio filters, lyrics, AI assistant routing, AI playlist tools, download helpers, and persistent stats.

## Features

- Slash and prefix commands for playback, queue, playlists, favorites, filters, lyrics, stats, and moderation helpers.
- Natural-language `/ai assistant` routing for common actions like playing songs, creating playlists, showing playlists, deleting playlists, notes, todos, reminders, weather, and utility commands.
- Persistent SQLite storage for queues, playlists, favorites, stats, notes, todos, reminders, and AI playlist history.
- FFmpeg audio playback with filters such as bassboost, treble, echo, karaoke, 8D, nightcore, vaporwave, speed, pitch, equalizer, and normalize.
- Gemini primary AI support with fallback support for Groq when configured.

## Requirements

- Python 3.11 or newer
- FFmpeg installed and available on `PATH`
- A Discord bot token
- Discord Developer Portal settings:
  - `MESSAGE CONTENT INTENT` enabled
  - `SERVER MEMBERS INTENT` enabled if you want member-related commands
  - Bot invited with voice, slash-command, and message permissions

## Setup

1. Clone the repository.

```powershell
git clone https://github.com/Aayushjoshi12/MusicBot.git
cd MusicBot
```

2. Create and activate a virtual environment.

```powershell
python -m venv botenv
.\botenv\Scripts\activate
```

3. Install dependencies.

```powershell
python -m pip install --upgrade pip
pip install -r requirements.txt
```

4. Install FFmpeg.

On Windows, install FFmpeg and add the `bin` folder to `PATH`. Confirm it works:

```powershell
ffmpeg -version
```

5. Create a `.env` file beside `bot.py`.

```env
DISCORD_TOKEN=your_discord_bot_token
GEMINI_API_KEY=your_gemini_api_key
GENIUS_TOKEN=your_genius_token
GROQ_API_KEY=your_groq_api_key
OWNER_ID=your_discord_user_id
OWNER_IDS=123456789012345678,987654321098765432
TEST_GUILD_ID=your_test_server_id
AUTO_GUILD_SYNC=1

# Optional
GEMINI_MODEL=gemini-2.5-flash
GEMINI_FALLBACK_MODEL=gemini-2.5-flash
GROQ_MODEL=openai/gpt-oss-120b
SPOTIFY_CLIENT_ID=your_spotify_client_id
SPOTIFY_CLIENT_SECRET=your_spotify_client_secret
RAPIDAPI_KEY=your_rapidapi_key
YTDLP_COOKIES_FILE=cookies.txt
```

Only `DISCORD_TOKEN` is required to start the bot. AI, lyrics, Spotify expansion, and weather-style helpers need their matching keys.

Do not commit `.env`.

## Run

```powershell
python bot.py
```

When the bot starts, it syncs slash commands. If global slash commands are slow to update, set `TEST_GUILD_ID` and keep `AUTO_GUILD_SYNC=1` while testing.

## Common Commands

Music:

```text
/play query:Never Gonna Give You Up
/pause
/resume
/skip
/nowplaying
/queue show
/queue search query:pehla
/volume value:50
```

Playlists:

```text
/playlist new name:Chill
/playlist add name:Chill song:Perfect Ed Sheeran
/playlist show name:Chill
/playlist play name:Chill
/playlist list
/playlist menu
```

AI assistant:

```text
/ai assistant request:play Never Gonna Give You Up by Rick Astley
/ai assistant request:create a playlist named Codex Audit Temp with the song Never Gonna Give You Up by Rick Astley
/ai assistant request:show me the playlist named Chill
/ai assistant request:delete the playlist named Codex Audit Temp
```

The create-playlist-with-song natural-language flow creates the playlist, adds the requested song, and plays that same song.

Lyrics and AI:

```text
/lyrics
/translatelyrics payload:Spanish | Pehla Nasha
/translate payload:Spanish | hello
/recommend mood:happy Nepali songs
/explain topic:what is a music queue
```

Filters:

```text
/filter status
/filter bassboost
/filter equalizer preset:rock
/filter reset
```

Stats and profile:

```text
/stats
/profile
/achievements
/mostplayed
/topartists
/toplisteners
```

## Prefix Commands

Most slash commands also have prefix versions using `!`, for example:

```text
!play Never Gonna Give You Up
!queue
!playlist list
!lyrics
!volume 50
```

## Data Files

The bot creates local SQLite files:

- `musicbot.db`
- `musicbot.db-shm`
- `musicbot.db-wal`

These store queues, playlists, favorites, stats, notes, todos, and reminders. They are runtime data and should not be committed.

## Troubleshooting

If no audio plays:

- Confirm FFmpeg is installed and on `PATH`.
- Confirm the bot is in a voice channel.
- Confirm the bot has `Connect` and `Speak` permissions.
- Try a different YouTube search query.

If slash commands look outdated:

- Restart the bot.
- Use a test guild with `TEST_GUILD_ID`.
- Run the bot with `AUTO_GUILD_SYNC=1`.

If lyrics are missing:

- Add `GENIUS_TOKEN` to `.env`.
- Try a cleaner song title without movie names, "lyrics", "official video", or extra artist text.

If YouTube blocks streams:

- Update `yt-dlp`.
- Add a cookies file and set `YTDLP_COOKIES_FILE=cookies.txt`.

If AI commands fail:

- Add `GEMINI_API_KEY` for Gemini.
- Add `GROQ_API_KEY` if you want Groq fallback.

## Safety Notes

- Keep `.env` private.
- Do not commit Discord tokens, API keys, cookies, or database files.
- Test destructive commands only on temporary test data.

