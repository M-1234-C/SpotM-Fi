import pygame
import gc
import sys
import os
import io
import uuid
import tempfile
import time
import math
import random
import json
import re
import threading
import urllib.request
import urllib.parse
import urllib.error
import webbrowser
import datetime
import socket
import difflib

# --- NETWORK FIX: force IPv4-only DNS resolution ---
# On some Android devices, Python's socket.getaddrinfo() (used internally by
# every urllib.request.urlopen call) fails with:
#   URLError: <urlopen error [Errno 7] No address associated with hostname>
# even for perfectly valid, reachable domains (e.g. lrclib.net) and with a
# working internet connection. This happens because the default lookup mode
# (AF_UNSPEC) asks for both IPv4 and IPv6 addresses, and some devices'
# network stacks return an empty/invalid result for the IPv6 half, which
# getaddrinfo treats as a hard failure instead of falling back to IPv4.
# Forcing AF_INET-only resolution app-wide avoids this entirely.
_original_getaddrinfo = socket.getaddrinfo
def _ipv4_only_getaddrinfo(host, port, family=0, type=0, proto=0, flags=0):
    return _original_getaddrinfo(host, port, socket.AF_INET, type, proto, flags)
socket.getaddrinfo = _ipv4_only_getaddrinfo

# --- NETWORK FIX: SSL certificate verification on Android ---
# Android has no system CA certificate bundle that Python's ssl module can
# find on its own, so every single HTTPS request (lyrics search, album art
# search, Top 100 chart data, etc.) fails with:
#   URLError: <urlopen error [SSL: CERTIFICATE_VERIFY_FAILED] certificate
#   verify failed (_ssl.c:1007)>
# even though the connection itself works fine. certifi ships its own
# up-to-date CA bundle as a plain file, so pointing Python's default HTTPS
# context at that fixes verification for every urlopen() call app-wide.
try:
    import ssl
    import certifi
    ssl._create_default_https_context = lambda: ssl.create_default_context(cafile=certifi.where())
except Exception:
    pass

# --- BACKGROUND PLAYBACK: don't let SDL pause audio / freeze the main loop
# when the app is backgrounded (screen locked, user switches app, etc.) ---
# By default, SDL's Android activity pauses BOTH audio playback and the main
# thread the moment the app loses focus. That's fine for a game, but it's
# exactly why music used to just stop instead of continuing (and finished
# tracks never advanced to the next one) once the screen turned off or the
# app was minimized. These hints must be set before pygame.init() opens the
# audio device / activity.
os.environ.setdefault("SDL_ANDROID_BLOCK_ON_PAUSE_PAUSEAUDIO", "0")  # keep playing audio in the background
os.environ.setdefault("SDL_ANDROID_BLOCK_ON_PAUSE", "0")             # keep the main loop (and therefore auto-advance-to-next-track) running in the background

# --- WINDOW & SCALING CONFIGURATION ---
pygame.mixer.pre_init(44100, -16, 2, 2048)
pygame.init()
pygame.mixer.init()
pygame.font.init()
gc.disable()

# --- PLATFORM DETECTION (Android vs PC/desktop) ---
# Used below to decide fullscreen-locked (Android) vs a normal resizable
# window (PC) at startup, and again on window resize.
def _detect_is_android():
    try:
        from jnius import autoclass
        autoclass('org.libsdl.app.SDLActivity')
        return True
    except Exception:
        pass
    try:
        import android  # noqa: F401
        return True
    except Exception:
        pass
    return False

IS_ANDROID = _detect_is_android()

# Debug reveal: hidden by default. Press F5 to toggle back on — shows the
# Phone / Desktop-Tablet layout buttons in Settings again, plus a live FPS
# counter in the top-left corner. Press F5 again to hide both.
_debug_reveal = False

info = pygame.display.Info()
if IS_ANDROID:
    REAL_WIDTH, REAL_HEIGHT = info.current_w, info.current_h
else:
    # PC/desktop: open as a normal window that always starts at 1080p,
    # instead of fullscreen at the monitor's native resolution.
    REAL_WIDTH, REAL_HEIGHT = 1920, 1080

# Set (from a background/Android callback thread) when the user grants
# storage permission after app start; the main loop checks this each frame
# and does the actual library rescan on the main thread — see
# request_android_permissions() / _on_permissions_result() below.
_permissions_just_granted = False
_wake_lock_obj = None  # lazily created by _get_wake_lock() the first time playback starts

# --- FIRST-LAUNCH ONBOARDING ---
# Shown once, ever, on the very first time the app is opened (persisted via
# "onboarding_complete" in the save file so it never appears again after
# that). Three stages: a green animated welcome screen, then a notifications
# permission step, then a storage/files permission step. onboarding_stage is
# None once the flow is finished or on any later launch.
onboarding_complete = False
onboarding_stage = None            # None | "welcome" | "notifications" | "storage" | "folder" | "scrape"
onboarding_anim_start = 0.0        # time.time() when the current stage started, for animation
onboarding_button_rect = pygame.Rect(0, 0, 0, 0)   # set fresh each frame by draw_onboarding_overlay()
onboarding_button_rect_2 = pygame.Rect(0, 0, 0, 0) # second button on two-button stages (e.g. "scrape" Yes/No)
onboarding_skip_rect = pygame.Rect(0, 0, 0, 0)     # "Skip" link on the "folder" stage
onboarding_awaiting_folder = False  # True while the storage browser is open on behalf of the "folder" onboarding stage
onboarding_awaiting_permission = False  # True while the "notifications"/"storage" onboarding screens are waiting on an actual OS permission result before advancing
_notification_permission_result = None  # None=waiting/not asked yet, True=granted (or nothing to ask), False=denied
_storage_legacy_perm_done = False       # True once the READ/WRITE_EXTERNAL_STORAGE runtime dialog has been answered (or there was nothing to ask)
_manage_storage_intent_launched = False # True once we've launched the Android 11+ "All files access" settings screen for the current request, so we only launch it once
auto_scrape_media = None            # None (never asked) | True | False - user's answer on the "scrape" onboarding stage
onboarding_scrape_active = False    # True while the background art/lyrics scrape kicked off from onboarding is running
onboarding_scrape_progress = (0, 0) # (done, total) tracks processed by the onboarding scrape
_onboarding_hover_smooth = {}       # per-button eased hover amount (0..1), keyed by a label string, for smooth color/scale transitions
_onboarding_bar_disp = 0.0          # smoothed/animated display value of the scrape progress bar (chases onboarding_scrape_progress)


try:
    DEVICE_REFRESH_RATE = info.refresh_rate
    # Sanity clamp, not just a zero-check: some phones (mainly ones with
    # LTPO/"adaptive refresh" OLED panels - common on flagship Pixel/Samsung
    # models) can report back whatever low refresh rate the panel happens to
    # be idling at when this is queried at cold start (these panels drop as
    # low as 1-10Hz to save battery on static content), not the panel's real
    # max rate. Since clock.tick_busy_loop(DEVICE_REFRESH_RATE) below uses
    # this value to deliberately CAP the render loop to match it, a bad
    # early reading doesn't just "run a bit slow" - it locks the entire app
    # to that low number for the whole session, which is exactly a solid,
    # unmoving low FPS regardless of how much CPU/GPU headroom the device
    # actually has. Gaming-phone panels (e.g. Red Magic) are typically fixed
    # high-refresh, not LTPO, so they never hit this and always report their
    # real rate - which is why the same code runs fine there. Treat any
    # reading under 30 as bogus and fall back to a safe 60 floor.
    if DEVICE_REFRESH_RATE < 30:
        DEVICE_REFRESH_RATE = 60
except:
    DEVICE_REFRESH_RATE = 60

# --- PORTRAIT & SENSOR ORIENTATION ENGINE ---
# Lock/unlock device orientation on Android. Pygame on Android (incl. Pydroid 3) runs
# on top of SDL2, whose activity class is org.libsdl.app.SDLActivity — not Kivy's
# PythonActivity. We try SDLActivity first (correct for pygame/Pydroid), then fall
# back to PythonActivity in case of a Kivy/python-for-android build.
def set_android_orientation(portrait_locked):
    # 1 = SCREEN_ORIENTATION_PORTRAIT (locked), 4 = SCREEN_ORIENTATION_SENSOR (auto-rotate)
    target = 1 if portrait_locked else 4
    try:
        from jnius import autoclass
        SDLActivity = autoclass('org.libsdl.app.SDLActivity')
        activity = SDLActivity.mSingleton if hasattr(SDLActivity, 'mSingleton') else SDLActivity.mActivity
        activity.setRequestedOrientation(target)
        return
    except Exception:
        pass
    try:
        from jnius import autoclass
        PythonActivity = autoclass('org.kivy.android.PythonActivity')
        PythonActivity.mActivity.setRequestedOrientation(target)
    except Exception:
        pass

set_android_orientation(False)  # default: sensor/auto-rotate

# --- SUSTAINED PERFORMANCE MODE ---
# Window.setSustainedPerformanceMode(true) is a standard Android API (24+)
# meant for apps like games/media players that need stable frame timing: it
# asks the OS to keep CPU clocks steady during sustained load instead of
# aggressively scaling them down/up, which is the actual bottleneck behind
# low FPS on some devices/power profiles. It's a request, not a guarantee -
# the OS/vendor skin decides how much to honor it, and it silently does
# nothing on devices/API levels that don't support it. No-ops harmlessly on
# desktop. Isolated on purpose: doesn't touch rendering, display mode, or
# anything else, so it's trivial to remove if it doesn't help.
def set_android_sustained_performance_mode():
    try:
        from jnius import autoclass
        SDLActivity = autoclass('org.libsdl.app.SDLActivity')
        activity = SDLActivity.mSingleton if hasattr(SDLActivity, 'mSingleton') else SDLActivity.mActivity
        activity.getWindow().setSustainedPerformanceMode(True)
        return
    except Exception:
        pass
    try:
        from jnius import autoclass
        PythonActivity = autoclass('org.kivy.android.PythonActivity')
        PythonActivity.mActivity.getWindow().setSustainedPerformanceMode(True)
    except Exception:
        pass

set_android_sustained_performance_mode()

# --- MAIN-THREAD SCHEDULING PRIORITY BOOST ---
# The symptom this fixes: low FPS on stock devices (Pixel, Samsung, etc.)
# even though CPU/GPU usage looks low, while it runs fine on devices that
# let you manually lock CPU clocks high (e.g. Red Magic's game-mode clock
# boost). That's the signature of the stock "schedutil" CPU governor: it
# picks clock speed from measured utilization of a thread, and this app's
# per-frame work is short/bursty rather than sustained, so the governor
# never sees enough load to ramp clocks up in time for each frame's
# ~16-33ms budget. A manual clock lock bypasses the governor entirely,
# which is why that "fixes" it on devices that expose the option - but
# most devices don't expose it, so the fix has to come from the app side.
# Raising this thread's Android scheduling priority to
# THREAD_PRIORITY_URGENT_DISPLAY - the same class Android gives its own
# UI/render thread - tells schedutil to treat it as an urgent/display
# workload and boost clocks for it accordingly, without needing root or
# any vendor-specific API. It's a request, not a guarantee - the OS still
# decides how much to honor it - and it silently does nothing on
# non-Android platforms. Isolated on purpose: doesn't touch rendering,
# display mode, or anything else, so it's trivial to remove if it doesn't
# help.
def set_android_thread_priority_urgent_display():
    try:
        from jnius import autoclass
        Process = autoclass('android.os.Process')
        Process.setThreadPriority(Process.THREAD_PRIORITY_URGENT_DISPLAY)
    except Exception:
        pass

set_android_thread_priority_urgent_display()

# --- ANDROID RUNTIME PERMISSIONS ---
# Listing permissions in buildozer.spec only adds them to the manifest — on
# Android 6+ (API 23+) the app must also ASK for "dangerous" permissions
# (storage, notifications) at runtime, or the OS silently denies them even
# though they're declared. This must run before any file/music-library access.
def request_android_permissions():
    try:
        from android.permissions import Permission, request_permissions
    except Exception:
        return  # not on Android / pyjnius+android recipe unavailable (e.g. desktop testing)

    perms = [
        Permission.READ_EXTERNAL_STORAGE,
        Permission.WRITE_EXTERNAL_STORAGE,
    ]
    # POST_NOTIFICATIONS only exists as a runtime permission on Android 13+ (API 33).
    # Guard the attribute lookup so this doesn't break on older API levels/builds.
    post_notifications = getattr(Permission, "POST_NOTIFICATIONS", None)
    if post_notifications is not None:
        perms.append(post_notifications)

    def _on_permissions_result(permissions, results):
        # request_permissions() is fire-and-forget: it shows the OS dialog and
        # returns immediately, it does NOT wait for the user to tap Allow/Deny.
        # Without this callback, the very first library scan at startup
        # (rebuild_imported_tracks(), called from load-data during boot) runs
        # before permission is actually granted, finds nothing, and the app
        # then needs a force-close + relaunch for the (by-then-already-granted)
        # permission to take effect.
        #
        # IMPORTANT: this callback fires on Android's own callback thread, NOT
        # pygame's main thread. Calling rebuild_imported_tracks() (or anything
        # touching shared app state / pygame) directly from here caused random
        # crashes right after granting permission. So we just set a flag here;
        # the main loop checks it once per frame and does the actual rescan
        # safely on the main thread.
        global _permissions_just_granted
        if all(results):
            _permissions_just_granted = True

    try:
        request_permissions(perms, _on_permissions_result)
    except Exception:
        pass

    _maybe_request_manage_external_storage()

def _maybe_request_manage_external_storage():
    # MANAGE_EXTERNAL_STORAGE ("All files access") is a SPECIAL permission on
    # Android 11+ (API 30+) — it can't be granted via the normal runtime dialog
    # above. It requires sending the user to a dedicated system settings screen.
    try:
        from jnius import autoclass
        VERSION = autoclass('android.os.Build$VERSION')
        if VERSION.SDK_INT < 30:
            return  # not applicable below Android 11

        Environment = autoclass('android.os.Environment')
        if Environment.isExternalStorageManager():
            return  # already granted

        Intent = autoclass('android.content.Intent')
        Settings = autoclass('android.provider.Settings')
        Uri = autoclass('android.net.Uri')

        try:
            SDLActivity = autoclass('org.libsdl.app.SDLActivity')
            activity = SDLActivity.mSingleton if hasattr(SDLActivity, 'mSingleton') else SDLActivity.mActivity
        except Exception:
            PythonActivity = autoclass('org.kivy.android.PythonActivity')
            activity = PythonActivity.mActivity

        intent = Intent(Settings.ACTION_MANAGE_APP_ALL_FILES_ACCESS_PERMISSION)
        intent.setData(Uri.parse("package:" + activity.getPackageName()))
        activity.startActivity(intent)
    except Exception:
        pass

def request_notification_permission():
    """Used by the onboarding 'notifications' screen's button. Only requests
    POST_NOTIFICATIONS (Android 13+/API 33+ — older Android has no runtime
    notification prompt, so this is a no-op there and onboarding just moves
    on to the next screen)."""
    try:
        from android.permissions import Permission, request_permissions
    except Exception:
        return  # not on Android / desktop testing
    post_notifications = getattr(Permission, "POST_NOTIFICATIONS", None)
    if post_notifications is None:
        return
    try:
        request_permissions([post_notifications])
    except Exception:
        pass

def request_notification_permission_for_onboarding():
    """Same POST_NOTIFICATIONS request as request_notification_permission(),
    but for the onboarding 'notifications' screen, which needs to know the
    actual result (not just fire-and-forget) so it can wait on that screen
    until the user actually answers the OS dialog instead of advancing
    immediately. Result lands in the _notification_permission_result global:
    None while waiting, then True (granted, or nothing to ask) / False (denied)."""
    global _notification_permission_result
    _notification_permission_result = None
    try:
        from android.permissions import Permission, request_permissions
    except Exception:
        _notification_permission_result = True  # not on Android - nothing to wait on
        return
    post_notifications = getattr(Permission, "POST_NOTIFICATIONS", None)
    if post_notifications is None:
        _notification_permission_result = True  # older Android - no runtime prompt exists
        return

    def _on_result(permissions, results):
        global _notification_permission_result
        _notification_permission_result = bool(results and all(results))

    try:
        request_permissions([post_notifications], _on_result)
    except Exception:
        _notification_permission_result = True

def _check_storage_access_granted():
    """Polled once per frame while the onboarding 'storage' screen is waiting
    on a response, so that screen only advances once access has actually been
    granted (covers both the normal runtime-permission dialog on older
    Android, and the 'All files access' settings screen on Android 11+, which
    has no callback and can only be checked by polling)."""
    try:
        from jnius import autoclass
        VERSION = autoclass('android.os.Build$VERSION')
        if VERSION.SDK_INT >= 30:
            Environment = autoclass('android.os.Environment')
            return bool(Environment.isExternalStorageManager())
        from android.permissions import Permission, check_permission
        return bool(check_permission(Permission.READ_EXTERNAL_STORAGE)) and bool(check_permission(Permission.WRITE_EXTERNAL_STORAGE))
    except Exception:
        return True  # not on Android / desktop testing - nothing to wait on

def _get_wake_lock():
    """Lazily creates (once) and returns a partial WakeLock, or None if
    unavailable. A partial wake lock keeps the CPU running while the screen
    is off/locked without turning the screen back on - which is exactly
    what's needed so playback (and the auto-advance-to-next-track check)
    keeps going instead of the whole process going to sleep the moment the
    screen locks. Requires the WAKE_LOCK permission to be declared in
    buildozer.spec / the manifest; if it isn't, this just fails quietly and
    background playback falls back to whatever SDL/Android allow on their own."""
    global _wake_lock_obj
    if _wake_lock_obj is not None:
        return _wake_lock_obj
    try:
        from jnius import autoclass
        PowerManager = autoclass('android.os.PowerManager')
        try:
            SDLActivity = autoclass('org.libsdl.app.SDLActivity')
            activity = SDLActivity.mSingleton if hasattr(SDLActivity, 'mSingleton') else SDLActivity.mActivity
        except Exception:
            PythonActivity = autoclass('org.kivy.android.PythonActivity')
            activity = PythonActivity.mActivity
        power_service = activity.getSystemService(activity.POWER_SERVICE)
        _wake_lock_obj = power_service.newWakeLock(PowerManager.PARTIAL_WAKE_LOCK, "SpotMFi:PlaybackWakeLock")
        _wake_lock_obj.setReferenceCounted(False)
    except Exception:
        _wake_lock_obj = False  # remember failure so we don't retry every call
    return _wake_lock_obj or None

def acquire_playback_wake_lock():
    """Call whenever playback starts/resumes, so the device can't fully sleep
    (which would silently stop playback and prevent auto-advance) while a
    song is playing in the background."""
    try:
        lock = _get_wake_lock()
        if lock is not None and not lock.isHeld():
            lock.acquire()
    except Exception:
        pass

def release_playback_wake_lock():
    """Call whenever playback pauses/stops, so the wake lock isn't held (and
    draining battery) while nothing is actually playing."""
    try:
        lock = _get_wake_lock()
        if lock is not None and lock.isHeld():
            lock.release()
    except Exception:
        pass

# --- HAPTIC FEEDBACK (Android only) ---
# Settings > Haptics toggle: fires a short vibration "tick" on every button
# tap so the UI feels more tactile/responsive on Android. Off by default on
# PC/desktop (no vibration hardware there, and the setting is hidden there
# too - see the Settings page). Persisted the same way as every other
# setting, in save_app_data()/load_app_data().
haptics_enabled = True if IS_ANDROID else False
_vibrator_service = None  # lazily resolved the first time a haptic actually fires

def _get_vibrator_service():
    """Lazily resolves (once) and returns the Android Vibrator system
    service, or False if it's unavailable (PC, missing VIBRATE permission,
    older/unusual device, etc.) so we don't keep retrying jnius every tap."""
    global _vibrator_service
    if _vibrator_service is not None:
        return _vibrator_service
    try:
        from jnius import autoclass, cast
        try:
            SDLActivity = autoclass('org.libsdl.app.SDLActivity')
            activity = SDLActivity.mSingleton if hasattr(SDLActivity, 'mSingleton') else SDLActivity.mActivity
        except Exception:
            PythonActivity = autoclass('org.kivy.android.PythonActivity')
            activity = PythonActivity.mActivity
        Context = autoclass('android.content.Context')
        vibrator = activity.getSystemService(Context.VIBRATOR_SERVICE)
        _vibrator_service = cast('android.os.Vibrator', vibrator)
    except Exception:
        _vibrator_service = False
    return _vibrator_service

def trigger_haptic(duration_ms=15):
    """Fire one short vibration 'tick' for button-press feedback. No-op on
    PC/desktop and whenever the user has Haptics turned off in Settings, so
    it's always safe to call from anywhere a tap is handled."""
    if not IS_ANDROID or not haptics_enabled:
        return
    try:
        vibrator = _get_vibrator_service()
        if not vibrator:
            return
        try:
            from jnius import autoclass
            VibrationEffect = autoclass('android.os.VibrationEffect')
            effect = VibrationEffect.createOneShot(duration_ms, VibrationEffect.DEFAULT_AMPLITUDE)
            vibrator.vibrate(effect)
        except Exception:
            # Pre-Android-8 (API < 26) devices don't have VibrationEffect.
            vibrator.vibrate(duration_ms)
    except Exception:
        pass

# --- "NOW PLAYING" NOTIFICATION ---
# Note on what's actually achievable here: Android doesn't let apps paint an
# arbitrary full-bleed image as a system notification's background - the OS
# owns and locks that chrome (this has only gotten stricter since Android
# 12's notification redesign). The platform-supported equivalent - and what
# real media apps (Spotify, YT Music, etc.) actually ship - is a "colorized"
# notification whose background is tinted with a color, with the album art
# shown as the large thumbnail. That's what's built below: real album art as
# the thumbnail with the background tinted to a color sampled from that same
# art, or a plain green tile with the song name drawn on it when there's no
# art at all.
NOTIF_CHANNEL_ID = "spotmfi_playback"
NOTIF_ID = 1001
_notif_manager_obj = None
_notif_small_icon_id = None
_notif_last_state = (None, None)  # (track_path, is_playing) last posted

def _get_android_activity():
    try:
        from jnius import autoclass
        try:
            SDLActivity = autoclass('org.libsdl.app.SDLActivity')
            act = getattr(SDLActivity, 'mSingleton', None) or getattr(SDLActivity, 'mActivity', None)
            if act is not None:
                return act
        except Exception:
            pass
        PythonActivity = autoclass('org.kivy.android.PythonActivity')
        return PythonActivity.mActivity
    except Exception:
        return None

def _get_notif_manager():
    """Lazily creates (once) the NotificationManager + playback notification
    channel. Returns (manager, activity) or None if unavailable (desktop
    testing, missing permission, etc)."""
    global _notif_manager_obj, _notif_small_icon_id
    if _notif_manager_obj is not None:
        return _notif_manager_obj or None
    try:
        from jnius import autoclass
        activity = _get_android_activity()
        if activity is None:
            raise Exception("no activity")
        NotificationManager = autoclass('android.app.NotificationManager')
        manager = activity.getSystemService(activity.NOTIFICATION_SERVICE)
        VERSION = autoclass('android.os.Build$VERSION')
        if VERSION.SDK_INT >= 26:
            NotificationChannel = autoclass('android.app.NotificationChannel')
            if manager.getNotificationChannel(NOTIF_CHANNEL_ID) is None:
                channel = NotificationChannel(NOTIF_CHANNEL_ID, "Now Playing", NotificationManager.IMPORTANCE_LOW)
                channel.setDescription("Shows the currently playing song")
                channel.setShowBadge(False)
                manager.createNotificationChannel(channel)

        # Resolve the app's own launcher icon as the small status-bar icon;
        # fall back to a built-in system icon if that lookup fails.
        try:
            res = activity.getResources()
            pkg = activity.getPackageName()
            icon_id = res.getIdentifier("icon", "mipmap", pkg)
            if not icon_id:
                icon_id = res.getIdentifier("icon", "drawable", pkg)
        except Exception:
            icon_id = 0
        if not icon_id:
            android_R_drawable = autoclass('android.R$drawable')
            icon_id = android_R_drawable.ic_media_play
        _notif_small_icon_id = icon_id

        _notif_manager_obj = (manager, activity)
    except Exception:
        _notif_manager_obj = False
    return _notif_manager_obj or None

def _notif_dominant_color(cover_surf):
    """Cheap average-color sample of the album art (no PIL needed - just
    pygame, which is already loaded), used to tint the colorized
    notification's background so it visually matches the art."""
    try:
        small = pygame.transform.smoothscale(cover_surf.convert(), (8, 8))
        r_total = g_total = b_total = 0
        for x in range(8):
            for y in range(8):
                r, g, b = small.get_at((x, y))[:3]
                r_total += r; g_total += g; b_total += b
        n = 64
        return (r_total // n, g_total // n, b_total // n)
    except Exception:
        return None

def _notif_build_art_bitmap(title):
    """Returns (android.graphics.Bitmap, is_fallback). is_fallback is True
    when there was no real album art and a green placeholder tile with the
    song name on it was drawn instead."""
    try:
        from jnius import autoclass
        Bitmap = autoclass('android.graphics.Bitmap')
        BitmapConfig = autoclass('android.graphics.Bitmap$Config')
        Canvas = autoclass('android.graphics.Canvas')
        Paint = autoclass('android.graphics.Paint')
        Color = autoclass('android.graphics.Color')
        BitmapFactory = autoclass('android.graphics.BitmapFactory')

        cover_surf = current_track.get("cover_surface")
        if cover_surf is not None:
            try:
                tmp_art_path = os.path.join(tempfile.gettempdir(), "spotmfi_notif_art.png")
                pygame.image.save(cover_surf, tmp_art_path)
                art_bitmap = BitmapFactory.decodeFile(tmp_art_path)
                if art_bitmap is not None:
                    return art_bitmap, False
            except Exception:
                pass

        # No usable art - draw a solid green square with the song name on it.
        size = 512
        bmp = Bitmap.createBitmap(size, size, BitmapConfig.ARGB_8888)
        canvas = Canvas(bmp)
        canvas.drawColor(Color.parseColor("#1DB954"))
        paint = Paint(Paint.ANTI_ALIAS_FLAG)
        paint.setColor(Color.WHITE)
        paint.setTextAlign(Paint.Align.CENTER)
        paint.setTextSize(size * 0.09)
        paint.setFakeBoldText(True)

        text = (title or "Unknown Track").strip()
        words = text.split()
        lines, line = [], ""
        for w in words:
            trial = (line + " " + w).strip()
            if line and paint.measureText(trial) > size * 0.85:
                lines.append(line)
                line = w
            else:
                line = trial
        if line:
            lines.append(line)
        lines = lines[:4] or ["Unknown Track"]

        line_height = size * 0.12
        start_y = size / 2 - (line_height * (len(lines) - 1)) / 2
        for i, ln in enumerate(lines):
            canvas.drawText(ln, size / 2, start_y + i * line_height, paint)

        return bmp, True
    except Exception:
        return None, True

def update_playback_notification():
    """Posts/updates the persistent 'now playing' notification for the
    current track: song name, artist, real album art (or a green
    song-name placeholder tile when there's no art), and a background tint
    sampled from that same art."""
    try:
        result = _get_notif_manager()
        if result is None:
            return
        manager, activity = result
        if not current_track.get("path"):
            return

        from jnius import autoclass
        NotificationBuilder = autoclass('android.app.Notification$Builder')
        MediaStyle = autoclass('android.app.Notification$MediaStyle')
        Color = autoclass('android.graphics.Color')
        VERSION = autoclass('android.os.Build$VERSION')

        title = current_track.get("title", "Unknown Track")
        artist = current_track.get("artist", "")

        bitmap, is_fallback = _notif_build_art_bitmap(title)

        dom = None
        if not is_fallback and current_track.get("cover_surface") is not None:
            dom = _notif_dominant_color(current_track["cover_surface"])
        notif_color = Color.rgb(*dom) if dom else Color.parseColor("#1DB954")

        builder = NotificationBuilder(activity, NOTIF_CHANNEL_ID) if VERSION.SDK_INT >= 26 else NotificationBuilder(activity)
        builder.setContentTitle(title)
        builder.setContentText(artist)
        builder.setSmallIcon(_notif_small_icon_id)
        builder.setOngoing(bool(is_playing))
        builder.setOnlyAlertOnce(True)
        if bitmap is not None:
            builder.setLargeIcon(bitmap)
        try:
            builder.setStyle(MediaStyle())
        except Exception:
            pass
        try:
            builder.setColorized(True)
            builder.setColor(notif_color)
        except Exception:
            pass

        manager.notify(NOTIF_ID, builder.build())
    except Exception:
        pass

def request_storage_permission_for_onboarding():
    """Sequenced storage-permission flow for the onboarding 'storage' screen.
    Firing the legacy READ/WRITE_EXTERNAL_STORAGE runtime dialog AND
    launching the Android 11+ 'All files access' settings screen at the same
    time (as request_android_permissions() does for returning users) can
    crash on some devices when a permission dialog and a fresh Activity
    launch collide, and can also silently drop the first dialog - which is
    what made the onboarding button look like it needed a second tap. This
    version only opens the settings screen (via the poll in the main loop)
    once the first dialog has actually been answered."""
    global _storage_legacy_perm_done, _manage_storage_intent_launched
    _storage_legacy_perm_done = False
    _manage_storage_intent_launched = False

    try:
        from android.permissions import Permission, request_permissions
    except Exception:
        _storage_legacy_perm_done = True  # not on Android - nothing to wait on
        return

    perms = [Permission.READ_EXTERNAL_STORAGE, Permission.WRITE_EXTERNAL_STORAGE]

    def _on_result(permissions, results):
        # Runs on Android's own callback thread - just flip a flag, the main
        # loop does the actual follow-up (settings screen, etc) on the main thread.
        global _storage_legacy_perm_done
        _storage_legacy_perm_done = True

    try:
        request_permissions(perms, _on_result)
    except Exception:
        _storage_legacy_perm_done = True

def request_storage_permission():
    """Used by the onboarding 'storage' screen's button. Reuses the existing
    full permission flow (storage runtime dialog + the Android 11+ 'All
    files access' settings screen)."""
    request_android_permissions()

# NOTE: request_android_permissions() used to be called unconditionally here at
# boot. It's now only auto-called for returning users (see right after
# load_app_data() near the main loop) — first-time users grant these via the
# onboarding screens instead, one at a time, via explicit buttons.

# Opening links (Spotify/YouTube/Apple search URLs). webbrowser.open() is the
# safe, standard way to do this and works reliably across devices; wrapped in
# a try/except so a bad URL or missing handler never takes the app down.
def open_url(url):
    try:
        webbrowser.open(url)
    except Exception:
        pass

is_portrait = REAL_HEIGHT > REAL_WIDTH

# --- AUTOMATIC DEVICE TYPE DETECTION ---
# Determines whether the current device is a phone or a tablet/desktop, so a sensible
# default layout_mode can be picked automatically on first launch (before any saved
# preference exists). Uses physical screen diagonal (inches) via Android DisplayMetrics
# when available; falls back to a pixel-resolution heuristic otherwise.
def detect_device_layout_mode():
    try:
        from jnius import autoclass
        DisplayMetrics = autoclass('android.util.DisplayMetrics')
        try:
            SDLActivity = autoclass('org.libsdl.app.SDLActivity')
            activity = SDLActivity.mSingleton if hasattr(SDLActivity, 'mSingleton') else SDLActivity.mActivity
        except Exception:
            PythonActivity = autoclass('org.kivy.android.PythonActivity')
            activity = PythonActivity.mActivity
        metrics = DisplayMetrics()
        activity.getWindowManager().getDefaultDisplay().getMetrics(metrics)
        width_inches = metrics.widthPixels / metrics.xdpi
        height_inches = metrics.heightPixels / metrics.ydpi
        diagonal_inches = math.sqrt(width_inches ** 2 + height_inches ** 2)
        # Common phone/tablet cutoff: devices under ~6.9" diagonal are phones
        return "phone" if diagonal_inches < 6.9 else "desktop"
    except Exception:
        pass
    # Fallback heuristic for non-Android environments (e.g. desktop testing in Pydroid
    # window mode): treat smaller pixel resolutions as phone-sized
    smaller_dim = min(REAL_WIDTH, REAL_HEIGHT)
    larger_dim = max(REAL_WIDTH, REAL_HEIGHT)
    return "phone" if smaller_dim <= 500 and larger_dim <= 1000 else "desktop"

def compute_virtual_size(real_w, real_h, portrait, _layout_mode="desktop"):
    if portrait and _layout_mode == "phone":
        # Match phone aspect ratio exactly so there are no black bars.
        # Virtual width is halved (700 -> 350) so every element drawn in
        # virtual pixels ends up covering 2x the screen space once this
        # canvas is scaled up to the real display — same layout/style,
        # just twice the size.
        vw = 500
        vh = int(real_h * (vw / real_w)) if real_w > 0 else 785
        return vw, vh
    return (700, 1100) if portrait else (1100, 700)

WIDTH, HEIGHT = compute_virtual_size(REAL_WIDTH, REAL_HEIGHT, is_portrait, "desktop")

WIDTH, HEIGHT = compute_virtual_size(REAL_WIDTH, REAL_HEIGHT, is_portrait, "desktop")

# NOTE: pygame.SCALED (GPU-side upscale) was tried here to avoid the per-frame
# CPU smoothscale below, but it produced a black screen on this build's
# Android/SDL2 setup instead of raising an exception, so the try/except
# fallback never got a chance to engage - reverted back to the known-working
# CPU smoothscale path. USING_GPU_SCALE stays False/present so the FPS
# overlay and the flip logic later in the file don't need to change.
USING_GPU_SCALE = False

screen = pygame.display.set_mode(
    (REAL_WIDTH, REAL_HEIGHT),
    (pygame.FULLSCREEN | pygame.RESIZABLE | pygame.HWSURFACE | pygame.DOUBLEBUF) if IS_ANDROID else (pygame.RESIZABLE | pygame.DOUBLEBUF)
)
virtual_surface = pygame.Surface((WIDTH, HEIGHT)).convert()
clock = pygame.time.Clock()

# --- ANIMATED STARTUP SPLASH (spinning logo) ---
# NOTE on the native "Loading..." screen you see before this: that one is
# shown by Android itself / python-for-android's bootstrap while it unpacks
# and starts the embedded Python interpreter — it appears before any of our
# code has run yet, so it can't be replaced with an animation from here (it's
# a one-time, unavoidable bit of real work, typically a couple seconds). What
# we CAN control is everything from the moment Python actually starts, which
# is this screen: a branded, spinning version of the app icon while the rest
# of startup (fonts, saved data, music library scan) finishes underneath.
def _play_spinning_logo_splash(duration_seconds=1.4):
    try:
        logo_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "data", "icon.png")
        logo_img = pygame.image.load(logo_path).convert_alpha()
    except Exception:
        return  # no icon on disk (e.g. running a bare script copy) — just skip the splash

    logo_size = int(min(REAL_WIDTH, REAL_HEIGHT) * 0.28)
    logo_img = pygame.transform.smoothscale(logo_img, (logo_size, logo_size))
    center = (REAL_WIDTH // 2, REAL_HEIGHT // 2)

    splash_clock = pygame.time.Clock()
    elapsed = 0.0
    degrees_per_second = 260.0  # one full rotation ~every 1.4s

    while elapsed < duration_seconds:
        dt = splash_clock.tick(60) / 1000.0
        elapsed += dt

        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                pygame.quit()
                sys.exit()

        angle = (elapsed * degrees_per_second) % 360
        rotated = pygame.transform.rotozoom(logo_img, -angle, 1.0)
        rotated_rect = rotated.get_rect(center=center)

        screen.fill(COLOR_BLACK if "COLOR_BLACK" in globals() else (24, 24, 24))
        screen.blit(rotated, rotated_rect)
        pygame.display.flip()

_play_spinning_logo_splash()

# FIXED: Safe compilation safeguard for platforms missing the pygame.scrap module entirely
HAS_DESKTOP_SCRAP = False
try:
    import pygame.scrap
    pygame.scrap.init()
    HAS_DESKTOP_SCRAP = True
except:
    pass

# --- COLOR PALETTE ---
COLOR_BLACK = (24, 24, 24)       
COLOR_DARK_GREY = (18, 18, 18)   
COLOR_LIGHT_GREY = (40, 40, 40)  
COLOR_SPOTIFY_GREEN = (30, 215, 96)
COLOR_WHITE = (255, 255, 255)
COLOR_TEXT_MUTED = (179, 179, 179)
COLOR_HOVER = (50, 50, 50)
COLOR_CARD_BG = (30, 30, 30)
COLOR_RED = (230, 50, 50)
COLOR_OVERLAY = (0, 0, 0, 200)

# --- FONTS ---
font_title = pygame.font.SysFont("Arial", 22, bold=True)
font_body = pygame.font.SysFont("Arial", 16, bold=True)
font_small = pygame.font.SysFont("Arial", 14)
font_huge = pygame.font.SysFont("Arial", 50, bold=True)

# --- APP STATE ---
current_page = "Search"  
current_track = {      
    "title": "Select a song",
    "artist": "No Artist",
    "duration": "0:00",
    "path": ""
}
is_playing = False     
is_shuffle = False  
_wake_lock_prev_is_playing = False  # tracks is_playing transitions for acquire/release_playback_wake_lock()

green_toggled_tracks = set()
track_covers = {}  # { track_path: {"image_path": str, "surface": pygame.Surface} }
listen_stats = {}          # keyed by track path — all per-track listening data
_listen_session_start = None   # wall-clock float when current play session began

# --- AUDIO TRACKING STATE ---
track_duration = 0.0          
track_start_accumulator = 0.0 
TEMP_WAV_PATH = None          
current_backend = "pygame"    
music_loaded = False          
is_dragging_progress = False
drag_seek_target = 0.0

# Android Native Decoders Initialization
try:
    from jnius import autoclass
    MediaPlayer = autoclass('android.media.MediaPlayer')
    android_media_player = MediaPlayer()
    HAS_ANDROID_MEDIA = True
except:
    android_media_player = None
    HAS_ANDROID_MEDIA = False

# --- DUAL-PLATFORM HYBRID CLIPBOARD UTILITY ---
def get_clipboard_text():
    try:
        pasted_bytes = pygame.scrap.get(pygame.SCRAP_TEXT)
        if pasted_bytes:
            return pasted_bytes.decode('utf-8', errors='ignore').replace('\x00', '').replace('\r\n', '\n').replace('\r', '\n').replace('\xa0', ' ')
    except:
        pass
        
    if HAS_ANDROID_MEDIA:
        try:
            from jnius import autoclass
            PythonActivity = autoclass('org.kivy.android.PythonActivity')
            currentActivity = PythonActivity.mActivity
            Context = autoclass('android.content.Context')
            clipboard = currentActivity.getSystemService(Context.CLIPBOARD_SERVICE)
            if clipboard.hasPrimaryClip():
                clipData = clipboard.getPrimaryClip()
                if clipData.getItemCount() > 0:
                    item = clipData.getItemAt(0)
                    text_obj = item.getText()
                    if text_obj:
                        return text_obj.toString()
        except Exception as android_clip_err:
            print(f"Android Native Clipboard Error: {android_clip_err}")
            
    return ""

# --- DATA STORAGE ---
DATA_FILE = "SpotM-Fi.json"
# Absolute path: on Android, pygame.image.load() goes through SDL's file-loading
# layer, which treats a relative path as an app-asset lookup rather than
# resolving it against the process's working directory the way Python's own
# open() does. That mismatch meant a cover could download and save fine, but
# then fail to load right after with "No file 'SpotMFi_Covers/cover_...'" even
# though the file was really there. Using an absolute path here makes both the
# write (open()) and every later load (pygame.image.load()) agree on the same
# real filesystem location.
COVERS_DIR = os.path.abspath("SpotMFi_Covers")
os.makedirs(COVERS_DIR, exist_ok=True)
sidebar_items = ["Search", "Your Library", "Settings"] 
track_list = []
imported_tracks = []
liked_tracks = []        
saved_directories = []  

custom_playlists = {}  
liked_songs_custom_cover = {"image_path": None, "surface": None}
selected_custom_playlist_name = None
is_browsing_for_cover = False
browsing_cover_target = "create"

song_lyrics_database = {}  
show_lyrics_editor_view = False
lyrics_editor_cursor_timer = 0.0
lyrics_text_changed = False
lyrics_cursor_pos = 0
_lyric_cache_key = None
_lyric_cache_parsed = []

show_create_playlist_modal = False
playlist_input_text = ""
playlist_desc_text = ""
active_input_field = "name" 
show_add_to_playlist_modal = False
track_to_add_to_playlist = None
modal_playlist_cover_surface = None  
modal_playlist_cover_path = None

marquee_offset = 0.0
marquee_direction = 1

is_browsing_storage = False
search_input_active = False
search_query = ""
viewing_liked_playlist = False
viewing_settings_page = False  

# --- Daily-rotating content for Song / Artist of the Day and History Maker ---
# Picked deterministically from the current date, so the choice stays the
# same all day and moves on to the next entry tomorrow.
SOTD_ENTRIES = [
    {
        "title": "What a Wonderful World", "artist": "Louis Armstrong",
        "search": "What a Wonderful World Louis Armstrong",
        "description": (
            "Released in 1967, \"What a Wonderful World\" was written by Bob Thiele and "
            "George David Weiss and recorded by the legendary Louis Armstrong. At a time "
            "when the world was gripped by the Vietnam War, civil rights struggles and deep "
            "social division, Armstrong chose to record a song of pure, quiet wonder \u2014 "
            "an act of radical optimism that transcended politics entirely.\n\n"
            "The song asks nothing of the listener except to pause and notice: the colours "
            "of trees and roses, the handshakes of friends, the laughter of children. "
            "Armstrong\u2019s warm, weathered voice carries the weight of a life fully "
            "lived, making even the simplest observations feel earned and true.\n\n"
            "It was initially a commercial failure in the United States but became a number "
            "one hit in the United Kingdom, and its second life came after it was featured "
            "in the 1987 film \u2018Good Morning, Vietnam\u2019, introducing it to an "
            "entirely new generation. Since then it has become one of the most recognisable "
            "songs ever recorded, covered by hundreds of artists across every genre.\n\n"
            "What makes it the Song of the Day is its extraordinary staying power and "
            "universality. It holds no bitterness, no agenda and no boundary. Whether you "
            "are eight years old or eighty, hearing it for the first time or the thousandth, "
            "it reliably does what very few songs can \u2014 it makes the world feel, just "
            "for a moment, genuinely and completely wonderful."
        ),
    },
    {
        "title": "Redemption Song", "artist": "Bob Marley",
        "search": "Redemption Song Bob Marley",
        "description": (
            "Closing out 1980's \"Uprising\", \"Redemption Song\" is Bob Marley stripped "
            "down to just an acoustic guitar and his voice \u2014 a striking departure from "
            "the reggae rhythm section that defined nearly everything else he ever recorded.\n\n"
            "The lyrics draw partly from a 1937 speech by Marcus Garvey, weaving in the line "
            "\"none but ourselves can free our minds\", turning the song into a piece of "
            "protest poetry as much as a piece of music.\n\n"
            "Marley recorded it while already fighting the cancer that would take his life "
            "the following year, which lends the song's talk of freedom, mortality and legacy "
            "an extra, aching weight in hindsight.\n\n"
            "It endures as one of the most covered protest songs of all time, precisely "
            "because it says so much with so little \u2014 just a voice, a guitar, and a "
            "message that hasn't aged a day."
        ),
    },
    {
        "title": "Dreams", "artist": "Fleetwood Mac",
        "search": "Dreams Fleetwood Mac",
        "description": (
            "Written by Stevie Nicks in about ten minutes on a bed at the Sausalito studio "
            "where Fleetwood Mac were recording 1977's \"Rumours\", \"Dreams\" became the "
            "band's only US number one single \u2014 born out of the very breakup chaos "
            "that made the rest of the album so raw.\n\n"
            "Its hushed verses and cryptic imagery, all thunder and rain and players only "
            "loving you when they're playing, sit on top of one of the simplest bass "
            "grooves in the band's catalogue, proof that restraint can be just as "
            "hypnotic as excess.\n\n"
            "The song found an unexpected second life in 2020 when a video of a man "
            "skateboarding to it while drinking cranberry juice went viral, introducing an "
            "entire new generation to a track already over forty years old.\n\n"
            "Few songs manage to sound that timeless twice, decades apart, which is exactly "
            "why it earns its spot here."
        ),
    },
    {
        "title": "Hallelujah", "artist": "Jeff Buckley",
        "search": "Hallelujah Jeff Buckley",
        "description": (
            "Leonard Cohen wrote \"Hallelujah\" first, but it's Jeff Buckley's 1994 cover, "
            "recorded for his only studio album \"Grace\", that most people picture when "
            "they hear the song today.\n\n"
            "Buckley slowed it down, stripped the arrangement to just his voice and a "
            "clean electric guitar, and turned Cohen's dense, biblical lyric into something "
            "far more intimate and devastating.\n\n"
            "It sold modestly during Buckley's lifetime \u2014 he drowned in 1997 at just "
            "30 \u2014 and only became a genuine phenomenon years later, eventually "
            "topping charts and soundtracking films and talent-show finales alike.\n\n"
            "That a quiet, six-minute cover of an already-obscure song could grow into one "
            "of the most performed pieces of the last thirty years is exactly the kind of "
            "story worth a moment's pause."
        ),
    },
    {
        "title": "Bohemian Rhapsody", "artist": "Queen",
        "search": "Bohemian Rhapsody Queen",
        "description": (
            "At just under six minutes, with no chorus, an operatic middle section and a "
            "hard-rock finale, \"Bohemian Rhapsody\" broke essentially every rule of what a "
            "1975 single was supposed to be \u2014 and topped the UK charts anyway.\n\n"
            "Freddie Mercury reportedly worked out much of the song on a piano at his own "
            "home before the band spent weeks in the studio layering as many as 180 "
            "separate vocal overdubs to build the operatic section alone.\n\n"
            "Radio programmers thought it was commercial suicide at over twice the usual "
            "single length, until DJ Kenny Everett played it repeatedly on air and public "
            "demand forced its release.\n\n"
            "Its second wave of fame, thanks to \"Wayne's World\" in 1992 and the 2018 "
            "biopic of the same name, has kept introducing it to listeners who weren't even "
            "born when it first topped the charts."
        ),
    },
    {
        "title": "Respect", "artist": "Aretha Franklin",
        "search": "Respect Aretha Franklin",
        "description": (
            "Otis Redding wrote and recorded \"Respect\" first in 1965, but it was Aretha "
            "Franklin's 1967 version, reworked with her sisters' backing vocals and the "
            "iconic spelled-out chorus, that turned it into something entirely new.\n\n"
            "Franklin flipped the song's perspective from a man demanding respect at home "
            "to a woman demanding it on her own terms, and it landed right in the middle "
            "of both the civil rights and women's movements of the era.\n\n"
            "Redding reportedly said, half-joking, that the song belonged to Aretha now "
            "\u2014 a rare and generous admission that her cover had eclipsed the "
            "original completely.\n\n"
            "It remains one of the most instantly recognisable openings in music, and "
            "arguably the definitive record of what soul music could do at its peak."
        ),
    },
    {
        "title": "Billie Jean", "artist": "Michael Jackson",
        "search": "Billie Jean Michael Jackson",
        "description": (
            "Built around one of the most instantly recognisable basslines in pop, "
            "\"Billie Jean\" was almost left off 1982's \"Thriller\" entirely until "
            "producer Quincy Jones was convinced otherwise.\n\n"
            "Its accompanying video, with Jackson's light-up sidewalk, was one of the "
            "first by a Black artist in heavy rotation on MTV, breaking down a barrier "
            "the network had been criticised for maintaining.\n\n"
            "The song's paranoid, tightly wound production and Jackson's falsetto "
            "delivery turned a personal anecdote about an obsessive fan into one of the "
            "most meticulously crafted pop records ever made.\n\n"
            "Decades on, that bassline alone is still enough for a dance floor to "
            "recognise the song within half a second."
        ),
    },
    {
        "title": "Like a Rolling Stone", "artist": "Bob Dylan",
        "search": "Like a Rolling Stone Bob Dylan",
        "description": (
            "At over six minutes with a snarling vocal and no conventional love-song "
            "subject matter, \"Like a Rolling Stone\" broke almost every rule of 1965 "
            "AM radio \u2014 and reached number two on the charts anyway.\n\n"
            "It arrived just as Dylan was moving from acoustic folk into electric rock, "
            "a shift that famously drew boos from purists at the Newport Folk Festival "
            "that same year.\n\n"
            "Al Kooper's organ part, played almost by accident after he talked his way "
            "onto the session, became one of the most quietly influential parts of the "
            "entire recording.\n\n"
            "Rolling Stone magazine itself later named it the greatest song of all time, "
            "and whether or not you'd rank it there, its influence on turning rock "
            "lyrics into serious writing is hard to overstate."
        ),
    },
    {
        "title": "Purple Rain", "artist": "Prince",
        "search": "Purple Rain Prince",
        "description": (
            "Recorded live at Minneapolis's First Avenue club in 1983, \"Purple Rain\" "
            "is one of the rare power ballads that's also, quietly, a genuine guitar "
            "showcase \u2014 Prince's extended solo remains one of his most celebrated.\n\n"
            "It anchored the film of the same name, which turned Prince into a "
            "bona fide movie star alongside his existing reputation as one of the most "
            "gifted musicians of his generation.\n\n"
            "The song blends gospel, rock balladry and orchestral strings into "
            "something that never quite resolves into a single genre, mirroring "
            "Prince's own refusal to be easily categorised.\n\n"
            "Nearly every arena still plays it as fans hold their phone lights aloft, "
            "which is about the highest tribute a power ballad can receive."
        ),
    },
    {
        "title": "Fast Car", "artist": "Tracy Chapman",
        "search": "Fast Car Tracy Chapman",
        "description": (
            "Tracy Chapman's 1988 debut single tells a plain, devastating story of "
            "poverty and stalled escape entirely through a folk arrangement of just "
            "voice and acoustic guitar, with barely any embellishment at all.\n\n"
            "Her performance at the Nelson Mandela 70th Birthday Tribute concert, "
            "filling in on short notice, introduced her to a global audience almost "
            "overnight and sent the song to the top of charts worldwide.\n\n"
            "It found a surprising second life in 2023 when country singer Luke Combs "
            "covered it note for note, introducing an entirely new generation and "
            "audience to Chapman's original songwriting.\n\n"
            "Few songs manage to say so much about class and circumstance with so few "
            "chords, which is exactly why it still lands as hard today as it did in 1988."
        ),
    },
    {
        "title": "Take Five", "artist": "The Dave Brubeck Quartet",
        "search": "Take Five Dave Brubeck Quartet",
        "description": (
            "Written by saxophonist Paul Desmond in the unusual 5/4 time signature that "
            "gives the song its name, \"Take Five\" became, against all odds, one of "
            "the best-selling jazz singles ever recorded.\n\n"
            "Drummer Joe Morello's rolling solo section, unusual for a mainstream jazz "
            "single of 1959, gave the track a rhythmic identity that still sounds "
            "instantly recognisable today.\n\n"
            "Radio stations at the time were sceptical an odd-metre jazz instrumental "
            "could ever be a hit, yet it eventually sold over a million copies and "
            "helped bring modern jazz into mainstream listening rooms.\n\n"
            "It remains proof that an unconventional time signature, played with "
            "enough cool confidence, can become genuinely catchy."
        ),
    },
    {
        "title": "Losing My Religion", "artist": "R.E.M.",
        "search": "Losing My Religion R.E.M.",
        "description": (
            "Built around a mandolin riff that guitarist Peter Buck was still learning "
            "to play, \"Losing My Religion\" became R.E.M.'s biggest hit almost by "
            "accident, despite having no chorus in the traditional sense.\n\n"
            "The title is a Southern American expression for being at the end of one's "
            "rope, not a statement about faith, something widely misunderstood at the "
            "time of release.\n\n"
            "Its stark, symbolism-heavy music video won six MTV Video Music Awards and "
            "helped push the song, and the band, into mainstream rotation worldwide.\n\n"
            "It's a rare example of a genuinely strange, mandolin-led alternative rock "
            "song becoming a true global hit on its own terms."
        ),
    },
    {
        "title": "Wuthering Heights", "artist": "Kate Bush",
        "search": "Wuthering Heights Kate Bush",
        "description": (
            "Written when Kate Bush was just eighteen, inspired by the final scenes of "
            "Emily Bronte's novel, \"Wuthering Heights\" made her the first woman to "
            "reach UK number one with a self-written song.\n\n"
            "Her soaring, theatrical vocal delivery and the song's unusual, swooping "
            "melody were unlike anything else on the charts in 1978, and she reportedly "
            "insisted on it as her debut single against her label's wishes.\n\n"
            "The accompanying video, with Bush in flowing red, became just as iconic as "
            "the song itself and helped define her singular, uncompromising public "
            "image from the very start of her career.\n\n"
            "Few debut singles announce a wholly original artist this clearly, on the "
            "very first attempt."
        ),
    },
    {
        "title": "A Change Is Gonna Come", "artist": "Sam Cooke",
        "search": "A Change Is Gonna Come Sam Cooke",
        "description": (
            "Inspired partly by Bob Dylan's \"Blowin' in the Wind\" and partly by "
            "Cooke's own experience being turned away from a whites-only motel, "
            "\"A Change Is Gonna Come\" became one of the defining anthems of the "
            "civil rights era.\n\n"
            "Its lush orchestral arrangement was a marked departure from Cooke's usual "
            "pop sound, giving the song a gravity that matched its subject matter.\n\n"
            "Tragically, Cooke was shot and killed in December 1964, just weeks before "
            "the song's release, and never got to see the impact it would go on to "
            "have.\n\n"
            "It's been covered and referenced ever since by artists across soul, rock "
            "and hip-hop, and remains one of the most quietly devastating protest "
            "songs ever recorded."
        ),
    },
    {
        "title": "Ohio", "artist": "Crosby, Stills, Nash & Young",
        "search": "Ohio Crosby Stills Nash Young",
        "description": (
            "Neil Young wrote \"Ohio\" within days of the Kent State shootings in May "
            "1970, when National Guardsmen opened fire on unarmed student protesters, "
            "killing four.\n\n"
            "The band rushed it into a studio and released it almost immediately, an "
            "unusually fast turnaround for the era, driven purely by the urgency of "
            "the moment.\n\n"
            "Some radio stations refused to play it given its direct reference to "
            "President Nixon, but it still became a defining protest record of the "
            "Vietnam War period.\n\n"
            "Few songs have ever been written, recorded and released in response to a "
            "real news event this quickly, which is exactly what gives it its raw, "
            "unfiltered urgency."
        ),
    },
    {
        "title": "Hurt", "artist": "Johnny Cash",
        "search": "Hurt Johnny Cash",
        "description": (
            "Originally a Nine Inch Nails song about addiction, \"Hurt\" was "
            "reimagined by Johnny Cash in 2002, near the end of his life, as a "
            "stripped-back piano-and-voice meditation on age, regret and mortality.\n\n"
            "The accompanying video, cutting between Cash's frail present and archival "
            "footage of his younger self, is widely considered one of the most "
            "devastating music videos ever made. Nine Inch Nails' Trent Reznor said "
            "watching it made him feel the song no longer belonged to him."
        ),
    },
    {
        "title": "Superstition", "artist": "Stevie Wonder",
        "search": "Superstition Stevie Wonder",
        "description": (
            "Built around a razor-sharp clavinet riff Stevie Wonder played himself, "
            "\"Superstition\" was originally written as a gift for Jeff Beck before "
            "Wonder's own version was rushed out first and became a bigger hit.\n\n"
            "It marked Wonder's arrival as a full studio auteur, playing nearly every "
            "instrument himself, and remains one of the most sampled funk grooves in "
            "hip-hop and pop production history."
        ),
    },
    {
        "title": "Good Vibrations", "artist": "The Beach Boys",
        "search": "Good Vibrations Beach Boys",
        "description": (
            "Brian Wilson spent months and a then-unheard-of studio budget "
            "assembling \"Good Vibrations\" from dozens of separately recorded "
            "sections, splicing them together like a pop symphony rather than a "
            "conventional single.\n\n"
            "Its use of the theremin-like electro-theremin gave it a genuinely "
            "otherworldly texture, and it's still routinely cited as one of the "
            "most ambitious studio productions of the 1960s."
        ),
    },
    {
        "title": "Ain't No Sunshine", "artist": "Bill Withers",
        "search": "Ain't No Sunshine Bill Withers",
        "description": (
            "Bill Withers was still working a factory job assembling airplane "
            "toilets when he recorded \"Ain't No Sunshine\" in 1971, and kept the "
            "job even after it became a hit, unsure the music career would last.\n\n"
            "Its famous repeated \"I know\" section was originally a placeholder "
            "Withers meant to replace with real lyrics later \u2014 producer Booker "
            "T. Jones convinced him to leave it exactly as it was."
        ),
    },
    {
        "title": "Where Is My Mind?", "artist": "Pixies",
        "search": "Where Is My Mind Pixies",
        "description": (
            "Frontman Black Francis has said the song was inspired by a scuba diving "
            "trip where a small fish kept swimming circles around him, giving him "
            "the disorienting feeling that summed up the song's title.\n\n"
            "Largely overlooked on its 1988 release, it found a huge second life "
            "after soundtracking the final scene of \u2018Fight Club\u2019 in 1999, "
            "introducing Pixies to an entirely new generation of listeners."
        ),
    },
    {
        "title": "River", "artist": "Joni Mitchell",
        "search": "River Joni Mitchell",
        "description": (
            "Written for 1971's \u2018Blue\u2019, \"River\" quotes the opening notes "
            "of \u2018Jingle Bells\u2019 in a minor key, turning a Christmas song "
            "into a melancholy backdrop for a story about heartbreak and wanting "
            "to disappear.\n\n"
            "Despite its wintry imagery it was never released as a single, yet it "
            "has since become one of the most widely covered songs in Mitchell's "
            "entire catalogue, especially around the holidays."
        ),
    },
    {
        "title": "Strange Fruit", "artist": "Billie Holiday",
        "search": "Strange Fruit Billie Holiday",
        "description": (
            "Adapted from a poem by schoolteacher Abel Meeropol about the lynching "
            "of Black Americans in the South, \"Strange Fruit\" was too politically "
            "charged for Holiday's usual label, forcing her to record it elsewhere "
            "in 1939.\n\n"
            "She reportedly closed every live performance of it with the lights "
            "dimmed and no encore, refusing to let any other song follow it. It's "
            "widely considered one of the first true protest songs in American "
            "popular music."
        ),
    },
    {
        "title": "Voodoo Child (Slight Return)", "artist": "Jimi Hendrix",
        "search": "Voodoo Child Slight Return Jimi Hendrix",
        "description": (
            "Recorded almost as an afterthought after a documentary film crew asked "
            "the Jimi Hendrix Experience to keep playing for the cameras, \"Voodoo "
            "Child (Slight Return)\" became one of the most virtuosic guitar "
            "recordings of the era almost by accident.\n\n"
            "It gave Hendrix his only UK number one single, released after his "
            "death in 1970, and remains a foundational text for rock guitarists "
            "studying his use of wah-wah and feedback."
        ),
    },
    {
        "title": "At Last", "artist": "Etta James",
        "search": "At Last Etta James",
        "description": (
            "Though written years earlier for a 1941 film, \"At Last\" became "
            "definitively Etta James's song after her lush 1960 recording, complete "
            "with a full orchestral arrangement rare for an R&B single of the time.\n\n"
            "It has since become one of the most requested wedding songs in "
            "American music, despite James herself later saying she grew tired of "
            "being reduced to just that one recording."
        ),
    },
    {
        "title": "Blue Moon of Kentucky", "artist": "Bill Monroe",
        "search": "Blue Moon of Kentucky Bill Monroe",
        "description": (
            "Written as a slow waltz, \"Blue Moon of Kentucky\" is considered a "
            "founding document of bluegrass music, a genre Bill Monroe is widely "
            "credited with inventing single-handedly.\n\n"
            "A young Elvis Presley reworked it into an up-tempo rockabilly single "
            "in 1954, and the two very different versions \u2014 waltz and rocker "
            "\u2014 are still performed side by side as a lesson in how genres "
            "split from a single source."
        ),
    },
    {
        "title": "Tutti Frutti", "artist": "Little Richard",
        "search": "Tutti Frutti Little Richard",
        "description": (
            "Little Richard's original lyrics were far too explicit for 1955 radio, "
            "so they were hastily rewritten just before recording, though his wild "
            "vocal delivery and piano playing stayed just as untamed.\n\n"
            "Its opening \u201cA-wop-bop-a-loo-bop\u201d is one of the most "
            "recognisable vocal hooks in rock history, and the song is widely "
            "credited as one of the true starting points of rock and roll itself."
        ),
    },
    {
        "title": "Johnny B. Goode", "artist": "Chuck Berry",
        "search": "Johnny B. Goode Chuck Berry",
        "description": (
            "Chuck Berry's autobiographical guitar riff and lyrics about a "
            "country boy who could \"play a guitar just like ringing a bell\" "
            "became the defining blueprint for rock and roll guitar playing.\n\n"
            "It was famously included on the Voyager Golden Record, launched into "
            "space in 1977 as a representation of humanity's music \u2014 making "
            "it, quite literally, one of the furthest-travelled songs ever "
            "recorded."
        ),
    },
    {
        "title": "My Girl", "artist": "The Temptations",
        "search": "My Girl The Temptations",
        "description": (
            "Written by Smokey Robinson, \"My Girl\" gave the Temptations their "
            "first number one single and became one of Motown's most enduring "
            "songwriting achievements, with its instantly hummable opening bassline.\n\n"
            "David Ruffin's lead vocal, recorded in a single unrehearsed take "
            "according to studio legend, helped define the smooth, romantic sound "
            "Motown would become famous for throughout the decade."
        ),
    },
    {
        "title": "I Want You Back", "artist": "The Jackson 5",
        "search": "I Want You Back Jackson 5",
        "description": (
            "Michael Jackson was just eleven years old when he recorded the lead "
            "vocal on \"I Want You Back\", his precocious delivery convincing "
            "Motown to build an entire family act around him and his brothers.\n\n"
            "It became the label's fastest-selling single up to that point, and "
            "remains one of the most joyfully constructed pop-soul records of the "
            "era, packed with hooks in nearly every bar."
        ),
    },
    {
        "title": "Gimme Shelter", "artist": "The Rolling Stones",
        "search": "Gimme Shelter The Rolling Stones",
        "description": (
            "Written amid the Vietnam War and a string of political assassinations, "
            "\"Gimme Shelter\" opens with one of the most ominous guitar intros in "
            "rock before Merry Clayton's blistering, nearly unrehearsed vocal takes "
            "over.\n\n"
            "Clayton, pulled out of bed at midnight to record it, reportedly cracked "
            "her voice mid-take from the sheer intensity \u2014 the take used on "
            "the record is the one with the crack left in."
        ),
    },
    {
        "title": "Heroes", "artist": "David Bowie",
        "search": "Heroes David Bowie",
        "description": (
            "Recorded in Berlin within sight of the Wall dividing the city, "
            "\"Heroes\" was inspired by producer Tony Visconti and a backing "
            "singer embracing near the studio window, close enough to the "
            "border to feel the divide.\n\n"
            "Guitarist Robert Fripp built the song's soaring, feedback-heavy "
            "guitar line from layered passes at different distances from his amp, "
            "creating a texture no one had quite recorded before."
        ),
    },
    {
        "title": "Once in a Lifetime", "artist": "Talking Heads",
        "search": "Once in a Lifetime Talking Heads",
        "description": (
            "Built from a looped groove the band jammed for hours before David "
            "Byrne wrote lyrics over the top, \"Once in a Lifetime\" borrows its "
            "spoken-word cadence partly from radio preachers Byrne had been "
            "listening to.\n\n"
            "Its jerky, hypnotic music video, choreographed with movements inspired "
            "by Japanese Noh theatre and religious possession, became just as "
            "influential as the song itself on early MTV."
        ),
    },
    {
        "title": "Rocket Man", "artist": "Elton John",
        "search": "Rocket Man Elton John",
        "description": (
            "Written by lyricist Bernie Taupin after reading Ray Bradbury short "
            "stories, \"Rocket Man\" reframes space travel as a mundane, lonely "
            "job rather than a heroic adventure, a deliberately unglamorous take "
            "on a very glamorous subject.\n\n"
            "Elton John's aching vocal delivery and the song's sweeping "
            "production helped make it one of the defining singles of his "
            "imperial mid-1970s run."
        ),
    },
    {
        "title": "Blackbird", "artist": "The Beatles",
        "search": "Blackbird The Beatles",
        "description": (
            "Paul McCartney has said \"Blackbird\", recorded solo on acoustic "
            "guitar, was written in response to the civil rights struggles "
            "unfolding in America in 1968, using the bird as a quiet metaphor "
            "for a Black woman finding the strength to rise.\n\n"
            "The finger-picked guitar part, inspired by Bach, has since become "
            "one of the most commonly taught pieces for beginner acoustic "
            "guitarists worldwide."
        ),
    },
    {
        "title": "Suzanne", "artist": "Leonard Cohen",
        "search": "Suzanne Leonard Cohen",
        "description": (
            "Originally published as a poem before Judy Collins convinced Leonard "
            "Cohen to set it to music, \"Suzanne\" describes a real friendship with "
            "a Montreal dancer, blending the spiritual and the romantic without "
            "ever quite resolving which one it is.\n\n"
            "Cohen was reportedly nervous about his own singing voice and almost "
            "didn't record it himself, letting other artists' covers reach the "
            "charts first before his own version became the definitive one."
        ),
    },
    {
        "title": "The Sound of Silence", "artist": "Simon & Garfunkel",
        "search": "The Sound of Silence Simon and Garfunkel",
        "description": (
            "Recorded first as a quiet acoustic folk song that went nowhere "
            "commercially, \"The Sound of Silence\" was secretly overdubbed with "
            "electric instruments by a producer without the duo's knowledge after "
            "they had already split up.\n\n"
            "The reworked version became a surprise number one, reuniting Simon "
            "and Garfunkel almost by accident and launching their career as one "
            "of the era's defining folk-rock acts."
        ),
    },
    {
        "title": "What's Going On", "artist": "Marvin Gaye",
        "search": "What's Going On Marvin Gaye",
        "description": (
            "Inspired partly by his brother's accounts of serving in Vietnam and "
            "partly by police brutality he witnessed firsthand, Marvin Gaye had "
            "to fight Motown's Berry Gordy to release \"What's Going On\" at all, "
            "since Gordy considered it too political for a pop single.\n\n"
            "Its overlapping, conversational vocal layers and jazz-inflected "
            "arrangement were unlike anything else on Motown at the time, and it "
            "became one of the label's most critically celebrated records."
        ),
    },
    {
        "title": "Waterloo Sunset", "artist": "The Kinks",
        "search": "Waterloo Sunset The Kinks",
        "description": (
            "Ray Davies has described \"Waterloo Sunset\" as his most personal "
            "song, a quiet tribute to London itself rather than any specific "
            "romance, built around watching the city from a train window.\n\n"
            "Its gentle, unhurried melody stood in deliberate contrast to the "
            "harder rock sound The Kinks were known for, and it's now widely "
            "regarded as one of the finest pieces of British songwriting from "
            "the era."
        ),
    },
    {
        "title": "Hey Ya!", "artist": "OutKast",
        "search": "Hey Ya OutKast",
        "description": (
            "Andre 3000 has said \"Hey Ya!\" is actually a fairly bleak song about "
            "relationships falling apart, deliberately disguised behind one of the "
            "most infectiously upbeat melodies of the 2000s.\n\n"
            "Its clapping breakdown and genre-blending production, part funk, part "
            "rock, part pop, made it one of the rare singles to top both hip-hop "
            "and mainstream pop charts at once."
        ),
    },
    {
        "title": "So What", "artist": "Miles Davis",
        "search": "So What Miles Davis",
        "description": (
            "Opening 1959's \u2018Kind of Blue\u2019, \"So What\" was built around "
            "modal scales rather than the dense chord changes typical of bebop, "
            "giving the musicians far more room to improvise melodically.\n\n"
            "The album remains the best-selling jazz record of all time, and "
            "\"So What\"'s laid-back call-and-response bass and horn line is now "
            "one of the most widely recognised phrases in jazz history."
        ),
    },
    {
        "title": "Immigrant Song", "artist": "Led Zeppelin",
        "search": "Immigrant Song Led Zeppelin",
        "description": (
            "Written after a trip to Iceland, \"Immigrant Song\" imagines Robert "
            "Plant as a Viking warrior, complete with a war-cry vocal that became "
            "one of the most instantly recognisable openings in hard rock.\n\n"
            "At under two and a half minutes, it's remarkably short for Led "
            "Zeppelin, hitting hard and fast rather than sprawling the way many "
            "of their other tracks did."
        ),
    },
    {
        "title": "I Will Survive", "artist": "Gloria Gaynor",
        "search": "I Will Survive Gloria Gaynor",
        "description": (
            "Originally recorded as a B-side, \"I Will Survive\" only became a hit "
            "after DJs started flipping the single over, eventually pushing "
            "Gloria Gaynor to the top of the charts and turning it into one of "
            "disco's defining anthems.\n\n"
            "Its message of recovering from heartbreak turned it into an "
            "unofficial anthem for the LGBTQ+ community, a status it has held "
            "for decades since."
        ),
    },
    {
        "title": "Ex-Factor", "artist": "Lauryn Hill",
        "search": "Ex-Factor Lauryn Hill",
        "description": (
            "Taken from 1998's \u2018The Miseducation of Lauryn Hill\u2019, "
            "\"Ex-Factor\" blends soul, hip-hop and gospel-inflected vocal runs "
            "into a raw account of a relationship neither party can quite let go "
            "of.\n\n"
            "The album went on to win five Grammy Awards, and \"Ex-Factor\" "
            "itself has been sampled and interpolated by artists across hip-hop "
            "for decades since, most famously by Drake."
        ),
    },
    {
        "title": "Zombie", "artist": "The Cranberries",
        "search": "Zombie The Cranberries",
        "description": (
            "Written by Dolores O'Riordan in response to an IRA bombing in "
            "Warrington, England that killed two children, \"Zombie\" was a "
            "marked departure from The Cranberries' earlier, gentler alternative "
            "rock sound.\n\n"
            "Its grunge-inflected guitars and O'Riordan's furious vocal delivery "
            "made it one of the most direct protest songs of the 1990s, and it "
            "remains the band's most streamed and recognised track worldwide."
        ),
    },
    {
        "title": "Killing Me Softly with His Song", "artist": "Roberta Flack",
        "search": "Killing Me Softly With His Song Roberta Flack",
        "description": (
            "Inspired by a singer-songwriter named Lori Lieberman who was moved "
            "to tears watching Don McLean perform live, \"Killing Me Softly\" "
            "became a hit for Roberta Flack after she heard an early version on "
            "an in-flight airline recording.\n\n"
            "Her hushed, deliberate vocal delivery won Grammys for both Record "
            "and Song of the Year, and the song was later reintroduced to a "
            "new generation via the Fugees' 1996 cover."
        ),
    },
]

AOTD_ENTRIES = [
    {
        "name": "Fela Kuti", "genre": "Afrobeat Pioneer",
        "search": "Fela Kuti",
        "description": (
            "Fela Anikulapo Kuti was a Nigerian multi-instrumentalist, bandleader and "
            "outspoken political activist who, through the 1970s, forged an entirely new "
            "genre out of highlife, jazz, funk and traditional Yoruba rhythms \u2014 a "
            "sound he named Afrobeat. His songs were rarely short: sprawling, "
            "horn-driven grooves built around interlocking drums and bass, often "
            "stretching past fifteen minutes, with call-and-response vocals sung half "
            "in English and half in pidgin.\n\n"
            "He isn\u2019t a chart-topping name the way some of his contemporaries "
            "became, and that\u2019s rather the point of picking him \u2014 the Artist "
            "of the Day doesn\u2019t have to be the biggest name in music, just one "
            "worth spending a little time with. Fela used his music as a direct "
            "weapon against the corrupt Nigerian military government of his era, "
            "founding his own compound, Kalakuta Republic, which he declared "
            "independent from the state entirely.\n\n"
            "That defiance came at enormous personal cost: his home was raided and "
            "burned by soldiers in 1977, and his mother, the activist Funmilayo "
            "Ransome-Kuti, later died from injuries sustained in the attack. Rather "
            "than retreat, Fela responded with some of his most furious and enduring "
            "records, including \u2018Zombie\u2019, a searing critique of military "
            "obedience that remains one of the most powerful protest songs ever "
            "recorded.\n\n"
            "Decades on, his influence runs through Afrobeats, hip-hop and jazz alike, "
            "carried forward by his sons Femi and Seun Kuti, who still tour his songs "
            "today. Whether or not you\u2019d ever heard his name before this page, "
            "that\u2019s exactly why he\u2019s here."
        ),
    },
    {
        "name": "Nina Simone", "genre": "Singer, Pianist & Civil Rights Icon",
        "search": "Nina Simone",
        "description": (
            "Classically trained on piano from childhood, Nina Simone was rejected from "
            "the Curtis Institute of Music in 1951 in what she always believed was a "
            "racially motivated decision \u2014 a wound that shaped much of her life and "
            "art that followed.\n\n"
            "She moved between jazz, blues, folk and classical with total ease, often "
            "inside the same song, and became one of the defining musical voices of the "
            "American civil rights movement with tracks like \u2018Mississippi Goddam\u2019 "
            "and \u2018Four Women\u2019.\n\n"
            "Her performances were famously uncompromising; she would stop mid-song to "
            "reprimand a talking audience, and refused for most of her career to soften her "
            "message for commercial comfort.\n\n"
            "Whether or not she's a household name to a given listener today, her fingerprints "
            "are all over decades of soul, hip-hop and pop that sampled or covered her "
            "work long after her death in 2003."
        ),
    },
    {
        "name": "Rodriguez", "genre": "Folk-Rock Singer-Songwriter",
        "search": "Rodriguez Sugar Man",
        "description": (
            "Sixto Rodriguez recorded two folk-rock albums in Detroit in the early 1970s "
            "that went almost completely unnoticed in the United States \u2014 and he "
            "went back to working construction, believing his music career was over.\n\n"
            "Unbeknownst to him, bootleg copies of his record had spread through apartheid-era "
            "South Africa, where he became, without exaggeration, one of the biggest rock "
            "stars in the country's history \u2014 all while rumours circulated that he had "
            "died on stage.\n\n"
            "He had no idea any of this was happening until the late 1990s, when fans "
            "tracked him down and he was finally flown out to play sold-out arena shows to "
            "crowds who already knew every word.\n\n"
            "The 2012 documentary \u2018Searching for Sugar Man\u2019 told the story to a "
            "global audience and won an Academy Award, decades after the music itself was "
            "made \u2014 proof that importance and fame don't always arrive on the same "
            "schedule."
        ),
    },
    {
        "name": "Big Mama Thornton", "genre": "Blues Singer",
        "search": "Big Mama Thornton",
        "description": (
            "Willie Mae \u201cBig Mama\u201d Thornton recorded the original version of "
            "\u2018Hound Dog\u2019 in 1952, three years before Elvis Presley's cover made "
            "the song a global phenomenon and Presley a household name.\n\n"
            "A powerhouse blues singer and drummer from Alabama, she toured relentlessly "
            "through the segregated South, and also wrote and first recorded \u2018Ball "
            "and Chain\u2019, later made famous by Janis Joplin.\n\n"
            "She saw comparatively little of the money or credit that followed from either "
            "song's massive success elsewhere, a common story for Black blues artists of "
            "her era whose songs were covered into the mainstream.\n\n"
            "Her raw, commanding voice remains a direct line back to the roots of rock and "
            "roll itself \u2014 a reminder that some of music's biggest hits started with "
            "artists far less famous than the ones who made them stars."
        ),
    },
    {
        "name": "Sister Rosetta Tharpe", "genre": "Gospel & Rock Guitar Pioneer",
        "search": "Sister Rosetta Tharpe",
        "description": (
            "Long before Chuck Berry or Elvis Presley, Sister Rosetta Tharpe was playing "
            "distorted, driving electric guitar lines in the 1930s and 40s that would "
            "later become the entire vocabulary of rock and roll.\n\n"
            "She came up performing gospel music but scandalised some of her religious "
            "audience by playing it in nightclubs alongside secular blues and swing, "
            "blending the sacred and the secular in a way almost nobody else dared to at "
            "the time.\n\n"
            "Her 1944 recording of \u2018Strange Things Happening Every Day\u2019 is "
            "often cited by historians as one of the very first rock and roll records, "
            "years before the genre had a name.\n\n"
            "She's rarely mentioned in the same breath as the rock pioneers she directly "
            "influenced, which is exactly why she's worth featuring here."
        ),
    },
    {
        "name": "Woody Guthrie", "genre": "Folk Singer-Songwriter",
        "search": "Woody Guthrie",
        "description": (
            "Travelling across Depression-era America on freight trains and highways, "
            "Woody Guthrie wrote hundreds of songs documenting the lives of migrant "
            "workers, union organisers and the rural poor he met along the way.\n\n"
            "His best-known song, \u2018This Land Is Your Land\u2019, was written partly "
            "as a pointed response to \u2018God Bless America\u2019, though the verses "
            "critical of inequality are rarely sung in schools today.\n\n"
            "His guitar famously bore the handwritten slogan \u201cThis Machine Kills "
            "Fascists\u201d, a blunt statement of the political convictions running "
            "through nearly everything he recorded.\n\n"
            "Bob Dylan, Bruce Springsteen and countless folk and protest artists since "
            "have named him as a direct and foundational influence."
        ),
    },
    {
        "name": "Betty Davis", "genre": "Funk Singer",
        "search": "Betty Davis",
        "description": (
            "Betty Davis released three albums of raw, sexually explicit funk in the "
            "early-to-mid 1970s that were too far ahead of their time for mainstream "
            "radio, and too confrontational for many stations to touch at all.\n\n"
            "She briefly married Miles Davis and is widely credited with introducing "
            "him to Jimi Hendrix and Sly Stone, nudging his sound toward the "
            "electric fusion period that followed.\n\n"
            "Her own records were commercial flops on release, and she largely retreated "
            "from the industry by the end of the decade, reportedly worn down by the "
            "backlash to her image and lyrics.\n\n"
            "Reissued decades later, her catalogue is now widely regarded as some of "
            "the boldest and most uncompromising funk ever recorded."
        ),
    },
    {
        "name": "Karen Dalton", "genre": "Folk & Blues Singer",
        "search": "Karen Dalton",
        "description": (
            "A fixture of the early-1960s Greenwich Village folk scene alongside Bob "
            "Dylan, who called her his favourite singer in the whole scene, Karen "
            "Dalton nonetheless resisted recording for years.\n\n"
            "Her two studio albums, released almost reluctantly, feature a cracked, "
            "aching voice often compared to Billie Holiday, wrapped around traditional "
            "folk and blues songs rather than originals.\n\n"
            "She struggled with addiction and poverty for most of her life and died "
            "largely unrecognised in 1993, her records having sold poorly at the time.\n\n"
            "A wave of reissues and tributes since has slowly built her a devoted "
            "following she never got to see in her own lifetime."
        ),
    },
    {
        "name": "Mississippi John Hurt", "genre": "Delta Blues Guitarist",
        "search": "Mississippi John Hurt",
        "description": (
            "Mississippi John Hurt recorded a handful of songs in 1928 that sold "
            "poorly, then returned to farming in rural Mississippi for over thirty "
            "years, apparently content to be forgotten by the record industry.\n\n"
            "A folk music researcher tracked him down in 1963 after decoding a place "
            "name in one of his old lyrics, and Hurt was suddenly performing at "
            "folk festivals to enthusiastic young audiences in his seventies.\n\n"
            "His fingerpicking guitar style, gentle and melodic rather than raw and "
            "aggressive, became hugely influential on the folk revival guitarists who "
            "discovered him during this unexpected second act.\n\n"
            "He died just a few years into his rediscovery, but left behind a style "
            "still taught to fingerstyle guitarists today."
        ),
    },
    {
        "name": "Alice Coltrane", "genre": "Jazz Pianist & Harpist",
        "search": "Alice Coltrane",
        "description": (
            "A classically trained pianist who later took up the harp, Alice Coltrane "
            "built a body of spiritual jazz recordings in the 1970s that blended free "
            "jazz, Indian classical music and Hindu devotional themes.\n\n"
            "She was married to saxophonist John Coltrane until his death in 1967, "
            "after which she continued to develop his final, most experimental "
            "musical ideas on her own terms.\n\n"
            "Later in life she largely stepped back from the commercial music industry "
            "to lead an ashram in California, recording devotional cassette tapes for "
            "her community rather than for public release.\n\n"
            "Her catalogue has found a substantial new audience through reissues and "
            "sampling in the decades since, introducing her far beyond jazz circles."
        ),
    },
    {
        "name": "Gil Scott-Heron", "genre": "Spoken-Word Poet & Musician",
        "search": "Gil Scott-Heron",
        "description": (
            "Often cited as a forerunner of hip-hop, Gil Scott-Heron blended jazz, "
            "soul and spoken-word poetry into sharp, political recordings throughout "
            "the 1970s, most famously \u2018The Revolution Will Not Be Televised\u2019.\n\n"
            "His work directly addressed racism, poverty and consumer culture at a "
            "time when few artists on major labels were willing to be so explicit.\n\n"
            "Decades later, artists across hip-hop routinely cite him as foundational, "
            "both for his rhythmic delivery and his willingness to use music as direct "
            "social commentary.\n\n"
            "He struggled publicly with addiction later in life, but his final album, "
            "released in 2010, was widely praised as a genuine late-career return to "
            "form."
        ),
    },
    {
        "name": "Broadcast", "genre": "Electronic & Psychedelic Pop Band",
        "search": "Broadcast band",
        "description": (
            "Formed in Birmingham, England in the early 1990s, Broadcast built a "
            "sound out of vintage synthesisers, library-music textures and Trish "
            "Keenan's cool, detached vocals that felt like it belonged to no single "
            "decade.\n\n"
            "Their records drew heavily on 1960s and 70s soundtrack and public "
            "information film music, filtered through a distinctly modern, "
            "melancholic pop sensibility.\n\n"
            "Keenan died suddenly from pneumonia in 2011, cutting short a catalogue "
            "that had quietly influenced a generation of electronic and dream-pop "
            "artists.\n\n"
            "Their records remain a reference point for anyone chasing that specific, "
            "hard-to-name blend of warmth and unease."
        ),
    },
    {
        "name": "Arthur Russell", "genre": "Cellist & Composer",
        "search": "Arthur Russell",
        "description": (
            "Arthur Russell moved between disco, minimalist composition, folk-pop and "
            "avant-garde cello performance, often within the same year, releasing "
            "music under a dozen different names and projects.\n\n"
            "Much of his catalogue existed only as unfinished demos and tapes at the "
            "time of his death from AIDS-related illness in 1992, since he rarely "
            "considered any recording truly finished.\n\n"
            "Posthumous archival releases in the 2000s introduced his work to a much "
            "wider audience than he ever reached during his own lifetime.\n\n"
            "He's now regularly cited across dance, indie and classical circles alike "
            "as one of the most genuinely uncategorisable musicians of his era."
        ),
    },
    {
        "name": "Shuggie Otis", "genre": "Multi-Instrumentalist & Songwriter",
        "search": "Shuggie Otis",
        "description": (
            "A teenage guitar prodigy who had already toured with his father's blues "
            "revue and recorded with Frank Zappa, Shuggie Otis released \u2018Inspiration "
            "Information\u2019 in 1974 as a one-man band, playing nearly every "
            "instrument himself.\n\n"
            "The album sold poorly on release and his label dropped him shortly "
            "after, effectively ending his mainstream recording career at just "
            "twenty years old.\n\n"
            "A 2001 reissue found the record decades ahead of its time, its "
            "drum-machine-and-guitar sound directly anticipating neo-soul and "
            "bedroom production that followed decades later.\n\n"
            "He largely stepped away from the industry afterward, making his "
            "rediscovery all the more striking when it finally arrived."
        ),
    },
    {
        "name": "Roky Erickson", "genre": "Psychedelic Rock Pioneer",
        "search": "Roky Erickson 13th Floor Elevators",
        "description": (
            "As frontman of The 13th Floor Elevators, Roky Erickson helped originate "
            "the term \u201cpsychedelic rock\u201d itself in 1966, years before the "
            "genre became a mainstream label.\n\n"
            "A 1969 marijuana arrest led to him pleading insanity to avoid prison, "
            "resulting in years of institutionalisation and psychiatric treatment "
            "that permanently affected his health.\n\n"
            "He continued recording sporadically for decades afterward, blending "
            "horror-movie imagery with genuinely melodic rock songwriting in a way "
            "few artists have matched.\n\n"
            "A wave of tribute concerts and reissues in the 2000s helped restore him "
            "to something like the recognition his influence always deserved."
        ),
    },
    {
        "name": "Nick Drake", "genre": "Folk Singer-Songwriter",
        "search": "Nick Drake",
        "description": (
            "Nick Drake released three quietly devastating folk albums between "
            "1969 and 1972 that sold so poorly he reportedly believed his music "
            "career had already ended by the time he died in 1974.\n\n"
            "A 1999 Volkswagen advert using \u2018Pink Moon\u2019 introduced him to "
            "a huge new audience decades after his death, turning a commercial "
            "failure in his lifetime into one of folk music's most enduring "
            "cult catalogues."
        ),
    },
    {
        "name": "Vashti Bunyan", "genre": "Folk Singer",
        "search": "Vashti Bunyan",
        "description": (
            "After her one and only 1970 album sold so poorly it was quickly "
            "deleted, Vashti Bunyan gave up music entirely and moved to a "
            "remote farm, assuming her recording career was simply over.\n\n"
            "Decades later, collectors and a new generation of freak-folk "
            "musicians rediscovered the record, prompting her genuinely "
            "unexpected return to music in her sixties."
        ),
    },
    {
        "name": "Judee Sill", "genre": "Singer-Songwriter",
        "search": "Judee Sill",
        "description": (
            "Judee Sill wrote intricate, hymn-like songs blending folk, baroque "
            "pop and gospel, becoming the very first artist signed to David "
            "Geffen's Asylum Records label in the early 1970s.\n\n"
            "Struggles with addiction derailed her career after just two albums, "
            "and she died in 1979 largely forgotten, though her records have "
            "since been reissued to considerable critical acclaim."
        ),
    },
    {
        "name": "Captain Beefheart", "genre": "Avant-Garde Rock Musician",
        "search": "Captain Beefheart Trout Mask Replica",
        "description": (
            "Born Don Van Vliet, Captain Beefheart made his backing band, the "
            "Magic Band, rehearse his sprawling 1969 double album \u2018Trout "
            "Mask Replica\u2019 for months in near-isolation, reportedly under "
            "gruelling conditions.\n\n"
            "The resulting record, jagged and largely without conventional "
            "melody, is now considered one of the most influential and "
            "uncompromising albums in rock history."
        ),
    },
    {
        "name": "Robert Wyatt", "genre": "Drummer, Singer & Composer",
        "search": "Robert Wyatt",
        "description": (
            "A founding member of Soft Machine, Robert Wyatt fell from a "
            "fourth-floor window at a party in 1973, leaving him paralysed from "
            "the waist down and unable to continue drumming.\n\n"
            "He rebuilt an entirely new solo career afterward as a singer and "
            "composer, blending jazz, political songwriting and his own "
            "distinctively fragile voice into one of British music's most "
            "quietly influential catalogues."
        ),
    },
    {
        "name": "Linda Perhacs", "genre": "Folk Singer",
        "search": "Linda Perhacs",
        "description": (
            "A practising dental hygienist by trade, Linda Perhacs released a "
            "single, largely overlooked psychedelic folk album in 1970 after a "
            "patient who worked in film music encouraged her to record it.\n\n"
            "She returned to dentistry afterward for decades, unaware the record "
            "had quietly built a cult following until fans eventually tracked "
            "her down in the 2000s."
        ),
    },
    {
        "name": "Bill Fay", "genre": "Singer-Songwriter",
        "search": "Bill Fay",
        "description": (
            "Bill Fay released two commercially unsuccessful albums in the early "
            "1970s blending folk, gospel and orchestral arrangements before his "
            "label dropped him and he spent years working manual labour jobs.\n\n"
            "Wilco's Jeff Tweedy became a vocal champion of his work decades "
            "later, helping spark a genuine late-career revival that saw Fay "
            "recording new albums again in his seventies."
        ),
    },
    {
        "name": "Emitt Rhodes", "genre": "Multi-Instrumentalist Songwriter",
        "search": "Emitt Rhodes",
        "description": (
            "Often compared to a one-man Beatles, Emitt Rhodes recorded lush "
            "power-pop albums entirely by himself in a home studio in the early "
            "1970s, playing every instrument on the record.\n\n"
            "A punishing contract requiring an album every six months, combined "
            "with poor sales, effectively ended his recording career by his "
            "mid-twenties, though his sound quietly influenced decades of "
            "bedroom-pop that followed."
        ),
    },
    {
        "name": "Connie Converse", "genre": "Singer-Songwriter",
        "search": "Connie Converse",
        "description": (
            "Recording plainspoken, confessional folk songs in the early 1950s, "
            "years before that style became fashionable, Connie Converse never "
            "found an audience and eventually gave up entirely.\n\n"
            "In 1974 she packed her belongings into her car and drove away, "
            "never to be heard from again. Her home recordings were only "
            "rediscovered and released decades later, in 2009."
        ),
    },
    {
        "name": "Jackie Shane", "genre": "Soul Singer",
        "search": "Jackie Shane Any Other Way",
        "description": (
            "A Black transgender soul singer performing openly in Toronto clubs "
            "throughout the 1960s, Jackie Shane built a devoted live following "
            "with hits like \u2018Any Other Way\u2019, despite the era's open "
            "hostility toward her identity.\n\n"
            "She disappeared from the public eye in the mid-1970s and lived in "
            "seclusion for decades before a Grammy-nominated archival reissue in "
            "2017 finally brought her story to a much wider audience."
        ),
    },
    {
        "name": "Charley Patton", "genre": "Delta Blues Pioneer",
        "search": "Charley Patton",
        "description": (
            "Often called the father of the Delta blues, Charley Patton's "
            "raspy, percussive guitar style and showmanship in the 1920s and "
            "30s directly shaped everyone from Son House to Muddy Waters.\n\n"
            "He recorded only a modest catalogue before his death in 1934, but "
            "his influence on the entire lineage of American blues guitar is "
            "difficult to overstate."
        ),
    },
    {
        "name": "Skip James", "genre": "Delta Blues Musician",
        "search": "Skip James",
        "description": (
            "Skip James recorded a small set of haunting, minor-key blues songs "
            "in 1931 using an unusual open tuning, then largely vanished from "
            "music, working as a preacher and sharecropper for decades.\n\n"
            "Blues revivalists tracked him down in a hospital in 1964, and his "
            "unexpected return to performing at folk festivals introduced his "
            "eerie style to a whole new generation of listeners."
        ),
    },
    {
        "name": "Blind Willie Johnson", "genre": "Gospel Blues Guitarist",
        "search": "Blind Willie Johnson",
        "description": (
            "Blinded as a child, Blind Willie Johnson recorded a small but "
            "towering catalogue of gospel blues in the late 1920s, his "
            "rasping vocals and slide guitar work later cited as a direct "
            "influence on rock guitarists like Eric Clapton and Ry Cooder.\n\n"
            "His wordless instrumental \u2018Dark Was the Night, Cold Was the "
            "Ground\u2019 was included on the Voyager Golden Record sent into "
            "space in 1977."
        ),
    },
    {
        "name": "Elizabeth Cotten", "genre": "Folk & Blues Guitarist",
        "search": "Elizabeth Cotten Freight Train",
        "description": (
            "Elizabeth Cotten wrote \u2018Freight Train\u2019 as a child but "
            "didn't record it until her sixties, after being discovered while "
            "working as a housekeeper for the folk-singing Seeger family.\n\n"
            "A left-handed guitarist who played a right-handed guitar upside "
            "down, she developed a completely self-taught fingerpicking style "
            "now studied by guitarists worldwide as \"Cotten picking\"."
        ),
    },
    {
        "name": "Jimmy Scott", "genre": "Jazz Vocalist",
        "search": "Jimmy Scott jazz singer",
        "description": (
            "A rare genetic condition kept Jimmy Scott's voice permanently "
            "high and unchanged from childhood, giving him one of the most "
            "instantly recognisable, aching vocal tones in jazz.\n\n"
            "Record label disputes kept him largely out of the studio for over "
            "two decades in his prime, and it took until his seventies for a "
            "wave of new recordings to finally bring him the wider recognition "
            "his voice had always deserved."
        ),
    },
    {
        "name": "Moondog", "genre": "Composer & Street Musician",
        "search": "Moondog composer",
        "description": (
            "Blind since a teenage accident, Louis Hardin, better known as "
            "Moondog, spent decades busking on New York street corners dressed "
            "as a Viking while composing intricate, self-taught classical "
            "pieces on the side.\n\n"
            "Despite performing on the street, he recorded albums for major "
            "labels and was quietly studied and admired by classical composers "
            "like Philip Glass, who briefly lived with him as a young man."
        ),
    },
    {
        "name": "Tim Buckley", "genre": "Singer-Songwriter",
        "search": "Tim Buckley",
        "description": (
            "Tim Buckley moved restlessly between folk, jazz and experimental "
            "avant-garde vocal music across nine albums in less than a decade, "
            "refusing to settle into any single commercially safe style.\n\n"
            "He died of an accidental overdose in 1975 at just 28, but his son "
            "Jeff Buckley would go on to have his own major impact on music two "
            "decades later, tying two very different careers together."
        ),
    },
    {
        "name": "Judy Henske", "genre": "Folk Singer",
        "search": "Judy Henske",
        "description": (
            "Known for a booming, theatrical voice unusual among the hushed "
            "folk singers of the early 1960s, Judy Henske built a strong live "
            "reputation on the Greenwich Village and West Coast folk circuits.\n\n"
            "Her boundary-pushing 1969 album \u2018Farewell Aldebaran\u2019, made "
            "with future Doors producer Jac Holzman's backing, remains a "
            "strange, ambitious cult favourite decades later."
        ),
    },
    {
        "name": "The Slits", "genre": "Punk Band",
        "search": "The Slits Cut album",
        "description": (
            "One of the first all-female punk bands, The Slits mixed reggae "
            "rhythms into their raw, confrontational sound on 1979's "
            "\u2018Cut\u2019, whose cover \u2014 the band covered in mud, "
            "topless \u2014 caused as much stir as the music itself.\n\n"
            "Their refusal to conform to expectations of how women in punk "
            "should look or sound made them hugely influential on riot grrrl "
            "and post-punk acts that followed."
        ),
    },
    {
        "name": "Poly Styrene", "genre": "Punk Singer (X-Ray Spex)",
        "search": "X-Ray Spex Poly Styrene",
        "description": (
            "As frontwoman of X-Ray Spex, Poly Styrene wrote sharp, satirical "
            "punk songs about consumerism and identity while wearing braces and "
            "thrift-store clothes, deliberately rejecting typical rock star "
            "styling.\n\n"
            "One of the first women of colour to front a major UK punk band, "
            "she stepped away from music for years afterward, later citing the "
            "intense pressures of early fame on her mental health."
        ),
    },
    {
        "name": "ESG", "genre": "Post-Punk & Funk Band",
        "search": "ESG band UFO",
        "description": (
            "Formed by four sisters from the South Bronx, ESG built a stripped-"
            "down, bass-and-drums-heavy sound in the late 1970s that would go on "
            "to become one of the most sampled catalogues in hip-hop and dance "
            "music.\n\n"
            "Their track \u2018UFO\u2019 alone has been sampled by dozens of "
            "artists across decades, despite the band themselves seeing very "
            "little commercial success at the time."
        ),
    },
    {
        "name": "Grace Jones", "genre": "Singer & Performance Artist",
        "search": "Grace Jones",
        "description": (
            "Grace Jones fused disco, reggae, new wave and stark visual art "
            "into a persona so striking it arguably overshadowed the fact she "
            "was also a genuinely groundbreaking vocalist and songwriter.\n\n"
            "Albums like 1981's \u2018Nightclubbing\u2019 blended Jamaican "
            "rhythm section players with icy European art-pop production, a "
            "combination almost nobody else was attempting at the time."
        ),
    },
    {
        "name": "Klaus Nomi", "genre": "Operatic New Wave Singer",
        "search": "Klaus Nomi",
        "description": (
            "Klaus Nomi combined an operatic countertenor voice with stark, "
            "geometric costumes and new wave production, creating a stage "
            "persona unlike anything else on the early-1980s New York club "
            "scene.\n\n"
            "He was among the first public figures in the arts to die from "
            "AIDS-related illness, in 1983, cutting short a career that had "
            "only just begun reaching a wider audience."
        ),
    },
    {
        "name": "Scott Walker", "genre": "Singer & Avant-Garde Composer",
        "search": "Scott Walker musician",
        "description": (
            "After finding teen-idol fame with The Walker Brothers, Scott "
            "Walker spent the following decades moving further and further "
            "from pop, eventually making some of the most genuinely "
            "unsettling avant-garde records ever released by a major label.\n\n"
            "Albums like 2006's \u2018The Drift\u2019 feature production choices "
            "such as punching a side of meat for percussion, a world away from "
            "his 1960s chart-topping beginnings."
        ),
    },
    {
        "name": "Terry Callier", "genre": "Folk & Soul Singer-Songwriter",
        "search": "Terry Callier",
        "description": (
            "Terry Callier blended folk guitar with jazz chords and soul "
            "phrasing across a run of albums in the 1970s that sold poorly "
            "enough to push him out of music entirely and into a computer "
            "programming job at the University of Chicago.\n\n"
            "British DJs and acid jazz artists rediscovered his records in the "
            "1990s, prompting a genuinely improbable late-career return to "
            "touring and recording."
        ),
    },
    {
        "name": "Vic Chesnutt", "genre": "Singer-Songwriter",
        "search": "Vic Chesnutt",
        "description": (
            "Paralysed from the chest down after a car accident at eighteen, "
            "Vic Chesnutt taught himself an unconventional guitar technique "
            "using his limited hand movement, developing a raw, plainspoken "
            "songwriting style out of necessity.\n\n"
            "R.E.M.'s Michael Stipe produced his early albums and championed "
            "his work for years, helping bring his darkly funny, unflinching "
            "songs to a wider audience than they might otherwise have reached."
        ),
    },
    {
        "name": "Ivor Cutler", "genre": "Poet & Musician",
        "search": "Ivor Cutler",
        "description": (
            "Ivor Cutler wrote absurdist, deadpan songs and monologues on a "
            "wheezing harmonium, occupying a strange space between music and "
            "comedy that few artists before or since have attempted.\n\n"
            "The Beatles cast him in \u2018Magical Mystery Tour\u2019, and Robert "
            "Wyatt and Billy Connolly were both vocal admirers, though his own "
            "work remained resolutely, happily uncommercial his entire career."
        ),
    },
    {
        "name": "Jandek", "genre": "Outsider Musician",
        "search": "Jandek musician",
        "description": (
            "Operating under near-total anonymity since the late 1970s, Jandek "
            "has released dozens of albums of deliberately dissonant, "
            "unconventionally tuned guitar music without ever granting an "
            "interview or confirming basic biographical facts.\n\n"
            "He gave his first-ever live performance, unannounced, in 2004 after "
            "over two decades of pure studio anonymity, stunning fans who had "
            "assumed he might never perform publicly at all."
        ),
    },
    {
        "name": "Larry Norman", "genre": "Christian Rock Pioneer",
        "search": "Larry Norman musician",
        "description": (
            "Widely credited as the father of Christian rock, Larry Norman "
            "fused gospel themes with genuine rock and roll instrumentation "
            "at a time in the late 1960s when most churches considered rock "
            "music itself sinful.\n\n"
            "His confrontational, mainstream-adjacent sound made him a "
            "controversial figure within the Christian music industry he "
            "effectively helped invent."
        ),
    },
    {
        "name": "Sandy Denny", "genre": "Folk Singer (Fairport Convention)",
        "search": "Sandy Denny Fairport Convention",
        "description": (
            "As lead singer of Fairport Convention, Sandy Denny helped pioneer "
            "British folk-rock, blending traditional English folk songs with "
            "electric instrumentation in a way almost no one else was doing at "
            "the time.\n\n"
            "She was the only guest vocalist ever featured on a Led Zeppelin "
            "studio track, duetting with Robert Plant on \u2018The Battle of "
            "Evermore\u2019, before her death in 1978 at just 31."
        ),
    },
]

HM_ENTRIES = [
    {
        "title": "The British Invasion Begins",
        "date": "The Beatles on The Ed Sullivan Show \u2014 February 9, 1964",
        "search": "The Beatles Meet The Beatles",
        "description": (
            "On the evening of February 9, 1964, an estimated 73 million Americans \u2014 "
            "roughly 40% of the entire population \u2014 tuned in to watch four young "
            "musicians from Liverpool play five songs on live television. It remains "
            "one of the most-watched broadcasts in US television history, and it is "
            "widely regarded as the moment the British Invasion truly began.\n\n"
            "The Beatles had already topped the American charts with \u2018I Want to "
            "Hold Your Hand\u2019 a few weeks earlier, but the Sullivan performance is "
            "what turned chart success into cultural upheaval. Screaming audiences, "
            "mop-top haircuts and a wave of British guitar bands chasing the same "
            "opportunity followed almost overnight.\n\n"
            "Within two years, acts like The Rolling Stones, The Who, The Kinks and "
            "The Animals had all crossed the Atlantic on the same wave, permanently "
            "reshaping American pop music and setting the template for the "
            "guitar-driven rock that would dominate the rest of the decade.\n\n"
            "What earns this moment its place here isn\u2019t just the ratings record "
            "\u2014 it\u2019s that a single television appearance can, occasionally, "
            "genuinely rewrite the direction of an entire industry. That's what makes "
            "it history."
        ),
    },
    {
        "title": "Woodstock Opens Its Gates",
        "date": "Woodstock Music & Art Fair \u2014 August 15, 1969",
        "search": "Woodstock Various Artists",
        "description": (
            "What was planned as a modest, ticketed music festival for around 50,000 "
            "people in rural New York State turned, almost by accident, into a gathering "
            "of nearly half a million \u2014 forcing organisers to simply declare it a "
            "free event once the fences came down.\n\n"
            "Over three rain-soaked days, acts including Jimi Hendrix, Janis Joplin, "
            "The Who and Santana played to a crowd stretching further than most performers "
            "could see, with food, medical care and basic infrastructure stretched far "
            "past what anyone had planned for.\n\n"
            "Hendrix's closing performance of \u2018The Star-Spangled Banner\u2019, all "
            "feedback and distortion, became one of the defining musical images of the "
            "entire decade, played to a crowd exhausted after three days on a muddy farm.\n\n"
            "Despite the chaos \u2014 or perhaps because of it \u2014 Woodstock became "
            "shorthand for an entire era's ideals, and remains the reference point every "
            "festival since has been measured against."
        ),
    },
    {
        "title": "Live Aid Spans Two Continents",
        "date": "Live Aid, Wembley Stadium & JFK Stadium \u2014 July 13, 1985",
        "search": "Live Aid Queen Wembley",
        "description": (
            "Organised in just twelve weeks by Bob Geldof and Midge Ure to raise money "
            "for the Ethiopian famine, Live Aid linked simultaneous concerts in London "
            "and Philadelphia, broadcast live to an estimated global audience of nearly "
            "two billion people.\n\n"
            "Queen's twenty-minute set at Wembley is still regularly named the greatest "
            "live performance in rock history, with Freddie Mercury commanding a stadium "
            "of 72,000 people with nothing more than a piano and a single held note.\n\n"
            "The event raised over \u00a3150 million for famine relief and proved, for "
            "the first time at that scale, that a satellite broadcast could turn a benefit "
            "concert into a genuinely unifying global event.\n\n"
            "Nearly forty years on, it's still the standard every charity concert since "
            "has tried, and largely failed, to match."
        ),
    },
    {
        "title": "Elvis Shakes Up The Ed Sullivan Show",
        "date": "Elvis Presley's third Ed Sullivan appearance \u2014 January 6, 1957",
        "search": "Elvis Presley Jailhouse Rock",
        "description": (
            "By his third and final appearance on The Ed Sullivan Show, Elvis Presley "
            "was already the most controversial performer in America, having been "
            "filmed only from the waist up on earlier broadcasts to avoid showing his "
            "hip movements to a nationwide audience.\n\n"
            "The appearance drew an audience of over 60 million viewers, a staggering "
            "share of American television sets at the time, and effectively confirmed "
            "rock and roll as mainstream, unstoppable entertainment rather than a passing "
            "fad.\n\n"
            "Sullivan himself, initially wary of booking Presley at all, ended the night "
            "by publicly calling him \u201ca real decent, fine boy\u201d on air, a moment "
            "credited with softening a great deal of the moral panic surrounding rock "
            "music at the time.\n\n"
            "It's a reminder that some of music's biggest cultural shifts happened not "
            "in a studio, but live, in front of an audience of millions, in a single "
            "unrepeatable television moment."
        ),
    },
    {
        "title": "Napster Changes Music Forever",
        "date": "Napster launches \u2014 June 1, 1999",
        "search": "Napster era hits 1999",
        "description": (
            "Built by a 19-year-old college dropout named Shawn Fanning, Napster let "
            "anyone with an internet connection share MP3 files directly with strangers "
            "\u2014 and within a year it had tens of millions of users trading music for "
            "free.\n\n"
            "The recording industry sued almost immediately, and a very public 2000 "
            "lawsuit from Metallica turned the fight over file-sharing into front-page "
            "news, with Napster shut down by court order in 2001 having barely existed "
            "for two years.\n\n"
            "But the genie didn't go back in the bottle: the model of instant, on-demand "
            "access to nearly any song ever recorded had already reset listener "
            "expectations for good, paving the way for iTunes and, eventually, for "
            "streaming services entirely.\n\n"
            "Two short years of a scrappy piece of college software changed how the "
            "entire industry sells music to this day \u2014 which is about as clear a "
            "definition of \u201chistory maker\u201d as it gets."
        ),
    },
    {
        "title": "Disco Demolition Night",
        "date": "Comiskey Park, Chicago \u2014 July 12, 1979",
        "search": "Chic Good Times",
        "description": (
            "Between games of a baseball double-header, a Chicago radio DJ invited "
            "fans to bring disco records to be blown up on the field in exchange for "
            "cheap admission \u2014 and roughly 50,000 people showed up, far more than "
            "expected.\n\n"
            "The explosion tore up the outfield turf and triggered a full pitch "
            "invasion, forcing the second game to be forfeited entirely amid the "
            "chaos.\n\n"
            "Critics have long pointed out the event's uncomfortable undertones, given "
            "disco's roots in Black and gay club culture, framing the backlash as "
            "about more than just musical taste.\n\n"
            "Whatever the intent, it's remembered today as the moment mainstream "
            "disco's commercial dominance visibly, dramatically cracked."
        ),
    },
    {
        "title": "MTV Signs On",
        "date": "MTV launches with 'Video Killed the Radio Star' \u2014 August 1, 1981",
        "search": "Video Killed the Radio Star Buggles",
        "description": (
            "MTV's very first broadcast opened with the Buggles' \u2018Video Killed "
            "the Radio Star\u2019, an almost too-perfect choice given what the channel "
            "was about to do to the music industry.\n\n"
            "Overnight, how a song looked became just as important as how it sounded, "
            "reshaping artist budgets, image and even chart performance around the "
            "music video format.\n\n"
            "Acts like Duran Duran and Michael Jackson thrived in this new visual "
            "economy, while others who couldn't adapt to the camera found their "
            "careers stalling almost immediately.\n\n"
            "It's hard to overstate how completely MTV rewired the relationship "
            "between artist, image and audience for the following two decades."
        ),
    },
    {
        "title": "The First Grammy Awards",
        "date": "1st Annual Grammy Awards \u2014 May 4, 1959",
        "search": "Domenico Modugno Nel Blu Dipinto Di Blu",
        "description": (
            "Held quietly at two hotel ceremonies in Los Angeles and New York with no "
            "television broadcast at all, the first Grammy Awards were a modest, "
            "industry-only affair compared to the show they'd later become.\n\n"
            "Domenico Modugno's Italian song \u2018Nel Blu Dipinto Di Blu (Volare)\u2019 "
            "won both Record and Song of the Year, a choice that looks almost "
            "unthinkable by today's Grammy standards.\n\n"
            "The ceremony was created partly in response to rock and roll's rise, as "
            "an attempt by the recording industry to keep honouring more "
            "traditional musicianship and songcraft.\n\n"
            "It would take until 1971 for the show to move to national television, "
            "beginning its transformation into the major broadcast event it is today."
        ),
    },
    {
        "title": "Sgt. Pepper Redefines the Album",
        "date": "The Beatles release 'Sgt. Pepper's Lonely Hearts Club Band' \u2014 June 1, 1967",
        "search": "Sgt Peppers Lonely Hearts Club Band",
        "description": (
            "Recorded over more studio hours than any pop record before it, "
            "\u2018Sgt. Pepper's\u2019 was conceived as a continuous concept album "
            "rather than a simple collection of singles, complete with a fictional "
            "alter-ego band.\n\n"
            "Its lavish, collage-style cover art and printed lyric sheet were nearly "
            "as influential as the music, helping establish the album itself as a "
            "serious artistic statement rather than disposable pop product.\n\n"
            "Critics and rival musicians alike, including Brian Wilson of the Beach "
            "Boys, described feeling both inspired and daunted by how far it pushed "
            "studio production.\n\n"
            "It's widely credited with helping shift the entire industry's focus from "
            "singles-driven pop toward the album as a complete artistic work."
        ),
    },
    {
        "title": "The First Billboard Hot 100",
        "date": "Billboard publishes its first Hot 100 chart \u2014 August 4, 1958",
        "search": "Poor Little Fool Ricky Nelson",
        "description": (
            "Before 1958, Billboard ran three separate, inconsistent singles charts "
            "based on sales, jukebox plays and radio airplay. The Hot 100 combined "
            "them into one definitive weekly ranking, and Ricky Nelson's \u2018Poor "
            "Little Fool\u2019 became its very first number one.\n\n"
            "The unified chart gave the whole industry, for the first time, a single "
            "shared scoreboard to compete over \u2014 turning chart position itself "
            "into something artists, labels and radio stations all began chasing "
            "directly.\n\n"
            "Updated weekly ever since, it remains the most quoted measure of a "
            "song's popularity in America more than sixty years later, adapting "
            "along the way to count streams and downloads alongside sales and "
            "airplay."
        ),
    },
    {
        "title": "Live 8 Circles the Globe",
        "date": "Live 8 concerts held across eight countries \u2014 July 2, 2005",
        "search": "Pink Floyd Comfortably Numb Live 8",
        "description": (
            "Timed deliberately to pressure G8 leaders meeting in Scotland days "
            "later, Live 8 staged free concerts simultaneously across London, "
            "Philadelphia, Paris, Berlin, Rome, Tokyo, Johannesburg and Toronto.\n\n"
            "Unlike 1985's Live Aid, the goal wasn't direct donations but political "
            "pressure \u2014 pushing wealthy nations toward debt relief and increased "
            "aid for the world's poorest countries.\n\n"
            "Pink Floyd reunited with Roger Waters for the first time in over two "
            "decades for the London show, a reunion many fans had assumed would "
            "never happen again.\n\n"
            "It remains one of the largest coordinated multi-city concert events ever "
            "staged, reaching a television audience estimated in the billions."
        ),
    },
    {
        "title": "The iPod Changes How Music Is Carried",
        "date": "Apple releases the first iPod \u2014 October 23, 2001",
        "search": "iPod launch 2001 music",
        "description": (
            "Announced with the tagline \u201c1,000 songs in your pocket\u201d, the "
            "original iPod held a five-gigabyte hard drive at a time when portable "
            "CD and MiniDisc players were still the norm.\n\n"
            "Paired a couple of years later with the iTunes Store, it gave listeners "
            "a simple, legal way to buy individual songs for a dollar each, directly "
            "challenging the album as the default unit of music sales.\n\n"
            "Music piracy through services like Napster had already reset listener "
            "expectations around instant access; the iPod and iTunes gave the "
            "industry a legitimate business model to catch up with those habits.\n\n"
            "Within a few years, physical CD sales began a decline they never "
            "recovered from, a shift that traces directly back to this one device."
        ),
    },
    {
        "title": "Spotify Launches in Sweden",
        "date": "Spotify's public launch \u2014 October 7, 2008",
        "search": "Spotify launch 2008",
        "description": (
            "Founded by Daniel Ek and Martin Lorentzon, Spotify launched first in "
            "Sweden with a free, ad-supported streaming model built specifically to "
            "compete directly with music piracy rather than just other retailers.\n\n"
            "Convincing major record labels to license their catalogues for "
            "unlimited on-demand streaming took years of negotiation, with several "
            "labels reportedly deeply skeptical it could ever work commercially.\n\n"
            "It expanded to the United States in 2011, arriving alongside competitors "
            "but quickly becoming the dominant name most listeners now associate with "
            "streaming itself.\n\n"
            "The shift from owning music to renting access to nearly all of it, "
            "which now feels completely normal, traces back to this single launch."
        ),
    },
    {
        "title": "Rapper's Delight Breaks Hip-Hop Into the Mainstream",
        "date": "The Sugarhill Gang release 'Rapper's Delight' \u2014 September 16, 1979",
        "search": "Rapper's Delight Sugarhill Gang",
        "description": (
            "Built over a looped bassline from Chic's \u2018Good Times\u2019, "
            "\u2018Rapper's Delight\u2019 was the first rap record to become a "
            "genuine mainstream hit, reaching the top 40 in the United States.\n\n"
            "The Sugarhill Gang were assembled specifically to record it and weren't "
            "well-known figures from the Bronx hip-hop scene the style had grown out "
            "of, a point of some controversy among early hip-hop artists at the time.\n\n"
            "At over fourteen minutes in its full version, it was also a radical "
            "departure from typical single-length pop records of the era.\n\n"
            "Whatever the arguments over its authenticity, it's the record that proved "
            "to labels rap could sell records well beyond its original scene."
        ),
    },
    {
        "title": "The Sex Pistols Shock Live Television",
        "date": "Sex Pistols on the Bill Grundy Show \u2014 December 1, 1976",
        "search": "Sex Pistols Anarchy in the UK",
        "description": (
            "Booked as a last-minute replacement guest, the Sex Pistols appeared on "
            "a British teatime talk show and, goaded by host Bill Grundy, responded "
            "with a string of swear words live on air.\n\n"
            "The resulting tabloid uproar, with headlines calling them \u201cthe "
            "filth and the fury\u201d, made the band infamous virtually overnight "
            "across the entire country.\n\n"
            "Grundy was suspended from the network shortly after, while the Sex "
            "Pistols found several tour dates cancelled by venues nervous about the "
            "backlash.\n\n"
            "The controversy did more to launch British punk into the national "
            "conversation than any amount of conventional promotion could have "
            "managed."
        ),
    },
    {
        "title": "Les Paul Invents Multitrack Recording",
        "date": "Les Paul builds the first practical multitrack recorder \u2014 1948",
        "search": "Les Paul Mary Ford How High the Moon",
        "description": (
            "Guitarist and inventor Les Paul modified tape recorders to layer "
            "multiple performances on top of each other, allowing a single "
            "musician to record entire harmony parts and solos with themselves.\n\n"
            "His technique, used on hits like \u2018How High the Moon\u2019 with "
            "wife Mary Ford, laid the technical groundwork for nearly every "
            "multi-layered studio recording made since, from Motown to modern "
            "pop production."
        ),
    },
    {
        "title": "The Grand Ole Opry Is Founded",
        "date": "The Grand Ole Opry radio program begins broadcasting \u2014 November 28, 1925",
        "search": "Grand Ole Opry Nashville",
        "description": (
            "What began as a small barn-dance radio program out of Nashville "
            "grew, over subsequent decades, into country music's most "
            "important institution, launching and cementing the careers of "
            "nearly every major star in the genre.\n\n"
            "Still broadcasting weekly nearly a century later, it remains the "
            "longest-running radio program in United States history."
        ),
    },
    {
        "title": "Sun Studio Records Elvis's First Single",
        "date": "Elvis Presley records 'That's All Right' at Sun Studio \u2014 July 5, 1954",
        "search": "That's All Right Elvis Presley Sun Studio",
        "description": (
            "During a break between takes at a small Memphis studio, Elvis "
            "Presley began fooling around with an up-tempo blues cover, and "
            "producer Sam Phillips, hearing something entirely new through the "
            "control room glass, told him to do it again from the top.\n\n"
            "That recording, blending Black rhythm and blues with white "
            "country music, is widely cited as one of the very first true "
            "rock and roll records ever made."
        ),
    },
    {
        "title": "Dylan Goes Electric at Newport",
        "date": "Bob Dylan plugs in at the Newport Folk Festival \u2014 July 25, 1965",
        "search": "Bob Dylan Maggie's Farm Newport 1965",
        "description": (
            "Taking the stage with a full electric band rather than his usual "
            "solo acoustic set, Bob Dylan was met with a chorus of boos from "
            "folk purists who saw amplified rock as a betrayal of the folk "
            "movement's values.\n\n"
            "Whatever the crowd's reaction that night, the performance is now "
            "seen as the moment folk and rock definitively merged, opening the "
            "door for the singer-songwriter rock era that followed."
        ),
    },
    {
        "title": "Motown Tours Britain",
        "date": "The Motortown Revue tours the UK \u2014 March 1965",
        "search": "Motortown Revue UK tour 1965",
        "description": (
            "A package tour of Motown's biggest stars, including The "
            "Supremes, Stevie Wonder and Martha and the Vandellas, introduced "
            "British audiences directly to the Detroit sound many UK bands "
            "had already been covering.\n\n"
            "It helped cement Motown's international reach just as British "
            "groups influenced by American soul were themselves crossing back "
            "over to the US, in a genuine two-way musical exchange."
        ),
    },
    {
        "title": "American Bandstand Goes National",
        "date": "American Bandstand's first national broadcast \u2014 August 5, 1957",
        "search": "American Bandstand 1957",
        "description": (
            "Already a local Philadelphia show, American Bandstand's move to "
            "national television gave teenagers across the country a shared, "
            "weekday window into new music and dance trends for the first "
            "time.\n\n"
            "Host Dick Clark's clean-cut presentation helped make rock and "
            "roll palatable to a wary adult audience, smoothing its path into "
            "the American mainstream."
        ),
    },
    {
        "title": "The Altamont Free Concert Turns Violent",
        "date": "Altamont Speedway Free Festival \u2014 December 6, 1969",
        "search": "Rolling Stones Altamont 1969",
        "description": (
            "Billed as a West Coast answer to Woodstock, the free Rolling "
            "Stones concert at Altamont Speedway used Hells Angels as informal "
            "security, a decision that ended in violence, including the death "
            "of an audience member during the Stones' set.\n\n"
            "Coming just months after Woodstock's peace-and-love high, "
            "Altamont is often cited by historians as the symbolic end of the "
            "1960s counterculture era."
        ),
    },
    {
        "title": "CBGB Opens Its Doors",
        "date": "CBGB opens in New York City \u2014 December 1973",
        "search": "CBGB New York punk club",
        "description": (
            "Founded as a country, bluegrass and blues bar, CBGB instead became "
            "the birthplace of American punk and new wave almost by accident, "
            "hosting early residencies by Television, Patti Smith, Blondie and "
            "the Ramones.\n\n"
            "Its small, unglamorous stage and famously filthy bathroom became "
            "part of punk's founding mythology, a far cry from the polished "
            "arena rock it was reacting against."
        ),
    },
    {
        "title": "DJ Kool Herc's Back-to-School Jam",
        "date": "Widely cited birth of hip-hop, the Bronx \u2014 August 11, 1973",
        "search": "DJ Kool Herc hip hop birth",
        "description": (
            "At a back-to-school party in a Bronx apartment building rec room, "
            "DJ Kool Herc extended the instrumental breakdown section of "
            "funk records using two copies of the same record, giving "
            "dancers a longer break to perform to.\n\n"
            "That simple technique, isolating and looping the \"break\", is now "
            "widely credited as the founding technical moment of hip-hop as a "
            "genre and culture."
        ),
    },
    {
        "title": "The Fillmore East Opens",
        "date": "The Fillmore East opens in New York City \u2014 March 8, 1968",
        "search": "Fillmore East New York venue",
        "description": (
            "Promoter Bill Graham's East Coast venue became one of rock's most "
            "important stages, hosting landmark live performances and "
            "recordings by acts including The Allman Brothers Band, The Who "
            "and Jimi Hendrix.\n\n"
            "Its relatively short life, closing in 1971, only added to its "
            "legendary status among musicians and fans who saw shows there "
            "during its brief but hugely influential run."
        ),
    },
    {
        "title": "Switched-On Bach Popularises the Synthesizer",
        "date": "Wendy Carlos releases 'Switched-On Bach' \u2014 October 1968",
        "search": "Switched-On Bach Wendy Carlos",
        "description": (
            "Wendy Carlos painstakingly recorded Bach compositions entirely "
            "on a Moog synthesizer, an instrument still considered a "
            "laboratory curiosity at the time, note by note using primitive "
            "monophonic technology.\n\n"
            "The album became an unexpected commercial and critical hit, "
            "convincing a generation of musicians that electronic synthesizers "
            "belonged in serious, mainstream music rather than novelty records."
        ),
    },
    {
        "title": "The First Glastonbury Festival",
        "date": "The first Glastonbury Festival is held \u2014 September 19, 1970",
        "search": "Glastonbury Festival 1970",
        "description": (
            "Held the day after Jimi Hendrix's death and inspired partly by "
            "the free festival movement, the first Glastonbury drew around "
            "1,500 people who were given free milk from the farm's own cows "
            "as part of the ticket price.\n\n"
            "It has since grown into one of the largest and most famous music "
            "festivals in the world, still held on the very same Somerset "
            "farmland over half a century later."
        ),
    },
    {
        "title": "Elvis Presley Dies",
        "date": "Elvis Presley dies at Graceland \u2014 August 16, 1977",
        "search": "Elvis Presley Graceland",
        "description": (
            "News of Elvis Presley's death at his Graceland home spread fast "
            "enough to draw an estimated 80,000 mourners to the mansion within "
            "days, an outpouring of grief on a scale rarely seen for a "
            "musician before.\n\n"
            "His death is often cited as a turning point that pushed his "
            "catalogue and legend into an entirely new, even larger cultural "
            "orbit than he occupied during his own lifetime."
        ),
    },
    {
        "title": "John Lennon Is Killed",
        "date": "John Lennon is shot outside the Dakota building, New York \u2014 December 8, 1980",
        "search": "John Lennon Imagine",
        "description": (
            "John Lennon was shot by a man he had signed an autograph for just "
            "hours earlier, outside the New York apartment building where he "
            "lived, in one of music's most shocking and senseless losses.\n\n"
            "Radio stations around the world interrupted programming to break "
            "the news, and vigils were held from Central Park to Liverpool, "
            "underscoring just how far his cultural reach extended."
        ),
    },
    {
        "title": "MTV's First VMAs and Madonna's Breakthrough",
        "date": "The first MTV Video Music Awards \u2014 September 14, 1984",
        "search": "Madonna Like a Virgin VMA 1984",
        "description": (
            "Madonna's rolling-on-the-floor performance of \u2018Like a "
            "Virgin\u2019 at the very first VMAs, complete with a wedding dress "
            "and a wardrobe mishap she recovered from mid-song, instantly "
            "became one of the ceremony's most talked-about moments.\n\n"
            "The award show itself quickly became an annual showcase for "
            "career-defining, deliberately provocative live performances that "
            "MTV built much of its identity around."
        ),
    },
    {
        "title": "Farm Aid's First Concert",
        "date": "The first Farm Aid concert, Champaign, Illinois \u2014 September 22, 1985",
        "search": "Farm Aid 1985 Willie Nelson",
        "description": (
            "Organised by Willie Nelson after a comment from Bob Dylan at that "
            "year's Live Aid about struggling American farmers, Farm Aid "
            "brought together country, rock and pop artists for a single "
            "cause few benefit concerts had addressed before.\n\n"
            "It has continued annually for decades since, becoming one of the "
            "longest-running benefit concert series in music history."
        ),
    },
    {
        "title": "Licensed to Ill Tops the Charts",
        "date": "The Beastie Boys' 'Licensed to Ill' hits number one \u2014 1987",
        "search": "Licensed to Ill Beastie Boys",
        "description": (
            "The Beastie Boys' debut became the first rap album ever to reach "
            "number one on the Billboard 200, a genuine milestone for a genre "
            "still widely dismissed by much of the mainstream music industry.\n\n"
            "Its enormous commercial success, helped along by MTV rotation, "
            "proved hip-hop could sell albums at the same scale as rock and "
            "pop, reshaping how labels invested in the genre afterward."
        ),
    },
    {
        "title": "Straight Outta Compton Redefines Rap",
        "date": "N.W.A release 'Straight Outta Compton' \u2014 August 8, 1988",
        "search": "Straight Outta Compton NWA",
        "description": (
            "N.W.A's blunt, confrontational accounts of life under police "
            "harassment in South Central Los Angeles brought gangsta rap into "
            "the mainstream, drawing both massive sales and an FBI warning "
            "letter over the track \u2018F*** tha Police\u2019.\n\n"
            "It reshaped the entire commercial landscape of hip-hop, proving "
            "unapologetically political and regional street narratives could "
            "sell on a national scale."
        ),
    },
    {
        "title": "The First Lollapalooza Tour",
        "date": "The first Lollapalooza tour begins \u2014 July 18, 1991",
        "search": "Lollapalooza 1991 Jane's Addiction",
        "description": (
            "Conceived by Jane's Addiction's Perry Farrell as a farewell tour "
            "for his own band, Lollapalooza instead became a genre-blending "
            "touring festival mixing alternative rock, hip-hop and industrial "
            "acts on one bill, unusual for the era.\n\n"
            "It helped bring alternative and underground music into the "
            "mainstream just as grunge was about to break wide open the "
            "following year."
        ),
    },
    {
        "title": "Kurt Cobain Dies",
        "date": "Kurt Cobain's death is discovered \u2014 April 8, 1994",
        "search": "Nirvana Smells Like Teen Spirit",
        "description": (
            "Kurt Cobain's death sent shockwaves through a grunge scene that "
            "had, only a couple of years earlier, unexpectedly dethroned "
            "mainstream pop and hair metal at the top of the charts with "
            "Nirvana's \u2018Nevermind\u2019.\n\n"
            "Vigils were held across the world, and his death is often "
            "described as marking the symbolic end of grunge's commercial "
            "dominance, even as the genre's influence continued for years."
        ),
    },
    {
        "title": "Selena's Death Shakes Latin Music",
        "date": "Selena Quintanilla is killed \u2014 March 31, 1995",
        "search": "Selena Quintanilla Dreaming of You",
        "description": (
            "Already a major star in Tejano and Latin music, Selena was shot "
            "and killed by the president of her own fan club just as she was "
            "preparing to cross over into the English-language mainstream.\n\n"
            "Her posthumously released English album debuted at number one, "
            "and her death remains one of the most significant losses in the "
            "history of Latin American music."
        ),
    },
    {
        "title": "Tupac Shakur Is Killed",
        "date": "Tupac Shakur dies after a Las Vegas shooting \u2014 September 13, 1996",
        "search": "Tupac Shakur All Eyez on Me",
        "description": (
            "Shot days earlier following a Mike Tyson fight in Las Vegas, "
            "Tupac Shakur's death came at the peak of a bitter East Coast-West "
            "Coast rap rivalry, intensifying tensions across the industry.\n\n"
            "His posthumous releases went on to sell tens of millions of "
            "copies, and he remains one of the most influential and "
            "extensively studied figures in hip-hop history."
        ),
    },
    {
        "title": "Believe Popularises Auto-Tune",
        "date": "Cher releases 'Believe' \u2014 October 1998",
        "search": "Believe Cher Auto-Tune",
        "description": (
            "Producers on Cher's \u2018Believe\u2019 used pitch-correction "
            "software in a deliberately extreme, obvious way rather than "
            "hiding it, creating the robotic vocal warble that became known "
            "as the \"Cher effect\".\n\n"
            "What started as a distinctive one-off production trick became, "
            "within a decade, one of the most widely used vocal tools in "
            "mainstream pop and hip-hop production."
        ),
    },
    {
        "title": "The First Coachella Festival",
        "date": "The first Coachella Valley Music and Arts Festival \u2014 October 9\u201310, 1999",
        "search": "Coachella 1999 first festival",
        "description": (
            "Held on a polo field in the California desert with headliners "
            "including Beck and Rage Against the Machine, the first Coachella "
            "actually lost money and nearly ended the festival before it had "
            "properly begun.\n\n"
            "Organisers persisted, and it eventually grew into one of the "
            "most influential and widely imitated festival brands in the "
            "world."
        ),
    },
    {
        "title": "Woodstock '99 Turns Chaotic",
        "date": "Woodstock '99, Rome, New York \u2014 July 1999",
        "search": "Woodstock 99",
        "description": (
            "Staged on a disused air base with inadequate water, sanitation "
            "and security, the 1999 revival of Woodstock's name ended in "
            "fires, vandalism and violence during Red Hot Chili Peppers' "
            "closing set.\n\n"
            "It became a widely cited cautionary case study in festival "
            "planning, and a stark contrast to the peace-and-love reputation "
            "the original Woodstock name still carried."
        ),
    },
    {
        "title": "The First Commercial CD Single",
        "date": "Billy Joel's '52nd Street' becomes the first commercially released CD \u2014 1982",
        "search": "Billy Joel 52nd Street CD",
        "description": (
            "Released alongside the first Sony CD players in Japan, Billy "
            "Joel's \u2018 52nd Street\u2019 became the very first album "
            "commercially available on compact disc, a format initially seen "
            "as a luxury niche product.\n\n"
            "Within little more than a decade, the CD had overtaken vinyl and "
            "cassette entirely to become the industry's dominant physical "
            "format for the following twenty years."
        ),
    },
    {
        "title": "The iTunes Store Launches",
        "date": "Apple launches the iTunes Music Store \u2014 April 28, 2003",
        "search": "iTunes Music Store 2003",
        "description": (
            "Offering songs for 99 cents each with major label backing, the "
            "iTunes Store gave the industry its first legitimate, "
            "widely-adopted answer to the piracy that services like Napster "
            "had unleashed a few years earlier.\n\n"
            "It sold its first million songs within under a week, and helped "
            "cement the single, rather than the album, as the primary unit of "
            "digital music purchasing for the decade that followed."
        ),
    },
    {
        "title": "Billboard Launches Its First R&B Chart",
        "date": "Billboard's first Race Records/R&B chart \u2014 1949",
        "search": "Billboard R&B chart history",
        "description": (
            "Renamed from the openly offensive \"Race Records\" chart it had "
            "run since the 1940s, Billboard's Rhythm & Blues chart gave Black "
            "artists a dedicated, tracked measure of commercial success "
            "separate from the pop charts of the era.\n\n"
            "The renaming itself reflected a broader, slow shift in how the "
            "recording industry publicly categorised and marketed Black "
            "musicians' work."
        ),
    },
    {
        "title": "The Monkees Are Assembled for Television",
        "date": "The Monkees debut on NBC \u2014 September 12, 1966",
        "search": "The Monkees I'm a Believer",
        "description": (
            "Created specifically for a television show rather than forming "
            "organically, The Monkees were cast through open auditions as an "
            "American answer to Beatlemania, initially playing music written "
            "and performed largely by session musicians.\n\n"
            "The band later fought for and won creative control over their own "
            "recordings, becoming a genuinely significant early example of a "
            "manufactured act pushing back against its own machine."
        ),
    },
    {
        "title": "The First Billboard 200 Albums Chart",
        "date": "Billboard's first weekly albums chart is published \u2014 March 24, 1956",
        "search": "Billboard 200 first albums chart",
        "description": (
            "Before 1956, Billboard tracked singles far more closely than "
            "full albums, but the introduction of a dedicated weekly albums "
            "chart reflected records increasingly being sold, and judged, as "
            "complete artistic works.\n\n"
            "Still published weekly today as the Billboard 200, it remains "
            "the industry's primary measure of an album's commercial "
            "performance in America."
        ),
    },
]

def _pick_daily_entry(entries):
    """Deterministically picks today's entry from a list, based on the date,
    so it stays the same all day and moves on to the next one tomorrow."""
    idx = datetime.date.today().toordinal() % len(entries)
    return idx, entries[idx]

sotd_shown_day_idx = None   # which SOTD_ENTRIES index is currently loaded/cached
aotd_shown_day_idx = None
hm_shown_day_idx   = None

show_top100_page = False
top100_tracks        = []        # list of dicts: rank, title, artist, spotify_url, youtube_url, apple_url
top100_loading       = False
top100_error         = ""
top100_last_fetched  = 0.0       # epoch time of last successful fetch
top100_scroll_offset = 0.0
target_top100_scroll = 0.0
max_top100_scroll    = 0
top100_link_rects    = []        # list of (rect, url) for link buttons
top100_thread        = None
top100_art_cache     = {}        # { rank(int): pygame.Surface or None }
show_song_of_day_page = False
sotd_cover_surface   = None      # pygame.Surface once downloaded
sotd_cover_loading   = False
sotd_link_rects      = []        # [(rect, url), ...]
sotd_scroll_offset   = 0.0
target_sotd_scroll   = 0.0
max_sotd_scroll      = 0
show_artist_of_day_page = False
aotd_cover_surface   = None      # pygame.Surface once downloaded
aotd_cover_loading   = False
aotd_link_rects      = []        # [(rect, url), ...]
aotd_scroll_offset   = 0.0
target_aotd_scroll   = 0.0
max_aotd_scroll      = 0
show_history_maker_page = False
hm_cover_surface     = None      # pygame.Surface once downloaded
hm_cover_loading     = False
hm_link_rects        = []        # [(rect, url), ...]
hm_scroll_offset     = 0.0
target_hm_scroll     = 0.0
max_hm_scroll        = 0
subpage_back_rect = pygame.Rect(0, 0, 0, 0)
top100_btn_rect = pygame.Rect(0, 0, 0, 0)
song_of_day_btn_rect = pygame.Rect(0, 0, 0, 0)
artist_of_day_btn_rect = pygame.Rect(0, 0, 0, 0)
history_maker_btn_rect = pygame.Rect(0, 0, 0, 0)
btn_row_scroll_offset = 0.0
target_btn_row_scroll = 0.0
max_btn_row_scroll = 0
btn_row_rect = pygame.Rect(0, 0, 0, 0)
user_scrolled_btn_row = False
playlist_is_playing = None  
layout_mode = "desktop"  
_last_gc_time = 0.0

is_dragging_grid = False
is_dragging_row = False
last_touch_y = 0
last_touch_x = 0
total_drag_dy = 0
press_origin_pos = (0, 0)  # touch/click position at press-down, used to measure NET
                            # displacement for the tap-vs-drag decision (see MOUSEMOTION below)
_scroll_velocity_samples = []   # [(time, dy), ...] rolling window for momentum on lift

# --- REAL INERTIAL SCROLL PHYSICS ---
# The old approach kept a single "target" position and eased the visible
# offset toward it every frame with offset += (target-offset)*12*dt. That's
# fine for programmatic jumps (tapping a tab), but for a flick-to-scroll it's
# the wrong model: on release we computed one average velocity and used it to
# pick a *new target position*, then chased that target with the same generic
# ease. That chase curve doesn't match how a flung list actually decelerates
# (constant, framerate-independent friction), so every flick "arrived" with a
# slightly different, faintly laggy feel instead of smoothly bleeding off
# speed like Spotify/iOS lists do. Below, released flicks get a real velocity
# that decays continuously each frame (framerate-independent via dt), plus a
# touch of rubber-band resistance at the scroll bounds instead of a hard
# stop. Non-flick scroll changes (tab switches, wheel nudges, buttons) still
# use a snappy ease so they don't feel physics-y when they shouldn't.
_scroll_momentum = {}      # name -> current velocity in px/sec, while a flick is decelerating
SCROLL_FRICTION = 3.4       # higher = flicks stop sooner. velocity *= e^(-SCROLL_FRICTION*dt)
SCROLL_MIN_VELOCITY = 40.0  # px/sec floor - below this we just snap to 0 instead of creeping forever
SCROLL_MAX_FLICK_VELOCITY = 4500.0  # px/sec cap so a wild flick can't launch the list off screen
SCROLL_EASE_RATE = 16.0     # 1/sec rate for the non-momentum "chase the target" ease
# (area_name, target_var_name, offset_var_name, max_var_name_or_None)
SCROLL_AREAS = [
    ("music",         "target_music_scroll",         "music_grid_scroll_offset",     "max_music_scroll"),
    ("browser",        "target_browser_scroll",        "browser_scroll_offset",        "max_browser_scroll"),
    ("settings",        "target_settings_scroll",       "settings_scroll_offset",       "max_settings_scroll"),
    ("lyrics",          "target_lyrics_scroll",         "lyrics_scroll_offset",         "max_lyrics_scroll"),
    ("top100",          "target_top100_scroll",         "top100_scroll_offset",         "max_top100_scroll"),
    ("theme_page",      "target_theme_page_scroll",     "theme_page_scroll_offset",     "max_theme_page_scroll"),
    ("sotd",            "target_sotd_scroll",           "sotd_scroll_offset",           "max_sotd_scroll"),
    ("aotd",            "target_aotd_scroll",           "aotd_scroll_offset",           "max_aotd_scroll"),
    ("hm",              "target_hm_scroll",             "hm_scroll_offset",             "max_hm_scroll"),
    ("art_search",      "target_art_search_scroll",     "art_search_scroll_offset",     "max_art_search_scroll"),
    ("lyrics_search",   "target_lyrics_search_scroll",  "lyrics_search_scroll_offset",  "max_lyrics_search_scroll"),
    ("btn_row",         "target_btn_row_scroll",        "btn_row_scroll_offset",        None),
]

def _update_scroll_physics(dt):
    """Called once per frame. Areas with an active flick (_scroll_momentum[name]
    != 0) get real velocity/friction physics; everything else gets the old
    snappy ease-toward-target so tab switches etc. still feel immediate."""
    g = globals()
    for name, target_var, offset_var, max_var in SCROLL_AREAS:
        vel = _scroll_momentum.get(name, 0.0)
        if vel == 0.0:
            g[offset_var] += (g[target_var] - g[offset_var]) * (SCROLL_EASE_RATE * dt)
            continue

        offset = g[offset_var] + vel * dt
        vel *= math.exp(-SCROLL_FRICTION * dt)
        if abs(vel) < SCROLL_MIN_VELOCITY:
            vel = 0.0

        max_val = g.get(max_var) if max_var else None
        if max_val is not None:
            max_val = float(max_val)
            if offset < 0.0:
                offset *= 0.55          # rubber-band resistance past the top
                vel *= 0.6
            elif offset > max_val:
                overshoot = offset - max_val
                offset = max_val + overshoot * 0.55
                vel *= 0.6
            if vel == 0.0:
                offset = max(0.0, min(max_val, offset))  # bounce settled - snap firmly in bounds

        g[offset_var] = offset
        g[target_var] = offset
        _scroll_momentum[name] = vel

music_grid_scroll_offset = 0.0  
target_music_scroll = 0.0
browser_scroll_offset = 0       
target_browser_scroll = 0.0     
settings_scroll_offset = 0
target_settings_scroll = 0.0
lyrics_scroll_offset = 0.0
target_lyrics_scroll = 0.0
max_music_scroll = 0
max_browser_scroll = 0
max_settings_scroll = 0
max_lyrics_scroll = 0

ROOT_PATH = "/storage/emulated/0" if os.path.exists("/storage/emulated/0") else "/sdcard"
current_browser_path = ROOT_PATH
browser_items = []  

search_message = "Tap '+ Add Folder' to open the built-in storage browser."

track_rects = []
sidebar_rects = []
browser_rects = []
settings_dir_rects = []
custom_playlist_rects = []
modal_playlist_rects = []

playlist_cover_rect = pygame.Rect(0, 0, 0, 0)
liked_songs_card_rect = pygame.Rect(260, 95, 160, 200)
search_box_rect = pygame.Rect(260, 80, 500, 40)
play_btn_rect = pygame.Rect(0, 0, 0, 0)
prev_btn_rect = pygame.Rect(0, 0, 0, 0)
next_btn_rect = pygame.Rect(0, 0, 0, 0)
minus_10_btn_rect = pygame.Rect(0, 0, 0, 0)
plus_10_btn_rect = pygame.Rect(0, 0, 0, 0)
shuffle_btn_rect = pygame.Rect(0, 0, 0, 0)
mediabar_add_btn_rect = pygame.Rect(0, 0, 0, 0)
mediabar_lyrics_btn_rect = pygame.Rect(0, 0, 0, 0)
mediabar_cover_btn_rect = pygame.Rect(0, 0, 0, 0)
star_btn_rect = pygame.Rect(0, 0, 0, 0)
playlist_play_btn_rect = pygame.Rect(0, 0, 0, 0)
playlist_random_btn_rect = pygame.Rect(0, 0, 0, 0) 
add_folder_btn_rect = pygame.Rect(0, 0, 0, 0)
settings_btn_rect = pygame.Rect(0, 0, 0, 0)
create_playlist_btn_rect = pygame.Rect(390, 35, 40, 40)
select_folder_btn_rect = pygame.Rect(0, 0, 0, 0)
browser_extra_search_btn_rect = pygame.Rect(0, 0, 0, 0)

show_art_search_modal    = False
show_art_manual_modal    = False
art_search_loading       = False
art_search_results       = []
art_search_error         = ""
art_search_thread        = None
art_search_close_rect    = pygame.Rect(0, 0, 0, 0)
art_manual_rect          = pygame.Rect(0, 0, 0, 0)
art_manual_title_rect    = pygame.Rect(0, 0, 0, 0)
art_manual_artist_rect   = pygame.Rect(0, 0, 0, 0)
art_manual_go_rect       = pygame.Rect(0, 0, 0, 0)
art_search_item_rects    = []
art_search_scroll_offset = 0.0
target_art_search_scroll = 0.0
max_art_search_scroll    = 0
art_apply_thread         = None
art_apply_pending        = False   # True while the chosen artwork is downloading in the background
art_apply_result_path    = None    # set by the worker thread when the download finishes ("" on failure)
art_apply_track_path     = None    # which track the in-flight download belongs to
art_search_thumb_surfaces = {}     # artworkUrl60 -> small pygame.Surface, filled in as thumbnails download
art_search_thumb_failed   = set()  # urls that failed to download, so we stop retrying them
art_search_thumb_gen      = 0      # bumped each new search so stale background downloads don't overwrite a newer search's thumbs
cancel_browser_btn_rect = pygame.Rect(0, 0, 0, 0)
close_settings_btn_rect = pygame.Rect(0, 0, 0, 0)
grid_toggle_btn_rect = pygame.Rect(0, 0, 0, 0)
grid_cols_override = None   # None = default column count; otherwise the user-chosen override
progress_bar_rect = pygame.Rect(0, 0, 0, 0)
media_bar_rect = pygame.Rect(0, 0, 0, 0)
desktop_btn_rect = pygame.Rect(0, 0, 0, 0)
phone_btn_rect = pygame.Rect(0, 0, 0, 0)
theme_btn_rect = pygame.Rect(0, 0, 0, 0)
language_btn_rect = pygame.Rect(0, 0, 0, 0)
resolution_btn_rect = pygame.Rect(0, 0, 0, 0)
font_size_btn_rect = pygame.Rect(0, 0, 0, 0)
haptics_btn_rect = pygame.Rect(0, 0, 0, 0)

# --- PERSONALIZE / THEME SYSTEM ---
current_theme = "classic"
show_theme_page = False
theme_option_rects = []   # [(pygame.Rect, theme_key), ...]
theme_page_scroll_offset = 0.0
target_theme_page_scroll = 0.0
max_theme_page_scroll = 0

# --- FONT SYSTEM (Personalize page also lets you pick the app-wide font) ---
current_font_family = "classic"
font_option_rects = []   # [(pygame.Rect, font_key), ...]
FONTS = {
    "classic":   {"label": "Classic",   "family": "Arial"},
}

# Settings > Font Size button: cycles Small/Medium/Large by scaling the base
# point sizes used in apply_font() above.
font_scale = 1.0
FONT_SCALE_STEPS = [("Small", 0.85), ("Medium", 1.0), ("Large", 1.2)]
def cycle_font_size():
    global font_scale
    labels = [lbl for lbl, _ in FONT_SCALE_STEPS]
    scales = [sc for _, sc in FONT_SCALE_STEPS]
    try:
        idx = scales.index(font_scale)
    except ValueError:
        idx = 1  # default to Medium if font_scale was ever an odd value
    idx = (idx + 1) % len(FONT_SCALE_STEPS)
    font_scale = scales[idx]
    apply_font(current_font_family)

def current_font_size_label():
    for lbl, sc in FONT_SCALE_STEPS:
        if sc == font_scale:
            return lbl
    return "Medium"

# Cache for the small preview-only font objects used on the Personalize page,
# so scrolling doesn't rebuild ~16 SysFont objects every single frame.
_font_preview_cache = {}
def get_preview_font(family, size, bold=False):
    key = (family, size, bold)
    cached = _font_preview_cache.get(key)
    if cached is None:
        cached = pygame.font.SysFont(family, size, bold=bold)
        _font_preview_cache[key] = cached
    return cached

def apply_font(font_key):
    """Rebuild every global font object with a new family, restyling all text
    drawn throughout the app since every draw function reads these globals."""
    global current_font_family, font_title, font_body, font_small, font_huge
    font = FONTS.get(font_key, FONTS["classic"])
    family = font["family"]
    current_font_family = font_key
    font_title = pygame.font.SysFont(family, round(22 * font_scale), bold=True)
    font_body  = pygame.font.SysFont(family, round(16 * font_scale), bold=True)
    font_small = pygame.font.SysFont(family, round(14 * font_scale))
    font_huge  = pygame.font.SysFont(family, round(50 * font_scale), bold=True)

# --- LANGUAGE SYSTEM (Settings tab) ---
current_language = "English"
show_language_page = False
language_option_rects = []   # [(pygame.Rect, language_name), ...]
LANGUAGES = ["English", "Spanish", "French", "German", "Italian", "Portuguese", "Polish"]

# Translations for the app's core UI chrome — nav, settings, and the
# Personalize/Language pages themselves. Keyed by the original English
# string; t() falls back to that English string for anything not listed,
# so the app never shows a blank label for an untranslated string.
TRANSLATIONS = {
    "Spanish": {
        "Search": "Buscar", "Your Library": "Tu Biblioteca", "Settings": "Configuración",
        "ALBUM": "ÁLBUM", "Cancel": "Cancelar", "Delete [x]": "Eliminar [x]", "Delete and Clear Music  [x] ": "Eliminar y Borrar Música  [x] ", "Refresh": "Actualizar", "+ Add Folder": "+ Añadir Carpeta", "Close": "Cerrar", "Manual": "Manual", "Artist": "Artista", "Save": "Guardar", "Clear": "Borrar", "Import": "Importar", "Name": "Nombre", "Description": "Descripción", "Go to 'Your Library' and tap '+' to create one.": "Ve a 'Tu Biblioteca' y toca '+' para crear una.", "Tap '+ Add Folder' to open the built-in storage browser.": "Toca '+ Añadir Carpeta' para abrir el explorador de almacenamiento.", "No local music loaded. Tap '+ Add Folder' above to explore your storage!": "No hay música local cargada. ¡Toca '+ Añadir Carpeta' arriba para explorar tu almacenamiento!", "Access Denied: Restricted system folder or permission missing.": "Acceso Denegado: Carpeta de sistema restringida o falta de permiso.",
        "Desktop/Tablet": "Escritorio/Tableta", "Phone": "Teléfono", "Personalize": "Personalizar",
        "Language": "Idioma", "Back": "Atrás", "Active": "Activo", "Tap to apply": "Toca para aplicar",
        "Color Themes": "Temas de Color", "App Font": "Fuente de la App", "Grid": "Cuadrícula",
        "Liked Songs": "Canciones Favoritas",
        "Pick a color theme, then a font, for the whole app": "Elige un tema de color y luego una fuente para toda la app",
        "Changes the font used everywhere in the app": "Cambia la fuente usada en toda la app",
        "Choose your preferred language": "Elige tu idioma preferido",
        "Add an optional description": "Añade una descripción opcional",
        "Add to Playlist": "Añadir a Lista",
        "Artist of the Day": "Artista del Día",
        "CUSTOM PLAYLIST": "LISTA PERSONALIZADA",
        "PUBLIC PLAYLIST": "LISTA PÚBLICA",
        "Choose Cover Image": "Elegir Imagen de Portada",
        "Create playlist": "Crear lista",
        "Edit Song Lyrics": "Editar Letra de la Canción",
        "History Maker": "Hito Histórico",
        "Imported Music Directories": "Carpetas de Música Importadas",
        "Loading art...": "Cargando portada...",
        "Loading chart data...": "Cargando datos del ranking...",
        "My Playlist #1": "Mi Lista #1",
        "No custom playlists built yet.": "Aún no has creado ninguna lista personalizada.",
        "Search Album Art  •  iTunes": "Buscar Portada  •  iTunes",
        "Search Results": "Resultados de Búsqueda",
        "Search Synced Lyrics": "Buscar Letra Sincronizada",
        "Searching iTunes...": "Buscando en iTunes...",
        "Searching...": "Buscando...",
        "Song name": "Nombre de la canción",
        "Song of the Day": "Canción del Día",
        "Top 100": "Top 100",
        "e.g. Blinding Lights": "ej. Blinding Lights",
        "e.g. The Weeknd": "ej. The Weeknd",
        "Song of Day": "Canción del Día",
        "Artist of Day": "Artista del Día",
        "History": "Histórico",
    },
    "French": {
        "Search": "Rechercher", "Your Library": "Ta Bibliothèque", "Settings": "Paramètres",
        "ALBUM": "ALBUM", "Cancel": "Annuler", "Delete [x]": "Supprimer [x]", "Delete and Clear Music  [x] ": "Supprimer et Vider la Musique  [x] ", "Refresh": "Actualiser", "+ Add Folder": "+ Ajouter un Dossier", "Close": "Fermer", "Manual": "Manuel", "Artist": "Artiste", "Save": "Enregistrer", "Clear": "Effacer", "Import": "Importer", "Name": "Nom", "Description": "Description", "Go to 'Your Library' and tap '+' to create one.": "Va dans 'Ta Bibliothèque' et touche '+' pour en créer une.", "Tap '+ Add Folder' to open the built-in storage browser.": "Touche '+ Ajouter un Dossier' pour ouvrir l'explorateur de stockage.", "No local music loaded. Tap '+ Add Folder' above to explore your storage!": "Aucune musique locale chargée. Touche '+ Ajouter un Dossier' ci-dessus pour explorer ton stockage !", "Access Denied: Restricted system folder or permission missing.": "Accès Refusé : dossier système restreint ou permission manquante.",
        "Desktop/Tablet": "Bureau/Tablette", "Phone": "Téléphone", "Personalize": "Personnaliser",
        "Language": "Langue", "Back": "Retour", "Active": "Actif", "Tap to apply": "Toucher pour appliquer",
        "Color Themes": "Thèmes de Couleur", "App Font": "Police de l'App", "Grid": "Grille",
        "Liked Songs": "Titres Aimés",
        "Pick a color theme, then a font, for the whole app": "Choisis un thème de couleur, puis une police, pour toute l'app",
        "Changes the font used everywhere in the app": "Change la police utilisée partout dans l'app",
        "Choose your preferred language": "Choisis ta langue préférée",
        "Add an optional description": "Ajoute une description facultative",
        "Add to Playlist": "Ajouter à la Playlist",
        "Artist of the Day": "Artiste du Jour",
        "CUSTOM PLAYLIST": "PLAYLIST PERSONNALISÉE",
        "PUBLIC PLAYLIST": "PLAYLIST PUBLIQUE",
        "Choose Cover Image": "Choisir une Image de Couverture",
        "Create playlist": "Créer une playlist",
        "Edit Song Lyrics": "Modifier les Paroles",
        "History Maker": "Fait Marquant",
        "Imported Music Directories": "Dossiers de Musique Importés",
        "Loading art...": "Chargement de la pochette...",
        "Loading chart data...": "Chargement du classement...",
        "My Playlist #1": "Ma Playlist #1",
        "No custom playlists built yet.": "Aucune playlist personnalisée pour l'instant.",
        "Search Album Art  •  iTunes": "Rechercher une Pochette  •  iTunes",
        "Search Results": "Résultats de Recherche",
        "Search Synced Lyrics": "Rechercher des Paroles Synchronisées",
        "Searching iTunes...": "Recherche sur iTunes...",
        "Searching...": "Recherche...",
        "Song name": "Titre de la chanson",
        "Song of the Day": "Chanson du Jour",
        "Top 100": "Top 100",
        "e.g. Blinding Lights": "p. ex. Blinding Lights",
        "e.g. The Weeknd": "p. ex. The Weeknd",
        "Song of Day": "Chanson du Jour",
        "Artist of Day": "Artiste du Jour",
        "History": "Historique",
    },
    "German": {
        "Search": "Suchen", "Your Library": "Deine Bibliothek", "Settings": "Einstellungen",
        "ALBUM": "ALBUM", "Cancel": "Abbrechen", "Delete [x]": "Löschen [x]", "Delete and Clear Music  [x] ": "Löschen und Musik Leeren  [x] ", "Refresh": "Aktualisieren", "+ Add Folder": "+ Ordner hinzufügen", "Close": "Schließen", "Manual": "Manuell", "Artist": "Künstler", "Save": "Speichern", "Clear": "Leeren", "Import": "Importieren", "Name": "Name", "Description": "Beschreibung", "Go to 'Your Library' and tap '+' to create one.": "Gehe zu 'Deine Bibliothek' und tippe auf '+', um eine zu erstellen.", "Tap '+ Add Folder' to open the built-in storage browser.": "Tippe auf '+ Ordner hinzufügen', um den Speicher-Browser zu öffnen.", "No local music loaded. Tap '+ Add Folder' above to explore your storage!": "Keine lokale Musik geladen. Tippe oben auf '+ Ordner hinzufügen', um deinen Speicher zu durchsuchen!", "Access Denied: Restricted system folder or permission missing.": "Zugriff Verweigert: Eingeschränkter Systemordner oder fehlende Berechtigung.",
        "Desktop/Tablet": "Desktop/Tablet", "Phone": "Telefon", "Personalize": "Anpassen",
        "Language": "Sprache", "Back": "Zurück", "Active": "Aktiv", "Tap to apply": "Tippen zum Anwenden",
        "Color Themes": "Farbthemen", "App Font": "App-Schriftart", "Grid": "Raster",
        "Liked Songs": "Lieblingssongs",
        "Pick a color theme, then a font, for the whole app": "Wähle ein Farbthema und dann eine Schriftart für die ganze App",
        "Changes the font used everywhere in the app": "Ändert die überall in der App verwendete Schriftart",
        "Choose your preferred language": "Wähle deine bevorzugte Sprache",
        "Add an optional description": "Optionale Beschreibung hinzufügen",
        "Add to Playlist": "Zur Playlist hinzufügen",
        "Artist of the Day": "Künstler des Tages",
        "CUSTOM PLAYLIST": "EIGENE PLAYLIST",
        "PUBLIC PLAYLIST": "ÖFFENTLICHE PLAYLIST",
        "Choose Cover Image": "Cover-Bild wählen",
        "Create playlist": "Playlist erstellen",
        "Edit Song Lyrics": "Songtext bearbeiten",
        "History Maker": "Geschichtsmoment",
        "Imported Music Directories": "Importierte Musikordner",
        "Loading art...": "Cover wird geladen...",
        "Loading chart data...": "Chart-Daten werden geladen...",
        "My Playlist #1": "Meine Playlist #1",
        "No custom playlists built yet.": "Noch keine eigenen Playlists erstellt.",
        "Search Album Art  •  iTunes": "Cover suchen  •  iTunes",
        "Search Results": "Suchergebnisse",
        "Search Synced Lyrics": "Synchronisierte Lyrics suchen",
        "Searching iTunes...": "Suche bei iTunes...",
        "Searching...": "Suche...",
        "Song name": "Songname",
        "Song of the Day": "Song des Tages",
        "Top 100": "Top 100",
        "e.g. Blinding Lights": "z. B. Blinding Lights",
        "e.g. The Weeknd": "z. B. The Weeknd",
        "Song of Day": "Song des Tages",
        "Artist of Day": "Künstler des Tages",
        "History": "Verlauf",
    },
    "Italian": {
        "Search": "Cerca", "Your Library": "La Tua Libreria", "Settings": "Impostazioni",
        "ALBUM": "ALBUM", "Cancel": "Annulla", "Delete [x]": "Elimina [x]", "Delete and Clear Music  [x] ": "Elimina e Svuota Musica  [x] ", "Refresh": "Aggiorna", "+ Add Folder": "+ Aggiungi Cartella", "Close": "Chiudi", "Manual": "Manuale", "Artist": "Artista", "Save": "Salva", "Clear": "Cancella", "Import": "Importa", "Name": "Nome", "Description": "Descrizione", "Go to 'Your Library' and tap '+' to create one.": "Vai su 'La Tua Libreria' e tocca '+' per crearne una.", "Tap '+ Add Folder' to open the built-in storage browser.": "Tocca '+ Aggiungi Cartella' per aprire l'esploratore di archiviazione.", "No local music loaded. Tap '+ Add Folder' above to explore your storage!": "Nessuna musica locale caricata. Tocca '+ Aggiungi Cartella' sopra per esplorare la tua memoria!", "Access Denied: Restricted system folder or permission missing.": "Accesso Negato: cartella di sistema riservata o permesso mancante.",
        "Desktop/Tablet": "Desktop/Tablet", "Phone": "Telefono", "Personalize": "Personalizza",
        "Language": "Lingua", "Back": "Indietro", "Active": "Attivo", "Tap to apply": "Tocca per applicare",
        "Color Themes": "Temi Colore", "App Font": "Font dell'App", "Grid": "Griglia",
        "Liked Songs": "Brani Preferiti",
        "Pick a color theme, then a font, for the whole app": "Scegli un tema colore, poi un font, per tutta l'app",
        "Changes the font used everywhere in the app": "Cambia il font usato in tutta l'app",
        "Choose your preferred language": "Scegli la tua lingua preferita",
        "Add an optional description": "Aggiungi una descrizione facoltativa",
        "Add to Playlist": "Aggiungi alla Playlist",
        "Artist of the Day": "Artista del Giorno",
        "CUSTOM PLAYLIST": "PLAYLIST PERSONALIZZATA",
        "PUBLIC PLAYLIST": "PLAYLIST PUBBLICA",
        "Choose Cover Image": "Scegli Immagine di Copertina",
        "Create playlist": "Crea playlist",
        "Edit Song Lyrics": "Modifica Testo della Canzone",
        "History Maker": "Momento Storico",
        "Imported Music Directories": "Cartelle Musicali Importate",
        "Loading art...": "Caricamento copertina...",
        "Loading chart data...": "Caricamento classifica...",
        "My Playlist #1": "La Mia Playlist #1",
        "No custom playlists built yet.": "Nessuna playlist personalizzata creata finora.",
        "Search Album Art  •  iTunes": "Cerca Copertina  •  iTunes",
        "Search Results": "Risultati di Ricerca",
        "Search Synced Lyrics": "Cerca Testo Sincronizzato",
        "Searching iTunes...": "Ricerca su iTunes...",
        "Searching...": "Ricerca...",
        "Song name": "Nome della canzone",
        "Song of the Day": "Canzone del Giorno",
        "Top 100": "Top 100",
        "e.g. Blinding Lights": "es. Blinding Lights",
        "e.g. The Weeknd": "es. The Weeknd",
        "Song of Day": "Canzone del Giorno",
        "Artist of Day": "Artista del Giorno",
        "History": "Cronologia",
    },
    "Portuguese": {
        "Search": "Pesquisar", "Your Library": "Sua Biblioteca", "Settings": "Configurações",
        "ALBUM": "ÁLBUM", "Cancel": "Cancelar", "Delete [x]": "Excluir [x]", "Delete and Clear Music  [x] ": "Excluir e Limpar Música  [x] ", "Refresh": "Atualizar", "+ Add Folder": "+ Adicionar Pasta", "Close": "Fechar", "Manual": "Manual", "Artist": "Artista", "Save": "Salvar", "Clear": "Limpar", "Import": "Importar", "Name": "Nome", "Description": "Descrição", "Go to 'Your Library' and tap '+' to create one.": "Vá em 'Sua Biblioteca' e toque em '+' para criar uma.", "Tap '+ Add Folder' to open the built-in storage browser.": "Toque em '+ Adicionar Pasta' para abrir o explorador de armazenamento.", "No local music loaded. Tap '+ Add Folder' above to explore your storage!": "Nenhuma música local carregada. Toque em '+ Adicionar Pasta' acima para explorar seu armazenamento!", "Access Denied: Restricted system folder or permission missing.": "Acesso Negado: pasta do sistema restrita ou permissão ausente.",
        "Desktop/Tablet": "Desktop/Tablet", "Phone": "Telefone", "Personalize": "Personalizar",
        "Language": "Idioma", "Back": "Voltar", "Active": "Ativo", "Tap to apply": "Toque para aplicar",
        "Color Themes": "Temas de Cor", "App Font": "Fonte do App", "Grid": "Grade",
        "Liked Songs": "Músicas Curtidas",
        "Pick a color theme, then a font, for the whole app": "Escolha um tema de cor, depois uma fonte, para o app inteiro",
        "Changes the font used everywhere in the app": "Muda a fonte usada em todo o app",
        "Choose your preferred language": "Escolha seu idioma preferido",
        "Add an optional description": "Adicione uma descrição opcional",
        "Add to Playlist": "Adicionar à Playlist",
        "Artist of the Day": "Artista do Dia",
        "CUSTOM PLAYLIST": "PLAYLIST PERSONALIZADA",
        "PUBLIC PLAYLIST": "PLAYLIST PÚBLICA",
        "Choose Cover Image": "Escolher Imagem de Capa",
        "Create playlist": "Criar playlist",
        "Edit Song Lyrics": "Editar Letra da Música",
        "History Maker": "Marco Histórico",
        "Imported Music Directories": "Pastas de Música Importadas",
        "Loading art...": "Carregando capa...",
        "Loading chart data...": "Carregando dados do ranking...",
        "My Playlist #1": "Minha Playlist #1",
        "No custom playlists built yet.": "Nenhuma playlist personalizada criada ainda.",
        "Search Album Art  •  iTunes": "Buscar Capa  •  iTunes",
        "Search Results": "Resultados da Busca",
        "Search Synced Lyrics": "Buscar Letra Sincronizada",
        "Searching iTunes...": "Buscando no iTunes...",
        "Searching...": "Buscando...",
        "Song name": "Nome da música",
        "Song of the Day": "Música do Dia",
        "Top 100": "Top 100",
        "e.g. Blinding Lights": "ex. Blinding Lights",
        "e.g. The Weeknd": "ex. The Weeknd",
        "Song of Day": "Música do Dia",
        "Artist of Day": "Artista do Dia",
        "History": "Histórico",
    },
    "Polish": {
        "Search": "Szukaj", "Your Library": "Twoja Biblioteka", "Settings": "Ustawienia",
        "ALBUM": "ALBUM", "Cancel": "Anuluj", "Delete [x]": "Usuń [x]", "Delete and Clear Music  [x] ": "Usuń i Wyczyść Muzykę  [x] ", "Refresh": "Odśwież", "+ Add Folder": "+ Dodaj Folder", "Close": "Zamknij", "Manual": "Ręcznie", "Artist": "Artysta", "Save": "Zapisz", "Clear": "Wyczyść", "Import": "Importuj", "Name": "Nazwa", "Description": "Opis", "Go to 'Your Library' and tap '+' to create one.": "Przejdź do 'Twojej Biblioteki' i dotknij '+', aby ją utworzyć.", "Tap '+ Add Folder' to open the built-in storage browser.": "Dotknij '+ Dodaj Folder', aby otworzyć przeglądarkę pamięci.", "No local music loaded. Tap '+ Add Folder' above to explore your storage!": "Nie wczytano lokalnej muzyki. Dotknij '+ Dodaj Folder' powyżej, aby przeszukać pamięć!", "Access Denied: Restricted system folder or permission missing.": "Odmowa Dostępu: folder systemowy jest zastrzeżony lub brak uprawnień.",
        "Desktop/Tablet": "Komputer/Tablet", "Phone": "Telefon", "Personalize": "Personalizuj",
        "Language": "Język", "Back": "Wstecz", "Active": "Aktywny", "Tap to apply": "Dotknij, aby zastosować",
        "Color Themes": "Motywy Kolorystyczne", "App Font": "Czcionka Aplikacji", "Grid": "Siatka",
        "Liked Songs": "Ulubione Utwory",
        "Pick a color theme, then a font, for the whole app": "Wybierz motyw kolorystyczny, a potem czcionkę dla całej aplikacji",
        "Changes the font used everywhere in the app": "Zmienia czcionkę używaną w całej aplikacji",
        "Choose your preferred language": "Wybierz preferowany język",
        "Add an optional description": "Dodaj opcjonalny opis",
        "Add to Playlist": "Dodaj do Playlisty",
        "Artist of the Day": "Artysta Dnia",
        "CUSTOM PLAYLIST": "WŁASNA PLAYLISTA",
        "PUBLIC PLAYLIST": "PUBLICZNA PLAYLISTA",
        "Choose Cover Image": "Wybierz Okładkę",
        "Create playlist": "Utwórz playlistę",
        "Edit Song Lyrics": "Edytuj Tekst Piosenki",
        "History Maker": "Moment Historyczny",
        "Imported Music Directories": "Zaimportowane Foldery Muzyczne",
        "Loading art...": "Wczytywanie okładki...",
        "Loading chart data...": "Wczytywanie listy przebojów...",
        "My Playlist #1": "Moja Playlista #1",
        "No custom playlists built yet.": "Nie utworzono jeszcze żadnej własnej playlisty.",
        "Search Album Art  •  iTunes": "Szukaj Okładki  •  iTunes",
        "Search Results": "Wyniki Wyszukiwania",
        "Search Synced Lyrics": "Szukaj Zsynchronizowanego Tekstu",
        "Searching iTunes...": "Wyszukiwanie w iTunes...",
        "Searching...": "Wyszukiwanie...",
        "Song name": "Nazwa utworu",
        "Song of the Day": "Piosenka Dnia",
        "Top 100": "Top 100",
        "e.g. Blinding Lights": "np. Blinding Lights",
        "e.g. The Weeknd": "np. The Weeknd",
        "Song of Day": "Piosenka Dnia",
        "Artist of Day": "Artysta Dnia",
        "History": "Historia",
    },
}

def t(text):
    """Translate a UI string into the currently-selected language, falling
    back to the original English text if no translation is defined."""
    return TRANSLATIONS.get(current_language, {}).get(text, text)

def apply_language(language_name):
    global current_language
    if language_name in LANGUAGES:
        current_language = language_name

# Cache of shrunk fonts so we're not rebuilding SysFont objects every frame.
_FIT_FONT_CACHE = {}

def _get_fit_font(size, bold):
    key = (size, bold)
    f = _FIT_FONT_CACHE.get(key)
    if f is None:
        f = pygame.font.SysFont("Arial", size, bold=bold)
        _FIT_FONT_CACHE[key] = f
    return f

def render_fit_text(text, color, max_width, base_size=14, bold=False, min_size=9):
    """Render text that auto-shrinks (down to min_size) so translated button
    labels never overlap a neighboring button or spill off the screen."""
    size = base_size
    surf = _get_fit_font(size, bold).render(text, True, color)
    while surf.get_width() > max_width and size > min_size:
        size -= 1
        surf = _get_fit_font(size, bold).render(text, True, color)
    # Hard clamp: even at the smallest font size some system fonts (varies by
    # device/OS) can still render wider than max_width, e.g. longer Polish/
    # German words. Guarantee the surface never exceeds max_width so labels
    # can never overlap a neighboring button.
    if surf.get_width() > max_width and max_width > 0:
        scale = max_width / surf.get_width()
        new_h = max(1, int(surf.get_height() * scale))
        surf = pygame.transform.smoothscale(surf, (max_width, new_h))
    return surf

# Each theme defines a full color set for the whole app. "classic" is the
# original SpotM-Fi black/green look. The others recolor everything — some
# flat, some ("gradient") sweep through multiple hues for the app background.
THEMES = {
    "classic": {
        "label": "Classic SpotM-Fi",
        "COLOR_BLACK":          (24, 24, 24),
        "COLOR_DARK_GREY":      (18, 18, 18),
        "COLOR_LIGHT_GREY":     (40, 40, 40),
        "COLOR_SPOTIFY_GREEN":  (30, 215, 96),
        "COLOR_WHITE":          (255, 255, 255),
        "COLOR_TEXT_MUTED":     (179, 179, 179),
        "COLOR_HOVER":          (50, 50, 50),
        "COLOR_CARD_BG":        (30, 30, 30),
        "COLOR_RED":            (230, 50, 50),
        "gradient":             None,
    },
    "midnight": {
        "label": "Midnight Blue",
        "COLOR_BLACK":          (14, 18, 28),
        "COLOR_DARK_GREY":      (10, 14, 22),
        "COLOR_LIGHT_GREY":     (30, 38, 54),
        "COLOR_SPOTIFY_GREEN":  (64, 156, 255),
        "COLOR_WHITE":          (235, 240, 250),
        "COLOR_TEXT_MUTED":     (150, 165, 190),
        "COLOR_HOVER":          (40, 50, 70),
        "COLOR_CARD_BG":        (22, 28, 42),
        "COLOR_RED":            (230, 70, 90),
        "gradient":             None,
    },
    "sunset": {
        "label": "Sunset Orange",
        "COLOR_BLACK":          (28, 18, 16),
        "COLOR_DARK_GREY":      (22, 14, 12),
        "COLOR_LIGHT_GREY":     (54, 34, 26),
        "COLOR_SPOTIFY_GREEN":  (255, 140, 66),
        "COLOR_WHITE":          (255, 245, 235),
        "COLOR_TEXT_MUTED":     (200, 165, 145),
        "COLOR_HOVER":          (70, 44, 32),
        "COLOR_CARD_BG":        (40, 26, 20),
        "COLOR_RED":            (235, 70, 60),
        "gradient":             None,
    },
    "rainbow": {
        "label": "Rainbow Pop",
        "COLOR_BLACK":          (26, 20, 30),
        "COLOR_DARK_GREY":      (20, 15, 24),
        "COLOR_LIGHT_GREY":     (48, 36, 52),
        "COLOR_SPOTIFY_GREEN":  (255, 209, 0),
        "COLOR_WHITE":          (255, 255, 255),
        "COLOR_TEXT_MUTED":     (210, 195, 215),
        "COLOR_HOVER":          (66, 46, 70),
        "COLOR_CARD_BG":        (36, 26, 40),
        "COLOR_RED":            (255, 60, 90),
        "gradient": [
            (60, 15, 20), (90, 40, 15), (85, 75, 15),
            (25, 70, 40), (15, 45, 80), (45, 20, 75), (60, 15, 20),
        ],
    },
    "neon": {
        "label": "Neon Cyberpunk",
        "COLOR_BLACK":          (10, 8, 18),
        "COLOR_DARK_GREY":      (8, 6, 14),
        "COLOR_LIGHT_GREY":     (28, 16, 42),
        "COLOR_SPOTIFY_GREEN":  (0, 255, 225),
        "COLOR_WHITE":          (240, 240, 255),
        "COLOR_TEXT_MUTED":     (170, 150, 210),
        "COLOR_HOVER":          (45, 15, 60),
        "COLOR_CARD_BG":        (18, 10, 30),
        "COLOR_RED":            (255, 45, 120),
        "gradient": [
            (10, 6, 24), (45, 8, 60), (60, 8, 40), (10, 30, 55), (10, 6, 24),
        ],
    },
    "pastel": {
        "label": "Pastel Dream",
        "COLOR_BLACK":          (32, 26, 34),
        "COLOR_DARK_GREY":      (26, 21, 28),
        "COLOR_LIGHT_GREY":     (54, 44, 56),
        "COLOR_SPOTIFY_GREEN":  (170, 230, 200),
        "COLOR_WHITE":          (255, 250, 250),
        "COLOR_TEXT_MUTED":     (215, 195, 210),
        "COLOR_HOVER":          (66, 52, 64),
        "COLOR_CARD_BG":        (42, 34, 44),
        "COLOR_RED":            (255, 150, 165),
        "gradient": [
            (60, 40, 50), (58, 46, 62), (44, 52, 60), (48, 58, 48), (60, 40, 50),
        ],
    },
    "galaxy": {
        "label": "Galaxy",
        "COLOR_BLACK":          (10, 8, 20),
        "COLOR_DARK_GREY":      (7, 6, 15),
        "COLOR_LIGHT_GREY":     (28, 20, 48),
        "COLOR_SPOTIFY_GREEN":  (200, 120, 255),
        "COLOR_WHITE":          (235, 232, 250),
        "COLOR_TEXT_MUTED":     (160, 150, 200),
        "COLOR_HOVER":          (42, 24, 66),
        "COLOR_CARD_BG":        (16, 12, 28),
        "COLOR_RED":            (255, 90, 150),
        "gradient": [
            (6, 5, 16), (18, 10, 38), (45, 15, 55), (20, 15, 50), (6, 5, 16),
        ],
    },
    "vaporwave": {
        "label": "Vaporwave",
        "COLOR_BLACK":          (24, 12, 30),
        "COLOR_DARK_GREY":      (18, 9, 24),
        "COLOR_LIGHT_GREY":     (46, 22, 54),
        "COLOR_SPOTIFY_GREEN":  (255, 113, 206),
        "COLOR_WHITE":          (245, 240, 255),
        "COLOR_TEXT_MUTED":     (200, 170, 210),
        "COLOR_HOVER":          (58, 26, 66),
        "COLOR_CARD_BG":        (32, 15, 40),
        "COLOR_RED":            (255, 80, 130),
        "gradient": [
            (45, 10, 45), (60, 15, 60), (20, 40, 60), (10, 55, 60), (45, 10, 45),
        ],
    },
    "tropical": {
        "label": "Tropical Punch",
        "COLOR_BLACK":          (8, 24, 22),
        "COLOR_DARK_GREY":      (6, 18, 17),
        "COLOR_LIGHT_GREY":     (16, 46, 40),
        "COLOR_SPOTIFY_GREEN":  (255, 209, 70),
        "COLOR_WHITE":          (250, 255, 245),
        "COLOR_TEXT_MUTED":     (170, 210, 190),
        "COLOR_HOVER":          (20, 60, 52),
        "COLOR_CARD_BG":        (12, 36, 32),
        "COLOR_RED":            (255, 90, 95),
        "gradient": [
            (5, 45, 55), (10, 90, 90), (30, 130, 90), (255, 160, 60), (255, 90, 95),
        ],
    },
    "candy": {
        "label": "Candy Shop",
        "COLOR_BLACK":          (26, 14, 24),
        "COLOR_DARK_GREY":      (20, 10, 18),
        "COLOR_LIGHT_GREY":     (52, 26, 46),
        "COLOR_SPOTIFY_GREEN":  (0, 220, 200),
        "COLOR_WHITE":          (255, 245, 250),
        "COLOR_TEXT_MUTED":     (215, 175, 205),
        "COLOR_HOVER":          (68, 30, 58),
        "COLOR_CARD_BG":        (38, 18, 34),
        "COLOR_RED":            (255, 70, 140),
        "gradient": [
            (255, 105, 180), (255, 170, 60), (255, 235, 90), (100, 220, 190), (140, 110, 255), (255, 105, 180),
        ],
    },
    "firestorm": {
        "label": "Firestorm",
        "COLOR_BLACK":          (20, 8, 8),
        "COLOR_DARK_GREY":      (16, 6, 6),
        "COLOR_LIGHT_GREY":     (48, 20, 16),
        "COLOR_SPOTIFY_GREEN":  (255, 200, 40),
        "COLOR_WHITE":          (255, 245, 235),
        "COLOR_TEXT_MUTED":     (215, 165, 140),
        "COLOR_HOVER":          (62, 24, 16),
        "COLOR_CARD_BG":        (34, 14, 12),
        "COLOR_RED":            (255, 60, 40),
        "gradient": [
            (20, 6, 6), (90, 15, 10), (200, 60, 10), (255, 140, 20), (255, 210, 50),
        ],
    },
    "arctic": {
        "label": "Arctic Aurora",
        "COLOR_BLACK":          (8, 14, 20),
        "COLOR_DARK_GREY":      (6, 11, 16),
        "COLOR_LIGHT_GREY":     (20, 36, 44),
        "COLOR_SPOTIFY_GREEN":  (110, 255, 200),
        "COLOR_WHITE":          (235, 250, 255),
        "COLOR_TEXT_MUTED":     (150, 190, 200),
        "COLOR_HOVER":          (24, 48, 56),
        "COLOR_CARD_BG":        (14, 26, 32),
        "COLOR_RED":            (255, 100, 150),
        "gradient": [
            (6, 10, 25), (10, 40, 55), (30, 110, 110), (110, 220, 190), (150, 110, 220), (6, 10, 25),
        ],
    },
    "carnival": {
        "label": "Carnival",
        "COLOR_BLACK":          (30, 10, 26),
        "COLOR_DARK_GREY":      (24, 8, 20),
        "COLOR_LIGHT_GREY":     (58, 20, 46),
        "COLOR_SPOTIFY_GREEN":  (255, 225, 0),
        "COLOR_WHITE":          (255, 250, 240),
        "COLOR_TEXT_MUTED":     (225, 185, 150),
        "COLOR_HOVER":          (72, 26, 54),
        "COLOR_CARD_BG":        (40, 14, 32),
        "COLOR_RED":            (255, 45, 85),
        "gradient": [
            (255, 45, 85), (255, 150, 0), (255, 225, 0), (0, 200, 140), (0, 140, 255), (170, 50, 220), (255, 45, 85),
        ],
    },
    "bubblegum": {
        "label": "Bubblegum",
        "COLOR_BLACK":          (28, 12, 30),
        "COLOR_DARK_GREY":      (22, 9, 24),
        "COLOR_LIGHT_GREY":     (56, 24, 58),
        "COLOR_SPOTIFY_GREEN":  (120, 235, 255),
        "COLOR_WHITE":          (255, 245, 252),
        "COLOR_TEXT_MUTED":     (220, 180, 220),
        "COLOR_HOVER":          (72, 30, 72),
        "COLOR_CARD_BG":        (40, 16, 42),
        "COLOR_RED":            (255, 90, 170),
        "gradient": [
            (255, 150, 210), (255, 200, 230), (200, 170, 255), (150, 220, 255), (255, 150, 210),
        ],
    },
    "citrus": {
        "label": "Citrus Splash",
        "COLOR_BLACK":          (24, 20, 6),
        "COLOR_DARK_GREY":      (18, 15, 5),
        "COLOR_LIGHT_GREY":     (52, 42, 12),
        "COLOR_SPOTIFY_GREEN":  (170, 230, 30),
        "COLOR_WHITE":          (255, 252, 235),
        "COLOR_TEXT_MUTED":     (215, 195, 130),
        "COLOR_HOVER":          (66, 52, 14),
        "COLOR_CARD_BG":        (36, 28, 8),
        "COLOR_RED":            (255, 70, 40),
        "gradient": [
            (255, 235, 40), (255, 170, 20), (255, 90, 20), (170, 230, 30), (255, 235, 40),
        ],
    },
    "cosmic_candy": {
        "label": "Cosmic Candy",
        "COLOR_BLACK":          (10, 6, 22),
        "COLOR_DARK_GREY":      (8, 5, 17),
        "COLOR_LIGHT_GREY":     (32, 18, 52),
        "COLOR_SPOTIFY_GREEN":  (0, 255, 190),
        "COLOR_WHITE":          (245, 240, 255),
        "COLOR_TEXT_MUTED":     (190, 170, 220),
        "COLOR_HOVER":          (46, 22, 66),
        "COLOR_CARD_BG":        (22, 12, 38),
        "COLOR_RED":            (255, 60, 130),
        "gradient": [
            (10, 6, 22), (90, 20, 130), (220, 40, 160), (255, 130, 60), (0, 220, 190), (10, 6, 22),
        ],
    },
    "disco": {
        "label": "Disco Fever",
        "COLOR_BLACK":          (16, 12, 8),
        "COLOR_DARK_GREY":      (12, 9, 6),
        "COLOR_LIGHT_GREY":     (48, 34, 14),
        "COLOR_SPOTIFY_GREEN":  (255, 190, 0),
        "COLOR_WHITE":          (255, 250, 235),
        "COLOR_TEXT_MUTED":     (215, 190, 140),
        "COLOR_HOVER":          (60, 40, 12),
        "COLOR_CARD_BG":        (32, 22, 10),
        "COLOR_RED":            (255, 50, 50),
        "gradient": [
            (255, 50, 50), (255, 150, 0), (255, 220, 0), (60, 220, 90), (0, 180, 255), (170, 60, 255), (255, 50, 50),
        ],
    },
    "high_contrast": {
        "label": "High Contrast",
        "COLOR_BLACK":          (0, 0, 0),
        "COLOR_DARK_GREY":      (0, 0, 0),
        "COLOR_LIGHT_GREY":     (35, 35, 35),
        "COLOR_SPOTIFY_GREEN":  (255, 230, 0),   # high-visibility accent
        "COLOR_WHITE":          (255, 255, 255),
        "COLOR_TEXT_MUTED":     (225, 225, 225), # much lighter than the usual muted grey, for readability
        "COLOR_HOVER":          (90, 90, 90),
        "COLOR_CARD_BG":        (15, 15, 15),
        "COLOR_RED":            (255, 70, 70),
        "gradient":             None,
    },
}

# --- GRADIENT-BACKGROUND CACHE ---
# Same per-frame-recompute issue as the caches above: this painted a
# multi-stop gradient one pixel-row at a time via a Python-level loop of
# pygame.draw.line calls, redone from scratch every single frame it was
# visible, even though the same rect size + color stops always produce the
# exact same image until the theme or window size actually changes. Cache
# the finished gradient as a Surface and blit it thereafter. Keyed on
# (rect size, colors) using the same identity/value-based reasoning as the
# other caches here, so a theme switch (new color list) or a resize simply
# misses and rebuilds fresh.
_gradient_cache = {}
def draw_multicolor_gradient(surface, rect, colors):
    """Paint a smooth multi-stop vertical gradient into rect (a pygame.Rect-like
    tuple) using the given list of colors as sequential stops."""
    x, y, w, h = rect
    if not colors:
        return
    key = (w, h, tuple(colors))
    cached = _gradient_cache.get(key)
    if cached is None:
        cached = pygame.Surface((w, h))
        if len(colors) == 1:
            cached.fill(colors[0])
        else:
            segments = len(colors) - 1
            seg_h = h / segments
            for i in range(segments):
                c1, c2 = colors[i], colors[i + 1]
                seg_top = int(i * seg_h)
                seg_bottom = int((i + 1) * seg_h)
                seg_height = max(1, seg_bottom - seg_top)
                for row in range(seg_height):
                    t = row / seg_height
                    r = int(c1[0] + (c2[0] - c1[0]) * t)
                    g = int(c1[1] + (c2[1] - c1[1]) * t)
                    b = int(c1[2] + (c2[2] - c1[2]) * t)
                    pygame.draw.line(cached, (r, g, b), (0, seg_top + row), (w, seg_top + row))
        _gradient_cache[key] = cached
    surface.blit(cached, (x, y))

def apply_theme(theme_key):
    """Recolor the entire app by reassigning the global color constants used
    throughout every draw function."""
    global current_theme
    global COLOR_BLACK, COLOR_DARK_GREY, COLOR_LIGHT_GREY, COLOR_SPOTIFY_GREEN
    global COLOR_WHITE, COLOR_TEXT_MUTED, COLOR_HOVER, COLOR_CARD_BG, COLOR_RED
    theme = THEMES.get(theme_key, THEMES["classic"])
    current_theme = theme_key
    COLOR_BLACK          = theme["COLOR_BLACK"]
    COLOR_DARK_GREY      = theme["COLOR_DARK_GREY"]
    COLOR_LIGHT_GREY     = theme["COLOR_LIGHT_GREY"]
    COLOR_SPOTIFY_GREEN  = theme["COLOR_SPOTIFY_GREEN"]
    COLOR_WHITE          = theme["COLOR_WHITE"]
    COLOR_TEXT_MUTED     = theme["COLOR_TEXT_MUTED"]
    COLOR_HOVER          = theme["COLOR_HOVER"]
    COLOR_CARD_BG        = theme["COLOR_CARD_BG"]
    COLOR_RED            = theme["COLOR_RED"]

modal_close_rect = pygame.Rect(0, 0, 0, 0)
modal_save_rect = pygame.Rect(0, 0, 0, 0)
modal_input_rect = pygame.Rect(0, 0, 0, 0)
modal_desc_rect = pygame.Rect(0, 0, 0, 0)
modal_image_picker_rect = pygame.Rect(0, 0, 0, 0)

lyrics_close_rect = pygame.Rect(0, 0, 0, 0)
lyrics_save_rect = pygame.Rect(0, 0, 0, 0)
lyrics_clear_rect = pygame.Rect(0, 0, 0, 0)
lyrics_import_rect = pygame.Rect(0, 0, 0, 0)
lyrics_search_rect = pygame.Rect(0, 0, 0, 0)
lyrics_textarea_rect = pygame.Rect(270, 145, 760, 420)

# --- LYRICS SEARCH (synced lyrics library lookup) MODAL STATE ---
show_lyrics_search_modal = False
lyrics_search_loading = False
lyrics_search_results = []      
lyrics_search_error = ""        
lyrics_search_thread = None
lyrics_search_close_rect = pygame.Rect(0, 0, 0, 0)
lyrics_search_item_rects = []    
lyrics_search_scroll_offset = 0.0
target_lyrics_search_scroll = 0.0
max_lyrics_search_scroll = 0

# --- MANUAL SONG/ARTIST ENTRY MODAL STATE (for the synced lyrics search) ---
show_lyrics_manual_modal = False
manual_title_text    = ""
manual_artist_text   = ""
manual_title_cursor  = 0
manual_artist_cursor = 0
lyrics_manual_rect = pygame.Rect(0, 0, 0, 0)
lyrics_manual_title_rect = pygame.Rect(0, 0, 0, 0)
lyrics_manual_artist_rect = pygame.Rect(0, 0, 0, 0)
lyrics_manual_go_rect = pygame.Rect(0, 0, 0, 0)
lyrics_manual_close_rect = pygame.Rect(0, 0, 0, 0)

_LYRICS_SEARCH_NOISE_WORDS = {
    "official", "video", "audio", "lyrics", "lyric", "hd", "hq", "4k",
    "remastered", "remaster", "extended", "radio", "edit", "version",
    "mv", "explicit", "clean", "visualizer", "live", "ost", "soundtrack",
    "full", "track", "single"
}

def _safe_str(s):
    """Strip null bytes and non-printable control characters that crash
    pygame.font.render, then return a plain ASCII-safe unicode string."""
    if not isinstance(s, str):
        s = str(s) if s is not None else ""
    # Remove null bytes and C0/C1 control chars except tab/newline
    s = re.sub(r'[\x00-\x08\x0b\x0c\x0e-\x1f\x7f-\x9f]', '', s)
    return s

def shorten_title_keywords(raw_title):
    """Strips filler noise (bracketed tags, file extensions, words like
    'Official Video', 'Remastered', etc.) from a messy song title and
    returns just the core keywords, so the lyrics search can match a
    wider range of different songs instead of one exact messy string."""
    if not raw_title:
        return raw_title
    t = raw_title
    t = re.sub(r'\.[a-zA-Z0-9]{2,4}$', '', t)
    t = re.sub(r'[\(\[\{][^\)\]\}]*[\)\]\}]', ' ', t)
    words = re.findall(r"[A-Za-z0-9']+", t)
    keywords = [w for w in words if w.lower() not in _LYRICS_SEARCH_NOISE_WORDS]
    if not keywords:
        keywords = words
    return " ".join(keywords[:6]).strip()

def _query_lrclib(params):
    """Runs a single lrclib.net search request and returns the parsed
    JSON list (or raises on network/HTTP error). Retries a couple of times
    on transient 502/503/504 gateway errors, which lrclib's infrastructure
    occasionally returns for a moment even when the API itself is fine."""
    url = "https://lrclib.net/api/search?" + urllib.parse.urlencode(params)
    req = urllib.request.Request(url, headers={
        "User-Agent": "MusicPlayerApp/1.0 (+https://github.com)",
        "Accept": "application/json",
    })

    attempts = 3
    last_exc = None
    for attempt in range(attempts):
        try:
            try:
                with urllib.request.urlopen(req, timeout=8) as resp:
                    raw = resp.read().decode("utf-8", errors="ignore")
            except urllib.error.URLError as ssl_err:
                # Android/Pydroid builds often ship without a usable CA bundle, which
                # makes HTTPS requests fail with a certificate verify error even when
                # the network connection itself is fine. Retry once with an
                # unverified SSL context so it isn't misreported as "no internet".
                if "CERTIFICATE_VERIFY_FAILED" in str(ssl_err) or "certificate" in str(ssl_err).lower():
                    import ssl
                    unverified_ctx = ssl._create_unverified_context()
                    with urllib.request.urlopen(req, timeout=8, context=unverified_ctx) as resp:
                        raw = resp.read().decode("utf-8", errors="ignore")
                else:
                    raise
            return json.loads(raw)
        except urllib.error.HTTPError as http_err:
            last_exc = http_err
            if http_err.code in (502, 503, 504) and attempt < attempts - 1:
                time.sleep(0.6 * (attempt + 1))
                continue
            raise
        except urllib.error.URLError as url_err:
            last_exc = url_err
            if attempt < attempts - 1:
                time.sleep(0.6 * (attempt + 1))
                continue
            raise
    if last_exc:
        raise last_exc

def fetch_synced_lyrics_candidates(title, artist):
    """Runs on a background thread: queries the lrclib.net synced lyrics
    library for candidate matches of the currently playing song title.
    Tries a few different query variants, since a messy/auto-detected
    title can fail to match even when the song is really in the library."""
    global lyrics_search_loading, lyrics_search_results, lyrics_search_error
    has_artist = bool(artist and artist.lower() not in ("unknown artist", "unknown", ""))

    last_error = "Failed - no matches found for this song."
    try:
        query_variants = []
        shortened = shorten_title_keywords(title)
        if shortened:
            query_variants.append({"track_name": shortened})
        if title and title != shortened:
            query_variants.append({"track_name": title})
        fuzzy_text = f"{title} {artist}".strip() if has_artist else (title or "")
        if fuzzy_text:
            query_variants.append({"q": fuzzy_text})

        for base_params in query_variants:
            params = dict(base_params)
            if has_artist and "q" not in params:
                params["artist_name"] = artist
            try:
                data = _query_lrclib(params)
            except Exception as e:
                last_error = f"Failed - {type(e).__name__}: {e}"
                continue
            if isinstance(data, list) and len(data) > 0:
                clean = []
                for item in data[:12]:
                    try:
                        clean.append({
                            "trackName":    _safe_str(item.get("trackName",   "")),
                            "artistName":   _safe_str(item.get("artistName",  "")),
                            "albumName":    _safe_str(item.get("albumName",   "")),
                            "duration":     item.get("duration"),
                            "syncedLyrics": item.get("syncedLyrics") or "",
                            "plainLyrics":  item.get("plainLyrics")  or "",
                        })
                    except Exception:
                        pass
                if clean:
                    lyrics_search_results = clean
                    lyrics_search_error = ""
                    lyrics_search_loading = False
                    return
        lyrics_search_results = []
        lyrics_search_error = last_error
    except Exception as e:
        lyrics_search_results = []
        # Show the actual exception so real causes (no permission, DNS, SSL,
        # timeout, HTTP error) are visible instead of one generic message.
        lyrics_search_error = f"Failed - {type(e).__name__}: {e}"
    finally:
        lyrics_search_loading = False

def start_lyrics_search(title, artist):
    global show_lyrics_search_modal, show_lyrics_manual_modal, lyrics_search_loading, lyrics_search_results, lyrics_search_error, lyrics_search_thread, lyrics_search_scroll_offset
    show_lyrics_search_modal = True
    show_lyrics_manual_modal = False
    lyrics_search_loading = True
    lyrics_search_results = []
    lyrics_search_error = ""
    lyrics_search_scroll_offset = 0.0
    lyrics_search_thread = threading.Thread(target=fetch_synced_lyrics_candidates, args=(title, artist), daemon=True)
    lyrics_search_thread.start()

def _decode_image_bytes_safely(img_bytes):
    """Decode raw image bytes into a pygame Surface, going through Pillow first.
    Pygame's own built-in image loader can lack full JPEG support (and has been
    seen to hard-crash the whole app instead of raising a catchable error) on
    some Android builds — this is the same workaround already used elsewhere in
    this file for embedded ID3/FLAC/MP4 cover art. iTunes artwork downloads hit
    the exact same decoder, so they need the same protection. Falls back to
    pygame's own loader only if Pillow isn't available."""
    try:
        from PIL import Image
        pil_img = Image.open(io.BytesIO(img_bytes)).convert("RGB")
        return pygame.image.fromstring(pil_img.tobytes(), pil_img.size, "RGB")
    except Exception:
        pass
    return pygame.image.load(io.BytesIO(img_bytes))

def fetch_itunes_art_candidates(title, artist):
    """Background thread: queries the iTunes Search API for artwork candidates."""
    global art_search_loading, art_search_results, art_search_error
    try:
        query_variants = []
        has_artist = bool(artist and artist.lower() not in ("unknown artist", "unknown", ""))
        if has_artist:
            query_variants.append(f"{title} {artist}")
        query_variants.append(title)

        for q in query_variants:
            params = urllib.parse.urlencode({
                "term": q, "entity": "song", "media": "music", "limit": 12
            })
            url = f"https://itunes.apple.com/search?{params}"
            req = urllib.request.Request(url, headers={"User-Agent": "SpotMFi/1.0"})
            with urllib.request.urlopen(req, timeout=10) as resp:
                data = json.loads(resp.read().decode("utf-8"))
            results = data.get("results", [])
            if results:
                art_search_results = results
                art_search_error = ""
                art_search_loading = False
                _start_art_search_thumbnails(results)
                return

        art_search_results = []
        art_search_error = "Failed - no results found for this song."
    except Exception as e:
        art_search_results = []
        art_search_error = f"Failed - {type(e).__name__}: {e}"
    finally:
        art_search_loading = False

def _fetch_art_search_thumbnails_worker(results, my_gen):
    """Background thread: downloads the small (60x60) iTunes thumbnail for each
    search result so the list can show the actual cover instead of a generic
    placeholder icon. Runs sequentially (thumbnails are tiny) and stores decoded
    surfaces in art_search_thumb_surfaces, keyed by artworkUrl60, as they arrive
    so rows can start showing real art before the whole batch finishes."""
    global art_search_thumb_gen
    for result in results:
        if my_gen != art_search_thumb_gen:
            return  # a newer search superseded this one; stop wasting requests
        url = result.get("artworkUrl60") or result.get("artworkUrl100") or result.get("artworkUrl30")
        if not url or url in art_search_thumb_surfaces or url in art_search_thumb_failed:
            continue
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "SpotMFi/1.0"})
            with urllib.request.urlopen(req, timeout=10) as resp:
                img_bytes = resp.read()
            raw_img = _decode_image_bytes_safely(img_bytes)
            thumb_surf = pygame.transform.smoothscale(raw_img, (52, 52))
            if my_gen == art_search_thumb_gen:
                art_search_thumb_surfaces[url] = thumb_surf
        except Exception:
            art_search_thumb_failed.add(url)

def _start_art_search_thumbnails(results):
    global art_search_thumb_gen
    art_search_thumb_gen += 1
    threading.Thread(target=_fetch_art_search_thumbnails_worker,
                      args=(results, art_search_thumb_gen), daemon=True).start()

def start_art_search(title, artist):
    global show_art_search_modal, art_search_loading, art_search_results, art_search_error, art_search_thread, art_search_scroll_offset
    show_art_search_modal = True
    art_search_loading = True
    art_search_results = []
    art_search_error = ""
    art_search_scroll_offset = 0.0
    art_search_thread = threading.Thread(target=fetch_itunes_art_candidates, args=(title, artist), daemon=True)
    art_search_thread.start()

def apply_itunes_art(artwork_url):
    """Download an iTunes artwork URL (swap 100x100 thumbnail for 600x600),
    save it into the app's own covers folder (so it's easy to find and
    survives OS temp-file cleanup), and return the saved path."""
    global art_search_error
    try:
        hq_url = artwork_url.replace("100x100bb", "600x600bb")
        req = urllib.request.Request(hq_url, headers={"User-Agent": "SpotMFi/1.0"})
        with urllib.request.urlopen(req, timeout=15) as resp:
            img_bytes = resp.read()
        suffix = ".jpg" if "jpeg" in hq_url or "jpg" in hq_url else ".png"
        file_name = f"cover_{uuid.uuid4().hex}{suffix}"
        dest_path = os.path.join(COVERS_DIR, file_name)
        with open(dest_path, "wb") as f:
            f.write(img_bytes)
        return dest_path
    except Exception as e:
        art_search_error = f"Failed - {type(e).__name__}: {e}"
        return None

def _apply_itunes_art_worker(artwork_url, track_path):
    """Background thread: downloads the chosen artwork off the UI thread so the
    app doesn't freeze while waiting on the network (this was previously done
    inline in the click handler, which blocked rendering/input on slow/mobile
    connections)."""
    global art_apply_result_path, art_apply_pending
    result = apply_itunes_art(artwork_url)
    art_apply_result_path = result if result else ""
    art_apply_pending = False

def start_apply_itunes_art(artwork_url, track_path):
    global art_apply_thread, art_apply_pending, art_apply_result_path, art_apply_track_path, art_search_error
    art_apply_pending     = True
    art_apply_result_path = None
    art_apply_track_path  = track_path
    art_search_error      = ""
    art_apply_thread = threading.Thread(target=_apply_itunes_art_worker, args=(artwork_url, track_path), daemon=True)
    art_apply_thread.start()

def _normalize_match_text(s):
    """Lowercases, strips bracketed noise (feat./remaster/official video tags
    etc.) and punctuation, so two differently-formatted strings for the same
    song ('Song Title (Remastered 2011)' vs 'Song Title') compare as equal
    rather than merely similar."""
    s = (s or "").lower()
    s = re.sub(r'[\(\[\{][^\)\]\}]*[\)\]\}]', ' ', s)
    s = re.sub(r"[^a-z0-9']+", ' ', s)
    return re.sub(r'\s+', ' ', s).strip()

def _match_score(candidate_title, candidate_artist, wanted_title, wanted_artist):
    """0..1 similarity score blending title and artist closeness. Used to
    pick the right result out of several search-API candidates instead of
    blindly trusting whichever one the API happens to list first - which is
    what let unrelated songs' art/lyrics get attached to the wrong track."""
    t_score = difflib.SequenceMatcher(None, _normalize_match_text(candidate_title), _normalize_match_text(wanted_title)).ratio()
    if wanted_artist:
        a_score = difflib.SequenceMatcher(None, _normalize_match_text(candidate_artist), _normalize_match_text(wanted_artist)).ratio()
        return t_score * 0.65 + a_score * 0.35
    return t_score

def _onboarding_fetch_lyrics_for_track(title, artist):
    """Best-effort lrclib.net lyrics lookup for the onboarding auto-scrape
    flow. Unlike fetch_synced_lyrics_candidates this doesn't touch any of the
    "Search Lyrics" modal's UI globals - it just returns a lyrics string or
    None so it's safe to run in a plain background loop over the whole
    library.

    Two accuracy improvements over the old version: it falls back to plain
    (unsynced) lyrics when lrclib has no synced version for a track, instead
    of skipping that track entirely - so "yes, find lyrics for everything"
    actually covers everything lrclib has, not just the subset with karaoke
    timing. And every candidate is scored against the track's own
    title/artist (see _match_score) so a loosely-related search hit can't
    get attached to the wrong song; only a strong-enough match is used."""
    try:
        has_artist = bool(artist and artist.lower() not in ("unknown artist", "unknown", ""))
        variants = []
        shortened = shorten_title_keywords(title)
        if shortened:
            variants.append({"track_name": shortened})
        if title and title != shortened:
            variants.append({"track_name": title})
        fuzzy_text = f"{title} {artist}".strip() if has_artist else (title or "")
        if fuzzy_text:
            variants.append({"q": fuzzy_text})

        best_lyrics = None
        best_score = 0.0
        top_of_list_lyrics = None  # first usable result seen, in API order - same thing a
                                    # manual "Search Lyrics" lookup shows at the top and is
                                    # almost always right, used as a fallback below so a
                                    # merely-imperfect score doesn't cause a track to be
                                    # skipped entirely
        for base in variants:
            params = dict(base)
            if has_artist and "q" not in params:
                params["artist_name"] = artist
            try:
                data = _query_lrclib(params)
            except Exception:
                continue
            if not isinstance(data, list):
                continue
            for item in data:
                lyr = item.get("syncedLyrics") or item.get("plainLyrics")
                if not lyr:
                    continue
                if top_of_list_lyrics is None:
                    top_of_list_lyrics = lyr
                score = _match_score(item.get("trackName", ""), item.get("artistName", ""), title, artist if has_artist else "")
                if item.get("syncedLyrics"):
                    score += 0.05  # small nudge - prefer synced over plain when scores are close
                if score > best_score:
                    best_score = score
                    best_lyrics = lyr
            if best_score >= 0.8:
                break  # good enough match already - no need to burn another request
            if top_of_list_lyrics is not None:
                break  # already have a top-of-list fallback candidate, no need to widen the search

        if best_lyrics and best_score >= 0.35:
            return best_lyrics
        if top_of_list_lyrics:
            # scoring wasn't confident enough, but the top search result is exactly
            # what a manual lyrics search would show and use - trust it rather than
            # skipping the track entirely
            return top_of_list_lyrics
    except Exception:
        pass
    return None

def _onboarding_fetch_art_for_track(title, artist):
    """Best-effort iTunes artwork lookup + download for the onboarding
    auto-scrape flow. Returns a saved local file path (see apply_itunes_art)
    or None on failure.

    Two accuracy improvements over the old version: it queries with a
    cleaned-up title first (stripping noise like "(Official Video)" or
    "Remastered 2011" - the same cleanup lyrics matching already used),
    falling back to the raw title if that turns up nothing; and it pulls
    back several candidates per query and scores each one's title/artist
    against the track's own (see _match_score) instead of blindly trusting
    result #1, so a same-named-but-different song can't get attached as the
    cover. A match that's too weak is skipped rather than guessed at."""
    try:
        has_artist = bool(artist and artist.lower() not in ("unknown artist", "unknown", ""))
        cleaned_title = shorten_title_keywords(title) or title

        query_variants = []
        if cleaned_title:
            query_variants.append(f"{cleaned_title} {artist}" if has_artist else cleaned_title)
        if title and title != cleaned_title:
            query_variants.append(f"{title} {artist}" if has_artist else title)
        seen = set()
        query_variants = [q for q in query_variants if q.strip() and not (q in seen or seen.add(q))]
        if not query_variants:
            return None

        best_result = None
        best_score = 0.0
        top_of_list_result = None  # first result returned by iTunes, in API order - this is
                                    # exactly what a manual "Search Artwork" lookup shows at
                                    # the top of the list (and picks correctly), so it's used
                                    # as a fallback below instead of skipping the track just
                                    # because our own scoring wasn't confident enough
        for query in query_variants:
            params = urllib.parse.urlencode({"term": query, "entity": "song", "media": "music", "limit": 8})
            url = f"https://itunes.apple.com/search?{params}"
            req = urllib.request.Request(url, headers={"User-Agent": "SpotMFi/1.0"})
            try:
                with urllib.request.urlopen(req, timeout=10) as resp:
                    data = json.loads(resp.read().decode("utf-8"))
            except Exception:
                continue
            results = data.get("results", [])
            if results and top_of_list_result is None:
                top_of_list_result = results[0]
            for result in results:
                score = _match_score(result.get("trackName", ""), result.get("artistName", ""), title, artist if has_artist else "")
                if score > best_score:
                    best_score = score
                    best_result = result
            if best_score >= 0.75:
                break  # strong match already - no need to also burn the raw-title fallback request
            if top_of_list_result is not None:
                break  # already have a top-of-list fallback candidate, no need to widen the search

        if best_result is None or best_score < 0.4:
            if top_of_list_result is None:
                return None  # genuinely no results at all - nothing to fall back to
            best_result = top_of_list_result  # trust the top-of-list result, same as a manual search would

        art_url = best_result.get("artworkUrl100")
        if art_url:
            return apply_itunes_art(art_url)
    except Exception:
        pass
    return None

def _onboarding_scrape_worker():
    """Runs on a background thread once the user opts in on the "scrape"
    onboarding stage: walks every currently-imported track and, for any track
    still missing lyrics and/or cover art, tries to fill them in from lrclib.net
    / the iTunes Search API. Skips tracks that already have either, so it never
    clobbers something the user (or the tag/embedded art) already set."""
    global onboarding_scrape_active, onboarding_scrape_progress
    tracks_todo = list(imported_tracks)
    total = len(tracks_todo)
    onboarding_scrape_progress = (0, total)
    for i, trk in enumerate(tracks_todo):
        path = trk.get("path", "")
        title = trk.get("title", "") or ""
        artist = trk.get("artist", "") or ""

        if path and not song_lyrics_database.get(path):
            try:
                lyrics = _onboarding_fetch_lyrics_for_track(title, artist)
                if lyrics:
                    song_lyrics_database[path] = lyrics
            except Exception:
                pass

        if path and path not in track_covers:
            try:
                art_path = _onboarding_fetch_art_for_track(title, artist)
                if art_path:
                    with open(art_path, "rb") as f:
                        img_bytes = f.read()
                    raw_img = _decode_image_bytes_safely(img_bytes)
                    cover_surf = pygame.transform.smoothscale(raw_img, (130, 130))
                    track_covers[path] = {"image_path": art_path, "surface": cover_surf}
                    for t2 in imported_tracks:
                        if t2["path"] == path:
                            t2["cover_surface"] = cover_surf
            except Exception:
                pass

        onboarding_scrape_progress = (i + 1, total)

    try:
        save_app_data()
    except Exception:
        pass
    onboarding_scrape_active = False

def start_onboarding_scrape():
    global onboarding_scrape_active, onboarding_scrape_progress
    onboarding_scrape_active = True
    onboarding_scrape_progress = (0, len(imported_tracks))
    threading.Thread(target=_onboarding_scrape_worker, daemon=True).start()

def _fetch_top100_worker():
    """Background thread: fetches chart data then kicks off artwork downloads."""
    global top100_tracks, top100_loading, top100_error, top100_last_fetched

    def build_links(title, artist):
        q = urllib.parse.quote_plus(f"{title} {artist}")
        spotify_url = f"https://open.spotify.com/search/{urllib.parse.quote(title + ' ' + artist)}"
        youtube_url = f"https://music.youtube.com/search?q={q}"
        apple_url   = f"https://music.apple.com/us/search?term={q}"
        return spotify_url, youtube_url, apple_url

    tracks = []

    # --- Primary: Spotify Charts public page (no auth, updates daily) ---
    try:
        url = "https://charts.spotify.com/charts/view/regional-global-daily/latest"
        req = urllib.request.Request(url, headers={
            "User-Agent": "Mozilla/5.0 (compatible; SpotMFi/1.0)",
            "Accept": "application/json"
        })
        with urllib.request.urlopen(req, timeout=12) as r:
            raw = r.read().decode("utf-8", errors="replace")
        if raw.strip().startswith("{"):
            data = json.loads(raw)
            entries = data.get("entries", data.get("chartEntryData", []))
            for entry in entries[:100]:
                try:
                    td = entry.get("trackMetadata", entry)
                    title  = td.get("trackName", td.get("name",   ""))
                    artist = td.get("artists",    td.get("artist", ""))
                    if isinstance(artist, list):
                        artist = ", ".join(a.get("name", str(a)) for a in artist)
                    if title:
                        sp, yt, ap = build_links(title, artist)
                        tracks.append({"rank": len(tracks)+1, "title": title,
                                       "artist": artist, "spotify_url": sp,
                                       "youtube_url": yt, "apple_url": ap,
                                       "art_url": ""})
                except Exception:
                    pass
    except Exception:
        pass

    # --- Fallback / top-up: Apple Music Global Top 100 RSS (always public) ---
    # The RSS also gives us artworkUrl100 for free — upgrade to 600x600
    if len(tracks) < 50:
        try:
            url2 = "https://rss.applemarketingtools.com/api/v2/us/music/most-played/100/songs.json"
            req2 = urllib.request.Request(url2, headers={"User-Agent": "SpotMFi/1.0"})
            with urllib.request.urlopen(req2, timeout=12) as r2:
                data2 = json.loads(r2.read().decode("utf-8"))
            seen = {(t["title"].lower(), t["artist"].lower()) for t in tracks}
            for item in data2.get("feed", {}).get("results", []):
                title   = item.get("name", "")
                artist  = item.get("artistName", "")
                art_url = item.get("artworkUrl100", "").replace("100x100bb", "300x300bb")
                if not title or (title.lower(), artist.lower()) in seen:
                    continue
                sp, yt, ap = build_links(title, artist)
                tracks.append({"rank": len(tracks)+1, "title": title,
                                "artist": artist, "spotify_url": sp,
                                "youtube_url": yt, "apple_url": ap,
                                "art_url": art_url})
                seen.add((title.lower(), artist.lower()))
                if len(tracks) >= 100:
                    break
        except Exception as e2:
            if not tracks:
                top100_error   = f"Failed to load chart data: {e2}"
                top100_loading = False
                return

    # Re-number ranks
    for i, t in enumerate(tracks):
        t["rank"] = i + 1

    top100_tracks       = tracks[:100]
    top100_last_fetched = time.time()
    top100_error        = ""
    top100_loading      = False

    # For tracks that still have no art URL, fetch from iTunes search
    # Do this in a second pass so the list appears immediately
    def _fetch_missing_art_urls():
        for t in top100_tracks:
            if t.get("art_url"):
                continue
            try:
                params = urllib.parse.urlencode({
                    "term": f"{t['title']} {t['artist']}",
                    "entity": "song", "media": "music", "limit": 1
                })
                req_i = urllib.request.Request(
                    f"https://itunes.apple.com/search?{params}",
                    headers={"User-Agent": "SpotMFi/1.0"})
                with urllib.request.urlopen(req_i, timeout=8) as ri:
                    rd = json.loads(ri.read().decode("utf-8"))
                results = rd.get("results", [])
                if results:
                    t["art_url"] = results[0].get("artworkUrl100", "").replace("100x100bb", "300x300bb")
            except Exception:
                pass

    threading.Thread(target=_fetch_missing_art_urls, daemon=True).start()
    # Kick off actual image downloads
    threading.Thread(target=_download_top100_art, daemon=True).start()


def _download_top100_art():
    """Downloads artwork for each top-100 track and stores decoded surfaces."""
    import io
    for t in top100_tracks:
        rank = t["rank"]
        if rank in top100_art_cache:
            continue
        url = t.get("art_url", "")
        if not url:
            # Wait briefly for the URL-fetch thread to populate it
            time.sleep(0.05)
            url = t.get("art_url", "")
        if not url:
            continue
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "SpotMFi/1.0"})
            with urllib.request.urlopen(req, timeout=10) as r:
                img_bytes = r.read()
            buf = io.BytesIO(img_bytes)
            surf = pygame.image.load(buf)
            surf = pygame.transform.smoothscale(surf, (56, 56))
            top100_art_cache[rank] = surf
        except Exception:
            top100_art_cache[rank] = None  # mark as attempted so we don't retry


def start_top100_fetch():
    global top100_loading, top100_error, top100_tracks, top100_thread
    global top100_scroll_offset, target_top100_scroll, top100_art_cache
    top100_loading       = True
    top100_error         = ""
    top100_tracks        = []
    top100_art_cache     = {}
    top100_scroll_offset = 0.0
    target_top100_scroll = 0.0
    top100_thread = threading.Thread(target=_fetch_top100_worker, daemon=True)
    top100_thread.start()


def _fetch_sotd_cover():
    """Fetch cover art for today's Song of the Day pick from iTunes."""
    global sotd_cover_surface, sotd_cover_loading
    import io
    try:
        _, entry = _pick_daily_entry(SOTD_ENTRIES)
        params = urllib.parse.urlencode({
            "term": entry["search"],
            "entity": "song", "media": "music", "limit": 1
        })
        req = urllib.request.Request(
            f"https://itunes.apple.com/search?{params}",
            headers={"User-Agent": "SpotMFi/1.0"})
        with urllib.request.urlopen(req, timeout=10) as r:
            data = json.loads(r.read().decode("utf-8"))
        results = data.get("results", [])
        if results:
            art_url = results[0].get("artworkUrl100", "").replace("100x100bb", "600x600bb")
            if art_url:
                req2 = urllib.request.Request(art_url, headers={"User-Agent": "SpotMFi/1.0"})
                with urllib.request.urlopen(req2, timeout=12) as r2:
                    img_bytes = r2.read()
                surf = pygame.image.load(io.BytesIO(img_bytes))
                sotd_cover_surface = surf
    except Exception:
        pass
    finally:
        sotd_cover_loading = False


def _fetch_aotd_cover():
    """Fetch representative artwork for today's Artist of the Day pick from iTunes."""
    global aotd_cover_surface, aotd_cover_loading
    import io
    try:
        _, entry = _pick_daily_entry(AOTD_ENTRIES)
        params = urllib.parse.urlencode({
            "term": entry["search"],
            "entity": "album", "media": "music", "limit": 1
        })
        req = urllib.request.Request(
            f"https://itunes.apple.com/search?{params}",
            headers={"User-Agent": "SpotMFi/1.0"})
        with urllib.request.urlopen(req, timeout=10) as r:
            data = json.loads(r.read().decode("utf-8"))
        results = data.get("results", [])
        if results:
            art_url = results[0].get("artworkUrl100", "").replace("100x100bb", "600x600bb")
            if art_url:
                req2 = urllib.request.Request(art_url, headers={"User-Agent": "SpotMFi/1.0"})
                with urllib.request.urlopen(req2, timeout=12) as r2:
                    img_bytes = r2.read()
                surf = pygame.image.load(io.BytesIO(img_bytes))
                aotd_cover_surface = surf
    except Exception:
        pass
    finally:
        aotd_cover_loading = False


def _fetch_hm_cover():
    """Fetch representative artwork for today's History Maker entry from iTunes."""
    global hm_cover_surface, hm_cover_loading
    import io
    try:
        _, entry = _pick_daily_entry(HM_ENTRIES)
        params = urllib.parse.urlencode({
            "term": entry["search"],
            "entity": "album", "media": "music", "limit": 1
        })
        req = urllib.request.Request(
            f"https://itunes.apple.com/search?{params}",
            headers={"User-Agent": "SpotMFi/1.0"})
        with urllib.request.urlopen(req, timeout=10) as r:
            data = json.loads(r.read().decode("utf-8"))
        results = data.get("results", [])
        if results:
            art_url = results[0].get("artworkUrl100", "").replace("100x100bb", "600x600bb")
            if art_url:
                req2 = urllib.request.Request(art_url, headers={"User-Agent": "SpotMFi/1.0"})
                with urllib.request.urlopen(req2, timeout=12) as r2:
                    img_bytes = r2.read()
                surf = pygame.image.load(io.BytesIO(img_bytes))
                hm_cover_surface = surf
    except Exception:
        pass
    finally:
        hm_cover_loading = False


def _get_stats(path):
    """Return the listen_stats entry for path, creating it with zero values if missing."""
    if path not in listen_stats:
        listen_stats[path] = {
            "play_count":             0,      # times playback started
            "total_seconds_listened": 0.0,    # cumulative real seconds of active play
            "completed_count":        0,      # times listened past 80% of duration
            "skip_count":             0,      # times skipped before 80%
            "last_played_timestamp":  None,   # ISO-8601 string of most recent play start
            "session_count":          0,      # distinct listening sessions (play → pause/stop cycles)
        }
    return listen_stats[path]

def _flush_listen_session(path, completed=False, skipped=False):
    """Flush elapsed real-play seconds from the current session into stats, then clear it."""
    global _listen_session_start
    if path and _listen_session_start is not None:
        delta = time.time() - _listen_session_start
        if delta > 0.5:   # ignore sub-half-second blips
            s = _get_stats(path)
            s["total_seconds_listened"] += delta
            s["session_count"]          += 1
            if completed:
                s["completed_count"] += 1
            if skipped:
                s["skip_count"] += 1
    _listen_session_start = None

def _start_listen_session(path):
    """Record that a track has started playing: increment play count and note timestamp."""
    global _listen_session_start
    import datetime
    s = _get_stats(path)
    s["play_count"] += 1
    s["last_played_timestamp"] = datetime.datetime.now().isoformat(timespec="seconds")
    _listen_session_start = time.time()


def _json_safe_track(t):
    """Return a copy of a track dict with runtime-only, non-JSON-serializable
    fields stripped out (currently just "cover_surface", a pygame.Surface).

    Track dicts get a live "cover_surface" attached in-memory whenever art is
    applied (from the iTunes search, from a local file, or from embedded
    ID3/FLAC/MP4 tags) so they render immediately without a reload. That same
    dict object is what liked_tracks / custom_playlists store, so saving them
    as-is means the Surface goes straight into json.dump(), which doesn't
    know how to serialize it. That raised a TypeError partway through writing
    the file - after it was already truncated open in "w" mode - leaving a
    corrupt, half-written data file on disk. The next load would then fail to
    parse it and silently reset the whole library (saved folders, liked
    songs, playlists) to empty, even though nothing looked wrong at the time
    the art was applied. Stripping the surface here (the actual pixels are
    still safe on disk via "image_path"/track_covers) avoids that entirely.
    """
    if "cover_surface" in t:
        t = {k: v for k, v in t.items() if k != "cover_surface"}
    return t


def save_app_data():
    data = {
        "saved_directories": saved_directories,
        "liked_tracks": [_json_safe_track(t) for t in liked_tracks],
        "liked_songs_custom_cover": {"image_path": liked_songs_custom_cover.get("image_path")},
        "custom_playlists": {},
        "song_lyrics_database": song_lyrics_database,
        "green_toggled_tracks": list(green_toggled_tracks),
        "layout_mode": layout_mode,
        "grid_cols_override": grid_cols_override,
        "current_theme": current_theme,
        "current_font_family": current_font_family,
        "font_scale": font_scale,
        "haptics_enabled": haptics_enabled,
        "current_language": current_language,
        "track_covers": {p: {"image_path": v.get("image_path")} for p, v in track_covers.items()},
        "listen_stats": listen_stats,
        "onboarding_complete": onboarding_complete,
        "auto_scrape_media": auto_scrape_media,
    }
    
    for p_name, p_data in custom_playlists.items():
        data["custom_playlists"][p_name] = {
            "tracks": [_json_safe_track(t) for t in p_data["tracks"]],
            "image_path": p_data["image_path"],
            "description": p_data["description"]
        }
        
    try:
        with open(DATA_FILE, "w") as f:
            json.dump(data, f, indent=4)
    except Exception as e:
        print(f"File Save Error: {e}")

def load_app_data():
    global saved_directories, liked_tracks
    global song_lyrics_database, green_toggled_tracks, layout_mode, track_covers
    global grid_cols_override, listen_stats
    global onboarding_complete, onboarding_stage, auto_scrape_media
    global font_scale, haptics_enabled
    
    if not os.path.exists(DATA_FILE):
        layout_mode = detect_device_layout_mode()
        return
        
    try:
        with open(DATA_FILE, "r") as f:
            data = json.load(f)
            
        saved_directories = data.get("saved_directories", [])
        liked_tracks = data.get("liked_tracks", [])
        layout_mode = data.get("layout_mode", detect_device_layout_mode())
        grid_cols_override = data.get("grid_cols_override", None)
        apply_theme(data.get("current_theme", "classic"))
        font_scale = data.get("font_scale", 1.0)
        haptics_enabled = data.get("haptics_enabled", True if IS_ANDROID else False)
        apply_font(data.get("current_font_family", "classic"))
        apply_language(data.get("current_language", "English"))
        
        lsc = data.get("liked_songs_custom_cover", {})
        liked_songs_custom_cover["image_path"] = lsc.get("image_path")
        if liked_songs_custom_cover["image_path"] and os.path.exists(liked_songs_custom_cover["image_path"]):
            try:
                with open(liked_songs_custom_cover["image_path"], "rb") as _f:
                    raw_img = _decode_image_bytes_safely(_f.read())
                raw_img = raw_img.convert()
                liked_songs_custom_cover["surface"] = pygame.transform.smoothscale(raw_img, (130, 110))
            except:
                pass
                
        song_lyrics_database = data.get("song_lyrics_database", {})
        green_toggled_tracks = set(data.get("green_toggled_tracks", []))
        listen_stats = data.get("listen_stats", {})
        onboarding_complete = data.get("onboarding_complete", False)
        onboarding_stage = None if onboarding_complete else "welcome"
        auto_scrape_media = data.get("auto_scrape_media", None)
        
        loaded_track_covers = data.get("track_covers", {})
        track_covers = {}
        for t_path, t_cover in loaded_track_covers.items():
            img_path = t_cover.get("image_path")
            if img_path and os.path.exists(img_path):
                try:
                    with open(img_path, "rb") as _f:
                        raw_img = _decode_image_bytes_safely(_f.read())
                    raw_img = raw_img.convert()
                    cover_surf = pygame.transform.smoothscale(raw_img, (130, 130))
                    track_covers[t_path] = {"image_path": img_path, "surface": cover_surf}
                except:
                    pass
        
        loaded_playlists = data.get("custom_playlists", {})
        for p_name, p_data in loaded_playlists.items():
            surface = None
            if p_data.get("image_path") and os.path.exists(p_data["image_path"]):
                try:
                    with open(p_data["image_path"], "rb") as _f:
                        raw_img = _decode_image_bytes_safely(_f.read())
                    raw_img = raw_img.convert()
                    surface = pygame.transform.smoothscale(raw_img, (130, 110))
                except:
                    pass
            playlist_tracks = p_data.get("tracks", [])
            for t in playlist_tracks:
                if t.get("path") in track_covers:
                    t["cover_surface"] = track_covers[t["path"]]["surface"]
            custom_playlists[p_name] = {
                "tracks": playlist_tracks,
                "image_path": p_data.get("image_path"),
                "description": p_data.get("description", ""),
                "surface": surface
            }
            
        for t in liked_tracks:
            if t.get("path") in track_covers:
                t["cover_surface"] = track_covers[t["path"]]["surface"]
            
        rebuild_imported_tracks()

        # Backfill embedded metadata covers (extracted during rebuild_imported_tracks)
        # onto liked_tracks / custom_playlists tracks that don't already have a custom cover
        embedded_cover_lookup = {t["path"]: t["cover_surface"] for t in imported_tracks if t.get("cover_surface")}
        for t in liked_tracks:
            if not t.get("cover_surface") and t.get("path") in embedded_cover_lookup:
                t["cover_surface"] = embedded_cover_lookup[t["path"]]
        for p_data in custom_playlists.values():
            for t in p_data["tracks"]:
                if not t.get("cover_surface") and t.get("path") in embedded_cover_lookup:
                    t["cover_surface"] = embedded_cover_lookup[t["path"]]
    except Exception as e:
        print(f"File Load Error: {e}")

def advance_track(backward=False):
    global current_track, is_playing
    if playlist_is_playing == "Liked Songs":
        playlist = liked_tracks
    elif playlist_is_playing in custom_playlists:
        playlist = custom_playlists[playlist_is_playing]["tracks"]
    else:
        playlist = imported_tracks
        
    if not playlist:
        return
    
    current_index = -1
    for i, track in enumerate(playlist):
        if track["path"] == current_track["path"]:
            current_index = i
            break
            
    if current_index != -1:
        if is_shuffle and len(playlist) > 1:
            next_index = current_index
            while next_index == current_index:
                next_index = random.randint(0, len(playlist) - 1)
        else:
            if backward:
                next_index = (current_index - 1) % len(playlist)
            else:
                next_index = (current_index + 1) % len(playlist)
                
        current_track = playlist[next_index]
        green_toggled_tracks.add(current_track["path"])
        is_playing = True
        load_and_play_track(current_track["path"])

def load_and_play_track(track_path):
    global track_duration, track_start_accumulator, TEMP_WAV_PATH, current_backend, music_loaded

    # Flush listening time for whatever was playing before
    prev_path = current_track.get("path", "")
    if prev_path:
        elapsed_ratio = (track_start_accumulator / track_duration) if track_duration > 0 else 0
        _flush_listen_session(prev_path, completed=False, skipped=elapsed_ratio < 0.8)
    
    music_loaded = False
    try: 
        pygame.mixer.music.stop()
        pygame.mixer.music.unload() 
    except: pass
    
    if HAS_ANDROID_MEDIA and android_media_player:
        try: android_media_player.reset()
        except: pass

    if TEMP_WAV_PATH and os.path.exists(TEMP_WAV_PATH):
        try: os.remove(TEMP_WAV_PATH)
        except: pass
        TEMP_WAV_PATH = None

    track_start_accumulator = 0.0
    is_mp4 = track_path.lower().endswith(('.mp4', '.m4a', '.aac', '.alac', '.dsf', '.dff'))

    if is_mp4 and HAS_ANDROID_MEDIA and android_media_player:
        current_backend = "android"
        try:
            android_media_player.setDataSource(track_path)
            android_media_player.prepare()
            track_duration = android_media_player.getDuration() / 1000.0
            android_media_player.start()
            music_loaded = True
            _start_listen_session(track_path)
        except Exception as e:
            print(f"Android Native Decoder Error: {e}")
            music_loaded = False
    else:
        current_backend = "pygame"
        play_path = track_path
        duration = 0.0 

        if not is_mp4:
            try:
                snd_probe = pygame.mixer.Sound(track_path)
                duration = snd_probe.get_length()
            except:
                try:
                    from mutagen.mp3 import MP3
                    audio = MP3(track_path)
                    duration = audio.info.length
                except:
                    try:
                        from mutagen.oggvorbis import OggVorbis
                        audio = OggVorbis(track_path)
                        duration = audio.info.length
                    except:
                        try:
                            from mutagen.flac import FLAC
                            audio = FLAC(track_path)
                            duration = audio.info.length
                        except:
                            duration = 180.0
        else:
            try:
                from moviepy.editor import AudioFileClip
                clip = AudioFileClip(track_path)
                duration = clip.duration
                TEMP_WAV_PATH = os.path.join(tempfile.gettempdir(), "spotify_fi_temp.wav")
                clip.write_audiofile(TEMP_WAV_PATH, logger=None)
                clip.close()
                play_path = TEMP_WAV_PATH
            except:
                try:
                    from pydub import AudioSegment
                    sound = AudioSegment.from_file(track_path)
                    duration = len(sound) / 1000.0
                    TEMP_WAV_PATH = os.path.join(tempfile.gettempdir(), "spotify_fi_temp.wav")
                    sound.export(TEMP_WAV_PATH, format="wav")
                    play_path = TEMP_WAV_PATH
                except: pass

        track_duration = duration
        try:
            pygame.mixer.music.load(play_path)
            pygame.mixer.music.play(start=0.0)
            music_loaded = True
            current_track["_play_start_time"] = time.time()
            current_track["_has_started"] = False
            _start_listen_session(track_path)
        except Exception as e:
            print(f"Playback engine error: {e}")
            music_loaded = False

def update_browser_contents():
    global browser_items, search_message, browser_scroll_offset, target_browser_scroll
    browser_items = []
    browser_scroll_offset = 0
    target_browser_scroll = 0.0
    
    if current_browser_path != ROOT_PATH and current_browser_path != "/":
        browser_items.append({"name": "[.. Go Back to Previous Folder]", "is_dir": True, "path": os.path.dirname(current_browser_path)})
        
    try:
        for item in sorted(os.listdir(current_browser_path)):
            full_path = os.path.join(current_browser_path, item)
            is_dir = os.path.isdir(full_path)
            if is_browsing_for_cover and not is_dir:
                if browsing_cover_target == "lyrics_import" and not item.lower().endswith(('.txt', '.lrc')):
                    continue
                elif browsing_cover_target != "lyrics_import" and not item.lower().endswith(('.png', '.jpg', '.jpeg')):
                    continue
            browser_items.append({"name": item, "is_dir": is_dir, "path": full_path})
    except Exception:
        search_message = t("Access Denied: Restricted system folder or permission missing.")

def extract_embedded_cover(track_path):
    """Attempts to read embedded album art from a music file's metadata (ID3 APIC for MP3,
    FLAC pictures, M4A covr atom). Returns a pygame Surface scaled to (130, 130), or None
    if the file has no embedded artwork or can't be read."""
    art_bytes = None
    try:
        lower_path = track_path.lower()
        if lower_path.endswith('.mp3'):
            from mutagen.id3 import ID3
            tags = ID3(track_path)
            for tag_key in tags.keys():
                if tag_key.startswith('APIC'):
                    art_bytes = tags[tag_key].data
                    break
        elif lower_path.endswith('.flac'):
            from mutagen.flac import FLAC
            audio = FLAC(track_path)
            if audio.pictures:
                art_bytes = audio.pictures[0].data
        elif lower_path.endswith(('.m4a', '.mp4', '.alac')):
            from mutagen.mp4 import MP4
            audio = MP4(track_path)
            covr = audio.tags.get('covr') if audio.tags else None
            if covr:
                art_bytes = bytes(covr[0])
        elif lower_path.endswith('.ogg'):
            from mutagen.oggvorbis import OggVorbis
            from mutagen.flac import Picture
            import base64
            audio = OggVorbis(track_path)
            pics = audio.get('metadata_block_picture', [])
            if pics:
                pic = Picture(base64.b64decode(pics[0]))
                art_bytes = pic.data
    except Exception:
        art_bytes = None

    if not art_bytes:
        return None

    import io
    try:
        art_surface = pygame.image.load(io.BytesIO(art_bytes))
        return pygame.transform.smoothscale(art_surface, (130, 130))
    except Exception:
        pass

    # Fallback: pygame's built-in loader can lack full JPEG support on some Android/Pydroid
    # builds. Most embedded album art is JPEG, so decode via Pillow and hand pygame raw
    # RGB pixel data instead, which sidesteps pygame's own JPEG decoder entirely.
    try:
        from PIL import Image
        pil_img = Image.open(io.BytesIO(art_bytes)).convert("RGB")
        art_surface = pygame.image.fromstring(pil_img.tobytes(), pil_img.size, "RGB")
        return pygame.transform.smoothscale(art_surface, (130, 130))
    except Exception:
        return None

def rebuild_imported_tracks():
    global imported_tracks, search_message
    imported_tracks = []
    track_counter = 1
    new_songs_found = 0
    
    for directory in saved_directories:
        try:
            for file in os.listdir(directory):
                if file.lower().endswith(('.mp3', '.mp4', '.m4a', '.wav', '.ogg', '.flac', '.mpe', '.mpeg', '.aac', '.alac', '.dsf', '.dff')):
                    clean_title = os.path.splitext(file)[0]
                    
                    if len(clean_title) > 18:
                        display_title = clean_title[:15] + "..."
                    else:
                        display_title = clean_title
                        
                    track_data = {
                        "num": str(track_counter),
                        "title": display_title,
                        "raw_title": clean_title, 
                        "artist": "Local File",
                        "album": os.path.basename(directory) if os.path.basename(directory) else "Storage",
                        "duration": "Media",
                        "path": os.path.join(directory, file) 
                    }
                    full_track_path = track_data["path"]
                    if full_track_path in track_covers and track_covers[full_track_path].get("surface"):
                        track_data["cover_surface"] = track_covers[full_track_path]["surface"]
                    else:
                        embedded_cover = extract_embedded_cover(full_track_path)
                        if embedded_cover:
                            track_data["cover_surface"] = embedded_cover
                    imported_tracks.append(track_data)
                    track_counter += 1
                    new_songs_found += 1
        except Exception:
            continue
    if saved_directories:
        search_message = f"Scanned folders! Found {new_songs_found} media files in layout index."
    else:
        search_message = t("Tap '+ Add Folder' to open the built-in storage browser.")

def scan_confirmed_directory(target_dir):
    global music_grid_scroll_offset, target_music_scroll, is_browsing_storage, is_browsing_for_cover
    if is_browsing_for_cover:
        is_browsing_for_cover = False
        return
        
    if target_dir not in saved_directories:
        saved_directories.append(target_dir)
    music_grid_scroll_offset = 0.0
    target_music_scroll = 0.0
    rebuild_imported_tracks()
    is_browsing_storage = False  
    save_app_data() 
    
def get_virtual_mouse_pos(real_pos=None):
    # real_pos lets a caller pass the exact position carried by a specific event
    # (event.pos) instead of falling back to pygame.mouse.get_pos(). On some
    # Android/SDL2 builds the internally-tracked cursor position queried via
    # get_pos() can drift slightly from the position an actual touch event
    # carried, which showed up as every tap needing to land above the button
    # it was meant to hit. Passing the event's own pos avoids that mismatch.
    #
    # On top of that: if a real touch was just seen (_last_touch_norm, set from
    # FINGERDOWN/FINGERMOTION/FINGERUP's own normalized [0,1] coordinates),
    # prefer computing straight from that instead of any pixel-space position at
    # all. SDL synthesizes MOUSEBUTTONDOWN/UP's pixel event.pos from the same
    # touch using SDL's own internally-tracked window size - if that internal
    # size is stale, the synthesized pixel position is wrong in a way neither
    # get_pos() nor event.pos can recover from. Normalized touch coordinates
    # aren't derived from any window-size assumption, so they can't drift.
    if _last_touch_norm is not None:
        nx, ny = _last_touch_norm
        virtual_x = int(nx * WIDTH)
        virtual_y = int(ny * HEIGHT)
        return (virtual_x, virtual_y)
    real_x, real_y = real_pos if real_pos is not None else pygame.mouse.get_pos()
    scale_x = REAL_WIDTH / WIDTH
    scale_y = REAL_HEIGHT / HEIGHT
    virtual_x = int(real_x / scale_x)
    virtual_y = int(real_y / scale_y)
    return (virtual_x, virtual_y)


def draw_manual_thumbs_up(surface, x, y, w, h, color):
    pygame.draw.rect(surface, color, (x, y + h * 0.5, w * 0.22, h * 0.4), border_radius=max(1, int(w * 0.04)))
    pygame.draw.rect(surface, color, (x + w * 0.28, y + h * 0.35, w * 0.62, h * 0.55), border_radius=max(1, int(w * 0.06)))
    pygame.draw.rect(surface, color, (x + w * 0.28, y, w * 0.25, h * 0.45), border_radius=max(1, int(w * 0.06)))

def draw_piece_of_paper_icon(surface, rect, color):
    x, y, w, h = rect.x, rect.y, rect.width, rect.height
    px = x + 5
    py = y + 4
    pw = w - 10
    ph = h - 8
    
    pygame.draw.rect(surface, color, (px, py, pw, ph), width=2)
    pygame.draw.line(surface, color, (px + 4, py + 4), (px + pw - 4, py + 4), 2)
    pygame.draw.line(surface, color, (px + 4, py + 9), (px + pw - 4, py + 9), 2)
    pygame.draw.line(surface, color, (px + 4, py + 14), (px + pw - 4, py + 14), 2)

def draw_picture_frame_icon(surface, rect, color):
    x, y, w, h = rect.x, rect.y, rect.width, rect.height
    px = x + 4
    py = y + 4
    pw = w - 8
    ph = h - 8
    pygame.draw.rect(surface, color, (px, py, pw, ph), width=2, border_radius=2)
    # small "mountain" glyph to suggest an image
    pygame.draw.circle(surface, color, (px + 6, py + 6), 2)
    pygame.draw.lines(surface, color, False, [
        (px + 2, py + ph - 4),
        (px + pw * 0.4, py + ph * 0.45),
        (px + pw * 0.62, py + ph * 0.68),
        (px + pw * 0.78, py + ph * 0.42),
        (px + pw - 2, py + ph - 4)
    ], 2)

def draw_spotify_shuffle_icon(surface, rect, color):
    cx, cy = rect.centerx, rect.centery
    w, h = 16, 12
    x_left = cx - w // 2
    x_right = cx + w // 2
    y_top = cy - h // 2
    y_bottom = cy + h // 2
    
    pygame.draw.line(surface, color, (x_left, y_top), (cx - 2, y_top), 2)
    pygame.draw.line(surface, color, (cx - 2, y_top), (cx + 2, y_bottom), 2)
    pygame.draw.line(surface, color, (cx + 2, y_bottom), (x_right, y_bottom), 2)
    
    pygame.draw.line(surface, color, (x_left, y_bottom), (cx - 2, y_bottom), 2)
    pygame.draw.line(surface, color, (cx - 2, y_bottom), (cx + 2, y_top), 2)
    pygame.draw.line(surface, color, (cx + 2, y_top), (x_right, y_top), 2)
    
    pygame.draw.polygon(surface, color, [(x_right, y_top - 3), (x_right + 4, y_top), (x_right, y_top + 3)])
    pygame.draw.polygon(surface, color, [(x_right, y_bottom - 3), (x_right + 4, y_bottom), (x_right, y_bottom + 3)])

def draw_solid_cog_wheel(surface, x, y, w, h, color):
    cx, cy = x + w // 2, y + h // 2
    r_out = min(w, h) // 2
    
    pygame.draw.circle(surface, color, (cx, cy), int(r_out * 0.85))
    num_teeth = 8
    for i in range(num_teeth):
        angle = i * (2 * math.pi / num_teeth)
        tx = int(cx + r_out * math.cos(angle))
        ty = int(cy + r_out * math.sin(angle))
        pygame.draw.line(surface, color, (cx, cy), (tx, ty), width=int(r_out * 0.45))
        
    pygame.draw.circle(surface, COLOR_BLACK, (cx, cy), int(r_out * 0.25))

def draw_spotify_pencil(surface, cx, cy, color):
    pencil_surf = pygame.Surface((40, 40), pygame.SRCALPHA)
    pygame.draw.rect(pencil_surf, color, (12, 8, 8, 22))
    pygame.draw.polygon(pencil_surf, color, [(12, 30), (20, 30), (16, 36)])
    pygame.draw.rect(pencil_surf, COLOR_BLACK, (12, 5, 8, 3))
    
    rotated_surf = pygame.transform.rotate(pencil_surf, 45)
    new_rect = rotated_surf.get_rect(center=(cx, cy))
    surface.blit(rotated_surf, new_rect.topleft)

def draw_search_icon(surface, cx, cy, size, color):
    pygame.draw.circle(surface, color, (int(cx - size*0.1), int(cy - size*0.1)), int(size*0.3), width=2)
    pygame.draw.line(surface, color, (cx + size*0.1, cy + size*0.1), (cx + size*0.4, cy + size*0.4), width=3)

def draw_library_icon(surface, cx, cy, size, color):
    w = max(2, int(size * 0.15))
    h = int(size * 0.6)
    pygame.draw.rect(surface, color, (cx - size*0.4, cy - h//2, w, h), border_radius=1)
    pygame.draw.rect(surface, color, (cx - size*0.1, cy - h//2, w, h), border_radius=1)
    
    book_surf = pygame.Surface((w, h), pygame.SRCALPHA)
    pygame.draw.rect(book_surf, color, (0, 0, w, h), border_radius=1)
    rotated_book = pygame.transform.rotate(book_surf, -20)
    rect = rotated_book.get_rect(center=(cx + size*0.25, cy))
    surface.blit(rotated_book, rect.topleft)

def get_wrapped_lines(text, font, max_width):
    words = text.split(' ')
    lines = []
    current_line = ""
    
    for word in words:
        if font.size(word)[0] > max_width:
            if current_line:
                lines.append(current_line)
                current_line = ""
            for char in word:
                test_line = current_line + char
                if font.size(test_line)[0] <= max_width:
                    current_line = test_line
                else:
                    lines.append(current_line)
                    current_line = char
        else:
            test_line = current_line + " " + word if current_line else word
            if font.size(test_line)[0] <= max_width:
                current_line = test_line
            else:
                if current_line:
                    lines.append(current_line)
                current_line = word
                
    if current_line:
        lines.append(current_line)
    return lines

def draw_unified_cover_overlay(surface, rect, mouse_pos):
    if rect.collidepoint(mouse_pos):
        overlay_height = 32
        overlay_surf = pygame.Surface((rect.width, overlay_height), pygame.SRCALPHA)
        overlay_surf.fill((0, 0, 0, 180))
        
        hint_surf = _cached_render(font_small, t("Choose Cover Image"), True, COLOR_WHITE)
        tx = (rect.width - hint_surf.get_width()) // 2
        ty = (overlay_height - hint_surf.get_height()) // 2
        overlay_surf.blit(hint_surf, (tx, ty))
        surface.blit(overlay_surf, (rect.x, rect.bottom - overlay_height))

# --- SCALED-COVER CACHE ---
# Several places below re-run pygame.transform.smoothscale() on the exact
# same cover-art Surface at the exact same target size on EVERY frame (once
# per visible grid card/row), even though neither the source image nor the
# target size changes between frames while just sitting there or scrolling.
# smoothscale is a real per-pixel bilinear resample, so redoing it for every
# visible card every single frame was a large, entirely avoidable chunk of
# per-frame cost - this was the main reason framerate was so low even though
# nothing on screen was actually changing frame to frame.
# Keyed on (surface object, size): pygame.Surface uses default identity-based
# hashing/equality (no custom __eq__), so a cache hit only ever happens for
# the literal same image object at the literal same size. If a cover is
# later replaced with a new Surface (e.g. user changes a playlist's cover),
# that's simply a different object -> automatic cache miss -> scaled fresh,
# same as before. Holding the surface as a dict key also keeps it alive for
# as long as it's cached, so there's no risk of a stale/incorrect hit.
_scale_cache = {}
def _cached_scale(surf, size):
    key = (surf, size)
    out = _scale_cache.get(key)
    if out is None:
        out = pygame.transform.smoothscale(surf, size)
        _scale_cache[key] = out
    return out

# --- RENDERED-TEXT CACHE ---
# Same idea as the cover-scale cache above, applied to text: font.render()
# does real per-glyph antialiased rasterization, and it was being re-run for
# every visible label on every single frame - track titles/artists, rank
# numbers, playlist names, buttons - even though the same font+text+color
# produces the exact same bitmap every time until the underlying data
# actually changes. That per-frame re-rendering of dozens of labels (times
# every visible row in a scrolling list) was a large remaining chunk of
# per-frame cost. Keyed on (font object, text, antialias flag, color) with
# the same identity-based-key reasoning as _cached_scale above: a cache hit
# only happens for the literal same request, so genuinely new/changed text
# (search-as-you-type, live counters, etc.) simply misses and renders fresh,
# identical to before.
_text_cache = {}
def _cached_render(font, text, antialias, color):
    key = (font, text, antialias, color)
    out = _text_cache.get(key)
    if out is None:
        out = font.render(text, antialias, color)
        _text_cache[key] = out
    return out

# --- MASKED-COVER CACHE ---
# The album-grid cards round the corners of each cover by cropping it to
# the box size and applying a rounded-rect alpha mask (BLEND_RGBA_MIN).
# That mask draw uses pygame's anti-aliased border_radius rect, which is a
# real per-pixel software rasterization - not GPU/hardware accelerated -
# and it (plus the crop blit and the full-surface blend) was being redone
# from scratch for every visible card on every single frame, even though
# neither the source cover nor the card size changes frame to frame while
# just sitting there or scrolling. That made this the single largest
# remaining per-frame cost on the main library/grid view - the one screen
# most people are looking at most of the time - which is exactly why FPS
# stayed low regardless of device: the work itself, not the device's
# available power, was the bottleneck. Same identity-based-key caching
# approach as _cached_scale/_cached_render above: keyed on the literal
# source Surface object plus the target box size, so a genuinely new/
# resized/replaced cover is simply a cache miss and gets rebuilt fresh.
_masked_cover_cache = {}
def _cached_masked_cover(src_surf, box_w, box_h):
    key = (src_surf, box_w, box_h)
    out = _masked_cover_cache.get(key)
    if out is None:
        src_w, src_h = src_surf.get_size()
        scale_factor = max(box_w / src_w, box_h / src_h)
        fit_w, fit_h = max(1, round(src_w * scale_factor)), max(1, round(src_h * scale_factor))
        scaled_cover = _cached_scale(src_surf, (fit_w, fit_h))
        crop_x = (fit_w - box_w) // 2
        crop_y = (fit_h - box_h) // 2
        cropped_cover = pygame.Surface((box_w, box_h), pygame.SRCALPHA)
        cropped_cover.blit(scaled_cover, (-crop_x, -crop_y))
        mask_surf = pygame.Surface((box_w, box_h), pygame.SRCALPHA)
        pygame.draw.rect(mask_surf, (255, 255, 255), mask_surf.get_rect(), border_radius=6)
        cropped_cover.blit(mask_surf, (0, 0), special_flags=pygame.BLEND_RGBA_MIN)
        out = cropped_cover
        _masked_cover_cache[key] = out
    return out

# --- ROUNDED-RECT SURFACE CACHE ---
# Same reasoning as the caches above: pygame's border_radius rect fill runs
# a real anti-aliased software rasterization, and the album-grid cards were
# redrawing TWO of these per visible card every single frame - the card's
# own background, and a placeholder box behind the cover art - even though
# each only ever takes one of a small, fixed set of (color, size) shapes.
# Caching the finished rounded-rect as a Surface and blitting it (a cheap
# straight pixel copy) instead of re-rasterizing it live cuts that cost to
# effectively zero after the first frame. Keyed on the literal color/size/
# radius/outline-width, so a theme change (which reassigns the COLOR_*
# globals to new color tuples) or a resize simply produces a new key and a
# fresh cache entry, exactly like the other caches here.
_rounded_rect_cache = {}
def _cached_rounded_rect(color, w, h, radius, width=0):
    key = (color, w, h, radius, width)
    surf = _rounded_rect_cache.get(key)
    if surf is None:
        surf = pygame.Surface((w, h), pygame.SRCALPHA)
        pygame.draw.rect(surf, color, surf.get_rect(), width=width, border_radius=radius)
        _rounded_rect_cache[key] = surf
    return surf

def draw_sidebar():
    global sidebar_rects
    sidebar_rects = [] 
    
    if not is_portrait:
        sidebar_rect = pygame.Rect(0, 0, 230, HEIGHT)
        pygame.draw.rect(virtual_surface, COLOR_DARK_GREY, sidebar_rect)
        
        logo_text = _cached_render(font_title, "SpotM-Fi", True, COLOR_SPOTIFY_GREEN)
        virtual_surface.blit(logo_text, (20, 30))
        
        y_offset = 90
        mouse_pos = get_virtual_mouse_pos()
        
        for item in sidebar_items:
            item_rect = pygame.Rect(10, y_offset - 5, 210, 35)
            sidebar_rects.append((item_rect, item))
            
            is_hovered = item_rect.collidepoint(mouse_pos)
            is_clicked = is_hovered and mouse_held
            
            if is_clicked:
                pygame.draw.rect(virtual_surface, (60, 60, 60), item_rect, border_radius=5)
                text_color = COLOR_SPOTIFY_GREEN
            elif is_hovered or (current_page == item and not is_browsing_storage and not viewing_liked_playlist and not viewing_settings_page and not selected_custom_playlist_name and not show_create_playlist_modal and not show_add_to_playlist_modal):
                pygame.draw.rect(virtual_surface, COLOR_HOVER, item_rect, border_radius=5)
                text_color = COLOR_WHITE
            else:
                text_color = COLOR_TEXT_MUTED
                
            text_surf = render_fit_text(t(item), text_color, item_rect.width - 15, base_size=16, bold=True)
            virtual_surface.blit(text_surf, (25, y_offset))
            y_offset += 40
    else:
        _is_phone_tabs = layout_mode == "phone"
        sidebar_height = 80 if _is_phone_tabs else 65
        sidebar_rect = pygame.Rect(0, HEIGHT - sidebar_height, WIDTH, sidebar_height)
        pygame.draw.rect(virtual_surface, COLOR_DARK_GREY, sidebar_rect)
        
        mouse_pos = get_virtual_mouse_pos()
        item_width = WIDTH // len(sidebar_items)
        
        for i, item in enumerate(sidebar_items):
            item_rect = pygame.Rect(i * item_width, sidebar_rect.y, item_width, sidebar_height)
            sidebar_rects.append((item_rect, item))
            
            is_hovered = item_rect.collidepoint(mouse_pos)
            is_clicked = is_hovered and mouse_held
            
            if is_clicked:
                text_color = COLOR_SPOTIFY_GREEN
            elif is_hovered or (current_page == item and not is_browsing_storage and not viewing_liked_playlist and not viewing_settings_page and not selected_custom_playlist_name and not show_create_playlist_modal and not show_add_to_playlist_modal):
                text_color = COLOR_WHITE
            else:
                text_color = COLOR_TEXT_MUTED
                
            cx = item_rect.centerx
            cy = item_rect.y + (26 if _is_phone_tabs else 22)
            icon_size = 30 if _is_phone_tabs else 24
            
            if item == "Search":
                draw_search_icon(virtual_surface, cx, cy, icon_size, text_color)
            elif item == "Your Library":
                draw_library_icon(virtual_surface, cx, cy, icon_size, text_color)
            elif item == "Settings":
                draw_solid_cog_wheel(virtual_surface, cx-(15 if _is_phone_tabs else 12), cy-(15 if _is_phone_tabs else 12), icon_size, icon_size, text_color)
                
            text_surf = render_fit_text(t(item), text_color, item_rect.width - 8)
            tx = item_rect.x + (item_rect.width - text_surf.get_width()) // 2
            ty = item_rect.y + (48 if _is_phone_tabs else 40)
            virtual_surface.blit(text_surf, (tx, ty))

def draw_main_content():
    global track_rects, add_folder_btn_rect, settings_btn_rect, create_playlist_btn_rect, browser_rects, settings_dir_rects, custom_playlist_rects, select_folder_btn_rect, browser_extra_search_btn_rect, cancel_browser_btn_rect, close_settings_btn_rect, liked_songs_card_rect, playlist_play_btn_rect, playlist_random_btn_rect, playlist_cover_rect, max_music_scroll, max_browser_scroll, max_settings_scroll, marquee_offset, marquee_direction, desktop_btn_rect, phone_btn_rect, search_box_rect, top100_btn_rect, song_of_day_btn_rect, artist_of_day_btn_rect, history_maker_btn_rect, subpage_back_rect, max_btn_row_scroll, btn_row_rect, btn_row_scroll_offset, target_btn_row_scroll, grid_toggle_btn_rect, theme_btn_rect, language_btn_rect, resolution_btn_rect, font_size_btn_rect, haptics_btn_rect
    track_rects = []
    browser_rects = []
    settings_dir_rects = []
    custom_playlist_rects = []
    
    _phone = is_portrait and layout_mode == "phone"
    content_bottom_margin = (100 if _phone else (144 if is_portrait else 90)) if (current_track["title"] != "Select a song" and not show_lyrics_editor_view and not show_create_playlist_modal) else 0
    portrait_sidebar_h = (80 if (is_portrait and layout_mode == "phone") else (65 if is_portrait else 0))
    
    main_x = 0 if is_portrait else 230
    main_y = 0
    main_w = WIDTH - main_x
    main_h = HEIGHT - content_bottom_margin - portrait_sidebar_h
    content_pad_x = main_x + 30
    
    main_rect = pygame.Rect(main_x, main_y, main_w, main_h)
    pygame.draw.rect(virtual_surface, COLOR_BLACK, main_rect)
    mouse_pos = get_virtual_mouse_pos()

    if show_add_to_playlist_modal or show_lyrics_editor_view:
        return

    # --- DETAILED PLAYLIST VIEWS ---
    if (viewing_liked_playlist or selected_custom_playlist_name) and current_page == "Your Library" and not is_browsing_for_cover:
        is_custom = selected_custom_playlist_name is not None
        active_tracks = custom_playlists[selected_custom_playlist_name]["tracks"] if is_custom else liked_tracks
        p_title_text = selected_custom_playlist_name if is_custom else "Liked Songs"
        
        header_rect = pygame.Rect(main_x, 0, main_w, 200)
        pygame.draw.rect(virtual_surface, COLOR_HOVER, header_rect)
        
        playlist_cover_rect = pygame.Rect(content_pad_x, 30, 140, 140)
        
        if is_custom and custom_playlists[selected_custom_playlist_name]["surface"]:
            disp_surf = _cached_scale(custom_playlists[selected_custom_playlist_name]["surface"], (140, 140))
            virtual_surface.blit(disp_surf, (content_pad_x, 30))
        elif not is_custom and liked_songs_custom_cover["surface"]:
            disp_surf = _cached_scale(liked_songs_custom_cover["surface"], (140, 140))
            virtual_surface.blit(disp_surf, (content_pad_x, 30))
        else:
            pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, playlist_cover_rect)
            if not is_custom:
                draw_manual_thumbs_up(virtual_surface, content_pad_x + 45, 75, 50, 50, COLOR_BLACK)
            else:
                draw_spotify_pencil(virtual_surface, content_pad_x + 70, 100, COLOR_BLACK)
                
        draw_unified_cover_overlay(virtual_surface, playlist_cover_rect, mouse_pos)
        
        type_lbl = _cached_render(font_small, t("CUSTOM PLAYLIST") if is_custom else t("PUBLIC PLAYLIST"), True, COLOR_WHITE)
        playlist_title = _cached_render(font_huge, p_title_text, True, COLOR_WHITE)
        
        virtual_surface.blit(type_lbl, (content_pad_x + 160, 45))
        virtual_surface.blit(playlist_title, (content_pad_x + 160, 70))

        if is_custom:
            desc_str = custom_playlists[selected_custom_playlist_name].get("description", "")
            base_meta_str = f" • {len(active_tracks)} songs"
            
            if desc_str:
                desc_w = font_body.size(desc_str)[0]
                meta_w = font_body.size(base_meta_str)[0]
                max_allowed_w = main_w - 210 - meta_w
                
                if desc_w > max_allowed_w and max_allowed_w > 0:
                    max_scroll_range = desc_w - max_allowed_w
                    marquee_offset += marquee_direction * (40.0 * (clock.get_time() / 1000.0))

                    if marquee_offset >= max_scroll_range + 20:
                        marquee_offset = max_scroll_range + 20
                        marquee_direction = -1
                    elif marquee_offset <= -20:
                        marquee_offset = -20
                        marquee_direction = 1
                    
                    marquee_surf = pygame.Surface((max_allowed_w, 24), pygame.SRCALPHA)
                    desc_raw_surf = _cached_render(font_body, desc_str, True, COLOR_WHITE)
                    marquee_surf.blit(desc_raw_surf, (-int(marquee_offset), 0))
                    virtual_surface.blit(marquee_surf, (content_pad_x + 160, 140))
                    
                    meta_lbl = _cached_render(font_body, base_meta_str, True, COLOR_TEXT_MUTED)
                    virtual_surface.blit(meta_lbl, (content_pad_x + 160 + max_allowed_w, 140))
                else:
                    info_lbl = _cached_render(font_body, f"{desc_str}{base_meta_str}", True, COLOR_TEXT_MUTED)
                    virtual_surface.blit(info_lbl, (content_pad_x + 160, 140))
            else:
                info_lbl = _cached_render(font_body, f"Local Account{base_meta_str}", True, COLOR_TEXT_MUTED)
                virtual_surface.blit(info_lbl, (content_pad_x + 160, 140))
        else:
            info_lbl = _cached_render(font_body, f"Local Account • {len(active_tracks)} songs", True, COLOR_TEXT_MUTED)
            virtual_surface.blit(info_lbl, (content_pad_x + 160, 140))
        
        playlist_play_btn_rect = pygame.Rect(content_pad_x, 215, 50, 50)
        is_p_hovered = playlist_play_btn_rect.collidepoint(mouse_pos)
        is_p_clicked = is_p_hovered and mouse_held
        
        if is_p_clicked:
            pygame.draw.circle(virtual_surface, (20, 150, 65), (content_pad_x + 25, 240), 23)
        elif is_p_hovered:
            pygame.draw.circle(virtual_surface, (40, 230, 110), (content_pad_x + 25, 240), 26)
        else:
            pygame.draw.circle(virtual_surface, COLOR_SPOTIFY_GREEN, (content_pad_x + 25, 240), 25)
            
        if not (is_playing and playlist_is_playing == p_title_text):
            pygame.draw.polygon(virtual_surface, COLOR_BLACK, [(content_pad_x + 20, 230), (content_pad_x + 20, 250), (content_pad_x + 35, 240)])
        else:
            pygame.draw.rect(virtual_surface, COLOR_BLACK, (content_pad_x + 19, 232, 4, 16))
            pygame.draw.rect(virtual_surface, COLOR_BLACK, (content_pad_x + 27, 232, 4, 16))

        playlist_random_btn_rect = pygame.Rect(content_pad_x + 65, 222, 36, 36)
        is_pr_hovered = playlist_random_btn_rect.collidepoint(mouse_pos)
        if is_pr_hovered:
            pygame.draw.circle(virtual_surface, COLOR_HOVER, playlist_random_btn_rect.center, 18)
            
        if is_shuffle:
            shuffle_icon_color = COLOR_SPOTIFY_GREEN
        else:
            shuffle_icon_color = COLOR_WHITE if is_pr_hovered else COLOR_TEXT_MUTED
            
        draw_spotify_shuffle_icon(virtual_surface, playlist_random_btn_rect, shuffle_icon_color)
        if is_shuffle:
            pygame.draw.circle(virtual_surface, COLOR_SPOTIFY_GREEN, (playlist_random_btn_rect.centerx, playlist_random_btn_rect.centery + 12), 2)
            
        hash_lbl = _cached_render(font_small, "#  TITLE", True, COLOR_TEXT_MUTED)
        virtual_surface.blit(hash_lbl, (content_pad_x + 10, 285))
        
        if not is_portrait:
            album_lbl = _cached_render(font_small, t("ALBUM"), True, COLOR_TEXT_MUTED)
            virtual_surface.blit(album_lbl, (content_pad_x + 390, 285))
            
        pygame.draw.line(virtual_surface, COLOR_LIGHT_GREY, (content_pad_x, 305), (main_x + main_w - 40, 305), 1)
        
        total_content_height = len(active_tracks) * 50
        max_music_scroll = max(0, total_content_height - (main_h - 315) + 50)
        
        clip_rect = pygame.Rect(main_x, 315, main_w, main_h - 315)
        virtual_surface.set_clip(clip_rect)
        
        y_offset = 315 - round(music_grid_scroll_offset)
        for index, track in enumerate(active_tracks):
            row_rect = pygame.Rect(main_x + 20, y_offset, main_w - 50, 45)
            if row_rect.colliderect(clip_rect):
                track_rects.append((row_rect, track))
                
                is_row_hovered = row_rect.collidepoint(mouse_pos)
                is_row_clicked = is_row_hovered and mouse_held
                
                if is_row_clicked:
                    pygame.draw.rect(virtual_surface, (60, 60, 60), row_rect, border_radius=6)
                elif track["path"] in green_toggled_tracks and track["title"] == current_track["title"]:
                    pygame.draw.rect(virtual_surface, (40, 60, 45), row_rect, border_radius=6)
                elif is_row_hovered:
                    pygame.draw.rect(virtual_surface, COLOR_HOVER, row_rect, border_radius=6)
                
                if track["title"] == current_track["title"]:
                    title_color = COLOR_SPOTIFY_GREEN
                else:
                    title_color = COLOR_WHITE
                
                num_surf = _cached_render(font_body, str(index + 1), True, COLOR_TEXT_MUTED)
                title_surf = _cached_render(font_body, track["title"], True, title_color)
                artist_surf = _cached_render(font_small, track["artist"], True, COLOR_TEXT_MUTED)
                
                virtual_surface.blit(num_surf, (main_x + 40, y_offset + 12))
                virtual_surface.blit(title_surf, (main_x + 80, y_offset + 4))
                virtual_surface.blit(artist_surf, (main_x + 80, y_offset + 24))
                
                if not is_portrait:
                    album_surf = _cached_render(font_body, track["album"], True, COLOR_TEXT_MUTED)
                    virtual_surface.blit(album_surf, (main_x + 420, y_offset + 12))
                
            y_offset += 50
        virtual_surface.set_clip(None)

    # --- STORAGE BROWSER ---
    elif (is_browsing_storage or is_browsing_for_cover) and (current_page in ["Search", "Your Library"] or browsing_cover_target in ("track_cover", "lyrics_import")):
        pygame.draw.rect(virtual_surface, COLOR_BLACK, (main_x, 0, main_w, HEIGHT))
        if is_browsing_for_cover and browsing_cover_target == "lyrics_import":
            title_string = "Import lyrics file (.txt / .lrc)"
        elif is_browsing_for_cover:
            title_string = "Import Cover (.png, .jpg)"
        else:
            title_string = "Device Storage Explorer"
        browser_title = _cached_render(font_title, title_string, True, COLOR_WHITE)
        virtual_surface.blit(browser_title, (content_pad_x, 40))
        
        path_lbl = _cached_render(font_small, f"Path: {current_browser_path}", True, COLOR_SPOTIFY_GREEN)
        virtual_surface.blit(path_lbl, (content_pad_x, 75))
        
        _phone_browser = is_portrait and layout_mode == "phone"
        if _phone_browser:
            # Phone: the title text ("Import Cover (.png, .jpg)" etc.) is too wide for
            # this button row to sit top-right without overlapping it, so the 3 buttons
            # move to their own left-aligned row underneath the title/path text instead.
            # Extra headroom below the path line (vs. just clearing its bottom edge) so
            # this row can't crowd/touch the text on any device's font metrics - this is
            # what made "Add Folder" (title "Device Storage Explorer") look like it
            # overlapped even though it shares this exact layout with "Import Cover".
            _browser_btn_row_y = 118
            if is_browsing_for_cover and browsing_cover_target not in ("lyrics_import",):
                browser_extra_search_btn_rect = pygame.Rect(content_pad_x, _browser_btn_row_y, 80, 35)
                select_folder_btn_rect = pygame.Rect(content_pad_x + 90, _browser_btn_row_y, 140, 35)
                cancel_browser_btn_rect = pygame.Rect(content_pad_x + 240, _browser_btn_row_y, 80, 35)
            else:
                # No "Search" button on this screen (Add Folder / lyrics import), so
                # don't reserve its space - start the row flush left like the other two
                # buttons do when Search is actually shown.
                browser_extra_search_btn_rect = pygame.Rect(content_pad_x, _browser_btn_row_y, 80, 35)
                select_folder_btn_rect = pygame.Rect(content_pad_x, _browser_btn_row_y, 140, 35)
                cancel_browser_btn_rect = pygame.Rect(content_pad_x + 150, _browser_btn_row_y, 80, 35)
        elif not is_portrait:
            cancel_browser_btn_rect = pygame.Rect(main_x + main_w - 250, 35, 90, 35)
            select_folder_btn_rect = pygame.Rect(cancel_browser_btn_rect.x - 170, 35, 160, 35)
            browser_extra_search_btn_rect = pygame.Rect(select_folder_btn_rect.x - 110, 35, 100, 35)
        else:
            cancel_browser_btn_rect = pygame.Rect(main_x + main_w - 130, 35, 90, 35)
            select_folder_btn_rect = pygame.Rect(cancel_browser_btn_rect.x - 170, 35, 160, 35)
            browser_extra_search_btn_rect = pygame.Rect(select_folder_btn_rect.x - 110, 35, 100, 35)

        bes_hovered = browser_extra_search_btn_rect.collidepoint(mouse_pos)
        bes_clicked = bes_hovered and mouse_held
        bes_color = (20, 150, 65) if bes_clicked else (COLOR_HOVER if bes_hovered else COLOR_LIGHT_GREY)
        if is_browsing_for_cover and browsing_cover_target not in ("lyrics_import",):
            pygame.draw.rect(virtual_surface, bes_color, browser_extra_search_btn_rect, border_radius=15)
            bes_lbl = _cached_render(font_small, t("Search"), True, COLOR_WHITE)
            bes_lbl_x = browser_extra_search_btn_rect.x + (browser_extra_search_btn_rect.width - bes_lbl.get_width()) // 2
            virtual_surface.blit(bes_lbl, (bes_lbl_x, browser_extra_search_btn_rect.y + 9))
        
        sf_hovered = select_folder_btn_rect.collidepoint(mouse_pos)
        sf_clicked = sf_hovered and mouse_held
        if sf_clicked:
            sf_color = (20, 150, 65)
        else:
            sf_color = COLOR_SPOTIFY_GREEN if sf_hovered else COLOR_LIGHT_GREY
        pygame.draw.rect(virtual_surface, sf_color, select_folder_btn_rect, border_radius=15)
        
        sf_text = "Confirm File" if is_browsing_for_cover else "Select Current"
        sf_lbl = _cached_render(font_small, sf_text, True, COLOR_WHITE if sf_color == COLOR_LIGHT_GREY else COLOR_BLACK)
        sf_lbl_x = select_folder_btn_rect.x + (select_folder_btn_rect.width - sf_lbl.get_width()) // 2
        virtual_surface.blit(sf_lbl, (sf_lbl_x, select_folder_btn_rect.y + 9))
        
        cc_hovered = cancel_browser_btn_rect.collidepoint(mouse_pos)
        cc_clicked = cc_hovered and mouse_held
        if cc_clicked:
            cc_color = (30, 30, 30)
        else:
            cc_color = COLOR_HOVER if cc_hovered else COLOR_LIGHT_GREY
        pygame.draw.rect(virtual_surface, cc_color, cancel_browser_btn_rect, border_radius=15)
        cc_lbl = _cached_render(font_small, t("Cancel"), True, COLOR_WHITE)
        virtual_surface.blit(cc_lbl, (cancel_browser_btn_rect.x + (cancel_browser_btn_rect.width - cc_lbl.get_width()) // 2, cancel_browser_btn_rect.y + 9))
        
        _browser_list_top = 163 if _phone_browser else 130   # phone needs extra room below the button row
        _browser_divider_y = 163 if _phone_browser else 115
        pygame.draw.line(virtual_surface, COLOR_LIGHT_GREY, (content_pad_x, _browser_divider_y), (main_x + main_w - 40, _browser_divider_y), 1)
        
        browser_available_h = HEIGHT - portrait_sidebar_h
        total_content_height = len(browser_items) * 42
        max_browser_scroll = max(0, total_content_height - (browser_available_h - _browser_list_top) + 30)
        
        clip_rect = pygame.Rect(main_x, _browser_list_top, main_w, browser_available_h - _browser_list_top)
        virtual_surface.set_clip(clip_rect)
        
        y_offset = _browser_list_top - round(browser_scroll_offset)
        for item in browser_items:
            item_row_rect = pygame.Rect(main_x + 20, y_offset - 4, main_w - 50, 35)
            if item_row_rect.colliderect(clip_rect):
                browser_rects.append((item_row_rect, item))
                
                is_b_hovered = item_row_rect.collidepoint(mouse_pos) and not show_art_search_modal
                is_b_clicked = is_b_hovered and mouse_held
                
                if is_b_clicked:
                    pygame.draw.rect(virtual_surface, (60, 60, 60), item_row_rect, border_radius=5)
                elif is_b_hovered:
                    pygame.draw.rect(virtual_surface, COLOR_HOVER, item_row_rect, border_radius=5)
                    
                if item["is_dir"]:
                    prefix = "[FOLDER] "
                    display_color = COLOR_TEXT_MUTED
                else:
                    prefix = "[IMAGE] "
                    display_color = COLOR_SPOTIFY_GREEN
                
                item_surf = _cached_render(font_body, f"{prefix}{item['name']}", True, display_color)
                virtual_surface.blit(item_surf, (content_pad_x, y_offset))
            y_offset += 42
        virtual_surface.set_clip(None)

    # --- DEDICATED SETTINGS PAGE VIEW ---
    elif viewing_settings_page and current_page == "Search":
        settings_title = _cached_render(font_title, t("Imported Music Directories"), True, COLOR_WHITE)
        virtual_surface.blit(settings_title, (content_pad_x, 40))
        
        if not is_portrait:
            close_settings_btn_rect = pygame.Rect(main_x + main_w - 250, 35, 90, 35)
        else:
            close_settings_btn_rect = pygame.Rect(main_x + main_w - 130, 35, 90, 35)
            
        cs_hovered = close_settings_btn_rect.collidepoint(mouse_pos)
        cs_clicked = cs_hovered and mouse_held
        if cs_clicked:
            cs_color = (30, 30, 30)
        else:
            cs_color = COLOR_HOVER if cs_hovered else COLOR_LIGHT_GREY
        pygame.draw.rect(virtual_surface, cs_color, close_settings_btn_rect, border_radius=15)
        cs_lbl = _cached_render(font_small, t("Back"), True, COLOR_WHITE)
        virtual_surface.blit(cs_lbl, (close_settings_btn_rect.x + 26, 44))
        
        pygame.draw.line(virtual_surface, COLOR_LIGHT_GREY, (content_pad_x, 115), (main_x + main_w - 40, 115), 1)
        
        total_content_height = len(saved_directories) * 50
        max_settings_scroll = max(0, total_content_height - (main_h - 130) + 30)
        
        clip_rect = pygame.Rect(main_x, 130, main_w, main_h - 130)
        virtual_surface.set_clip(clip_rect)
        
        y_offset = 130 - round(settings_scroll_offset)
        for d_path in saved_directories:
            row_item_rect = pygame.Rect(main_x + 20, y_offset - 4, main_w - 50, 42)
            if row_item_rect.colliderect(clip_rect):
                settings_dir_rects.append((row_item_rect, d_path))
                
                is_row_h = row_item_rect.collidepoint(mouse_pos)
                row_bg = COLOR_RED if is_row_h else COLOR_LIGHT_GREY
                pygame.draw.rect(virtual_surface, row_bg, row_item_rect, border_radius=6)
                
                lbl_path = _cached_render(font_body, f"  [FOLDER]  {d_path}", True, COLOR_WHITE)
                lbl_del = _cached_render(font_body, t("Delete [x]") if is_portrait else t("Delete and Clear Music  [x] "), True, COLOR_WHITE if is_row_h else COLOR_TEXT_MUTED)
                
                virtual_surface.blit(lbl_path, (main_x + 35, y_offset + 6))
                virtual_surface.blit(lbl_del, (main_x + main_w - (120 if is_portrait else 250), y_offset + 6))
            y_offset += 50
        virtual_surface.set_clip(None)

    # --- TOP 100 / SONG OF DAY / ARTIST OF DAY / HISTORY MAKER EMPTY PAGES ---
    elif show_top100_page and current_page == "Search":
        pygame.draw.rect(virtual_surface, COLOR_BLACK, (main_x, 0, main_w, HEIGHT - portrait_sidebar_h))

        # --- Header ---
        page_title = _cached_render(font_title, t("Top 100"), True, COLOR_WHITE)
        virtual_surface.blit(page_title, (content_pad_x, 40))
        subpage_back_rect = pygame.Rect(main_x + main_w - (130 if is_portrait else 250), 35, 90, 35)
        sb_hov = subpage_back_rect.collidepoint(mouse_pos)
        sb_clk = sb_hov and mouse_held
        sb_color = (30, 30, 30) if sb_clk else (COLOR_HOVER if sb_hov else COLOR_LIGHT_GREY)
        pygame.draw.rect(virtual_surface, sb_color, subpage_back_rect, border_radius=15)
        sb_lbl = _cached_render(font_small, t("Back"), True, COLOR_WHITE)
        virtual_surface.blit(sb_lbl, (subpage_back_rect.x + 26, 44))

        # Refresh button
        refresh_rect = pygame.Rect(main_x + main_w - (240 if is_portrait else 360), 35, 90, 35)
        rf_hov = refresh_rect.collidepoint(mouse_pos)
        rf_clk = rf_hov and mouse_held
        rf_color = COLOR_SPOTIFY_GREEN if rf_clk else (COLOR_HOVER if rf_hov else COLOR_LIGHT_GREY)
        pygame.draw.rect(virtual_surface, rf_color, refresh_rect, border_radius=15)
        rf_lbl = _cached_render(font_small, t("Refresh"), True, COLOR_WHITE)
        virtual_surface.blit(rf_lbl, (refresh_rect.x + (refresh_rect.width - rf_lbl.get_width()) // 2, 44))

        # Freshness label
        if top100_last_fetched > 0:
            import datetime
            age_str = datetime.datetime.fromtimestamp(top100_last_fetched).strftime("Updated %d %b %H:%M")
            age_surf = _cached_render(font_small, age_str, True, COLOR_TEXT_MUTED)
            virtual_surface.blit(age_surf, (content_pad_x, 88))

        pygame.draw.line(virtual_surface, COLOR_LIGHT_GREY,
                         (content_pad_x, 115), (main_x + main_w - 40, 115), 1)

        body_top  = 125
        body_h    = HEIGHT - portrait_sidebar_h - body_top
        body_rect = pygame.Rect(main_x, body_top, main_w, body_h)

        if top100_loading:
            wait = _cached_render(font_body, t("Loading chart data..."), True, COLOR_TEXT_MUTED)
            virtual_surface.blit(wait, (content_pad_x, body_top + 30))
        elif top100_error and not top100_tracks:
            for ei, el in enumerate(top100_error.split("\n")):
                virtual_surface.blit(_cached_render(font_body, el, True, (200, 90, 90)),
                                     (content_pad_x, body_top + 30 + ei * 28))
        else:
            virtual_surface.set_clip(body_rect)
            top100_link_rects.clear()
            global max_top100_scroll

            phone_rows = (layout_mode == "phone")
            row_h       = 128 if phone_rows else 80
            link_w      = 96
            link_h      = 30
            link_gap    = 8
            rank_w      = 52
            art_w       = 48

            y_row = body_top - round(top100_scroll_offset)
            total_h = len(top100_tracks) * row_h
            max_top100_scroll = max(0, total_h - body_h + 20)

            for track in top100_tracks:
                row_rect = pygame.Rect(main_x + 10, y_row, main_w - 20, row_h - 6)
                if row_rect.bottom < body_top or row_rect.top > body_top + body_h:
                    y_row += row_h
                    continue

                # Row background
                row_hov = row_rect.collidepoint(mouse_pos)
                pygame.draw.rect(virtual_surface, (28, 28, 28) if row_hov else (20, 20, 20),
                                 row_rect, border_radius=6)

                # Rank number — uniform muted colour
                rank_surf = _cached_render(font_body, str(track["rank"]), True, COLOR_TEXT_MUTED)
                rx = row_rect.x + 10 + (rank_w - rank_surf.get_width()) // 2
                info_h = 68 if phone_rows else (row_h - 6)
                virtual_surface.blit(rank_surf, (rx, y_row + (info_h - rank_surf.get_height()) // 2))

                # Art box — show downloaded surface or placeholder while loading
                art_rect = pygame.Rect(row_rect.x + rank_w + 8, y_row + 8, art_w, art_w)
                cached = top100_art_cache.get(track["rank"])
                if cached is not None:
                    virtual_surface.blit(_cached_scale(cached, (art_w, art_w)), art_rect)
                    pygame.draw.rect(virtual_surface, (50, 50, 50), art_rect, width=1, border_radius=4)
                else:
                    pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, art_rect, border_radius=4)
                    note = _cached_render(font_small, "\u266a", True, (120, 120, 120))
                    virtual_surface.blit(note, (art_rect.x + (art_w - note.get_width()) // 2,
                                                art_rect.y + (art_w - note.get_height()) // 2))

                # Title + artist
                tx = row_rect.x + rank_w + art_w + 20
                if phone_rows:
                    # Links move to their own full-width row below, so text can
                    # use the entire row width here instead of squeezing next
                    # to three link buttons.
                    text_max_w = row_rect.right - tx - 14
                else:
                    link_area_w = (link_w + link_gap) * 3 - link_gap
                    text_max_w  = row_rect.right - tx - link_area_w - 14

                title_str  = track["title"]
                artist_str = track["artist"]
                while font_body.size(title_str)[0]  > text_max_w and len(title_str)  > 4: title_str  = title_str[:-1]
                while font_small.size(artist_str)[0] > text_max_w and len(artist_str) > 4: artist_str = artist_str[:-1]
                if title_str  != track["title"]:  title_str  += "\u2026"
                if artist_str != track["artist"]: artist_str += "\u2026"

                virtual_surface.blit(_cached_render(font_body, title_str,  True, COLOR_WHITE),
                                     (tx, y_row + 12))
                virtual_surface.blit(_cached_render(font_small, artist_str, True, COLOR_TEXT_MUTED),
                                     (tx, y_row + 38))

                # Link buttons: black bg, coloured text per service
                link_defs = [
                    ("Spotify",  track["spotify_url"],  (30, 215, 96)),
                    ("YouTube",  track["youtube_url"],  (255, 80,  80)),
                    ("Apple",    track["apple_url"],    (250, 110, 200)),
                ]
                if phone_rows:
                    # Full-width row of three evenly-spaced link buttons below
                    # the title/artist line, so each one has a real tap target.
                    phone_link_gap = 8
                    phone_link_w = (row_rect.width - 16 - phone_link_gap * 2) // 3
                    lx = row_rect.x + 8
                    ly = y_row + info_h + 6
                    for lbl, url, txt_col in link_defs:
                        lr = pygame.Rect(lx, ly, phone_link_w, link_h)
                        l_hov = lr.collidepoint(mouse_pos)
                        l_clk = l_hov and mouse_held
                        bg = (50, 50, 50) if l_clk else (COLOR_HOVER if l_hov else COLOR_LIGHT_GREY)
                        pygame.draw.rect(virtual_surface, bg, lr, border_radius=15)
                        ls = _cached_render(font_small, lbl, True, txt_col)
                        virtual_surface.blit(ls, (lr.x + (lr.width - ls.get_width()) // 2,
                                                 lr.y + (lr.height - ls.get_height()) // 2))
                        top100_link_rects.append((lr, url))
                        lx += phone_link_w + phone_link_gap
                else:
                    link_area_w = (link_w + link_gap) * 3 - link_gap
                    lx = row_rect.right - link_area_w - 8
                    ly = y_row + (row_h - 6 - link_h) // 2
                    for lbl, url, txt_col in link_defs:
                        lr = pygame.Rect(lx, ly, link_w, link_h)
                        l_hov = lr.collidepoint(mouse_pos)
                        l_clk = l_hov and mouse_held
                        bg = (50, 50, 50) if l_clk else (COLOR_HOVER if l_hov else COLOR_LIGHT_GREY)
                        pygame.draw.rect(virtual_surface, bg, lr, border_radius=15)
                        ls = _cached_render(font_small, lbl, True, txt_col)
                        virtual_surface.blit(ls, (lr.x + (lr.width - ls.get_width()) // 2,
                                                 lr.y + (lr.height - ls.get_height()) // 2))
                        top100_link_rects.append((lr, url))
                        lx += link_w + link_gap

                pygame.draw.line(virtual_surface, (35, 35, 35),
                                 (row_rect.x + rank_w, row_rect.bottom + 2),
                                 (row_rect.right - 10, row_rect.bottom + 2), 1)
                y_row += row_h

            virtual_surface.set_clip(None)

            # Error banner at bottom if partial data with warning
            if top100_error:
                err_surf = _cached_render(font_small, top100_error[:80], True, (200, 90, 90))
                virtual_surface.blit(err_surf, (content_pad_x, HEIGHT - portrait_sidebar_h - 28))

    elif show_song_of_day_page and current_page == "Search":
        pygame.draw.rect(virtual_surface, COLOR_BLACK, (main_x, 0, main_w, HEIGHT - portrait_sidebar_h))

        # Header
        page_title = _cached_render(font_title, t("Song of the Day"), True, COLOR_WHITE)
        virtual_surface.blit(page_title, (content_pad_x, 40))
        subpage_back_rect = pygame.Rect(main_x + main_w - (130 if is_portrait else 250), 35, 90, 35)
        sb_hov = subpage_back_rect.collidepoint(mouse_pos)
        sb_clk = sb_hov and mouse_held
        sb_color = (30, 30, 30) if sb_clk else (COLOR_HOVER if sb_hov else COLOR_LIGHT_GREY)
        pygame.draw.rect(virtual_surface, sb_color, subpage_back_rect, border_radius=15)
        virtual_surface.blit(_cached_render(font_small, t("Back"), True, COLOR_WHITE), (subpage_back_rect.x + 26, 44))
        pygame.draw.line(virtual_surface, COLOR_LIGHT_GREY, (content_pad_x, 115), (main_x + main_w - 40, 115), 1)

        # --- Scrollable body ---
        body_top  = 125
        body_h    = HEIGHT - portrait_sidebar_h - body_top
        body_rect = pygame.Rect(main_x, body_top, main_w, body_h)
        virtual_surface.set_clip(body_rect)
        global max_sotd_scroll, sotd_link_rects
        sotd_link_rects = []
        _sotd_idx, _sotd_entry = _pick_daily_entry(SOTD_ENTRIES)

        # All content drawn relative to scroll
        cy = body_top + 20 - round(sotd_scroll_offset)

        # Cover art box
        cover_size = min(main_w - 80, 260)
        cover_x    = main_x + (main_w - cover_size) // 2
        cover_rect = pygame.Rect(cover_x, cy, cover_size, cover_size)
        if sotd_cover_surface:
            scaled = _cached_scale(sotd_cover_surface, (cover_size, cover_size))
            virtual_surface.blit(scaled, cover_rect)
            pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, cover_rect, width=1, border_radius=8)
        else:
            pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, cover_rect, border_radius=8)
            note = _cached_render(font_huge, "\u266a", True, (80, 80, 80))
            virtual_surface.blit(note, (cover_rect.x + (cover_size - note.get_width())  // 2,
                                        cover_rect.y + (cover_size - note.get_height()) // 2))
            if sotd_cover_loading:
                lbl = _cached_render(font_small, t("Loading art..."), True, COLOR_TEXT_MUTED)
                virtual_surface.blit(lbl, (cover_rect.x + (cover_size - lbl.get_width()) // 2,
                                           cover_rect.bottom + 8))
        cy += cover_size + 22

        # Song title and artist
        song_title_surf = _cached_render(font_huge, _sotd_entry["title"], True, COLOR_WHITE)
        if song_title_surf.get_width() > main_w - 60:
            song_title_surf = _cached_render(font_title, _sotd_entry["title"], True, COLOR_WHITE)
        virtual_surface.blit(song_title_surf, (main_x + (main_w - song_title_surf.get_width()) // 2, cy))
        cy += song_title_surf.get_height() + 8

        artist_surf = _cached_render(font_body, _sotd_entry["artist"], True, COLOR_TEXT_MUTED)
        virtual_surface.blit(artist_surf, (main_x + (main_w - artist_surf.get_width()) // 2, cy))
        cy += artist_surf.get_height() + 24

        # Link buttons row
        sotd_q    = urllib.parse.quote_plus(_sotd_entry["search"])
        sotd_links = [
            ("Spotify",  f"https://open.spotify.com/search/{urllib.parse.quote(_sotd_entry['search'])}",
             (30, 215, 96)),
            ("YouTube",  f"https://music.youtube.com/search?q={sotd_q}",  (255, 80,  80)),
            ("Apple",    f"https://music.apple.com/us/search?term={sotd_q}", (250, 110, 200)),
        ]
        btn_w   = 110
        btn_h   = 38
        btn_gap = 12
        total_btns_w = len(sotd_links) * btn_w + (len(sotd_links) - 1) * btn_gap
        bx = main_x + (main_w - total_btns_w) // 2
        for lbl, url, txt_col in sotd_links:
            br = pygame.Rect(bx, cy, btn_w, btn_h)
            b_hov = br.collidepoint(mouse_pos)
            b_clk = b_hov and mouse_held
            bg    = (50, 50, 50) if b_clk else (COLOR_HOVER if b_hov else COLOR_LIGHT_GREY)
            pygame.draw.rect(virtual_surface, bg, br, border_radius=19)
            bs = _cached_render(font_body, lbl, True, txt_col)
            virtual_surface.blit(bs, (br.x + (btn_w - bs.get_width()) // 2,
                                      br.y + (btn_h - bs.get_height()) // 2))
            sotd_link_rects.append((br, url))
            bx += btn_w + btn_gap
        cy += btn_h + 30

        # Divider
        pygame.draw.line(virtual_surface, COLOR_LIGHT_GREY,
                         (content_pad_x, cy), (main_x + main_w - 40, cy), 1)
        cy += 18

        # Description
        description = _sotd_entry["description"]
        desc_x     = content_pad_x
        desc_max_w = main_w - (content_pad_x - main_x) * 2
        for para in description.split("\n\n"):
            for line in get_wrapped_lines(para.strip(), font_small, desc_max_w):
                if cy > body_top + body_h + 40:
                    break
                ls = _cached_render(font_small, line, True, (200, 200, 200))
                virtual_surface.blit(ls, (desc_x, cy))
                cy += ls.get_height() + 4
            cy += 12  # paragraph gap

        max_sotd_scroll = max(0, cy + round(sotd_scroll_offset) - (body_top + body_h) + 40)
        virtual_surface.set_clip(None)

    elif show_artist_of_day_page and current_page == "Search":
        pygame.draw.rect(virtual_surface, COLOR_BLACK, (main_x, 0, main_w, HEIGHT - portrait_sidebar_h))

        # Header
        page_title = _cached_render(font_title, t("Artist of the Day"), True, COLOR_WHITE)
        virtual_surface.blit(page_title, (content_pad_x, 40))
        subpage_back_rect = pygame.Rect(main_x + main_w - (130 if is_portrait else 250), 35, 90, 35)
        sb_hov = subpage_back_rect.collidepoint(mouse_pos)
        sb_clk = sb_hov and mouse_held
        sb_color = (30, 30, 30) if sb_clk else (COLOR_HOVER if sb_hov else COLOR_LIGHT_GREY)
        pygame.draw.rect(virtual_surface, sb_color, subpage_back_rect, border_radius=15)
        virtual_surface.blit(_cached_render(font_small, t("Back"), True, COLOR_WHITE), (subpage_back_rect.x + 26, 44))
        pygame.draw.line(virtual_surface, COLOR_LIGHT_GREY, (content_pad_x, 115), (main_x + main_w - 40, 115), 1)

        # --- Scrollable body ---
        body_top  = 125
        body_h    = HEIGHT - portrait_sidebar_h - body_top
        body_rect = pygame.Rect(main_x, body_top, main_w, body_h)
        virtual_surface.set_clip(body_rect)
        global max_aotd_scroll, aotd_link_rects
        aotd_link_rects = []
        _aotd_idx, _aotd_entry = _pick_daily_entry(AOTD_ENTRIES)

        # All content drawn relative to scroll
        cy = body_top + 20 - round(aotd_scroll_offset)

        # Cover art box (circular-feeling square, same treatment as Song of Day)
        cover_size = min(main_w - 80, 260)
        cover_x    = main_x + (main_w - cover_size) // 2
        cover_rect = pygame.Rect(cover_x, cy, cover_size, cover_size)
        if aotd_cover_surface:
            scaled = _cached_scale(aotd_cover_surface, (cover_size, cover_size))
            virtual_surface.blit(scaled, cover_rect)
            pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, cover_rect, width=1, border_radius=8)
        else:
            pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, cover_rect, border_radius=8)
            note = _cached_render(font_huge, "\u266a", True, (80, 80, 80))
            virtual_surface.blit(note, (cover_rect.x + (cover_size - note.get_width())  // 2,
                                        cover_rect.y + (cover_size - note.get_height()) // 2))
            if aotd_cover_loading:
                lbl = _cached_render(font_small, t("Loading art..."), True, COLOR_TEXT_MUTED)
                virtual_surface.blit(lbl, (cover_rect.x + (cover_size - lbl.get_width()) // 2,
                                           cover_rect.bottom + 8))
        cy += cover_size + 22

        # Artist name
        artist_name_surf = _cached_render(font_huge, _aotd_entry["name"], True, COLOR_WHITE)
        if artist_name_surf.get_width() > main_w - 60:
            artist_name_surf = _cached_render(font_title, _aotd_entry["name"], True, COLOR_WHITE)
        virtual_surface.blit(artist_name_surf, (main_x + (main_w - artist_name_surf.get_width()) // 2, cy))
        cy += artist_name_surf.get_height() + 8

        genre_surf = _cached_render(font_body, _aotd_entry["genre"], True, COLOR_TEXT_MUTED)
        virtual_surface.blit(genre_surf, (main_x + (main_w - genre_surf.get_width()) // 2, cy))
        cy += genre_surf.get_height() + 24

        # Link buttons row
        aotd_q    = urllib.parse.quote_plus(_aotd_entry["search"])
        aotd_links = [
            ("Spotify",  f"https://open.spotify.com/search/{urllib.parse.quote(_aotd_entry['search'])}",
             (30, 215, 96)),
            ("YouTube",  f"https://music.youtube.com/search?q={aotd_q}",  (255, 80,  80)),
            ("Apple",    f"https://music.apple.com/us/search?term={aotd_q}", (250, 110, 200)),
        ]
        btn_w   = 110
        btn_h   = 38
        btn_gap = 12
        total_btns_w = len(aotd_links) * btn_w + (len(aotd_links) - 1) * btn_gap
        bx = main_x + (main_w - total_btns_w) // 2
        for lbl, url, txt_col in aotd_links:
            br = pygame.Rect(bx, cy, btn_w, btn_h)
            b_hov = br.collidepoint(mouse_pos)
            b_clk = b_hov and mouse_held
            bg    = (50, 50, 50) if b_clk else (COLOR_HOVER if b_hov else COLOR_LIGHT_GREY)
            pygame.draw.rect(virtual_surface, bg, br, border_radius=19)
            bs = _cached_render(font_body, lbl, True, txt_col)
            virtual_surface.blit(bs, (br.x + (btn_w - bs.get_width()) // 2,
                                      br.y + (btn_h - bs.get_height()) // 2))
            aotd_link_rects.append((br, url))
            bx += btn_w + btn_gap
        cy += btn_h + 30

        # Divider
        pygame.draw.line(virtual_surface, COLOR_LIGHT_GREY,
                         (content_pad_x, cy), (main_x + main_w - 40, cy), 1)
        cy += 18

        # Description
        description = _aotd_entry["description"]
        desc_x     = content_pad_x
        desc_max_w = main_w - (content_pad_x - main_x) * 2
        for para in description.split("\n\n"):
            for line in get_wrapped_lines(para.strip(), font_small, desc_max_w):
                if cy > body_top + body_h + 40:
                    break
                ls = _cached_render(font_small, line, True, (200, 200, 200))
                virtual_surface.blit(ls, (desc_x, cy))
                cy += ls.get_height() + 4
            cy += 12  # paragraph gap

        max_aotd_scroll = max(0, cy + round(aotd_scroll_offset) - (body_top + body_h) + 40)
        virtual_surface.set_clip(None)

    elif show_history_maker_page and current_page == "Search":
        pygame.draw.rect(virtual_surface, COLOR_BLACK, (main_x, 0, main_w, HEIGHT - portrait_sidebar_h))

        # Header
        page_title = _cached_render(font_title, t("History Maker"), True, COLOR_WHITE)
        virtual_surface.blit(page_title, (content_pad_x, 40))
        subpage_back_rect = pygame.Rect(main_x + main_w - (130 if is_portrait else 250), 35, 90, 35)
        sb_hov = subpage_back_rect.collidepoint(mouse_pos)
        sb_clk = sb_hov and mouse_held
        sb_color = (30, 30, 30) if sb_clk else (COLOR_HOVER if sb_hov else COLOR_LIGHT_GREY)
        pygame.draw.rect(virtual_surface, sb_color, subpage_back_rect, border_radius=15)
        virtual_surface.blit(_cached_render(font_small, t("Back"), True, COLOR_WHITE), (subpage_back_rect.x + 26, 44))
        pygame.draw.line(virtual_surface, COLOR_LIGHT_GREY, (content_pad_x, 115), (main_x + main_w - 40, 115), 1)

        # --- Scrollable body ---
        body_top  = 125
        body_h    = HEIGHT - portrait_sidebar_h - body_top
        body_rect = pygame.Rect(main_x, body_top, main_w, body_h)
        virtual_surface.set_clip(body_rect)
        global max_hm_scroll, hm_link_rects
        hm_link_rects = []
        _hm_idx, _hm_entry = _pick_daily_entry(HM_ENTRIES)

        # All content drawn relative to scroll
        cy = body_top + 20 - round(hm_scroll_offset)

        # Cover art box
        cover_size = min(main_w - 80, 260)
        cover_x    = main_x + (main_w - cover_size) // 2
        cover_rect = pygame.Rect(cover_x, cy, cover_size, cover_size)
        if hm_cover_surface:
            scaled = _cached_scale(hm_cover_surface, (cover_size, cover_size))
            virtual_surface.blit(scaled, cover_rect)
            pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, cover_rect, width=1, border_radius=8)
        else:
            pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, cover_rect, border_radius=8)
            note = _cached_render(font_huge, "\u266a", True, (80, 80, 80))
            virtual_surface.blit(note, (cover_rect.x + (cover_size - note.get_width())  // 2,
                                        cover_rect.y + (cover_size - note.get_height()) // 2))
            if hm_cover_loading:
                lbl = _cached_render(font_small, t("Loading art..."), True, COLOR_TEXT_MUTED)
                virtual_surface.blit(lbl, (cover_rect.x + (cover_size - lbl.get_width()) // 2,
                                           cover_rect.bottom + 8))
        cy += cover_size + 22

        # Event title and date
        hm_title_surf = _cached_render(font_huge, _hm_entry["title"], True, COLOR_WHITE)
        if hm_title_surf.get_width() > main_w - 60:
            hm_title_surf = _cached_render(font_title, _hm_entry["title"], True, COLOR_WHITE)
        virtual_surface.blit(hm_title_surf, (main_x + (main_w - hm_title_surf.get_width()) // 2, cy))
        cy += hm_title_surf.get_height() + 8

        date_surf = _cached_render(font_body, _hm_entry["date"], True, COLOR_TEXT_MUTED)
        if date_surf.get_width() > main_w - 60:
            date_surf = _cached_render(font_small, _hm_entry["date"], True, COLOR_TEXT_MUTED)
        virtual_surface.blit(date_surf, (main_x + (main_w - date_surf.get_width()) // 2, cy))
        cy += date_surf.get_height() + 24

        # Link buttons row
        hm_q    = urllib.parse.quote_plus(_hm_entry["search"])
        hm_links = [
            ("Spotify",  f"https://open.spotify.com/search/{urllib.parse.quote(_hm_entry['search'])}",
             (30, 215, 96)),
            ("YouTube",  f"https://music.youtube.com/search?q={hm_q}",  (255, 80,  80)),
            ("Apple",    f"https://music.apple.com/us/search?term={hm_q}", (250, 110, 200)),
        ]
        btn_w   = 110
        btn_h   = 38
        btn_gap = 12
        total_btns_w = len(hm_links) * btn_w + (len(hm_links) - 1) * btn_gap
        bx = main_x + (main_w - total_btns_w) // 2
        for lbl, url, txt_col in hm_links:
            br = pygame.Rect(bx, cy, btn_w, btn_h)
            b_hov = br.collidepoint(mouse_pos)
            b_clk = b_hov and mouse_held
            bg    = (50, 50, 50) if b_clk else (COLOR_HOVER if b_hov else COLOR_LIGHT_GREY)
            pygame.draw.rect(virtual_surface, bg, br, border_radius=19)
            bs = _cached_render(font_body, lbl, True, txt_col)
            virtual_surface.blit(bs, (br.x + (btn_w - bs.get_width()) // 2,
                                      br.y + (btn_h - bs.get_height()) // 2))
            hm_link_rects.append((br, url))
            bx += btn_w + btn_gap
        cy += btn_h + 30

        # Divider
        pygame.draw.line(virtual_surface, COLOR_LIGHT_GREY,
                         (content_pad_x, cy), (main_x + main_w - 40, cy), 1)
        cy += 18

        # Description
        description = _hm_entry["description"]
        desc_x     = content_pad_x
        desc_max_w = main_w - (content_pad_x - main_x) * 2
        for para in description.split("\n\n"):
            for line in get_wrapped_lines(para.strip(), font_small, desc_max_w):
                if cy > body_top + body_h + 40:
                    break
                ls = _cached_render(font_small, line, True, (200, 200, 200))
                virtual_surface.blit(ls, (desc_x, cy))
                cy += ls.get_height() + 4
            cy += 12  # paragraph gap

        max_hm_scroll = max(0, cy + round(hm_scroll_offset) - (body_top + body_h) + 40)
        virtual_surface.set_clip(None)

    # --- SEARCH PAGE ---
    elif current_page == "Search":
        search_title = _cached_render(font_title, t("Search Results"), True, COLOR_WHITE)
        virtual_surface.blit(search_title, (content_pad_x, 40))

        # --- PHONE PORTRAIT LAYOUT: search bar full-width on row 1, buttons on row 2 ---
        if is_portrait and layout_mode == "phone":
            search_row_y = 80   # row 1: full-width search bar
            btn_row_y = 150      # row 2: buttons (+ Add Folder, cog)

            # --- Full-width search bar (top row) ---
            search_box_rect = pygame.Rect(content_pad_x, search_row_y, main_w - (content_pad_x - main_x) * 2, 52)
            pygame.draw.rect(virtual_surface, COLOR_WHITE, search_box_rect, border_radius=22)
            if search_input_active and not show_create_playlist_modal:
                pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, search_box_rect, width=2, border_radius=22)

            if search_query != "":
                search_text_surf = _cached_render(font_small, f"  {search_query}", True, COLOR_BLACK)
            else:
                search_text_surf = _cached_render(font_small, f"  {search_message}", True, COLOR_LIGHT_GREY)
            # clip long text inside the box
            clip_surf = pygame.Surface((search_box_rect.width - 30, search_text_surf.get_height()), pygame.SRCALPHA)
            clip_surf.blit(search_text_surf, (0, 0))
            virtual_surface.blit(clip_surf, (search_box_rect.x + 15, search_box_rect.y + (52 - search_text_surf.get_height()) // 2))

            # --- Button row: horizontally scrollable strip ---
            ph_add_w = 180
            ph_btn_h = 52
            ph_cog_w = 52
            ph_gap   = 12

            row_inset  = content_pad_x - main_x
            row_x      = content_pad_x
            row_w      = main_w - row_inset * 2
            row_clip_rect = pygame.Rect(row_x, btn_row_y, row_w, ph_btn_h)
            btn_row_rect = row_clip_rect

            # Build the ordered list of buttons in the strip: (kind, label, width)
            strip_buttons = [("add_folder", t("+ Add Folder"), ph_add_w)]
            if saved_directories:
                strip_buttons.append(("settings", None, ph_cog_w))
            strip_buttons.append(("top100", t("Top 100"), 150))
            strip_buttons.append(("song_of_day", t("Song of Day"), 170))
            strip_buttons.append(("artist_of_day", t("Artist of Day"), 175))
            strip_buttons.append(("history_maker", t("History"), 140))

            total_strip_w = sum(w for _, _, w in strip_buttons) + ph_gap * len(strip_buttons)
            max_btn_row_scroll = total_strip_w

            if not user_scrolled_btn_row:
                group_w = ph_add_w + (ph_gap + ph_cog_w if saved_directories else 0)
                center_shift = (row_w - group_w) / 2.0
                initial_offset = (-center_shift) % total_strip_w
                btn_row_scroll_offset = initial_offset
                target_btn_row_scroll = initial_offset

            settings_btn_rect = pygame.Rect(0, 0, 0, 0)
            top100_btn_rect = pygame.Rect(0, 0, 0, 0)
            song_of_day_btn_rect = pygame.Rect(0, 0, 0, 0)
            artist_of_day_btn_rect = pygame.Rect(0, 0, 0, 0)
            history_maker_btn_rect = pygame.Rect(0, 0, 0, 0)

            virtual_surface.set_clip(row_clip_rect)
            wrapped_offset = btn_row_scroll_offset % total_strip_w
            x_cursor = row_x - wrapped_offset - total_strip_w
            while x_cursor < row_x + row_w:
                for kind, label, w in strip_buttons:
                    btn_rect = pygame.Rect(int(x_cursor), btn_row_y, w, ph_btn_h)
                    if btn_rect.colliderect(row_clip_rect):
                        is_hov = btn_rect.collidepoint(mouse_pos)
                        is_clk = is_hov and mouse_held

                        if kind == "add_folder":
                            add_folder_btn_rect = btn_rect
                            if is_clk:
                                pygame.draw.rect(virtual_surface, (20, 150, 65), btn_rect, border_radius=20)
                                btn_color = COLOR_WHITE
                            elif is_hov:
                                pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, btn_rect, border_radius=20)
                                btn_color = COLOR_BLACK
                            else:
                                pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, btn_rect, border_radius=20)
                                btn_color = COLOR_WHITE
                            btn_txt = render_fit_text(label, btn_color, w - 16)
                            virtual_surface.blit(btn_txt, (btn_rect.x + (w - btn_txt.get_width()) // 2,
                                                           btn_rect.y + (ph_btn_h - btn_txt.get_height()) // 2))
                        elif kind == "settings":
                            settings_btn_rect = btn_rect
                            if is_clk:
                                box_bg_color = (20, 150, 65); st_color = COLOR_WHITE
                            elif is_hov:
                                box_bg_color = COLOR_SPOTIFY_GREEN; st_color = COLOR_BLACK
                            else:
                                box_bg_color = COLOR_LIGHT_GREY; st_color = COLOR_WHITE
                            pygame.draw.rect(virtual_surface, box_bg_color, btn_rect, border_radius=20)
                            draw_solid_cog_wheel(virtual_surface, btn_rect.x + 16, btn_rect.y + 16, 20, 20, st_color)
                        else:
                            if kind == "top100": top100_btn_rect = btn_rect
                            elif kind == "song_of_day": song_of_day_btn_rect = btn_rect
                            elif kind == "artist_of_day": artist_of_day_btn_rect = btn_rect
                            elif kind == "history_maker": history_maker_btn_rect = btn_rect

                            if is_clk:
                                pygame.draw.rect(virtual_surface, (20, 150, 65), btn_rect, border_radius=20)
                                btn_color = COLOR_WHITE
                            elif is_hov:
                                pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, btn_rect, border_radius=20)
                                btn_color = COLOR_BLACK
                            else:
                                pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, btn_rect, border_radius=20)
                                btn_color = COLOR_WHITE
                            btn_txt = render_fit_text(label, btn_color, w - 16)
                            virtual_surface.blit(btn_txt, (btn_rect.x + (w - btn_txt.get_width()) // 2,
                                                           btn_rect.y + (ph_btn_h - btn_txt.get_height()) // 2))
                    x_cursor += w + ph_gap
            virtual_surface.set_clip(None)

            grid_start_y = btn_row_y + 60

        else:
            # --- DESKTOP / TABLET PORTRAIT LAYOUT (unchanged) ---
            if not is_portrait:
                add_folder_btn_rect = pygame.Rect(content_pad_x + 520, 80, 150, 40)
            else:
                add_folder_btn_rect = pygame.Rect(main_x + main_w - 220, 80, 150, 40)

            is_af_hovered = add_folder_btn_rect.collidepoint(mouse_pos)
            is_af_clicked = is_af_hovered and mouse_held
            if is_af_clicked:
                pygame.draw.rect(virtual_surface, (20, 150, 65), add_folder_btn_rect, border_radius=20)
                btn_color = COLOR_WHITE
            elif is_af_hovered:
                pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, add_folder_btn_rect, border_radius=20)
                btn_color = COLOR_BLACK
            else:
                pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, add_folder_btn_rect, border_radius=20)
                btn_color = COLOR_WHITE
            btn_txt = _cached_render(font_small, t("+ Add Folder"), True, btn_color)
            virtual_surface.blit(btn_txt, (add_folder_btn_rect.x + 38, 92))

            if saved_directories:
                if not is_portrait:
                    settings_btn_rect = pygame.Rect(content_pad_x + 680, 80, 40, 40)
                else:
                    settings_btn_rect = pygame.Rect(main_x + main_w - 55, 80, 40, 40)

                is_st_hovered = settings_btn_rect.collidepoint(mouse_pos)
                is_st_clicked = is_st_hovered and mouse_held
                if is_st_clicked:
                    box_bg_color = (20, 150, 65); st_color = COLOR_WHITE
                elif is_st_hovered:
                    box_bg_color = COLOR_SPOTIFY_GREEN; st_color = COLOR_BLACK
                else:
                    box_bg_color = COLOR_LIGHT_GREY; st_color = COLOR_WHITE
                pygame.draw.rect(virtual_surface, box_bg_color, settings_btn_rect, border_radius=20)
                draw_solid_cog_wheel(virtual_surface, settings_btn_rect.x + 10, settings_btn_rect.y + 10, 20, 20, st_color)

            search_box_rect = pygame.Rect(content_pad_x, 80, 500 if not is_portrait else main_w - 280, 40)
            pygame.draw.rect(virtual_surface, COLOR_WHITE, search_box_rect, border_radius=20)
            if search_input_active and not show_create_playlist_modal:
                pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, search_box_rect, width=2, border_radius=20)

            if search_query != "":
                search_text_surf = _cached_render(font_small, f"  {search_query}", True, COLOR_BLACK)
            else:
                search_text_surf = _cached_render(font_small, f"  {search_message}", True, COLOR_LIGHT_GREY)
            virtual_surface.blit(search_text_surf, (content_pad_x + 15, 92))

            grid_start_y = 150

        filtered_tracks = []
        cleaned_query = search_query.strip().lower()
        for track in imported_tracks:
            if cleaned_query == "" or cleaned_query in track["raw_title"].lower() or cleaned_query in track["album"].lower():
                filtered_tracks.append(track)

        if not imported_tracks:
            empty_surf = _cached_render(font_body, t("No local music loaded. Tap '+ Add Folder' above to explore your storage!"), True, COLOR_TEXT_MUTED)
            virtual_surface.blit(empty_surf, (content_pad_x, grid_start_y + 10))
        elif not filtered_tracks:
            no_match_surf = _cached_render(font_body, f"No results match your search query for '{search_query}'.", True, COLOR_TEXT_MUTED)
            virtual_surface.blit(no_match_surf, (content_pad_x, grid_start_y + 10))
        else:
            start_y = grid_start_y
            if layout_mode == "phone":
                # Cards side by side — size them to fill the available width.
                # Column count defaults to 2, but can be bumped up via the
                # Settings "Grid" button (up to 4).
                cols = grid_cols_override if grid_cols_override else 2
                gap_x = 16
                side_pad = 16
                card_width = (main_w - side_pad * 2 - gap_x * (cols - 1)) // cols
                # Compensate for vertical stretch between virtual surface and real screen
                # so cards appear square on the actual device display
                stretch_ratio = (REAL_WIDTH * HEIGHT) / (REAL_HEIGHT * WIDTH)
                card_height = int(card_width * max(0.65, min(1.0, stretch_ratio)))
                gap_y = 65
            else:
                gap_x = 14
                gap_y = 55
                side_pad = 0
                # Column count defaults to 5, and can be bumped up via the
                # Settings "Grid" button (up to 7).
                cols = grid_cols_override if grid_cols_override else 5
                card_width = (main_w - 20 - gap_x * (cols - 1)) // cols
                if card_width < 60: card_width = 60
                card_height = card_width

            if layout_mode == "phone":
                # Phone: fixed-column grid, flush left with side padding
                actual_grid_w = (cols * card_width) + ((cols - 1) * gap_x)
                start_x = main_x + side_pad
            elif is_portrait:
                # Portrait desktop: keep grid centred
                actual_grid_w = (cols * card_width) + ((cols - 1) * gap_x)
                start_x = main_x + (main_w - actual_grid_w) // 2
            else:
                actual_grid_w = (cols * card_width) + ((cols - 1) * gap_x)
                # Landscape: left edge lines up with search bar / content padding,
                # and leave a matching gap on the right instead of running to the
                # screen edge.
                right_budget = main_w - (content_pad_x - main_x) - 30
                if cols > 0:
                    landscape_card_width = (right_budget - gap_x * (cols - 1)) // cols
                    if landscape_card_width < 60: landscape_card_width = 60
                    card_width = landscape_card_width
                    card_height = card_width
                    actual_grid_w = (cols * card_width) + ((cols - 1) * gap_x)
                start_x = content_pad_x

            rows = (len(filtered_tracks) + cols - 1) // cols if cols > 0 else 0
            total_content_height = rows * (card_height + gap_y)
            max_music_scroll = max(0, total_content_height - (main_h - grid_start_y) + 50)

            clip_rect = pygame.Rect(main_x, grid_start_y, main_w, main_h - grid_start_y)
            virtual_surface.set_clip(clip_rect)
            
            for index, track in enumerate(filtered_tracks):
                col = index % cols
                row = index // cols
                
                box_x = start_x + (col * (card_width + gap_x))
                box_y = start_y + (row * (card_height + gap_y)) - round(music_grid_scroll_offset)
                
                card_rect = pygame.Rect(box_x, box_y, card_width, card_height + 40)
                
                if card_rect.colliderect(clip_rect):
                    track_rects.append((card_rect, track))
                    
                    is_card_hovered = card_rect.collidepoint(mouse_pos)
                    is_card_clicked = is_card_hovered and mouse_held
                    
                    if is_card_clicked:
                        virtual_surface.blit(_cached_rounded_rect((45, 45, 45), card_rect.width, card_rect.height, 8), card_rect.topleft)
                    elif track["path"] in green_toggled_tracks and track["title"] == current_track["title"]:
                        virtual_surface.blit(_cached_rounded_rect(COLOR_SPOTIFY_GREEN, card_rect.width, card_rect.height, 8, width=2), card_rect.topleft)
                    elif is_card_hovered:
                        virtual_surface.blit(_cached_rounded_rect(COLOR_HOVER, card_rect.width, card_rect.height, 8), card_rect.topleft)
                    else:
                        virtual_surface.blit(_cached_rounded_rect(COLOR_CARD_BG, card_rect.width, card_rect.height, 8), card_rect.topleft)
                    
                    cover_rect = pygame.Rect(box_x + 12, box_y + 12, card_width - 24, card_height - 24)
                    virtual_surface.blit(_cached_rounded_rect(COLOR_LIGHT_GREY, cover_rect.width, cover_rect.height, 6), cover_rect.topleft)
                    if track.get("cover_surface"):
                        src_surf = track["cover_surface"]
                        box_w, box_h = cover_rect.width, cover_rect.height
                        cropped_cover = _cached_masked_cover(src_surf, box_w, box_h)
                        virtual_surface.blit(cropped_cover, (cover_rect.x, cover_rect.y))
                    
                    if track["title"] == current_track["title"]:
                        title_color = COLOR_SPOTIFY_GREEN
                        sub_color = COLOR_TEXT_MUTED
                    else:
                        title_color = COLOR_WHITE
                        sub_color = COLOR_TEXT_MUTED
                        
                    max_text_w = card_width - 24

                    title_text = track["title"]
                    title_surf = _cached_render(font_small, title_text, True, title_color)
                    if title_surf.get_width() > max_text_w:
                        while title_text and font_small.size(title_text + "...")[0] > max_text_w:
                            title_text = title_text[:-1]
                        title_surf = _cached_render(font_small, title_text + "...", True, title_color)
                    virtual_surface.blit(title_surf, (box_x + 12, box_y + card_height - 4))

                    sub_text = track["album"]
                    sub_surf = _cached_render(font_small, sub_text, True, sub_color)
                    if sub_surf.get_width() > max_text_w:
                        while sub_text and font_small.size(sub_text + "...")[0] > max_text_w:
                            sub_text = sub_text[:-1]
                        sub_surf = _cached_render(font_small, sub_text + "...", True, sub_color)
                    virtual_surface.blit(sub_surf, (box_x + 12, box_y + card_height + 14))
            virtual_surface.set_clip(None)

    # --- DEDICATED PERSONALIZE / THEME PAGE (opened from Settings) ---
    elif show_theme_page:
        global theme_option_rects, font_option_rects, max_theme_page_scroll
        theme_option_rects = []
        font_option_rects = []

        theme_order = ["classic", "midnight", "sunset", "rainbow", "neon", "pastel",
                        "galaxy", "vaporwave", "tropical", "candy", "firestorm", "arctic",
                        "carnival", "bubblegum", "citrus", "cosmic_candy", "disco", "high_contrast"]

        page_bg_theme = THEMES[current_theme]
        page_body_rect = pygame.Rect(main_x, 0, main_w, HEIGHT - portrait_sidebar_h)
        if page_bg_theme.get("gradient"):
            draw_multicolor_gradient(virtual_surface, page_body_rect, page_bg_theme["gradient"])
        else:
            pygame.draw.rect(virtual_surface, COLOR_BLACK, page_body_rect)

        page_title = _cached_render(font_title, t("Personalize"), True, COLOR_WHITE)
        virtual_surface.blit(page_title, (content_pad_x, 40))
        sub_surf = _cached_render(font_small, t("Pick a color theme, then a font, for the whole app"), True, COLOR_TEXT_MUTED)
        virtual_surface.blit(sub_surf, (content_pad_x, 68))

        subpage_back_rect = pygame.Rect(main_x + main_w - (130 if is_portrait else 250), 35, 90, 35)
        sb_hov = subpage_back_rect.collidepoint(mouse_pos)
        sb_clk = sb_hov and mouse_held
        sb_color = (30, 30, 30) if sb_clk else (COLOR_HOVER if sb_hov else COLOR_LIGHT_GREY)
        pygame.draw.rect(virtual_surface, sb_color, subpage_back_rect, border_radius=15)
        sb_lbl = _cached_render(font_small, t("Back"), True, COLOR_WHITE)
        virtual_surface.blit(sb_lbl, (subpage_back_rect.x + 26, 44))

        body_top = 100
        body_h = HEIGHT - portrait_sidebar_h - body_top
        body_rect = pygame.Rect(main_x, body_top, main_w, body_h)
        virtual_surface.set_clip(body_rect)

        scroll = round(theme_page_scroll_offset)

        # --- THEMES SECTION ---
        section_lbl = _cached_render(font_body, t("Color Themes"), True, COLOR_WHITE)
        virtual_surface.blit(section_lbl, (content_pad_x, body_top + 10 - scroll))

        grid_top = body_top + 45 - scroll
        card_gap = 16
        cols = 1 if main_w < 480 else 2
        card_w = (main_w - 60 - (card_gap * (cols - 1))) // cols
        card_h = 118

        for idx, theme_key in enumerate(theme_order):
            theme = THEMES[theme_key]
            col = idx % cols
            row = idx // cols
            card_x = content_pad_x + col * (card_w + card_gap)
            card_y = grid_top + row * (card_h + card_gap)
            card_rect = pygame.Rect(card_x, card_y, card_w, card_h)

            if card_rect.bottom < body_top or card_rect.top > body_top + body_h:
                continue
            theme_option_rects.append((card_rect, theme_key))

            is_active = (theme_key == current_theme)
            is_hovered = card_rect.collidepoint(mouse_pos)

            pygame.draw.rect(virtual_surface, theme["COLOR_CARD_BG"], card_rect, border_radius=12)

            # Fun multi-color top strip — either a real gradient sweep, or
            # (for the flat themes) a row of that theme's own varied colors
            if theme.get("gradient"):
                strip_colors = theme["gradient"]
            else:
                strip_colors = [theme["COLOR_SPOTIFY_GREEN"], theme["COLOR_RED"], theme["COLOR_HOVER"], theme["COLOR_LIGHT_GREY"]]
            seg_w = max(1, card_w // len(strip_colors))
            for si, sc in enumerate(strip_colors):
                pygame.draw.rect(virtual_surface, sc, (card_x + si * seg_w, card_y, seg_w + 1, 14))

            border_color = theme["COLOR_SPOTIFY_GREEN"] if is_active else (COLOR_WHITE if is_hovered else theme["COLOR_LIGHT_GREY"])
            pygame.draw.rect(virtual_surface, border_color, card_rect, width=3, border_radius=12)

            # Swatches showing this theme's key colors
            swatch_colors = [theme["COLOR_BLACK"], theme["COLOR_SPOTIFY_GREEN"], theme["COLOR_RED"], theme["COLOR_CARD_BG"]]
            sw_x = card_x + 18
            sw_y = card_y + 32
            for sw_color in swatch_colors:
                pygame.draw.rect(virtual_surface, sw_color, (sw_x, sw_y, 34, 34), border_radius=6)
                pygame.draw.rect(virtual_surface, theme["COLOR_WHITE"], (sw_x, sw_y, 34, 34), width=1, border_radius=6)
                sw_x += 42

            name_surf = _cached_render(font_body, theme["label"], True, theme["COLOR_WHITE"])
            virtual_surface.blit(name_surf, (card_x + 18, card_y + 76))
            if is_active:
                active_surf = _cached_render(font_small, t("Active"), True, theme["COLOR_SPOTIFY_GREEN"])
                virtual_surface.blit(active_surf, (card_x + 18, card_y + 98))
            elif is_hovered:
                tap_surf = _cached_render(font_small, t("Tap to apply"), True, theme["COLOR_TEXT_MUTED"])
                virtual_surface.blit(tap_surf, (card_x + 18, card_y + 98))

        theme_rows = (len(theme_order) + cols - 1) // cols
        themes_bottom = grid_top + theme_rows * (card_h + card_gap)

        # --- DIVIDER LINE (everything below changes the app-wide font) ---
        divider_y = themes_bottom + 10
        pygame.draw.line(virtual_surface, COLOR_LIGHT_GREY,
                          (content_pad_x, divider_y), (main_x + main_w - 30, divider_y), 2)

        # --- FONTS SECTION ---
        font_section_top = divider_y + 25
        section_lbl2 = _cached_render(font_body, t("App Font"), True, COLOR_WHITE)
        virtual_surface.blit(section_lbl2, (content_pad_x, font_section_top))
        sub2 = _cached_render(font_small, t("Changes the font used everywhere in the app"), True, COLOR_TEXT_MUTED)
        virtual_surface.blit(sub2, (content_pad_x, font_section_top + 24))

        font_row_top = font_section_top + 55
        font_gap = 14
        font_cols = 1 if main_w < 420 else (2 if main_w < 700 else 5)
        font_box_w = (main_w - 60 - (font_gap * (font_cols - 1))) // font_cols
        font_box_h = 90
        font_order = ["classic"]

        for fidx, font_key in enumerate(font_order):
            fdef = FONTS[font_key]
            fcol = fidx % font_cols
            frow = fidx // font_cols
            fbox_x = content_pad_x + fcol * (font_box_w + font_gap)
            fbox_y = font_row_top + frow * (font_box_h + font_gap)
            fbox_rect = pygame.Rect(fbox_x, fbox_y, font_box_w, font_box_h)

            if fbox_rect.bottom < body_top or fbox_rect.top > body_top + body_h:
                continue
            font_option_rects.append((fbox_rect, font_key))

            is_font_active = (font_key == current_font_family)
            is_font_hovered = fbox_rect.collidepoint(mouse_pos)

            box_bg = COLOR_HOVER if (is_font_hovered and not is_font_active) else COLOR_CARD_BG
            pygame.draw.rect(virtual_surface, box_bg, fbox_rect, border_radius=10)
            fborder = COLOR_SPOTIFY_GREEN if is_font_active else (COLOR_WHITE if is_font_hovered else COLOR_LIGHT_GREY)
            pygame.draw.rect(virtual_surface, fborder, fbox_rect, width=3, border_radius=10)

            # Preview this font's own family, not the currently-applied one
            preview_font = get_preview_font(fdef["family"], 20, bold=True)
            preview_surf = preview_font.render("Aa", True, COLOR_WHITE)
            virtual_surface.blit(preview_surf, (fbox_x + (font_box_w - preview_surf.get_width()) // 2, fbox_y + 14))

            label_font = get_preview_font(fdef["family"], 14)
            label_surf = label_font.render(fdef["label"], True, COLOR_TEXT_MUTED)
            virtual_surface.blit(label_surf, (fbox_x + (font_box_w - label_surf.get_width()) // 2, fbox_y + 44))
            if is_font_active:
                act_surf = _cached_render(font_small, t("Active"), True, COLOR_SPOTIFY_GREEN)
                virtual_surface.blit(act_surf, (fbox_x + (font_box_w - act_surf.get_width()) // 2, fbox_y + 66))

        font_rows = (len(font_order) + font_cols - 1) // font_cols
        content_bottom = font_row_top + font_rows * (font_box_h + font_gap)

        virtual_surface.set_clip(None)
        doc_content_bottom = content_bottom + scroll
        max_theme_page_scroll = max(0, doc_content_bottom - (body_top + body_h) + 30)

    # --- DEDICATED LANGUAGE PAGE (opened from Settings) ---
    elif show_language_page:
        global language_option_rects
        language_option_rects = []

        pygame.draw.rect(virtual_surface, COLOR_BLACK, (main_x, 0, main_w, HEIGHT - portrait_sidebar_h))

        page_title = _cached_render(font_title, t("Language"), True, COLOR_WHITE)
        virtual_surface.blit(page_title, (content_pad_x, 40))
        sub_surf = _cached_render(font_small, t("Choose your preferred language"), True, COLOR_TEXT_MUTED)
        virtual_surface.blit(sub_surf, (content_pad_x, 68))

        subpage_back_rect = pygame.Rect(main_x + main_w - (130 if is_portrait else 250), 35, 90, 35)
        sb_hov = subpage_back_rect.collidepoint(mouse_pos)
        sb_clk = sb_hov and mouse_held
        sb_color = (30, 30, 30) if sb_clk else (COLOR_HOVER if sb_hov else COLOR_LIGHT_GREY)
        pygame.draw.rect(virtual_surface, sb_color, subpage_back_rect, border_radius=15)
        sb_lbl = _cached_render(font_small, t("Back"), True, COLOR_WHITE)
        virtual_surface.blit(sb_lbl, (subpage_back_rect.x + 26, 44))

        # Each language's own native name + a short code chip, for polish
        LANGUAGE_NATIVE = {
            "English": ("English", "EN"), "Spanish": ("Español", "ES"), "French": ("Français", "FR"),
            "German": ("Deutsch", "DE"), "Italian": ("Italiano", "IT"), "Portuguese": ("Português", "PT"),
            "Polish": ("Polski", "PL"),
        }

        grid_top = 105
        gap = 14
        cols = 1 if main_w < 420 else (2 if main_w < 700 else 3)
        box_w = (main_w - 60 - (gap * (cols - 1))) // cols
        box_h = 68

        for idx, lang in enumerate(LANGUAGES):
            col = idx % cols
            row = idx // cols
            box_x = content_pad_x + col * (box_w + gap)
            box_y = grid_top + row * (box_h + gap)
            box_rect = pygame.Rect(box_x, box_y, box_w, box_h)
            language_option_rects.append((box_rect, lang))

            is_active = (lang == current_language)
            is_hovered = box_rect.collidepoint(mouse_pos)
            native_name, code = LANGUAGE_NATIVE.get(lang, (lang, lang[:2].upper()))

            box_bg = COLOR_HOVER if (is_hovered and not is_active) else COLOR_CARD_BG
            pygame.draw.rect(virtual_surface, box_bg, box_rect, border_radius=12)
            border_color = COLOR_SPOTIFY_GREEN if is_active else (COLOR_WHITE if is_hovered else COLOR_LIGHT_GREY)
            pygame.draw.rect(virtual_surface, border_color, box_rect, width=3, border_radius=12)

            # Small rounded code chip on the left, like a mini flag badge
            chip_rect = pygame.Rect(box_x + 14, box_y + (box_h - 36) // 2, 44, 36)
            chip_bg = COLOR_SPOTIFY_GREEN if is_active else COLOR_LIGHT_GREY
            chip_text_color = COLOR_BLACK if is_active else COLOR_WHITE
            pygame.draw.rect(virtual_surface, chip_bg, chip_rect, border_radius=8)
            code_surf = _cached_render(font_small, code, True, chip_text_color)
            virtual_surface.blit(code_surf, (chip_rect.x + (chip_rect.width - code_surf.get_width()) // 2,
                                              chip_rect.y + (chip_rect.height - code_surf.get_height()) // 2))

            text_x = chip_rect.right + 14
            lang_surf = _cached_render(font_body, lang, True, COLOR_WHITE)
            virtual_surface.blit(lang_surf, (text_x, box_y + 12))
            native_surf = _cached_render(font_small, native_name, True, COLOR_TEXT_MUTED)
            virtual_surface.blit(native_surf, (text_x, box_y + 36))

            if is_active:
                check_surf = _cached_render(font_small, t("Active"), True, COLOR_SPOTIFY_GREEN)
                virtual_surface.blit(check_surf, (box_x + box_w - check_surf.get_width() - 14, box_y + (box_h - check_surf.get_height()) // 2))

    # --- SETTINGS PAGE (sidebar tab) ---
    elif current_page == "Settings":
        settings_page_title = _cached_render(font_title, t("Settings"), True, COLOR_WHITE)
        virtual_surface.blit(settings_page_title, (content_pad_x, 40))

        btn_w, btn_h = 160, 40
        btn_gap = 20
        btn_y = 100
        row_h = btn_h + btn_gap  # vertical spacing between rows

        # Build the ordered list of buttons that should actually appear right
        # now, then lay them out as a centered grid. Centering is per-row (not
        # just per-page), so a trailing partial row — e.g. a lone Resolution
        # button — still ends up centered rather than stuck on the left.
        _settings_btn_keys = []
        if _debug_reveal:
            _settings_btn_keys += ["desktop", "phone"]
        _settings_btn_keys += ["grid_toggle", "theme", "language", "font_size"]
        if IS_ANDROID:
            _settings_btn_keys.append("haptics")
        if not IS_ANDROID:
            _settings_btn_keys.append("resolution")

        # Desktop/Tablet layout gets more buttons per row than Phone layout
        # since it usually has more width to work with - but "usually" isn't
        # "always": in portrait orientation, Desktop/Tablet's content area is
        # only 700px wide (vs. ~1100px in landscape), which isn't wide enough
        # to fit a fixed 4-per-row layout (4 buttons + gaps needs 700px, but
        # only ~640px is actually available after margins) - that's what was
        # pushing the last button in each row off the right edge. Instead of
        # a fixed column count per layout_mode, size it to the width that's
        # actually available this frame, so it degrades gracefully at any
        # width/orientation instead of assuming a specific one. This still
        # resolves to the same 4 columns in Desktop/Tablet landscape and 2 in
        # Phone portrait as before - it just also handles the width in
        # between (Desktop/Tablet portrait) correctly instead of clipping.
        _avail_w = main_w - 60  # content_pad_x is main_x+30; mirror that as a symmetric right margin
        _cols_per_row = max(1, min(4, (_avail_w + btn_gap) // (btn_w + btn_gap)))

        _settings_btn_rects = {}
        for _i, _key in enumerate(_settings_btn_keys):
            _row = _i // _cols_per_row
            _col = _i % _cols_per_row
            _row_keys = _settings_btn_keys[_row * _cols_per_row: _row * _cols_per_row + _cols_per_row]
            _row_n = len(_row_keys)
            _row_w = _row_n * btn_w + (_row_n - 1) * btn_gap
            _row_start_x = content_pad_x + max(0, (_avail_w - _row_w) // 2)
            _settings_btn_rects[_key] = pygame.Rect(
                _row_start_x + _col * (btn_w + btn_gap), btn_y + _row * row_h, btn_w, btn_h
            )

        _empty_rect = pygame.Rect(0, 0, 0, 0)
        desktop_btn_rect       = _settings_btn_rects.get("desktop", _empty_rect)
        phone_btn_rect         = _settings_btn_rects.get("phone", _empty_rect)
        grid_toggle_btn_rect   = _settings_btn_rects.get("grid_toggle", _empty_rect)
        theme_btn_rect          = _settings_btn_rects.get("theme", _empty_rect)
        language_btn_rect       = _settings_btn_rects.get("language", _empty_rect)
        font_size_btn_rect      = _settings_btn_rects.get("font_size", _empty_rect)
        haptics_btn_rect        = _settings_btn_rects.get("haptics", _empty_rect)
        resolution_btn_rect     = _settings_btn_rects.get("resolution", _empty_rect)

        # Desktop/Tablet & Phone layout buttons — hidden by default, press F5 to reveal
        is_dt_hovered = desktop_btn_rect.collidepoint(mouse_pos) and _debug_reveal
        is_ph_hovered = phone_btn_rect.collidepoint(mouse_pos) and _debug_reveal
        if _debug_reveal:
            # Desktop/Tablet button — green when active
            is_dt_clicked = is_dt_hovered and mouse_held
            if layout_mode == "desktop":
                dt_color = COLOR_SPOTIFY_GREEN
                dt_text_color = COLOR_BLACK
            elif is_dt_clicked:
                dt_color = (20, 150, 65)
                dt_text_color = COLOR_WHITE
            elif is_dt_hovered:
                dt_color = COLOR_SPOTIFY_GREEN
                dt_text_color = COLOR_BLACK
            else:
                dt_color = COLOR_LIGHT_GREY
                dt_text_color = COLOR_WHITE
            pygame.draw.rect(virtual_surface, dt_color, desktop_btn_rect, border_radius=20)
            dt_lbl = render_fit_text(t("Desktop/Tablet"), dt_text_color, btn_w - 16)
            dt_lbl_x = desktop_btn_rect.x + (btn_w - dt_lbl.get_width()) // 2
            dt_lbl_y = desktop_btn_rect.y + (btn_h - dt_lbl.get_height()) // 2
            virtual_surface.blit(dt_lbl, (dt_lbl_x, dt_lbl_y))

            # Phone button — green when active
            is_ph_clicked = is_ph_hovered and mouse_held
            if layout_mode == "phone":
                ph_color = COLOR_SPOTIFY_GREEN
                ph_text_color = COLOR_BLACK
            elif is_ph_clicked:
                ph_color = (20, 150, 65)
                ph_text_color = COLOR_WHITE
            elif is_ph_hovered:
                ph_color = COLOR_SPOTIFY_GREEN
                ph_text_color = COLOR_BLACK
            else:
                ph_color = COLOR_LIGHT_GREY
                ph_text_color = COLOR_WHITE
            pygame.draw.rect(virtual_surface, ph_color, phone_btn_rect, border_radius=20)
            ph_lbl = render_fit_text(t("Phone"), ph_text_color, btn_w - 16)
            ph_lbl_x = phone_btn_rect.x + (btn_w - ph_lbl.get_width()) // 2
            ph_lbl_y = phone_btn_rect.y + (btn_h - ph_lbl.get_height()) // 2
            virtual_surface.blit(ph_lbl, (ph_lbl_x, ph_lbl_y))

        # Grid columns button
        gt_hovered = grid_toggle_btn_rect.collidepoint(mouse_pos)
        gt_clicked = gt_hovered and mouse_held
        gt_color = (30, 30, 30) if gt_clicked else (COLOR_HOVER if gt_hovered else COLOR_LIGHT_GREY)
        pygame.draw.rect(virtual_surface, gt_color, grid_toggle_btn_rect, border_radius=20)
        if layout_mode == "phone":
            _grid_lbl_n = grid_cols_override if grid_cols_override else 2
        else:
            _grid_lbl_n = grid_cols_override if grid_cols_override else 5
        gt_lbl = render_fit_text(f"{t('Grid')}: {_grid_lbl_n}", COLOR_WHITE, btn_w - 16)
        gt_lbl_x = grid_toggle_btn_rect.x + (btn_w - gt_lbl.get_width()) // 2
        gt_lbl_y = grid_toggle_btn_rect.y + (btn_h - gt_lbl.get_height()) // 2
        virtual_surface.blit(gt_lbl, (gt_lbl_x, gt_lbl_y))

        # Personalize button — opens the theme/color picker page
        th_hovered = theme_btn_rect.collidepoint(mouse_pos)
        th_clicked = th_hovered and mouse_held
        th_color = (20, 150, 65) if th_clicked else (COLOR_SPOTIFY_GREEN if th_hovered else COLOR_LIGHT_GREY)
        th_text_color = COLOR_BLACK if (th_hovered or th_clicked) else COLOR_WHITE
        pygame.draw.rect(virtual_surface, th_color, theme_btn_rect, border_radius=20)
        th_lbl = render_fit_text(t("Personalize"), th_text_color, btn_w - 16)
        th_lbl_x = theme_btn_rect.x + (btn_w - th_lbl.get_width()) // 2
        th_lbl_y = theme_btn_rect.y + (btn_h - th_lbl.get_height()) // 2
        virtual_surface.blit(th_lbl, (th_lbl_x, th_lbl_y))

        # Language button — opens the language picker page
        lg_hovered = language_btn_rect.collidepoint(mouse_pos)
        lg_clicked = lg_hovered and mouse_held
        lg_color = (20, 150, 65) if lg_clicked else (COLOR_SPOTIFY_GREEN if lg_hovered else COLOR_LIGHT_GREY)
        lg_text_color = COLOR_BLACK if (lg_hovered or lg_clicked) else COLOR_WHITE
        pygame.draw.rect(virtual_surface, lg_color, language_btn_rect, border_radius=20)
        lg_lbl = render_fit_text(t("Language"), lg_text_color, btn_w - 16)
        lg_lbl_x = language_btn_rect.x + (btn_w - lg_lbl.get_width()) // 2
        lg_lbl_y = language_btn_rect.y + (btn_h - lg_lbl.get_height()) // 2
        virtual_surface.blit(lg_lbl, (lg_lbl_x, lg_lbl_y))

        # Font Size — cycles Small/Medium/Large
        fs_hovered = font_size_btn_rect.collidepoint(mouse_pos)
        fs_clicked = fs_hovered and mouse_held
        fs_color = (30, 30, 30) if fs_clicked else (COLOR_HOVER if fs_hovered else COLOR_LIGHT_GREY)
        pygame.draw.rect(virtual_surface, fs_color, font_size_btn_rect, border_radius=20)
        fs_lbl = render_fit_text(f"{t('Font')}: {t(current_font_size_label())}", COLOR_WHITE, btn_w - 16)
        fs_lbl_x = font_size_btn_rect.x + (btn_w - fs_lbl.get_width()) // 2
        fs_lbl_y = font_size_btn_rect.y + (btn_h - fs_lbl.get_height()) // 2
        virtual_surface.blit(fs_lbl, (fs_lbl_x, fs_lbl_y))

        # Haptics — on/off toggle (Android only; vibrates on button taps)
        if IS_ANDROID:
            hp_hovered = haptics_btn_rect.collidepoint(mouse_pos)
            hp_clicked = hp_hovered and mouse_held
            if haptics_enabled or hp_hovered:
                hp_color, hp_text_color = COLOR_SPOTIFY_GREEN, COLOR_BLACK
            elif hp_clicked:
                hp_color, hp_text_color = (20, 150, 65), COLOR_WHITE
            else:
                hp_color, hp_text_color = COLOR_LIGHT_GREY, COLOR_WHITE
            pygame.draw.rect(virtual_surface, hp_color, haptics_btn_rect, border_radius=20)
            hp_lbl = render_fit_text(f"{t('Haptics')}: {t('On') if haptics_enabled else t('Off')}", hp_text_color, btn_w - 16)
            hp_lbl_x = haptics_btn_rect.x + (btn_w - hp_lbl.get_width()) // 2
            hp_lbl_y = haptics_btn_rect.y + (btn_h - hp_lbl.get_height()) // 2
            virtual_surface.blit(hp_lbl, (hp_lbl_x, hp_lbl_y))

        # Resolution button — PC/desktop-window only (Android is fullscreen and
        # the resolution isn't user-adjustable there, so there's nothing for
        # this to do on-device). Shows the current window size; click resets
        # the window back to 1080p, which is also what it always starts at.
        if not IS_ANDROID:
            res_hovered = resolution_btn_rect.collidepoint(mouse_pos)
            res_clicked = res_hovered and mouse_held
            res_color = (20, 150, 65) if res_clicked else (COLOR_SPOTIFY_GREEN if res_hovered else COLOR_LIGHT_GREY)
            res_text_color = COLOR_BLACK if (res_hovered or res_clicked) else COLOR_WHITE
            pygame.draw.rect(virtual_surface, res_color, resolution_btn_rect, border_radius=20)
            res_lbl = render_fit_text(f"{REAL_WIDTH}x{REAL_HEIGHT}", res_text_color, btn_w - 16)
            res_lbl_x = resolution_btn_rect.x + (btn_w - res_lbl.get_width()) // 2
            res_lbl_y = resolution_btn_rect.y + (btn_h - res_lbl.get_height()) // 2
            virtual_surface.blit(res_lbl, (res_lbl_x, res_lbl_y))

    # --- YOUR LIBRARY GRID VIEW ---
    elif current_page == "Your Library":
        lib_title = _cached_render(font_title, t("Your Library"), True, COLOR_WHITE)
        virtual_surface.blit(lib_title, (content_pad_x, 40))
        
        create_playlist_btn_rect = pygame.Rect(content_pad_x + lib_title.get_width() + 20, 35, 40, 40)
        is_cp_hovered = create_playlist_btn_rect.collidepoint(mouse_pos)
        is_cp_clicked = is_cp_hovered and mouse_held
        
        if is_cp_clicked:
            cp_box_color = (20, 150, 65)
            cp_text_color = COLOR_WHITE
        elif is_cp_hovered:
            cp_box_color = COLOR_SPOTIFY_GREEN
            cp_text_color = COLOR_BLACK
        else:
            cp_box_color = COLOR_LIGHT_GREY
            cp_text_color = COLOR_WHITE
            
        pygame.draw.rect(virtual_surface, cp_box_color, create_playlist_btn_rect, border_radius=20)
        cp_plus_surf = _cached_render(font_body, "+", True, cp_text_color)
        
        plus_x = create_playlist_btn_rect.x + (create_playlist_btn_rect.width - cp_plus_surf.get_width()) // 2
        plus_y = create_playlist_btn_rect.y + (create_playlist_btn_rect.height - cp_plus_surf.get_height()) // 2
        virtual_surface.blit(cp_plus_surf, (plus_x, plus_y))
        
        liked_songs_card_rect = pygame.Rect(content_pad_x, 95, 160, 200)
        is_lib_hovered = liked_songs_card_rect.collidepoint(mouse_pos)
        is_lib_clicked = is_lib_hovered and mouse_held
        
        if is_lib_clicked:
            pygame.draw.rect(virtual_surface, (45, 45, 45), liked_songs_card_rect, border_radius=8)
        elif is_lib_hovered:
            pygame.draw.rect(virtual_surface, COLOR_HOVER, liked_songs_card_rect, border_radius=8)
        else:
            pygame.draw.rect(virtual_surface, COLOR_CARD_BG, liked_songs_card_rect, border_radius=8)
            
        if liked_songs_custom_cover["surface"]:
            disp_thumb = _cached_scale(liked_songs_custom_cover["surface"], (130, 110))
            virtual_surface.blit(disp_thumb, (content_pad_x + 15, 110))
        else:
            pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, (content_pad_x + 15, 110, 130, 110), border_radius=4)
            draw_manual_thumbs_up(virtual_surface, content_pad_x + 55, 140, 50, 50, COLOR_BLACK)
        
        card_txt1 = _cached_render(font_body, t("Liked Songs"), True, COLOR_WHITE)
        card_txt2 = _cached_render(font_small, f"Playlist • {len(liked_tracks)} songs", True, COLOR_TEXT_MUTED)
        virtual_surface.blit(card_txt1, (content_pad_x + 15, 230))
        virtual_surface.blit(card_txt2, (content_pad_x + 15, 255))

        start_x = content_pad_x
        start_y = 95
        card_w, card_h = 160, 200
        gap_x, gap_y = 20, 20
        columns_count = (main_w - 20) // (card_w + gap_x)
        if columns_count < 1: columns_count = 1
        
        for idx, p_name in enumerate(list(custom_playlists.keys())):
            layout_index = idx + 1
            col = layout_index % columns_count
            row = layout_index // columns_count
            
            box_x = start_x + (col * (card_w + gap_x))
            box_y = start_y + (row * (card_h + gap_y)) - round(music_grid_scroll_offset)
            
            c_rect = pygame.Rect(box_x, box_y, card_w, card_h)
            custom_playlist_rects.append((c_rect, p_name))
            
            is_c_hover = c_rect.collidepoint(mouse_pos)
            if is_c_hover and mouse_held:
                pygame.draw.rect(virtual_surface, (45, 45, 45), c_rect, border_radius=8)
            elif is_c_hover:
                pygame.draw.rect(virtual_surface, COLOR_HOVER, c_rect, border_radius=8)
            else:
                pygame.draw.rect(virtual_surface, COLOR_CARD_BG, c_rect, border_radius=8)
                
            cover_frame = pygame.Rect(box_x + 15, box_y + 15, 130, 110)
            if custom_playlists[p_name]["surface"]:
                disp_thumb = _cached_scale(custom_playlists[p_name]["surface"], (130, 110))
                virtual_surface.blit(disp_thumb, (box_x + 15, box_y + 15))
            else:
                pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, cover_frame, border_radius=4)
                draw_spotify_pencil(virtual_surface, box_x + 80, box_y + 70, COLOR_BLACK)
                
            name_lbl = _cached_render(font_body, p_name if len(p_name) <= 14 else p_name[:12] + "...", True, COLOR_WHITE)
            count_lbl = _cached_render(font_small, f"Playlist • {len(custom_playlists[p_name]['tracks'])} tracks", True, COLOR_TEXT_MUTED)
            virtual_surface.blit(name_lbl, (box_x + 15, box_y + 135))
            virtual_surface.blit(count_lbl, (box_x + 15, box_y + 160))

def _wrap_text_lines(text, font, max_width):
    """Simple word-wrap: splits text into a list of lines that each fit
    within max_width when rendered with the given font."""
    words = text.split(" ")
    lines = []
    current = ""
    for word in words:
        trial = (current + " " + word).strip()
        if font.size(trial)[0] <= max_width or not current:
            current = trial
        else:
            lines.append(current)
            current = word
    if current:
        lines.append(current)
    return lines

# --- FIRST-LAUNCH ONBOARDING OVERLAY ---
def _draw_onboarding_icon(surface, center, kind, size, color):
    """Small vector glyphs for the onboarding cards - drawn with plain shapes
    (no image assets needed) so they always match the current accent color."""
    cx, cy = center
    r = size / 2
    if kind == "folder":
        w, h = size, size * 0.72
        x, y = cx - w / 2, cy - h / 2
        tab_w, tab_h = w * 0.42, h * 0.24
        pygame.draw.rect(surface, color, (x, y + tab_h, w, h - tab_h), border_radius=6)
        pygame.draw.rect(surface, color, (x, y, tab_w, tab_h + 6), border_radius=4)
    elif kind == "sparkle":
        def _star(sx, sy, sr):
            pts = []
            for i in range(8):
                ang = i * (math.pi / 4)
                rad = sr if i % 2 == 0 else sr * 0.32
                pts.append((sx + rad * math.sin(ang), sy - rad * math.cos(ang)))
            pygame.draw.polygon(surface, color, pts)
        _star(cx - r * 0.12, cy - r * 0.12, r)
        _star(cx + r * 0.62, cy + r * 0.55, r * 0.4)


def _ease_out_cubic(t):
    t = max(0.0, min(1.0, t))
    return 1 - (1 - t) ** 3


def _ease_out_back(t, overshoot=1.6):
    t = max(0.0, min(1.0, t))
    t -= 1
    return t * t * ((overshoot + 1) * t + overshoot) + 1


def _smooth_hover(key, hovered, rate=0.30):
    """Eases a per-button hover amount towards 0/1 instead of snapping, so
    hover/press color and scale changes feel like a real transition rather
    than a hard flip. Persists across frames in _onboarding_hover_smooth."""
    global _onboarding_hover_smooth
    current = _onboarding_hover_smooth.get(key, 0.0)
    target = 1.0 if hovered else 0.0
    current += (target - current) * rate
    if abs(current - target) < 0.004:
        current = target
    _onboarding_hover_smooth[key] = current
    return current


def _lerp_color(c1, c2, t):
    t = max(0.0, min(1.0, t))
    return (int(c1[0] + (c2[0] - c1[0]) * t),
            int(c1[1] + (c2[1] - c1[1]) * t),
            int(c1[2] + (c2[2] - c1[2]) * t))


def _ease_out_elastic(t):
    """Classic elastic-out easing - overshoots past the target and settles
    back like a rubber band. t is 0..1."""
    if t <= 0:
        return 0.0
    if t >= 1:
        return 1.0
    c4 = (2 * math.pi) / 3
    return (2 ** (-10 * t)) * math.sin((t * 10 - 0.75) * c4) + 1


def _blit_rubber_band_line(surface, text_surf, target_center, elapsed, delay=0.0, duration=0.7, from_left=True):
    """Blits a pre-rendered text surface sliding in from off-screen to
    target_center with an elastic/rubber-band settle. Returns True once the
    entrance animation has fully finished (so callers can chain follow-up
    fades)."""
    t = max(0.0, min(1.0, (elapsed - delay) / duration))
    if elapsed < delay:
        return False
    eased = _ease_out_elastic(t)
    off_x = -WIDTH * 0.9 if from_left else WIDTH * 0.9
    cur_x = target_center[0] + off_x * (1 - eased)
    surface.blit(text_surf, text_surf.get_rect(center=(int(cur_x), target_center[1])))
    return t >= 1.0


def draw_onboarding_overlay():
    """Full-screen first-launch flow: animated green welcome screen, then a
    notifications-permission screen, then a storage/files-permission screen.
    Drawn on top of everything else and owns all clicks while active (see the
    onboarding_stage check in the main event loop)."""
    global onboarding_button_rect, onboarding_button_rect_2, onboarding_skip_rect

    # A darker shade of the app's own brand green (COLOR_SPOTIFY_GREEN), used
    # everywhere else in SpotM-Fi for accents/buttons/liked icon - kept as the
    # same hue rather than a new color so onboarding still feels on-brand.
    ONBOARDING_GREEN = (18, 158, 71)
    virtual_surface.fill(ONBOARDING_GREEN)
    center_x = WIDTH // 2
    center_y = HEIGHT // 2
    elapsed = time.time() - onboarding_anim_start

    if onboarding_stage == "welcome":
        # Title rubber-bands in from the left, subtext fades in once it settles.
        anim_dur = 0.7
        title_surf = render_fit_text("Welcome to SpotM-Fi", COLOR_BLACK, WIDTH - 80, base_size=48, bold=True, min_size=24)
        target_y = center_y - 10
        settled = _blit_rubber_band_line(virtual_surface, title_surf, (center_x, target_y), elapsed, delay=0.0, duration=anim_dur, from_left=True)

        # Subtext fades in once the title has essentially settled in place.
        if settled or elapsed >= anim_dur * 0.9:
            fade_elapsed = elapsed - (anim_dur * 0.9)
            fade_alpha = max(0, min(255, int(fade_elapsed * 500)))
            sub_surf = _cached_render(font_title, "Click/tap anywhere to continue", True, COLOR_BLACK)
            sub_surf.set_alpha(fade_alpha)
            virtual_surface.blit(sub_surf, sub_surf.get_rect(center=(center_x, target_y + 55)))

        onboarding_button_rect = None  # the whole screen is the "button" on this stage
        onboarding_button_rect_2 = None
        onboarding_skip_rect = None
        return

    onboarding_button_rect_2 = None
    onboarding_skip_rect = None

    if onboarding_stage == "notifications":
        heading = "First we need permission to give you notifications"
        button_label = "Allow Notifications"
    elif onboarding_stage == "storage":
        heading = "Now give us access to your files so you can find your music"
        button_label = "Give File Access"

    if onboarding_stage in ("notifications", "storage"):
        lines = _wrap_text_lines(heading, font_huge, WIDTH - 140)
        if len(lines) == 1 and font_huge.size(lines[0])[0] > WIDTH - 140:
            lines = _wrap_text_lines(heading, font_title, WIDTH - 140)
            line_font = font_title
        else:
            line_font = font_huge
        line_h = line_font.get_height() + 4
        block_h = line_h * len(lines)
        start_y = center_y - 90 - block_h // 2
        for i, line in enumerate(lines):
            line_surf = line_font.render(line, True, COLOR_BLACK)
            # Each line rubber-bands in from alternating sides, staggered
            # slightly so a multi-line heading doesn't all snap in at once.
            _blit_rubber_band_line(
                virtual_surface, line_surf,
                (center_x, start_y + i * line_h + line_h // 2),
                elapsed, delay=i * 0.1, duration=0.7, from_left=(i % 2 == 0)
            )

        mouse_pos = get_virtual_mouse_pos()
        btn_w, btn_h = 300, 60
        btn_rect = pygame.Rect(0, 0, btn_w, btn_h)
        btn_rect.center = (center_x, center_y + 90)
        waiting = onboarding_awaiting_permission
        hovered = (not waiting) and btn_rect.collidepoint(mouse_pos)
        hv = _smooth_hover("perm_btn", hovered)
        fill = _lerp_color(COLOR_DARK_GREY, COLOR_BLACK, hv)
        txt_color = _lerp_color(COLOR_WHITE, COLOR_SPOTIFY_GREEN, hv)
        shown_label = "Waiting for you..." if waiting else button_label
        # Button gently fades/rises in once the heading has mostly settled,
        # rather than just appearing the instant the stage starts.
        btn_appear = _ease_out_cubic(max(0.0, min(1.0, (elapsed - 0.35) / 0.35)))
        if btn_appear > 0:
            btn_surf = pygame.Surface((btn_w + 4, btn_h + 4), pygame.SRCALPHA)
            local_rect = pygame.Rect(2, 2, btn_w, btn_h)
            # Slow pulse while waiting on the OS dialog/settings screen, so it
            # reads as "actively waiting" rather than stuck.
            pulse = 0.5 + 0.5 * math.sin(time.time() * 3.0) if waiting else 1.0
            draw_fill = _lerp_color(fill, COLOR_DARK_GREY, 0) if not waiting else _lerp_color((40, 40, 40), (70, 70, 70), pulse)
            pygame.draw.rect(btn_surf, draw_fill if waiting else fill, local_rect, border_radius=30)
            btn_text_surf = render_fit_text(shown_label, COLOR_TEXT_MUTED if waiting else txt_color, btn_w - 30, base_size=20, bold=True)
            btn_surf.blit(btn_text_surf, btn_text_surf.get_rect(center=local_rect.center))
            btn_surf.set_alpha(int(255 * btn_appear))
            rise = int(10 * (1 - btn_appear))
            virtual_surface.blit(btn_surf, (btn_rect.x - 2, btn_rect.y - 2 + rise))

        if waiting:
            hint_surf = _cached_render(font_small, "Answer the prompt to continue", True, COLOR_DARK_GREY)
            virtual_surface.blit(hint_surf, hint_surf.get_rect(center=(center_x, btn_rect.bottom + 34)))

        onboarding_button_rect = btn_rect
        return

    # --- "folder" and "scrape" stages: a polished dark card floating on the
    # brand-green background (matching the app's own black/near-black
    # surfaces), instead of text sitting directly on the green, so these two
    # feel like a deliberate part of the app rather than a placeholder screen. ---
    mouse_pos = get_virtual_mouse_pos()

    ONBOARDING_CARD_BG = (16, 16, 16)

    card_w = min(520, WIDTH - 80)
    if onboarding_stage == "scrape" and onboarding_scrape_active:
        card_h = 260
    elif onboarding_stage == "scrape":
        card_h = 400
    else:
        card_h = 380
    card_rect = pygame.Rect(0, 0, card_w, card_h)
    card_rect.center = (center_x, center_y)

    # Smooth entrance: the whole card (shadow, background, icon, text,
    # buttons - everything below) is composited onto its own surface first,
    # then faded + eased upward into place as one piece, instead of popping
    # in instantly. Reset per-stage since elapsed restarts on every stage change.
    entrance_dur = 0.32
    entrance_t = _ease_out_cubic(min(1.0, elapsed / entrance_dur))
    entrance_alpha = int(255 * entrance_t)
    entrance_rise = int(24 * (1 - entrance_t))

    pad = 24
    canvas = pygame.Surface((card_w + pad * 2, card_h + pad * 2 + 20), pygame.SRCALPHA)
    origin_x, origin_y = card_rect.x - pad, card_rect.y - pad
    local_card_rect = pygame.Rect(pad, pad, card_w, card_h)

    # Soft drop shadow, then the card itself, both rounded to match the
    # pill buttons/rounded cards used everywhere else in the app.
    pygame.draw.rect(canvas, (0, 0, 0, 90), local_card_rect.move(0, 10), border_radius=28)
    pygame.draw.rect(canvas, ONBOARDING_CARD_BG, local_card_rect, border_radius=28)

    inner_w = card_w - 72
    cursor_y = local_card_rect.y + 34

    local_center_x = local_card_rect.centerx

    if onboarding_stage == "folder":
        _draw_onboarding_icon(canvas, (local_center_x, cursor_y + 26), "folder", 52, COLOR_SPOTIFY_GREEN)
        cursor_y += 78
        heading, subtitle = "Where's your music?", "Pick the folder with your songs - we'll scan it (and any subfolders) for tracks."
    elif onboarding_scrape_active:
        _draw_onboarding_icon(canvas, (local_center_x, cursor_y + 26), "sparkle", 52, COLOR_SPOTIFY_GREEN)
        cursor_y += 78
        heading, subtitle = "Finding album art & lyrics", ""
    else:
        _draw_onboarding_icon(canvas, (local_center_x, cursor_y + 26), "sparkle", 52, COLOR_SPOTIFY_GREEN)
        cursor_y += 78
        heading = "Fill in missing covers & lyrics?"
        subtitle = "We'll check iTunes and lrclib.net for anything missing. Anything you've already set stays untouched."

    head_lines = _wrap_text_lines(heading, font_title, inner_w)
    for line in head_lines:
        line_surf = _cached_render(font_title, line, True, COLOR_WHITE)
        canvas.blit(line_surf, line_surf.get_rect(center=(local_center_x, cursor_y)))
        cursor_y += font_title.get_height() + 2
    cursor_y += 6

    if subtitle:
        sub_lines = _wrap_text_lines(subtitle, font_small, inner_w)
        for line in sub_lines:
            line_surf = _cached_render(font_small, line, True, COLOR_TEXT_MUTED)
            canvas.blit(line_surf, line_surf.get_rect(center=(local_center_x, cursor_y)))
            cursor_y += font_small.get_height() + 4
        cursor_y += 10

    if onboarding_stage == "scrape" and onboarding_scrape_active:
        # Progress bar instead of buttons while the batch job is running -
        # the fill smoothly chases the real progress instead of snapping
        # forward each time a track finishes.
        global _onboarding_bar_disp
        done, total = onboarding_scrape_progress
        target_frac = 0.0 if total <= 0 else max(0.0, min(1.0, done / total))
        _onboarding_bar_disp += (target_frac - _onboarding_bar_disp) * 0.12
        if abs(_onboarding_bar_disp - target_frac) < 0.003:
            _onboarding_bar_disp = target_frac
        disp_frac = _onboarding_bar_disp

        bar_w, bar_h = inner_w, 14
        bar_rect = pygame.Rect(0, 0, bar_w, bar_h)
        bar_rect.center = (local_center_x, local_card_rect.bottom - 60)
        pygame.draw.rect(canvas, COLOR_LIGHT_GREY, bar_rect, border_radius=bar_h // 2)
        if disp_frac > 0:
            fill_rect = pygame.Rect(bar_rect.x, bar_rect.y, max(bar_h, int(bar_w * disp_frac)), bar_h)
            pygame.draw.rect(canvas, COLOR_SPOTIFY_GREEN, fill_rect, border_radius=bar_h // 2)
            # A soft lighter cap at the leading edge gives the fill a gentle
            # "glow" so it doesn't feel like a static bar even when progress
            # is momentarily paused between tracks.
            cap_x = fill_rect.right - bar_h // 2
            pygame.draw.circle(canvas, COLOR_SPOTIFY_GREEN, (cap_x, bar_rect.centery), bar_h // 2)
        pct_surf = _cached_render(font_small, f"{done} / {max(total, done)} tracks", True, COLOR_TEXT_MUTED)
        canvas.blit(pct_surf, pct_surf.get_rect(center=(local_center_x, bar_rect.bottom + 20)))

        canvas.set_alpha(entrance_alpha)
        virtual_surface.blit(canvas, (origin_x, origin_y + entrance_rise))
        onboarding_button_rect = None
        return

    if onboarding_stage == "scrape":
        btn_w, btn_h, gap = (inner_w - 16) // 2, 54, 16
        yes_local = pygame.Rect(0, 0, btn_w, btn_h)
        no_local = pygame.Rect(0, 0, btn_w, btn_h)
        total_w = btn_w * 2 + gap
        row_y = local_card_rect.bottom - 100
        yes_local.topleft = (local_center_x - total_w // 2, row_y)
        no_local.topleft = (yes_local.right + gap, row_y)
        # Screen-space equivalents, used for hit-testing/hover only.
        yes_rect = yes_local.move(origin_x, origin_y)
        no_rect = no_local.move(origin_x, origin_y)

        for local_rect, screen_rect, key, label, is_primary in (
            (yes_local, yes_rect, "scrape_yes", "Yes, Find Them", True),
            (no_local, no_rect, "scrape_no", "No Thanks", False),
        ):
            hovered = screen_rect.collidepoint(mouse_pos)
            hv = _smooth_hover(key, hovered)
            if is_primary:
                fill = _lerp_color(COLOR_SPOTIFY_GREEN, COLOR_HOVER, hv)
                txt_color = _lerp_color(COLOR_BLACK, COLOR_SPOTIFY_GREEN, hv)
            else:
                fill = _lerp_color(COLOR_LIGHT_GREY, COLOR_HOVER, hv)
                txt_color = COLOR_WHITE
            # A subtle press-in scale on hover, eased via the same smoothed value.
            scale = 1.0 - 0.02 * hv
            scaled = local_rect.inflate(-int(local_rect.w * (1 - scale)), -int(local_rect.h * (1 - scale)))
            pygame.draw.rect(canvas, fill, scaled, border_radius=27)
            if not is_primary:
                pygame.draw.rect(canvas, COLOR_TEXT_MUTED, scaled, width=1, border_radius=27)
            txt_surf = render_fit_text(label, txt_color, btn_w - 24, base_size=17, bold=True)
            canvas.blit(txt_surf, txt_surf.get_rect(center=scaled.center))

        canvas.set_alpha(entrance_alpha)
        virtual_surface.blit(canvas, (origin_x, origin_y + entrance_rise))
        onboarding_button_rect = yes_rect
        onboarding_button_rect_2 = no_rect
        return

    # "folder" stage button + skip link
    btn_w, btn_h = inner_w, 54
    btn_local = pygame.Rect(0, 0, btn_w, btn_h)
    btn_local.center = (local_center_x, local_card_rect.bottom - 100)
    btn_rect = btn_local.move(origin_x, origin_y)
    hovered = btn_rect.collidepoint(mouse_pos)
    hv = _smooth_hover("folder_choose", hovered)
    fill = _lerp_color(COLOR_SPOTIFY_GREEN, COLOR_HOVER, hv)
    txt_color = _lerp_color(COLOR_BLACK, COLOR_SPOTIFY_GREEN, hv)
    scale = 1.0 - 0.02 * hv
    scaled_btn = btn_local.inflate(-int(btn_local.w * (1 - scale)), -int(btn_local.h * (1 - scale)))
    pygame.draw.rect(canvas, fill, scaled_btn, border_radius=27)
    btn_text_surf = render_fit_text("Choose Folder", txt_color, btn_w - 30, base_size=18, bold=True)
    canvas.blit(btn_text_surf, btn_text_surf.get_rect(center=scaled_btn.center))
    onboarding_button_rect = btn_rect

    skip_local = pygame.Rect(0, 0, 160, 30)
    skip_local.center = (local_center_x, btn_local.bottom + 30)
    skip_rect = skip_local.move(origin_x, origin_y)
    skip_hovered = skip_rect.collidepoint(mouse_pos)
    skip_hv = _smooth_hover("folder_skip", skip_hovered)
    skip_color = _lerp_color(COLOR_TEXT_MUTED, COLOR_WHITE, skip_hv)
    skip_surf = _cached_render(font_small, "Skip for now", True, skip_color)
    canvas.blit(skip_surf, skip_surf.get_rect(center=skip_local.center))
    onboarding_skip_rect = skip_rect

    canvas.set_alpha(entrance_alpha)
    virtual_surface.blit(canvas, (origin_x, origin_y + entrance_rise))


def _onboarding_default_music_dir():
    """Best-guess starting folder for the onboarding folder browser - the
    device's actual Music folder when it exists, so the user doesn't have to
    dig through unrelated system folders to find their songs."""
    candidates = [
        os.path.join(ROOT_PATH, "Music"),
        os.path.join(ROOT_PATH, "Download", "Music"),
        ROOT_PATH,
    ]
    for path in candidates:
        if os.path.isdir(path):
            return path
    return ROOT_PATH


def _refresh_onboarding_rects():
    """Recomputes onboarding_button_rect / onboarding_button_rect_2 /
    onboarding_skip_rect immediately after an onboarding stage change,
    instead of waiting for the next full render frame to redraw them. Without
    this, a fast tap right after a stage transition could still land on the
    *previous* stage's stale rect (e.g. tapping "Skip for now" on the new
    "folder" screen landing on where the old "storage" screen's button used
    to be) - which is what caused onboarding buttons needing two taps, and
    "Skip for now" sometimes opening the folder browser instead of skipping."""
    try:
        draw_onboarding_overlay()
    except Exception:
        pass


def handle_onboarding_click(pos):
    """Handles a click/tap anywhere on the onboarding overlay. pos is already
    in virtual-surface coordinates (via get_virtual_mouse_pos())."""
    global onboarding_stage, onboarding_anim_start, onboarding_complete
    global onboarding_awaiting_folder, auto_scrape_media, current_page, is_browsing_storage, current_browser_path
    global onboarding_awaiting_permission

    if onboarding_stage == "welcome":
        # Click anywhere advances to the notifications-permission screen.
        onboarding_stage = "notifications"
        onboarding_anim_start = time.time()
        _refresh_onboarding_rects()
        return

    if onboarding_stage == "folder" and onboarding_skip_rect is not None and onboarding_skip_rect.collidepoint(pos):
        # "Skip for now" actually skips - it finishes onboarding right here
        # instead of still funneling into the scrape question.
        _onboarding_hover_smooth["folder_skip"] = 0.0
        auto_scrape_media = False
        onboarding_complete = True
        onboarding_stage = None
        save_app_data()
        return

    if onboarding_stage == "scrape" and onboarding_scrape_active:
        return  # scrape in progress - ignore clicks until it finishes

    if onboarding_stage == "scrape" and onboarding_button_rect_2 is not None and onboarding_button_rect_2.collidepoint(pos):
        # "No Thanks" - skip the auto-scrape and finish onboarding.
        _onboarding_hover_smooth["scrape_no"] = 0.0
        auto_scrape_media = False
        onboarding_complete = True
        onboarding_stage = None
        save_app_data()
        return

    if onboarding_stage in ("notifications", "storage") and onboarding_awaiting_permission:
        return  # already waiting on an OS permission result - ignore taps until it resolves

    if onboarding_button_rect is None or not onboarding_button_rect.collidepoint(pos):
        return  # click missed the button on a permission screen - do nothing

    if onboarding_stage == "notifications":
        # Stay on this screen - the main loop advances to "storage" only once
        # _notification_permission_result actually comes back True.
        onboarding_awaiting_permission = True
        _onboarding_hover_smooth["perm_btn"] = 0.0  # snap the button back to its normal look immediately, not stuck "hovered"
        request_notification_permission_for_onboarding()
    elif onboarding_stage == "storage":
        # Stay on this screen - the main loop advances to "folder" only once
        # _check_storage_access_granted() actually confirms access. Uses the
        # sequenced request (legacy dialog, THEN the settings screen) so the
        # two don't collide.
        onboarding_awaiting_permission = True
        _onboarding_hover_smooth["perm_btn"] = 0.0
        request_storage_permission_for_onboarding()
    elif onboarding_stage == "folder":
        # Open the app's own in-app storage browser (same one used by the
        # "+ Add Folder" button in Search) so the user can pick their music
        # folder, starting from the device's actual Music folder when there
        # is one. The overlay hides itself while it's open; the main loop
        # brings the "scrape" stage back once a folder is picked or cancelled.
        _onboarding_hover_smooth["folder_choose"] = 0.0
        onboarding_awaiting_folder = True
        current_page = "Search"
        is_browsing_storage = True
        current_browser_path = _onboarding_default_music_dir()
        update_browser_contents()
        onboarding_stage = None
    elif onboarding_stage == "scrape":
        # "Yes, Find Them" - kick off the background auto-scrape, then finish
        # onboarding once it completes (see the main loop's onboarding_scrape_active check).
        _onboarding_hover_smooth["scrape_yes"] = 0.0
        auto_scrape_media = True
        start_onboarding_scrape()


# --- MODAL RENDERING ENGINE ---
def draw_modals():
    global modal_close_rect, modal_save_rect, modal_input_rect, modal_desc_rect, modal_playlist_rects, modal_image_picker_rect, lyrics_close_rect, lyrics_save_rect, lyrics_clear_rect, lyrics_import_rect, lyrics_search_rect, lyrics_textarea_rect, max_music_scroll, max_lyrics_scroll, target_lyrics_scroll, lyrics_text_changed, lyrics_search_close_rect, lyrics_search_item_rects, max_lyrics_search_scroll, lyrics_manual_rect, lyrics_manual_title_rect, lyrics_manual_artist_rect, lyrics_manual_go_rect, lyrics_manual_close_rect, art_search_close_rect, art_search_item_rects, max_art_search_scroll, art_manual_rect, art_manual_title_rect, art_manual_artist_rect, art_manual_go_rect
    mouse_pos = get_virtual_mouse_pos()
    
    portrait_sidebar_h = (80 if (is_portrait and layout_mode == "phone") else (65 if is_portrait else 0))
    main_x = 0 if is_portrait else 230
    main_w = WIDTH - main_x
    content_pad_x = main_x + 30

    # --- ART SEARCH MODAL (overlays the cover browser) ---
    if show_art_search_modal:
        overlay_rect = pygame.Rect(main_x, 0, main_w, HEIGHT - portrait_sidebar_h)
        dim = pygame.Surface((overlay_rect.width, overlay_rect.height), pygame.SRCALPHA)
        dim.fill((0, 0, 0, 210))
        virtual_surface.blit(dim, (overlay_rect.x, overlay_rect.y))

        card_w = min(main_w - 80, 700)
        card_h = min(HEIGHT - portrait_sidebar_h - 80, 520)
        card_x = main_x + (main_w - card_w) // 2
        card_y = (HEIGHT - portrait_sidebar_h - card_h) // 2
        card_rect = pygame.Rect(card_x, card_y, card_w, card_h)
        pygame.draw.rect(virtual_surface, (22, 22, 22), card_rect, border_radius=12)
        pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, card_rect, width=1, border_radius=12)

        hdr = _cached_render(font_body, t("Search Album Art  •  iTunes"), True, COLOR_SPOTIFY_GREEN)
        virtual_surface.blit(hdr, (card_x + 20, card_y + 18))
        sub_title = f"{current_track['title']} — {current_track['artist']}"
        if len(sub_title) > 55: sub_title = sub_title[:53] + "…"
        sub = _cached_render(font_small, sub_title, True, COLOR_TEXT_MUTED)
        virtual_surface.blit(sub, (card_x + 20, card_y + 46))

        art_search_close_rect = pygame.Rect(card_x + card_w - 110, card_y + 14, 90, 34)
        cls_hov = art_search_close_rect.collidepoint(mouse_pos)
        pygame.draw.rect(virtual_surface, COLOR_HOVER if cls_hov else COLOR_LIGHT_GREY,
                         art_search_close_rect, border_radius=17)
        cls_txt = _cached_render(font_small, t("Close"), True, COLOR_WHITE)
        virtual_surface.blit(cls_txt, (
            art_search_close_rect.x + (art_search_close_rect.width - cls_txt.get_width()) // 2,
            art_search_close_rect.y + 9))

        art_manual_rect = pygame.Rect(card_x + card_w - 220, card_y + 14, 90, 34)
        amn_hov = art_manual_rect.collidepoint(mouse_pos)
        amn_bg = COLOR_SPOTIFY_GREEN if (amn_hov and mouse_held) else (COLOR_HOVER if amn_hov else COLOR_LIGHT_GREY)
        pygame.draw.rect(virtual_surface, amn_bg, art_manual_rect, border_radius=17)
        amn_txt = _cached_render(font_small, t("Manual"), True, COLOR_WHITE)
        virtual_surface.blit(amn_txt, (
            art_manual_rect.x + (art_manual_rect.width - amn_txt.get_width()) // 2,
            art_manual_rect.y + 9))

        divider_y = card_y + 72
        pygame.draw.line(virtual_surface, COLOR_LIGHT_GREY,
                         (card_x + 20, divider_y), (card_x + card_w - 20, divider_y))

        body_top = divider_y + 10
        body_rect = pygame.Rect(card_x + 10, body_top, card_w - 20, card_y + card_h - body_top - 10)
        art_search_item_rects = []

        if show_art_manual_modal:
            pygame.draw.rect(virtual_surface, COLOR_CARD_BG, body_rect, border_radius=8)

            name_lbl = _cached_render(font_small, t("Song name"), True, COLOR_TEXT_MUTED)
            virtual_surface.blit(name_lbl, (body_rect.x + 25, body_rect.y + 25))
            art_manual_title_rect = pygame.Rect(body_rect.x + 25, body_rect.y + 47, body_rect.width - 50, 44)
            pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, art_manual_title_rect, border_radius=6)
            _amt_active = search_input_active and active_input_field == "art_manual_title"
            if _amt_active:
                pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, art_manual_title_rect, width=2, border_radius=6)
            if manual_title_text:
                amt_surf = _cached_render(font_small, manual_title_text, True, COLOR_WHITE)
                virtual_surface.blit(amt_surf, (art_manual_title_rect.x + 12, art_manual_title_rect.y + 13))
                if _amt_active and not HAS_ANDROID_MEDIA and int(time.time() * 2) % 2 == 0:
                    _tc = min(manual_title_cursor, len(manual_title_text))
                    _cx = art_manual_title_rect.x + 12 + font_small.size(manual_title_text[:_tc])[0]
                    pygame.draw.line(virtual_surface, COLOR_WHITE,
                                     (_cx, art_manual_title_rect.y + 8), (_cx, art_manual_title_rect.y + 36), 2)
            else:
                virtual_surface.blit(_cached_render(font_small, t("e.g. Blinding Lights"), True, COLOR_TEXT_MUTED),
                                     (art_manual_title_rect.x + 12, art_manual_title_rect.y + 13))

            artist_lbl = _cached_render(font_small, t("Artist"), True, COLOR_TEXT_MUTED)
            virtual_surface.blit(artist_lbl, (body_rect.x + 25, body_rect.y + 107))
            art_manual_artist_rect = pygame.Rect(body_rect.x + 25, body_rect.y + 129, body_rect.width - 50, 44)
            pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, art_manual_artist_rect, border_radius=6)
            _ama_active = search_input_active and active_input_field == "art_manual_artist"
            if _ama_active:
                pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, art_manual_artist_rect, width=2, border_radius=6)
            if manual_artist_text:
                ama_surf = _cached_render(font_small, manual_artist_text, True, COLOR_WHITE)
                virtual_surface.blit(ama_surf, (art_manual_artist_rect.x + 12, art_manual_artist_rect.y + 13))
                if _ama_active and not HAS_ANDROID_MEDIA and int(time.time() * 2) % 2 == 0:
                    _ac = min(manual_artist_cursor, len(manual_artist_text))
                    _cx = art_manual_artist_rect.x + 12 + font_small.size(manual_artist_text[:_ac])[0]
                    pygame.draw.line(virtual_surface, COLOR_WHITE,
                                     (_cx, art_manual_artist_rect.y + 8), (_cx, art_manual_artist_rect.y + 36), 2)
            else:
                virtual_surface.blit(_cached_render(font_small, t("e.g. The Weeknd"), True, COLOR_TEXT_MUTED),
                                     (art_manual_artist_rect.x + 12, art_manual_artist_rect.y + 13))

            art_manual_go_rect = pygame.Rect(body_rect.x + 25, body_rect.y + 195, 140, 44)
            amg_hovered = art_manual_go_rect.collidepoint(mouse_pos)
            amg_bg = (40, 230, 110) if amg_hovered else COLOR_SPOTIFY_GREEN
            pygame.draw.rect(virtual_surface, amg_bg, art_manual_go_rect, border_radius=22)
            amg_txt = _cached_render(font_body, t("Search"), True, COLOR_BLACK)
            amg_txt_x = art_manual_go_rect.x + (art_manual_go_rect.width - amg_txt.get_width()) // 2
            virtual_surface.blit(amg_txt, (amg_txt_x, art_manual_go_rect.y + 11))
        elif art_search_loading:
            wait_lbl = _cached_render(font_body, t("Searching iTunes..."), True, COLOR_TEXT_MUTED)
            virtual_surface.blit(wait_lbl, (card_x + 20, body_top + 20))
        elif art_apply_pending:
            dl_lbl = _cached_render(font_body, t("Downloading cover..."), True, COLOR_TEXT_MUTED)
            virtual_surface.blit(dl_lbl, (card_x + 20, body_top + 20))
        elif art_search_error and not art_search_results:
            for ei, eline in enumerate(get_wrapped_lines(art_search_error, font_body, body_rect.width - 30)):
                virtual_surface.blit(_cached_render(font_body, eline, True, (200, 90, 90)),
                                     (card_x + 20, body_top + 20 + ei * 28))
        else:
            banner_h = 0
            if art_search_error:
                banner_h = 34
                banner_rect = pygame.Rect(card_x + 14, body_top, card_w - 28, banner_h - 6)
                pygame.draw.rect(virtual_surface, (60, 30, 30), banner_rect, border_radius=6)
                err_txt = art_search_error
                if len(err_txt) > 70: err_txt = err_txt[:68] + "\u2026"
                err_surf = _cached_render(font_small, err_txt, True, (235, 140, 140))
                virtual_surface.blit(err_surf, (banner_rect.x + 10, banner_rect.y + 6))

            list_top = body_top + banner_h
            list_rect = pygame.Rect(body_rect.x, list_top, body_rect.width, body_rect.height - banner_h)
            virtual_surface.set_clip(list_rect)
            item_h = 68
            y_item = list_top - round(art_search_scroll_offset)
            max_art_search_scroll = max(0, len(art_search_results) * item_h - list_rect.height + 10)

            for idx, result in enumerate(art_search_results):
                row_rect = pygame.Rect(card_x + 14, y_item, card_w - 28, item_h - 6)
                if row_rect.colliderect(list_rect):
                    art_search_item_rects.append((row_rect, idx))
                    row_hov = row_rect.collidepoint(mouse_pos)
                    row_clk = row_hov and mouse_held
                    row_bg  = (45, 45, 45) if row_clk else (COLOR_HOVER if row_hov else (30, 30, 30))
                    pygame.draw.rect(virtual_surface, row_bg, row_rect, border_radius=6)

                    thumb_rect = pygame.Rect(row_rect.x + 8, row_rect.y + 8, 52, 52)
                    thumb_url = result.get("artworkUrl60") or result.get("artworkUrl100") or result.get("artworkUrl30")
                    thumb_surf = art_search_thumb_surfaces.get(thumb_url) if thumb_url else None
                    if thumb_surf is not None:
                        virtual_surface.blit(thumb_surf, thumb_rect.topleft)
                    else:
                        pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, thumb_rect, border_radius=4)
                        note = _cached_render(font_small, "\u266a", True, COLOR_TEXT_MUTED)
                        virtual_surface.blit(note, (thumb_rect.x + 20, thumb_rect.y + 16))

                    track_name  = result.get("trackName")  or result.get("collectionName") or "Unknown"
                    artist_name = result.get("artistName") or "Unknown"
                    coll_name   = result.get("collectionName") or ""
                    if len(track_name)  > 40: track_name  = track_name[:38]  + "\u2026"
                    if len(artist_name) > 40: artist_name = artist_name[:38] + "\u2026"
                    if len(coll_name)   > 40: coll_name   = coll_name[:38]   + "\u2026"

                    tx = row_rect.x + 70
                    virtual_surface.blit(_cached_render(font_body, track_name,   True, COLOR_WHITE),       (tx, row_rect.y + 6))
                    virtual_surface.blit(_cached_render(font_small, artist_name, True, COLOR_TEXT_MUTED),  (tx, row_rect.y + 28))
                    if coll_name:
                        virtual_surface.blit(_cached_render(font_small, coll_name, True, (130, 130, 130)), (tx, row_rect.y + 44))
                y_item += item_h
            virtual_surface.set_clip(None)
        return

    if show_lyrics_editor_view:
        pygame.draw.rect(virtual_surface, COLOR_BLACK, (main_x, 0, main_w, HEIGHT - portrait_sidebar_h))
        current_lyrics_str = song_lyrics_database.get(track_ref, "")
        
        header_lbl = _cached_render(font_huge, t("Edit Song Lyrics"), True, COLOR_SPOTIFY_GREEN)
        track_lbl = _cached_render(font_body, f"Track: {current_track['title']} • {current_track['artist']}", True, COLOR_WHITE)
        virtual_surface.blit(header_lbl, (main_x + 40, 45))
        virtual_surface.blit(track_lbl, (main_x + 40, 105))
        
        _phone_lyrics = is_portrait and layout_mode == "phone"
        # Phone has 2 rows of buttons below the textarea now (vs. 1 on desktop), so it
        # needs extra headroom subtracted here or the second row clips off the bottom.
        if _phone_lyrics:
            lyrics_box_h = HEIGHT - portrait_sidebar_h - 305
        elif is_portrait:
            lyrics_box_h = HEIGHT - portrait_sidebar_h - 250
        else:
            lyrics_box_h = 420
        lyrics_textarea_rect = pygame.Rect(main_x + 40, 145, main_w - 80, lyrics_box_h)
        pygame.draw.rect(virtual_surface, COLOR_CARD_BG, lyrics_textarea_rect, border_radius=8)
        
        if search_input_active and active_input_field == "lyrics":
            pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, lyrics_textarea_rect, width=2, border_radius=8)
            
        if current_lyrics_str or current_lyrics_str == "":
            elapsed_sec = 0.0
            if track_duration > 0 and music_loaded:
                if current_backend == "android" and android_media_player:
                    try: elapsed_sec = android_media_player.getCurrentPosition() / 1000.0
                    except: elapsed_sec = 0.0
                else:
                    mix_pos = pygame.mixer.music.get_pos()
                    if mix_pos == -1:
                        elapsed_sec = track_duration if current_track.get("_has_started", False) else track_start_accumulator
                    else:
                        elapsed_sec = track_start_accumulator + (mix_pos / 1000.0)
                elapsed_sec = min(track_duration, elapsed_sec)

            lines = current_lyrics_str.split('\n')
            active_line_idx = -1
            best_time = -1
            for i, line in enumerate(lines):
                line_stripped = line.strip()
                if line_stripped.startswith('[') and ']' in line_stripped:
                    try:
                        time_part = line_stripped.split(']', 1)[0][1:].strip()
                        if ':' in time_part:
                            t_parts = time_part.split(':')
                            lyric_time = float(t_parts[0]) * 60 + float(t_parts[1])
                            if lyric_time <= elapsed_sec and lyric_time > best_time:
                                best_time = lyric_time
                                active_line_idx = i
                    except:
                        pass

            total_lyrics_height = 0
            for line in lines:
                wrapped_sublines = get_wrapped_lines(line, font_small, lyrics_textarea_rect.width - 40)
                if wrapped_sublines:
                    total_lyrics_height += len(wrapped_sublines) * 20
                if not line:
                    total_lyrics_height += 12
                    
            if total_lyrics_height > lyrics_box_h:
                max_lyrics_scroll = max(0, total_lyrics_height - (lyrics_textarea_rect.height - 30))
            else:
                max_lyrics_scroll = 0

            if lyrics_text_changed:
                target_lyrics_scroll = max_lyrics_scroll
                lyrics_text_changed = False

            virtual_surface.set_clip(lyrics_textarea_rect)

            y_pos = lyrics_textarea_rect.y + 15 - round(lyrics_scroll_offset)
            
            temp_idx = 0
            target_line_idx = 0
            target_char_offset = 0
            for idx, l in enumerate(lines):
                if temp_idx <= lyrics_cursor_pos <= temp_idx + len(l):
                    target_line_idx = idx
                    target_char_offset = lyrics_cursor_pos - temp_idx
                    break
                temp_idx += len(l) + 1

            cursor_x = lyrics_textarea_rect.x + 15
            cursor_y = y_pos
            cursor_drawn_for_line = False
            
            for i, line in enumerate(lines):
                wrapped_sublines = get_wrapped_lines(line, font_small, lyrics_textarea_rect.width - 40)
                line_color = COLOR_SPOTIFY_GREEN if i == active_line_idx else COLOR_WHITE
                
                if not line:
                    if i == target_line_idx:
                        cursor_x = lyrics_textarea_rect.x + 15
                        cursor_y = y_pos
                    y_pos += 12
                else:
                    accumulated_chars = 0
                    for sub_idx, sl in enumerate(wrapped_sublines):
                        line_surf = _cached_render(font_small, sl, True, line_color)
                        virtual_surface.blit(line_surf, (lyrics_textarea_rect.x + 15, y_pos))
                        
                        if i == target_line_idx and not cursor_drawn_for_line:
                            next_accumulated = accumulated_chars + len(sl)
                            if accumulated_chars <= target_char_offset <= next_accumulated:
                                rem_offset = target_char_offset - accumulated_chars
                                cursor_x = lyrics_textarea_rect.x + 15 + font_small.size(sl[:rem_offset])[0]
                                cursor_y = y_pos
                                cursor_drawn_for_line = True
                            elif sub_idx == len(wrapped_sublines) - 1:
                                cursor_x = lyrics_textarea_rect.x + 15 + font_small.size(sl)[0]
                                cursor_y = y_pos
                                cursor_drawn_for_line = True
                        
                        accumulated_chars += len(sl) + 1
                        y_pos += 20
                        
            virtual_surface.set_clip(None)
                
            if search_input_active and active_input_field == "lyrics" and (time.time() % 1.0 < 0.5):
                if cursor_y + 16 <= lyrics_textarea_rect.bottom and cursor_y >= lyrics_textarea_rect.y:
                    pygame.draw.line(virtual_surface, COLOR_SPOTIFY_GREEN, (cursor_x, cursor_y), (cursor_x, cursor_y + 16), 2)
        else:
            max_lyrics_scroll = 0
            placeholder = _cached_render(font_small, "Type or paste the song lyrics here... (e.g., [00:12] Synced Line! Press Ctrl+V to paste)", True, COLOR_TEXT_MUTED)
            virtual_surface.blit(placeholder, (lyrics_textarea_rect.x + 15, lyrics_textarea_rect.y + 15))
            
        if is_portrait and layout_mode == "phone":
            # Phone: row of 3 (Close/Save/Clear) doesn't leave room for Import/Search
            # on this narrow width, so those two go on their own centred row below.
            row1_y = lyrics_textarea_rect.bottom + 20
            row1_w = 100 * 3 + 10 * 2
            row1_x = main_x + (main_w - row1_w) // 2
            lyrics_close_rect = pygame.Rect(row1_x, row1_y, 100, 42)
            lyrics_save_rect = pygame.Rect(row1_x + 110, row1_y, 100, 42)
            lyrics_clear_rect = pygame.Rect(row1_x + 220, row1_y, 100, 42)

            row2_y = row1_y + 52
            row2_w = 100 * 2 + 10
            row2_x = main_x + (main_w - row2_w) // 2
            lyrics_import_rect = pygame.Rect(row2_x, row2_y, 100, 42)
            lyrics_search_rect = pygame.Rect(row2_x + 110, row2_y, 100, 42)
        elif is_portrait:
            btn_y = lyrics_textarea_rect.bottom + 20
            start_x = main_x + (main_w - 570) // 2 
            lyrics_close_rect = pygame.Rect(start_x, btn_y, 100, 42)
            lyrics_save_rect = pygame.Rect(start_x + 120, btn_y, 110, 42)
            lyrics_clear_rect = pygame.Rect(start_x + 250, btn_y, 100, 42)
            lyrics_import_rect = pygame.Rect(start_x + 360, btn_y, 100, 42)
            lyrics_search_rect = pygame.Rect(start_x + 470, btn_y, 100, 42)
        else:
            lyrics_close_rect = pygame.Rect(main_x + 40, 590, 100, 42)
            lyrics_save_rect = pygame.Rect(main_x + 150, 590, 100, 42)
            lyrics_clear_rect = pygame.Rect(main_x + 260, 590, 100, 42)
            lyrics_import_rect = pygame.Rect(main_x + 370, 590, 100, 42)
            lyrics_search_rect = pygame.Rect(main_x + 480, 590, 100, 42)
        
        c_hovered = lyrics_close_rect.collidepoint(mouse_pos)
        c_clicked = c_hovered and mouse_held
        c_bg = COLOR_SPOTIFY_GREEN if c_clicked else (COLOR_HOVER if c_hovered else COLOR_LIGHT_GREY)
        pygame.draw.rect(virtual_surface, c_bg, lyrics_close_rect, border_radius=21)
        c_txt = _cached_render(font_body, t("Close"), True, COLOR_WHITE)
        virtual_surface.blit(c_txt, (lyrics_close_rect.x + 28, lyrics_close_rect.y + 11))
        
        s_hovered = lyrics_save_rect.collidepoint(mouse_pos)
        s_clicked = s_hovered and mouse_held
        s_bg = COLOR_SPOTIFY_GREEN if s_clicked else (COLOR_HOVER if s_hovered else COLOR_LIGHT_GREY)
        pygame.draw.rect(virtual_surface, s_bg, lyrics_save_rect, border_radius=21)
        s_txt = _cached_render(font_body, t("Save"), True, COLOR_WHITE)
        virtual_surface.blit(s_txt, (lyrics_save_rect.x + 30, lyrics_save_rect.y + 11))

        cl_hovered = lyrics_clear_rect.collidepoint(mouse_pos)
        cl_clicked = cl_hovered and mouse_held
        cl_bg = COLOR_SPOTIFY_GREEN if cl_clicked else (COLOR_HOVER if cl_hovered else COLOR_LIGHT_GREY)
        pygame.draw.rect(virtual_surface, cl_bg, lyrics_clear_rect, border_radius=21)
        cl_txt = _cached_render(font_body, t("Clear"), True, COLOR_WHITE)
        virtual_surface.blit(cl_txt, (lyrics_clear_rect.x + 28, lyrics_clear_rect.y + 11))

        im_hovered = lyrics_import_rect.collidepoint(mouse_pos)
        im_clicked = im_hovered and mouse_held
        im_bg = COLOR_SPOTIFY_GREEN if im_clicked else (COLOR_HOVER if im_hovered else COLOR_LIGHT_GREY)
        pygame.draw.rect(virtual_surface, im_bg, lyrics_import_rect, border_radius=21)
        im_txt = _cached_render(font_body, t("Import"), True, COLOR_WHITE)
        im_txt_x = lyrics_import_rect.x + (lyrics_import_rect.width - im_txt.get_width()) // 2
        virtual_surface.blit(im_txt, (im_txt_x, lyrics_import_rect.y + 11))

        se_hovered = lyrics_search_rect.collidepoint(mouse_pos)
        se_clicked = se_hovered and mouse_held
        se_bg = COLOR_SPOTIFY_GREEN if se_clicked else (COLOR_HOVER if se_hovered else COLOR_LIGHT_GREY)
        pygame.draw.rect(virtual_surface, se_bg, lyrics_search_rect, border_radius=21)
        se_txt = _cached_render(font_body, t("Search"), True, COLOR_WHITE)
        se_txt_x = lyrics_search_rect.x + (lyrics_search_rect.width - se_txt.get_width()) // 2
        virtual_surface.blit(se_txt, (se_txt_x, lyrics_search_rect.y + 11))

        if show_lyrics_search_modal:
            overlay_rect = pygame.Rect(main_x, 0, main_w, HEIGHT - portrait_sidebar_h)
            dim = pygame.Surface((overlay_rect.width, overlay_rect.height), pygame.SRCALPHA)
            dim.fill((0, 0, 0, 210))
            virtual_surface.blit(dim, (overlay_rect.x, overlay_rect.y))

            card_w = min(main_w - 80, 700)
            card_h = min(HEIGHT - portrait_sidebar_h - 80, 520)
            card_x = main_x + (main_w - card_w) // 2
            card_y = (HEIGHT - portrait_sidebar_h - card_h) // 2
            card_rect = pygame.Rect(card_x, card_y, card_w, card_h)
            pygame.draw.rect(virtual_surface, (22, 22, 22), card_rect, border_radius=12)
            pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, card_rect, width=1, border_radius=12)

            hdr = _cached_render(font_body, t("Search Synced Lyrics"), True, COLOR_SPOTIFY_GREEN)
            virtual_surface.blit(hdr, (card_x + 20, card_y + 18))
            sub_title = f"{current_track['title']} \u2014 {current_track['artist']}"
            if len(sub_title) > 55: sub_title = sub_title[:53] + "\u2026"
            sub = _cached_render(font_small, sub_title, True, COLOR_TEXT_MUTED)
            virtual_surface.blit(sub, (card_x + 20, card_y + 46))

            lyrics_search_close_rect = pygame.Rect(card_x + card_w - 110, card_y + 14, 90, 34)
            cls_hov = lyrics_search_close_rect.collidepoint(mouse_pos)
            pygame.draw.rect(virtual_surface, COLOR_HOVER if cls_hov else COLOR_LIGHT_GREY,
                             lyrics_search_close_rect, border_radius=17)
            cls_txt = _cached_render(font_small, t("Close"), True, COLOR_WHITE)
            virtual_surface.blit(cls_txt, (
                lyrics_search_close_rect.x + (lyrics_search_close_rect.width - cls_txt.get_width()) // 2,
                lyrics_search_close_rect.y + 9))

            lyrics_manual_rect = pygame.Rect(card_x + card_w - 220, card_y + 14, 90, 34)
            man_hov = lyrics_manual_rect.collidepoint(mouse_pos)
            man_bg = COLOR_SPOTIFY_GREEN if (man_hov and mouse_held) else (COLOR_HOVER if man_hov else COLOR_LIGHT_GREY)
            pygame.draw.rect(virtual_surface, man_bg, lyrics_manual_rect, border_radius=17)
            man_txt = _cached_render(font_small, t("Manual"), True, COLOR_WHITE)
            virtual_surface.blit(man_txt, (
                lyrics_manual_rect.x + (lyrics_manual_rect.width - man_txt.get_width()) // 2,
                lyrics_manual_rect.y + 9))

            divider_y = card_y + 72
            pygame.draw.line(virtual_surface, COLOR_LIGHT_GREY,
                             (card_x + 20, divider_y), (card_x + card_w - 20, divider_y))

            body_top = divider_y + 10
            body_rect = pygame.Rect(card_x + 10, body_top, card_w - 20, card_y + card_h - body_top - 10)

            if show_lyrics_manual_modal:
                pygame.draw.rect(virtual_surface, COLOR_CARD_BG, body_rect, border_radius=8)

                name_lbl = _cached_render(font_small, t("Song name"), True, COLOR_TEXT_MUTED)
                virtual_surface.blit(name_lbl, (body_rect.x + 25, body_rect.y + 25))
                lyrics_manual_title_rect = pygame.Rect(body_rect.x + 25, body_rect.y + 47, body_rect.width - 50, 44)
                pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, lyrics_manual_title_rect, border_radius=6)
                _lmt_active = search_input_active and active_input_field == "manual_title"
                if _lmt_active:
                    pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, lyrics_manual_title_rect, width=2, border_radius=6)
                if manual_title_text:
                    mt_surf = _cached_render(font_small, manual_title_text.replace("\n", " ").replace("\r", ""), True, COLOR_WHITE)
                    virtual_surface.blit(mt_surf, (lyrics_manual_title_rect.x + 12, lyrics_manual_title_rect.y + 13))
                    if _lmt_active and not HAS_ANDROID_MEDIA and int(time.time() * 2) % 2 == 0:
                        _tc = min(manual_title_cursor, len(manual_title_text))
                        _cx = lyrics_manual_title_rect.x + 12 + font_small.size(manual_title_text[:_tc])[0]
                        pygame.draw.line(virtual_surface, COLOR_WHITE,
                                         (_cx, lyrics_manual_title_rect.y + 8), (_cx, lyrics_manual_title_rect.y + 36), 2)
                else:
                    virtual_surface.blit(_cached_render(font_small, t("e.g. Blinding Lights"), True, COLOR_TEXT_MUTED),
                                         (lyrics_manual_title_rect.x + 12, lyrics_manual_title_rect.y + 13))

                artist_lbl = _cached_render(font_small, t("Artist"), True, COLOR_TEXT_MUTED)
                virtual_surface.blit(artist_lbl, (body_rect.x + 25, body_rect.y + 107))
                lyrics_manual_artist_rect = pygame.Rect(body_rect.x + 25, body_rect.y + 129, body_rect.width - 50, 44)
                pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, lyrics_manual_artist_rect, border_radius=6)
                _lma_active = search_input_active and active_input_field == "manual_artist"
                if _lma_active:
                    pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, lyrics_manual_artist_rect, width=2, border_radius=6)
                if manual_artist_text:
                    maa_surf = _cached_render(font_small, manual_artist_text.replace("\n", " ").replace("\r", ""), True, COLOR_WHITE)
                    virtual_surface.blit(maa_surf, (lyrics_manual_artist_rect.x + 12, lyrics_manual_artist_rect.y + 13))
                    if _lma_active and not HAS_ANDROID_MEDIA and int(time.time() * 2) % 2 == 0:
                        _ac = min(manual_artist_cursor, len(manual_artist_text))
                        _cx = lyrics_manual_artist_rect.x + 12 + font_small.size(manual_artist_text[:_ac])[0]
                        pygame.draw.line(virtual_surface, COLOR_WHITE,
                                         (_cx, lyrics_manual_artist_rect.y + 8), (_cx, lyrics_manual_artist_rect.y + 36), 2)
                else:
                    virtual_surface.blit(_cached_render(font_small, t("e.g. The Weeknd"), True, COLOR_TEXT_MUTED),
                                         (lyrics_manual_artist_rect.x + 12, lyrics_manual_artist_rect.y + 13))

                lyrics_manual_go_rect = pygame.Rect(body_rect.x + 25, body_rect.y + 195, 140, 44)
                mg_hovered = lyrics_manual_go_rect.collidepoint(mouse_pos)
                mg_bg = (40, 230, 110) if mg_hovered else COLOR_SPOTIFY_GREEN
                pygame.draw.rect(virtual_surface, mg_bg, lyrics_manual_go_rect, border_radius=22)
                mg_txt = _cached_render(font_body, t("Search"), True, COLOR_BLACK)
                mg_txt_x = lyrics_manual_go_rect.x + (lyrics_manual_go_rect.width - mg_txt.get_width()) // 2
                virtual_surface.blit(mg_txt, (mg_txt_x, lyrics_manual_go_rect.y + 11))
                lyrics_manual_close_rect = pygame.Rect(0, 0, 0, 0)
            else:
                lyrics_search_item_rects = []
                if lyrics_search_loading:
                    loading_lbl = _cached_render(font_body, t("Searching..."), True, COLOR_TEXT_MUTED)
                    virtual_surface.blit(loading_lbl, (card_x + 20, body_top + 20))
                elif lyrics_search_error and not lyrics_search_results:
                    for ei, eline in enumerate(get_wrapped_lines(lyrics_search_error, font_body, body_rect.width - 30)):
                        virtual_surface.blit(_cached_render(font_body, eline, True, (200, 90, 90)),
                                             (card_x + 20, body_top + 20 + ei * 28))
                else:
                    virtual_surface.set_clip(body_rect)
                    item_h = 68
                    y_item = body_top - round(lyrics_search_scroll_offset)
                    max_lyrics_search_scroll = max(0, len(lyrics_search_results) * item_h - body_rect.height + 10)

                    for idx, cand in enumerate(lyrics_search_results):
                        row_rect = pygame.Rect(card_x + 14, y_item, card_w - 28, item_h - 6)
                        if row_rect.colliderect(body_rect):
                            lyrics_search_item_rects.append((row_rect, idx))
                            row_hov = row_rect.collidepoint(mouse_pos)
                            row_clk = row_hov and mouse_held
                            row_bg  = (45, 45, 45) if row_clk else (COLOR_HOVER if row_hov else (30, 30, 30))
                            pygame.draw.rect(virtual_surface, row_bg, row_rect, border_radius=6)

                            thumb_rect = pygame.Rect(row_rect.x + 8, row_rect.y + 8, 52, 52)
                            pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, thumb_rect, border_radius=4)
                            has_synced = bool(cand.get("syncedLyrics"))
                            icon_char = "\u266a" if has_synced else "\u2715"
                            icon_col  = COLOR_SPOTIFY_GREEN if has_synced else (200, 90, 90)
                            icon_surf = _cached_render(font_body, icon_char, True, icon_col)
                            virtual_surface.blit(icon_surf, (
                                thumb_rect.x + (thumb_rect.width  - icon_surf.get_width())  // 2,
                                thumb_rect.y + (thumb_rect.height - icon_surf.get_height()) // 2))

                            cand_title  = (cand.get("trackName")  or "Unknown title").replace("\n", " ").replace("\r", "")
                            cand_artist = (cand.get("artistName") or "Unknown artist").replace("\n", " ").replace("\r", "")
                            dur = cand.get("duration")
                            dur_str = f"{int(dur // 60)}:{int(dur % 60):02d}" if isinstance(dur, (int, float)) else "--:--"
                            if len(cand_title)  > 40: cand_title  = cand_title[:38]  + "\u2026"
                            if len(cand_artist) > 40: cand_artist = cand_artist[:38] + "\u2026"

                            tx = row_rect.x + 70
                            virtual_surface.blit(_cached_render(font_body, cand_title,  True, COLOR_WHITE),      (tx, row_rect.y + 6))
                            virtual_surface.blit(_cached_render(font_small, cand_artist, True, COLOR_TEXT_MUTED), (tx, row_rect.y + 28))
                            sync_lbl = "synced" if has_synced else "no synced lyrics"
                            sync_col  = COLOR_TEXT_MUTED if has_synced else (200, 90, 90)
                            virtual_surface.blit(_cached_render(font_small, f"{dur_str} \u2022 {sync_lbl}", True, sync_col),
                                                 (tx, row_rect.y + 44))
                        y_item += item_h
                    virtual_surface.set_clip(None)

                    if lyrics_search_error:
                        fail_lines = get_wrapped_lines(lyrics_search_error, font_small, body_rect.width - 40)[:2]
                        y_fail = body_rect.bottom - 24 - (len(fail_lines) - 1) * 18
                        for fline in fail_lines:
                            virtual_surface.blit(_cached_render(font_small, fline, True, (200, 90, 90)),
                                                 (body_rect.x + 20, y_fail))
                            y_fail += 18
        return

    if show_create_playlist_modal:
        if is_browsing_for_cover:
            draw_main_content()
            return

        pygame.draw.rect(virtual_surface, COLOR_BLACK, (main_x, 0, main_w, HEIGHT))
        
        lbl = _cached_render(font_huge, t("Create playlist"), True, COLOR_WHITE)
        if is_portrait:
            virtual_surface.blit(lbl, (main_x + (main_w - lbl.get_width()) // 2, 45))
        else:
            virtual_surface.blit(lbl, (main_x + 50, 60))
        
        if is_portrait:
            img_x = main_x + (main_w - 220) // 2
            img_y = 120
        else:
            img_x = main_x + 50
            img_y = 160
            
        modal_image_picker_rect = pygame.Rect(img_x, img_y, 220, 220)
        if modal_playlist_cover_surface:
            disp_modal_cover = _cached_scale(modal_playlist_cover_surface, (220, 220))
            virtual_surface.blit(disp_modal_cover, (img_x, img_y))
        else:
            pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, modal_image_picker_rect)
            draw_spotify_pencil(virtual_surface, img_x + 110, img_y + 110, COLOR_BLACK)
            
        draw_unified_cover_overlay(virtual_surface, modal_image_picker_rect, mouse_pos)
            
        label_meta = _cached_render(font_small, t("Name"), True, COLOR_TEXT_MUTED)
        
        input_x = main_x + 300 if not is_portrait else main_x + 50
        input_y = 185 if not is_portrait else 405
        input_w = main_w - 330 if not is_portrait else main_w - 100
        
        virtual_surface.blit(label_meta, (input_x, input_y - 25))
        
        modal_input_rect = pygame.Rect(input_x, input_y, input_w, 42)
        pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, modal_input_rect, border_radius=6)
        if search_input_active and active_input_field == "name":
            pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, modal_input_rect, width=2, border_radius=6)
            
        if playlist_input_text:
            text_surf = _cached_render(font_body, playlist_input_text, True, COLOR_WHITE)
        else:
            text_surf = _cached_render(font_body, t("My Playlist #1"), True, COLOR_TEXT_MUTED)
        virtual_surface.blit(text_surf, (modal_input_rect.x + 15, modal_input_rect.y + 11))
        
        label_desc = _cached_render(font_small, t("Description"), True, COLOR_TEXT_MUTED)
        virtual_surface.blit(label_desc, (input_x, input_y + 60))
        
        modal_desc_rect = pygame.Rect(input_x, input_y + 85, input_w, 110)
        pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, modal_desc_rect, border_radius=6)
        if search_input_active and active_input_field == "description":
            pygame.draw.rect(virtual_surface, COLOR_SPOTIFY_GREEN, modal_desc_rect, width=2, border_radius=6)
            
        if playlist_desc_text:
            wrapped_lines = get_wrapped_lines(playlist_desc_text, font_small, input_w - 30)
            y_text_line = modal_desc_rect.y + 12
            for line in wrapped_lines:
                if y_text_line + 18 <= modal_desc_rect.bottom:
                    line_surf = _cached_render(font_small, line, True, COLOR_WHITE)
                    virtual_surface.blit(line_surf, (modal_desc_rect.x + 15, y_text_line))
                    y_text_line += 18
        else:
            desc_surf = _cached_render(font_small, t("Add an optional description"), True, COLOR_TEXT_MUTED)
            virtual_surface.blit(desc_surf, (modal_desc_rect.x + 15, modal_desc_rect.y + 12))
        
        desc_lbl = _cached_render(font_small, "Personalize your new local playlist with a clean title and custom description.", True, COLOR_WHITE)
        if not is_portrait:
            virtual_surface.blit(desc_lbl, (main_x + 50, 415))
        else:
            lbl_x = main_x + (main_w - desc_lbl.get_width()) // 2
            virtual_surface.blit(desc_lbl, (max(main_x + 10, lbl_x), input_y + 215))
        
        if is_portrait:
            btn_y = input_y + 250
            start_x = main_x + (main_w - 220) // 2
            modal_close_rect = pygame.Rect(start_x, btn_y, 100, 42)
            modal_save_rect = pygame.Rect(start_x + 120, btn_y, 100, 42)
        else:
            btn_y = 460
            modal_close_rect = pygame.Rect(main_x + 50, btn_y, 100, 42)
            modal_save_rect = pygame.Rect(main_x + 170, btn_y, 100, 42)
        
        c_bg = COLOR_HOVER if modal_close_rect.collidepoint(mouse_pos) else COLOR_CARD_BG
        pygame.draw.rect(virtual_surface, c_bg, modal_close_rect, border_radius=21)
        c_txt = _cached_render(font_body, t("Cancel"), True, COLOR_WHITE)
        virtual_surface.blit(c_txt, (modal_close_rect.x + 24, modal_close_rect.y + 11))
        
        s_bg = (40, 230, 110) if modal_save_rect.collidepoint(mouse_pos) else COLOR_SPOTIFY_GREEN
        pygame.draw.rect(virtual_surface, s_bg, modal_save_rect, border_radius=21)
        s_txt = _cached_render(font_body, t("Save"), True, COLOR_BLACK)
        virtual_surface.blit(s_txt, (modal_save_rect.x + 32, modal_save_rect.y + 11))

    elif show_add_to_playlist_modal:
        pygame.draw.rect(virtual_surface, COLOR_BLACK, (main_x, 0, main_w, HEIGHT - portrait_sidebar_h))
        
        lbl = _cached_render(font_title, t("Add to Playlist"), True, COLOR_WHITE)
        virtual_surface.blit(lbl, (content_pad_x, 40))
        
        track_lbl_text = f"Song: {track_to_add_to_playlist['title']}" if track_to_add_to_playlist else ""
        track_lbl = _cached_render(font_small, track_lbl_text, True, COLOR_TEXT_MUTED)
        virtual_surface.blit(track_lbl, (content_pad_x, 70))
        
        modal_close_rect = pygame.Rect(main_x + main_w - 110, 35, 90, 35)
        c_bg = COLOR_HOVER if modal_close_rect.collidepoint(mouse_pos) else COLOR_LIGHT_GREY
        pygame.draw.rect(virtual_surface, c_bg, modal_close_rect, border_radius=15)
        c_txt = _cached_render(font_small, t("Cancel"), True, COLOR_WHITE)
        virtual_surface.blit(c_txt, (modal_close_rect.x + 23, modal_close_rect.y + 8))
        
        pygame.draw.line(virtual_surface, COLOR_LIGHT_GREY, (content_pad_x, 115), (main_x + main_w - 40, 115), 1)
        
        modal_playlist_rects = []
        p_names = list(custom_playlists.keys())
        
        if not p_names:
            empty_lbl = _cached_render(font_body, t("No custom playlists built yet."), True, COLOR_TEXT_MUTED)
            virtual_surface.blit(empty_lbl, (content_pad_x, 150))
            hint_lbl = _cached_render(font_small, t("Go to 'Your Library' and tap '+' to create one."), True, COLOR_TEXT_MUTED)
            virtual_surface.blit(hint_lbl, (content_pad_x, 180))
            max_music_scroll = 0
        else:
            playlist_available_h = HEIGHT - portrait_sidebar_h
            total_content_height = len(p_names) * 55
            max_music_scroll = max(0, total_content_height - (playlist_available_h - 130) + 30)
            
            clip_rect = pygame.Rect(main_x, 130, main_w, playlist_available_h - 130)
            virtual_surface.set_clip(clip_rect)
            
            y_item = 130 - round(music_grid_scroll_offset)
            for p_name in p_names:
                item_rect = pygame.Rect(main_x + 20, y_item, main_w - 50, 45)
                if item_rect.colliderect(clip_rect):
                    modal_playlist_rects.append((item_rect, p_name))
                    
                    if item_rect.collidepoint(mouse_pos):
                        pygame.draw.rect(virtual_surface, COLOR_HOVER, item_rect, border_radius=6)
                    else:
                        pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, item_rect, border_radius=6)
                        
                    p_lbl = _cached_render(font_body, f" ♫  {p_name}", True, COLOR_WHITE)
                    virtual_surface.blit(p_lbl, (item_rect.x + 15, item_rect.y + 12))
                    
                    count_lbl = _cached_render(font_small, f"{len(custom_playlists[p_name]['tracks'])} tracks", True, COLOR_TEXT_MUTED)
                    virtual_surface.blit(count_lbl, (main_x + main_w - 140, item_rect.y + 14))
                y_item += 55
            virtual_surface.set_clip(None)

def draw_media_bar():
    global play_btn_rect, prev_btn_rect, next_btn_rect, minus_10_btn_rect, plus_10_btn_rect, mediabar_add_btn_rect, mediabar_lyrics_btn_rect, star_btn_rect, shuffle_btn_rect, progress_bar_rect, mediabar_cover_btn_rect, _lyric_cache_key, _lyric_cache_parsed, media_bar_rect
    
    if current_track["title"] == "Select a song" or show_lyrics_editor_view or show_create_playlist_modal or show_add_to_playlist_modal or is_browsing_for_cover or is_browsing_storage or viewing_settings_page:
        media_bar_rect = pygame.Rect(0, 0, 0, 0)
        return

    mouse_pos = get_virtual_mouse_pos()
    is_phone_mode = is_portrait and layout_mode == "phone"

    # --- Compute playback position early so both layout branches can show the active lyric line ---
    elapsed_sec = 0.0
    remaining_sec = 0.0
    percent_fill = 0.0

    if is_dragging_progress:
        elapsed_sec = min(track_duration, drag_seek_target)
        remaining_sec = max(0.0, track_duration - elapsed_sec)
        percent_fill = min(1.0, max(0.0, elapsed_sec / track_duration))
    elif track_duration > 0 and music_loaded:
        if current_backend == "android" and android_media_player:
            try: elapsed_sec = android_media_player.getCurrentPosition() / 1000.0
            except: elapsed_sec = 0.0
        else:
            mix_pos = pygame.mixer.music.get_pos()
            if mix_pos == -1:
                elapsed_sec = track_duration if current_track.get("_has_started", False) else track_start_accumulator
            else:
                elapsed_sec = track_start_accumulator + (mix_pos / 1000.0)

        elapsed_sec = min(track_duration, elapsed_sec)
        remaining_sec = max(0.0, track_duration - elapsed_sec)
        percent_fill = min(1.0, max(0.0, elapsed_sec / track_duration))

    track_ref = current_track.get("path", "")
    current_lyrics_str = song_lyrics_database.get(track_ref, "")
    active_lyric_text = ""
    if current_lyrics_str:
        cache_key = (track_ref, current_lyrics_str)
        if cache_key != _lyric_cache_key:
            parsed_lines = []
            for line in current_lyrics_str.split('\n'):
                line_stripped = line.strip()
                if line_stripped.startswith('[') and ']' in line_stripped:
                    try:
                        time_part, lyric_part = line_stripped.split(']', 1)
                        time_part = time_part[1:].strip()
                        if ':' in time_part:
                            t_parts = time_part.split(':')
                            lyric_time = float(t_parts[0]) * 60 + float(t_parts[1])
                            parsed_lines.append((lyric_time, lyric_part.strip()))
                    except:
                        pass
            _lyric_cache_parsed = parsed_lines
            _lyric_cache_key = cache_key

        best_time = -1
        for lyric_time, lyric_text in _lyric_cache_parsed:
            if lyric_time <= elapsed_sec and lyric_time > best_time:
                best_time = lyric_time
                active_lyric_text = lyric_text

    # --- PHONE MODE: taller 2-row bar ---
    # Row 1 (top): track title + artist left, lyrics/add/star icons right
    # Row 2 (mid): -10  ◀  ▶  ▶  +10  shuffle  — all centred
    # Row 3 (bot): progress bar spanning full width
    if is_phone_mode:
        bar_height = 124
        bar_y = HEIGHT - bar_height - 80   # sit just above the bottom tab bar
        bar_rect = pygame.Rect(0, bar_y, WIDTH, bar_height)
        media_bar_rect = bar_rect
        pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, bar_rect)
        # Icon cluster is centred on its own row; title/artist moved below the progress bar
        ctrl_y = bar_y + 32

        icon_gap = 38   # gap between each icon - pulled in a bit so the cluster
                         # isn't spread so wide it sits right on the screen edges
        # Total span of the 10-icon cluster, centred independently within WIDTH
        cluster_span = icon_gap * 9 + 8 + 6 + 6 + 8
        icons_start_x = (WIDTH - cluster_span) // 2

        lyrics_cx = icons_start_x
        add_cx    = lyrics_cx + icon_gap
        star_cx   = add_cx + icon_gap
        m10_cx    = star_cx + icon_gap + 8
        prev_cx   = m10_cx + icon_gap
        play_cx   = prev_cx + icon_gap + 6
        next_cx   = play_cx + icon_gap + 6
        p10_cx    = next_cx + icon_gap
        sh_cx     = p10_cx + icon_gap + 8
        cover_cx  = sh_cx + icon_gap

        mediabar_lyrics_btn_rect = pygame.Rect(lyrics_cx - 18, ctrl_y - 18, 36, 36)
        mediabar_add_btn_rect    = pygame.Rect(add_cx - 18, ctrl_y - 18, 36, 36)
        star_btn_rect            = pygame.Rect(star_cx - 16, ctrl_y - 16, 32, 32)
        minus_10_btn_rect        = pygame.Rect(m10_cx - 21, ctrl_y - 21, 42, 42)
        prev_btn_rect            = pygame.Rect(prev_cx - 18, ctrl_y - 23, 36, 46)
        play_btn_rect            = pygame.Rect(play_cx - 23, ctrl_y - 23, 46, 46)
        next_btn_rect            = pygame.Rect(next_cx - 18, ctrl_y - 23, 36, 46)
        plus_10_btn_rect         = pygame.Rect(p10_cx - 21, ctrl_y - 21, 42, 42)
        shuffle_btn_rect         = pygame.Rect(sh_cx - 21, ctrl_y - 21, 42, 42)
        mediabar_cover_btn_rect  = pygame.Rect(cover_cx - 18, ctrl_y - 18, 36, 36)

        # Lyrics button
        lyrics_hover = mediabar_lyrics_btn_rect.collidepoint(mouse_pos)
        lyrics_click = lyrics_hover and mouse_held
        if lyrics_click:
            paper_icon_color = COLOR_SPOTIFY_GREEN
        elif lyrics_hover:
            paper_icon_color = COLOR_WHITE
        else:
            paper_icon_color = COLOR_TEXT_MUTED
        draw_piece_of_paper_icon(virtual_surface, mediabar_lyrics_btn_rect, paper_icon_color)

        # Add-to-playlist button
        add_hover = mediabar_add_btn_rect.collidepoint(mouse_pos)
        add_click = add_hover and mouse_held
        if add_click:
            pygame.draw.circle(virtual_surface, (20, 150, 65), mediabar_add_btn_rect.center, 13)
            plus_color = COLOR_WHITE
        elif add_hover:
            pygame.draw.circle(virtual_surface, COLOR_WHITE, mediabar_add_btn_rect.center, 14)
            plus_color = COLOR_BLACK
        else:
            pygame.draw.circle(virtual_surface, COLOR_TEXT_MUTED, mediabar_add_btn_rect.center, 13, width=2)
            plus_color = COLOR_TEXT_MUTED
        plus_surf = _cached_render(font_body, "+", True, plus_color)
        virtual_surface.blit(plus_surf, (mediabar_add_btn_rect.centerx - plus_surf.get_width() // 2,
                                          mediabar_add_btn_rect.centery - plus_surf.get_height() // 2 - 2))

        # Star (like) button
        is_starred = current_track in liked_tracks
        is_star_hovered = star_btn_rect.collidepoint(mouse_pos)
        is_star_clicked = is_star_hovered and mouse_held
        if is_star_clicked:
            star_color = (20, 150, 65) if is_starred else COLOR_SPOTIFY_GREEN
        elif is_star_hovered:
            star_color = COLOR_WHITE if not is_starred else (40, 230, 110)
        else:
            star_color = COLOR_SPOTIFY_GREEN if is_starred else COLOR_TEXT_MUTED
        draw_manual_thumbs_up(virtual_surface, star_btn_rect.x, star_btn_rect.y, star_btn_rect.width, star_btn_rect.height, star_color)

        # -10
        m10_hover = minus_10_btn_rect.collidepoint(mouse_pos)
        m10_click = m10_hover and mouse_held
        if m10_click:
            pygame.draw.circle(virtual_surface, (20, 150, 65), minus_10_btn_rect.center, 21)
            pygame.draw.circle(virtual_surface, COLOR_WHITE, minus_10_btn_rect.center, 21, width=2)
            m10_text_color = COLOR_WHITE
        elif m10_hover:
            pygame.draw.circle(virtual_surface, COLOR_HOVER, minus_10_btn_rect.center, 21)
            pygame.draw.circle(virtual_surface, COLOR_WHITE, minus_10_btn_rect.center, 21, width=2)
            m10_text_color = COLOR_WHITE
        else:
            pygame.draw.circle(virtual_surface, COLOR_TEXT_MUTED, minus_10_btn_rect.center, 21, width=2)
            m10_text_color = COLOR_TEXT_MUTED
        m10_surf = _cached_render(font_small, "-10", True, m10_text_color)
        virtual_surface.blit(m10_surf, (minus_10_btn_rect.centerx - m10_surf.get_width() // 2,
                                         minus_10_btn_rect.centery - m10_surf.get_height() // 2))

        # Prev
        prev_hover = prev_btn_rect.collidepoint(mouse_pos)
        prev_click = prev_hover and mouse_held
        prev_color = COLOR_SPOTIFY_GREEN if prev_click else (COLOR_WHITE if prev_hover else COLOR_TEXT_MUTED)
        pygame.draw.polygon(virtual_surface, prev_color,
                            [(prev_cx + 1, ctrl_y), (prev_cx + 18, ctrl_y - 12), (prev_cx + 18, ctrl_y + 12)])

        # Play/Pause
        is_mb_play_hovered = play_btn_rect.collidepoint(mouse_pos)
        is_mb_play_pressed = is_mb_play_hovered and mouse_held
        if is_mb_play_pressed:
            pygame.draw.circle(virtual_surface, COLOR_TEXT_MUTED, (play_cx, ctrl_y), 21)
        elif is_mb_play_hovered:
            pygame.draw.circle(virtual_surface, COLOR_WHITE, (play_cx, ctrl_y), 25)
        else:
            pygame.draw.circle(virtual_surface, COLOR_WHITE, (play_cx, ctrl_y), 23)
        if not is_playing:
            pygame.draw.polygon(virtual_surface, COLOR_BLACK,
                                [(play_cx - 7, ctrl_y - 9), (play_cx - 7, ctrl_y + 9), (play_cx + 10, ctrl_y)])
        else:
            pygame.draw.rect(virtual_surface, COLOR_BLACK, (play_cx - 8, ctrl_y - 9, 5, 18))
            pygame.draw.rect(virtual_surface, COLOR_BLACK, (play_cx + 3, ctrl_y - 9, 5, 18))

        # Next
        next_hover = next_btn_rect.collidepoint(mouse_pos)
        next_click = next_hover and mouse_held
        next_color = COLOR_SPOTIFY_GREEN if next_click else (COLOR_WHITE if next_hover else COLOR_TEXT_MUTED)
        pygame.draw.polygon(virtual_surface, next_color,
                            [(next_cx - 1, ctrl_y), (next_cx - 18, ctrl_y - 12), (next_cx - 18, ctrl_y + 12)])

        # +10
        p10_hover = plus_10_btn_rect.collidepoint(mouse_pos)
        p10_click = p10_hover and mouse_held
        if p10_click:
            pygame.draw.circle(virtual_surface, (20, 150, 65), plus_10_btn_rect.center, 21)
            pygame.draw.circle(virtual_surface, COLOR_WHITE, plus_10_btn_rect.center, 21, width=2)
            p10_text_color = COLOR_WHITE
        elif p10_hover:
            pygame.draw.circle(virtual_surface, COLOR_HOVER, plus_10_btn_rect.center, 21)
            pygame.draw.circle(virtual_surface, COLOR_WHITE, plus_10_btn_rect.center, 21, width=2)
            p10_text_color = COLOR_WHITE
        else:
            pygame.draw.circle(virtual_surface, COLOR_TEXT_MUTED, plus_10_btn_rect.center, 21, width=2)
            p10_text_color = COLOR_TEXT_MUTED
        p10_surf = _cached_render(font_small, "+10", True, p10_text_color)
        virtual_surface.blit(p10_surf, (plus_10_btn_rect.centerx - p10_surf.get_width() // 2,
                                         plus_10_btn_rect.centery - p10_surf.get_height() // 2))

        # Shuffle
        sh_hover = shuffle_btn_rect.collidepoint(mouse_pos)
        if is_shuffle:
            sh_icon_color = COLOR_SPOTIFY_GREEN
            pygame.draw.circle(virtual_surface, COLOR_SPOTIFY_GREEN,
                               (shuffle_btn_rect.centerx, shuffle_btn_rect.centery + 16), 2)
        else:
            sh_icon_color = COLOR_WHITE if sh_hover else COLOR_TEXT_MUTED
        draw_spotify_shuffle_icon(virtual_surface, shuffle_btn_rect, sh_icon_color)

        # Picture frame (set song cover) button
        cover_hover = mediabar_cover_btn_rect.collidepoint(mouse_pos)
        cover_click = cover_hover and mouse_held
        if cover_click:
            cover_icon_color = COLOR_SPOTIFY_GREEN
        elif cover_hover:
            cover_icon_color = COLOR_WHITE
        else:
            cover_icon_color = COLOR_TEXT_MUTED
        draw_picture_frame_icon(virtual_surface, mediabar_cover_btn_rect, cover_icon_color)

        # --- Row 3: progress bar (shortened to fit time labels) ---
        progress_bar_width = WIDTH - 140
        progress_bar_x = 70
        progress_bar_y = ctrl_y + 34
        progress_bar_rect = pygame.Rect(progress_bar_x, progress_bar_y - 10, progress_bar_width, 24)

        # --- Row 4: active lyric line (falls back to title+artist if no lyric is active), spans available width, centred under the timer bar ---
        # Available width is bounded by the icon row's own left/right edges (lyrics icon to cover icon)
        text_bound_left = mediabar_lyrics_btn_rect.left
        text_bound_right = mediabar_cover_btn_rect.right
        available_text_w = text_bound_right - text_bound_left

        if active_lyric_text:
            display_text = active_lyric_text
            display_color = COLOR_SPOTIFY_GREEN
            trimmed_text = display_text
            now_playing_title = _cached_render(font_body, trimmed_text, True, display_color)
            while trimmed_text and now_playing_title.get_width() > available_text_w:
                trimmed_text = trimmed_text[:-1]
                now_playing_title = _cached_render(font_body, trimmed_text + "...", True, display_color)
            title_row_y = progress_bar_y + 18
            title_row_x = text_bound_left + (available_text_w - now_playing_title.get_width()) // 2
            virtual_surface.blit(now_playing_title, (title_row_x, title_row_y))
        else:
            full_title = current_track["title"]
            full_artist = " - " + current_track["artist"]

            def _render_title_artist(title_str, artist_str):
                t_surf = _cached_render(font_body, title_str, True, COLOR_WHITE)
                a_surf = _cached_render(font_small, artist_str, True, COLOR_TEXT_MUTED)
                return t_surf, a_surf

            now_playing_title, now_playing_artist = _render_title_artist(full_title, full_artist)
            combined_w = now_playing_title.get_width() + now_playing_artist.get_width()

            if combined_w > available_text_w:
                # Progressively shorten the title (keep full artist) until it fits, then add "..."
                trimmed_title = full_title
                while trimmed_title and combined_w > available_text_w:
                    trimmed_title = trimmed_title[:-1]
                    now_playing_title = _cached_render(font_body, trimmed_title + "...", True, COLOR_WHITE)
                    combined_w = now_playing_title.get_width() + now_playing_artist.get_width()

            title_row_y = progress_bar_y + 18
            title_row_x = text_bound_left + (available_text_w - combined_w) // 2
            virtual_surface.blit(now_playing_title, (title_row_x, title_row_y))
            virtual_surface.blit(now_playing_artist, (title_row_x + now_playing_title.get_width(), title_row_y + 2))

    else:
        # -----------------------------------------------------------------------
        # ORIGINAL non-phone layout (desktop / tablet portrait) — UNCHANGED
        # -----------------------------------------------------------------------
        bar_height = 144 if is_portrait else 90
        bar_y = HEIGHT - bar_height - (65 if is_portrait else 0)   # sit above bottom tab bar in portrait
        bar_rect = pygame.Rect(0, bar_y, WIDTH, bar_height)
        media_bar_rect = bar_rect
        pygame.draw.rect(virtual_surface, COLOR_LIGHT_GREY, bar_rect)
        now_playing_title = _cached_render(font_body, current_track["title"] if len(current_track["title"]) < 20 else current_track["title"][:17] + "...", True, COLOR_WHITE)
        now_playing_artist = _cached_render(font_small, current_track["artist"] if len(current_track["artist"]) < 20 else current_track["artist"][:17] + "...", True, COLOR_TEXT_MUTED)
        if not (is_portrait and active_lyric_text):
            virtual_surface.blit(now_playing_title, (20, bar_y + 25))
            virtual_surface.blit(now_playing_artist, (20, bar_y + 45))

        center_x = WIDTH // 2
        center_y = (bar_y + 40) if is_portrait else (HEIGHT - 60)
        btn_offset_x = center_x

        _btn_center_shift = -18 if is_portrait else 0
        star_btn_rect = pygame.Rect(btn_offset_x - 130 + _btn_center_shift, center_y - 10, 20, 20)

        is_starred = current_track in liked_tracks
        is_star_hovered = star_btn_rect.collidepoint(mouse_pos)
        is_star_clicked = is_star_hovered and mouse_held
        if is_star_clicked:
            star_color = (20, 150, 65) if is_starred else COLOR_SPOTIFY_GREEN
        elif is_star_hovered:
            star_color = COLOR_WHITE if not is_starred else (40, 230, 110)
        else:
            star_color = COLOR_SPOTIFY_GREEN if is_starred else COLOR_TEXT_MUTED
        draw_manual_thumbs_up(virtual_surface, star_btn_rect.x, star_btn_rect.y, star_btn_rect.width, star_btn_rect.height, star_color)

        mediabar_lyrics_btn_rect = pygame.Rect(btn_offset_x - 165 + _btn_center_shift, center_y - 14, 28, 28)
        mediabar_add_btn_rect    = pygame.Rect(btn_offset_x - 95 + _btn_center_shift, center_y - 14, 28, 28)
        minus_10_btn_rect        = pygame.Rect(btn_offset_x - 55 + _btn_center_shift, center_y - 16, 32, 32)
        prev_btn_rect            = pygame.Rect(btn_offset_x - 18 + _btn_center_shift, center_y - 18, 28, 36)
        play_btn_rect            = pygame.Rect(btn_offset_x + 15 + _btn_center_shift, center_y - 18, 36, 36)
        next_btn_rect            = pygame.Rect(btn_offset_x + 56 + _btn_center_shift, center_y - 18, 28, 36)
        plus_10_btn_rect         = pygame.Rect(btn_offset_x + 90 + _btn_center_shift, center_y - 16, 32, 32)
        shuffle_btn_rect         = pygame.Rect(btn_offset_x + 132 + _btn_center_shift, center_y - 16, 32, 32)
        mediabar_cover_btn_rect  = pygame.Rect(btn_offset_x + 174 + _btn_center_shift, center_y - 14, 28, 28)

        lyrics_hover = mediabar_lyrics_btn_rect.collidepoint(mouse_pos)
        lyrics_click = lyrics_hover and mouse_held
        if lyrics_click:
            paper_icon_color = COLOR_SPOTIFY_GREEN
        elif lyrics_hover:
            paper_icon_color = COLOR_WHITE
        else:
            paper_icon_color = COLOR_TEXT_MUTED
        draw_piece_of_paper_icon(virtual_surface, mediabar_lyrics_btn_rect, paper_icon_color)

        add_hover = mediabar_add_btn_rect.collidepoint(mouse_pos)
        add_click = add_hover and mouse_held
        if add_click:
            pygame.draw.circle(virtual_surface, (20, 150, 65), mediabar_add_btn_rect.center, 13)
            plus_color = COLOR_WHITE
        elif add_hover:
            pygame.draw.circle(virtual_surface, COLOR_WHITE, mediabar_add_btn_rect.center, 14)
            plus_color = COLOR_BLACK
        else:
            pygame.draw.circle(virtual_surface, COLOR_TEXT_MUTED, mediabar_add_btn_rect.center, 13, width=2)
            plus_color = COLOR_TEXT_MUTED
        plus_surf = _cached_render(font_body, "+", True, plus_color)
        plus_x = mediabar_add_btn_rect.centerx - plus_surf.get_width() // 2
        plus_y = mediabar_add_btn_rect.centery - plus_surf.get_height() // 2 - 2
        virtual_surface.blit(plus_surf, (plus_x, plus_y))

        m10_hover = minus_10_btn_rect.collidepoint(mouse_pos)
        m10_click = m10_hover and mouse_held
        if m10_click:
            pygame.draw.circle(virtual_surface, (20, 150, 65), minus_10_btn_rect.center, 16)
            pygame.draw.circle(virtual_surface, COLOR_WHITE, minus_10_btn_rect.center, 16, width=2)
            m10_text_color = COLOR_WHITE
        elif m10_hover:
            pygame.draw.circle(virtual_surface, COLOR_HOVER, minus_10_btn_rect.center, 16)
            pygame.draw.circle(virtual_surface, COLOR_WHITE, minus_10_btn_rect.center, 16, width=2)
            m10_text_color = COLOR_WHITE
        else:
            pygame.draw.circle(virtual_surface, COLOR_TEXT_MUTED, minus_10_btn_rect.center, 16, width=2)
            m10_text_color = COLOR_TEXT_MUTED
        m10_surf = _cached_render(font_small, "-10", True, m10_text_color)
        virtual_surface.blit(m10_surf, (minus_10_btn_rect.centerx - m10_surf.get_width() // 2, minus_10_btn_rect.centery - m10_surf.get_height() // 2))

        prev_hover = prev_btn_rect.collidepoint(mouse_pos)
        prev_click = prev_hover and mouse_held
        prev_color = COLOR_SPOTIFY_GREEN if prev_click else (COLOR_WHITE if prev_hover else COLOR_TEXT_MUTED)
        pygame.draw.polygon(virtual_surface, prev_color, [(btn_offset_x - 15 + _btn_center_shift, center_y), (btn_offset_x + _btn_center_shift, center_y - 9), (btn_offset_x + _btn_center_shift, center_y + 9)])

        is_mb_play_hovered = play_btn_rect.collidepoint(mouse_pos)
        is_mb_play_pressed = is_mb_play_hovered and mouse_held
        if is_mb_play_pressed:
            pygame.draw.circle(virtual_surface, COLOR_TEXT_MUTED, (btn_offset_x + 33 + _btn_center_shift, center_y), 16)
        elif is_mb_play_hovered:
            pygame.draw.circle(virtual_surface, COLOR_WHITE, (btn_offset_x + 33 + _btn_center_shift, center_y), 20)
        else:
            pygame.draw.circle(virtual_surface, COLOR_WHITE, (btn_offset_x + 33 + _btn_center_shift, center_y), 18)
        if not is_playing:
            pygame.draw.polygon(virtual_surface, COLOR_BLACK, [(btn_offset_x + 30 + _btn_center_shift, center_y - 6), (btn_offset_x + 30 + _btn_center_shift, center_y + 6), (btn_offset_x + 40 + _btn_center_shift, center_y)])
        else:
            pygame.draw.rect(virtual_surface, COLOR_BLACK, (btn_offset_x + 29 + _btn_center_shift, center_y - 6, 3, 12))
            pygame.draw.rect(virtual_surface, COLOR_BLACK, (btn_offset_x + 35 + _btn_center_shift, center_y - 6, 3, 12))

        next_hover = next_btn_rect.collidepoint(mouse_pos)
        next_click = next_hover and mouse_held
        next_color = COLOR_SPOTIFY_GREEN if next_click else (COLOR_WHITE if next_hover else COLOR_TEXT_MUTED)
        pygame.draw.polygon(virtual_surface, next_color, [(btn_offset_x + 80 + _btn_center_shift, center_y), (btn_offset_x + 65 + _btn_center_shift, center_y - 9), (btn_offset_x + 65 + _btn_center_shift, center_y + 9)])

        p10_hover = plus_10_btn_rect.collidepoint(mouse_pos)
        p10_click = p10_hover and mouse_held
        if p10_click:
            pygame.draw.circle(virtual_surface, (20, 150, 65), plus_10_btn_rect.center, 16)
            pygame.draw.circle(virtual_surface, COLOR_WHITE, plus_10_btn_rect.center, 16, width=2)
            p10_text_color = COLOR_WHITE
        elif p10_hover:
            pygame.draw.circle(virtual_surface, COLOR_HOVER, plus_10_btn_rect.center, 16)
            pygame.draw.circle(virtual_surface, COLOR_WHITE, plus_10_btn_rect.center, 16, width=2)
            p10_text_color = COLOR_WHITE
        else:
            pygame.draw.circle(virtual_surface, COLOR_TEXT_MUTED, plus_10_btn_rect.center, 16, width=2)
            p10_text_color = COLOR_TEXT_MUTED
        p10_surf = _cached_render(font_small, "+10", True, p10_text_color)
        virtual_surface.blit(p10_surf, (plus_10_btn_rect.centerx - p10_surf.get_width() // 2, plus_10_btn_rect.centery - p10_surf.get_height() // 2))

        sh_hover = shuffle_btn_rect.collidepoint(mouse_pos)
        if is_shuffle:
            sh_icon_color = COLOR_SPOTIFY_GREEN
            pygame.draw.circle(virtual_surface, COLOR_SPOTIFY_GREEN, (shuffle_btn_rect.centerx, shuffle_btn_rect.centery + 12), 2)
        else:
            sh_icon_color = COLOR_WHITE if sh_hover else COLOR_TEXT_MUTED
        draw_spotify_shuffle_icon(virtual_surface, shuffle_btn_rect, sh_icon_color)

        cover_hover = mediabar_cover_btn_rect.collidepoint(mouse_pos)
        cover_click = cover_hover and mouse_held
        if cover_click:
            cover_icon_color = COLOR_SPOTIFY_GREEN
        elif cover_hover:
            cover_icon_color = COLOR_WHITE
        else:
            cover_icon_color = COLOR_TEXT_MUTED
        draw_picture_frame_icon(virtual_surface, mediabar_cover_btn_rect, cover_icon_color)

        progress_bar_width = min(WIDTH - 140, WIDTH - 40) if is_portrait else 400
        progress_bar_x = center_x - (progress_bar_width // 2) if is_portrait else btn_offset_x - (progress_bar_width // 2) + 20
        progress_bar_y = (bar_y + 80) if is_portrait else (HEIGHT - 25)
        progress_bar_rect = pygame.Rect(progress_bar_x, progress_bar_y - 10, progress_bar_width, 24)

        if is_portrait:
            # --- PORTRAIT: lyric line sits under the song timer bar, centred, capped to the same width as the timer bar ---
            lyric_row_y = progress_bar_y + 28
            lyric_max_w = progress_bar_width
            lyric_clip_rect = pygame.Rect(progress_bar_x, lyric_row_y, lyric_max_w, 18)
            if active_lyric_text:
                trimmed_text = active_lyric_text
                lyric_surf = _cached_render(font_small, trimmed_text, True, COLOR_SPOTIFY_GREEN)
                while trimmed_text and lyric_surf.get_width() > lyric_max_w:
                    trimmed_text = trimmed_text[:-1]
                    lyric_surf = _cached_render(font_small, trimmed_text + "...", True, COLOR_SPOTIFY_GREEN)
                if trimmed_text:
                    lyric_x = progress_bar_x + (lyric_max_w - lyric_surf.get_width()) // 2
                    virtual_surface.set_clip(lyric_clip_rect)
                    virtual_surface.blit(lyric_surf, (lyric_x, lyric_row_y))
                    virtual_surface.set_clip(None)
            # else: gap stays invisible/empty, nothing drawn

        if not is_portrait:
            # --- LANDSCAPE: invisible box barrier so the lyric ticker can never go outside it ---
            # Anchored well clear of the icons, lower toward the bottom of the bar;
            # if there's no active lyric the gap simply stays invisible
            lyric_clip_left = btn_offset_x + 280
            lyric_clip_right = WIDTH - 30
            lyric_row_y = center_y - 7
            if lyric_clip_right > lyric_clip_left and active_lyric_text:
                lyric_clip_w = max(0, lyric_clip_right - lyric_clip_left)
                lyric_clip_rect = pygame.Rect(lyric_clip_left, lyric_row_y, lyric_clip_w, 24)
                trimmed_text = active_lyric_text
                lyric_surf = _cached_render(font_small, trimmed_text, True, COLOR_SPOTIFY_GREEN)
                # Trim with a safety margin so the rendered text never reaches the box edge
                while trimmed_text and lyric_surf.get_width() > max(0, lyric_clip_w - 8):
                    trimmed_text = trimmed_text[:-1]
                    lyric_surf = _cached_render(font_small, trimmed_text + "...", True, COLOR_SPOTIFY_GREEN)
                if trimmed_text:
                    virtual_surface.set_clip(lyric_clip_rect)
                    virtual_surface.blit(lyric_surf, (lyric_clip_left, lyric_row_y))
                    virtual_surface.set_clip(None)
            # else: gap stays invisible/empty, nothing drawn
    
    pygame.draw.rect(virtual_surface, COLOR_HOVER, (progress_bar_x, progress_bar_y, progress_bar_width, 4), border_radius=2)
    pygame.draw.rect(virtual_surface, COLOR_WHITE, (progress_bar_x, progress_bar_y, int(progress_bar_width * percent_fill), 4), border_radius=2)
    
    el_min, el_sec = int(elapsed_sec) // 60, int(elapsed_sec) % 60
    rem_min, rem_sec = int(remaining_sec) // 60, int(remaining_sec) % 60
    
    time_start = _cached_render(font_small, f"{el_min}:{el_sec:02d}", True, COLOR_TEXT_MUTED)
    time_end = _cached_render(font_small, f"-{rem_min}:{rem_sec:02d}" if track_duration > 0 else "0:00", True, COLOR_TEXT_MUTED)
    
    virtual_surface.blit(time_start, (progress_bar_x - 35, progress_bar_y - 6))
    virtual_surface.blit(time_end, (progress_bar_x + progress_bar_width + 10, progress_bar_y - 6))


# --- MAIN LOOP ---
load_app_data()
search_message = t("Tap '+ Add Folder' to open the built-in storage browser.")
if onboarding_complete:
    # Returning user — same behavior as before: request permissions right away.
    request_android_permissions()
else:
    # First launch ever — hold off on the OS permission dialogs; the
    # onboarding screens below trigger them one at a time via their buttons.
    onboarding_stage = "welcome"
    onboarding_anim_start = time.time()
set_android_orientation(layout_mode == "phone")
if layout_mode == "phone":
    is_portrait = True

running = True


virtual_keyboard_active = False
mouse_held = False
mouse_just_released = False
button_flash_frames = 0
# Most recent touch position as SDL's own normalized [0,1] finger coordinates
# (from FINGERDOWN/FINGERMOTION/FINGERUP). These are resolution-independent by
# definition, unlike the synthesized MOUSEBUTTONDOWN/UP event.pos Android
# derives from them - if SDL's touch-to-pixel translation is using a stale
# window size internally, event.pos can be scaled wrong in a way nothing on
# the Python side can detect or correct. Preferring the raw normalized touch
# position sidesteps that class of bug entirely. None on desktop (no touches).
_last_touch_norm = None
# Per-gesture snapshots of the normalized touch position, captured exactly once
# at FINGERDOWN/FINGERUP and consumed exactly once by the synthesized
# MOUSEBUTTONDOWN/MOUSEBUTTONUP that follows. Needed because _last_touch_norm
# above is a single shared "most recent touch" value: if a second tap starts
# before the first tap's delayed synthesized mouse event has arrived (the SDL
# lag documented above), _last_touch_norm gets overwritten by the second touch
# before the first touch's MOUSEBUTTONUP is processed - so the first tap's
# click ends up acting on wherever the second touch landed instead of where it
# was actually pressed. This was the cause of tapping a media bar button also
# registering on the song row underneath it. Snapshotting per-gesture and
# consuming (then clearing) on use avoids that mix-up.
_pending_touch_down_norm = None
_pending_touch_up_norm = None
# Timestamp of the last onboarding click handled directly from a FINGERDOWN
# event (see the FINGERDOWN handler below). Used to stop the synthesized
# MOUSEBUTTONDOWN that follows a real touch from re-handling the same tap.
_last_onboarding_finger_click_time = 0.0

while running:
    # Keep REAL_WIDTH/REAL_HEIGHT in sync with the actual window size every frame.
    # On some Android devices the fullscreen window's true size keeps settling for a
    # frame or two after it's created, so a single one-time re-measurement (as used
    # to happen right before this loop) can still catch a stale value. That stale
    # value silently breaks touch accuracy: rendering still looks fine (it just uses
    # whatever WIDTH/HEIGHT was derived from it), but get_virtual_mouse_pos() scales
    # every tap by REAL_HEIGHT/HEIGHT, so a too-small REAL_HEIGHT makes taps register
    # lower than where you actually touched — you end up having to tap above a button
    # to hit it. Re-checking every frame means it self-corrects the instant the OS
    # reports the settled size, with no rotation/resize needed to trigger it.
    _cur_w, _cur_h = screen.get_size()
    if (_cur_w, _cur_h) != (REAL_WIDTH, REAL_HEIGHT):
        REAL_WIDTH, REAL_HEIGHT = _cur_w, _cur_h
        if layout_mode == "phone":
            is_portrait = True
        else:
            is_portrait = REAL_HEIGHT > REAL_WIDTH
        if layout_mode == "phone":
            _calc_w, _calc_h = (REAL_WIDTH, REAL_HEIGHT) if REAL_HEIGHT >= REAL_WIDTH else (REAL_HEIGHT, REAL_WIDTH)
            WIDTH, HEIGHT = compute_virtual_size(_calc_w, _calc_h, is_portrait, layout_mode)
        else:
            WIDTH, HEIGHT = compute_virtual_size(REAL_WIDTH, REAL_HEIGHT, is_portrait, layout_mode)
        virtual_surface = pygame.Surface((WIDTH, HEIGHT)).convert()

    if _permissions_just_granted:
        _permissions_just_granted = False
        try:
            rebuild_imported_tracks()
        except Exception:
            pass

    # Onboarding "notifications"/"storage" screens only advance once the OS
    # permission result actually comes back - not the instant the button is
    # tapped. Polled every frame while onboarding_awaiting_permission is set.
    if onboarding_awaiting_permission and onboarding_stage == "notifications":
        if _notification_permission_result is True:
            onboarding_awaiting_permission = False
            onboarding_stage = "storage"
            onboarding_anim_start = time.time()
            _refresh_onboarding_rects()
        elif _notification_permission_result is False:
            onboarding_awaiting_permission = False  # denied - let them try again from the same screen
    elif onboarding_awaiting_permission and onboarding_stage == "storage":
        # Sequenced: wait for the legacy runtime dialog to be answered first,
        # THEN (only once) open the Android 11+ "All files access" settings
        # screen if it's still needed, THEN wait for access to actually show
        # up as granted. Never overlaps the dialog and the settings screen.
        if not _storage_legacy_perm_done:
            pass
        elif not _manage_storage_intent_launched:
            _manage_storage_intent_launched = True
            try:
                _maybe_request_manage_external_storage()  # no-ops if already granted or below Android 11
            except Exception:
                pass
        elif _check_storage_access_granted():
            onboarding_awaiting_permission = False
            onboarding_stage = "folder"
            onboarding_anim_start = time.time()
            _refresh_onboarding_rects()

    # Once the onboarding "scrape" background job (see start_onboarding_scrape)
    # finishes, close out onboarding for good - it was the last step.
    if onboarding_stage == "scrape" and not onboarding_scrape_active and auto_scrape_media is True:
        onboarding_complete = True
        onboarding_stage = None
        save_app_data()

    # Pick up the result of a background artwork download started from the
    # "Search Album Art" modal (see start_apply_itunes_art). We poll here
    # instead of blocking in the click handler so the UI stays responsive
    # while the download is in flight.
    if not art_apply_pending and art_apply_result_path is not None:
        tmp_path = art_apply_result_path
        t_path = art_apply_track_path
        art_apply_result_path = None
        art_apply_track_path = None
        if tmp_path:
            try:
                with open(tmp_path, "rb") as _cover_f:
                    _cover_bytes = _cover_f.read()
                raw_img = _decode_image_bytes_safely(_cover_bytes)
                raw_img = raw_img.convert()  # normalize to the display's pixel format (main thread only) before smoothscale/blit
                grid_cover_surf = pygame.transform.smoothscale(raw_img, (130, 130))
                track_covers[t_path] = {"image_path": tmp_path, "surface": grid_cover_surf}
                if current_track.get("path") == t_path:
                    current_track["cover_surface"] = grid_cover_surf
                for trk in imported_tracks:
                    if trk["path"] == t_path:
                        trk["cover_surface"] = grid_cover_surf
                for trk in liked_tracks:
                    if trk["path"] == t_path:
                        trk["cover_surface"] = grid_cover_surf
                for p_data in custom_playlists.values():
                    for trk in p_data["tracks"]:
                        if trk["path"] == t_path:
                            trk["cover_surface"] = grid_cover_surf
                save_app_data()
                show_art_search_modal = False
                is_browsing_for_cover = False
            except Exception as art_err:
                art_search_error = f"Failed - {art_err}"
        # if tmp_path is falsy, apply_itunes_art already set art_search_error
        # with the real failure reason, so the modal just shows that message.

    # Button highlight: count down flash frames so highlight shows for at least 2
    # rendered frames even when FINGERDOWN+FINGERUP arrive in the same event pump
    if button_flash_frames > 0:
        button_flash_frames -= 1
        mouse_held = True
    else:
        mouse_held = False
    mouse_just_released = False

    if search_input_active and not virtual_keyboard_active:
        try: pygame.key.start_text_input()
        except: pass
        virtual_keyboard_active = True
    elif not search_input_active and virtual_keyboard_active:
        try: pygame.key.stop_text_input()
        except: pass
        virtual_keyboard_active = False

    dt = min(0.05, clock.get_time() / 1000.0)

    frame_had_input = False
    
    # Real inertial-scroll physics (velocity + friction decay + rubber-band)
    # for areas currently decelerating from a flick; a snappy ease-to-target
    # for everything else. See _update_scroll_physics / SCROLL_AREAS above.
    _update_scroll_physics(dt)
    if max_btn_row_scroll > 0:
        if target_btn_row_scroll > 100000 or target_btn_row_scroll < -100000:
            target_btn_row_scroll %= max_btn_row_scroll
            btn_row_scroll_offset %= max_btn_row_scroll

    if mouse_held or is_dragging_progress:
        frame_had_input = True

    _finger_moved_this_frame = False

    for event in pygame.event.get():
        if event.type in (pygame.MOUSEBUTTONDOWN, pygame.MOUSEBUTTONUP, pygame.MOUSEMOTION, pygame.KEYDOWN, pygame.TEXTINPUT, pygame.VIDEORESIZE, pygame.FINGERDOWN, pygame.FINGERUP, pygame.FINGERMOTION):
            frame_had_input = True
        if event.type == pygame.QUIT:
            running = False
            
        elif event.type == pygame.VIDEORESIZE:
            REAL_WIDTH, REAL_HEIGHT = event.w, event.h
            if layout_mode == "phone":
                # Phone mode is locked to portrait — never fall back to landscape/desktop layout
                is_portrait = True
                _calc_w, _calc_h = (REAL_WIDTH, REAL_HEIGHT) if REAL_HEIGHT >= REAL_WIDTH else (REAL_HEIGHT, REAL_WIDTH)
                WIDTH, HEIGHT = compute_virtual_size(_calc_w, _calc_h, is_portrait, layout_mode)
            else:
                is_portrait = REAL_HEIGHT > REAL_WIDTH
                WIDTH, HEIGHT = compute_virtual_size(REAL_WIDTH, REAL_HEIGHT, is_portrait, layout_mode)
            screen = pygame.display.set_mode(
                (REAL_WIDTH, REAL_HEIGHT),
                (pygame.FULLSCREEN | pygame.RESIZABLE) if IS_ANDROID else pygame.RESIZABLE
            )
            virtual_surface = pygame.Surface((WIDTH, HEIGHT)).convert()
            
        elif event.type == pygame.TEXTINPUT:
            if search_input_active:
                if show_lyrics_editor_view and active_input_field == "lyrics":
                    track_ref = current_track.get("path", "")
                    txt = song_lyrics_database.get(track_ref, "")
                    if lyrics_cursor_pos > len(txt): lyrics_cursor_pos = len(txt)
                    new_txt = txt[:lyrics_cursor_pos] + event.text + txt[lyrics_cursor_pos:]
                    song_lyrics_database[track_ref] = new_txt
                    lyrics_cursor_pos += len(event.text)
                    lyrics_text_changed = True
                elif show_lyrics_editor_view and show_lyrics_manual_modal:
                    clean_text = event.text.replace("\n", "").replace("\r", "")
                    if active_input_field == "manual_title" and len(manual_title_text) < 60:
                        if HAS_ANDROID_MEDIA:
                            manual_title_text += clean_text
                            manual_title_cursor = len(manual_title_text)
                        else:
                            c = min(manual_title_cursor, len(manual_title_text))
                            manual_title_text = manual_title_text[:c] + clean_text + manual_title_text[c:]
                            manual_title_cursor = c + len(clean_text)
                    elif active_input_field == "manual_artist" and len(manual_artist_text) < 40:
                        if HAS_ANDROID_MEDIA:
                            manual_artist_text += clean_text
                            manual_artist_cursor = len(manual_artist_text)
                        else:
                            c = min(manual_artist_cursor, len(manual_artist_text))
                            manual_artist_text = manual_artist_text[:c] + clean_text + manual_artist_text[c:]
                            manual_artist_cursor = c + len(clean_text)
                elif show_art_search_modal and show_art_manual_modal:
                    if active_input_field == "art_manual_title" and len(manual_title_text) < 60:
                        if HAS_ANDROID_MEDIA:
                            manual_title_text += event.text
                            manual_title_cursor = len(manual_title_text)
                        else:
                            c = min(manual_title_cursor, len(manual_title_text))
                            manual_title_text = manual_title_text[:c] + event.text + manual_title_text[c:]
                            manual_title_cursor = c + len(event.text)
                    elif active_input_field == "art_manual_artist" and len(manual_artist_text) < 40:
                        if HAS_ANDROID_MEDIA:
                            manual_artist_text += event.text
                            manual_artist_cursor = len(manual_artist_text)
                        else:
                            c = min(manual_artist_cursor, len(manual_artist_text))
                            manual_artist_text = manual_artist_text[:c] + event.text + manual_artist_text[c:]
                            manual_artist_cursor = c + len(event.text)
                elif show_create_playlist_modal:
                    if active_input_field == "name" and len(playlist_input_text) < 20:
                        playlist_input_text += event.text
                    elif active_input_field == "description":
                        lines_test = get_wrapped_lines(playlist_desc_text + event.text, font_small, 420)
                        if len(lines_test) * 18 <= 90:
                            playlist_desc_text += event.text
                elif current_page == "Search" and not is_browsing_storage and not viewing_settings_page:
                    if len(search_query) < 25:
                        search_query += event.text

        elif event.type == pygame.KEYDOWN:
            mods = pygame.key.get_mods()
            is_ctrl_or_cmd = (mods & pygame.KMOD_CTRL) or (mods & pygame.KMOD_META)

            if event.key == pygame.K_F5:
                _debug_reveal = not _debug_reveal

            if event.key == pygame.K_ESCAPE:
                search_input_active = False

            if is_ctrl_or_cmd and event.key == pygame.K_v and search_input_active:
                pasted_text = get_clipboard_text()
                
                if pasted_text:
                    if show_lyrics_editor_view and active_input_field == "lyrics":
                        track_ref = current_track.get("path", "")
                        txt = song_lyrics_database.get(track_ref, "")
                        if lyrics_cursor_pos > len(txt): lyrics_cursor_pos = len(txt)
                        song_lyrics_database[track_ref] = txt[:lyrics_cursor_pos] + pasted_text + txt[lyrics_cursor_pos:]
                        lyrics_cursor_pos += len(pasted_text)
                        lyrics_text_changed = True
                    elif show_lyrics_editor_view and show_lyrics_manual_modal:
                        clean_paste = pasted_text.replace("\n", " ").replace("\r", "")
                        if active_input_field == "manual_title":
                            manual_title_text = (manual_title_text + clean_paste)[:60]
                        elif active_input_field == "manual_artist":
                            manual_artist_text = (manual_artist_text + clean_paste)[:40]
                    elif show_art_search_modal and show_art_manual_modal:
                        if active_input_field == "art_manual_title":
                            manual_title_text = (manual_title_text + pasted_text)[:60]
                        elif active_input_field == "art_manual_artist":
                            manual_artist_text = (manual_artist_text + pasted_text)[:40]
                    elif show_create_playlist_modal:
                        if active_input_field == "name":
                            playlist_input_text = (playlist_input_text + pasted_text)[:20]
                        elif active_input_field == "description":
                            playlist_desc_text += pasted_text
                    elif current_page == "Search" and not is_browsing_storage and not viewing_settings_page:
                        search_query = (search_query + pasted_text)[:25]
                continue

            if show_lyrics_editor_view and search_input_active and active_input_field == "lyrics":
                track_ref = current_track.get("path", "")
                lyrics_txt = song_lyrics_database.get(track_ref, "")
                if lyrics_cursor_pos > len(lyrics_txt): lyrics_cursor_pos = len(lyrics_txt)
                
                if event.key == pygame.K_BACKSPACE:
                    if lyrics_cursor_pos > 0:
                        song_lyrics_database[track_ref] = lyrics_txt[:lyrics_cursor_pos - 1] + lyrics_txt[lyrics_cursor_pos:]
                        lyrics_cursor_pos -= 1
                        lyrics_text_changed = True
                elif event.key == pygame.K_DELETE:
                    if lyrics_cursor_pos < len(lyrics_txt):
                        song_lyrics_database[track_ref] = lyrics_txt[:lyrics_cursor_pos] + lyrics_txt[lyrics_cursor_pos + 1:]
                        lyrics_text_changed = True
                elif event.key == pygame.K_RETURN:
                    song_lyrics_database[track_ref] = lyrics_txt[:lyrics_cursor_pos] + "\n" + lyrics_txt[lyrics_cursor_pos:]
                    lyrics_cursor_pos += 1
                    lyrics_text_changed = True
                elif event.key == pygame.K_LEFT:
                    if lyrics_cursor_pos > 0:
                        lyrics_cursor_pos -= 1
                elif event.key == pygame.K_RIGHT:
                    if lyrics_cursor_pos < len(lyrics_txt):
                        lyrics_cursor_pos += 1
                elif event.key == pygame.K_UP:
                    lines_before = lyrics_txt[:lyrics_cursor_pos].split('\n')
                    if len(lines_before) > 1:
                        current_line_offset = len(lines_before[-1])
                        prev_line_len = len(lines_before[-2])
                        target_offset = min(current_line_offset, prev_line_len)
                        lyrics_cursor_pos = len('\n'.join(lines_before[:-1])) - prev_line_len + target_offset
                elif event.key == pygame.K_DOWN:
                    lines_before = lyrics_txt[:lyrics_cursor_pos].split('\n')
                    lines_after = lyrics_txt[lyrics_cursor_pos:].split('\n')
                    if len(lines_after) > 1:
                        current_line_offset = len(lines_before[-1])
                        next_line_len = len(lines_after[1])
                        target_offset = min(current_line_offset, next_line_len)
                        lyrics_cursor_pos = len(lyrics_txt[:lyrics_cursor_pos]) + len(lines_after[0]) + 1 + target_offset
                elif event.key == pygame.K_ESCAPE:
                    search_input_active = False
                        
            elif show_lyrics_editor_view and show_lyrics_manual_modal and search_input_active:
                if event.key == pygame.K_BACKSPACE:
                    if active_input_field == "manual_title" and manual_title_text:
                        c = min(manual_title_cursor, len(manual_title_text))
                        if c > 0:
                            manual_title_text   = manual_title_text[:c-1] + manual_title_text[c:]
                            manual_title_cursor = c - 1
                    elif active_input_field == "manual_artist" and manual_artist_text:
                        c = min(manual_artist_cursor, len(manual_artist_text))
                        if c > 0:
                            manual_artist_text   = manual_artist_text[:c-1] + manual_artist_text[c:]
                            manual_artist_cursor = c - 1
                elif event.key == pygame.K_DELETE and not HAS_ANDROID_MEDIA:
                    if active_input_field == "manual_title":
                        c = min(manual_title_cursor, len(manual_title_text))
                        manual_title_text = manual_title_text[:c] + manual_title_text[c+1:]
                    elif active_input_field == "manual_artist":
                        c = min(manual_artist_cursor, len(manual_artist_text))
                        manual_artist_text = manual_artist_text[:c] + manual_artist_text[c+1:]
                elif event.key == pygame.K_LEFT and not HAS_ANDROID_MEDIA:
                    if active_input_field == "manual_title":
                        manual_title_cursor  = max(0, manual_title_cursor - 1)
                    elif active_input_field == "manual_artist":
                        manual_artist_cursor = max(0, manual_artist_cursor - 1)
                elif event.key == pygame.K_RIGHT and not HAS_ANDROID_MEDIA:
                    if active_input_field == "manual_title":
                        manual_title_cursor  = min(len(manual_title_text),  manual_title_cursor  + 1)
                    elif active_input_field == "manual_artist":
                        manual_artist_cursor = min(len(manual_artist_text), manual_artist_cursor + 1)
                elif event.key == pygame.K_HOME and not HAS_ANDROID_MEDIA:
                    if active_input_field == "manual_title":   manual_title_cursor  = 0
                    elif active_input_field == "manual_artist": manual_artist_cursor = 0
                elif event.key == pygame.K_END and not HAS_ANDROID_MEDIA:
                    if active_input_field == "manual_title":   manual_title_cursor  = len(manual_title_text)
                    elif active_input_field == "manual_artist": manual_artist_cursor = len(manual_artist_text)
                elif event.key == pygame.K_TAB:
                    active_input_field = "manual_artist" if active_input_field == "manual_title" else "manual_title"
                elif event.key == pygame.K_RETURN:
                    if manual_title_text.strip():
                        show_lyrics_manual_modal = False
                        search_input_active = False
                        if not HAS_ANDROID_MEDIA: pygame.key.set_repeat(0, 0)
                        try:
                            start_lyrics_search(manual_title_text.strip(), manual_artist_text.strip())
                        except Exception as e:
                            show_lyrics_search_modal = True
                            lyrics_search_loading = False
                            lyrics_search_results = []
                            lyrics_search_error = f"Failed - {type(e).__name__}: {e}"
                elif event.key == pygame.K_ESCAPE:
                    search_input_active = False
                    if not HAS_ANDROID_MEDIA: pygame.key.set_repeat(0, 0)

            elif show_art_search_modal and show_art_manual_modal and search_input_active:
                if event.key == pygame.K_BACKSPACE:
                    if active_input_field == "art_manual_title" and manual_title_text:
                        c = min(manual_title_cursor, len(manual_title_text))
                        if c > 0:
                            manual_title_text   = manual_title_text[:c-1] + manual_title_text[c:]
                            manual_title_cursor = c - 1
                    elif active_input_field == "art_manual_artist" and manual_artist_text:
                        c = min(manual_artist_cursor, len(manual_artist_text))
                        if c > 0:
                            manual_artist_text   = manual_artist_text[:c-1] + manual_artist_text[c:]
                            manual_artist_cursor = c - 1
                elif event.key == pygame.K_DELETE and not HAS_ANDROID_MEDIA:
                    if active_input_field == "art_manual_title":
                        c = min(manual_title_cursor, len(manual_title_text))
                        manual_title_text = manual_title_text[:c] + manual_title_text[c+1:]
                    elif active_input_field == "art_manual_artist":
                        c = min(manual_artist_cursor, len(manual_artist_text))
                        manual_artist_text = manual_artist_text[:c] + manual_artist_text[c+1:]
                elif event.key == pygame.K_LEFT and not HAS_ANDROID_MEDIA:
                    if active_input_field == "art_manual_title":
                        manual_title_cursor  = max(0, manual_title_cursor  - 1)
                    elif active_input_field == "art_manual_artist":
                        manual_artist_cursor = max(0, manual_artist_cursor - 1)
                elif event.key == pygame.K_RIGHT and not HAS_ANDROID_MEDIA:
                    if active_input_field == "art_manual_title":
                        manual_title_cursor  = min(len(manual_title_text),  manual_title_cursor  + 1)
                    elif active_input_field == "art_manual_artist":
                        manual_artist_cursor = min(len(manual_artist_text), manual_artist_cursor + 1)
                elif event.key == pygame.K_HOME and not HAS_ANDROID_MEDIA:
                    if active_input_field == "art_manual_title":   manual_title_cursor  = 0
                    elif active_input_field == "art_manual_artist": manual_artist_cursor = 0
                elif event.key == pygame.K_END and not HAS_ANDROID_MEDIA:
                    if active_input_field == "art_manual_title":   manual_title_cursor  = len(manual_title_text)
                    elif active_input_field == "art_manual_artist": manual_artist_cursor = len(manual_artist_text)
                elif event.key == pygame.K_TAB:
                    active_input_field = "art_manual_artist" if active_input_field == "art_manual_title" else "art_manual_title"
                elif event.key == pygame.K_RETURN:
                    if manual_title_text.strip():
                        show_art_manual_modal = False
                        search_input_active = False
                        if not HAS_ANDROID_MEDIA: pygame.key.set_repeat(0, 0)
                        start_art_search(manual_title_text.strip(), manual_artist_text.strip())
                elif event.key == pygame.K_ESCAPE:
                    search_input_active = False
                    if not HAS_ANDROID_MEDIA: pygame.key.set_repeat(0, 0)

            elif show_create_playlist_modal and search_input_active:
                if event.key == pygame.K_BACKSPACE:
                    if active_input_field == "name":
                        playlist_input_text = playlist_input_text[:-1]
                    else:
                        playlist_desc_text = playlist_desc_text[:-1]
                elif event.key == pygame.K_RETURN or event.key == pygame.K_ESCAPE:
                    search_input_active = False
            
            elif current_page == "Search" and search_input_active:
                if event.key == pygame.K_BACKSPACE:
                    search_query = search_query[:-1]
                elif event.key == pygame.K_ESCAPE or event.key == pygame.K_RETURN:
                    search_input_active = False
                        
        elif event.type == pygame.FINGERDOWN:
            button_flash_frames = 3
            mouse_held = True
            _last_touch_norm = (event.x, event.y)
            _pending_touch_down_norm = (event.x, event.y)
            # Handle onboarding taps right here, on the raw touch-down, instead
            # of waiting for SDL's synthesized MOUSEBUTTONDOWN. On some
            # Android/SDL builds that synthesized mouse event lags a full event
            # pump behind the real touch - sometimes only showing up once the
            # *next* tap happens - which is exactly what made onboarding
            # buttons like "Skip for now" and "Allow Notifications" look like
            # they needed two taps: the first tap's FINGERDOWN produced no
            # click, and the second tap was what finally flushed the first
            # tap's delayed synthesized mouse event. Acting on FINGERDOWN
            # directly removes that dependency (and its lag) entirely.
            if onboarding_stage:
                _onboarding_finger_pos = (int(event.x * WIDTH), int(event.y * HEIGHT))
                handle_onboarding_click(_onboarding_finger_pos)
                _last_onboarding_finger_click_time = time.time()
            elif HAS_ANDROID_MEDIA:
                # The SAME lag described above breaks every OTHER button in the
                # app too, not just onboarding - anything gated on MOUSEBUTTONDOWN/
                # MOUSEBUTTONUP was still waiting on SDL's unreliable synthesized
                # echo, which is why it could take two taps to register: the first
                # tap's echo doesn't get flushed into the queue until a second tap
                # happens. Fix it the same way onboarding was fixed: post our OWN
                # mouse-down immediately off the real touch, tagged synthetic=True
                # so it's never mistaken for SDL's own echo. It shows up on the
                # very next frame regardless of whether/when SDL's echo arrives -
                # that echo is discarded outright below once it does.
                pygame.event.post(pygame.event.Event(pygame.MOUSEBUTTONDOWN, pos=(0, 0), button=1, synthetic=True))

        elif event.type == pygame.FINGERMOTION:
            _last_touch_norm = (event.x, event.y)
            if HAS_ANDROID_MEDIA:
                _finger_moved_this_frame = True

        elif event.type == pygame.FINGERUP:
            _last_touch_norm = (event.x, event.y)
            _pending_touch_up_norm = (event.x, event.y)
            if HAS_ANDROID_MEDIA and not onboarding_stage:
                # Same reasoning as FINGERDOWN above, for the release half of the
                # tap - most of the app's actual button actions (see the
                # MOUSEBUTTONUP handler below) fire on release, not press, so this
                # is the half that was most responsible for "needs two taps."
                pygame.event.post(pygame.event.Event(pygame.MOUSEBUTTONUP, pos=(0, 0), button=1, synthetic=True))

        elif event.type == getattr(pygame, 'WINDOWFOCUSLOST', None) or \
             event.type == getattr(pygame, 'WINDOWEVENT', None):
            if search_input_active:
                search_input_active = False

        elif event.type == pygame.MOUSEBUTTONDOWN:
            if HAS_ANDROID_MEDIA and not getattr(event, 'synthetic', False):
                # On Android every mouse event is SDL's own synthesized echo of a
                # touch - there's no real mouse. We now drive every tap directly
                # off FINGERDOWN/FINGERUP instead (see those handlers above),
                # posting our own mouse events tagged synthetic=True the instant
                # the real touch happens. Anything that reaches here WITHOUT that
                # tag is SDL's unreliable, unpredictably-delayed echo of a touch
                # we already handled - discard it outright instead of letting it
                # fire late (possibly on a stale position, or requiring a second
                # tap to even show up at all).
                continue
            if event.button == 1:
                button_flash_frames = 3
                mouse_held = True
            if event.button == 1 and _pending_touch_down_norm is not None:
                # Use the exact touch position captured at THIS gesture's own
                # FINGERDOWN rather than get_virtual_mouse_pos()'s "most recent
                # touch" fallback, which a later tap could have already
                # overwritten if this synthesized event arrived late (see the
                # _pending_touch_down_norm comment above).
                _pdx, _pdy = _pending_touch_down_norm
                mouse_pos = (int(_pdx * WIDTH), int(_pdy * HEIGHT))
                _pending_touch_down_norm = None
            else:
                mouse_pos = get_virtual_mouse_pos(event.pos)

            # If a FINGERDOWN moments ago already handled this exact tap (see
            # the FINGERDOWN handler above), this MOUSEBUTTONDOWN is just
            # SDL's synthesized echo of that same physical touch arriving
            # late - swallow it outright instead of letting it fall through
            # onto whatever's on screen NOW. Without this, tapping "Skip for
            # now" would close onboarding on the FINGERDOWN, and then this
            # delayed echo would land on the newly-revealed Search page at
            # the same screen position - e.g. right on "Add Folder" - and
            # open the folder browser as an unwanted second click. Real
            # desktop mouse clicks never trigger a preceding FINGERDOWN, so
            # they're unaffected.
            if event.button == 1 and time.time() - _last_onboarding_finger_click_time <= 0.4:
                continue

            if onboarding_stage:
                if event.button == 1:
                    handle_onboarding_click(mouse_pos)
                continue
            
            if current_track["title"] != "Select a song" and not show_lyrics_editor_view and not show_create_playlist_modal:
                if progress_bar_rect.collidepoint(mouse_pos) and track_duration > 0 and music_loaded:
                    if event.button == 1:
                        is_dragging_progress = True
                        relative_x = mouse_pos[0] - progress_bar_rect.x
                        fraction = min(1.0, max(0.0, relative_x / progress_bar_rect.width))
                        drag_seek_target = fraction * track_duration
                        continue

            if show_art_search_modal:
                if event.button == 4: target_art_search_scroll = max(0.0, target_art_search_scroll - 120.0)
                elif event.button == 5: target_art_search_scroll = min(max_art_search_scroll, target_art_search_scroll + 120.0)
            elif show_lyrics_search_modal:
                if event.button == 4: target_lyrics_search_scroll = max(0.0, target_lyrics_search_scroll - 120.0)
                elif event.button == 5: target_lyrics_search_scroll = min(max_lyrics_search_scroll, target_lyrics_search_scroll + 120.0)
            elif show_lyrics_editor_view:
                if event.button == 4: target_lyrics_scroll = max(0.0, target_lyrics_scroll - 120.0)
                elif event.button == 5: target_lyrics_scroll = min(max_lyrics_scroll, target_lyrics_scroll + 120.0)
            elif not show_create_playlist_modal:
                if show_add_to_playlist_modal or current_page == "Search" or (current_page == "Your Library" and (viewing_liked_playlist or selected_custom_playlist_name)):
                    if is_browsing_storage or is_browsing_for_cover:
                        if event.button == 4: target_browser_scroll = max(0.0, target_browser_scroll - 120.0)
                        elif event.button == 5: target_browser_scroll = min(max_browser_scroll, target_browser_scroll + 120.0)
                    elif viewing_settings_page:
                        if event.button == 4: target_settings_scroll = max(0.0, target_settings_scroll - 120.0)
                        elif event.button == 5: target_settings_scroll = min(max_settings_scroll, target_settings_scroll + 120.0)
                    else:
                        if event.button == 4: target_music_scroll = max(0.0, target_music_scroll - 150.0)
                        elif event.button == 5: target_music_scroll = min(max_music_scroll, target_music_scroll + 150.0)
            elif show_create_playlist_modal and is_browsing_for_cover:
                if event.button == 4: target_browser_scroll = max(0.0, target_browser_scroll - 120.0)
                elif event.button == 5: target_browser_scroll = min(max_browser_scroll, target_browser_scroll + 120.0)

            if event.button == 3 and current_page == "Search" and not is_browsing_storage and not viewing_settings_page and not (show_create_playlist_modal or show_add_to_playlist_modal or show_lyrics_editor_view):
                for rect, track in track_rects:
                    if rect.collidepoint(mouse_pos):
                        track_to_add_to_playlist = track
                        show_add_to_playlist_modal = True
                        target_music_scroll = 0.0
                        break

            if event.button == 1:
                is_dragging_grid = True
                is_dragging_row = False
                last_touch_y = mouse_pos[1]
                total_drag_dy = 0
                press_origin_pos = mouse_pos
                _scroll_velocity_samples.clear()
                _scroll_momentum.clear()  # a new grab always wins over any flick still decelerating
                if media_bar_rect.collidepoint(mouse_pos) and current_track["title"] != "Select a song":
                    is_dragging_grid = False
                if (current_page == "Search" and is_portrait and layout_mode == "phone"
                        and not is_browsing_storage and not viewing_settings_page
                        and not (show_top100_page or show_song_of_day_page or show_artist_of_day_page or show_history_maker_page)
                        and btn_row_rect.collidepoint(mouse_pos)):
                    is_dragging_row = True
                    is_dragging_grid = False
                    last_touch_x = mouse_pos[0]
                
        elif event.type == pygame.MOUSEMOTION:
            if HAS_ANDROID_MEDIA and not getattr(event, 'synthetic', False):
                # Same reasoning as the MOUSEBUTTONDOWN guard above.
                continue
            mouse_pos = get_virtual_mouse_pos(event.pos)
            
            if is_dragging_progress:
                relative_x = mouse_pos[0] - progress_bar_rect.x
                fraction = min(1.0, max(0.0, relative_x / progress_bar_rect.width))
                drag_seek_target = fraction * track_duration
            elif is_dragging_row:
                dx = last_touch_x - mouse_pos[0]
                # NET distance from the original press point, not a running sum of
                # every intermediate frame's movement - touchscreen digitizer noise
                # fires several tiny motion events even while a finger is basically
                # held still, and summing their absolute deltas made that noise add
                # up past the tap/drag threshold, which is why taps were needing 2-3
                # presses before one happened to have little enough jitter to count
                # as a tap instead of a drag.
                total_drag_dy = abs(mouse_pos[0] - press_origin_pos[0])
                if abs(dx) > 0:
                    user_scrolled_btn_row = True
                target_btn_row_scroll += dx * 2.5
                last_touch_x = mouse_pos[0]
            elif is_dragging_grid:
                dy = last_touch_y - mouse_pos[1]
                # Same net-distance-from-origin reasoning as is_dragging_row above.
                total_drag_dy = abs(mouse_pos[1] - press_origin_pos[1])

                # Record for momentum — keep only the last 120ms
                _now = time.time()
                _scroll_velocity_samples.append((_now, dy))
                _scroll_velocity_samples[:] = [s for s in _scroll_velocity_samples if _now - s[0] < 0.12]
                
                if show_art_search_modal:
                    target_art_search_scroll += dy * 2.5
                    target_art_search_scroll = max(0.0, min(max_art_search_scroll, target_art_search_scroll))
                    art_search_scroll_offset = target_art_search_scroll
                    last_touch_y = mouse_pos[1]
                elif show_lyrics_search_modal:
                    target_lyrics_search_scroll += dy * 2.5
                    target_lyrics_search_scroll = max(0.0, min(max_lyrics_search_scroll, target_lyrics_search_scroll))
                    lyrics_search_scroll_offset = target_lyrics_search_scroll
                    last_touch_y = mouse_pos[1]
                elif show_top100_page:
                    target_top100_scroll += dy * 2.5
                    target_top100_scroll = max(0.0, min(float(max_top100_scroll), target_top100_scroll))
                    top100_scroll_offset = target_top100_scroll
                    last_touch_y = mouse_pos[1]
                elif show_theme_page:
                    target_theme_page_scroll += dy * 2.5
                    target_theme_page_scroll = max(0.0, min(float(max_theme_page_scroll), target_theme_page_scroll))
                    theme_page_scroll_offset = target_theme_page_scroll
                    last_touch_y = mouse_pos[1]
                elif show_song_of_day_page:
                    target_sotd_scroll += dy * 2.5
                    target_sotd_scroll = max(0.0, min(float(max_sotd_scroll), target_sotd_scroll))
                    sotd_scroll_offset = target_sotd_scroll
                    last_touch_y = mouse_pos[1]
                elif show_artist_of_day_page:
                    target_aotd_scroll += dy * 2.5
                    target_aotd_scroll = max(0.0, min(float(max_aotd_scroll), target_aotd_scroll))
                    aotd_scroll_offset = target_aotd_scroll
                    last_touch_y = mouse_pos[1]
                elif show_history_maker_page:
                    target_hm_scroll += dy * 2.5
                    target_hm_scroll = max(0.0, min(float(max_hm_scroll), target_hm_scroll))
                    hm_scroll_offset = target_hm_scroll
                    last_touch_y = mouse_pos[1]
                elif show_create_playlist_modal:
                    if is_browsing_for_cover:
                        target_browser_scroll += dy * 2.5
                        target_browser_scroll = max(0.0, min(max_browser_scroll, target_browser_scroll))
                        browser_scroll_offset = target_browser_scroll
                        last_touch_y = mouse_pos[1]
                elif show_lyrics_editor_view:
                    target_lyrics_scroll += dy * 2.5
                    target_lyrics_scroll = max(0.0, min(max_lyrics_scroll, target_lyrics_scroll))
                    lyrics_scroll_offset = target_lyrics_scroll
                    last_touch_y = mouse_pos[1]
                else:
                    if show_add_to_playlist_modal or current_page == "Search" or (current_page == "Your Library" and (viewing_liked_playlist or selected_custom_playlist_name)):
                        if is_browsing_storage or is_browsing_for_cover:
                            target_browser_scroll += dy * 2.5
                            target_browser_scroll = max(0.0, min(max_browser_scroll, target_browser_scroll))
                            browser_scroll_offset = target_browser_scroll
                            last_touch_y = mouse_pos[1]
                        elif viewing_settings_page:
                            target_settings_scroll += dy * 2.5
                            target_settings_scroll = max(0.0, min(max_settings_scroll, target_settings_scroll))
                            settings_scroll_offset = target_settings_scroll
                            last_touch_y = mouse_pos[1]
                        else:
                            target_music_scroll += dy * 2.5
                            target_music_scroll = max(0.0, min(max_music_scroll, target_music_scroll))
                            music_grid_scroll_offset = target_music_scroll
                            last_touch_y = mouse_pos[1]

        elif event.type == pygame.MOUSEBUTTONUP:
            if HAS_ANDROID_MEDIA and not getattr(event, 'synthetic', False):
                # Same reasoning as the MOUSEBUTTONDOWN guard above. This is the
                # release half of the tap, and it's the half that actually fires
                # most of the app's button actions (see below), so it's the half
                # most responsible for the "needs two taps" symptom.
                continue
            if event.button == 1 and _pending_touch_up_norm is not None:
                # Same reasoning as the MOUSEBUTTONDOWN case above: use this
                # gesture's own captured touch-up position instead of the
                # shared "most recent touch" fallback, which a later tap could
                # have already overwritten by the time this synthesized event
                # is finally processed. This was the direct cause of tapping a
                # media bar button also registering on the song row behind it.
                _pux, _puy = _pending_touch_up_norm
                mouse_pos = (int(_pux * WIDTH), int(_puy * HEIGHT))
                _pending_touch_up_norm = None
            else:
                mouse_pos = get_virtual_mouse_pos(event.pos)
            if event.button == 1:
                # Hand off to real inertial physics: give the released area a
                # genuine velocity (px/sec) and let _update_scroll_physics decay
                # it with friction every frame, instead of pre-computing a single
                # "landing spot" and easing toward it. This is what makes the
                # release feel like a continuous, decelerating flick (Spotify/iOS
                # style) rather than a snap-to-target catch-up.
                if _scroll_velocity_samples and is_dragging_grid:
                    total_dy = sum(s[1] for s in _scroll_velocity_samples)
                    elapsed  = max(0.001, _scroll_velocity_samples[-1][0] - _scroll_velocity_samples[0][0])
                    velocity = total_dy / elapsed   # px/sec
                    velocity = max(-SCROLL_MAX_FLICK_VELOCITY, min(SCROLL_MAX_FLICK_VELOCITY, velocity))

                    if abs(velocity) > SCROLL_MIN_VELOCITY:
                        if show_art_search_modal:
                            _scroll_momentum["art_search"] = velocity
                        elif show_lyrics_search_modal:
                            _scroll_momentum["lyrics_search"] = velocity
                        elif show_top100_page:
                            _scroll_momentum["top100"] = velocity
                        elif show_theme_page:
                            _scroll_momentum["theme_page"] = velocity
                        elif show_song_of_day_page:
                            _scroll_momentum["sotd"] = velocity
                        elif show_artist_of_day_page:
                            _scroll_momentum["aotd"] = velocity
                        elif show_history_maker_page:
                            _scroll_momentum["hm"] = velocity
                        elif show_lyrics_editor_view:
                            _scroll_momentum["lyrics"] = velocity
                        elif is_browsing_storage or is_browsing_for_cover:
                            _scroll_momentum["browser"] = velocity
                        elif viewing_settings_page:
                            _scroll_momentum["settings"] = velocity
                        else:
                            _scroll_momentum["music"] = velocity
                _scroll_velocity_samples.clear()
                if search_input_active:
                    _was_in_manual = (
                        (show_lyrics_editor_view and show_lyrics_manual_modal) or
                        (show_art_search_modal and show_art_manual_modal)
                    )
                    search_input_active = False
                    if not HAS_ANDROID_MEDIA and not _was_in_manual:
                        pygame.key.set_repeat(0, 0)
                if is_dragging_progress:
                    is_dragging_progress = False
                    track_start_accumulator = drag_seek_target
                    current_track["_has_started"] = False
                    if current_backend == "android" and android_media_player:
                        try:
                            android_media_player.seekTo(int(drag_seek_target * 1000))
                            android_media_player.start()
                        except: pass
                    else:
                        try: pygame.mixer.music.play(start=drag_seek_target)
                        except: pass
                    is_playing = True
                    continue 

                is_dragging_grid = False
                is_dragging_row = False

                tap_on_media_bar = media_bar_rect.collidepoint(mouse_pos) and current_track["title"] != "Select a song"

                # A short tap (not a drag/flick that moved past the threshold)
                # is about to be dispatched to whatever button/row/tab is under
                # it below - fire one haptic tick for it here, in one place,
                # so every tappable control in the app gets the same feedback
                # instead of needing a trigger_haptic() call at each of the
                # many individual click sites further down.
                if total_drag_dy < 15:
                    trigger_haptic()

                if total_drag_dy < 15 and not tap_on_media_bar:
                    if show_lyrics_editor_view and show_lyrics_search_modal:
                        if show_lyrics_manual_modal:
                            if lyrics_manual_go_rect.collidepoint(mouse_pos):
                                if manual_title_text.strip():
                                    try:
                                        show_lyrics_manual_modal = False
                                        search_input_active = False
                                        start_lyrics_search(manual_title_text.strip(), manual_artist_text.strip())
                                    except Exception as e:
                                        show_lyrics_search_modal = True
                                        show_lyrics_manual_modal = False
                                        lyrics_search_loading = False
                                        lyrics_search_results = []
                                        lyrics_search_error = f"Failed - {type(e).__name__}: {e}"
                            elif lyrics_manual_title_rect.collidepoint(mouse_pos):
                                search_input_active = True
                                active_input_field = "manual_title"
                                manual_title_cursor = len(manual_title_text)
                                if not HAS_ANDROID_MEDIA: pygame.key.set_repeat(400, 45)
                            elif lyrics_manual_artist_rect.collidepoint(mouse_pos):
                                search_input_active = True
                                active_input_field = "manual_artist"
                                manual_artist_cursor = len(manual_artist_text)
                                if not HAS_ANDROID_MEDIA: pygame.key.set_repeat(400, 45)
                            elif lyrics_search_close_rect.collidepoint(mouse_pos):
                                show_lyrics_search_modal = False
                                show_lyrics_manual_modal = False
                                search_input_active = False
                        else:
                            if lyrics_search_close_rect.collidepoint(mouse_pos):
                                show_lyrics_search_modal = False
                                search_input_active = False
                            elif lyrics_manual_rect.collidepoint(mouse_pos):
                                manual_title_text = current_track.get("title", "") if current_track.get("title") != "Select a song" else ""
                                manual_artist_text = ""
                                manual_title_cursor  = len(manual_title_text)
                                manual_artist_cursor = 0
                                show_lyrics_manual_modal = True
                                search_input_active = True
                                active_input_field = "manual_title"
                                if not HAS_ANDROID_MEDIA: pygame.key.set_repeat(400, 45)
                            else:
                                for item_rect, idx in lyrics_search_item_rects:
                                    if item_rect.collidepoint(mouse_pos):
                                        if idx >= len(lyrics_search_results):
                                            break
                                        candidate = lyrics_search_results[idx]
                                        synced = candidate.get("syncedLyrics")
                                        if synced:
                                            track_ref = current_track.get("path", "")
                                            song_lyrics_database[track_ref] = synced
                                            lyrics_cursor_pos = 0
                                            lyrics_text_changed = True
                                            show_lyrics_search_modal = False
                                        else:
                                            lyrics_search_error = "Failed - no synced lyrics found for that match."
                                        break
                        continue
                    if show_lyrics_editor_view:
                        if lyrics_close_rect.collidepoint(mouse_pos):
                            show_lyrics_editor_view = False
                            search_input_active = False
                        elif lyrics_save_rect.collidepoint(mouse_pos):
                            show_lyrics_editor_view = False
                            search_input_active = False
                            save_app_data()
                        elif lyrics_clear_rect.collidepoint(mouse_pos):
                            track_ref = current_track.get("path", "")
                            song_lyrics_database[track_ref] = ""
                            lyrics_cursor_pos = 0
                            lyrics_text_changed = True
                        elif lyrics_import_rect.collidepoint(mouse_pos):
                            is_browsing_for_cover = True
                            browsing_cover_target = "lyrics_import"
                            show_lyrics_editor_view = False
                            update_browser_contents()
                            search_input_active = False
                        elif lyrics_search_rect.collidepoint(mouse_pos):
                            start_lyrics_search(current_track.get("title", ""), "")
                            search_input_active = False
                        elif lyrics_textarea_rect.collidepoint(mouse_pos):
                            search_input_active = True
                            active_input_field = "lyrics"
                        else:
                            search_input_active = False
                        continue

                    if show_create_playlist_modal:
                        if is_browsing_for_cover:
                            if cancel_browser_btn_rect.collidepoint(mouse_pos):
                                is_browsing_for_cover = False
                            else:
                                for rect, item in browser_rects:
                                    if rect.collidepoint(mouse_pos):
                                        if item["is_dir"]:
                                            current_browser_path = item["path"]
                                            update_browser_contents()
                                        else:
                                            try:
                                                raw_img = pygame.image.load(item["path"])
                                                modal_playlist_cover_surface = pygame.transform.smoothscale(raw_img, (220, 220))
                                                modal_playlist_cover_path = item["path"]
                                            except Exception as image_err:
                                                print(f"Error importing cover layout graphics: {image_err}")
                                            is_browsing_for_cover = False
                                        break
                            continue

                        if modal_close_rect.collidepoint(mouse_pos):
                            show_create_playlist_modal = False
                            playlist_input_text = ""
                            playlist_desc_text = ""
                            modal_playlist_cover_surface = None
                            modal_playlist_cover_path = None
                            search_input_active = False
                        elif modal_save_rect.collidepoint(mouse_pos):
                            clean_name = playlist_input_text.strip() if playlist_input_text.strip() else "My Playlist"
                            if clean_name not in custom_playlists:
                                final_thumb = None
                                if modal_playlist_cover_surface:
                                    final_thumb = pygame.transform.smoothscale(modal_playlist_cover_surface, (130, 110))
                                custom_playlists[clean_name] = {
                                    "tracks": [], 
                                    "image_path": modal_playlist_cover_path, 
                                    "surface": final_thumb,
                                    "description": playlist_desc_text.strip()
                                }
                            playlist_input_text = ""
                            playlist_desc_text = ""
                            modal_playlist_cover_surface = None
                            modal_playlist_cover_path = None
                            show_create_playlist_modal = False
                            search_input_active = False
                            save_app_data()
                        elif modal_input_rect.collidepoint(mouse_pos):
                            search_input_active = True
                            active_input_field = "name"
                        elif modal_desc_rect.collidepoint(mouse_pos):
                            search_input_active = True
                            active_input_field = "description"
                        elif modal_image_picker_rect.collidepoint(mouse_pos):
                            is_browsing_for_cover = True
                            browsing_cover_target = "create"
                            update_browser_contents()
                        else:
                            search_input_active = False
                        continue
                        
                    elif show_add_to_playlist_modal:
                        if modal_close_rect.collidepoint(mouse_pos):
                            show_add_to_playlist_modal = False
                            track_to_add_to_playlist = None
                            target_music_scroll = 0.0
                        else:
                            for rect, p_name in modal_playlist_rects:
                                if rect.collidepoint(mouse_pos):
                                    if track_to_add_to_playlist and track_to_add_to_playlist not in custom_playlists[p_name]["tracks"]:
                                        custom_playlists[p_name]["tracks"].append(track_to_add_to_playlist)
                                    show_add_to_playlist_modal = False
                                    track_to_add_to_playlist = None
                                    target_music_scroll = 0.0 
                                    save_app_data()
                                    break
                        continue

                    clicked_panel_item = False
                    if current_page == "Search" and viewing_settings_page and saved_directories:
                        for rect, d_path in settings_dir_rects:
                            if rect.collidepoint(mouse_pos):
                                saved_directories.remove(d_path)
                                rebuild_imported_tracks()
                                clicked_panel_item = True
                                save_app_data()
                                break
                        if clicked_panel_item:
                            continue

                    if current_page == "Search" and not is_browsing_storage and not viewing_settings_page and search_box_rect.collidepoint(mouse_pos):
                        search_input_active = True
                    else:
                        if not show_create_playlist_modal:
                            search_input_active = False

                    for rect, target_page in sidebar_rects:
                        if rect.collidepoint(mouse_pos):
                            current_page = target_page
                            is_browsing_storage = False 
                            is_browsing_for_cover = False
                            viewing_liked_playlist = False
                            selected_custom_playlist_name = None
                            viewing_settings_page = False
                            show_theme_page = False
                            show_language_page = False
                            target_music_scroll = 0.0
                            target_browser_scroll = 0.0
                            target_settings_scroll = 0.0
                            target_lyrics_scroll = 0.0
                            clicked_panel_item = True
                            break
                    if clicked_panel_item:
                        continue

                    if show_theme_page and current_page == "Settings":
                        if subpage_back_rect.collidepoint(mouse_pos):
                            show_theme_page = False
                        else:
                            _picked = False
                            for _rect, _theme_key in theme_option_rects:
                                if _rect.collidepoint(mouse_pos):
                                    apply_theme(_theme_key)
                                    save_app_data()
                                    _picked = True
                                    break
                            if not _picked:
                                for _rect, _font_key in font_option_rects:
                                    if _rect.collidepoint(mouse_pos):
                                        apply_font(_font_key)
                                        save_app_data()
                                        break

                    elif show_language_page and current_page == "Settings":
                        if subpage_back_rect.collidepoint(mouse_pos):
                            show_language_page = False
                        else:
                            for _rect, _lang in language_option_rects:
                                if _rect.collidepoint(mouse_pos):
                                    apply_language(_lang)
                                    if not is_browsing_storage and not is_browsing_for_cover:
                                        search_message = t("Tap '+ Add Folder' to open the built-in storage browser.")
                                    save_app_data()
                                    break

                    elif current_page == "Settings":
                        if (not IS_ANDROID) and resolution_btn_rect.collidepoint(mouse_pos):
                            REAL_WIDTH, REAL_HEIGHT = 1920, 1080
                            screen = pygame.display.set_mode((REAL_WIDTH, REAL_HEIGHT), pygame.RESIZABLE)
                            is_portrait = REAL_HEIGHT > REAL_WIDTH
                            WIDTH, HEIGHT = compute_virtual_size(REAL_WIDTH, REAL_HEIGHT, is_portrait, layout_mode)
                            virtual_surface = pygame.Surface((WIDTH, HEIGHT)).convert()
                        elif font_size_btn_rect.collidepoint(mouse_pos):
                            cycle_font_size()
                            save_app_data()
                        elif IS_ANDROID and haptics_btn_rect.collidepoint(mouse_pos):
                            haptics_enabled = not haptics_enabled
                            if haptics_enabled:
                                trigger_haptic()  # immediate confirmation tick that it's on
                            save_app_data()
                        elif _debug_reveal and desktop_btn_rect.collidepoint(mouse_pos):
                            layout_mode = "desktop"
                            grid_cols_override = None
                            set_android_orientation(False)
                            WIDTH, HEIGHT = compute_virtual_size(REAL_WIDTH, REAL_HEIGHT, is_portrait, "desktop")
                            virtual_surface = pygame.Surface((WIDTH, HEIGHT)).convert()
                            save_app_data()
                        elif _debug_reveal and phone_btn_rect.collidepoint(mouse_pos):
                            layout_mode = "phone"
                            grid_cols_override = None
                            set_android_orientation(True)
                            is_portrait = True
                            WIDTH, HEIGHT = compute_virtual_size(REAL_WIDTH, REAL_HEIGHT, is_portrait, "phone")
                            virtual_surface = pygame.Surface((WIDTH, HEIGHT)).convert()
                            save_app_data()
                        elif grid_toggle_btn_rect.collidepoint(mouse_pos):
                            if layout_mode == "phone":
                                current_val = grid_cols_override if grid_cols_override else 2
                                current_val += 1
                                if current_val > 4:
                                    current_val = 2
                                grid_cols_override = current_val
                            else:
                                current_val = grid_cols_override if grid_cols_override else 5
                                current_val += 1
                                if current_val > 7:
                                    current_val = 5
                                grid_cols_override = current_val
                            save_app_data()
                        elif theme_btn_rect.collidepoint(mouse_pos):
                            show_theme_page = True
                        elif language_btn_rect.collidepoint(mouse_pos):
                            show_language_page = True

                    if show_art_search_modal:
                        if show_art_manual_modal:
                            if art_manual_go_rect.collidepoint(mouse_pos):
                                if manual_title_text.strip():
                                    show_art_manual_modal = False
                                    search_input_active = False
                                    start_art_search(manual_title_text.strip(), manual_artist_text.strip())
                            elif art_manual_title_rect.collidepoint(mouse_pos):
                                search_input_active = True
                                active_input_field = "art_manual_title"
                                manual_title_cursor = len(manual_title_text)
                                if not HAS_ANDROID_MEDIA: pygame.key.set_repeat(400, 45)
                            elif art_manual_artist_rect.collidepoint(mouse_pos):
                                search_input_active = True
                                active_input_field = "art_manual_artist"
                                manual_artist_cursor = len(manual_artist_text)
                                if not HAS_ANDROID_MEDIA: pygame.key.set_repeat(400, 45)
                            elif art_search_close_rect.collidepoint(mouse_pos):
                                show_art_search_modal = False
                                show_art_manual_modal = False
                                search_input_active = False
                            continue
                        if art_search_close_rect.collidepoint(mouse_pos):
                            show_art_search_modal = False
                        elif art_manual_rect.collidepoint(mouse_pos):
                            manual_title_text = current_track.get("title", "") if current_track.get("title") != "Select a song" else ""
                            manual_artist_text = ""
                            manual_title_cursor  = len(manual_title_text)
                            manual_artist_cursor = 0
                            show_art_manual_modal = True
                            search_input_active = True
                            active_input_field = "art_manual_title"
                            if not HAS_ANDROID_MEDIA: pygame.key.set_repeat(400, 45)
                        else:
                            for row_rect, idx in art_search_item_rects:
                                if row_rect.collidepoint(mouse_pos):
                                    result = art_search_results[idx]
                                    art_url = result.get("artworkUrl100", "")
                                    if art_url and not art_apply_pending:
                                        # Download in the background instead of blocking the UI thread here.
                                        # art_apply_pending is polled each frame (see main loop) and the
                                        # cover gets applied once the download finishes.
                                        start_apply_itunes_art(art_url, current_track["path"])
                                    break
                        continue

                    if is_browsing_for_cover and (current_page == "Your Library" or browsing_cover_target in ("track_cover", "lyrics_import")):
                        if browser_extra_search_btn_rect.collidepoint(mouse_pos) and is_browsing_for_cover and browsing_cover_target not in ("lyrics_import",):
                            start_art_search(current_track.get("title", ""), current_track.get("artist", ""))
                            continue
                        if cancel_browser_btn_rect.collidepoint(mouse_pos):
                            is_browsing_for_cover = False
                            if browsing_cover_target == "lyrics_import":
                                show_lyrics_editor_view = True
                        else:
                            for rect, item in browser_rects:
                                if rect.collidepoint(mouse_pos):
                                    if item["is_dir"]:
                                        current_browser_path = item["path"]
                                        update_browser_contents()
                                    elif browsing_cover_target == "lyrics_import":
                                        try:
                                            with open(item["path"], "r", encoding="utf-8", errors="replace") as lyrics_file:
                                                imported_lyrics_text = lyrics_file.read()
                                            track_ref = current_track.get("path", "")
                                            song_lyrics_database[track_ref] = imported_lyrics_text
                                            lyrics_cursor_pos = len(imported_lyrics_text)
                                            lyrics_text_changed = True
                                            save_app_data()
                                        except Exception as lyrics_err:
                                            print(f"Error importing lyrics file: {lyrics_err}")
                                        is_browsing_for_cover = False
                                        show_lyrics_editor_view = True
                                    else:
                                        try:
                                            raw_img = pygame.image.load(item["path"])
                                            scaled_surf = pygame.transform.smoothscale(raw_img, (130, 110))
                                            if browsing_cover_target == "custom_view":
                                                custom_playlists[selected_custom_playlist_name]["image_path"] = item["path"]
                                                custom_playlists[selected_custom_playlist_name]["surface"] = scaled_surf
                                            elif browsing_cover_target == "liked_view":
                                                liked_songs_custom_cover["image_path"] = item["path"]
                                                liked_songs_custom_cover["surface"] = scaled_surf
                                            elif browsing_cover_target == "track_cover":
                                                grid_cover_surf = pygame.transform.smoothscale(raw_img, (130, 130))
                                                track_covers[current_track["path"]] = {"image_path": item["path"], "surface": grid_cover_surf}
                                                current_track["cover_surface"] = grid_cover_surf
                                                for trk in imported_tracks:
                                                    if trk["path"] == current_track["path"]:
                                                        trk["cover_surface"] = grid_cover_surf
                                                for trk in liked_tracks:
                                                    if trk["path"] == current_track["path"]:
                                                        trk["cover_surface"] = grid_cover_surf
                                                for p_data in custom_playlists.values():
                                                    for trk in p_data["tracks"]:
                                                        if trk["path"] == current_track["path"]:
                                                            trk["cover_surface"] = grid_cover_surf
                                            save_app_data()
                                        except Exception as image_err:
                                            print(f"Error importing cover layout graphics: {image_err}")
                                        is_browsing_for_cover = False
                                    break
                        continue

                    if (viewing_liked_playlist or selected_custom_playlist_name) and current_page == "Your Library":
                        p_title_text = selected_custom_playlist_name if selected_custom_playlist_name else "Liked Songs"
                        if playlist_cover_rect.collidepoint(mouse_pos):
                            is_browsing_for_cover = True
                            browsing_cover_target = "custom_view" if selected_custom_playlist_name else "liked_view"
                            update_browser_contents()
                            continue
                            
                        if playlist_play_btn_rect.collidepoint(mouse_pos):
                            active_tracks = custom_playlists[selected_custom_playlist_name]["tracks"] if selected_custom_playlist_name else liked_tracks
                            if active_tracks:
                                is_current_track_in_playlist = any(track["path"] == current_track["path"] for track in active_tracks)
                                if is_current_track_in_playlist and playlist_is_playing == p_title_text:
                                    is_playing = not is_playing
                                    if is_playing:
                                        if current_backend == "android": android_media_player.start()
                                        else: pygame.mixer.music.unpause()
                                        _start_listen_session(current_track.get("path", ""))
                                    else:
                                        if current_backend == "android": android_media_player.pause()
                                        else: pygame.mixer.music.pause()
                                        _flush_listen_session(current_track.get("path", ""))
                                else:
                                    current_track = active_tracks[0]  
                                    playlist_is_playing = p_title_text  
                                    is_playing = True
                                    green_toggled_tracks.add(current_track["path"])
                                    load_and_play_track(current_track["path"])

                        if playlist_random_btn_rect.collidepoint(mouse_pos):
                            active_tracks = custom_playlists[selected_custom_playlist_name]["tracks"] if selected_custom_playlist_name else liked_tracks
                            if active_tracks:
                                is_shuffle = not is_shuffle
                                playlist_is_playing = p_title_text
                                if is_shuffle:
                                    random_index = random.randint(0, len(active_tracks) - 1)
                                    current_track = active_tracks[random_index]
                                    is_playing = True
                                    green_toggled_tracks.add(current_track["path"])
                                    load_and_play_track(current_track["path"])

                    if current_page == "Your Library" and not viewing_liked_playlist and not selected_custom_playlist_name:
                        if create_playlist_btn_rect.collidepoint(mouse_pos):
                            show_create_playlist_modal = True
                        elif liked_songs_card_rect.collidepoint(mouse_pos):
                            viewing_liked_playlist = True
                            target_music_scroll = 0.0
                        else:
                            for rect, name in custom_playlist_rects:
                                if rect.collidepoint(mouse_pos):
                                    selected_custom_playlist_name = name
                                    target_music_scroll = 0.0
                                    marquee_offset = 0.0
                                    marquee_direction = 1
                                    break

                    if is_browsing_storage and current_page == "Search":
                        if select_folder_btn_rect.collidepoint(mouse_pos):
                            scan_confirmed_directory(current_browser_path)
                            if onboarding_awaiting_folder:
                                onboarding_awaiting_folder = False
                                onboarding_stage = "scrape"
                                onboarding_anim_start = time.time()
                                _refresh_onboarding_rects()
                        elif cancel_browser_btn_rect.collidepoint(mouse_pos):
                            is_browsing_storage = False
                            if onboarding_awaiting_folder:
                                onboarding_awaiting_folder = False
                                onboarding_stage = "scrape"
                                onboarding_anim_start = time.time()
                                _refresh_onboarding_rects()
                        else:
                            for rect, item in browser_rects:
                                if rect.collidepoint(mouse_pos) and item["is_dir"]:
                                    current_browser_path = item["path"]
                                    update_browser_contents()
                                    break
                                    
                    elif viewing_settings_page and current_page == "Search":
                        if close_settings_btn_rect.collidepoint(mouse_pos):
                            viewing_settings_page = False
                    elif (show_top100_page or show_song_of_day_page or show_artist_of_day_page or show_history_maker_page) and current_page == "Search":
                        if subpage_back_rect.collidepoint(mouse_pos):
                            show_top100_page = False
                            show_song_of_day_page = False
                            show_artist_of_day_page = False
                            show_history_maker_page = False
                        elif show_top100_page:
                            # Refresh button
                            _main_x = 0 if is_portrait else 230
                            _main_w = WIDTH - _main_x
                            refresh_rect_hit = pygame.Rect(
                                _main_x + _main_w - (240 if is_portrait else 360), 35, 90, 35)
                            if refresh_rect_hit.collidepoint(mouse_pos) and not top100_loading:
                                start_top100_fetch()
                            else:
                                # Link button taps
                                for lr, url in top100_link_rects:
                                    if lr.collidepoint(mouse_pos):
                                        try:
                                            open_url(url)
                                        except Exception:
                                            pass
                                        break
                        elif show_song_of_day_page:
                            for lr, url in sotd_link_rects:
                                if lr.collidepoint(mouse_pos):
                                    try:
                                        open_url(url)
                                    except Exception:
                                        pass
                                    break
                        elif show_artist_of_day_page:
                            for lr, url in aotd_link_rects:
                                if lr.collidepoint(mouse_pos):
                                    try:
                                        open_url(url)
                                    except Exception:
                                        pass
                                    break
                        elif show_history_maker_page:
                            for lr, url in hm_link_rects:
                                if lr.collidepoint(mouse_pos):
                                    try:
                                        open_url(url)
                                    except Exception:
                                        pass
                                    break
                    else:
                        if current_page == "Search" and add_folder_btn_rect.collidepoint(mouse_pos):
                            is_browsing_storage = True
                            viewing_settings_page = False
                            update_browser_contents()
                        
                        if current_page == "Search" and saved_directories and settings_btn_rect.collidepoint(mouse_pos):
                            viewing_settings_page = True
                            target_settings_scroll = 0.0

                        if current_page == "Search" and top100_btn_rect.collidepoint(mouse_pos):
                            show_top100_page = True
                            # Fetch if never loaded or data is older than 1 hour
                            if not top100_tracks and not top100_loading:
                                start_top100_fetch()
                            elif top100_last_fetched > 0 and (time.time() - top100_last_fetched) > 3600 and not top100_loading:
                                start_top100_fetch()
                        if current_page == "Search" and song_of_day_btn_rect.collidepoint(mouse_pos):
                            show_song_of_day_page = True
                            sotd_scroll_offset  = 0.0
                            target_sotd_scroll  = 0.0
                            _idx, _ = _pick_daily_entry(SOTD_ENTRIES)
                            if _idx != sotd_shown_day_idx:
                                sotd_cover_surface = None
                                sotd_shown_day_idx = _idx
                            if sotd_cover_surface is None and not sotd_cover_loading:
                                sotd_cover_loading = True
                                threading.Thread(target=_fetch_sotd_cover, daemon=True).start()
                        if current_page == "Search" and artist_of_day_btn_rect.collidepoint(mouse_pos):
                            show_artist_of_day_page = True
                            aotd_scroll_offset  = 0.0
                            target_aotd_scroll  = 0.0
                            _idx, _ = _pick_daily_entry(AOTD_ENTRIES)
                            if _idx != aotd_shown_day_idx:
                                aotd_cover_surface = None
                                aotd_shown_day_idx = _idx
                            if aotd_cover_surface is None and not aotd_cover_loading:
                                aotd_cover_loading = True
                                threading.Thread(target=_fetch_aotd_cover, daemon=True).start()
                        if current_page == "Search" and history_maker_btn_rect.collidepoint(mouse_pos):
                            show_history_maker_page = True
                            hm_scroll_offset  = 0.0
                            target_hm_scroll  = 0.0
                            _idx, _ = _pick_daily_entry(HM_ENTRIES)
                            if _idx != hm_shown_day_idx:
                                hm_cover_surface = None
                                hm_shown_day_idx = _idx
                            if hm_cover_surface is None and not hm_cover_loading:
                                hm_cover_loading = True
                                threading.Thread(target=_fetch_hm_cover, daemon=True).start()
                                
                        if current_page in ["Search"] or (current_page == "Your Library" and (viewing_liked_playlist or selected_custom_playlist_name)):
                            for rect, track in track_rects:
                                portrait_sidebar_h = (80 if (is_portrait and layout_mode == "phone") else (65 if is_portrait else 0))
                                main_x = 0 if is_portrait else 230
                                main_w = WIDTH - main_x
                                
                                event_margin = (100 if (is_portrait and layout_mode == "phone") else (144 if is_portrait else 90)) if current_track["title"] != "Select a song" else 0
                                main_h_event = HEIGHT - event_margin - portrait_sidebar_h
                                
                                if current_page == "Your Library" and (viewing_liked_playlist or selected_custom_playlist_name):
                                    clip_rect_bounds = pygame.Rect(main_x, 315, main_w, main_h_event - 315)
                                else:
                                    search_clip_top = 210 if (is_portrait and layout_mode == "phone") else 140
                                    clip_rect_bounds = pygame.Rect(main_x, search_clip_top, main_w, main_h_event - search_clip_top)
                                    
                                if clip_rect_bounds.collidepoint(mouse_pos) and rect.collidepoint(mouse_pos):
                                    current_track = track
                                    playlist_is_playing = (selected_custom_playlist_name if selected_custom_playlist_name else "Liked Songs") if (viewing_liked_playlist or selected_custom_playlist_name) else None
                                    is_playing = True 
                                    green_toggled_tracks.add(current_track["path"])
                                    load_and_play_track(current_track["path"])
                                    
                if current_track["title"] != "Select a song" and not show_lyrics_editor_view and not show_create_playlist_modal:
                    if total_drag_dy < 15:
                        if mediabar_lyrics_btn_rect.collidepoint(mouse_pos):
                            show_lyrics_editor_view = True
                            track_ref = current_track.get("path", "")
                            if track_ref not in song_lyrics_database:
                                song_lyrics_database[track_ref] = ""
                            search_input_active = True
                            active_input_field = "lyrics"
                            target_lyrics_scroll = 0.0
                            lyrics_cursor_pos = len(song_lyrics_database[track_ref])

                        if mediabar_add_btn_rect.collidepoint(mouse_pos):
                            track_to_add_to_playlist = current_track
                            show_add_to_playlist_modal = True
                            target_music_scroll = 0.0

                        if mediabar_cover_btn_rect.collidepoint(mouse_pos):
                            is_browsing_for_cover = True
                            browsing_cover_target = "track_cover"
                            update_browser_contents()
                            continue

                        if minus_10_btn_rect.collidepoint(mouse_pos) and track_duration > 0 and music_loaded:
                            current_track["_has_started"] = False
                            if current_backend == "android" and android_media_player:
                                try: current_pos = android_media_player.getCurrentPosition() / 1000.0
                                except: current_pos = 0.0
                            else:
                                mix_pos = pygame.mixer.music.get_pos()
                                current_pos = track_start_accumulator + (mix_pos / 1000.0) if mix_pos != -1 else track_start_accumulator
                        
                            seek_target = max(0.0, current_pos - 10.0)
                            track_start_accumulator = seek_target
                            if current_backend == "android" and android_media_player:
                                try:
                                    android_media_player.seekTo(int(seek_target * 1000))
                                    android_media_player.start()
                                except: pass
                            else:
                                try: pygame.mixer.music.play(start=seek_target)
                                except: pass
                            is_playing = True

                        if prev_btn_rect.collidepoint(mouse_pos):
                            advance_track(backward=True)

                        if play_btn_rect.collidepoint(mouse_pos):
                            if music_loaded: 
                                is_playing = not is_playing
                                if is_playing:
                                    if current_backend == "android": android_media_player.start()
                                    else: pygame.mixer.music.unpause()
                                    _start_listen_session(current_track.get("path", ""))
                                else:
                                    if current_backend == "android": android_media_player.pause()
                                    else: pygame.mixer.music.pause()
                                    _flush_listen_session(current_track.get("path", ""))

                        if next_btn_rect.collidepoint(mouse_pos):
                            advance_track(backward=False)

                        if plus_10_btn_rect.collidepoint(mouse_pos) and track_duration > 0 and music_loaded:
                            current_track["_has_started"] = False
                            if current_backend == "android" and android_media_player:
                                try: current_pos = android_media_player.getCurrentPosition() / 1000.0
                                except: current_pos = 0.0
                            else:
                                mix_pos = pygame.mixer.music.get_pos()
                                current_pos = track_start_accumulator + (mix_pos / 1000.0) if mix_pos != -1 else track_start_accumulator
                        
                            seek_target = min(track_duration, current_pos + 10.0)
                            track_start_accumulator = seek_target
                            if current_backend == "android" and android_media_player:
                                try:
                                    android_media_player.seekTo(int(seek_target * 1000))
                                    android_media_player.start()
                                except: pass
                            else:
                                try: pygame.mixer.music.play(start=seek_target)
                                except: pass
                            is_playing = True
                        
                        if shuffle_btn_rect.collidepoint(mouse_pos):
                            is_shuffle = not is_shuffle

                        if star_btn_rect.collidepoint(mouse_pos):
                            if current_track in liked_tracks:
                                liked_tracks.remove(current_track)
                            else:
                                liked_tracks.append(current_track)
                        save_app_data()

        elif event.type == pygame.MOUSEWHEEL:
            if show_theme_page:
                target_theme_page_scroll -= event.y * 60
                target_theme_page_scroll = max(0.0, min(float(max_theme_page_scroll), target_theme_page_scroll))

    if _finger_moved_this_frame:
        pygame.event.post(pygame.event.Event(pygame.MOUSEMOTION, pos=(0, 0), rel=(0, 0), buttons=(1, 0, 0), synthetic=True))

    # Keep a partial wake lock held for exactly as long as something is
    # actually playing, so the device can't fully sleep mid-song (which
    # would silently stop playback and prevent auto-advance once the
    # screen locks / app is backgrounded). Edge-triggered on is_playing
    # changing, rather than hooked into every individual play/pause button,
    # so it can't be missed by any one of them.
    if is_playing != _wake_lock_prev_is_playing:
        if is_playing:
            acquire_playback_wake_lock()
        else:
            release_playback_wake_lock()
        _wake_lock_prev_is_playing = is_playing

    # Keep the "now playing" notification in sync with whatever's actually
    # loaded/playing, edge-triggered on (track, is_playing) changing so it's
    # only rebuilt when something actually changed, not every frame.
    _notif_key = (current_track.get("path"), is_playing)
    if _notif_key != _notif_last_state and current_track.get("path"):
        update_playback_notification()
        _notif_last_state = _notif_key

    if is_playing and track_duration > 0 and music_loaded and not is_dragging_progress:
        if current_backend == "android" and android_media_player:
            try: elapsed = android_media_player.getCurrentPosition() / 1000.0
            except: elapsed = 0.0
            if elapsed >= track_duration:
                _flush_listen_session(current_track.get("path", ""), completed=True)
                advance_track(backward=False)
        else:
            mix_pos = pygame.mixer.music.get_pos()
            if mix_pos > 500:
                current_track["_has_started"] = True
                
            elapsed = track_start_accumulator + (mix_pos / 1000.0)
            time_elapsed = time.time() - current_track.get("_play_start_time", time.time())
            
            if (current_track.get("_has_started", False) and (mix_pos == -1 or mix_pos == 0 or elapsed >= track_duration - 0.5)) or (mix_pos == -1 and time_elapsed > 2.0):
                current_track["_has_started"] = False
                _flush_listen_session(current_track.get("path", ""), completed=True)
                advance_track(backward=False)

    virtual_surface.fill(COLOR_BLACK)
    
    import traceback as _tb
    if onboarding_stage:
        try:
            draw_onboarding_overlay()
        except Exception as _e:
            print("Render error in draw_onboarding_overlay (recovered):")
            _tb.print_exc()
    else:
        # Each draw call gets its own try/except instead of one shared block: if a
        # single section (e.g. modals, right after a cover finishes applying) hits
        # an error, the others still render instead of the whole frame coming out
        # blank/gray. Previously all four were in one try, so an early failure in
        # draw_main_content meant NOTHING else drew that frame - and since the
        # underlying state causing the error didn't change, it repeated every
        # single frame, which is exactly what a "stuck gray screen" looks like.
        try:
            draw_main_content()
        except Exception as _e:
            print("Render error in draw_main_content (recovered):")
            _tb.print_exc()
        try:
            draw_sidebar()
        except Exception as _e:
            print("Render error in draw_sidebar (recovered):")
            _tb.print_exc()
        try:
            draw_media_bar()
        except Exception as _e:
            print("Render error in draw_media_bar (recovered):")
            _tb.print_exc()
        try:
            draw_modals()
        except Exception as _e:
            print("Render error in draw_modals (recovered):")
            _tb.print_exc()

    # --- FPS DEBUG OVERLAY ---
    # Shown only while _debug_reveal is True (press F5 to toggle). Real
    # measured framerate via clock.get_fps() (a rolling average of recent
    # frame times, not a guess).
    if _debug_reveal:
        _fps_txt = f"{clock.get_fps():.0f} fps" + ("" if USING_GPU_SCALE else " (CPU scale)")
        _fps_surf = _cached_render(font_small, _fps_txt, True, (0, 255, 0))
        virtual_surface.blit(_fps_surf, (8, 8))

    # Accurate Letterbox/Pillarbox Screen Scaling
    # When USING_GPU_SCALE is True, virtual_surface IS screen (same object) and
    # SDL already scales it onto the real display during presentation, so
    # there's nothing left to do here but flip. Only do the CPU upscale when
    # the GPU path wasn't available.
    # NOTE: this used to be pygame.transform.smoothscale (bilinear-filtered).
    # smoothscale does a real per-pixel filtered resample, and this call runs
    # on the ENTIRE screen at full display resolution, unconditionally,
    # every single frame, regardless of what's actually on screen - making it
    # by far the single most expensive fixed per-frame cost in the app, and
    # exactly the kind of flat, workload-independent cost that produces a
    # solid low FPS no matter how much CPU/GPU headroom a device has. The
    # last known-good version (V1_0_1) used plain pygame.transform.scale
    # (nearest-neighbor, no filtering) for this exact same call and ran fine,
    # so this switches back to that - same visual letterbox/pillarbox
    # behavior, far cheaper per frame.
    if not USING_GPU_SCALE:
        scaled_frame = pygame.transform.scale(virtual_surface, (REAL_WIDTH, REAL_HEIGHT))
        screen.blit(scaled_frame, (0, 0))

    pygame.display.flip()

    # --- Idle-aware frame pacing ---
    # Every frame is still drawn fully and correctly (nothing is skipped) — this only
    # changes how OFTEN we redraw. We keep the full device refresh rate any time
    # something on screen needs to keep moving on its own (music playing/progress bar/
    # synced lyrics, an in-flight scroll animation still settling, the playlist
    # description marquee, or the lyrics editor's blinking text cursor), and any time
    # there was actual touch/mouse/keyboard input this frame. Otherwise (genuinely
    # idle screen, nothing playing, nothing animating) we drop to a low tick rate to
    # save CPU/battery, since there's nothing new to show until something changes.
    _scroll_settling = (
        abs(target_music_scroll          - music_grid_scroll_offset)    > 0.5 or
        abs(target_browser_scroll        - browser_scroll_offset)       > 0.5 or
        abs(target_settings_scroll       - settings_scroll_offset)      > 0.5 or
        abs(target_lyrics_scroll         - lyrics_scroll_offset)        > 0.5 or
        abs(target_top100_scroll         - top100_scroll_offset)        > 0.5 or
        abs(target_theme_page_scroll     - theme_page_scroll_offset)    > 0.5 or
        abs(target_sotd_scroll           - sotd_scroll_offset)          > 0.5 or
        abs(target_aotd_scroll           - aotd_scroll_offset)          > 0.5 or
        abs(target_hm_scroll             - hm_scroll_offset)            > 0.5 or
        abs(target_art_search_scroll     - art_search_scroll_offset)    > 0.5 or
        abs(target_lyrics_search_scroll  - lyrics_search_scroll_offset) > 0.5 or
        abs(target_btn_row_scroll        - btn_row_scroll_offset)       > 0.5 or
        any(v != 0.0 for v in _scroll_momentum.values())
    )
    _needs_continuous_frames = (
        is_playing or
        frame_had_input or
        _scroll_settling or
        show_lyrics_editor_view or
        show_lyrics_search_modal or
        show_art_search_modal or
        search_input_active or
        selected_custom_playlist_name is not None or
        viewing_liked_playlist or
        top100_loading or
        art_search_loading or
        lyrics_search_loading or
        sotd_cover_loading or
        aotd_cover_loading or
        hm_cover_loading or
        (show_top100_page and len(top100_art_cache) < len(top100_tracks))
    )
    # tick_busy_loop spins instead of sleeping for the last ~1ms, which costs
    # a little extra CPU but hits the target interval far more precisely than
    # tick()'s OS-sleep-based delay (whose granularity can itself shave a few
    # fps off the top on some Android kernels). Only worth that trade while
    # something's actually animating; the idle low-power tick stays a plain
    # sleep-based tick() since there's nothing to keep smooth there.
    if _needs_continuous_frames:
        clock.tick_busy_loop(DEVICE_REFRESH_RATE)
    else:
        clock.tick(10)

    if not _needs_continuous_frames and time.time() - _last_gc_time > 5.0:
        gc.collect()
        _last_gc_time = time.time()

_flush_listen_session(current_track.get("path", ""))
save_app_data()

if TEMP_WAV_PATH and os.path.exists(TEMP_WAV_PATH):
    try: os.remove(TEMP_WAV_PATH)
    except: pass

if HAS_ANDROID_MEDIA and android_media_player:
    try: android_media_player.release()
    except: pass

pygame.quit()
sys.exit()
