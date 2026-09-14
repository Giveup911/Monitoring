"""
PC Monitor - crash diagnosis tool (Windows)

Logs everything it can reach every few seconds - CPU/GPU temp, clock,
power, fan RPM, voltages, memory, swap, disk, battery, top CPU/memory
processes, network throughput/packet loss, real FPS/frame-time data
per game (via PresentMon), and the active foreground app - to rotating
log files organized into clean nested groups. Also tails the Windows
System event log for Error-level entries (Kernel-Power, BugCheck,
WHEA-Logger, display driver timeouts, etc.), usually the strongest
signal for *why* a crash happened. Dark-mode dashboard GUI for live
readings and history browsing across as many log files as a chosen
time range spans.

SETUP
  pip install psutil wmi pywin32 pystray Pillow
  (pystray + Pillow are for the tray icon - optional but recommended;
  see RUN below for why.)
  Download & run LibreHardwareMonitor, leave it open:
  https://github.com/LibreHardwareMonitor/LibreHardwareMonitor
  Launching it via this app's "Auto-Locate / Download Tools" button
  (or the installer) enables Remote Web Server, Minimize to Tray, and
  minimize-on-close for you automatically - but only from the SECOND
  launch onward, since it works by patching LibreHardwareMonitor's own
  saved settings file, which doesn't exist yet before it's ever been
  run once. The very first launch needs its window visible for a
  one-time manual step: in Options, check Remote Web Server > Run
  (what this app reads sensors from - the main thing to check if data
  isn't showing up, not Administrator), Minimize to Tray, and Run On
  Windows Startup. After that once, it's hands-off.

  For FPS / frame time / stutters / 1% lows, download PresentMon (a
  separate free tool from Intel/GameTechDev) and point the app at it
  with the "Locate PresentMon.exe" button:
  https://github.com/GameTechDev/PresentMon/releases
  (It may ask to elevate itself to Administrator the first time it
  runs - that's PresentMon's own prompt, not this app's.)

  Everything else (memory, CPU, disk, battery, processes, network,
  event log, foreground app) logs fine with no extra downloads.

RUN
  First launch (no PC Monitor data/config yet) automatically runs
  the guided installer below, then marks itself done so every launch
  after that goes straight to the GUI - including the copy the
  installer places in your Start Menu, which starts out already
  marked done. Re-run setup any time with:
    python pc_monitor.py install
  Tick "Start with Windows" in the app to have it launch automatically
  at login, already elevated, with no UAC prompt on any boot after the
  one that happened when you ticked it (a Task Scheduler task, "Run
  with highest privileges" - visible/removable via Task Scheduler >
  Task Scheduler Library, or the same checkbox in the app). Falls back
  to a plain HKCU Run registry entry if Task Scheduler creation fails
  for some reason - works, but means a fresh UAC prompt every single
  boot instead of just the one time.

  Closing the window (the X button, or Alt+F4) minimizes to the
  system tray instead of exiting, so it can't accidentally stop
  logging - right-click the tray icon for Show/Exit, or double-click
  to reopen. Needs pystray + Pillow (installed above); without them,
  closing falls back to an explicit "this will stop logging, are you
  sure?" confirmation rather than silently exiting either way.

LOGS
  Written by default to %ProgramData%\\PCMonitorRemote\\logs. The Python payload
  can live in Downloads or anywhere else without the app creating runtime files there;
  a custom logs location can still be selected explicitly.
  Each file caps at 10 MB, then a new timestamped file starts.
  Total logs folder caps at 1.5 GB - oldest files are deleted first.
  The History tab reads across however many files a chosen time range
  spans, automatically.

INSTALL
  Runs by itself on first launch (see RUN above). What it does:
  installs the pip packages above, lets you pick a logs folder and
  (optionally) a PresentMon path, installs the persistent app under %ProgramData%\\PCMonitorRemote, creates
  Start Menu/Startup shortcuts, deploys the watchdog there, and can enable launch-at-login.
  Everything asks before it does anything.

PERFORMANCE
  All polling runs on a background thread, separate from the window,
  at below-normal OS thread priority, sleeping between polls rather
  than busy-looping - it won't compete with foreground apps for CPU.
  Packet loss is checked with a single ping per poll rather than a
  full speed test, which would itself use enough bandwidth to distort
  the very thing you're trying to measure.
"""

import csv
import glob
import heapq
import json
import os
import platform
import secrets
import string
import queue
import re
import subprocess
import sys
sys.dont_write_bytecode = True
import threading
import time
import tkinter as tk
import urllib.request
import webbrowser
import zipfile
from datetime import datetime, timedelta
from tkinter import ttk, messagebox, filedialog

try:
    import psutil
except ImportError:
    # Not fatal here - the installer (which needs none of this) is what's
    # supposed to fix it. The check that actually matters happens right
    # before the GUI launches, at the bottom of this file.
    psutil = None

try:
    import wmi
    HAVE_WMI = True
except ImportError:
    HAVE_WMI = False

try:
    import win32evtlog
    HAVE_EVTLOG = True
except ImportError:
    HAVE_EVTLOG = False

try:
    import winreg
    HAVE_WINREG = True
except ImportError:
    HAVE_WINREG = False

try:
    import pystray
    from PIL import Image, ImageDraw
    HAVE_TRAY = True
except ImportError:
    HAVE_TRAY = False

CREATE_NO_WINDOW = getattr(subprocess, "CREATE_NO_WINDOW", 0)
CREATE_NEW_CONSOLE = getattr(subprocess, "CREATE_NEW_CONSOLE", 0)

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))

# All runtime-generated PC Monitor files live in one machine-wide data
# directory.  This is deliberately NOT SCRIPT_DIR: the launcher/update copy
# may be sitting in Downloads (or another arbitrary folder), and the app must
# never litter that folder with configs, watchdog scripts, logs, .new/.bak
# files, heartbeat markers, crash reports, tools, or temporary installers.
# The downloaded/installed Python file is only the executable payload; all
# mutable state belongs under ProgramData.
_PROGRAMDATA_ROOT = os.environ.get("PROGRAMDATA") or os.environ.get("LOCALAPPDATA") or SCRIPT_DIR
APP_DATA_DIR = os.path.join(_PROGRAMDATA_ROOT, "PCMonitorRemote")
APP_LOGS_DIR = os.path.join(APP_DATA_DIR, "logs")
APP_TOOLS_DIR = os.path.join(APP_DATA_DIR, "tools")
APP_UPDATES_DIR = os.path.join(APP_DATA_DIR, "updates")
APP_EXPORTS_DIR = os.path.join(APP_DATA_DIR, "exports")
APP_CRASH_DIR = os.path.join(APP_DATA_DIR, "crash_dumps")
APP_PATH = os.path.join(APP_DATA_DIR, "pc_monitor.py")

APP_VERSION = "3.4"

# The external watchdog is a PowerShell script CARRIED INSIDE this file and
# written to disk at setup. It runs as a Scheduled Task independently of
# Python, so it can update/relaunch the app even when Python itself is mid-
# update or wedged. Cross-update: the watchdog keeps THIS .py current, and
# the .py keeps the watchdog current - on launch the app compares the on-disk
# watchdog version to WATCHDOG_VERSION and rewrites the .ps1 when this file
# (pulled by the watchdog) carries a newer one. Bump WATCHDOG_VERSION whenever
# WATCHDOG_PS1 changes so deployed copies refresh.
WATCHDOG_VERSION = "16"
WATCHDOG_PS1 = r'''# PC Monitor watchdog (auto-generated from pc_monitor.py - do not edit;
# it is overwritten from the app's embedded copy whenever this app deploys.
$ErrorActionPreference = 'SilentlyContinue'
# ALL mutable PC Monitor state lives under ProgramData. The watchdog can be
# launched from anywhere; only the Python payload path is resolved from its
# own folder as a fallback. This keeps Downloads/Desktop completely clean.
$dir = Split-Path -Parent $MyInvocation.MyCommand.Definition
$dataDir = Join-Path $env:ProgramData 'PCMonitorRemote'
New-Item -ItemType Directory -Path $dataDir -Force | Out-Null
$cfgPath = Join-Path $dataDir 'pcmonitor_config.json'
if (-not (Test-Path $cfgPath)) { exit }
try { $cfg = Get-Content $cfgPath -Raw | ConvertFrom-Json } catch { exit }

$script  = Join-Path $dataDir 'pc_monitor.py'
if (-not (Test-Path $script)) { $script = Join-Path $dir 'pc_monitor.py' }
$hb      = Join-Path $dataDir 'pcmonitor_heartbeat.json'
$exitReq = Join-Path $dataDir 'pcmonitor_exit_request'
$py  = if ($cfg.python_exe) { $cfg.python_exe } else { 'pythonw' }
$pyc = if ($cfg.python_console_exe) { $cfg.python_console_exe } else { 'python' }
$hook    = $cfg.discord_webhook_url
$url     = $cfg.update_url
$machine = if ($cfg.machine_label) { $cfg.machine_label } else { $env:COMPUTERNAME }
$stale   = 180
$stateFile = Join-Path $dataDir 'pcmonitor_watchdog_state.json'
$watchdogLog = Join-Path $dataDir 'pcmonitor_watchdog.log'

function Log($msg) {
  try { Add-Content -Path $watchdogLog -Value ((Get-Date -Format 'yyyy-MM-dd HH:mm:ss') + ' ' + $msg) } catch {}
}
function Notify($msg) {
  if (-not $hook) { return }
  try {
    $b = @{ content = $msg } | ConvertTo-Json -Compress
    Invoke-RestMethod -Uri $hook -Method Post -Body $b -ContentType 'application/json' -TimeoutSec 15 | Out-Null
  } catch {}
}
function VerTuple($v) { try { return ($v -split '\.' | ForEach-Object { [int]$_ }) } catch { return @(0) } }
function VerGt($a, $b) {
  $x = VerTuple $a; $y = VerTuple $b
  $n = [Math]::Max($x.Count, $y.Count)
  for ($i = 0; $i -lt $n; $i++) {
    $xi = if ($i -lt $x.Count) { $x[$i] } else { 0 }
    $yi = if ($i -lt $y.Count) { $y[$i] } else { 0 }
    if ($xi -gt $yi) { return $true }
    if ($xi -lt $yi) { return $false }
  }
  return $false
}
function AppRunning() {
  if (-not (Test-Path $hb)) { return $false }
  try {
    $h = Get-Content $hb -Raw | ConvertFrom-Json
    $now = [DateTimeOffset]::UtcNow.ToUnixTimeSeconds()
    $age = $now - [double]$h.ts
    $proc = Get-Process -Id ([int]$h.pid) -ErrorAction SilentlyContinue
    return (($proc -ne $null) -and ($age -lt $stale))
  } catch { return $false }
}
function LaunchApp() {
  try { Start-Process -FilePath $py -ArgumentList ('"' + $script + '"') -WindowStyle Hidden } catch {}
}

$updated = $false
Log("WATCHDOG v15 start pid=$PID")

# 1) update: if the hosted APP_VERSION is newer, cleanly stop the app, replace
# the file (validated with py_compile), relaunch, and notify.
if ($url) {
  Log("Update check URL=$url")
  try {
    $remote = (Invoke-WebRequest -Uri $url -UseBasicParsing -TimeoutSec 10).Content
    $rx = [regex]'APP_VERSION\s*=\s*"([0-9.]+)"'
    $remoteVer = $rx.Match($remote).Groups[1].Value
    $localVer = $rx.Match((Get-Content $script -Raw)).Groups[1].Value
    Log("Update versions local=$localVer remote=$remoteVer")
    if ($remoteVer -and $localVer -and (VerGt $remoteVer $localVer)) {
      if (AppRunning) {
        Log("Update required; requesting app shutdown")
        New-Item -Path $exitReq -ItemType File -Force | Out-Null
        for ($i = 0; $i -lt 20; $i++) { Start-Sleep -Seconds 1; if (-not (AppRunning)) { break } }
        if (AppRunning) {
          try { $h = Get-Content $hb -Raw | ConvertFrom-Json; Stop-Process -Id ([int]$h.pid) -Force } catch {}
        }
        Remove-Item $exitReq -Force -ErrorAction SilentlyContinue
      }
      $updateDir = Join-Path $env:ProgramData 'PCMonitorRemote\updates'
      New-Item -ItemType Directory -Path $updateDir -Force | Out-Null
      $tmp = Join-Path $updateDir (($script | Split-Path -Leaf) + '.new')
      $bak = Join-Path $updateDir (($script | Split-Path -Leaf) + '.bak')
      Remove-Item $tmp -Force -ErrorAction SilentlyContinue
      [System.IO.File]::WriteAllText($tmp, $remote)
      $pc = Start-Process -FilePath $pyc -ArgumentList @('-m','py_compile', $tmp) -WindowStyle Hidden -Wait -PassThru
      Log("py_compile exit code=$($pc.ExitCode)")
      if ($pc.ExitCode -eq 0) {
        Copy-Item $script $bak -Force -ErrorAction SilentlyContinue
        Move-Item $tmp $script -Force
        Notify ("PC Monitor updated " + $localVer + " -> " + $remoteVer + " on " + $machine + ". Restarting.")
        LaunchApp
        try { (@{ running = $true } | ConvertTo-Json -Compress) | Set-Content -Path $stateFile } catch {}
        $updated = $true
        Log("Update applied successfully $localVer -> $remoteVer")
      } else {
        Log("Update rejected because py_compile failed")
        Remove-Item $tmp -Force -ErrorAction SilentlyContinue
      }
    }
  } catch { Log("Update exception: $($_.Exception.GetType().Name): $($_.Exception.Message)") }
} else {
  Log("No update URL configured")
}

# 2) lifecycle: detect running <-> stopped TRANSITIONS via a persisted state
# file, so "stopped" fires exactly ONCE per stop (crash or clean close), not
# every run. "running" is announced by the app itself on startup, so the
# watchdog only records the running transition without re-notifying.
if (-not $updated) {
  $prevRunning = $false
  try { if (Test-Path $stateFile) { $prevRunning = [bool]((Get-Content $stateFile -Raw | ConvertFrom-Json).running) } } catch {}
  $nowRunning = AppRunning
  if ($nowRunning -ne $prevRunning) {
    if (-not $nowRunning) {
      if (Test-Path $hb) {
        Notify ("PC Monitor STOPPED on " + $machine + " (crash or task killed).")
        Remove-Item $hb -Force -ErrorAction SilentlyContinue
      } else {
        Notify ("PC Monitor STOPPED on " + $machine + " (closed).")
      }
    }
    try { (@{ running = $nowRunning } | ConvertTo-Json -Compress) | Set-Content -Path $stateFile } catch {}
    Log("Lifecycle state changed running=$nowRunning")
  }
}
'''

# A windowless VBScript launcher for the watchdog. The Scheduled Task runs
# this via wscript.exe (which has NO console), and it launches PowerShell with
# window style 0 (fully hidden) - so the watchdog never flashes a window every
# few minutes. Self-locating: runs the .ps1 sitting next to it.
WATCHDOG_VBS = r'''Dim sh, fso, dir
Set sh = CreateObject("WScript.Shell")
Set fso = CreateObject("Scripting.FileSystemObject")
dir = fso.GetParentFolderName(WScript.ScriptFullName)
sh.Run "powershell -NoProfile -ExecutionPolicy Bypass -WindowStyle Hidden -File """ & dir & "\pcmonitor_watchdog.ps1""", 0, False
'''
# generic, unlabeled SuperIO sensors (unconnected motherboard headers that
# read a fixed bogus value forever, e.g. a constant 104C phantom) - matched
# so they can be kept in the raw log but excluded from decision logic
_PHANTOM_SENSOR_RE = re.compile(r"(temperature|voltage|fan|current|power)\s*#?\s*\d+\s*$", re.I)
CONFIG_PATH = os.path.join(APP_DATA_DIR, "pcmonitor_config.json")
LEGACY_CONFIG_PATH = os.path.join(SCRIPT_DIR, "pcmonitor_config.json")

# External-watchdog coordination files (all next to the script, so the
# watchdog running the same file with --watchdog finds them):
#  - heartbeat: main app stamps {pid, ts, version} here while alive, and
#    DELETES it on a clean exit, so the watchdog can tell "running" from
#    "crashed/killed" from "closed on purpose".
#  - exit-request: the watchdog drops this to ask the running app to shut
#    down cleanly (for an update) rather than being force-killed.
HEARTBEAT_FILE = os.path.join(APP_DATA_DIR, "pcmonitor_heartbeat.json")
EXIT_REQUEST_FILE = os.path.join(APP_DATA_DIR, "pcmonitor_exit_request")
HEARTBEAT_STALE_SECONDS = 180  # heartbeat older than this => app is gone
DEFAULT_CONFIG = {"logs_dir": None, "presentmon_path": None, "ping_host": "1.1.1.1",
                   "lhm_web_port": 8085, "setup_complete": False,
                   # auto-open LibreHardwareMonitor (with its web server) when
                   # PC Monitor starts, if it isn't already running. Set false
                   # in pcmonitor_config.json to disable.
                   "auto_launch_lhm": True,
                   # adaptive sampling: idle at the base interval (the Poll
                   # spinbox), automatically burst to fast_poll_interval while
                   # gaming (frames flowing / GPU busy), hot, or just after an
                   # error event - so the seconds around a crash are captured
                   # at high resolution without paying for it at the desktop.
                   "adaptive_poll": True,
                   "fast_poll_interval": 1.0,
                   "fast_gpu_load": 50,   # % GPU-core load that counts as "busy"
                   "fast_temp_c": 80,     # any temp >= this counts as "hot"
                   # GPU-hang handling. Detection is always on (it just flags
                   # the log). Recovery is opt-in and best-effort: when the GPU
                   # stalls, try the Win+Ctrl+Shift+B graphics-stack reset. It's
                   # non-destructive but a long shot once a driver is fully hung.
                   "gpu_stall_recovery": False,
                   "gpu_stall_flag_samples": 3,   # (legacy, superseded by seconds)
                   "gpu_stall_recover_samples": 5, # (legacy, superseded by seconds)
                   # time-based GPU-stall thresholds (adaptive polling means
                   # sample counts map to different real durations - #10)
                   "gpu_stall_flag_seconds": 3.0,
                   "gpu_stall_recover_seconds": 5.0,
                   # write a plain-text crash report under APP_CRASH_DIR on the next
                   # launch after a session that didn't shut down cleanly
                   "crash_dump_to_desktop": True,  # legacy setting name; reports now stay in APP_CRASH_DIR
                   # also dump the last N MB of RAW log data (the telemetry
                   # leading up to the crash, across rotated files) under APP_CRASH_DIR
                   "crash_dump_last_mb": 10,
                   # optional: POST the crash report + data to a Discord webhook
                   # so crashes come to you automatically (leave blank to disable)
                   "discord_webhook_url": "https://discord.com/api/webhooks/1547039567759278141/-Xh74R07jsP4YN7QaSJF416C4_eP-yfAA7_7dp5M8hSmZTeqEa2pJ6jv0hq1YW5sygHc",
                   "discord_upload_crash": True,
                   # label this machine (e.g. a friend's name) - stamped into
                   # every session header, report, and Discord message so you
                   # can tell whose crash you're looking at. Blank = hostname.
                   "machine_label": "",
                   # self-update: on launch, fetch update_url and if its
                   # APP_VERSION is newer, back up + replace this file so you
                   # never have to hand friends a new copy again. Set update_url
                   # to a raw GitHub/Gist URL of pc_monitor.py. Blank = off.
                   "auto_update": True,
                   "update_url": "https://raw.githubusercontent.com/Giveup911/Monitoring/main/pc_monitor.py",
                   "update_check_interval_hours": 1 / 60,
                   "auto_update_restart": True,
                   # external watchdog (a Scheduled Task running this same file
                   # with --watchdog every 1 minute). It owns updates (clean
                   # stop + replace + restart, so the running script never
                   # replaces itself) and detects crashes/kills to relaunch and
                   # notify. Much more reliable than in-process self-update.
                   "watchdog_enabled": True,
                   "watchdog_interval_minutes": 1,
                   "watchdog_autostart": True,    # relaunch the app if it's not running
                   "auto_update_via_watchdog": True}  # main app skips in-process update


def _load_config():
    """Load the machine-wide config.

    Older builds stored config beside the Python file, which meant a copy
    launched from Downloads created support files there.  Prefer the new
    ProgramData config, but read the old config once so existing installs do
    not lose their settings; migration is completed after CONFIG is created.
    """
    cfg = dict(DEFAULT_CONFIG)
    loaded_from_legacy = False
    for path in (CONFIG_PATH, LEGACY_CONFIG_PATH):
        if path == LEGACY_CONFIG_PATH and os.path.normcase(path) == os.path.normcase(CONFIG_PATH):
            continue
        try:
            with open(path, "r", encoding="utf-8") as f:
                cfg.update(json.load(f))
            loaded_from_legacy = (path == LEGACY_CONFIG_PATH)
            if path == CONFIG_PATH:
                loaded_from_legacy = False
                break
        except (FileNotFoundError, json.JSONDecodeError, OSError):
            continue
    if not cfg.get("logs_dir") or (loaded_from_legacy and os.path.normcase(str(cfg.get("logs_dir"))) == os.path.normcase(os.path.join(SCRIPT_DIR, "pc_monitor_logs"))):
        cfg["logs_dir"] = APP_LOGS_DIR
    cfg["_legacy_config_loaded"] = loaded_from_legacy
    return cfg


_CONFIG_LOCK = threading.Lock()


def _atomic_write_json(path, obj):
    """#18: write to a temp file, flush+fsync, then os.replace - so a power
    loss or kill mid-write can never leave a half-written (corrupt) config
    that the next launch fails to parse. os.replace is atomic on Windows."""
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(obj, f, indent=2)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, path)


def _save_config(cfg):
    with _CONFIG_LOCK:
        try:
            _atomic_write_json(CONFIG_PATH, cfg)
            return True
        except OSError:
            return False


def _set_config(key, value):
    """Mutates the shared CONFIG dict and persists it atomically, under a
    lock - CONFIG gets written from the GUI thread, the auto-setup worker
    thread, and read from the polling thread."""
    with _CONFIG_LOCK:
        CONFIG[key] = value
        try:
            _atomic_write_json(CONFIG_PATH, CONFIG)
            return True
        except OSError:
            return False


CONFIG = _load_config()
LOGS_DIR = CONFIG["logs_dir"]
TOOLS_DIR = APP_TOOLS_DIR


def _migrate_legacy_runtime_files():
    """Move support files left beside an older copy into APP_DATA_DIR.

    Never moves/deletes the user's actual Python payload.  This is specifically
    for the files previous builds generated beside the script (especially in
    Downloads).  Existing files in the central location win; legacy files are
    only copied/moved when the destination does not already exist.
    """
    if os.path.normcase(SCRIPT_DIR) == os.path.normcase(APP_DATA_DIR):
        return
    try:
        os.makedirs(APP_DATA_DIR, exist_ok=True)
        os.makedirs(APP_LOGS_DIR, exist_ok=True)
        os.makedirs(APP_TOOLS_DIR, exist_ok=True)
        os.makedirs(APP_UPDATES_DIR, exist_ok=True)
        os.makedirs(APP_EXPORTS_DIR, exist_ok=True)
        os.makedirs(APP_CRASH_DIR, exist_ok=True)
        import shutil
        legacy_files = [
            "pcmonitor_config.json", "pcmonitor_heartbeat.json",
            "pcmonitor_exit_request", "pcmonitor_watchdog.ps1",
            "pcmonitor_watchdog.ver", "pcmonitor_watchdog_launch.vbs",
            "pcmonitor_watchdog_state.json", "pcmonitor_watchdog.log",
            "pc_monitor_crash.log", ".pcmon_lastupdate",
        ]
        for name in legacy_files:
            src = os.path.join(SCRIPT_DIR, name)
            dst = os.path.join(APP_DATA_DIR, name)
            if os.path.isfile(src):
                if not os.path.exists(dst):
                    try:
                        shutil.move(src, dst)
                    except OSError:
                        try:
                            shutil.copy2(src, dst)
                        except OSError:
                            pass
                else:
                    try:
                        os.remove(src)
                    except OSError:
                        pass
        # Previous updaters could leave these beside the downloaded script.
        # Move only PC Monitor's known transient/backup names; never touch the
        # actual source .py or unrelated files in the user's Downloads folder.
        for name in ("pc_monitor.py.new", "pc_monitor.py.bak", "pc_monitor.py.tmp",
                     "pcmonitor_config.json.tmp", "pcmonitor_watchdog_state.json.tmp",
                     "pcmonitor_watchdog.ps1.tmp", "pcmonitor_watchdog.ver.tmp",
                     "pcmonitor_watchdog_launch.vbs.tmp", ".pcmon_lastupdate.tmp"):
            src = os.path.join(SCRIPT_DIR, name)
            dst = os.path.join(APP_UPDATES_DIR, name)
            if os.path.isfile(src):
                if not os.path.exists(dst):
                    try:
                        shutil.move(src, dst)
                    except OSError:
                        pass
                else:
                    try:
                        os.remove(src)
                    except OSError:
                        pass
        legacy_log_dir = os.path.join(SCRIPT_DIR, "pc_monitor_logs")
        if os.path.isdir(legacy_log_dir) and os.path.normcase(legacy_log_dir) != os.path.normcase(LOGS_DIR):
            os.makedirs(LOGS_DIR, exist_ok=True)
            for name in os.listdir(legacy_log_dir):
                src = os.path.join(legacy_log_dir, name)
                dst = os.path.join(LOGS_DIR, name)
                if os.path.isfile(src):
                    if not os.path.exists(dst):
                        try:
                            shutil.move(src, dst)
                        except OSError:
                            pass
                    else:
                        try:
                            os.remove(src)
                        except OSError:
                            pass
            try:
                if not os.listdir(legacy_log_dir):
                    os.rmdir(legacy_log_dir)
            except OSError:
                pass
        # Persist the migrated config without the internal migration marker.
        if CONFIG.pop("_legacy_config_loaded", False) or not os.path.exists(CONFIG_PATH):
            _atomic_write_json(CONFIG_PATH, CONFIG)
    except Exception:
        CONFIG.pop("_legacy_config_loaded", None)


_migrate_legacy_runtime_files()
MAX_FILE_BYTES = 10 * 1024 * 1024
MAX_TOTAL_BYTES = int(1.5 * 1024**3)

RUN_KEY = r"Software\Microsoft\Windows\CurrentVersion\Run"
APP_REG_NAME = "PCMonitor"

# ---- dark theme colors ----
BG = "#1e1e1e"
PANEL = "#272727"
FG = "#e6e6e6"
MUTED = "#9a9a9a"
ACCENT = "#4da3ff"
GOOD = "#4caf50"
WARN = "#e0b23e"
BAD = "#e05a5a"
BORDER = "#3a3a3a"
# category accents, used as a thin top strip on each stat card
ACCENT_THERMAL = "#e0625a"
ACCENT_CPU = "#4da3ff"
ACCENT_MEM = "#8a7ff0"
ACCENT_NET = "#3ecf8e"
ACCENT_FPS = "#f0b84d"
ACCENT_GPU = "#e0589e"


def is_admin():
    """Whether this process is elevated. Several things want it, though
    NOT the default sensor path:
    - Reading sensors over REST (localhost HTTP) does NOT need it - only
      LibreHardwareMonitor itself needs privilege to touch the hardware.
    - The legacy WMI sensor path DOES need the *reading* process elevated
      (a common cause of sensors showing N/A while LHM's own window shows
      live data - it's running fine, this process just can't query it).
    - Controlling PresentMon (reading its exe path, terminating orphans,
      lowering its priority) needs matching integrity: once PresentMon
      self-elevates via --restart_as_admin, a non-elevated app hits
      AccessDenied across the boundary and that cleanup silently no-ops.
    - Hiding LHM's elevated window (SW_HIDE under UIPI) also needs it.
    So auto-elevation is kept, but note it's for tool *control*, not for
    the REST read the app now uses by default."""
    try:
        import ctypes
        return bool(ctypes.windll.shell32.IsUserAnAdmin())
    except Exception:
        return False


def relaunch_as_admin():
    """Restarts this exact script, with the same arguments, elevated.
    Goes through the normal Windows UAC prompt like anything else
    requesting elevation - nothing here bypasses that.

    Deliberately resolves the real interpreter via find_pythonw()
    rather than just reusing sys.executable: when a script is launched
    by double-clicking through py.exe (the Python Launcher - a
    separate small executable in its own folder, e.g. AppData\\Local\\
    Programs\\Python\\Launcher\\, which some Windows Python installs
    use as the .py file association), sys.executable can report
    py.exe's own path instead of the real interpreter's. Elevating and
    relaunching py.exe directly in that case has been observed to open
    a stuck, blank console instead of actually running anything -
    find_pythonw() resolves the real pythonw.exe via the registry
    first specifically to avoid that.

    Returns True if the launch genuinely appears to have gone through,
    False if it didn't (including if the UAC prompt was declined -
    ShellExecuteW's return value convention makes both look the same:
    any value <= 32 means failure, anything above means the new
    process instance handle, per the documented Win32 API contract).
    Callers should check this before assuming it's safe to close their
    own window - closing unconditionally risks leaving nothing open at
    all if elevation was declined."""
    import ctypes
    script = os.path.abspath(__file__)
    args = " ".join(f'"{a}"' for a in sys.argv[1:])
    param = f'"{script}"' + (f" {args}" if args else "")
    target = find_pythonw()
    ret = ctypes.windll.shell32.ShellExecuteW(
        None, "runas", target, param, os.path.dirname(script), 1)
    return ret > 32


IS_ADMIN = is_admin()


def _is_process_name_running(name_substring):
    """Checks by process name substring (case-insensitive) - used for
    LibreHardwareMonitor specifically, since (unlike PresentMon) this
    app doesn't track a specific exe path for it; sensor reads just
    connect to whatever's listening on localhost, wherever it's
    running from. A name-based check carries a small false-positive
    risk (another program happening to share a similar name) that
    path-based matching wouldn't, but there's no expected path to
    match against here. Returns False (never raises) if psutil isn't
    available or the check itself fails for any reason - this is a
    diagnostic nicety, not something that should ever break polling."""
    if psutil is None:
        return False
    try:
        for p in psutil.process_iter(["name"]):
            try:
                if name_substring in (p.info.get("name") or "").lower():
                    return True
            except (psutil.NoSuchProcess, psutil.AccessDenied):
                continue
    except Exception:
        pass
    return False


def _lower_thread_priority():
    """Keeps background polling from competing with whatever you're
    actually doing (games, encoding, etc.) for CPU time under load.
    Only affects this one background thread, not the GUI thread - the
    window stays responsive either way. Safe no-op if unavailable."""
    try:
        import win32api
        import win32process
        handle = win32api.GetCurrentThread()
        win32process.SetThreadPriority(handle, win32process.THREAD_PRIORITY_BELOW_NORMAL)
    except Exception:
        pass


# ---------------------------------------------------------------- sensors --

LHM_REST_TIMEOUT = 3


def _parse_lhm_value(text):
    """LibreHardwareMonitor's REST API gives values as formatted
    strings like "45.0 C" or "3600 RPM", not raw numbers - this pulls
    out just the leading numeric part. Returns None for "-" (LHM's
    placeholder for "no current reading") or anything unparseable."""
    if not text:
        return None
    m = re.match(r"[-+]?\d*\.?\d+", text.strip())
    return float(m.group()) if m else None


def _walk_lhm_tree(node, parent_label, out):
    """Recursively walks LibreHardwareMonitor's data.json tree. Every
    leaf (no Children) is an actual sensor reading; its immediate
    parent's Text is the category group (Temperatures/Voltages/Fans/
    Controls/Clocks/Loads/Powers/...) - close enough to this app's
    existing "{Type}: {Name}" key convention that the singular-prefix
    matching in find_metric()/_extract_sensor_headline() (e.g.
    "temperature" is a prefix of "temperatures") already works against
    it unchanged."""
    children = node.get("Children") or []
    if not children:
        name = node.get("Text")
        value = _parse_lhm_value(node.get("Value"))
        if name and value is not None:
            out[f"{parent_label}: {name}"] = round(value, 3)
        return
    label = node.get("Text") or parent_label
    for child in children:
        _walk_lhm_tree(child, label, out)


def _fetch_lhm_rest(port):
    """LibreHardwareMonitor 0.9.5+ removed WMI publishing entirely
    (see LibreHardwareMonitor/LibreHardwareMonitor issue #2143,
    "0.9.5: WMI Output Broken") and moved to a REST API instead -
    Options > Remote Web Server > Run in LHM, served at this URL by
    default. Returns a sensors dict in the same shape this app has
    always used, or None on any failure."""
    url = f"http://localhost:{port}/data.json"
    req = urllib.request.Request(url, headers={"User-Agent": "PCMonitor"})
    with urllib.request.urlopen(req, timeout=LHM_REST_TIMEOUT) as resp:
        tree = json.loads(resp.read().decode("utf-8"))
    out = {}
    _walk_lhm_tree(tree, tree.get("Text", ""), out)
    return out or None


class SensorReader:
    """Wraps access to LibreHardwareMonitor's sensor data. Tries the
    WMI namespace first (works on older LHM versions), then falls back
    to LHM's REST API (Options > Remote Web Server > Run, default
    http://localhost:8085/data.json) - LHM 0.9.5+ stopped publishing
    via WMI at all, so the namespace either doesn't exist or connects
    successfully but returns zero sensors on those versions. This
    isn't a bug in this app; it's an upstream change in LHM itself.
    Degrades gracefully if neither is reachable."""

    def __init__(self, web_port=8085):
        self.connected = False
        self.method = None  # "wmi" or "rest", once connected
        self.last_error = None
        self._conn = None
        self.web_port = web_port
        self._try_connect()

    def _try_connect(self):
        errors = []
        if HAVE_WMI:
            try:
                conn = wmi.WMI(namespace="root\\LibreHardwareMonitor")
                if list(conn.Sensor()):
                    self._conn = conn
                    self.connected = True
                    self.method = "wmi"
                    self.last_error = None
                    return
                errors.append("WMI namespace connected but returned no sensors "
                               "(LibreHardwareMonitor 0.9.5+ no longer publishes "
                               "via WMI at all - this is expected on recent "
                               "versions, not an error)")
            except Exception as e:
                errors.append(f"WMI: {type(e).__name__}: {e}")
        else:
            errors.append("WMI: wmi/pywin32 package not installed")

        try:
            if _fetch_lhm_rest(self.web_port):
                self.connected = True
                self.method = "rest"
                self.last_error = None
                return
            errors.append(f"REST (localhost:{self.web_port}/data.json): no "
                           "sensors returned - is \"Options > Remote Web "
                           "Server > Run\" enabled in LibreHardwareMonitor?")
        except Exception as e:
            errors.append(f"REST (localhost:{self.web_port}/data.json): "
                           f"{type(e).__name__}: {e}")

        self._conn = None
        self.connected = False
        self.method = None
        self.last_error = "; ".join(errors)

    def read_sensors(self):
        if not self.connected:
            return {}
        if self.method == "rest":
            return _fetch_lhm_rest(self.web_port) or {}
        out = {}
        for s in self._conn.Sensor():
            if s.Value is not None:
                out[f"{s.SensorType}: {s.Name}"] = round(s.Value, 3)
        return out


class ProcessMonitor:
    """Tracks per-process CPU% across polls by keeping the same psutil
    Process objects alive between calls (a fresh Process object always
    reports 0% on its first sample). Readings settle in after the
    first poll."""

    def __init__(self):
        self._cache = {}
        # psutil's per-process cpu_percent() is scaled 0..100*ncores (a
        # process pegging 4 of 8 logical cores reads ~400%). Cache the
        # logical core count once so top() can divide back down to the
        # 0..100, Task-Manager-style number the GUI/table actually imply.
        self._ncores = psutil.cpu_count(logical=True) or 1

    def top(self, n=5):
        current = set(psutil.pids())
        for pid in current:
            if pid not in self._cache:
                try:
                    proc = psutil.Process(pid)
                    proc.cpu_percent(interval=None)  # prime the baseline
                    self._cache[pid] = proc
                except (psutil.NoSuchProcess, psutil.AccessDenied):
                    continue
        for pid in list(self._cache):
            if pid not in current:
                del self._cache[pid]

        rows = []
        for pid, proc in list(self._cache.items()):
            # PID 0 is the System Idle Process: it represents UNUSED CPU,
            # not usage, and psutil reports it at ~100%*ncores, so left in
            # it dominates the Top-CPU list nearly every poll (observed as
            # #1 in ~98% of rows in a real log). It's noise here - skip it.
            if pid == 0:
                continue
            try:
                name = proc.name()
                if name == "System Idle Process":
                    continue
                rows.append({
                    "pid": pid,
                    "name": name,
                    # divide by logical core count -> 0..100 like Task Manager
                    "cpu": round(proc.cpu_percent(interval=None) / self._ncores, 1),
                    "mem": round(proc.memory_percent(), 1),
                })
            except (psutil.NoSuchProcess, psutil.AccessDenied):
                continue

        # nlargest instead of a full sort: only the top n (5) actually
        # matter out of what can be 100-300+ processes, and this runs
        # twice (cpu, mem) on every single poll for as long as the app
        # is logging - sorting the whole list every time to throw away
        # everything past the first 5 is pure waste at that scale.
        by_cpu = heapq.nlargest(n, rows, key=lambda r: r["cpu"])
        by_mem = heapq.nlargest(n, rows, key=lambda r: r["mem"])
        return by_cpu, by_mem


class EventLogWatcher:
    """Surfaces new Error-level entries from the Windows event logs -
    usually the strongest signal for *why* a crash happened, not just
    its symptoms. Only reports events seen after the watcher starts, so
    it doesn't dump the whole log history. Reading these logs doesn't
    require admin rights.

    Watches BOTH the System log (Kernel-Power 41, BugCheck, WHEA-Logger,
    display-driver timeouts) AND the Application log (Application Error
    1000, App Hang 1002, .NET Runtime) - a game/app crash and its
    WerFault report land in the Application log, so watching only System
    (as this did before) missed exactly the per-app crashes WerFault
    fires on. Each event also carries its detail strings (StringInserts):
    for Application Error 1000 those are the faulting app, version,
    faulting module, and exception code - i.e. the actual cause, not
    just "something crashed."

    Opens a fresh handle per poll per log rather than reusing one:
    EVENTLOG_SEQUENTIAL_READ's cursor only ever moves backward through
    history on a given handle, so reusing one across polls would just
    walk further into the past each time instead of ever reaching
    newly-appended events. Each poll also loops through multiple reads
    if more events landed since the last check than fit in one buffer,
    so a burst doesn't get partially skipped."""

    LOG_NAMES = ("System", "Application")

    def __init__(self):
        self.available = False
        self._last_record = {}  # per-log high-water RecordNumber
        if not HAVE_EVTLOG:
            return
        for log_name in self.LOG_NAMES:
            self._last_record[log_name] = None
            try:
                hand = win32evtlog.OpenEventLog(None, log_name)
                try:
                    events = self._read_chunk(hand)
                    if events:
                        self._last_record[log_name] = events[0].RecordNumber
                finally:
                    win32evtlog.CloseEventLog(hand)
                self.available = True  # at least one log opened
            except Exception:
                continue

    def _read_chunk(self, hand):
        flags = win32evtlog.EVENTLOG_BACKWARDS_READ | win32evtlog.EVENTLOG_SEQUENTIAL_READ
        return win32evtlog.ReadEventLog(hand, flags, 0)

    @staticmethod
    def _detail(ev):
        """The event's insertion strings, trimmed. For Application Error
        (1000) this is [faulting app, app version, app timestamp,
        faulting module, module version, module timestamp, exception
        code, fault offset, ...] - the crash cause in plain text."""
        try:
            inserts = ev.StringInserts or []
        except Exception:
            return None
        cleaned = [str(s).strip() for s in inserts if s]
        if not cleaned:
            return None
        # cap so a pathological event can't bloat every log line
        return cleaned[:10]

    def _poll_log(self, log_name):
        try:
            hand = win32evtlog.OpenEventLog(None, log_name)
        except Exception:
            return []
        last = self._last_record.get(log_name)
        # #28: a cleared or rolled-over log restarts RecordNumber at a low
        # value. If the newest record is now BELOW our high-water mark, the
        # log was cleared - re-baseline to the new newest and report nothing
        # this poll, instead of silently missing every new event until the
        # numbers climb back past the old mark.
        try:
            peek = self._read_chunk(hand)
            if peek and last is not None and peek[0].RecordNumber < last:
                self._last_record[log_name] = peek[0].RecordNumber
                try:
                    win32evtlog.CloseEventLog(hand)
                except Exception:
                    pass
                return []
            # reopen so the backward-read cursor starts at the newest again
            win32evtlog.CloseEventLog(hand)
            hand = win32evtlog.OpenEventLog(None, log_name)
        except Exception:
            try:
                win32evtlog.CloseEventLog(hand)
            except Exception:
                pass
            return []
        new = []
        newest_seen = last
        try:
            for _ in range(50):  # hard cap - a pathological log can't loop forever
                try:
                    events = self._read_chunk(hand)
                except Exception:
                    break
                if not events:
                    break
                reached_known = False
                for ev in events:
                    if last is not None and ev.RecordNumber <= last:
                        reached_known = True
                        break
                    if newest_seen is None or ev.RecordNumber > newest_seen:
                        newest_seen = ev.RecordNumber
                    if ev.EventType == win32evtlog.EVENTLOG_ERROR_TYPE:
                        new.append({
                            "log": log_name,
                            "record": ev.RecordNumber,
                            "source": ev.SourceName,
                            "event_id": ev.EventID & 0xFFFF,
                            "detail": self._detail(ev),
                            # Deliberately NOT ev.TimeGenerated.isoformat() -
                            # pywin32's PyTime has a long-documented,
                            # confirmed bug where values built from a
                            # Windows FILETIME (always UTC) get run through
                            # a C mktime() call that assumes local time,
                            # silently shifting the result by the local
                            # UTC offset (pywin32 bug 2831327 - confirmed
                            # for GetProcessTimes/GetThreadTimes, sharing
                            # the same PyTime conversion machinery event
                            # log timestamps also go through). int(PyTime)
                            # gives the raw Unix timestamp directly,
                            # sidestepping that conversion chain entirely -
                            # then datetime.fromtimestamp() converts it to
                            # local time the same well-tested way boot
                            # time already does elsewhere in this file,
                            # keeping every timestamp in the app on the
                            # same convention.
                            "time": datetime.fromtimestamp(
                                int(ev.TimeGenerated)).isoformat(timespec="seconds"),
                        })
                if reached_known or last is None:
                    break
        finally:
            try:
                win32evtlog.CloseEventLog(hand)
            except Exception:
                pass
        self._last_record[log_name] = newest_seen
        return list(reversed(new))

    def poll_new(self):
        if not self.available:
            return []
        out = []
        for log_name in self.LOG_NAMES:
            try:
                out.extend(self._poll_log(log_name))
            except Exception:
                continue
        # oldest-first across both logs, by record time
        out.sort(key=lambda e: e.get("time") or "")
        return out


def get_foreground_app():
    """Whatever window currently has focus - cheap, reliable, and needs
    no hardcoded list of "known games". Returns None off-Windows or if
    pywin32's window APIs aren't available."""
    try:
        import win32gui
        import win32process
        hwnd = win32gui.GetForegroundWindow()
        if not hwnd:
            return None
        _, pid = win32process.GetWindowThreadProcessId(hwnd)
        title = win32gui.GetWindowText(hwnd) or ""
        name = None
        try:
            name = psutil.Process(pid).name()
        except (psutil.NoSuchProcess, psutil.AccessDenied):
            pass
        return {"pid": pid, "process": name, "title": title[:120]}
    except Exception:
        return None


def _parse_ping_output(text):
    """Pulls packet loss % and round-trip time (ms) out of Windows
    ping's text output. Either may be None if not found (e.g. a total
    timeout has no time= line).

    Deliberately does NOT rely on the English words "loss" or "time"
    anywhere in here - Windows ping's output text is entirely
    different on a non-English system locale (e.g. German, French),
    and even within English installs the exact phrasing has drifted
    across Windows versions before. Loss for a single-packet ping
    (-n 1, what this app sends) is derived from the process's own
    return code instead: language-independent, and a value ping.exe
    has always been contractually correct about - 0 means a reply
    came back, anything else means it didn't. Only the round-trip
    time itself still comes from the text, since the return code
    doesn't carry that - matched via a looser pattern (just digits
    immediately before "ms", wherever they appear) that doesn't
    require any particular language's surrounding words, only the
    "ms" unit, which stays in Latin script even on localized Windows."""
    ms = None
    m = re.search(r"[=<](\d+)\s*ms\b", text)
    if m:
        ms = int(m.group(1))
    return ms


def _ping_loss_from_returncode(returncode):
    """0% loss if ping.exe's own return code says a reply came back,
    100% if not - see _parse_ping_output for why this replaces parsing
    the word "loss" out of ping's (English-only) text output."""
    return 0 if returncode == 0 else 100


_VIRTUAL_IFACE_RE = re.compile(
    r"^lo$|loopback|vethernet|virtualbox|vbox|vmware|hyper-v|npcap|"
    r"teredo|isatap|tap-windows|docker|wsl|"
    r"tailscale|wireguard|wintun|nordlynx|nordvpn|protonvpn|mullvad|"
    r"openvpn|zerotier|expressvpn|surfshark",
    re.IGNORECASE,
)


class NetMonitor:
    """Throughput via psutil (cheap, continuous, every poll), summed
    across your real network adapters only. psutil's system-wide total
    otherwise also counts loopback and any virtual adapters
    (VirtualBox, Hyper-V, WSL, VPN taps, ...) - local IPC traffic
    between processes (game engines, VR runtimes, etc.) shows up on
    those and can dwarf your real connection in one direction, making
    up/down look wildly asymmetric or "swapped" when they're not.
    Packet loss/latency via a single Windows `ping` per poll (one
    packet, ~1s max wait) rather than a full speed test, which would
    itself use enough bandwidth to distort the very thing you're
    trying to measure."""

    # Ping spawns a subprocess (~up to 1s) - the single most expensive thing
    # a poll does. When polling fast (adaptive burst, or a user-set 1s base)
    # we don't want to spawn it every tick; latency/loss doesn't change
    # meaningfully second-to-second. Run it at most this often and reuse the
    # last result in between, so fast polling doesn't multiply ping cost.
    PING_MIN_INTERVAL = 4.0

    def __init__(self, ping_host="1.1.1.1"):
        self.ping_host = ping_host
        self._last_totals = None
        self._last_time = None
        self._last_ifaces = None      # #8: the adapter set the baseline was for
        self._last_ping_time = None
        self._last_ping = (None, None)  # (loss_percent, ms)

    def _real_adapter_totals(self):
        try:
            per_nic = psutil.net_io_counters(pernic=True)
        except Exception:
            return None
        real = {n: io for n, io in per_nic.items() if not _VIRTUAL_IFACE_RE.search(n)}
        pool = real if real else per_nic  # never end up with nothing to report
        sent = sum(io.bytes_sent for io in pool.values())
        recv = sum(io.bytes_recv for io in pool.values())
        return frozenset(pool), sent, recv  # #8: also report which adapters

    def sample(self):
        stats = {}
        try:
            totals = self._real_adapter_totals()
            now = time.monotonic()  # #52: monotonic - immune to clock changes
            if totals is not None:
                ifaces, sent, recv = totals
                # #7/#8: only compute a rate against a comparable baseline.
                # If the adapter SET changed (Wi-Fi<->Ethernet) or a counter
                # rolled BACKWARD (interface/counter reset), the summed totals
                # aren't a continuous series - reset the baseline and emit no
                # rate this sample instead of a bogus spike or a false zero.
                comparable = (self._last_totals is not None
                              and ifaces == self._last_ifaces
                              and sent >= self._last_totals[0]
                              and recv >= self._last_totals[1])
                if comparable:
                    dt = max(now - self._last_time, 0.001)
                    d_sent = sent - self._last_totals[0]
                    d_recv = recv - self._last_totals[1]
                    stats["sent_mbps"] = round(d_sent * 8 / dt / 1_000_000, 2)
                    stats["recv_mbps"] = round(d_recv * 8 / dt / 1_000_000, 2)
                elif self._last_totals is not None:
                    stats["net_baseline_reset"] = True
                self._last_totals = (sent, recv)
                self._last_time = now
                self._last_ifaces = ifaces
                stats["sent_gb_total"] = round(sent / 1024**3, 3)
                stats["recv_gb_total"] = round(recv / 1024**3, 3)
        except Exception:
            pass

        now = time.time()
        if self._last_ping_time is None or (now - self._last_ping_time) >= self.PING_MIN_INTERVAL:
            try:
                result = subprocess.run(
                    ["ping", "-n", "1", "-w", "1000", self.ping_host],
                    capture_output=True, text=True, timeout=2,
                    creationflags=CREATE_NO_WINDOW)
                self._last_ping = (_ping_loss_from_returncode(result.returncode),
                                   _parse_ping_output(result.stdout))
            except Exception:
                self._last_ping = (None, None)
            self._last_ping_time = now
        stats["ping_loss_percent"], stats["ping_ms"] = self._last_ping
        return stats


FRAME_STUTTER_MULT = 1.5
FRAME_STUTTER_STDDEV = 3


def is_phantom_sensor(key):
    """True for generic, unlabeled SuperIO sensors like 'Temperatures:
    Temperature #4' or 'Voltages: Voltage #6' - unconnected motherboard
    headers that read a fixed bogus value (e.g. a constant 104C) forever.
    Used to keep phantoms OUT OF LOGIC (danger triggers, stall detection,
    headline) while still logging every raw sensor value untouched - the
    data isn't stripped, it's just not trusted for decisions."""
    tail = key.split(":", 1)[-1].strip()
    return bool(_PHANTOM_SENSOR_RE.search(tail))


def _find_sensor(sensors, *substr):
    """First sensor value whose key contains all the given substrings
    (case-insensitive). Substring matching so it works across GPU vendors
    and LHM versions, whose exact key text varies."""
    for k, v in sensors.items():
        kl = k.lower()
        if all(s in kl for s in substr):
            return v
    return None


def _gpu_signature(sensors):
    """A tuple of the live GPU readings used to detect a driver hang: if
    these are byte-identical across consecutive polls while the poll
    clock keeps advancing, the driver has stopped updating them - the GPU
    is stalled and every value is just its last-known reading repeated.
    Substring-matched so it works on NVIDIA/AMD/Intel. Returns None if no
    GPU sensors are present."""
    vals = (_find_sensor(sensors, "load", "gpu core"),
            _find_sensor(sensors, "temperature", "gpu core"),
            _find_sensor(sensors, "temperature", "gpu hot"),
            _find_sensor(sensors, "power", "gpu"),
            _find_sensor(sensors, "clock", "gpu core"),
            _find_sensor(sensors, "voltage", "gpu core"))
    if all(v is None for v in vals):
        return None
    return vals


def _gpu_active(sensors):
    """Was the GPU doing real work (so a freeze is a hang, not just idle)?"""
    load = _find_sensor(sensors, "load", "gpu core")
    return isinstance(load, (int, float)) and load >= 10


def attempt_gpu_recovery():
    """Best-effort graphics-stack reset using SendInput for Win+Ctrl+Shift+B.
    This replaces the older keybd_event implementation because malformed or
    partially-processed synthetic modifier input can accidentally invoke
    Windows accessibility shortcuts (such as Magnifier).  Every modifier is
    released in a finally block so no synthetic key can remain stuck.
    Returns True if SendInput accepted the complete sequence."""
    try:
        import ctypes
        from ctypes import wintypes
    except Exception:
        return False

    try:
        user32 = ctypes.windll.user32
        INPUT_KEYBOARD = 1
        KEYEVENTF_KEYUP = 0x0002
        KEYEVENTF_EXTENDEDKEY = 0x0001
        VK_LWIN, VK_CONTROL, VK_SHIFT, VK_B = 0x5B, 0x11, 0x10, 0x42

        class KEYBDINPUT(ctypes.Structure):
            _fields_ = [
                ("wVk", wintypes.WORD),
                ("wScan", wintypes.WORD),
                ("dwFlags", wintypes.DWORD),
                ("time", wintypes.DWORD),
                ("dwExtraInfo", wintypes.ULONG_PTR),
            ]

        class INPUT_UNION(ctypes.Union):
            _fields_ = [("ki", KEYBDINPUT)]

        class INPUT(ctypes.Structure):
            _anonymous_ = ("u",)
            _fields_ = [("type", wintypes.DWORD), ("u", INPUT_UNION)]

        user32.SendInput.argtypes = (wintypes.UINT, ctypes.POINTER(INPUT), ctypes.c_int)
        user32.SendInput.restype = wintypes.UINT

        def make_key(vk, flags=0):
            x = INPUT()
            x.type = INPUT_KEYBOARD
            x.ki = KEYBDINPUT(vk, 0, flags, 0, 0)
            return x

        seq = [VK_LWIN, VK_CONTROL, VK_SHIFT, VK_B]
        events = (INPUT * (len(seq) * 2))()
        for i, vk in enumerate(seq):
            flags = KEYEVENTF_EXTENDEDKEY if vk == VK_LWIN else 0
            events[i] = make_key(vk, flags)
        for i, vk in enumerate(reversed(seq), len(seq)):
            flags = KEYEVENTF_KEYUP | (KEYEVENTF_EXTENDEDKEY if vk == VK_LWIN else 0)
            events[i] = make_key(vk, flags)

        sent = user32.SendInput(len(events), events, ctypes.sizeof(INPUT))
        return sent == len(events)
    except Exception:
        return False


def _gather_inventory():
    """Static machine facts, collected once per session for the log header
    - crucially the GPU driver version, so crashes can be correlated with
    driver updates (the top question for a recurring GPU-driver hang).
    Every source is best-effort; missing pieces are simply omitted."""
    inv = {"app_version": APP_VERSION}
    try:
        label = CONFIG.get("machine_label") or ""
        if not label:
            import socket
            label = socket.gethostname()
        inv["machine"] = label
    except Exception:
        pass
    try:
        import platform
        inv["os"] = platform.platform()
        inv["cpu"] = platform.processor() or None
    except Exception:
        pass
    try:
        inv["ram_total_gb"] = round(psutil.virtual_memory().total / 1024**3, 1)
    except Exception:
        pass
    try:
        inv["cpu_cores"] = "%s logical / %s physical" % (
            psutil.cpu_count(True), psutil.cpu_count(False))
    except Exception:
        pass
    # GPU name + driver version: nvidia-smi first (most reliable driver
    # string on NVIDIA), then WMI as a vendor-neutral fallback.
    try:
        out = subprocess.run(
            ["nvidia-smi", "--query-gpu=name,driver_version",
             "--format=csv,noheader"],
            capture_output=True, text=True, timeout=6,
            creationflags=CREATE_NO_WINDOW)
        if out.returncode == 0 and out.stdout.strip():
            name, _, drv = out.stdout.strip().splitlines()[0].partition(",")
            inv["gpu"] = name.strip()
            inv["gpu_driver"] = drv.strip()
    except Exception:
        pass
    if "gpu" not in inv:
        try:
            import wmi as _wmi
            for v in _wmi.WMI().Win32_VideoController():
                if getattr(v, "Name", None):
                    inv["gpu"] = v.Name
                    inv["gpu_driver"] = getattr(v, "DriverVersion", None)
                    break
        except Exception:
            pass
    try:
        import wmi as _wmi
        c = _wmi.WMI()
        for b in c.Win32_BaseBoard():
            inv["motherboard"] = " ".join(
                x for x in (getattr(b, "Manufacturer", ""),
                             getattr(b, "Product", "")) if x).strip() or None
            break
        for bios in c.Win32_BIOS():
            inv["bios"] = getattr(bios, "SMBIOSBIOSVersion", None)
            break
    except Exception:
        pass
    return inv


def _danger_from_sensors(sensors):
    """One cheap pass over a sensors dict for the two adaptive-sampling
    triggers: the hottest *real* component temperature and GPU-core load.
    Returns (max_temp_c_or_None, gpu_core_load_or_None).

    Only CPU/GPU-identified temperature sensors count toward max_temp -
    generic unconnected motherboard headers (e.g. "Temperature #4") often
    read a fixed bogus value like 104C forever, which would otherwise pin
    the app in fast mode permanently (observed in a real capture). Kept to
    a single loop because it runs every poll."""
    max_temp = None
    gpu_load = None
    _real_temp = ("cpu", "gpu", "core", "package", "tctl", "tdie")
    for k, v in sensors.items():
        if not isinstance(v, (int, float)):
            continue
        if is_phantom_sensor(k):
            continue  # never let an unconnected header drive the trigger
        kl = k.lower()
        if kl.startswith("temperature"):
            if any(t in kl for t in _real_temp):
                if max_temp is None or v > max_temp:
                    max_temp = v
        elif gpu_load is None and kl.startswith("load") and "gpu core" in kl:
            gpu_load = v
    return max_temp, gpu_load


def compute_frame_stats(frame_times_ms):
    """frame_times_ms: per-frame time between Present() calls, in ms
    (PresentMon's MsBetweenPresents column). Returns avg FPS, "1% low"
    and "0.1% low" (the standard definition: average FPS of the
    slowest 1%/0.1% of frames by frame time - not the lowest
    instantaneous FPS readings, the frames that actually took longest),
    the single highest and lowest instantaneous FPS seen this poll
    (from the shortest/longest individual frame times - these are
    single-sample extremes, noisier than the 1%/0.1% lows, which is
    exactly why both are useful together), and a stutter count: any
    frame at least FRAME_STUTTER_MULT times the window's mean, or
    FRAME_STUTTER_STDDEV standard deviations above it, whichever is
    more lenient - adjust those two constants if that doesn't match
    what you'd call a stutter on your system.

    Uses heapq.nlargest for the worst-frame slice rather than a full
    sort of every frame this poll - at high FPS with a longer poll
    interval this list can be well over a thousand entries, and only
    the worst ~1% (a handful) are ever actually used, so a full
    O(n log n) sort just to keep the first few percent is wasted work
    on every poll, for every app presenting frames, for as long as
    logging runs."""
    n = len(frame_times_ms)
    if n == 0:
        return None
    mean_ms = sum(frame_times_ms) / n
    avg_fps = round(1000.0 / mean_ms, 1) if mean_ms > 0 else 0.0

    k_1pct = max(1, int(n * 0.01))
    k_01pct = max(1, int(n * 0.001))
    worst = heapq.nlargest(k_1pct, frame_times_ms)  # descending; k_01pct <= k_1pct always
    shortest_frametime = min(frame_times_ms)  # plain min() is enough for a single value

    def low_fps(worst_slice):
        avg = sum(worst_slice) / len(worst_slice)
        return round(1000.0 / avg, 1) if avg > 0 else 0.0

    variance = sum((t - mean_ms) ** 2 for t in frame_times_ms) / n
    stdev = variance ** 0.5
    stutter_threshold = max(mean_ms * FRAME_STUTTER_MULT, mean_ms + FRAME_STUTTER_STDDEV * stdev)
    stutters = sum(1 for t in frame_times_ms if t > stutter_threshold)

    return {
        "frame_count": n,
        "avg_fps": avg_fps,
        "low_1pct_fps": low_fps(worst[:k_1pct]),
        "low_01pct_fps": low_fps(worst[:k_01pct]),
        "min_fps": round(1000.0 / worst[0], 1) if worst[0] > 0 else 0.0,
        "max_fps": round(1000.0 / shortest_frametime, 1) if shortest_frametime > 0 else 0.0,
        "stutter_count": stutters,
        "max_frametime_ms": round(worst[0], 2),
    }


class PresentMonWatcher:
    """Shells out to PresentMon (github.com/GameTechDev/PresentMon) - a
    separate, free, open-source tool, not bundled here, same pattern as
    LibreHardwareMonitor - to capture real per-frame timing for every
    process currently presenting 3D frames, i.e. whatever games/GPU
    apps are actually running. It may elevate itself to Administrator
    to create its capture session (--restart_as_admin) - that's
    PresentMon's own UAC prompt, not this app's, and it's the part
    that's hardest to test outside a real Windows session, so if the
    capture doesn't start, check that PresentMon runs fine on its own
    first.

    The raw capture CSV is periodically wiped and restarted once it
    passes MAX_CSV_BYTES - unlike this app's own JSONL logs, PresentMon
    itself never rotates or caps this file, and it's pure scratch data
    once we've parsed each poll's new frames into our own (properly
    capped) logs, so there's no reason to let it grow forever."""

    # Each rotation is a full stop + orphan-sweep + delete + relaunch, which
    # re-initializes PresentMon's ETW session - a brief hitch. At high FPS a
    # 20MB cap was hit roughly every ~11 min, so games got a periodic stutter.
    # We only ever read NEW bytes (incremental _pos tracking), so a larger
    # scratch file costs nothing but disk and pushes rotations hours apart.
    MAX_CSV_BYTES = 128 * 1024 * 1024

    def __init__(self, exe_path, work_dir):
        self.available = False
        self.proc = None
        self.exe_path = exe_path
        self.csv_path = os.path.join(work_dir, "_presentmon_capture.csv")
        self._pos = 0
        self._header = None
        self._app_idx = None
        self._ft_idx = None
        self.column_error = None      # surfaced when the CSV header isn't recognized
        self.launch_error = None      # surfaced when PresentMon fails to start
        self._just_rotated = False    # #21: set on rotation so the poll loop marks the gap
        self._priority_lowered = False
        self._launch_checked = True   # only meaningful once _start sets it False
        self._stderr_path = None
        self._stderr_fh = None
        if exe_path and os.path.exists(exe_path):
            self._start(exe_path)

    def _start(self, exe_path):
        try:
            os.makedirs(os.path.dirname(self.csv_path), exist_ok=True)
            # PresentMon writes any startup/argument error to stderr then
            # exits. Sending stderr to DEVNULL (as before) meant a rejected
            # flag looked identical to "no frames" - the app just silently
            # never got data. Capture it to a file so failures are visible
            # and surfaced (see the immediate-exit check + launch_error).
            self._stderr_path = os.path.join(
                os.path.dirname(self.csv_path), "_presentmon_stderr.log")
            self._stderr_fh = open(self._stderr_path, "w", encoding="utf-8")
            # NOTE: '--v2_metrics' was removed here. In PresentMon 2.x the v2
            # metrics ARE the default, and there is no such flag - passing it
            # makes PresentMon reject the command line and exit immediately,
            # which is the most likely reason capture "wasn't working" at all.
            # (Left as a comment rather than deleted, per keep-history rule.)
            cmd = [exe_path, "--output_file", self.csv_path,
                   "--stop_existing_session",
                   # "--v2_metrics",   # invalid in PresentMon 2.x (default) - see note above
                   "--no_console_stats", "--restart_as_admin"]
            self.proc = subprocess.Popen(
                cmd, stdout=subprocess.DEVNULL, stderr=self._stderr_fh,
                creationflags=CREATE_NO_WINDOW)
            self.available = True
            self._pos = 0
            self._header = None
            self._app_idx = None
            self._ft_idx = None
            self.column_error = None
            self.launch_error = None
            self._priority_lowered = False  # re-lower the new process on next poll
            self._launch_checked = False    # verify it didn't instantly die (next poll)
            self._launch_time = time.time()
        except Exception as e:
            self.available = False
            self.launch_error = str(e)

    def _check_launch(self):
        """Called once shortly after start: if PresentMon already exited,
        it rejected the command line or failed - read its stderr and
        surface why, instead of silently reporting no frames. Skipped when
        --restart_as_admin legitimately replaced the original process (a
        same-exe instance is still running)."""
        self._launch_checked = True
        if self.proc is None or self.proc.poll() is None:
            return  # still running via this handle - fine
        if self.is_actually_running():
            return  # original handle exited but a re-elevated instance runs
        detail = ""
        try:
            with open(self._stderr_path, "r", encoding="utf-8", errors="ignore") as f:
                detail = f.read().strip().replace("\n", " ")[:200]
        except Exception:
            pass
        self.launch_error = ("PresentMon exited immediately after launch"
                             + (" - " + detail if detail else "")
                             + ". Check the exe version/flags.")
        self.available = False

    def _restart_fresh(self):
        """Stops PresentMon, clears the capture file, and relaunches -
        only ever needs forward data, so a clean restart is fine.

        Also sweeps for and stops ANY process actually running this
        exact exe, not just the one handle self.proc happens to hold:
        --restart_as_admin (used at launch) can make PresentMon
        replace itself with a new, separately-elevated process the
        moment it starts, if it wasn't already elevated - and that
        replacement, not the original handle, is what's actually still
        writing the CSV file about to be deleted below. Terminating
        only the original would leave the replacement running right
        through the delete, which would likely just fail outright on
        Windows (can't delete a file another process still has open),
        and leave an orphaned PresentMon instance this app has lost
        track of even on the rare chance the delete didn't fail.

        This sweep runs on rotation (every ~20MB, not on the hot poll
        path), not on final shutdown - stop() alone stays fast there,
        since that path has its own tight timing budget this doesn't
        need to compete with."""
        self.stop()
        self._stop_orphaned_instances()
        try:
            if os.path.exists(self.csv_path):
                os.remove(self.csv_path)
        except OSError:
            pass
        if self.exe_path:
            self._start(self.exe_path)
        # #21: signal that a capture gap just occurred (teardown + relaunch),
        # so the poll loop can log an explicit marker instead of leaving an
        # unexplained blank in the frame data that could look like the game
        # stopping.
        self._just_rotated = True

    def _stop_orphaned_instances(self):
        if psutil is None or not self.exe_path:
            return
        target_exe = self.exe_path.lower()
        matches = []
        try:
            for p in psutil.process_iter(["exe"]):
                try:
                    if (p.info.get("exe") or "").lower() == target_exe:
                        matches.append(p)
                except (psutil.NoSuchProcess, psutil.AccessDenied):
                    continue
        except Exception:
            return
        for p in matches:
            try:
                p.terminate()
            except Exception:
                pass
        if matches:
            try:
                psutil.wait_procs(matches, timeout=1)
            except Exception:
                pass

    def _lower_capture_priority(self):
        """Drop PresentMon to below-normal priority so it yields CPU to
        the game instead of competing with it at normal priority - the
        capture only has to keep up with frame events, it doesn't need
        to race the very thing it's measuring. This is the main fix for
        "PresentMon takes performance away from games."

        Swept by exact exe path rather than just self.proc, because
        --restart_as_admin can replace the original with a separately-
        elevated process, and only that replacement is the real
        capturer. Best-effort and one-shot per capture lifetime (see the
        _priority_lowered gate in poll_new_frames): if this app isn't
        elevated while PresentMon is, the nice() call hits AccessDenied
        across the integrity boundary and is harmlessly skipped."""
        if psutil is None or not self.exe_path:
            return
        below = getattr(psutil, "BELOW_NORMAL_PRIORITY_CLASS", None)
        if below is None:
            return
        target_exe = self.exe_path.lower()
        try:
            for p in psutil.process_iter(["exe"]):
                try:
                    if (p.info.get("exe") or "").lower() == target_exe:
                        p.nice(below)
                except (psutil.NoSuchProcess, psutil.AccessDenied):
                    continue
        except Exception:
            pass

    # Frame-time (present-interval) column, in preference order. PresentMon
    # has renamed/re-cased columns across versions and metric modes; matching
    # a known set (case-insensitively) rather than one hard-coded name means a
    # header change degrades to a *visible* warning (column_error) instead of
    # silently dropping every frame - the likeliest cause of "FPS half-works."
    _FT_COLUMN_ALIASES = ("msbetweenpresents", "msbetweendisplaychange")
    _APP_COLUMN_ALIASES = ("application", "processname", "process")

    def _resolve_columns(self, header):
        lower = [h.strip().lower() for h in header]

        def find(aliases):
            for alias in aliases:
                if alias in lower:
                    return lower.index(alias)
            return None

        self._app_idx = find(self._APP_COLUMN_ALIASES)
        self._ft_idx = find(self._FT_COLUMN_ALIASES)
        if self._app_idx is None or self._ft_idx is None:
            missing = []
            if self._app_idx is None:
                missing.append("application/process name")
            if self._ft_idx is None:
                missing.append("frame time (MsBetweenPresents)")
            self.column_error = (
                "PresentMon CSV columns not recognized - missing "
                + " and ".join(missing)
                + ". Header was: " + ", ".join(header[:12])
                + (" ..." if len(header) > 12 else ""))
        else:
            self.column_error = None

    def is_actually_running(self):
        """Whether PresentMon is genuinely running right now - checks
        the specific handle this app spawned first (cheap, no process
        enumeration needed), but falls back to matching by exact exe
        path across all running processes if that handle looks dead.
        That fallback matters: --restart_as_admin can replace the
        original process with a new, separately-elevated one the
        moment PresentMon starts (if it wasn't already elevated), and
        the original handle then shows as exited even though the
        actual capture is still running fine under the replacement -
        checking only self.proc would misreport that as 'not
        running'."""
        if self.proc is not None and self.proc.poll() is None:
            return True
        if psutil is None or not self.exe_path:
            return False
        target_exe = self.exe_path.lower()
        try:
            for p in psutil.process_iter(["exe"]):
                try:
                    if (p.info.get("exe") or "").lower() == target_exe:
                        return True
                except (psutil.NoSuchProcess, psutil.AccessDenied):
                    continue
        except Exception:
            pass
        return False

    def poll_new_frames(self):
        """Returns {process_name: [frametime_ms, ...]} for whole lines
        appended to the capture CSV since the last call. Byte-exact
        position tracking so a line PresentMon hasn't finished writing
        yet is left for the next poll instead of being misparsed."""
        # Verify launch shortly after starting: if PresentMon rejected its
        # flags and died, there'll be no CSV and this would otherwise just
        # look like "no frames" forever - _check_launch surfaces the real
        # reason instead. Runs once, ~one poll after start.
        if not self._launch_checked and time.time() - getattr(self, "_launch_time", 0) >= 0.5:
            self._check_launch()
        if not self.available or not os.path.exists(self.csv_path):
            return {}
        # One-shot per capture lifetime: yield CPU to the game. Done here (a
        # poll or two after launch) rather than in _start, so the possibly
        # re-elevated --restart_as_admin replacement process already exists.
        if not self._priority_lowered:
            self._lower_capture_priority()
            self._priority_lowered = True
        out = {}
        try:
            # #40: if the capture file shrank below our read cursor, it was
            # truncated or replaced out from under us (e.g. PresentMon restarted
            # itself, or an external tool cleared it). Re-read from the top and
            # re-detect the header instead of seeking past the end and reading
            # nothing forever.
            try:
                if os.path.getsize(self.csv_path) < self._pos:
                    self._pos = 0
                    self._header = None
                    self._app_idx = None
                    self._ft_idx = None
            except OSError:
                pass
            with open(self.csv_path, "rb") as f:
                f.seek(self._pos)
                chunk = f.read()
            if chunk:
                last_nl = chunk.rfind(b"\n")
                if last_nl != -1:
                    complete = chunk[:last_nl + 1]
                    self._pos += len(complete)
                    text = complete.decode("utf-8", errors="ignore")
                    # one csv.reader over the whole batch, not one
                    # constructed per line - this runs every poll and at
                    # high FPS with a longer poll interval that can be
                    # hundreds of lines, so hundreds of reader objects
                    # instead of one adds up over a long session
                    for row in csv.reader(text.splitlines()):
                        if not row:
                            continue
                        if self._header is None:
                            self._header = row
                            self._resolve_columns(row)
                            continue
                        if self._app_idx is None or self._ft_idx is None:
                            continue  # header unrecognized; column_error is set
                        if len(row) != len(self._header):
                            continue
                        app = row[self._app_idx]
                        ft = row[self._ft_idx]
                        if not app or not ft:
                            continue
                        try:
                            ft = float(ft)
                        except ValueError:
                            continue
                        if ft <= 0:
                            continue
                        out.setdefault(app, []).append(ft)
        except Exception:
            pass

        try:
            if os.path.getsize(self.csv_path) > self.MAX_CSV_BYTES:
                self._restart_fresh()
        except OSError:
            pass
        return out

    def stop(self):
        """terminate() alone doesn't confirm the process actually died -
        on a long session this gets called on every rotation (every
        ~20MB of capture, which for a lot of gaming could be several
        times a session), so waiting briefly avoids relying on garbage
        collection timing to release each one's process handle. Kept
        short (not a multi-second wait+kill fallback): Windows'
        TerminateProcess is already forceful, not a cooperative signal
        a process can delay responding to, and this needs to comfortably
        fit inside the 2s join() budget used when stopping/restarting
        logging - a long wait here would eat into that and reopen the
        exact race that fix was for."""
        if self.proc:
            try:
                self.proc.terminate()
                self.proc.wait(timeout=1)
            except Exception:
                pass
            self.proc = None


# ------------------------------------------------------- tool acquisition --
# Locating and downloading LibreHardwareMonitor / PresentMon. "Download"
# here means exactly that - fetching a file over HTTPS from the official
# GitHub repo, nothing more. Neither tool needs a traditional installer:
# LibreHardwareMonitor is a portable ZIP (extract, run the exe inside),
# and PresentMon's console app is a standalone exe you invoke directly.
# Actually *running* LibreHardwareMonitor with full sensor access still
# goes through Windows' own UAC elevation prompt - that's the real
# consent gate for anything privileged, and nothing here tries to work
# around it. Only the two official repos are ever used, on purpose -
# LibreHardwareMonitor's own README specifically warns that
# librehardwaremonitor.com is NOT them and should be avoided.

LHM_REPO = "LibreHardwareMonitor/LibreHardwareMonitor"
PRESENTMON_REPO = "GameTechDev/PresentMon"
LHM_ASSET_RE = re.compile(r"^LibreHardwareMonitor.*\.zip$", re.IGNORECASE)
PRESENTMON_ASSET_RE = re.compile(r"^PresentMon-[\d.]+-x64\.exe$", re.IGNORECASE)


def _github_latest_release(repo):
    url = f"https://api.github.com/repos/{repo}/releases/latest"
    req = urllib.request.Request(url, headers={
        "User-Agent": "PCMonitor", "Accept": "application/vnd.github+json"})
    with urllib.request.urlopen(req, timeout=15) as resp:
        return json.loads(resp.read().decode("utf-8"))


def _pick_asset(release_json, pattern):
    """Only looks at the release's actual uploaded assets - never the
    zipball_url/tarball_url GitHub auto-generates for "Source code",
    which live outside the assets list entirely."""
    for asset in release_json.get("assets", []):
        name = asset.get("name", "")
        if pattern.search(name):
            return name, asset.get("browser_download_url")
    return None, None


def _download_file(url, dest_path):
    req = urllib.request.Request(url, headers={"User-Agent": "PCMonitor"})
    with urllib.request.urlopen(req, timeout=60) as resp, open(dest_path, "wb") as out:
        while True:
            chunk = resp.read(65536)
            if not chunk:
                break
            out.write(chunk)
    return dest_path


def _safe_extract(zip_path, extract_dir):
    """Extracts while refusing any entry that would land outside
    extract_dir (zip-slip protection) - cheap insurance even for a
    trusted official release."""
    with zipfile.ZipFile(zip_path, "r") as zf:
        for member in zf.namelist():
            dest = os.path.realpath(os.path.join(extract_dir, member))
            if not dest.startswith(os.path.realpath(extract_dir) + os.sep):
                raise ValueError(f"Unsafe path in zip: {member}")
        zf.extractall(extract_dir)


def locate_lhm():
    """Checks common install locations for an existing copy before ever
    downloading anything."""
    patterns = [
        os.path.join(TOOLS_DIR, "LibreHardwareMonitor", "**", "LibreHardwareMonitor.exe"),
        os.path.join(os.environ.get("ProgramFiles", r"C:\Program Files"),
                      "LibreHardwareMonitor", "LibreHardwareMonitor.exe"),
        os.path.join(os.environ.get("ProgramFiles(x86)", r"C:\Program Files (x86)"),
                      "LibreHardwareMonitor", "LibreHardwareMonitor.exe"),
        os.path.join(os.environ.get("LOCALAPPDATA", ""), "**", "LibreHardwareMonitor.exe"),
    ]
    for p in patterns:
        matches = glob.glob(p, recursive=True)
        if matches:
            return matches[0]
    return None


def locate_presentmon():
    patterns = [
        os.path.join(TOOLS_DIR, "PresentMon*.exe"),
        os.path.join(os.environ.get("ProgramFiles", r"C:\Program Files"),
                      "PresentMon", "PresentMon*.exe"),
        os.path.join(os.environ.get("LOCALAPPDATA", ""), "**", "PresentMon-*-x64.exe"),
    ]
    for p in patterns:
        matches = glob.glob(p, recursive=True)
        if matches:
            return matches[0]
    return None


def fetch_and_install_lhm(tools_dir=None):
    """Downloads the official LibreHardwareMonitor release zip and
    extracts it. Returns the path to LibreHardwareMonitor.exe, or None
    on any failure (network, parsing, missing asset, bad zip) - callers
    should treat None as "fall back to the manual download link"."""
    tools_dir = tools_dir or TOOLS_DIR
    try:
        rel = _github_latest_release(LHM_REPO)
        name, url = _pick_asset(rel, LHM_ASSET_RE)
        if not url:
            return None
        os.makedirs(tools_dir, exist_ok=True)
        zip_path = os.path.join(tools_dir, name)
        _download_file(url, zip_path)
        extract_dir = os.path.join(tools_dir, "LibreHardwareMonitor")
        _safe_extract(zip_path, extract_dir)
        os.remove(zip_path)
        for root, _, files in os.walk(extract_dir):
            for fn in files:
                if fn.lower() == "librehardwaremonitor.exe":
                    return os.path.join(root, fn)
        return None
    except Exception:
        return None


def fetch_presentmon(tools_dir=None):
    """Downloads the official PresentMon console exe directly - it's a
    standalone tool, not an installer, so there's no separate install
    step. Returns its path, or None on failure."""
    tools_dir = tools_dir or TOOLS_DIR
    try:
        rel = _github_latest_release(PRESENTMON_REPO)
        name, url = _pick_asset(rel, PRESENTMON_ASSET_RE)
        if not url:
            return None
        os.makedirs(tools_dir, exist_ok=True)
        exe_path = os.path.join(tools_dir, name)
        _download_file(url, exe_path)
        return exe_path
    except Exception:
        return None


LHM_CONFIG_KEYS = ("runWebServerMenuItem", "minTrayMenuItem", "minCloseMenuItem")


def patch_lhm_config(lhm_exe_path):
    """Best-effort: flips a few known settings to enabled in
    LibreHardwareMonitor's own config file - Remote Web Server (what
    this app reads sensors from), Minimize to Tray, and minimize
    (rather than exit) on close, which is the actual root cause fix
    for closing the window ending sensor data entirely.

    The key="X" value="Y" format and these three exact key names are
    confirmed via two independent, real, working automation scripts
    (a NuGet package's docs and a separate GitHub PowerShell module's
    docs) that both do exactly this for exactly this purpose - not a
    guess. What's NOT independently confirmed is the file's overall
    structure, so this only ever does a literal string replace on a
    file that already exists with the expected pattern already in it;
    it never fabricates a config file from scratch. That means it's a
    no-op on the very first-ever launch (before LibreHardwareMonitor
    has saved any settings at all) and starts actually helping from
    the second launch onward, once a real file exists to patch.

    Returns True if, after this call, the file confirms all three
    settings are enabled - whether they needed changing just now or
    were already set from a previous run. This matters: a caller using
    the return value to decide "is it safe to hide this window
    automatically" needs "is everything actually on", not "did I
    personally just flip something" - otherwise re-running setup after
    it's already fully configured would wrongly look like a fresh
    first-time launch again. Returns False whenever that can't be
    confirmed: no config file yet, an unreadable/unrecognized file, or
    only some of the three keys present - conservative on purpose,
    since the caller falls back to showing the window for manual
    setup/verification in that case, never to silently hiding it."""
    config_path = os.path.join(os.path.dirname(lhm_exe_path), "LibreHardwareMonitor.config")
    if not os.path.exists(config_path):
        return False
    try:
        with open(config_path, "r", encoding="utf-8") as f:
            text = f.read()
    except Exception:
        return False

    changed = False
    for key in LHM_CONFIG_KEYS:
        for old_val in ("false", "False"):
            old = f'key="{key}" value="{old_val}"'
            if old in text:
                text = text.replace(old, f'key="{key}" value="true"')
                changed = True

    if changed:
        try:
            with open(config_path, "w", encoding="utf-8") as f:
                f.write(text)
        except Exception:
            return False

    return all(f'key="{key}" value="true"' in text for key in LHM_CONFIG_KEYS)


def launch_elevated(path, minimized=False):
    """Asks Windows to launch path with Administrator rights - this is
    what actually shows the user the UAC prompt; nothing here bypasses
    or pre-answers it. minimized=True requests a minimized initial
    window (SW_SHOWMINNOACTIVE) as a best-effort hint - in practice
    LibreHardwareMonitor ignores this and shows its window normally
    regardless, so hide_window_when_ready() below is the actual fix
    for that, not this flag."""
    import ctypes
    show_cmd = 7 if minimized else 1  # SW_SHOWMINNOACTIVE : SW_SHOWNORMAL
    ctypes.windll.shell32.ShellExecuteW(
        None, "runas", path, None, os.path.dirname(path), show_cmd)


def hide_window_when_ready(title_substring, timeout=15, poll_interval=0.5):
    """Waits for a top-level window whose title contains title_substring
    to appear, then hides it outright (SW_HIDE, not just minimize).

    This exists because LibreHardwareMonitor ignores the
    SW_SHOWMINNOACTIVE launch hint above and just shows its window
    normally - and a visible, easy-to-mistake-for-clutter window is
    exactly what leads to someone closing it, which by default fully
    exits LibreHardwareMonitor (not minimize-to-tray, unless its own
    separate "Minimize to tray" option is enabled) and takes the whole
    sensor connection down with it. Hiding it outright removes that
    risk instead of hoping it doesn't happen. Doesn't touch any of
    LibreHardwareMonitor's own settings or files - this only ever
    calls a standard Win32 window API on a window it doesn't own.

    Blocks for up to `timeout` seconds while polling, so call this
    from a background thread, never the GUI thread. Returns True if a
    matching window was found and hidden, False otherwise (window
    never appeared, or win32gui isn't available)."""
    try:
        import win32con
        import win32gui
    except ImportError:
        return False

    deadline = time.time() + timeout
    found = []

    def _enum(hwnd, _):
        if win32gui.IsWindowVisible(hwnd) and title_substring.lower() in win32gui.GetWindowText(hwnd).lower():
            found.append(hwnd)
        return True

    while time.time() < deadline:
        found.clear()
        try:
            win32gui.EnumWindows(_enum, None)
        except Exception:
            return False
        if found:
            try:
                win32gui.ShowWindow(found[0], win32con.SW_HIDE)
                return True
            except Exception:
                return False
        time.sleep(poll_interval)
    return False


def read_system_stats(proc_monitor, net_monitor, cached_cpu_counts=None, cached_boot_time=None):
    """Everything psutil can reach, organized into clean nested groups
    rather than one flat pile of keys - both for readability in the
    log file and so the GUI/history code can pull sections cleanly.

    cached_cpu_counts and cached_boot_time let a caller that polls
    repeatedly (PollThread) pass in values it already computed once -
    core count and boot time can't change during a running session
    without a reboot, which would kill this process anyway, so
    re-querying psutil for them on every single poll is pure waste.
    Left as optional so a one-off caller (tests, scripts) can still
    just call this directly and get correct, freshly-computed values."""
    # #6: total and per-core must come from ONE sample interval. Two separate
    # cpu_percent(interval=None) calls back-to-back measure different (and for
    # the second, near-zero) windows, so they wouldn't correspond. Take the
    # per-core reading once and derive the total from it - one interval, and
    # total == mean(per-core) by construction.
    cpu = {}
    try:
        per_core = psutil.cpu_percent(interval=None, percpu=True)
        if per_core:
            cpu["percent_per_core"] = per_core
            cpu["percent"] = round(sum(per_core) / len(per_core), 1)
        else:
            cpu["percent"] = psutil.cpu_percent(interval=None)
    except Exception:
        try:
            cpu["percent"] = psutil.cpu_percent(interval=None)
        except Exception:
            cpu["percent"] = None
    if cached_cpu_counts is not None:
        cpu["count_logical"], cpu["count_physical"] = cached_cpu_counts
    else:
        try:
            cpu["count_logical"] = psutil.cpu_count(logical=True)
            cpu["count_physical"] = psutil.cpu_count(logical=False)
        except Exception:
            pass
    try:
        freq = psutil.cpu_freq()
        if freq:
            cpu["freq_mhz"] = round(freq.current, 1)
    except Exception:
        pass

    m = psutil.virtual_memory()
    memory = {
        "percent": m.percent,
        "used_gb": round(m.used / 1024**3, 2),
        "available_gb": round(m.available / 1024**3, 2),
        "total_gb": round(m.total / 1024**3, 2),
    }
    try:
        sw = psutil.swap_memory()
        memory["swap_percent"] = sw.percent
        memory["swap_used_gb"] = round(sw.used / 1024**3, 2)
    except Exception:
        pass

    disk = {}
    try:
        du = psutil.disk_usage(os.path.abspath(os.sep))
        disk["system_percent"] = du.percent
        disk["system_free_gb"] = round(du.free / 1024**3, 2)
    except Exception:
        pass
    try:
        io = psutil.disk_io_counters()
        if io:
            disk["read_gb_total"] = round(io.read_bytes / 1024**3, 2)
            disk["write_gb_total"] = round(io.write_bytes / 1024**3, 2)
    except Exception:
        pass

    system = {}
    try:
        boot = cached_boot_time if cached_boot_time is not None else psutil.boot_time()
        system["boot_time"] = datetime.fromtimestamp(boot).isoformat(timespec="seconds")
        system["uptime_hours"] = round((time.time() - boot) / 3600, 2)
    except Exception:
        pass

    battery = None
    try:
        b = psutil.sensors_battery()
        if b:
            battery = {"percent": b.percent, "plugged": b.power_plugged}
    except Exception:
        pass

    processes = {}
    try:
        top_cpu, top_mem = proc_monitor.top()
        processes["top_cpu"] = top_cpu
        processes["top_mem"] = top_mem
    except Exception:
        pass

    network = net_monitor.sample()
    foreground = get_foreground_app()

    row = {"cpu": cpu, "memory": memory, "disk": disk, "system": system,
           "processes": processes, "network": network}
    if battery:
        row["battery"] = battery
    if foreground:
        row["foreground"] = foreground
    return row


def find_metric(sensors, keywords, type_prefix=None):
    """Best-effort lookup within a sensors dict: first key containing
    all keywords (case-insensitive), optionally restricted to a type
    prefix like 'Temperature'. Used for one-off lookups; headline()
    below extracts its whole set of metrics in a single pass instead
    of calling this repeatedly - see _extract_sensor_headline."""
    for k, v in sensors.items():
        if not isinstance(k, str):
            continue
        kl = k.lower()
        if type_prefix and not kl.startswith(type_prefix.lower()):
            continue
        if all(kw in kl for kw in keywords):
            return v
    return None


def _extract_sensor_headline(sensors):
    """Pulls every headline sensor metric (CPU/GPU temp, clock, power,
    voltage, load) out of a sensors dict in a single pass, instead of
    scanning the whole dict from scratch once per metric via repeated
    find_metric() calls (up to 18 full scans per row, chaining primary
    + fallback keyword matches for 9 metrics). headline() runs on
    every live poll *and* on every row of a History load - for "All
    time" on a well-populated motherboard, rows x sensors x ~18 scans
    adds up to a genuinely large amount of redundant string work; this
    is the same one pass either way.

    Also fixes a real bug the old chained-`or` version had: `A or B`
    treats 0 / 0.0 as "not found" and falls through to B, so a GPU
    genuinely idling at 0% load or drawing 0W would have silently
    shown the broader fallback's value instead of the correct 0. This
    checks `is not None` instead, so a real zero reading stays zero."""
    cpu_temp = cpu_temp_fb = None
    gpu_temp = gpu_temp_fb = None
    cpu_clock = cpu_clock_fb = None
    cpu_power = cpu_power_fb = None
    gpu_clock = gpu_clock_fb = None
    gpu_mem_clock = None
    gpu_power = gpu_power_fb1 = gpu_power_fb2 = None
    gpu_voltage = gpu_voltage_fb = None
    gpu_load = gpu_load_fb = None

    for k, v in sensors.items():
        if not isinstance(k, str):
            continue
        kl = k.lower()
        is_gpu_named = "gpu" in kl
        if kl.startswith("temperature"):
            if cpu_temp is None and not is_gpu_named and "package" in kl:
                cpu_temp = v
            if cpu_temp_fb is None and not is_gpu_named and (
                    "cpu" in kl or "core" in kl or "tctl" in kl or "tdie" in kl):
                cpu_temp_fb = v
            if gpu_temp is None and "gpu core" in kl:
                gpu_temp = v
            if gpu_temp_fb is None and is_gpu_named:
                gpu_temp_fb = v
        elif kl.startswith("clock"):
            if cpu_clock is None and not is_gpu_named and (
                    "cpu core #1" in kl or "core #1" in kl):
                cpu_clock = v
            if cpu_clock_fb is None and not is_gpu_named and "cpu" in kl:
                cpu_clock_fb = v
            if gpu_clock is None and "gpu core" in kl:
                gpu_clock = v
            if gpu_clock_fb is None and is_gpu_named:
                gpu_clock_fb = v
            if gpu_mem_clock is None and "gpu memory" in kl:
                gpu_mem_clock = v
        elif kl.startswith("power"):
            if cpu_power is None and not is_gpu_named and "package" in kl:
                cpu_power = v
            if cpu_power_fb is None and not is_gpu_named and "cpu" in kl:
                cpu_power_fb = v
            if gpu_power is None and "gpu package" in kl:
                gpu_power = v
            if gpu_power_fb1 is None and "gpu power" in kl:
                gpu_power_fb1 = v
            if gpu_power_fb2 is None and is_gpu_named:
                gpu_power_fb2 = v
        elif kl.startswith("voltage"):
            if gpu_voltage is None and "gpu core" in kl:
                gpu_voltage = v
            if gpu_voltage_fb is None and "gpu" in kl:
                gpu_voltage_fb = v
        elif kl.startswith("load"):
            if gpu_load is None and "gpu core" in kl:
                gpu_load = v
            if gpu_load_fb is None and "gpu" in kl:
                gpu_load_fb = v

    return {
        "cpu_temp": cpu_temp if cpu_temp is not None else cpu_temp_fb,
        "gpu_temp": gpu_temp if gpu_temp is not None else gpu_temp_fb,
        "cpu_clock": cpu_clock if cpu_clock is not None else cpu_clock_fb,
        "cpu_power": cpu_power if cpu_power is not None else cpu_power_fb,
        "gpu_clock": gpu_clock if gpu_clock is not None else gpu_clock_fb,
        "gpu_mem_clock": gpu_mem_clock,
        "gpu_power": gpu_power if gpu_power is not None else (
            gpu_power_fb1 if gpu_power_fb1 is not None else gpu_power_fb2),
        "gpu_voltage": gpu_voltage if gpu_voltage is not None else gpu_voltage_fb,
        "gpu_load": gpu_load if gpu_load is not None else gpu_load_fb,
    }


def headline(row):
    """Curated subset used by both the Live cards and History table.
    Sensor names vary by motherboard/GPU - this is a best-effort match;
    the Live tab's raw table always shows everything actually found."""
    sensors = row.get("sensors", {})
    cpu = row.get("cpu", {})
    memory = row.get("memory", {})
    network = row.get("network", {})
    frames = row.get("frames", {})
    fg = row.get("foreground") or {}
    fg_stats = frames.get(fg.get("process")) if fg.get("process") else None
    s = _extract_sensor_headline(sensors)
    return {
        "ts": row.get("ts"),
        "cpu_temp": s["cpu_temp"],
        "gpu_temp": s["gpu_temp"],
        "cpu_clock": s["cpu_clock"],
        "cpu_power": s["cpu_power"],
        "gpu_clock": s["gpu_clock"],
        "gpu_mem_clock": s["gpu_mem_clock"],
        "gpu_power": s["gpu_power"],
        "gpu_voltage": s["gpu_voltage"],
        "gpu_load": s["gpu_load"],
        "mem_percent": memory.get("percent"),
        "cpu_percent": cpu.get("percent"),
        "ping_ms": network.get("ping_ms"),
        "ping_loss": network.get("ping_loss_percent"),
        "fg_fps": fg_stats["avg_fps"] if fg_stats else None,
        "fg_low1": fg_stats["low_1pct_fps"] if fg_stats else None,
        "foreground": fg.get("process"),
    }


def fmt_sysinfo(row):
    parts = []
    system = row.get("system", {})
    memory = row.get("memory", {})
    disk = row.get("disk", {})
    battery = row.get("battery")
    fg = row.get("foreground")
    if system.get("uptime_hours") is not None:
        parts.append(f"Uptime: {system['uptime_hours']}h")
    if memory.get("swap_percent") is not None:
        parts.append(f"Swap: {memory['swap_percent']}%")
    if disk.get("system_percent") is not None:
        parts.append(f"Disk: {disk['system_percent']}% used, "
                      f"{disk.get('system_free_gb')} GB free")
    if battery:
        plugged = "plugged" if battery.get("plugged") else "on battery"
        parts.append(f"Battery: {battery.get('percent')}% ({plugged})")
    if fg and fg.get("process"):
        parts.append(f"Active window: {fg['process']}")
    return "   |   ".join(parts)


# --------------------------------------------------------------- startup --

def _startup_command(script_path=None):
    if getattr(sys, "frozen", False):
        return f'"{sys.executable}"'
    exe = find_pythonw()
    script = script_path or os.path.abspath(__file__)
    return f'"{exe}" "{script}"'


def _schtasks_query(task_name):
    """Returns True if a scheduled task with this name currently
    exists. The query itself needs no elevation, regardless of the
    task's own configured privilege level."""
    try:
        result = subprocess.run(
            ["schtasks", "/query", "/tn", task_name],
            capture_output=True, text=True, creationflags=CREATE_NO_WINDOW)
        return result.returncode == 0
    except Exception:
        return False


def _create_scheduled_task(task_name, command):
    """command is the full '"exe" "script"' string _startup_command()
    builds - schtasks wants the program and its argument passed
    together as one /tr value when both are quoted like this.
    Creating a task with /rl highest generally needs an elevated
    creating process - since this app now auto-elevates on every
    launch (see the entry point), that requirement is normally already
    satisfied by the time someone toggles this checkbox, with no
    separate prompt of its own."""
    try:
        result = subprocess.run(
            ["schtasks", "/create", "/tn", task_name, "/tr", command,
             "/sc", "onlogon", "/rl", "highest", "/f"],
            capture_output=True, text=True, creationflags=CREATE_NO_WINDOW)
        return result.returncode == 0
    except Exception:
        return False


def _delete_scheduled_task(task_name):
    try:
        subprocess.run(["schtasks", "/delete", "/tn", task_name, "/f"],
                         capture_output=True, text=True, creationflags=CREATE_NO_WINDOW)
    except Exception:
        pass


def _delete_startup_registry_entry():
    """Cleans up the older HKCU Run key entry this app used before
    switching to Task Scheduler - relevant for anyone upgrading from a
    version that used it, so toggling the checkbox off actually turns
    off whichever mechanism happens to be active for them, not just
    the new one."""
    if not HAVE_WINREG:
        return
    try:
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, RUN_KEY, 0, winreg.KEY_SET_VALUE) as key:
            try:
                winreg.DeleteValue(key, APP_REG_NAME)
            except FileNotFoundError:
                pass
    except OSError:
        pass


def is_startup_enabled():
    if _schtasks_query(APP_REG_NAME):
        return True
    # backward compat: someone who enabled this before the switch to
    # Task Scheduler might still only have the old registry entry
    if not HAVE_WINREG:
        return False
    try:
        with winreg.OpenKey(winreg.HKEY_CURRENT_USER, RUN_KEY, 0, winreg.KEY_READ) as key:
            winreg.QueryValueEx(key, APP_REG_NAME)
        return True
    except OSError:
        return False


def set_startup_enabled(enabled, script_path=None):
    """Uses Task Scheduler (schtasks.exe) with a logon trigger and
    "Run with highest privileges" (/rl highest) rather than the
    simpler HKCU Run registry key this app used before - the Run key
    approach means Windows shows a fresh UAC prompt EVERY time it
    fires if the launched program then tries to elevate itself, which
    this app now always does on startup (see the auto-elevate entry
    point logic): a plain Run-key launch has no way to carry "this
    should already be elevated" information through to Windows. A
    Task Scheduler task configured with RunLevel=Highest gets its
    one-time admin consent baked in at CREATION time instead (schtasks
    itself needs an elevated creating process to register a highest-
    privilege task - normally already true by the time someone toggles
    this, since the app auto-elevates on launch) and then fires
    pre-elevated on every subsequent logon with no prompt at all -
    exactly the "one prompt, ever, not one per boot" behavior this is
    for.

    Falls back to the older registry Run key if schtasks.exe itself is
    unavailable or task creation fails for any reason - degraded (a
    UAC prompt every boot) rather than "Start with Windows" silently
    doing nothing at all."""
    if not enabled:
        _delete_scheduled_task(APP_REG_NAME)
        _delete_startup_registry_entry()
        return

    command = _startup_command(script_path)
    if _create_scheduled_task(APP_REG_NAME, command):
        _delete_startup_registry_entry()  # migrate cleanly off the old mechanism
        return
    if not HAVE_WINREG:
        raise RuntimeError("Neither Task Scheduler nor registry access is available on this platform.")
    with winreg.OpenKey(winreg.HKEY_CURRENT_USER, RUN_KEY, 0, winreg.KEY_SET_VALUE) as key:
        winreg.SetValueEx(key, APP_REG_NAME, 0, winreg.REG_SZ, command)


# ------------------------------------------------------------ log manager --

class LogManager:
    """Rotating JSONL writer: caps each file at max_file_bytes, caps the
    whole folder at max_total_bytes by deleting the oldest files first.
    Every write is flushed + fsynced so a crash doesn't lose the tail.

    Tracks the running total size in memory rather than re-scanning the
    whole logs folder (glob + stat every file) on every single write -
    that scan is only actually needed when a write pushes the total
    over the cap and something has to be deleted; every other write
    (the vast majority, for almost this file's whole life) just does
    an O(1) increment instead of walking the directory. This matters
    specifically because it runs on every poll for as long as the app
    is logging, which for this app can mean days or weeks."""

    def __init__(self, logs_dir, max_file_bytes=MAX_FILE_BYTES,
                 max_total_bytes=MAX_TOTAL_BYTES):
        self.logs_dir = logs_dir
        self.max_file_bytes = max_file_bytes
        self.max_total_bytes = max_total_bytes
        os.makedirs(logs_dir, exist_ok=True)
        self._fh = None
        self._path = None
        self._size = 0
        # #14: serialize all state/handle mutations. One PollThread is the
        # norm, but a lock makes write/rotate/delete safe even if the
        # overlapping-thread guard (#1) is ever defeated, and it also guards
        # the shutdown-marker write racing the poll thread's last write.
        self._lock = threading.RLock()
        # #16/#17: explicit logger health so the app can never look like it's
        # recording when writes are actually failing (disk full, drive gone).
        self.healthy = True
        self.last_error = None
        self.consecutive_failures = 0
        self.last_ok_time = time.time()
        # #54/#72: files the startup crash analysis still needs - never
        # deleted by cap enforcement until released.
        self._protected = set()
        self._total_size = sum(sz for _, sz in self._all_files())
        self._open_new_file()

    def protect(self, *paths):
        with self._lock:
            for p in paths:
                if p:
                    self._protected.add(os.path.abspath(p))

    def unprotect(self, *paths):
        with self._lock:
            for p in paths:
                self._protected.discard(os.path.abspath(p))

    def _open_new_file(self):
        if self._fh:
            try:
                self._fh.close()
            except Exception:
                pass
        ts = datetime.now().strftime("%Y%m%d_%H%M%S")
        base = os.path.join(self.logs_dir, f"pc_monitor_{ts}")
        path = base + ".jsonl"
        n = 1
        while os.path.exists(path):
            path = f"{base}_{n}.jsonl"
            n += 1
        self._path = path
        self._fh = open(self._path, "a", buffering=1, encoding="utf-8", newline="")  # #62/#63
        self._size = 0

    def write(self, row: dict):
        line = json.dumps(row) + "\n"
        b = len(line.encode("utf-8"))
        with self._lock:
            try:
                if self._size and self._size + b > self.max_file_bytes:
                    self._open_new_file()
                # #15: a single row bigger than the whole per-file cap still
                # gets written (splitting telemetry would corrupt it), but note
                # it so the oversize is visible rather than silently breaking
                # the "max file size" guarantee.
                if b > self.max_file_bytes:
                    self._oversized_rows = getattr(self, "_oversized_rows", 0) + 1
                self._fh.write(line)
                self._fh.flush()
                os.fsync(self._fh.fileno())
                self._size += b
                self._total_size += b
                self._enforce_total_cap()
                self.consecutive_failures = 0
                self.last_ok_time = time.time()
                self.healthy = True
            except Exception as e:
                # #16/#17: a failed write must not silently pass. Record the
                # failure, try to recover a usable handle + resync the size
                # accounting for next time, and re-raise so the caller can
                # persist a separate error record and surface the health state.
                self.consecutive_failures += 1
                self.last_error = f"{type(e).__name__}: {e}"
                self.healthy = False
                try:
                    self._open_new_file()
                    self._total_size = sum(sz for _, sz in self._all_files())
                except Exception:
                    pass
                raise

    def _all_files(self):
        paths = sorted(glob.glob(os.path.join(self.logs_dir, "pc_monitor_*.jsonl")))
        out = []
        for p in paths:
            try:
                out.append((p, os.path.getsize(p)))
            except OSError:
                continue
        return out

    def _enforce_total_cap(self):
        if self._total_size <= self.max_total_bytes:
            return  # the common case, every write until actually near the cap
        files = self._all_files()  # only re-scan when we might delete something
        for path, sz in files:
            if self._total_size <= self.max_total_bytes:
                break
            if path == self._path:
                continue
            if os.path.abspath(path) in self._protected:
                continue  # #54/#72: don't delete the crashed session pre-analysis
            try:
                os.remove(path)
                self._total_size -= sz
            except OSError:
                pass

    def health(self):
        with self._lock:
            return {"healthy": self.healthy, "last_error": self.last_error,
                    "consecutive_failures": self.consecutive_failures,
                    "oversized_rows": getattr(self, "_oversized_rows", 0),
                    "seconds_since_ok": round(time.time() - self.last_ok_time, 1)}

    def current_path(self):
        return self._path

    def total_size(self):
        return self._total_size

    def close(self):
        with self._lock:
            if self._fh:
                try:
                    self._fh.flush()
                    os.fsync(self._fh.fileno())
                except Exception:
                    pass
                try:
                    self._fh.close()
                except Exception:
                    pass
                self._fh = None


def read_range(logs_dir, start_dt=None, end_dt=None):
    """Reads across every rotated log file the range touches - this is
    what lets the History tab span an arbitrary time window regardless
    of how many 10MB files it crosses."""
    rows = []
    for path in sorted(glob.glob(os.path.join(logs_dir, "pc_monitor_*.jsonl"))):
        try:
            with open(path, "r") as f:
                for line in f:
                    line = line.strip()
                    if not line:
                        continue
                    try:
                        row = json.loads(line)
                        # Metric rows carry "ts"; event rows historically
                        # carried only "time", so keying strictly on "ts"
                        # silently dropped every event from History/CSV -
                        # exactly the crash-cause signal this tool exists to
                        # preserve. Accept either so events on disk (old and
                        # new) are readable.
                        stamp = row.get("ts") or row.get("time")
                        dt = datetime.fromisoformat(stamp)
                    except (json.JSONDecodeError, KeyError, ValueError, TypeError):
                        continue
                    if start_dt and dt < start_dt:
                        continue
                    if end_dt and dt > end_dt:
                        continue
                    rows.append((dt, row))
        except OSError:
            continue
    rows.sort(key=lambda x: x[0])
    return rows


def _safe_size(path):
    try:
        return os.path.getsize(path)
    except OSError:
        return 0


def previous_session_status(logs_dir, current_path=None):
    """Looks at the most recent PRIOR log file (not the one this run just
    opened) and decides whether the last session ended cleanly.

    A clean exit writes a trailing {"kind":"shutdown"} marker (see
    App._real_close). If the most recent prior file has real data but no
    such marker as its last line, the previous session ended abruptly -
    an app kill, a power loss, or a full hard-lock/hard-restart, which by
    definition can't record its own death. Returns a dict describing that
    for a startup notice, or None if the last session ended cleanly / no
    prior logs exist. Reads only the file tail, so it's cheap even on a
    full 10MB log."""
    try:
        files = sorted(glob.glob(os.path.join(logs_dir, "pc_monitor_*.jsonl")))
    except Exception:
        return None
    prior = [f for f in files if os.path.abspath(f) != os.path.abspath(current_path or "")]
    # #25: skip trailing empty/near-empty files (e.g. a session that opened a
    # log then died before writing anything) so we assess the real previous
    # session, not a zero-byte artifact.
    prior = [f for f in prior if _safe_size(f) > 2]
    if not prior:
        return None
    path = prior[-1]
    try:
        with open(path, "rb") as f:
            try:
                f.seek(-8192, os.SEEK_END)
            except OSError:
                f.seek(0)  # file smaller than the tail window
            tail = f.read().decode("utf-8", errors="ignore")
    except OSError:
        return None
    last_obj = None
    for line in tail.splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            last_obj = json.loads(line)
        except json.JSONDecodeError:
            continue  # a torn final line from an abrupt stop is itself a signal
    if last_obj is None:
        return None
    if last_obj.get("kind") == "shutdown":
        return None  # ended cleanly
    last_ts = last_obj.get("ts") or last_obj.get("time")
    return {"path": path, "last_ts": last_ts}


def _read_tail_objs(path, max_bytes=262144):
    """Parse the JSON objects in the tail of a log file (best-effort)."""
    objs = []
    try:
        with open(path, "rb") as f:
            try:
                f.seek(-max_bytes, os.SEEK_END)
            except OSError:
                f.seek(0)
            data = f.read().decode("utf-8", errors="ignore")
    except OSError:
        return objs
    for line in data.splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            objs.append(json.loads(line))
        except json.JSONDecodeError:
            continue
    return objs


def _find_recent_minidumps(after_iso):
    """New crash dumps Windows may have written for this crash - kernel
    minidumps, the full memory dump, and GPU-specific LiveKernelReports
    (where display-driver TDRs land)."""
    found = []
    seen = set()  # #59: the recursive + non-recursive globs overlap
    try:
        after = datetime.fromisoformat(after_iso) if after_iso else None
    except Exception:
        after = None
    # #60: if we couldn't parse the crash time, don't dump EVERY historical
    # minidump as if it were related - only keep ones from the last day.
    if after is None:
        after = datetime.now() - timedelta(days=1)
    pats = (r"C:\Windows\Minidump\*.dmp", r"C:\Windows\MEMORY.DMP",
            r"C:\Windows\LiveKernelReports\*.dmp",
            r"C:\Windows\LiveKernelReports\**\*.dmp")
    for pat in pats:
        try:
            for p in glob.glob(pat, recursive=True):
                rp = os.path.abspath(p)
                if rp in seen:
                    continue
                try:
                    mt = datetime.fromtimestamp(os.path.getmtime(p))
                except OSError:
                    continue
                if mt >= after:
                    seen.add(rp)
                    found.append((p, mt.isoformat(timespec="seconds")))
        except Exception:
            continue
    return found


def grab_windows_events(start_iso, logs=("System", "Application"), cap=400):
    """Retrospectively pull everything the Windows event logs recorded from
    `start_iso` onward - run on the boot AFTER a crash so it captures the
    Kernel-Power 41 / WHEA / Display 4101 entries Windows writes about the
    crash (which the live watcher can't see, because the machine was
    already frozen). Keeps Error/Warning levels plus a few known crash
    sources/IDs at any level. This is the 'auto-grab the Windows logs'
    step - the whole picture in the crash report without opening Event
    Viewer."""
    if not HAVE_EVTLOG:
        return []
    try:
        start = datetime.fromisoformat(start_iso) if start_iso else None
    except Exception:
        start = None
    level_name = {1: "Error", 2: "Warning", 4: "Information", 8: "AuditOK", 16: "AuditFail"}
    crash_sources = ("Microsoft-Windows-Kernel-Power", "Microsoft-Windows-WHEA-Logger",
                     "EventLog", "BugCheck", "Save Dump", "Display", "nvlddmkm", "amdkmdag")
    crash_ids = (41, 1001, 4101, 6008, 1074)
    out = []
    flags = win32evtlog.EVENTLOG_BACKWARDS_READ | win32evtlog.EVENTLOG_SEQUENTIAL_READ
    for log_name in logs:
        try:
            hand = win32evtlog.OpenEventLog(None, log_name)
        except Exception:
            continue
        got = 0
        try:
            done = False
            while not done and got < cap:
                try:
                    events = win32evtlog.ReadEventLog(hand, flags, 0)
                except Exception:
                    break
                if not events:
                    break
                for ev in events:
                    try:
                        t = datetime.fromtimestamp(int(ev.TimeGenerated))
                    except Exception:
                        continue
                    if start is not None and t < start:
                        done = True
                        break
                    et = ev.EventType
                    src = ev.SourceName or ""
                    eid = ev.EventID & 0xFFFF
                    keep = (et in (1, 2)) or (src in crash_sources) or (eid in crash_ids)
                    if not keep:
                        continue
                    inserts = None
                    try:
                        si = ev.StringInserts or []
                        inserts = [str(s).strip() for s in si if s][:8]
                    except Exception:
                        pass
                    out.append({"log": log_name, "level": level_name.get(et, str(et)),
                                "source": src, "event_id": eid,
                                "time": t.isoformat(timespec="seconds"), "detail": inserts})
                    got += 1
                    if got >= cap:
                        break
        finally:
            try:
                win32evtlog.CloseEventLog(hand)
            except Exception:
                pass
    out.sort(key=lambda e: e["time"])
    return out


def _session_span(path):
    """(start_ts, end_ts, duration, crashed?) for a log file, reading only
    its head and tail so it's cheap."""
    start = None
    try:
        with open(path, "rb") as f:
            head = f.read(4096).decode("utf-8", errors="ignore")
    except OSError:
        return None
    for line in head.splitlines():
        try:
            o = json.loads(line)
        except json.JSONDecodeError:
            continue
        ts = o.get("ts") or o.get("time")
        if ts:
            start = ts
            break
    tail = _read_tail_objs(path, 16384)
    if not tail or not start:
        return None
    crashed = tail[-1].get("kind") != "shutdown"
    end = None
    for o in reversed(tail):
        ts = o.get("ts") or o.get("time")
        if ts:
            end = ts
            break
    if not end:
        return None
    try:
        dur = (datetime.fromisoformat(end) - datetime.fromisoformat(start)).total_seconds()
    except Exception:
        return None
    return {"path": path, "start": start, "end": end, "dur": dur, "crashed": crashed}


def crash_acceleration(logs_dir, n=8):
    """Are crashes happening sooner each time? 'It crashes faster the next
    time' is a real signature (heat-soak, or a driver left in a bad state
    after the first hang). Compares the last couple of crashed sessions'
    durations."""
    try:
        files = sorted(glob.glob(os.path.join(logs_dir, "pc_monitor_*.jsonl")))
    except Exception:
        return None
    spans = [s for s in (_session_span(f) for f in files[-n:]) if s]
    # #43: only compare sessions that ran long enough to be meaningful. A
    # startup crash-loop produces several ~seconds-long sessions whose
    # durations aren't comparable to a real gaming session - excluding the
    # trivially short ones avoids a bogus "accelerating" verdict.
    crashed = [s for s in spans if s["crashed"] and s["dur"] is not None and s["dur"] >= 30]
    if len(crashed) < 2:
        return None
    d0, d1 = crashed[-2]["dur"], crashed[-1]["dur"]
    note = None
    if d0 > 0 and d1 < d0 * 0.7:
        note = (f"Crashes are accelerating - last session lasted {d1/60:.0f} min "
                f"vs {d0/60:.0f} min before. That's consistent with heat-soak or "
                "the driver being left in a bad state after the previous hang.")
    return {"durations_min": [round(s["dur"] / 60, 1) for s in crashed], "note": note}


def analyze_crash(path):
    """Read the tail of a crashed log and classify what happened, so the
    startup notice / desktop report can say *why*, not just 'unclean
    shutdown'. Returns a dict with a classification, evidence lines, and
    the raw pieces (events, proc_exits, inventory, last rows)."""
    objs = _read_tail_objs(path)
    metrics = [o for o in objs if not o.get("kind")]
    events = [o for o in objs if o.get("kind") == "event"]
    exits = [o for o in objs if o.get("kind") == "proc_exit"]
    inv = next((o.get("inventory") for o in objs if o.get("kind") == "session_start"), None)
    if inv is None:
        # the session_start header is at the TOP of the log, not the tail -
        # on any session longer than a few minutes it's outside the tail
        # window, so read the head for it too
        try:
            with open(path, "rb") as fh:
                head = fh.read(8192).decode("utf-8", errors="ignore")
            for line in head.splitlines():
                try:
                    o = json.loads(line)
                except json.JSONDecodeError:
                    continue
                if o.get("kind") == "session_start":
                    inv = o.get("inventory")
                    break
        except OSError:
            pass
    last_ts = metrics[-1]["ts"] if metrics else (
        objs[-1].get("ts") or objs[-1].get("time") if objs else None)

    classification = "abrupt stop with no clear precursor in the captured data"
    evidence = []

    # #23: don't mistake a SENSOR/LHM connection loss for a GPU failure. If the
    # tail is dominated by sensor_error rows, the GPU telemetry being "frozen"
    # (absent) is just LHM going away, not a driver hang.
    tail_metrics = metrics[-15:] if metrics else []
    sensor_lost = bool(tail_metrics) and sum(
        1 for o in tail_metrics if o.get("sensor_error")) >= max(3, len(tail_metrics) // 2)

    # GPU stall: prefer the live confidence grade the poll thread recorded
    # (#9/#24); fall back to detecting a frozen-while-recently-active signature
    # in the tail. Only call it a hang when the GPU was actually working.
    live_conf = next((o.get("gpu_stall_confidence") for o in reversed(tail_metrics)
                      if o.get("gpu_stall_confidence")), None)
    gpu_stalled = any(o.get("gpu_stalled") for o in tail_metrics)
    if not gpu_stalled and len(metrics) >= 4 and not sensor_lost:
        tail = metrics[-6:]
        sigs = [_gpu_signature(o.get("sensors") or {}) for o in tail]
        sigs = [s for s in sigs if s is not None]
        active = any(_gpu_active(o.get("sensors") or {}) for o in tail)
        if len(sigs) >= 4 and len(set(sigs)) == 1 and active:
            gpu_stalled = True
    if sensor_lost and not gpu_stalled:
        classification = ("sensor/LibreHardwareMonitor connection was lost before "
                          "the end - GPU state is unknown, not necessarily a hang")
        evidence.append("The final samples had sensor errors (LHM unreachable), so "
                        "absent GPU data here is a monitoring gap, not proof of a GPU hang.")
    elif gpu_stalled:
        # #24: hedge the wording to match the evidence strength.
        conf = live_conf or "possible"
        if conf == "likely":
            classification = ("GPU driver hang - LIKELY (GPU sensors froze while the "
                              "rest kept updating, with corroborating signals)")
        else:
            classification = ("GPU sensors froze while the rest kept updating - "
                              "POSSIBLE GPU driver hang (no independent corroboration)")
        evidence.append("GPU readings stopped changing before the end while CPU/system "
                        "readings continued - the pattern of a driver stall / TDR.")
        evidence.append("NOTE: frozen sensor values are strong but not definitive on "
                        "their own; confirm with a Display/nvlddmkm 4101 or WHEA event.")

    # thermal
    hot = None
    for o in metrics[-10:]:
        mt, _ = _danger_from_sensors(o.get("sensors") or {})
        if mt is not None and (hot is None or mt > hot):
            hot = mt
    if hot is not None and hot >= 95:
        classification = f"possible thermal event (a real sensor hit {hot:.0f}C)"
        evidence.append(f"A real CPU/GPU sensor reached {hot:.0f}C near the end.")

    # memory
    peak_mem = max((o.get("memory", {}).get("percent") or 0) for o in metrics) if metrics else 0
    min_avail = min((o.get("memory", {}).get("available_gb") or 1e9) for o in metrics) if metrics else None
    if peak_mem >= 92:
        classification = f"possible out-of-memory (RAM peaked at {peak_mem:.0f}%)"
        evidence.append(f"RAM use peaked at {peak_mem:.0f}%.")
    elif metrics:
        evidence.append(f"RAM was fine (peaked {peak_mem:.0f}%, "
                        f"{min_avail:.0f} GB still free) - not an OOM.")

    # peak temps + heat-soak trend (the 'temp related' angle). Absolute
    # temps rarely look dangerous at a 1s sample right before a GPU hang,
    # but a rising trend + an aggressive undervolt = temp-dependent
    # instability, which fits 'crashes faster when already warm'.
    def peak_temp(*substr):
        vals = [_find_sensor(o.get("sensors", {}), *substr) for o in metrics]
        vals = [v for v in vals if isinstance(v, (int, float))]
        return max(vals) if vals else None
    gpu_core_pk = peak_temp("temperature", "gpu core")
    gpu_hot_pk = peak_temp("temperature", "gpu hot")
    gpu_mem_pk = peak_temp("temperature", "gpu mem")
    if any(v is not None for v in (gpu_core_pk, gpu_hot_pk, gpu_mem_pk)):
        evidence.append("Peak GPU temps: core %s / hot spot %s / mem junction %s C."
                        % (gpu_core_pk, gpu_hot_pk, gpu_mem_pk))
    # heat-soak: GPU core temp trending up over the session
    core_series = [_find_sensor(o.get("sensors", {}), "temperature", "gpu core") for o in metrics]
    core_series = [v for v in core_series if isinstance(v, (int, float))]
    if len(core_series) >= 20:
        first_q = sum(core_series[:len(core_series)//4]) / (len(core_series)//4)
        last_q = sum(core_series[-len(core_series)//4:]) / (len(core_series)//4)
        if last_q - first_q >= 6:
            evidence.append(f"GPU was heat-soaking - core temp drifted up "
                            f"~{last_q-first_q:.0f}C over the session "
                            f"({first_q:.0f}->{last_q:.0f}C).")

    if exits:
        names = ", ".join(sorted({e.get("process", "?") for e in exits[-6:]}))
        evidence.append(f"Processes that exited near the end: {names}.")
        if any("dwm" in (e.get("process", "").lower()) for e in exits):
            evidence.append("dwm.exe (the desktop compositor) crashed - it "
                            "dies when the GPU driver goes down, corroborating "
                            "a graphics-driver failure.")
    if events:
        evs = "; ".join(f"{e.get('log','')}/{e.get('source','')} {e.get('event_id','')}"
                        for e in events[-5:])
        evidence.append(f"Error events logged: {evs}.")

    return {"path": path, "last_ts": last_ts, "classification": classification,
            "evidence": evidence, "inventory": inv, "gpu_stalled": gpu_stalled,
            "events": events, "proc_exits": exits,
            "forced_close": any(o.get("kind") == "forced_close" for o in objs)}


def _desktop_dir():
    for cand in (os.path.join(os.environ.get("OneDrive", ""), "Desktop"),
                 os.path.join(os.environ.get("USERPROFILE", ""), "Desktop"),
                 os.path.join(os.path.expanduser("~"), "Desktop")):
        if cand and os.path.isdir(cand):
            return cand
    return os.path.expanduser("~")


def previous_session_driver(logs_dir, current_path=None):
    """The GPU driver version recorded in the most recent PRIOR session's
    header, so a change can be flagged (did crashes start after an update?)."""
    try:
        files = sorted(glob.glob(os.path.join(logs_dir, "pc_monitor_*.jsonl")))
    except Exception:
        return None
    prior = [f for f in files if os.path.abspath(f) != os.path.abspath(current_path or "")]
    for f in reversed(prior):
        try:
            with open(f, "rb") as fh:
                head = fh.read(8192).decode("utf-8", errors="ignore")
        except OSError:
            continue
        for line in head.splitlines():
            try:
                o = json.loads(line)
            except json.JSONDecodeError:
                continue
            if o.get("kind") == "session_start":
                return (o.get("inventory") or {}).get("gpu_driver")
    return None


def dump_crash_data_to_desktop(logs_dir, last_ts, max_bytes=10 * 1024 * 1024):
    """Preserve the RAW telemetry leading up to the crash: the last
    `max_bytes` of log data across rotated files, written under APP_CRASH_DIR as
    pc_crash_{date-time}_last{N}mb.jsonl. The full picture (every sensor,
    every poll), not just the analysis - so nothing is lost even if logs
    later rotate away. Deduped by crash time."""
    stamp = (last_ts or datetime.now().isoformat(timespec="seconds"))
    stamp = stamp.replace(":", "").replace("-", "").replace("T", "_")[:15]
    mb = max(1, int(max_bytes / (1024 * 1024)))
    os.makedirs(APP_CRASH_DIR, exist_ok=True)
    out = os.path.join(APP_CRASH_DIR, f"pc_crash_{stamp}_last{mb}mb.jsonl")
    if os.path.exists(out):
        return out
    try:
        files = sorted(glob.glob(os.path.join(logs_dir, "pc_monitor_*.jsonl")))
    except Exception:
        return None
    if not files:
        return None
    chosen = []
    total = 0
    for f in reversed(files):  # newest -> oldest, whole files until over budget
        try:
            sz = os.path.getsize(f)
        except OSError:
            continue
        chosen.append((f, sz))
        total += sz
        if total >= max_bytes:
            break
    chosen.reverse()  # chronological
    rest = sum(sz for _, sz in chosen[1:])
    first_f, first_sz = chosen[0]
    first_take = max(0, min(first_sz, max_bytes - rest))
    try:
        with open(out, "wb") as w:
            with open(first_f, "rb") as r:
                if first_take < first_sz:
                    r.seek(first_sz - first_take)
                    chunk = r.read()
                    nl = chunk.find(b"\n")  # drop the torn partial first line
                    if nl != -1:
                        chunk = chunk[nl + 1:]
                    w.write(chunk)
                else:
                    w.write(r.read())
            for f, _sz in chosen[1:]:
                with open(f, "rb") as r:
                    w.write(r.read())
        return out
    except OSError:
        return None


def _multipart_form(fields, files):
    """Build a multipart/form-data body (stdlib only, no requests dep)."""
    import uuid
    boundary = "----pcmon" + uuid.uuid4().hex
    body = bytearray()
    for name, val in fields.items():
        body += f"--{boundary}\r\n".encode()
        body += f'Content-Disposition: form-data; name="{name}"\r\n\r\n'.encode()
        body += f"{val}\r\n".encode()
    for i, (fname, data, ctype) in enumerate(files):
        body += f"--{boundary}\r\n".encode()
        body += (f'Content-Disposition: form-data; name="files[{i}]"; '
                 f'filename="{fname}"\r\n').encode()
        body += f"Content-Type: {ctype}\r\n\r\n".encode()
        body += data + b"\r\n"
    body += f"--{boundary}--\r\n".encode()
    return boundary, bytes(body)


def post_crash_to_discord(webhook_url, content, files):
    """POST a message + file attachments to a Discord webhook. files is a
    list of (filename, bytes, content_type). Discord caps attachments at
    ~25MB; oversized ones are dropped (the report is tiny and always fits).
    Best-effort - returns (ok, detail). Never raises."""
    if not webhook_url:
        return False, "no webhook configured"
    import urllib.request
    LIMIT = 24 * 1024 * 1024
    files = [f for f in files if len(f[1]) <= LIMIT]
    try:
        boundary, body = _multipart_form(
            {"payload_json": json.dumps({"content": content[:1900]})}, files)
        req = urllib.request.Request(webhook_url, data=body, method="POST")
        req.add_header("Content-Type", f"multipart/form-data; boundary={boundary}")
        req.add_header("User-Agent", "PCMonitor/%s" % APP_VERSION)
        with urllib.request.urlopen(req, timeout=15) as resp:
            return (200 <= resp.status < 300), f"HTTP {resp.status}"
    except Exception as e:
        return False, str(e)


def export_diagnostics_zip(logs_dir, dest_dir=None, recent=3):
    """Bundle the recent logs + any crash reports + a fresh inventory into the
    central APP_EXPORTS_DIR unless the caller explicitly chooses a destination."""
    import zipfile
    label = (CONFIG.get("machine_label") or "").strip() or "pc"
    label = re.sub(r"[^A-Za-z0-9_-]+", "_", label)
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    dest_dir = dest_dir or APP_EXPORTS_DIR
    os.makedirs(dest_dir, exist_ok=True)
    out = os.path.join(dest_dir, f"pcmonitor_diag_{label}_{stamp}.zip")
    try:
        logs = sorted(glob.glob(os.path.join(logs_dir, "pc_monitor_*.jsonl")))[-recent:]
        reports = glob.glob(os.path.join(APP_CRASH_DIR, "pc_crash_*.txt"))
        with zipfile.ZipFile(out, "w", zipfile.ZIP_DEFLATED) as z:
            for f in logs:
                z.write(f, os.path.basename(f))
            for f in sorted(reports)[-5:]:
                z.write(f, os.path.basename(f))
            try:
                z.writestr("inventory.json", json.dumps(_gather_inventory(), indent=2))
            except Exception:
                pass
        return out
    except Exception:
        return None


def export_app_logs_zip(logs_dir, dest_path=None, max_log_mb=40):
    """Export useful PC Monitor/watchdog/remote logs without exporting the
    RustDesk state file that contains the saved password."""
    import zipfile
    dest_dir = os.path.dirname(dest_path) if dest_path else APP_EXPORTS_DIR
    os.makedirs(dest_dir, exist_ok=True)
    if not dest_path:
        dest_path = os.path.join(dest_dir, f"pcmonitor_logs_{datetime.now().strftime('%Y%m%d_%H%M%S')}.zip")
    candidates = []
    for pattern in (
        os.path.join(logs_dir, "pc_monitor_*.jsonl"),
        os.path.join(logs_dir, "pcmonitor_*.log"),
        os.path.join(APP_DATA_DIR, "pc_monitor_crash.log"),
        os.path.join(APP_DATA_DIR, "pcmonitor_watchdog.log"),
        os.path.join(APP_DATA_DIR, "pcmonitor_watchdog.ps1"),
        REMOTE_LOG_PATH,
    ):
        candidates.extend(glob.glob(pattern))
    candidates = sorted(set(p for p in candidates if os.path.isfile(p)), key=lambda p: os.path.getmtime(p), reverse=True)
    total = 0
    cap = max(1, int(max_log_mb)) * 1024 * 1024
    try:
        with zipfile.ZipFile(dest_path, "w", zipfile.ZIP_DEFLATED) as z:
            for path in candidates:
                try:
                    size = os.path.getsize(path)
                    if path.lower().endswith(".jsonl") and total + size > cap:
                        continue
                    z.write(path, os.path.relpath(path, APP_DATA_DIR))
                    if path.lower().endswith(".jsonl"):
                        total += size
                except OSError:
                    continue
            z.writestr("log_export_info.txt", f"PC Monitor {APP_VERSION}\nMachine: {_machine_label()}\nCreated: {datetime.now().isoformat(timespec='seconds')}\nRemote credentials state.json intentionally excluded.\n")
        return dest_path
    except Exception:
        try: os.remove(dest_path)
        except OSError: pass
        return None


def write_crash_report_to_desktop(path, last_ts, win_events=None, accel=None, analysis=None):
    """On the first launch after a crash, drop a plain-text report under
    APP_CRASH_DIR named pc_crash_{date-time}. Deduped by the crash's timestamp,
    so relaunching before a clean exit won't spam duplicates. Includes the
    auto-grabbed Windows event log entries and crash-acceleration note when
    provided. Returns the report path, or None."""
    stamp = (last_ts or datetime.now().isoformat(timespec="seconds"))
    stamp = stamp.replace(":", "").replace("-", "").replace("T", "_")[:15]
    os.makedirs(APP_CRASH_DIR, exist_ok=True)
    out = os.path.join(APP_CRASH_DIR, f"pc_crash_{stamp}.txt")
    if os.path.exists(out):
        return out  # already dumped for this crash
    a = analysis or analyze_crash(path)
    dumps = _find_recent_minidumps(a.get("last_ts"))
    lines = []
    lines.append("PC Monitor - crash report")
    lines.append("=" * 44)
    lines.append("Previous session ended without a clean shutdown.")
    lines.append(f"Last data logged: {a.get('last_ts')}")
    lines.append(f"Source log: {a.get('path')}")
    lines.append("")
    lines.append("LIKELY CAUSE:")
    lines.append(f"  {a.get('classification')}")
    lines.append("")
    if a.get("termination_note"):
        lines.append("WHAT ENDED (PC vs monitor):")
        lines.append(f"  {a['termination_note']}")
        lines.append("")
    if accel and accel.get("note"):
        lines.append("CRASH TREND:")
        lines.append(f"  {accel['note']}")
        lines.append("")
    if a.get("evidence"):
        lines.append("EVIDENCE:")
        for e in a["evidence"]:
            lines.append(f"  - {e}")
        lines.append("")
    if a.get("inventory"):
        lines.append("SYSTEM (from session start):")
        for k, v in a["inventory"].items():
            if v is not None:
                lines.append(f"  {k}: {v}")
        if a["inventory"].get("gpu_driver_changed_from"):
            lines.append("  ** GPU driver changed since the previous session - "
                         "if crashes started recently, suspect the driver update. **")
        lines.append("")
    if win_events:
        lines.append(f"WINDOWS EVENT LOG around the crash ({len(win_events)} entries):")
        for e in win_events:
            det = (" :: " + " | ".join(e["detail"])) if e.get("detail") else ""
            lines.append(f"  [{e.get('time')}] {e.get('level','')} {e.get('log','')}/"
                         f"{e.get('source','')} ({e.get('event_id','')}){det}")
        lines.append("")
    else:
        lines.append("WINDOWS EVENT LOG around the crash: none matched (either the "
                     "machine didn't reboot, nothing was logged in the window, or "
                     "the event log wasn't readable). If it was a hard lock, check "
                     "Event Viewer > System on this boot for Kernel-Power 41.")
        lines.append("")
    if dumps:
        lines.append("WINDOWS CRASH DUMPS written around this time:")
        for p, mt in dumps:
            lines.append(f"  {p}  ({mt})")
        lines.append("")
    lines.append("NEXT STEP: in the Windows events above, look for Kernel-Power 41 "
                 "(unclean shutdown), nvlddmkm / Display 4101 (GPU driver), or "
                 "WHEA-Logger (hardware). None of those + a GPU sensor freeze = "
                 "GPU hang, most often driver or an unstable undervolt/overclock.")
    try:
        with open(out, "w", encoding="utf-8") as f:
            f.write("\n".join(lines))
        return out
    except OSError:
        return None


# ------------------------------------------------------------- poll thread --

class PollThread(threading.Thread):
    def __init__(self, out_queue, log_manager, interval_holder, stop_event):
        super().__init__(daemon=True)
        self.out_queue = out_queue
        self.log_manager = log_manager
        self.interval_holder = interval_holder
        self.stop_event = stop_event

    def _put(self, item):
        # #4/#5/#74: the GUI queue is display transport, NOT evidence storage
        # (everything important is written to disk first). So it's bounded and
        # never blocks the poll loop: if the GUI has stalled and the queue is
        # full, drop the OLDEST item to make room for the newest rather than
        # letting the producer grow memory without limit during exactly the
        # instability this app exists to record.
        try:
            self.out_queue.put_nowait(item)
        except queue.Full:
            try:
                self.out_queue.get_nowait()
            except queue.Empty:
                pass
            try:
                self.out_queue.put_nowait(item)
            except queue.Full:
                pass

    def _log(self, rec):
        # #33/#68/#74: write to disk FIRST (the evidence), then queue for the
        # GUI. Returns True on success. On failure, try to persist a separate
        # minimal error record so the failure itself leaves a trace on disk
        # (the failed row never made it, so its error couldn't be in it).
        try:
            self.log_manager.write(rec)
            return True
        except Exception as e:
            try:
                self.log_manager.write({
                    "kind": "log_error",
                    "error": f"{type(e).__name__}: {e}",
                    "ts": datetime.now().isoformat(timespec="seconds")})
            except Exception:
                pass  # logger is down; health state carries it (see LogManager)
            return False

    def run(self):
        _lower_thread_priority()
        pythoncom = None
        if HAVE_WMI:
            import pythoncom
            pythoncom.CoInitialize()
        reader = SensorReader(CONFIG.get("lhm_web_port", 8085))
        proc_monitor = ProcessMonitor()
        ev_watcher = EventLogWatcher()
        net_monitor = NetMonitor(CONFIG.get("ping_host", "1.1.1.1"))
        presentmon = PresentMonWatcher(CONFIG.get("presentmon_path"), LOGS_DIR)

        # Core count and boot time can't change during a running session
        # (a reboot would kill this process anyway) - compute once here
        # instead of re-querying psutil for them on every single poll.
        try:
            cached_cpu_counts = (psutil.cpu_count(logical=True), psutil.cpu_count(logical=False))
        except Exception:
            cached_cpu_counts = None
        try:
            cached_boot_time = psutil.boot_time()
        except Exception:
            cached_boot_time = None

        loops_since_retry = 0
        # {pid: name} of last poll's heavy (top-CPU) processes, so we can flag
        # the exact poll one of them disappears - a crash or close. The VR
        # game that crashed in a real capture was a *background* top-CPU
        # process (foreground stayed on the desktop), so tracking foreground
        # alone would have missed it; track the heavy hitters instead.
        prev_heavy = {}
        last_heartbeat = 0.0            # throttle heartbeat writes (~15s)

        # --- adaptive sampling state ---
        adaptive = bool(CONFIG.get("adaptive_poll", True))
        # #50: validate config-driven thresholds so a bad value in the JSON
        # can't wedge the loop (0s spin) or disable adaptive behaviour silently.
        def _num(key, default, lo, hi):
            try:
                return min(max(float(CONFIG.get(key, default)), lo), hi)
            except (TypeError, ValueError):
                return default
        fast_interval = _num("fast_poll_interval", 1.0, 0.2, 60.0)
        fast_gpu_load = _num("fast_gpu_load", 50, 0, 100)
        fast_temp_c = _num("fast_temp_c", 80, 0, 150)
        recent_event_until = 0.0        # stay fast briefly after an error event
        last_event_scan = 0.0           # wall-clock gate for the event-log scan
        EVENT_SCAN_MIN_INTERVAL = 2.0   # don't reopen both logs more often than this

        # --- GPU-stall (driver-hang) detection state ---
        gpu_prev_sig = None
        gpu_frozen_since = None         # #10: monotonic time the signature froze
        gpu_last_active_mono = None     # #11: last time the GPU had real load
        gpu_recovery_tried = False
        gpu_flagged = False             # avoid re-emitting every frozen sample
        recovery_enabled = bool(CONFIG.get("gpu_stall_recovery", False))
        GPU_RECENT_ACTIVE_S = 30.0
        last_poll_wall = None           # for real inter-sample dt
        prev_interval = 5.0             # #67: interval the last sleep actually used
        poll_error_streak = 0           # #32: consecutive failed polls

        # --- session inventory header (once, first thing) ---
        try:
            inv = _gather_inventory()
            try:
                prev_drv = previous_session_driver(LOGS_DIR, self.log_manager.current_path())
                if prev_drv and inv.get("gpu_driver") and prev_drv != inv["gpu_driver"]:
                    inv["gpu_driver_changed_from"] = prev_drv
            except Exception:
                pass
            header = {"kind": "session_start",
                      "ts": datetime.now().isoformat(timespec="seconds"),
                      "inventory": inv}
            # #69: header write failure is no longer silent - it flows into the
            # same logger-health state the GUI surfaces.
            self._log(header)
            self._put(header)
        except Exception:
            pass
        try:
            last_sensor_retry = 0.0
            while not self.stop_event.is_set():
                try:
                    base_interval = min(max(float(self.interval_holder.get("val", 5.0)), 0.5), 60.0)
                except (TypeError, ValueError):
                    base_interval = 5.0
                next_interval = base_interval
                try:
                    # watchdog coordination: honour a clean-exit request (the
                    # watchdog asks for this before an update instead of killing
                    # us), and stamp a heartbeat so the watchdog can tell we're
                    # alive vs crashed/killed.
                    if os.path.exists(EXIT_REQUEST_FILE):
                        try:
                            os.remove(EXIT_REQUEST_FILE)
                        except OSError:
                            pass
                        self._put({"kind": "exit_request"})  # GUI does a clean close
                        break
                    now_hb = time.monotonic()
                    if now_hb - last_heartbeat >= 15:
                        last_heartbeat = now_hb
                        try:
                            with open(HEARTBEAT_FILE, "w", encoding="utf-8") as hf:
                                json.dump({"pid": os.getpid(), "ts": time.time(),
                                           "version": APP_VERSION}, hf)
                        except Exception:
                            pass

                    if not reader.connected:
                        # #34: retry on a wall-clock cadence (~30s), not a loop
                        # count - loop count means wildly different real spacing
                        # under adaptive polling (30 x 1s vs 30 x 5s).
                        now_retry = time.monotonic()
                        if now_retry - last_sensor_retry >= 30:
                            last_sensor_retry = now_retry
                            reader._try_connect()

                    row = {"ts": datetime.now().isoformat(timespec="seconds")}
                    now_wall = time.time()
                    if last_poll_wall is not None:
                        # actual seconds since the previous sample. A widening
                        # gap vs the intended interval means the poll thread
                        # (or the whole machine) was starved - itself a crash
                        # precursor seen in real captures right before a freeze.
                        row["dt"] = round(now_wall - last_poll_wall, 2)
                        row["expected_interval"] = round(prev_interval, 2)  # #67
                    last_poll_wall = now_wall
                    row.update(read_system_stats(proc_monitor, net_monitor,
                                                   cached_cpu_counts, cached_boot_time))

                    if reader.connected:
                        try:
                            row["sensors"] = reader.read_sensors()
                        except Exception as e:
                            row["sensor_error"] = str(e)
                            reader.connected = False
                    else:
                        detail = f" ({reader.last_error})" if reader.last_error else ""
                        row["sensor_error"] = f"LibreHardwareMonitor not detected{detail}"
                        # only worth the extra process sweep when we already
                        # know the simple connection check failed - if
                        # sensors ARE connected, LHM is obviously running,
                        # no need to also check this
                        row["lhm_process_running"] = _is_process_name_running(
                            "librehardwaremonitor")

                    try:
                        frame_samples = presentmon.poll_new_frames()
                        if frame_samples:
                            row["frames"] = {app: compute_frame_stats(times)
                                              for app, times in frame_samples.items()}
                        elif presentmon.available:
                            # no new frames this poll - normal if nothing's
                            # currently presenting 3D content, but worth
                            # distinguishing from "PresentMon itself isn't
                            # even running anymore" (only checked when
                            # there's nothing simpler - frames flowing
                            # already answers this for free)
                            row["presentmon_running"] = presentmon.is_actually_running()
                        # if PresentMon is running and writing, but its CSV
                        # header didn't match any known column names, frames
                        # would otherwise vanish with no explanation - surface
                        # it so the banner can say why FPS is blank
                        if presentmon.column_error:
                            row["presentmon_error"] = presentmon.column_error
                        elif presentmon.launch_error:
                            row["presentmon_error"] = presentmon.launch_error
                        # #21/#22: a rotation just tore down + relaunched capture,
                        # so any frame gap this poll is expected, NOT the game
                        # stopping - mark it so readers don't misread the gap.
                        if getattr(presentmon, "_just_rotated", False):
                            row["presentmon_rotated"] = True
                            presentmon._just_rotated = False
                    except Exception:
                        pass

                    # --- GPU driver-hang detection ---
                    # If the live GPU readings are byte-identical across
                    # consecutive polls while the clock keeps advancing AND the
                    # GPU was doing real work, the driver has stopped updating
                    # them: the GPU is stalled (every value is just its last
                    # reading repeated). This is the exact signature of the
                    # real crashes - GPU sensors froze while the CPU kept
                    # reporting - so flag it explicitly instead of leaving a
                    # misleading "GPU fine at 62%" in the log.
                    sensors_now = row.get("sensors") or {}
                    sig = _gpu_signature(sensors_now)
                    now_mono = time.monotonic()
                    if _gpu_active(sensors_now):
                        gpu_last_active_mono = now_mono
                    frozen = sig is not None and sig == gpu_prev_sig
                    if frozen:
                        if gpu_frozen_since is None:
                            gpu_frozen_since = now_mono
                    else:
                        gpu_frozen_since = None
                        gpu_recovery_tried = False
                        gpu_flagged = False
                    gpu_prev_sig = sig

                    # #10: threshold on ELAPSED TIME, not sample count (adaptive
                    # polling makes N samples mean different real durations).
                    # #11: count it a stall if the GPU was active RECENTLY, not
                    # only at the exact frozen samples - a real driver hang can
                    # drop load to 0 as it dies.
                    flag_s = _num("gpu_stall_flag_seconds", 3.0, 0.5, 120)
                    recover_s = _num("gpu_stall_recover_seconds", 5.0, 1.0, 300)
                    recently_active = (gpu_last_active_mono is not None
                                       and now_mono - gpu_last_active_mono <= GPU_RECENT_ACTIVE_S)
                    frozen_s = (now_mono - gpu_frozen_since) if gpu_frozen_since is not None else 0.0

                    if frozen and frozen_s >= flag_s and recently_active:
                        # #9: report the raw observation honestly and grade
                        # confidence instead of asserting a hang outright.
                        # Frozen sensors alone = "possible"; corroboration from
                        # frames stopping or a recent GPU/Display event = "likely".
                        corroborated = (row.get("presentmon_running") is False
                                        or time.monotonic() < recent_event_until)
                        row["gpu_sensor_values_frozen"] = True
                        row["gpu_frozen_seconds"] = round(frozen_s, 1)
                        row["gpu_stall_confidence"] = "likely" if corroborated else "possible"
                        row["gpu_stalled"] = True   # kept for back-compat readers
                        row["gpu_stale"] = True      # GPU readings are last-known, not live
                        if (recovery_enabled and not gpu_recovery_tried
                                and frozen_s >= recover_s):
                            gpu_recovery_tried = True
                            ok = attempt_gpu_recovery()
                            rec = {"kind": "recovery_attempt",
                                   "action": "gpu_reset_hotkey", "injected": bool(ok),
                                   "ts": row["ts"], "time": row["ts"]}
                            self._log(rec)
                            self._put(rec)
                            row["gpu_recovery_attempted"] = True
                        gpu_flagged = True

                    # --- decide the sampling cadence for the NEXT sleep ---
                    # Base interval comes from the Poll spinbox. Adaptive mode
                    # bursts to fast_interval when something crash-relevant is
                    # happening: a game presenting frames, the GPU under real
                    # load, a hot sensor, or the 15s after an error event. The
                    # expensive work (ping, event-log scan) is separately
                    # wall-clock gated, so bursting multiplies only the cheap
                    # signals, not the costly ones - which is what keeps a 1s
                    # burst from stealing performance from a game.
                    try:
                        base_interval = min(max(float(self.interval_holder.get("val", 5.0)), 0.5), 60.0)
                    except (TypeError, ValueError):
                        base_interval = 5.0
                    next_interval = base_interval
                    if adaptive:
                        max_temp, gpu_load = _danger_from_sensors(row.get("sensors") or {})
                        busy = bool(row.get("frames")) or (
                            gpu_load is not None and gpu_load >= fast_gpu_load)
                        hot = max_temp is not None and max_temp >= fast_temp_c
                        if (busy or hot or row.get("gpu_stalled")
                                or time.monotonic() < recent_event_until):
                            next_interval = min(fast_interval, base_interval)
                            row["poll_mode"] = "fast"

                    # #17/#68: write is disk-first; if it failed, surface the
                    # logger's health on the row so the GUI can show a
                    # persistent warning, and a separate log_error record was
                    # already attempted by _log().
                    if not self._log(row):
                        h = self.log_manager.health()
                        row["log_error"] = h.get("last_error")
                        row["logging_healthy"] = False
                    self._put(row)

                    # flag heavy processes that vanished since last poll - a
                    # game/app crashing (like the VR title WerFault fired on)
                    # shows up here as a precise exit marker, even when it was
                    # never the foreground window
                    try:
                        # #13: track (name, create_time) per PID. Windows reuses
                        # PIDs, so "pid still exists" isn't enough - a new process
                        # can inherit a crashed one's PID. Treat the tracked
                        # process as exited if the PID is gone OR now hosts a
                        # DIFFERENT process (create_time changed).
                        cur_heavy = {}
                        for p in row.get("processes", {}).get("top_cpu", []):
                            pid = p.get("pid")
                            if pid and p.get("name") not in ("System Idle Process", "System"):
                                ct = None
                                try:
                                    ct = psutil.Process(pid).create_time()
                                except Exception:
                                    ct = None
                                cur_heavy[pid] = (p["name"], ct)
                        for pid, (name, ct) in prev_heavy.items():
                            if pid in cur_heavy:
                                continue
                            gone = False
                            try:
                                if not psutil.pid_exists(pid):
                                    gone = True
                                elif ct is not None:
                                    try:
                                        gone = abs(psutil.Process(pid).create_time() - ct) > 1.0
                                    except Exception:
                                        gone = True  # can't inspect it -> treat as gone
                            except Exception:
                                gone = False
                            if gone:
                                marker = {
                                    "kind": "proc_exit", "process": name, "pid": pid,
                                    "ts": row["ts"], "time": row["ts"],
                                }
                                self._log(marker)
                                self._put(marker)
                        prev_heavy = cur_heavy
                    except Exception:
                        pass

                    # Event-log scan is wall-clock gated so fast polling
                    # doesn't reopen both logs every tick - a crash event's
                    # own Windows timestamp is accurate regardless of when we
                    # notice it, so a ~2s scan cadence loses nothing.
                    now_scan = time.time()
                    if now_scan - last_event_scan >= EVENT_SCAN_MIN_INTERVAL:
                        last_event_scan = now_scan
                        try:
                            got_event = False
                            for ev in ev_watcher.poll_new():
                                got_event = True
                                ev["kind"] = "event"
                                # mirror the event's timestamp into "ts" as well:
                                # every reader (read_range, History, CSV) keys on
                                # "ts", so without this the event is written to
                                # disk but can never be read back - see read_range
                                ev["ts"] = ev.get("time")
                                self._log(ev)
                                self._put(ev)
                            if got_event:
                                # capture the aftermath of any error at high res
                                recent_event_until = time.monotonic() + 15  # #51 monotonic
                        except Exception:
                            pass
                    row["poll_ok"] = True  # reached the end of a poll without error
                    poll_error_streak = 0
                except Exception as e:
                    # Something genuinely unexpected broke this poll (e.g.
                    # psutil itself misbehaving). Surface it instead of
                    # letting the whole thread die silently - especially
                    # important since the installed app runs via
                    # pythonw.exe with no console to print a traceback to.
                    poll_error_streak += 1
                    perr = {
                        "kind": "poll_error", "error": f"{type(e).__name__}: {e}",
                        "consecutive": poll_error_streak,  # #32: expose repeated failures
                        "ts": datetime.now().isoformat(timespec="seconds"),
                    }
                    self._log(perr)   # persist to disk, not just the GUI queue
                    self._put(perr)

                prev_interval = next_interval   # #67: remember for next dt comparison
                self.stop_event.wait(next_interval)
        finally:
            presentmon.stop()
            if pythoncom:
                pythoncom.CoUninitialize()


# --------------------------------------------------------------------- UI --

def _make_tray_image():
    """A simple generated icon (blue circle, "PC" monogram) - avoids
    needing a bundled .ico file, which would break the single-file
    design. Only called when HAVE_TRAY is True."""
    size = 64
    img = Image.new("RGBA", (size, size), (0, 0, 0, 0))
    draw = ImageDraw.Draw(img)
    draw.ellipse([2, 2, size - 2, size - 2], fill=(77, 163, 255, 255))
    draw.text((size // 2 - 12, size // 2 - 9), "PC", fill=(15, 15, 15, 255))
    return img


def status_color(value, warn_at, bad_at):
    if value is None:
        return MUTED
    if value >= bad_at:
        return BAD
    if value >= warn_at:
        return WARN
    return GOOD


class Card(tk.Frame):
    def __init__(self, master, title, accent=ACCENT):
        super().__init__(master, bg=PANEL, highlightbackground=BORDER,
                          highlightthickness=1)
        tk.Frame(self, bg=accent, height=3).pack(fill="x", side="top")
        tk.Label(self, text=title, bg=PANEL, fg=MUTED,
                  font=("Segoe UI", 10)).pack(anchor="w", padx=12, pady=(10, 0))
        self.value_lbl = tk.Label(self, text="--", bg=PANEL, fg=FG,
                                    font=("Segoe UI", 19, "bold"))
        self.value_lbl.pack(anchor="w", padx=12, pady=(0, 10))

    def set(self, text, color=FG):
        self.value_lbl.config(text=text, fg=color)


class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(f"PC Monitor  v{APP_VERSION}")
        self.configure(bg=BG)
        self.geometry("1180x720")
        self.minsize(980, 620)

        self._setup_style()

        self.queue = queue.Queue(maxsize=5000)  # #4: bounded; producer drops oldest
        self.closing = False  # #19/#20: set before teardown so workers bail out
        self.log_manager = LogManager(LOGS_DIR)
        self.stop_event = threading.Event()
        self.interval_holder = {"val": 5.0}
        self.poll_thread = None
        self.logging_on = False

        self._build_ui()
        self._start_logging()
        self.after(500, self._pump_queue)

        self._tray_icon = None
        self._tray_notified = False
        if HAVE_TRAY:
            self._start_tray()

        self.protocol("WM_DELETE_WINDOW", self._on_window_close)

        # Auto-open LibreHardwareMonitor (and its web server) on startup if
        # it isn't already up - runs on a background thread so it never
        # blocks the window appearing.
        if CONFIG.get("auto_launch_lhm", True):
            threading.Thread(target=self._autostart_lhm_worker, daemon=True).start()

        # Cross-update: if the watchdog just pulled a newer .py, that .py may
        # carry a newer embedded watchdog - redeploy it. Background so it never
        # delays the window.
        threading.Thread(
            target=lambda: sync_watchdog(APP_DATA_DIR, APP_PATH),
            daemon=True).start()
        threading.Thread(
            target=_ensure_remote_host_async,
            kwargs={"wait": False},
            daemon=True).start()
        # Credential delivery is independent of the RustDesk setup thread.
        # Existing credentials can be sent without elevation, and first-time
        # credentials are sent as soon as the setup thread creates state.json.
        threading.Thread(
            target=_remote_credential_delivery_worker,
            name="RemoteCredentialDelivery",
            daemon=True).start()

        # lifecycle: announce we're up (PC restart, or relaunched after being
        # closed/updated). The app sends "running" itself because it's alive
        # and can; the watchdog owns "stopped" (a crashed app can't report its
        # own death). Background so it never blocks the window.
        threading.Thread(target=self._notify_running, daemon=True).start()

        self._check_previous_session()

    def _notify_running(self):
        hook = (CONFIG.get("discord_webhook_url") or "").strip()
        if not hook:
            return
        try:
            post_crash_to_discord(
                hook, f"PC Monitor v{APP_VERSION} running on `{_machine_label()}`.", [])
        except Exception:
            pass

    def _check_previous_session(self):
        """If the last session didn't end cleanly, kick off crash handling
        on a background thread: classify the cause, auto-grab the Windows
        event logs around the crash, check whether crashes are speeding up,
        write a Desktop report, and surface it all. Threaded because
        reading the event logs can take a moment - it must never delay the
        window appearing."""
        try:
            info = previous_session_status(LOGS_DIR, self.log_manager.current_path())
        except Exception:
            info = None
        if not info:
            return
        self.crash_notice.config(
            text="Previous session ended without a clean shutdown - gathering "
                 "crash details and grabbing the Windows event logs...")
        threading.Thread(target=self._crash_report_worker, args=(info,),
                         daemon=True).start()

    def _crash_report_worker(self, info):
        # #72/#54: make sure startup log-cap enforcement can't delete the
        # crashed session out from under the analysis that's about to read it.
        try:
            self.log_manager.protect(info["path"])
        except Exception:
            pass
        try:
            a = analyze_crash(info["path"])
        except Exception:
            a = {"classification": "", "evidence": [], "last_ts": info.get("last_ts"),
                 "path": info["path"], "inventory": None}
        # auto-grab the Windows event logs from ~3 min before the crash onward
        # (captures the post-reboot Kernel-Power 41 / WHEA / Display entries)
        win_events = []
        try:
            start = None
            if a.get("last_ts"):
                start = (datetime.fromisoformat(a["last_ts"]) - timedelta(minutes=3)
                         ).isoformat(timespec="seconds")
            win_events = grab_windows_events(start)
        except Exception:
            win_events = []
        # #44/#65: distinguish "the PC crashed" from "the monitor process died"
        # (or was force-killed) so we never claim a PC crash that didn't happen.
        try:
            kp41 = any(e.get("event_id") == 41 and "Kernel-Power" in (e.get("source") or "")
                       for e in win_events)
            bugcheck = any("bugcheck" in (e.get("source") or "").lower()
                           or e.get("event_id") == 1001 and "BugCheck" in (e.get("source") or "")
                           for e in win_events)
            unclean_boot = any(e.get("event_id") == 6008 for e in win_events)  # "unexpected shutdown"
            py_err = any(e.get("event_id") == 1000 and any(
                "python" in (d or "").lower() for d in (e.get("detail") or []))
                for e in win_events)
            forced = a.get("forced_close")
            if kp41 or bugcheck or unclean_boot:
                a["termination_note"] = ("The PC itself went down uncleanly (Windows logged "
                                          "Kernel-Power 41 / BugCheck / unexpected-shutdown) - "
                                          "a real hard crash or power loss.")
            elif py_err:
                a["termination_note"] = ("Windows logged an Application Error for python/pythonw "
                                          "- the MONITOR process crashed; the PC may have stayed up.")
            elif forced:
                a["termination_note"] = ("The monitor was force-closed while still busy (not "
                                          "necessarily a system crash).")
            else:
                a["termination_note"] = ("No Kernel-Power 41 / BugCheck found yet - if the PC "
                                          "truly hard-locked this may still appear; otherwise the "
                                          "monitor may have been killed rather than the PC crashing.")
        except Exception:
            pass
        # fold the grabbed events into THIS session's log so History shows them
        for e in win_events:
            rec = dict(e)
            rec["kind"] = "event"
            rec["retrospective"] = True
            rec["ts"] = e.get("time")
            try:
                self.log_manager.write(rec)
            except Exception:
                pass
        try:
            accel = crash_acceleration(LOGS_DIR)
        except Exception:
            accel = None
        out = None
        if CONFIG.get("crash_dump_to_desktop", True):
            try:
                out = write_crash_report_to_desktop(
                    info["path"], info.get("last_ts"), win_events, accel, a)
            except Exception:
                out = None
        # preserve the raw telemetry too - the last N MB across rotated files
        data_path = None
        try:
            mb = int(CONFIG.get("crash_dump_last_mb", 10))
            if mb > 0:
                data_path = dump_crash_data_to_desktop(
                    LOGS_DIR, info.get("last_ts"), mb * 1024 * 1024)
        except Exception:
            data_path = None
        # ship it to Discord so crashes come to you automatically
        discord_status = None
        webhook = (CONFIG.get("discord_webhook_url") or "").strip()
        if webhook and CONFIG.get("discord_upload_crash", True):
            try:
                label = (a.get("inventory") or {}).get("machine") or (
                    CONFIG.get("machine_label") or "")
                content = (f"**PC crash** on `{label}` at {a.get('last_ts')}\n"
                           f"Likely cause: {a.get('classification')}")
                if accel and accel.get("note"):
                    content += "\n" + accel["note"]
                files = []
                if out:
                    with open(out, "rb") as fh:
                        files.append((os.path.basename(out), fh.read(), "text/plain"))
                if data_path:
                    import gzip
                    with open(data_path, "rb") as fh:
                        gz = gzip.compress(fh.read())
                    files.append((os.path.basename(data_path) + ".gz", gz,
                                  "application/gzip"))
                ok, detail = post_crash_to_discord(webhook, content, files)
                discord_status = "sent to Discord" if ok else f"Discord upload failed ({detail})"
            except Exception as e:
                discord_status = f"Discord upload failed ({e})"

        # #72/#54: analysis + export + upload done - the raw data is now
        # preserved on the Desktop, so it's safe to let cap enforcement
        # manage the original file again.
        try:
            self.log_manager.unprotect(info["path"])
        except Exception:
            pass

        def finish():
            if self.closing:  # #19
                return
            msg = ("Previous session ended WITHOUT a clean shutdown (last data at "
                   f"{a.get('last_ts')}).")
            if a.get("classification"):
                msg += f"  Likely cause: {a['classification']}."
            if a.get("termination_note"):
                msg += "  " + a["termination_note"]
            if accel and accel.get("note"):
                msg += "  " + accel["note"]
            if win_events:
                msg += (f"  Auto-grabbed {len(win_events)} Windows event(s) around the "
                        "crash - shown in the Events tab.")
            if out:
                msg += f"  Report saved in PC Monitor data: {os.path.basename(out)}."
            if data_path:
                msg += f"  Raw data: {os.path.basename(data_path)}."
            if discord_status:
                msg += "  " + discord_status + "."
            self.crash_notice.config(text=msg)
            for e in win_events[-60:]:
                self._add_event_row({**e, "kind": "event"})
        self.after(0, finish)

    def _autostart_lhm_worker(self):
        """Best-effort: make sure LibreHardwareMonitor is running with its
        Remote Web Server on, without the user clicking anything.

        - Already reachable? Do nothing (no duplicate launch, no UAC).
        - Not running at all? patch_lhm_config() to turn on the web server
          + minimize-to-tray + minimize-on-close (takes effect from LHM's
          2nd launch onward, since it reads its config at startup), then
          launch it elevated, minimized, and hide its window once it's up.
        - Running but NOT reachable (web server off)? Don't spawn a second
          instance and fight over the port - patch the config for next time
          and tell the user to flip the toggle (or restart LHM) once.

        COM is initialized on THIS thread because the reachability probe
        may go through WMI. Failures here are swallowed - this is a
        convenience, it must never take the app down."""
        pythoncom = None
        try:
            if HAVE_WMI:
                import pythoncom
                pythoncom.CoInitialize()

            reachable = False
            try:
                reachable = SensorReader(CONFIG.get("lhm_web_port", 8085)).connected
            except Exception:
                reachable = False
            if reachable:
                return

            path = locate_lhm()
            if not path or not os.path.exists(path):
                # nothing to launch - leave the existing banner / Auto-Locate
                # button to guide the user to download it
                return

            patched = patch_lhm_config(path)
            running = _is_process_name_running("librehardwaremonitor")

            if running:
                # open but web server off; config is now patched for next time
                if not self.closing:
                    self.after(0, lambda: self.autosetup_lbl.config(
                        text="LibreHardwareMonitor is open but its web server is "
                             "off - enable Options > Remote Web Server > Run, or "
                             "restart it to pick up the auto-config."))
                return

            try:
                launch_elevated(path, minimized=True)
            except Exception:
                return
            if patched:
                # fully configured from a prior run -> nothing to click, hide it
                hide_window_when_ready("Libre Hardware Monitor", timeout=20)
            else:
                # first-ever launch: window must stay visible for the one-time
                # Options step; tell the user what to tick
                if not self.closing:
                    self.after(0, lambda: self.autosetup_lbl.config(
                        text="Launched LibreHardwareMonitor - in Options, tick "
                             "Remote Web Server > Run (+ Minimize to Tray, Run On "
                             "Windows Startup). After that once, it's automatic."))
        finally:
            if pythoncom:
                pythoncom.CoUninitialize()

    # -- styling --
    def _setup_style(self):
        style = ttk.Style(self)
        style.theme_use("clam")
        style.configure(".", background=BG, foreground=FG,
                         fieldbackground=PANEL, bordercolor=BORDER,
                         font=("Segoe UI", 10))
        style.configure("TFrame", background=BG)
        style.configure("TLabel", background=BG, foreground=FG)
        style.configure("TButton", background=PANEL, foreground=FG,
                         padding=6, bordercolor=BORDER)
        style.map("TButton", background=[("active", "#3a3a3a")])
        style.configure("TCheckbutton", background=BG, foreground=FG)
        style.map("TCheckbutton", background=[("active", BG)])
        style.configure("TNotebook", background=BG, bordercolor=BORDER)
        style.configure("TNotebook.Tab", background=PANEL, foreground=FG,
                         padding=(14, 8))
        style.map("TNotebook.Tab", background=[("selected", ACCENT)],
                   foreground=[("selected", "#0b0b0b")])
        style.configure("Treeview", background=PANEL, fieldbackground=PANEL,
                         foreground=FG, rowheight=24, bordercolor=BORDER)
        style.configure("Treeview.Heading", background="#333333", foreground=FG)
        style.map("Treeview", background=[("selected", ACCENT)])
        style.configure("TSpinbox", fieldbackground=PANEL, foreground=FG,
                         background=PANEL)
        style.configure("TEntry", fieldbackground=PANEL, foreground=FG)
        style.configure("TPanedwindow", background=BG)

    # -- layout --
    def _build_ui(self):
        nb = ttk.Notebook(self)
        nb.pack(fill="both", expand=True, padx=10, pady=10)

        self.live_tab = ttk.Frame(nb)
        self.hist_tab = ttk.Frame(nb)
        self.remote_tab = ttk.Frame(nb)
        nb.add(self.live_tab, text="Live")
        nb.add(self.hist_tab, text="History")
        nb.add(self.remote_tab, text="Remote")

        self._build_live_tab()
        self._build_history_tab()
        self._build_remote_tab()

    def _build_live_tab(self):
        header = tk.Frame(self.live_tab, bg=BG)
        header.pack(fill="x", pady=(0, 4))
        tk.Label(header, text="PC MONITOR", bg=BG, fg=ACCENT,
                  font=("Segoe UI", 14, "bold")).pack(side="left")
        tk.Label(header, text="  crash diagnosis dashboard", bg=BG, fg=MUTED,
                  font=("Segoe UI", 9)).pack(side="left")

        self.banner = tk.Label(self.live_tab, text="", bg=BG, fg=WARN,
                                 font=("Segoe UI", 9), justify="left", anchor="w")
        self.banner.pack(anchor="w")
        self.error_lbl = tk.Label(self.live_tab, text="", bg=BG, fg=BAD,
                                    font=("Segoe UI", 9), justify="left", anchor="w")
        self.error_lbl.pack(anchor="w")
        # persistent notice shown when the PREVIOUS session ended without a
        # clean shutdown (crash / hard-restart) - points at the last log
        self.crash_notice = tk.Label(self.live_tab, text="", bg=BG, fg=BAD,
                                       font=("Segoe UI", 9, "bold"), justify="left",
                                       anchor="w", wraplength=1000)
        self.crash_notice.pack(anchor="w")
        # shows GPU model + driver version once the session header arrives
        self.inventory_lbl = tk.Label(self.live_tab, text="", bg=BG, fg=MUTED,
                                       font=("Segoe UI", 8), justify="left", anchor="w")
        self.inventory_lbl.pack(anchor="w")

        if not IS_ADMIN:
            admin_row = tk.Frame(self.live_tab, bg=BG)
            admin_row.pack(fill="x", pady=(2, 0))
            tk.Label(admin_row, text="Not running as Administrator - probably "
                      "not the issue if sensors show N/A (check \"Options > "
                      "Remote Web Server > Run\" in LibreHardwareMonitor "
                      "first - see the status row in the sensor table below "
                      "for the actual error), but some sensors on some "
                      "hardware still need it. Worth trying if the web "
                      "server toggle alone doesn't fix it.",
                      bg=BG, fg=WARN, font=("Segoe UI", 9),
                      wraplength=760, justify="left").pack(side="left")
            ttk.Button(admin_row, text="Restart as Administrator",
                        command=self._restart_elevated).pack(side="left", padx=8)

        self._static_missing = []
        self._last_banner_text = None  # sentinel so the first _update_banner() call always applies
        if not HAVE_WMI:
            self._static_missing.append(
                "the WMI fallback for older LibreHardwareMonitor versions "
                "(pip install wmi pywin32) - not needed if yours is 0.9.5+ "
                "and you've enabled Options > Remote Web Server > Run, "
                "which is what this app reads from by default now")
        if not HAVE_EVTLOG:
            self._static_missing.append("Windows event log (pip install pywin32)")
        if not CONFIG.get("presentmon_path"):
            self._static_missing.append('FPS/frame data (use "Locate PresentMon.exe" below)')
        if not HAVE_TRAY:
            self._static_missing.append("minimize-to-tray (pip install pystray Pillow) - "
                                          "closing this window will ask before it stops logging")
        self._update_banner(None)

        controls = ttk.Frame(self.live_tab)
        controls.pack(fill="x", pady=(6, 4))
        self.toggle_btn = ttk.Button(controls, text="Stop Logging",
                                       command=self._toggle_logging)
        self.toggle_btn.pack(side="left")
        ttk.Label(controls, text="  Poll every").pack(side="left", padx=(12, 4))
        self.interval_var = tk.StringVar(value="5")
        spin = ttk.Spinbox(controls, from_=1, to=60, width=4,
                             textvariable=self.interval_var,
                             command=self._on_interval_change)
        spin.bind("<Return>", lambda e: self._on_interval_change())
        spin.bind("<FocusOut>", lambda e: self._on_interval_change())
        spin.pack(side="left")
        ttk.Label(controls, text="sec").pack(side="left", padx=(4, 12))
        ttk.Button(controls, text="Open Logs Folder",
                    command=self._open_logs_folder).pack(side="left", padx=6)
        ttk.Button(controls, text="Export App Logs",
                    command=self._export_app_logs).pack(side="left", padx=6)
        self.status_lbl = ttk.Label(controls, text="", foreground=MUTED)
        self.status_lbl.pack(side="right")

        controls2 = ttk.Frame(self.live_tab)
        controls2.pack(fill="x", pady=(0, 10))
        self.startup_var = tk.BooleanVar(value=is_startup_enabled())
        startup_chk = ttk.Checkbutton(controls2, text="Start with Windows",
                                        variable=self.startup_var,
                                        command=self._toggle_startup)
        startup_chk.pack(side="left")
        if not HAVE_WINREG:
            startup_chk.state(["disabled"])
        ttk.Button(controls2, text="Locate PresentMon.exe",
                    command=self._choose_presentmon).pack(side="left", padx=12)
        self.presentmon_lbl = ttk.Label(controls2, text=self._presentmon_status_text(),
                                          foreground=MUTED)
        self.presentmon_lbl.pack(side="left")
        self.autosetup_btn = ttk.Button(controls2, text="Auto-Locate / Download Tools",
                                          command=self._auto_setup_tools)
        self.autosetup_btn.pack(side="left", padx=12)
        self.autosetup_lbl = ttk.Label(controls2, text="", foreground=MUTED)
        self.autosetup_lbl.pack(side="left")
        ttk.Button(controls2, text="Hide LibreHardwareMonitor Window",
                    command=self._hide_lhm_window).pack(side="left", padx=12)
        ttk.Button(controls2, text="Export Diagnostics (zip)",
                    command=self._export_diagnostics).pack(side="left", padx=6)
        ttk.Button(controls2, text="Repair Watchdog",
                    command=self._repair_watchdog).pack(side="left", padx=6)
        ttk.Button(controls2, text="Re-run Setup...",
                    command=self._rerun_installer).pack(side="right", padx=6)

        cards = ttk.Frame(self.live_tab)
        cards.pack(fill="x", pady=(0, 4))
        self.card_cpu_temp = Card(cards, "CPU Temp (C)", ACCENT_THERMAL)
        self.card_cpu_clock = Card(cards, "CPU Clock (MHz)", ACCENT_CPU)
        self.card_cpu_power = Card(cards, "CPU Power (W)", ACCENT_THERMAL)
        self.card_cpu_load = Card(cards, "CPU Load (%)", ACCENT_CPU)
        self.card_mem = Card(cards, "Memory", ACCENT_MEM)
        for c in (self.card_cpu_temp, self.card_cpu_clock,
                   self.card_cpu_power, self.card_cpu_load, self.card_mem):
            c.pack(side="left", fill="both", expand=True, padx=4)

        gpu_cards = ttk.Frame(self.live_tab)
        gpu_cards.pack(fill="x", pady=(4, 4))
        self.card_gpu_temp = Card(gpu_cards, "GPU Temp (C)", ACCENT_THERMAL)
        self.card_gpu_clock = Card(gpu_cards, "GPU Clock (MHz)", ACCENT_GPU)
        self.card_gpu_mem_clock = Card(gpu_cards, "GPU Mem Clock (MHz)", ACCENT_GPU)
        self.card_gpu_power = Card(gpu_cards, "GPU Power (W)", ACCENT_THERMAL)
        self.card_gpu_voltage = Card(gpu_cards, "GPU Voltage (V)", ACCENT_GPU)
        self.card_gpu_load = Card(gpu_cards, "GPU Load (%)", ACCENT_GPU)
        for c in (self.card_gpu_temp, self.card_gpu_clock, self.card_gpu_mem_clock,
                   self.card_gpu_power, self.card_gpu_voltage, self.card_gpu_load):
            c.pack(side="left", fill="both", expand=True, padx=4)

        cards2 = ttk.Frame(self.live_tab)
        cards2.pack(fill="x", pady=(4, 6))
        self.card_fps = Card(cards2, "FPS (active window)", ACCENT_FPS)
        self.card_low1 = Card(cards2, "1% Low FPS", ACCENT_FPS)
        self.card_ping = Card(cards2, "Ping (ms)", ACCENT_NET)
        self.card_loss = Card(cards2, "Packet Loss (%)", ACCENT_NET)
        self.card_net_down = Card(cards2, "Net Down (Mbps)", ACCENT_NET)
        self.card_net_up = Card(cards2, "Net Up (Mbps)", ACCENT_NET)
        for c in (self.card_fps, self.card_low1, self.card_ping, self.card_loss,
                   self.card_net_down, self.card_net_up):
            c.pack(side="left", fill="both", expand=True, padx=4)

        self.sysinfo_lbl = tk.Label(self.live_tab, text="", bg=BG, fg=MUTED,
                                      font=("Segoe UI", 9), anchor="w")
        self.sysinfo_lbl.pack(fill="x", pady=(0, 8))

        paned = ttk.Panedwindow(self.live_tab, orient="horizontal")
        paned.pack(fill="both", expand=True)

        left = ttk.Frame(paned)
        ttk.Label(left, text="All detected hardware sensors:").pack(anchor="w")
        self.raw_tree = ttk.Treeview(left, columns=("sensor", "value"),
                                       show="headings", height=18, selectmode="extended")
        self.raw_tree.heading("sensor", text="Sensor")
        self.raw_tree.heading("value", text="Value")
        self.raw_tree.column("sensor", width=460)
        self.raw_tree.column("value", width=120)
        self.raw_tree.pack(fill="both", expand=True, pady=(4, 0))
        self._raw_tree_items = {}  # sensor name -> Treeview item id, for in-place updates
        self._bind_tree_copy(self.raw_tree)
        paned.add(left, weight=3)

        right = ttk.Frame(paned)
        sub_nb = ttk.Notebook(right)
        sub_nb.pack(fill="both", expand=True)

        proc_tab = ttk.Frame(sub_nb)
        frames_tab = ttk.Frame(sub_nb)
        events_tab = ttk.Frame(sub_nb)
        sub_nb.add(proc_tab, text="Processes")
        sub_nb.add(frames_tab, text="Frames")
        sub_nb.add(events_tab, text="Events")

        ttk.Label(proc_tab, text="Top CPU processes:").pack(anchor="w")
        self.cpu_proc_tree = ttk.Treeview(
            proc_tab, columns=("name", "pid", "cpu"), show="headings", height=6, selectmode="extended")
        for c, t, w in [("name", "Process", 120), ("pid", "PID", 60), ("cpu", "CPU %", 60)]:
            self.cpu_proc_tree.heading(c, text=t)
            self.cpu_proc_tree.column(c, width=w, anchor="center")
        self.cpu_proc_tree.pack(fill="x", pady=(4, 10))

        ttk.Label(proc_tab, text="Top memory processes:").pack(anchor="w")
        self.mem_proc_tree = ttk.Treeview(
            proc_tab, columns=("name", "pid", "mem"), show="headings", height=6, selectmode="extended")
        for c, t, w in [("name", "Process", 120), ("pid", "PID", 60), ("mem", "Mem %", 60)]:
            self.mem_proc_tree.heading(c, text=t)
            self.mem_proc_tree.column(c, width=w, anchor="center")
        self.mem_proc_tree.pack(fill="both", expand=True, pady=(0, 4))
        self._bind_tree_copy(self.cpu_proc_tree)
        self._bind_tree_copy(self.mem_proc_tree)

        ttk.Label(frames_tab, text="Apps currently presenting frames:").pack(anchor="w")
        self.frames_tree = ttk.Treeview(
            frames_tab, columns=("app", "fps", "min", "max", "low1", "low01", "stutter", "frames"),
            show="headings", height=12)
        for c, t, w in [("app", "App", 110), ("fps", "Avg FPS", 60),
                          ("min", "Min FPS", 60), ("max", "Max FPS", 60),
                          ("low1", "1% Low", 60), ("low01", "0.1% Low", 60),
                          ("stutter", "Stutters", 60), ("frames", "Frames", 55)]:
            self.frames_tree.heading(c, text=t)
            self.frames_tree.column(c, width=w, anchor="center")
        self.frames_tree.pack(fill="both", expand=True, pady=(4, 4))
        self._bind_tree_copy(self.frames_tree)
        tk.Label(frames_tab,
                  text="Needs PresentMon configured above. Every process actively "
                       "rendering 3D frames shows up here with real per-frame FPS, "
                       "1%/0.1% lows, and a stutter count (frames far longer than "
                       "that app's recent average).",
                  bg=BG, fg=MUTED, font=("Segoe UI", 8), wraplength=320,
                  justify="left").pack(anchor="w")

        ttk.Label(events_tab, text="Recent errors (System + Application logs) and process exits:").pack(anchor="w")
        self.event_tree = ttk.Treeview(
            events_tab, columns=("time", "log", "source", "id", "detail"),
            show="headings", height=14, selectmode="extended")
        for c, t, w in [("time", "Time", 125), ("log", "Log", 70),
                          ("source", "Source", 120), ("id", "ID", 45),
                          ("detail", "Detail", 260)]:
            self.event_tree.heading(c, text=t)
            self.event_tree.column(c, width=w, anchor="w")
        self.event_tree.pack(fill="both", expand=True, pady=(4, 4))
        self._bind_tree_copy(self.event_tree)

        paned.add(right, weight=2)

    def _build_remote_tab(self):
        top = ttk.Frame(self.remote_tab)
        top.pack(fill="x", pady=(4, 8))
        ttk.Label(top, text="RustDesk unattended remote access", font=("Segoe UI", 13, "bold")).pack(anchor="w")
        ttk.Label(top, text="RustDesk is repaired/updated on PC Monitor startup and its service is configured for automatic boot.", foreground=MUTED, wraplength=1000, justify="left").pack(anchor="w", pady=(2, 8))
        creds = ttk.LabelFrame(self.remote_tab, text="Saved RustDesk credentials")
        creds.pack(fill="x", pady=(0, 8), padx=2)
        ttk.Label(creds, text="RustDesk ID").grid(row=0, column=0, sticky="w", padx=8, pady=8)
        self.remote_id_var = tk.StringVar()
        self.remote_id_entry = ttk.Entry(creds, textvariable=self.remote_id_var, width=28, state="readonly")
        self.remote_id_entry.grid(row=0, column=1, sticky="w", padx=4, pady=8)
        ttk.Label(creds, text="Permanent Password").grid(row=1, column=0, sticky="w", padx=8, pady=8)
        self.remote_pw_var = tk.StringVar()
        self.remote_pw_entry = ttk.Entry(creds, textvariable=self.remote_pw_var, width=28, state="readonly", show="*")
        self.remote_pw_entry.grid(row=1, column=1, sticky="w", padx=4, pady=8)
        ttk.Button(creds, text="Copy ID", command=lambda: self._copy_text(self.remote_id_var.get())).grid(row=0, column=2, padx=4, pady=8)
        ttk.Button(creds, text="Copy Password", command=lambda: self._copy_text(self.remote_pw_var.get())).grid(row=1, column=2, padx=4, pady=8)
        ttk.Button(creds, text="Resend Credentials", command=self._resend_remote_credentials).grid(row=0, column=3, rowspan=2, padx=12, pady=8)
        actions = ttk.Frame(self.remote_tab)
        actions.pack(fill="x", pady=(0, 8))
        ttk.Button(actions, text="Repair / Update RustDesk", command=self._repair_remote).pack(side="left", padx=4)
        ttk.Button(actions, text="Open Remote Log", command=self._open_remote_log).pack(side="left", padx=4)
        ttk.Button(actions, text="Export App Logs", command=self._export_app_logs).pack(side="left", padx=4)
        ttk.Button(actions, text="Send App Logs to Discord", command=self._send_app_logs_to_discord).pack(side="left", padx=4)
        self.remote_status_lbl = ttk.Label(self.remote_tab, text="", foreground=MUTED, wraplength=1000, justify="left")
        self.remote_status_lbl.pack(anchor="w", pady=(0, 6))
        info = tk.Text(self.remote_tab, height=12, wrap="word", bg=PANEL, fg=FG, insertbackground=FG, relief="flat", borderwidth=0)
        info.pack(fill="both", expand=True)
        info.insert("1.0", "You can highlight/copy the ID and password above.\n\nAll Live/History tables support row highlighting and Ctrl+C to copy selected rows.\n\nRemote setup log:\n" + REMOTE_LOG_PATH + "\n\nApp log folder:\n" + LOGS_DIR + "\n\nThe exported app-log bundle intentionally excludes state.json, which contains the saved RustDesk password.")
        info.configure(state="disabled")
        self._refresh_remote_ui()

    def _refresh_remote_ui(self):
        state = _remote_read_state() or {}
        self.remote_id_var.set(str(state.get("rustdesk_id") or ""))
        self.remote_pw_var.set(str(state.get("password") or ""))
        version = state.get("rustdesk_version") or "not configured"
        notified = state.get("credentials_notified_app_version") or "not yet"
        self.remote_status_lbl.config(text=f"RustDesk: v{version}    PC Monitor credentials last sent: {notified}")

    def _copy_text(self, text):
        text = str(text or "")
        if not text: return
        try:
            self.clipboard_clear(); self.clipboard_append(text); self.update()
            messagebox.showinfo("Copied", "Copied to clipboard.")
        except Exception as e:
            messagebox.showerror("Copy", f"Couldn't copy:\n{e}")

    def _bind_tree_copy(self, tree):
        def copy_selected(_event=None):
            items = tree.selection()
            if not items: return "break"
            self._copy_text("\n".join("\t".join(str(v) for v in tree.item(item, "values")) for item in items))
            return "break"
        tree.bind("<Control-c>", copy_selected)
        tree.bind("<Control-C>", copy_selected)

    def _resend_remote_credentials(self):
        self.remote_status_lbl.config(text="Sending saved RustDesk credentials to Discord...")
        def worker():
            ok = _remote_resend_credentials()
            def done():
                self._refresh_remote_ui()
                (messagebox.showinfo if ok else messagebox.showwarning)("RustDesk credentials", "RustDesk ID and password were sent to Discord." if ok else f"Discord delivery failed or credentials are missing.\n\nSee:\n{REMOTE_LOG_PATH}")
            self.after(0, done)
        threading.Thread(target=worker, daemon=True).start()

    def _repair_remote(self):
        self.remote_status_lbl.config(text="Repairing/checking RustDesk...")
        def worker():
            ok = _remote_install_host()
            def done():
                self._refresh_remote_ui()
                (messagebox.showinfo if ok else messagebox.showwarning)("RustDesk", "RustDesk repair/update completed and the service was checked." if ok else f"RustDesk repair/update failed.\n\nSee:\n{REMOTE_LOG_PATH}")
            self.after(0, done)
        threading.Thread(target=worker, daemon=True).start()

    def _open_remote_log(self):
        try:
            os.makedirs(REMOTE_INSTALL_DIR, exist_ok=True)
            with open(REMOTE_LOG_PATH, "a", encoding="utf-8"):
                pass
            os.startfile(REMOTE_LOG_PATH)
        except Exception:
            messagebox.showinfo("Remote log", REMOTE_LOG_PATH)

    def _export_app_logs(self):
        default = os.path.join(APP_EXPORTS_DIR, f"pcmonitor_logs_{datetime.now().strftime('%Y%m%d_%H%M%S')}.zip")
        path = filedialog.asksaveasfilename(title="Export PC Monitor logs", initialfile=os.path.basename(default), initialdir=os.path.dirname(default), defaultextension=".zip", filetypes=[("ZIP archive", "*.zip")])
        if not path: return
        def worker():
            out = export_app_logs_zip(LOGS_DIR, path)
            self.after(0, lambda: messagebox.showinfo("Export App Logs", f"Saved:\n{out}") if out else messagebox.showerror("Export App Logs", "Couldn't build the log bundle."))
        threading.Thread(target=worker, daemon=True).start()

    def _send_app_logs_to_discord(self):
        self.remote_status_lbl.config(text="Building app-log bundle for Discord...")
        def worker():
            tmp = os.path.join(APP_EXPORTS_DIR, f"pcmonitor_logs_{os.getpid()}_{int(time.time())}.zip")
            out = export_app_logs_zip(LOGS_DIR, tmp, max_log_mb=18)
            ok = False; detail = "bundle creation failed"
            if out:
                try:
                    with open(out, "rb") as f: data = f.read()
                    if len(data) > 24 * 1024 * 1024:
                        detail = f"bundle is too large ({len(data)/1024/1024:.1f} MB)"
                    else:
                        hook = (CONFIG.get("discord_webhook_url") or "").strip()
                        ok, detail = post_crash_to_discord(hook, f"📦 **PC Monitor logs** from `{_machine_label()}` (v{APP_VERSION})", [(os.path.basename(out), data, "application/zip")])
                except Exception as e: detail = f"{type(e).__name__}: {e}"
                try: os.remove(out)
                except OSError: pass
            self.after(0, lambda: (self._refresh_remote_ui(), messagebox.showinfo("Send Logs", "App logs sent to Discord.") if ok else messagebox.showwarning("Send Logs", f"Couldn't send app logs to Discord.\n\n{detail}")))
        threading.Thread(target=worker, daemon=True).start()

    def _build_history_tab(self):
        controls = ttk.Frame(self.hist_tab)
        controls.pack(fill="x", pady=(0, 4))
        for label, minutes in [("Last 15 min", 15), ("Last hour", 60),
                                 ("Last 24h", 1440)]:
            ttk.Button(controls, text=label,
                        command=lambda m=minutes: self._load_history(m)
                        ).pack(side="left", padx=4)
        ttk.Button(controls, text="All time",
                    command=lambda: self._load_history(None)).pack(side="left", padx=4)
        ttk.Button(controls, text="Export view to CSV",
                    command=self._export_csv).pack(side="right", padx=4)
        self.hist_status_lbl = ttk.Label(controls, text="", foreground=MUTED)
        self.hist_status_lbl.pack(side="right", padx=8)

        custom = ttk.Frame(self.hist_tab)
        custom.pack(fill="x", pady=(0, 8))
        ttk.Label(custom, text="Custom range (YYYY-MM-DD HH:MM):").pack(side="left")
        self.range_start_var = tk.StringVar()
        self.range_end_var = tk.StringVar()
        ttk.Entry(custom, textvariable=self.range_start_var, width=17).pack(side="left", padx=4)
        ttk.Label(custom, text="to").pack(side="left")
        ttk.Entry(custom, textvariable=self.range_end_var, width=17).pack(side="left", padx=4)
        ttk.Label(custom, text="(end blank = now)", foreground=MUTED).pack(side="left", padx=(4, 8))
        ttk.Button(custom, text="Apply", command=self._load_custom_range).pack(side="left")

        self.chart = tk.Canvas(self.hist_tab, bg=PANEL, height=170,
                                 highlightthickness=1, highlightbackground=BORDER)
        self.chart.pack(fill="x", pady=(0, 8))
        ttk.Label(self.hist_tab,
                   text="CPU Temp (red) and Memory % (blue), both on a 0-100 scale",
                   foreground=MUTED).pack(anchor="w")

        cols = ("time", "cpu_temp", "gpu_temp", "cpu_clock", "cpu_power",
                 "gpu_clock", "gpu_power", "gpu_voltage",
                 "mem_percent", "fg_fps", "ping_ms")
        self.hist_tree = ttk.Treeview(self.hist_tab, columns=cols,
                                        show="headings", height=14, selectmode="extended")
        headers = {"time": "Time", "cpu_temp": "CPU Temp (C)",
                    "gpu_temp": "GPU Temp (C)", "cpu_clock": "CPU Clock (MHz)",
                    "cpu_power": "CPU Power (W)",
                    "gpu_clock": "GPU Clock (MHz)", "gpu_power": "GPU Power (W)",
                    "gpu_voltage": "GPU Voltage (V)",
                    "mem_percent": "Mem %", "fg_fps": "FPS", "ping_ms": "Ping (ms)"}
        for c in cols:
            self.hist_tree.heading(c, text=headers[c])
            self.hist_tree.column(c, width=125, anchor="center")
        self.hist_tree.pack(fill="both", expand=True, pady=(6, 0))
        self._bind_tree_copy(self.hist_tree)
        self.chart.bind("<Configure>", lambda e: self._draw_chart())

        self._history_rows = []
        self._load_history(60)

    # -- logging control --
    def _start_logging(self):
        self.stop_event.clear()
        self.poll_thread = PollThread(self.queue, self.log_manager,
                                        self.interval_holder, self.stop_event)
        self.poll_thread.start()
        self.logging_on = True

    def _toggle_logging(self):
        if self.logging_on:
            self.stop_event.set()
            if self.poll_thread:
                self.poll_thread.join(timeout=4)
                # #1: if the old thread is still alive, do NOT mark logging
                # stopped and do NOT let a new PollThread start on top of it
                # (two threads sharing one LogManager/queue/PresentMon is the
                # critical race). Show "Stopping..." and keep polling for it
                # to actually exit via a non-blocking after() check.
                if self.poll_thread.is_alive():
                    self.toggle_btn.config(text="Stopping...", state="disabled")
                    self.after(500, self._await_poll_stop)
                    return
                self.poll_thread = None
            self.logging_on = False
            self.toggle_btn.config(text="Start Logging")
        else:
            self._start_logging()
            self.toggle_btn.config(text="Stop Logging")

    def _await_poll_stop(self):
        """Non-blocking wait for a slow poll thread to finish before allowing
        Start again - prevents overlapping PollThreads (#1)."""
        if self.closing:
            return
        if self.poll_thread and self.poll_thread.is_alive():
            self.after(500, self._await_poll_stop)
            return
        self.poll_thread = None
        self.logging_on = False
        self.toggle_btn.config(text="Start Logging", state="normal")

    def _on_interval_change(self):
        try:
            v = float(self.interval_var.get())
            # #49: clamp to a sane range - 0 or a huge value would break the
            # loop / adaptive logic; negative/garbage is ignored.
            self.interval_holder["val"] = min(max(v, 0.5), 60.0)
        except (ValueError, TypeError):
            pass

    def _open_logs_folder(self):
        try:
            os.startfile(LOGS_DIR)  # Windows only
        except Exception:
            messagebox.showinfo("Logs folder", LOGS_DIR)

    def _toggle_startup(self):
        try:
            set_startup_enabled(self.startup_var.get())
        except Exception as e:
            messagebox.showerror("Startup toggle failed", str(e))
            self.startup_var.set(is_startup_enabled())

    def _presentmon_status_text(self):
        p = CONFIG.get("presentmon_path")
        if p and os.path.exists(p):
            return f"PresentMon: {os.path.basename(p)}"
        return "PresentMon: not set (FPS/frame data unavailable)"

    def _restart_elevated(self):
        if not messagebox.askyesno(
                "Restart as Administrator",
                "This closes PC Monitor and reopens it elevated so it can "
                "actually read LibreHardwareMonitor's sensor data. Continue?"):
            return
        try:
            launched = relaunch_as_admin()
        except Exception as e:
            messagebox.showerror("Couldn't restart elevated", str(e))
            return
        if not launched:
            messagebox.showwarning(
                "Restart as Administrator",
                "That didn't go through (declined, or something blocked "
                "it) - staying open as-is rather than closing with nothing "
                "left running.")
            return
        self._real_close()

    def _update_banner(self, sensor_error, lhm_process_running=None,
                        presentmon_running=None, presentmon_error=None):
        """The static list (packages not installed / PresentMon not
        configured) plus, live, whether LibreHardwareMonitor is
        actually connected right now - the wmi/pywin32 packages being
        importable doesn't mean the LHM application itself is running
        and elevated, and cards showing N/A with no banner explanation
        is exactly the confusing state this avoids.

        lhm_process_running/presentmon_running distinguish "not
        running at all" from "running, but not reachable/not
        producing data right now" - two very different fixes (launch
        it vs. check a setting inside it / open a 3D app) that used to
        get lumped into the same vague N/A.

        Runs on every poll, but this text is almost always identical
        poll to poll (it only actually changes when the connection
        status text changes) - skips the .config() call entirely when
        the text hasn't changed, rather than forcing Tkinter to
        re-measure/redraw the label every single poll for nothing."""
        parts = list(self._static_missing)
        if sensor_error:
            if lhm_process_running is False:
                parts.append("hardware sensors right now (LibreHardwareMonitor "
                              "isn't running at all - launch it first)")
            elif lhm_process_running is True:
                parts.append("hardware sensors right now (LibreHardwareMonitor "
                              f"is running, but not reachable: {sensor_error} - "
                              "check Options > Remote Web Server > Run inside it)")
            else:
                parts.append(f"hardware sensors right now ({sensor_error})")
        if presentmon_running is False:
            parts.append("FPS/frame data right now (PresentMon isn't running "
                          "anymore - it may have crashed or failed to start; "
                          "try \"Locate PresentMon.exe\" again)")
        if presentmon_error:
            parts.append("FPS/frame data (" + presentmon_error + ")")
        text = ("Unavailable: " + "; ".join(parts) + ". Everything else still logs."
                if parts else "")
        if text != self._last_banner_text:
            self._last_banner_text = text
            self.banner.config(text=text)

    def _choose_presentmon(self):
        path = filedialog.askopenfilename(
            title="Locate PresentMon exe",
            filetypes=[("Executable", "*.exe"), ("All files", "*.*")])
        if not path:
            return
        _set_config("presentmon_path", path)
        self.presentmon_lbl.config(text=self._presentmon_status_text())
        messagebox.showinfo("PresentMon", "Saved. Toggle Stop/Start Logging once to pick it up.")

    def _rerun_installer(self):
        """Opens the guided setup again in its own console window. This
        is triggered by the "install" command-line argument - a
        mechanism completely separate from the setup_complete flag in
        config, which only governs the automatic first-launch check -
        so this always works regardless of whether that flag is set."""
        if not messagebox.askyesno(
                "Re-run setup",
                "This opens a console window and walks back through setup "
                "(packages, logs folder, PresentMon/LibreHardwareMonitor, "
                "shortcut, startup). This window keeps running separately. "
                "Continue?"):
            return
        console_python = find_console_python()
        if os.path.basename(console_python).lower() != "python.exe":
            if not messagebox.askyesno(
                    "Console not found",
                    "Couldn't find a console python.exe (only pythonw.exe, "
                    "which won't show a window for the setup prompts). "
                    "Try anyway?"):
                return
        try:
            subprocess.Popen(
                [console_python, os.path.abspath(__file__), "install"],
                creationflags=CREATE_NEW_CONSOLE)
        except Exception as e:
            messagebox.showerror("Couldn't start setup", str(e))

    def _hide_lhm_window(self):
        """On-demand, not automatic on launch - hiding it the moment it
        appears would race against the user actually being able to
        click into its Options menu for the one-time setup (Remote Web
        Server + Minimize to Tray), defeating the point. This is for
        after that's done, when the window is just sitting there."""
        if not messagebox.askyesno(
                "Hide LibreHardwareMonitor",
                "Looks for its window and hides it outright (not just "
                "minimizes - no taskbar entry either). Only do this once "
                "you've already enabled Remote Web Server and Minimize to "
                "Tray in its Options menu - there's no easy way to bring "
                "the window back afterward otherwise. Continue?"):
            return
        threading.Thread(target=self._hide_lhm_worker, daemon=True).start()

    def _hide_lhm_worker(self):
        found = hide_window_when_ready("Libre Hardware Monitor", timeout=5)
        self.after(0, lambda: messagebox.showinfo(
            "Hide LibreHardwareMonitor",
            "Hidden." if found else "Couldn't find its window right now - is it running?"))

    def _auto_setup_tools(self):
        self.autosetup_btn.state(["disabled"])
        self.autosetup_lbl.config(text="Checking for existing installs...")
        threading.Thread(target=self._auto_setup_worker, daemon=True).start()

    def _auto_setup_worker(self):
        pythoncom = None
        if HAVE_WMI:
            import pythoncom
            pythoncom.CoInitialize()
        try:
            results = []
            lhm_launch_path = None
            presentmon_ready = False

            pm_path = CONFIG.get("presentmon_path")
            if pm_path and os.path.exists(pm_path):
                results.append("PresentMon already set up.")
            else:
                found = locate_presentmon()
                if found:
                    _set_config("presentmon_path", found)
                    results.append(f"Found existing PresentMon: {found}")
                    presentmon_ready = True
                else:
                    self._set_autosetup_status("Downloading PresentMon...")
                    got = fetch_presentmon()
                    if got:
                        _set_config("presentmon_path", got)
                        results.append(f"Downloaded PresentMon: {got}")
                        presentmon_ready = True
                    else:
                        results.append("Couldn't auto-download PresentMon (check your "
                                        "connection, or grab it manually with the button above).")

            # this needs COM initialized on THIS thread - a fresh SensorReader()
            # here without it would (almost) always report "not connected" even
            # when LibreHardwareMonitor is actually running and reachable
            test_reader = SensorReader(CONFIG.get("lhm_web_port", 8085))
            if test_reader.connected:
                results.append("LibreHardwareMonitor already running and connected.")
            else:
                found = locate_lhm()
                if not found:
                    self._set_autosetup_status("Downloading LibreHardwareMonitor...")
                    found = fetch_and_install_lhm()
                if found:
                    results.append(f"LibreHardwareMonitor ready at: {found}")
                    lhm_launch_path = found
                else:
                    results.append("Couldn't auto-download LibreHardwareMonitor "
                                    "(check your connection, or grab it manually: " + LHM_URL + ")")

            if presentmon_ready:
                results.append("Toggle Stop/Start Logging once to pick up the new PresentMon path.")

            self.after(0, lambda: self._finish_autosetup(results, lhm_launch_path))
        finally:
            if pythoncom:
                pythoncom.CoUninitialize()

    def _set_autosetup_status(self, text):
        if self.closing:
            return
        try:
            self.after(0, lambda: self.autosetup_lbl.config(text=text))
        except Exception:
            pass

    def _finish_autosetup(self, results, lhm_launch_path):
        if self.closing:
            return
        self.autosetup_btn.state(["!disabled"])
        self.autosetup_lbl.config(text="Done - see popup")
        self.presentmon_lbl.config(text=self._presentmon_status_text())
        messagebox.showinfo("Auto-setup", "\n".join(results))
        if not lhm_launch_path:
            return
        already_configured = patch_lhm_config(lhm_launch_path)
        if already_configured:
            prompt = (f"Launch it now?\n{lhm_launch_path}\n\n"
                       "Found settings saved from a previous run and enabled "
                       "Remote Web Server, Minimize to Tray, and minimize-"
                       "on-close automatically. Windows will still show its "
                       "own Administrator prompt (that's not something this "
                       "hides), but once you approve that, LibreHardware"
                       "Monitor's own window will be hidden automatically - "
                       "nothing left to click, nothing visible to close.")
        else:
            prompt = (f"Launch it now?\n{lhm_launch_path}\n\n"
                       "Its window will open normally this first time - "
                       "there's a one-time setup step that needs it visible. "
                       "Once it's open, in its Options menu check ALL THREE:\n"
                       "  - Remote Web Server > Run (this app reads sensors "
                       "from this, not Administrator - the main thing to "
                       "check if data doesn't show up)\n"
                       "  - Minimize to Tray (so closing its window later "
                       "tucks it away instead of exiting and stopping "
                       "sensor data)\n"
                       "  - Run On Windows Startup (so it opens itself next "
                       "time you boot, without this app needing to launch "
                       "it and trigger an Administrator prompt every time)\n\n"
                       "After this once, future launches (including from "
                       "this app) will hide its window automatically - no "
                       "button to click, nothing left visible to close.")
        if messagebox.askyesno("LibreHardwareMonitor", prompt):
            try:
                launch_elevated(lhm_launch_path, minimized=True)
                if already_configured:
                    threading.Thread(target=hide_window_when_ready,
                                       args=("Libre Hardware Monitor",),
                                       daemon=True).start()
            except Exception as e:
                messagebox.showerror("Launch failed", str(e))

    # -- live updates --
    def _pump_queue(self):
        if self.closing:  # #19: don't touch widgets during teardown
            return
        latest_metrics = None
        new_events = []
        poll_error = None
        session_inv = None
        drained = 0
        try:
            # #5: cap how many items one GUI callback processes, so a large
            # backlog can't freeze the UI in a single pass - leftover items
            # are handled on the next tick (rescheduled sooner when busy).
            while drained < 800:
                item = self.queue.get_nowait()
                drained += 1
                kind = item.get("kind")
                if kind in ("event", "proc_exit", "recovery_attempt"):
                    new_events.append(item)
                elif kind == "poll_error":
                    poll_error = item
                elif kind == "session_start":
                    session_inv = item
                elif kind == "exit_request":
                    # watchdog asked us to shut down cleanly (for an update)
                    self._real_close()
                    return
                elif kind in ("shutdown", "forced_close", "log_error"):
                    pass  # markers with no live-UI meaning (already on disk)
                else:
                    latest_metrics = item
        except queue.Empty:
            pass
        if session_inv is not None:
            self._show_inventory(session_inv.get("inventory") or {})
        if latest_metrics:
            self._update_live(latest_metrics)
        for ev in new_events[-400:]:
            self._add_event_row(ev)
        # #17: persistent, unmissable warning if the logger has gone unhealthy -
        # the app must never look like it's recording when writes are failing.
        if latest_metrics and latest_metrics.get("logging_healthy") is False:
            self.crash_notice.config(
                text="CRITICAL: monitoring is running but LOG WRITES ARE FAILING "
                     f"({latest_metrics.get('log_error')}). Crash evidence is NOT "
                     "being saved - check disk space / the logs drive.")
        if poll_error:
            streak = poll_error.get("consecutive", 1)
            extra = f" ({streak} in a row - polling may be persistently broken)" if streak >= 3 else ""
            self.error_lbl.config(
                text=f"Polling hit an error at {poll_error['ts']}{extra}: {poll_error['error']}")
        # reschedule sooner if we hit the cap (backlog remains)
        self.after(200 if drained >= 800 else 1000, self._pump_queue)

    def _show_inventory(self, inv):
        """Surface the session inventory (GPU + driver especially) in the
        status area so the driver version is visible at a glance."""
        if not inv:
            return
        bits = [f"PC Monitor v{inv.get('app_version', APP_VERSION)}"]
        if inv.get("machine"):
            bits.append(str(inv["machine"]))
        if inv.get("gpu"):
            bits.append(inv["gpu"] + (f" (driver {inv['gpu_driver']})"
                                      if inv.get("gpu_driver") else ""))
        if inv.get("ram_total_gb"):
            bits.append(f"{inv['ram_total_gb']} GB RAM")
        try:
            self.inventory_lbl.config(text="   |   ".join(bits))
        except Exception:
            pass

    def _update_live(self, row):
        self._update_banner(row.get("sensor_error"), row.get("lhm_process_running"),
                              row.get("presentmon_running"), row.get("presentmon_error"))
        h = headline(row)
        memory = row.get("memory", {})
        network = row.get("network", {})
        sensors = row.get("sensors", {})
        frames = row.get("frames", {})

        self.card_cpu_temp.set(
            f"{h['cpu_temp']}" if h["cpu_temp"] is not None else "N/A",
            status_color(h["cpu_temp"], 70, 85))
        self.card_gpu_temp.set(
            f"{h['gpu_temp']}" if h["gpu_temp"] is not None else "N/A",
            status_color(h["gpu_temp"], 70, 85))
        self.card_cpu_clock.set(
            f"{h['cpu_clock']}" if h["cpu_clock"] is not None else "N/A")
        self.card_cpu_power.set(
            f"{h['cpu_power']}" if h["cpu_power"] is not None else "N/A")
        self.card_cpu_load.set(
            f"{h['cpu_percent']}" if h["cpu_percent"] is not None else "N/A",
            status_color(h["cpu_percent"], 80, 95))
        mem = h["mem_percent"]
        self.card_mem.set(
            f"{mem}% ({memory.get('used_gb')}/{memory.get('total_gb')} GB)"
            if mem is not None else "N/A",
            status_color(mem, 70, 90))

        self.card_gpu_clock.set(
            f"{h['gpu_clock']}" if h["gpu_clock"] is not None else "N/A")
        self.card_gpu_mem_clock.set(
            f"{h['gpu_mem_clock']}" if h["gpu_mem_clock"] is not None else "N/A")
        self.card_gpu_power.set(
            f"{h['gpu_power']}" if h["gpu_power"] is not None else "N/A")
        self.card_gpu_voltage.set(
            f"{h['gpu_voltage']}" if h["gpu_voltage"] is not None else "N/A")
        self.card_gpu_load.set(
            f"{h['gpu_load']}" if h["gpu_load"] is not None else "N/A",
            status_color(h["gpu_load"], 90, 99))

        self.card_fps.set(f"{h['fg_fps']}" if h["fg_fps"] is not None else "N/A")
        self.card_low1.set(f"{h['fg_low1']}" if h["fg_low1"] is not None else "N/A")
        ping = h["ping_ms"]
        self.card_ping.set(f"{ping}" if ping is not None else "N/A",
                             status_color(ping, 60, 150) if ping is not None else MUTED)
        loss = h["ping_loss"]
        self.card_loss.set(f"{loss}%" if loss is not None else "N/A",
                             status_color(loss, 1, 10) if loss is not None else MUTED)
        self.card_net_down.set(f"{network.get('recv_mbps', 'N/A')}")
        self.card_net_up.set(f"{network.get('sent_mbps', 'N/A')}")

        self.sysinfo_lbl.config(text=fmt_sysinfo(row))

        self._update_raw_sensor_tree(sensors, row.get("sensor_error"))

        procs = row.get("processes", {})
        self.cpu_proc_tree.delete(*self.cpu_proc_tree.get_children())
        for p in procs.get("top_cpu", []):
            self.cpu_proc_tree.insert("", "end", values=(p["name"], p["pid"], p["cpu"]))
        self.mem_proc_tree.delete(*self.mem_proc_tree.get_children())
        for p in procs.get("top_mem", []):
            self.mem_proc_tree.insert("", "end", values=(p["name"], p["pid"], p["mem"]))

        self.frames_tree.delete(*self.frames_tree.get_children())
        for app, s in sorted(frames.items(), key=lambda kv: kv[1].get("frame_count", 0),
                               reverse=True):
            self.frames_tree.insert("", "end", values=(
                app, s.get("avg_fps"), s.get("min_fps"), s.get("max_fps"),
                s.get("low_1pct_fps"), s.get("low_01pct_fps"),
                s.get("stutter_count"), s.get("frame_count")))

        total_mb = self.log_manager.total_size() / 1024**2
        cap_mb = self.log_manager.max_total_bytes / 1024**2
        mode = "fast 1s" if row.get("poll_mode") == "fast" else "normal"
        self.status_lbl.config(
            text=f"Logging to {os.path.basename(self.log_manager.current_path())}"
                 f"   |   sampling: {mode}"
                 f"   |   {total_mb:.1f} / {cap_mb:.0f} MB used")

    def _update_raw_sensor_tree(self, sensors, sensor_error):
        """In-place update instead of delete-everything-then-reinsert
        every poll: for a well-populated motherboard this table can be
        100+ rows, and the set of sensor names is almost always
        identical poll to poll (only the values change) - updating
        existing rows' values in place is far cheaper for Tkinter/Tcl
        than tearing down and rebuilding the whole table every single
        poll, for as long as the app is logging."""
        existing = self._raw_tree_items
        seen = set()
        for k, v in sorted(sensors.items()):
            seen.add(k)
            if k in existing:
                self.raw_tree.item(existing[k], values=(k, v))
            else:
                existing[k] = self.raw_tree.insert("", "end", values=(k, v))

        status_key = "(status)"
        if sensor_error:
            seen.add(status_key)
            if status_key in existing:
                self.raw_tree.item(existing[status_key], values=(status_key, sensor_error))
            else:
                existing[status_key] = self.raw_tree.insert(
                    "", "end", values=(status_key, sensor_error))

        for k in list(existing):
            if k not in seen:
                self.raw_tree.delete(existing[k])
                del existing[k]

    @staticmethod
    def _event_row_values(ev):
        """Normalize an event OR a proc_exit marker into the events tree's
        (time, log, source, id, detail) columns."""
        if ev.get("kind") == "proc_exit":
            return (ev.get("time", ""), "(exit)", ev.get("process", ""),
                    "exited", f"pid {ev.get('pid', '')} no longer running")
        if ev.get("kind") == "recovery_attempt":
            return (ev.get("time", ""), "(recovery)", ev.get("action", "gpu reset"),
                    "sent" if ev.get("injected") else "failed",
                    "attempted GPU driver reset (Win+Ctrl+Shift+B)")
        detail = ev.get("detail")
        detail_txt = " | ".join(detail) if isinstance(detail, list) else (detail or "")
        return (ev.get("time", ""), ev.get("log", ""), ev.get("source", ""),
                ev.get("event_id", ""), detail_txt)

    def _add_event_row(self, ev):
        # #29: the live watcher and the post-crash retrospective grab can both
        # surface the same Windows event. Dedup by (log, record) so it isn't
        # shown twice in the Events tab. Only Windows events have a record;
        # proc_exit / recovery markers always pass through.
        rec = ev.get("record")
        if rec is not None and ev.get("kind") == "event":
            key = (ev.get("log"), rec)
            if not hasattr(self, "_seen_event_keys"):
                self._seen_event_keys = set()
            if key in self._seen_event_keys:
                return
            self._seen_event_keys.add(key)
        self.event_tree.insert("", 0, values=self._event_row_values(ev))
        children = self.event_tree.get_children()
        if len(children) > 200:
            for c in children[200:]:
                self.event_tree.delete(c)

    # -- history --
    def _load_history(self, minutes):
        end_dt = datetime.now()
        start_dt = end_dt - timedelta(minutes=minutes) if minutes else None
        self._load_range_async(start_dt, end_dt)

    def _load_custom_range(self):
        start_text = self.range_start_var.get().strip()
        end_text = self.range_end_var.get().strip()
        try:
            start = datetime.strptime(start_text, "%Y-%m-%d %H:%M")
        except ValueError:
            messagebox.showerror("Custom range", "Start must look like 2026-08-30 14:00")
            return
        if end_text:
            try:
                end = datetime.strptime(end_text, "%Y-%m-%d %H:%M")
            except ValueError:
                messagebox.showerror("Custom range", "End must look like 2026-08-30 18:00")
                return
        else:
            end = datetime.now()
        self._load_range_async(start, end)

    def _load_range_async(self, start_dt, end_dt):
        """Reading + parsing every JSONL line across every rotated file
        a range touches can mean multiple seconds and a lot of memory
        for "All time" on a long-running, heavily-logged setup - doing
        that synchronously in the button handler would freeze the
        whole window. Runs on a background thread instead; a request
        token guards against an older, slower load finishing after
        (and overwriting the view with stale data from) a newer one."""
        self._hist_load_token = getattr(self, "_hist_load_token", 0) + 1
        token = self._hist_load_token
        self.hist_status_lbl.config(text="Loading...")
        threading.Thread(target=self._load_range_worker,
                           args=(start_dt, end_dt, token), daemon=True).start()

    def _load_range_worker(self, start_dt, end_dt, token):
        try:
            rows = read_range(LOGS_DIR, start_dt, end_dt)
            history_rows = [(dt, headline(r)) for dt, r in rows if not r.get("kind")]
            # error events + process-exit markers in the same window - now that
            # read_range no longer drops them, surface them so a post-crash
            # review shows the Application-Error / Kernel-Power entries and the
            # exact moment the crashed app disappeared
            event_rows = [r for dt, r in rows
                          if r.get("kind") in ("event", "proc_exit", "recovery_attempt")]
        except Exception as e:
            self.after(0, lambda: self.hist_status_lbl.config(text=f"Load failed: {e}"))
            return
        self.after(0, lambda: self._apply_history_rows(history_rows, event_rows, token))

    def _apply_history_rows(self, history_rows, event_rows=None, token=None):
        if token is not None and token != getattr(self, "_hist_load_token", token):
            return  # a newer request already superseded this one
        self.hist_status_lbl.config(text="")
        # repopulate the Events tab with the events from this range (most
        # recent first), so browsing a historical window shows the errors
        # from that window rather than only whatever arrived live this session
        if event_rows is not None:
            self.event_tree.delete(*self.event_tree.get_children())
            for ev in event_rows[-200:]:
                self.event_tree.insert("", 0, values=self._event_row_values(ev))
        self._history_rows = history_rows
        self.hist_tree.delete(*self.hist_tree.get_children())
        for dt, h in self._history_rows[-2000:]:  # keep the table responsive
            self.hist_tree.insert("", "end", values=(
                dt.strftime("%Y-%m-%d %H:%M:%S"),
                h["cpu_temp"] if h["cpu_temp"] is not None else "",
                h["gpu_temp"] if h["gpu_temp"] is not None else "",
                h["cpu_clock"] if h["cpu_clock"] is not None else "",
                h["cpu_power"] if h["cpu_power"] is not None else "",
                h["gpu_clock"] if h["gpu_clock"] is not None else "",
                h["gpu_power"] if h["gpu_power"] is not None else "",
                h["gpu_voltage"] if h["gpu_voltage"] is not None else "",
                h["mem_percent"] if h["mem_percent"] is not None else "",
                h["fg_fps"] if h["fg_fps"] is not None else "",
                h["ping_ms"] if h["ping_ms"] is not None else "",
            ))
        self._draw_chart()

    MAX_CHART_POINTS = 2000  # more points than a ~600-1000px wide canvas
                              # could usefully show anyway - plotting
                              # every one of potentially hundreds of
                              # thousands of rows for "All time" is pure
                              # waste, most landing on the same pixel

    @staticmethod
    def _downsample_for_chart(pts, max_points):
        """Buckets pts into max_points groups and keeps whichever point
        in each bucket has the highest cpu_temp - not just every Nth
        point (naive stride sampling), because a single skipped sample
        could be exactly the thermal spike that caused a crash, which
        is the whole point of this chart existing."""
        if len(pts) <= max_points:
            return pts
        bucket_size = len(pts) / max_points
        out = []
        for i in range(max_points):
            start = int(i * bucket_size)
            end = max(int((i + 1) * bucket_size), start + 1)
            bucket = pts[start:end]
            out.append(max(bucket, key=lambda p: p[1]))
        return out

    def _draw_chart(self):
        c = self.chart
        c.delete("all")
        w = max(c.winfo_width(), 600)
        h = 170
        pad = 20
        pts = [(dt, hh["cpu_temp"], hh["mem_percent"])
               for dt, hh in self._history_rows if hh["cpu_temp"] is not None]
        if len(pts) < 2:
            c.create_text(w // 2, h // 2, text="Not enough data for this range",
                           fill=MUTED)
            return
        pts = self._downsample_for_chart(pts, self.MAX_CHART_POINTS)
        t0 = pts[0][0].timestamp()
        t1 = pts[-1][0].timestamp()
        span = max(t1 - t0, 1)

        def xy(dt, val):
            x = pad + (dt.timestamp() - t0) / span * (w - 2 * pad)
            y = (h - pad) - (max(0, min(100, val)) / 100) * (h - 2 * pad)
            return x, y

        temp_pts = [xy(dt, v) for dt, v, _ in pts]
        mem_pts = [xy(dt, m) for dt, _, m in pts if m is not None]

        c.create_line(pad, h - pad, w - pad, h - pad, fill=BORDER)
        c.create_line(pad, pad, pad, h - pad, fill=BORDER)
        if len(temp_pts) > 1:
            c.create_line(*[coord for p in temp_pts for coord in p],
                           fill=BAD, width=2)
        if len(mem_pts) > 1:
            c.create_line(*[coord for p in mem_pts for coord in p],
                           fill=ACCENT, width=2)

    def _export_csv(self):
        if not self._history_rows:
            messagebox.showinfo("Export", "Nothing to export for this range.")
            return
        path = filedialog.asksaveasfilename(defaultextension=".csv",
                                              filetypes=[("CSV", "*.csv")])
        if not path:
            return
        with open(path, "w", newline="") as f:
            wr = csv.writer(f)
            wr.writerow(["time", "cpu_temp_c", "gpu_temp_c", "cpu_clock_mhz",
                          "cpu_power_w", "gpu_clock_mhz", "gpu_power_w",
                          "gpu_voltage_v", "mem_percent", "fg_fps",
                          "fg_low1pct_fps", "ping_ms", "ping_loss_percent"])
            for dt, h in self._history_rows:
                wr.writerow([dt.isoformat(), h["cpu_temp"], h["gpu_temp"],
                              h["cpu_clock"], h["cpu_power"], h["gpu_clock"],
                              h["gpu_power"], h["gpu_voltage"], h["mem_percent"],
                              h["fg_fps"], h["fg_low1"], h["ping_ms"], h["ping_loss"]])
        messagebox.showinfo("Export", f"Saved {path}")

    def _export_diagnostics(self):
        """One click: bundle recent logs + crash reports + inventory into a
        zip on the Desktop for a friend to send for support."""
        def worker():
            out = export_diagnostics_zip(LOGS_DIR)
            def done():
                if out:
                    messagebox.showinfo("Export Diagnostics",
                                         f"Saved diagnostics bundle:\n{out}")
                else:
                    messagebox.showerror("Export Diagnostics",
                                          "Couldn't build the diagnostics zip.")
            self.after(0, done)
        threading.Thread(target=worker, daemon=True).start()

    def _repair_watchdog(self):
        """Force a clean redeploy of the watchdog (new headless launcher +
        re-registered tasks) and report what's actually deployed - so a stuck
        auto-update chain can be fixed with one click instead of a reinstall."""
        def worker():
            ok = deploy_watchdog(APP_DATA_DIR, APP_PATH)
            # read back what's on disk / registered so the user can verify
            ver = "(none)"
            try:
                _, ver_path, _ = _watchdog_paths(APP_DATA_DIR)
                if os.path.exists(ver_path):
                    ver = open(ver_path, encoding="utf-8").read().strip()
            except Exception:
                pass
            task = "unknown"
            try:
                r = subprocess.run(["schtasks", "/Query", "/TN", "PCMonitorWatchdog", "/V", "/FO", "LIST"],
                                   capture_output=True, text=True, creationflags=CREATE_NO_WINDOW, timeout=15)
                task = "registered" if r.returncode == 0 else "NOT registered"
            except Exception:
                pass
            hook = "set" if (CONFIG.get("discord_webhook_url") or "").strip() else "MISSING"
            url = (CONFIG.get("update_url") or "").strip() or "MISSING"
            def done():
                (messagebox.showinfo if ok else messagebox.showwarning)(
                    "Repair Watchdog",
                    f"Redeploy: {'OK' if ok else 'FAILED'}\n"
                    f"Deployed watchdog version: {ver} (this app expects {WATCHDOG_VERSION})\n"
                    f"Scheduled task: {task}\n"
                    f"Webhook: {hook}\n"
                    f"Update URL: {url}\n\n"
                    f"Folder: {APP_DATA_DIR}\n"
                    "If PowerShell still flashes, delete any extra PCMonitor* tasks "
                    "in Task Scheduler - an old one may still run powershell directly.")
            self.after(0, done)
        threading.Thread(target=worker, daemon=True).start()

    # -- shutdown / tray --
    def _start_tray(self):
        try:
            menu = pystray.Menu(
                pystray.MenuItem("Show PC Monitor", self._tray_show, default=True),
                pystray.MenuItem("Exit", self._tray_exit),
            )
            self._tray_icon = pystray.Icon(
                "PCMonitor", _make_tray_image(), "PC Monitor - logging", menu)
            threading.Thread(target=self._tray_icon.run, daemon=True).start()
        except Exception:
            self._tray_icon = None

    def _tray_show(self, icon=None, item=None):
        self.after(0, self._restore_window)

    def _restore_window(self):
        self.deiconify()
        self.lift()
        self.focus_force()

    def _tray_exit(self, icon=None, item=None):
        self.after(0, self._real_close)

    def _on_window_close(self):
        """The X button and Alt+F4 both route here (Tkinter's
        WM_DELETE_WINDOW protocol covers both on Windows). With a tray
        icon available, this hides the window rather than stopping
        anything - closing this accidentally shouldn't silently kill
        logging. Only the tray menu's Exit actually shuts down. Without
        a tray icon (pystray/Pillow not installed), falls back to an
        explicit confirmation instead of a silent, easy-to-misclick
        exit."""
        if self._tray_icon is not None:
            self.withdraw()
            if not self._tray_notified:
                self._tray_notified = True
                try:
                    self._tray_icon.notify(
                        "Still running and logging - right-click the tray "
                        "icon to reopen or exit.", "PC Monitor")
                except Exception:
                    pass
        else:
            if messagebox.askyesno(
                    "Exit PC Monitor",
                    "Closing this window will stop logging.\n\n"
                    "Install pystray and Pillow (pip install pystray Pillow) "
                    "so this button minimizes to the tray instead.\n\n"
                    "Exit anyway?"):
                self._real_close()

    def _real_close(self):
        self.closing = True  # #19/#20: background workers check this and bail
        self.stop_event.set()
        thread_dead = True
        if self.poll_thread:
            # #2/#3: wait for the poll thread to actually finish before we
            # touch the log. Try longer than one interval, then confirm.
            self.poll_thread.join(timeout=6)
            thread_dead = not self.poll_thread.is_alive()
        # #3: only write the CLEAN-shutdown marker if monitoring truly stopped.
        # If the poll thread is wedged, writing "clean exit" would let the next
        # launch wrongly conclude the session ended normally - so mark it as an
        # unclean/forced close instead, which crash detection treats correctly.
        try:
            if thread_dead:
                self.log_manager.write({
                    "kind": "shutdown", "reason": "clean exit",
                    "ts": datetime.now().isoformat(timespec="seconds")})
            else:
                self.log_manager.write({
                    "kind": "forced_close",
                    "reason": "poll thread did not stop within timeout",
                    "ts": datetime.now().isoformat(timespec="seconds")})
        except Exception:
            pass
        # #2: closing the log races the poll thread only if it's still alive;
        # LogManager's lock (#14) makes a late write safe either way, but we've
        # already waited above.
        self.log_manager.close()
        # remove the heartbeat so the watchdog sees a CLEAN exit (no relaunch,
        # no crash webhook) rather than mistaking this for a crash/kill.
        try:
            os.remove(HEARTBEAT_FILE)
        except OSError:
            pass
        if self._tray_icon is not None:
            try:
                self._tray_icon.stop()
            except Exception:
                pass
        self.destroy()


# ============================================================
#  INSTALLER  -  run with:  python pc_monitor.py install
#  Guided CLI setup: installs pip deps, lets you pick a log
#  folder and (optionally) a PresentMon path, places a copy of
#  this same file in your Start Menu, makes a shortcut, and can
#  enable launch-at-login. Everything asks before it does
#  anything.
# ============================================================

SOURCE_APP = os.path.abspath(__file__)
LHM_URL = "https://github.com/LibreHardwareMonitor/LibreHardwareMonitor/releases"
PRESENTMON_URL = "https://github.com/GameTechDev/PresentMon/releases"


def ask_yes_no(prompt, default=True):
    suffix = "[Y/n]" if default else "[y/N]"
    while True:
        ans = input(f"{prompt} {suffix}: ").strip().lower()
        if not ans:
            return default
        if ans in ("y", "yes"):
            return True
        if ans in ("n", "no"):
            return False
        print("Please answer y or n.")


def ask_path(prompt, default):
    ans = input(f"{prompt}\n  [default: {default}]\n> ").strip().strip('"')
    return ans if ans else default


def step(title):
    print(f"\n== {title} ==")


def install_packages():
    step("Python packages")
    if ask_yes_no("Install/update psutil, wmi, pywin32, pystray, and pillow via pip?"):
        cmd = [sys.executable, "-m", "pip", "install", "--user",
               "psutil", "wmi", "pywin32", "pystray", "pillow"]
        print("Running:", " ".join(cmd))
        result = subprocess.run(cmd)
        if result.returncode != 0:
            print("pip install failed. You can retry manually with:")
            print("  " + " ".join(cmd))
            if not ask_yes_no("Continue anyway?", default=False):
                sys.exit(1)
        else:
            _verify_pywin32()
    else:
        print("Skipped. The app will still run with reduced features "
              "(memory/CPU/disk logging only) until these are installed.")


def _verify_pywin32():
    """pip reporting success doesn't guarantee pywin32's COM helper
    DLLs (pythoncom/pywintypes) actually got registered - a known
    quirk especially with --user installs. Actually importing them in
    a fresh subprocess catches that instead of finding out later when
    sensors mysteriously don't work."""
    check = subprocess.run(
        [sys.executable, "-c", "import win32com.client, wmi, win32evtlog"],
        capture_output=True, text=True)
    if check.returncode != 0:
        print("\nNote: pywin32 installed, but its COM helper DLLs might not be "
              "registered yet (a known pywin32/--user quirk). If sensors or "
              "the event log still don't work after this, try running:")
        print(f"  {sys.executable} -m pywin32_postinstall -install")
        print("(You may need to run that command as Administrator.)")


def _registry_python_paths():
    """Looks up Python's own registered install info in the registry
    (PEP 514: HKCU/HKLM \\Software\\Python\\PythonCore\\<version>\\
    InstallPath) - the reliable way to find the REAL python.exe/
    pythonw.exe, independent of how the currently running process was
    launched. This matters because sys.executable can report py.exe
    (the Python Launcher, a separate small executable in its own
    folder, e.g. AppData\\Local\\Programs\\Python\\Launcher\\) instead
    of the real interpreter, when a .py file's double-click
    association routes through it - a real, observed scenario, not a
    hypothetical: elevating and relaunching py.exe directly (rather
    than the real pythonw.exe/python.exe it would have dispatched to)
    produces a stuck, blank console instead of actually running
    anything. Returns (python_exe_or_None, pythonw_exe_or_None)."""
    if not HAVE_WINREG:
        return None, None
    for hive in (winreg.HKEY_CURRENT_USER, winreg.HKEY_LOCAL_MACHINE):
        try:
            core_key = winreg.OpenKey(hive, r"Software\Python\PythonCore")
        except OSError:
            continue
        with core_key:
            i = 0
            while True:
                try:
                    version = winreg.EnumKey(core_key, i)
                except OSError:
                    break
                i += 1
                try:
                    with winreg.OpenKey(core_key, f"{version}\\InstallPath") as ip_key:
                        try:
                            install_dir, _ = winreg.QueryValueEx(ip_key, "")
                        except OSError:
                            install_dir = None

                        def _resolve(value_name, default_filename):
                            try:
                                p, _ = winreg.QueryValueEx(ip_key, value_name)
                                if p and os.path.exists(p):
                                    return p
                            except OSError:
                                pass
                            if install_dir:
                                p = os.path.join(install_dir, default_filename)
                                if os.path.exists(p):
                                    return p
                            return None

                        py_exe = _resolve("ExecutablePath", "python.exe")
                        pyw_exe = _resolve("WindowedExecutablePath", "pythonw.exe")
                        if py_exe or pyw_exe:
                            return py_exe, pyw_exe
                except OSError:
                    continue
    return None, None


def _find_sibling_exe(name):
    p = os.path.join(os.path.dirname(sys.executable), name)
    return p if os.path.exists(p) else None


def find_pythonw():
    _, pyw = _registry_python_paths()
    if pyw:
        return pyw
    return _find_sibling_exe("pythonw.exe") or sys.executable


def find_console_python():
    """The console counterpart of find_pythonw() - needed when spawning
    the installer, which needs a real console for its input() prompts,
    even when the GUI calling this is itself running via pythonw.exe
    with no console at all. Tries the registry first (see
    _registry_python_paths), then a sibling-of-sys.executable search,
    then PATH, before finally giving up and returning sys.executable
    as a last resort - which, if that's actually pythonw.exe or py.exe,
    won't give the installer a working console; there's no way to
    detect that case in advance, so this last resort is genuinely
    best-effort."""
    py, _ = _registry_python_paths()
    if py:
        return py
    found = _find_sibling_exe("python.exe")
    if found:
        return found
    if os.path.basename(sys.executable).lower() == "python.exe":
        return sys.executable
    import shutil
    return shutil.which("python") or sys.executable


def choose_logs_dir():
    step("Log file location")
    default = APP_LOGS_DIR
    path = ask_path("Where should log files be stored?", default)
    os.makedirs(path, exist_ok=True)
    print(f"Logs will be written to: {path}")
    return path


def choose_presentmon_path():
    step("FPS / frame time capture")
    print("This uses PresentMon, a free tool from Intel/GameTechDev, to "
          "capture real per-frame data for FPS, 1% lows, and stutters. It's "
          "a standalone tool (not an installer), so \"downloading\" it is "
          "the whole setup - there's nothing separate to run afterward.")
    found = locate_presentmon()
    if found:
        print(f"Found an existing PresentMon install: {found}")
        if ask_yes_no("Use that one?"):
            return found
    if ask_yes_no("Download it automatically now (from the official "
                   "GameTechDev/PresentMon releases)?"):
        print("Downloading...")
        path = fetch_presentmon()
        if path:
            print(f"Downloaded: {path}")
            return path
        print("Download failed (network issue, or GitHub's release format "
              "changed). You can grab it manually instead.")
    path = ask_path("Path to PresentMon exe (blank to set up later inside the app)", "")
    if path and not os.path.exists(path):
        print("That path doesn't exist - skipping for now, you can set it later.")
        return None
    return path or None


def install_clone(logs_dir, extra_config=None):
    """Install the actual runnable payload under ProgramData.

    The original file can be launched from Downloads, a USB stick, etc.
    That location is treated as an input/source only.  The persistent app,
    config, watchdog, logs, tools, update staging, and crash state all live
    under APP_DATA_DIR so the source folder stays clean.
    """
    step("Installing PC Monitor")
    if not os.path.exists(SOURCE_APP):
        print(f"Can't find this script at {SOURCE_APP} - something odd happened to the file path. Try re-running it.")
        sys.exit(1)

    os.makedirs(APP_DATA_DIR, exist_ok=True)
    os.makedirs(APP_LOGS_DIR, exist_ok=True)
    os.makedirs(APP_TOOLS_DIR, exist_ok=True)
    os.makedirs(APP_UPDATES_DIR, exist_ok=True)
    os.makedirs(APP_EXPORTS_DIR, exist_ok=True)
    os.makedirs(APP_CRASH_DIR, exist_ok=True)

    clone_path = APP_PATH
    tmp_clone = os.path.join(APP_UPDATES_DIR, "pc_monitor.installing")
    with open(SOURCE_APP, "rb") as src, open(tmp_clone, "wb") as dst:
        dst.write(src.read())
    os.replace(tmp_clone, clone_path)

    cfg = dict(CONFIG)
    cfg["logs_dir"] = logs_dir or APP_LOGS_DIR
    cfg["setup_complete"] = True
    if extra_config:
        cfg.update(extra_config)
    _atomic_write_json(CONFIG_PATH, cfg)

    print(f"Installed to: {clone_path}")
    print(f"All PC Monitor runtime files: {APP_DATA_DIR}")
    print("It'll already show up if you search \"PC Monitor\" in the Start Menu.")

    if CONFIG.get("watchdog_enabled", True):
        try:
            if deploy_watchdog(APP_DATA_DIR, clone_path):
                print("Watchdog deployed (PowerShell; on login + every 1 min).")
        except Exception as e:
            print(f"Watchdog deployment failed: {e}")

    if create_startup_shortcut(clone_path):
        print("Added to Startup - it'll launch automatically when you log in.")
    return clone_path


def create_startup_shortcut(clone_path):
    """#5: put a shortcut to the app in the user's Startup folder so it
    launches on login. This - not the watchdog - is what starts the main app
    at boot (the watchdog only relaunches after an update). Best-effort."""
    try:
        import win32com.client
        startup = os.path.join(os.environ["APPDATA"], "Microsoft", "Windows",
                                "Start Menu", "Programs", "Startup")
        os.makedirs(startup, exist_ok=True)
        pythonw = find_pythonw()
        shell = win32com.client.Dispatch("WScript.Shell")
        sc = shell.CreateShortCut(os.path.join(startup, "PC Monitor.lnk"))
        sc.Targetpath = pythonw
        sc.Arguments = f'"{clone_path}"'
        sc.WorkingDirectory = os.path.dirname(clone_path)
        sc.IconLocation = pythonw
        sc.save()
        return True
    except Exception:
        return False


def create_shortcut(clone_path):
    step("Desktop / shortcut")
    if not ask_yes_no("Create a shortcut to it too?"):
        return
    default_dir = os.path.join(os.environ["USERPROFILE"], "Desktop")
    shortcut_dir = ask_path("Where should the shortcut go?", default_dir)
    os.makedirs(shortcut_dir, exist_ok=True)
    shortcut_path = os.path.join(shortcut_dir, "PC Monitor.lnk")

    try:
        import win32com.client
        pythonw = find_pythonw()
        shell = win32com.client.Dispatch("WScript.Shell")
        sc = shell.CreateShortCut(shortcut_path)
        sc.Targetpath = pythonw
        sc.Arguments = f'"{clone_path}"'
        sc.WorkingDirectory = os.path.dirname(clone_path)
        sc.IconLocation = pythonw
        sc.save()
        print(f"Shortcut created: {shortcut_path}")
    except Exception as e:
        print(f"Couldn't create the shortcut ({e}). You can still launch "
              f"the app from the Start Menu, or by running:\n"
              f'  "{find_pythonw()}" "{clone_path}"')


def enable_startup(clone_path):
    step("Launch at login")
    if not ask_yes_no("Start PC Monitor automatically when you log in?"):
        return
    try:
        set_startup_enabled(True, script_path=clone_path)
        print("Enabled via a scheduled task that runs elevated automatically "
              "at login (Task Scheduler, \"Run with highest privileges\") - "
              "any Administrator prompt you just saw covers this "
              "permanently, no prompt on future boots. Turn this off later "
              "from inside the app, or Task Scheduler > Task Scheduler "
              "Library > PCMonitor.")
    except Exception as e:
        print(f"Couldn't set that up ({e}). You can enable it later from "
              "the checkbox inside the app itself instead.")


def offer_lhm():
    step("Hardware sensors (temp / fan / clock / power / voltage)")
    print("This uses LibreHardwareMonitor, a free open-source tool. It's "
          "portable (a zip you extract, no setup wizard). This app reads "
          "sensors from its REST API by default (Options > Remote Web "
          "Server > Run, inside LibreHardwareMonitor once it's open) - "
          "that's the setting that actually matters on current LHM "
          "versions, which no longer support the older WMI method this "
          "app falls back to automatically for older LHM installs. "
          "Administrator rights may still help for some sensors on some "
          "hardware, but the web server toggle is the main thing.")
    found = locate_lhm()
    if not found and ask_yes_no("Download it automatically now (from the "
                                  "official LibreHardwareMonitor/"
                                  "LibreHardwareMonitor releases)?"):
        print("Downloading and extracting...")
        found = fetch_and_install_lhm()
        if found:
            print(f"Ready at: {found}")
        else:
            print("Download failed (network issue, or GitHub's release "
                  "format changed).")
    elif found:
        print(f"Found an existing install: {found}")

    if found:
        already_configured = patch_lhm_config(found)
        if already_configured:
            prompt = ("Launch it now? Found settings saved from a previous "
                       "run and enabled Remote Web Server, Minimize to Tray, "
                       "and minimize-on-close automatically. Windows will "
                       "still show its own Administrator prompt (not "
                       "something this hides), but once approved, "
                       "LibreHardwareMonitor's own window will be hidden "
                       "automatically - nothing left to click")
        else:
            prompt = ("Launch it now? Its window opens normally (there's a "
                       "one-time setup step you'll need it visible for)")
        if ask_yes_no(prompt):
            try:
                launch_elevated(found, minimized=True)
                if already_configured:
                    threading.Thread(target=hide_window_when_ready,
                                       args=("Libre Hardware Monitor",),
                                       daemon=True).start()
                    print("Launched with Remote Web Server, Minimize to "
                          "Tray, and minimize-on-close already enabled from "
                          "your previous settings - its window will hide "
                          "itself automatically once it's up.")
                else:
                    print("Launched. In LibreHardwareMonitor's Options menu, "
                          "check ALL THREE: Remote Web Server > Run (what this "
                          "app reads sensors from), Minimize to Tray (so "
                          "closing its window later tucks it away instead of "
                          "exiting and stopping sensor data), and Run On "
                          "Windows Startup (so it opens itself at boot, no "
                          "Administrator prompt from this app needed each "
                          "time). After this once, future launches will hide "
                          "its window automatically too.")
            except Exception as e:
                print(f"Couldn't launch it automatically ({e}). Run it yourself: {found}")
    else:
        print("You can grab it manually any time: " + LHM_URL)
        if ask_yes_no("Open the download page now?"):
            webbrowser.open(LHM_URL)


def offer_presentmon_download(already_set):
    if already_set:
        return
    step("Get PresentMon")
    print("Grab PresentMon-x.x.x-x64.exe from its GitHub releases if you "
          "want FPS/frame-time data, then use \"Locate PresentMon.exe\" "
          "inside the app to point at it whenever you download it.")
    if ask_yes_no("Open that page now?"):
        webbrowser.open(PRESENTMON_URL)


def _psutil_available():
    """Checks in a fresh subprocess rather than trusting this process's
    own psutil import - the module-level `psutil` name was already
    resolved (possibly to None) at the top of this file before
    install_packages() ever got a chance to run, so it can't reflect
    a pip install that just happened moments ago in this same run."""
    check = subprocess.run([sys.executable, "-c", "import psutil"],
                             capture_output=True, text=True)
    return check.returncode == 0


def offer_launch(clone_path):
    step("All done")
    if not _psutil_available():
        print("psutil isn't installed, so launching now would fail "
              "silently (pythonw.exe has no console to show an error in - "
              "it would just look like nothing happened). Install it, "
              "then run this installer again, or launch manually with:")
        print(f"  {sys.executable} -m pip install --user psutil")
        return
    if ask_yes_no("Launch PC Monitor now?"):
        subprocess.Popen([find_pythonw(), clone_path])
        print("Launched.")


def run_installer():
    if sys.platform != "win32":
        print("This installer is for Windows.")
        sys.exit(1)
    print("PC Monitor setup")
    print("Everything below asks before it does anything.\n")
    install_packages()
    logs_dir = choose_logs_dir()
    presentmon_path = choose_presentmon_path()
    extra = {"presentmon_path": presentmon_path} if presentmon_path else None
    clone_path = install_clone(logs_dir, extra)
    create_shortcut(clone_path)
    enable_startup(clone_path)
    offer_lhm()
    offer_presentmon_download(presentmon_path)
    offer_launch(clone_path)
    # Marks *this* file's own config (wherever it's actually being run
    # from - Downloads, a USB stick, wherever) so running this exact
    # file again skips straight to the GUI instead of reinstalling.
    # The Start Menu clone gets its own "setup_complete" baked in from
    # install_clone() above, independent of this.
    CONFIG["setup_complete"] = True
    _save_config(CONFIG)
    print("\nSetup complete.")


def _version_tuple(v):
    try:
        return tuple(int(x) for x in str(v).strip().split("."))
    except Exception:
        return (0,)


def _update_due(interval_hours):
    """Throttle so we don't hit the network every single launch. Records
    the last check time in a small file next to the script."""
    stamp = os.path.join(APP_DATA_DIR, ".pcmon_lastupdate")
    try:
        last = float(open(stamp).read().strip())
        if time.time() - last < max(0, interval_hours) * 3600:
            return False
    except Exception:
        pass
    try:
        with open(stamp, "w") as f:
            f.write(str(time.time()))
    except Exception:
        pass
    return True


def check_and_apply_update():
    """If auto_update is on and update_url points at a hosted copy of this
    script, fetch it and - only if its APP_VERSION is strictly newer -
    validate it compiles, back up the current file, and replace it in
    place. So you host one file and every friend's copy updates itself;
    you never send a new one again.

    Returns the new version string if the file was replaced (the caller
    should relaunch to run it), else None. Fail-open: any network, parse,
    compile, or permission problem just returns None and the current
    version keeps running - a bad update can never brick a friend's copy,
    and the previous version is always kept as pc_monitor.py.bak."""
    if not CONFIG.get("auto_update", True):
        return None
    url = (CONFIG.get("update_url") or "").strip()
    if not url.startswith(("http://", "https://")):
        return None
    if not _update_due(1 / 60):
        return None
    import urllib.request
    try:
        req = urllib.request.Request(url, headers={"User-Agent": "PCMonitor/%s" % APP_VERSION})
        with urllib.request.urlopen(req, timeout=6) as r:
            remote = r.read().decode("utf-8", errors="ignore")
    except Exception:
        return None
    m = re.search(r'APP_VERSION\s*=\s*["\']([\d.]+)["\']', remote)
    if not m:
        return None
    remote_ver = m.group(1)
    if _version_tuple(remote_ver) <= _version_tuple(APP_VERSION):
        return None
    target = APP_PATH if os.path.exists(APP_PATH) else os.path.abspath(__file__)
    update_dir = APP_UPDATES_DIR
    tmp = os.path.join(update_dir, os.path.basename(target) + ".new")
    bak = os.path.join(update_dir, os.path.basename(target) + ".bak")
    try:
        import py_compile
        import shutil
        os.makedirs(update_dir, exist_ok=True)
        try:
            os.remove(tmp)
        except OSError:
            pass
        with open(tmp, "w", encoding="utf-8") as f:
            f.write(remote)
        py_compile.compile(tmp, doraise=True)  # never trust a broken download
        try:
            shutil.copy2(target, bak)  # keep the old version outside Downloads
        except Exception:
            pass
        os.replace(tmp, target)
        return remote_ver
    except Exception:
        try:
            os.remove(tmp)
        except Exception:
            pass
        return None


def _maybe_self_update():
    """Run at the very top of launch: apply an update if available and,
    unless disabled, relaunch into the new version so it takes effect
    immediately. The --no-update arg on the relaunch prevents any loop.

    Skipped entirely when the external watchdog owns updates - having both
    the running app AND the watchdog try to replace the file is exactly the
    fragile self-replacement this architecture moved away from."""
    if "--no-update" in sys.argv:
        return
    if CONFIG.get("auto_update_via_watchdog", True) and CONFIG.get("watchdog_enabled", True):
        return  # the --watchdog Scheduled Task handles updates (clean stop/restart)
    try:
        newv = check_and_apply_update()
    except Exception:
        newv = None
    if not newv:
        return
    if not CONFIG.get("auto_update_restart", True):
        return  # applied; will run on next launch
    try:
        subprocess.Popen([sys.executable, APP_PATH if os.path.exists(APP_PATH) else os.path.abspath(__file__), "--no-update"]
                         + [a for a in sys.argv[1:] if a != "--no-update"])
    except Exception:
        return
    sys.exit(0)


# ---------------------------------------------------------------------------
# External watchdog: run by a Scheduled Task as `pc_monitor.py --watchdog`
# every minute in this testing build. It OWNS updates (clean stop + replace + restart, so the
# live app never rewrites itself) and detects crashes/kills to relaunch and
# notify. Short-lived: check, act, exit.
# ---------------------------------------------------------------------------
_SINGLE_INSTANCE_HANDLE = None


def ensure_single_instance():
    """#7: prevent overlapping copies of the app (Startup shortcut + a manual
    launch + an update relaunch could all try). A named mutex is the gate:
    - nobody holds it -> we're the sole instance, proceed.
    - a HEALTHY instance holds it (fresh heartbeat + live pid) -> we exit
      quietly so there's no duplicate window.
    - a STALE/zombie holder (hung, dead pid) -> terminate it and take over,
      so a wedged leftover can never block a fresh start.
    Returns True if we may run, False if the caller should exit. Windows-only;
    fails open (returns True) if the mutex API isn't available."""
    global _SINGLE_INSTANCE_HANDLE
    try:
        import ctypes
        k = ctypes.windll.kernel32
        ERROR_ALREADY_EXISTS = 183
        h = k.CreateMutexW(None, False, "Local\\PCMonitorMainInstance")
        if h and k.GetLastError() == ERROR_ALREADY_EXISTS:
            running, hb = _app_running()
            if running:
                return False  # a healthy instance already runs
            if hb and psutil:  # stale/zombie holder -> take over
                try:
                    psutil.Process(int(hb.get("pid"))).terminate()
                except Exception:
                    pass
        _SINGLE_INSTANCE_HANDLE = h  # keep the handle alive for our lifetime
        return True
    except Exception:
        return True  # fail open - better to run than to wrongly block


def _machine_label():
    lbl = (CONFIG.get("machine_label") or "").strip()
    if lbl:
        return lbl
    try:
        import socket
        return socket.gethostname()
    except Exception:
        return "unknown"


def _read_heartbeat():
    try:
        with open(HEARTBEAT_FILE, encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return None


def _app_running():
    """(running_bool, heartbeat) - is a PC Monitor MAIN instance alive?"""
    hb = _read_heartbeat()
    if not hb:
        return False, None
    try:
        pid = int(hb.get("pid", -1))
        fresh = (time.time() - float(hb.get("ts", 0))) <= HEARTBEAT_STALE_SECONDS
        alive = psutil.pid_exists(pid) if psutil else True
        return (fresh and alive), hb
    except Exception:
        return False, hb


def _launch_main_app():
    """Spawn the normal (GUI) instance of this same file, detached so it
    outlives the short-lived watchdog process."""
    try:
        target = APP_PATH if os.path.exists(APP_PATH) else os.path.abspath(__file__)
        py = find_pythonw() or sys.executable
        flags = (getattr(subprocess, "DETACHED_PROCESS", 0)
                 | getattr(subprocess, "CREATE_NEW_PROCESS_GROUP", 0))
        subprocess.Popen([py, target], creationflags=flags, close_fds=True)
        return True
    except Exception:
        return False


def _watchdog_notify(content):
    hook = (CONFIG.get("discord_webhook_url") or "").strip()
    if not hook:
        return
    try:
        post_crash_to_discord(hook, content, [])
    except Exception:
        pass


def _write_update_marker(old_v, new_v):
    """Record the update in a dedicated file in the logs dir (not the active
    session log, to avoid racing the running app), so the trail shows it."""
    try:
        p = os.path.join(LOGS_DIR, "pcmonitor_updates.log")
        with open(p, "a", encoding="utf-8") as f:
            f.write(json.dumps({"ts": datetime.now().isoformat(timespec="seconds"),
                                "event": "update", "from": old_v, "to": new_v,
                                "machine": _machine_label()}) + "\n")
    except Exception:
        pass


def _watchdog_update():
    """Check update_url; if newer, cleanly stop the running app, replace the
    file, relaunch, and notify. Returns the new version or None."""
    if not CONFIG.get("auto_update", True):
        return None
    url = (CONFIG.get("update_url") or "").strip()
    if not url.startswith(("http://", "https://")):
        return None
    import urllib.request
    try:
        req = urllib.request.Request(url, headers={"User-Agent": "PCMonitorWatchdog/%s" % APP_VERSION})
        with urllib.request.urlopen(req, timeout=8) as r:
            remote = r.read().decode("utf-8", errors="ignore")
    except Exception:
        return None
    m = re.search(r'APP_VERSION\s*=\s*["\']([\d.]+)["\']', remote)
    if not m or _version_tuple(m.group(1)) <= _version_tuple(APP_VERSION):
        return None
    remote_ver = m.group(1)
    # ask the running app to close cleanly, then wait for it to actually go
    running, hb = _app_running()
    if running:
        try:
            open(EXIT_REQUEST_FILE, "w").close()
        except OSError:
            pass
        for _ in range(20):
            time.sleep(1)
            if not _app_running()[0]:
                break
        running2, hb2 = _app_running()
        if running2 and hb2 and psutil:  # ignored the request -> force it
            try:
                psutil.Process(int(hb2.get("pid"))).terminate()
            except Exception:
                pass
        try:
            os.remove(EXIT_REQUEST_FILE)
        except OSError:
            pass
    # replace the file (validated + backed up, same rules as check_and_apply_update)
    target = APP_PATH if os.path.exists(APP_PATH) else os.path.abspath(__file__)
    os.makedirs(APP_UPDATES_DIR, exist_ok=True)
    tmp = os.path.join(APP_UPDATES_DIR, os.path.basename(target) + ".new")
    bak = os.path.join(APP_UPDATES_DIR, os.path.basename(target) + ".bak")
    try:
        import py_compile
        import shutil
        with open(tmp, "w", encoding="utf-8") as f:
            f.write(remote)
        py_compile.compile(tmp, doraise=True)
        try:
            shutil.copy2(target, bak)
        except Exception:
            pass
        os.replace(tmp, target)
    except Exception:
        try:
            os.remove(tmp)
        except Exception:
            pass
        return None
    _write_update_marker(APP_VERSION, remote_ver)
    _watchdog_notify(f"PC Monitor updated {APP_VERSION} -> {remote_ver} on `{_machine_label()}`. RustDesk health/update will run on the new version. Restarting.")
    _launch_main_app()
    return remote_ver


def run_watchdog():
    try:
        if _watchdog_update():
            return  # updated + relaunched; done this run
    except Exception:
        pass
    try:
        state_file = os.path.join(APP_DATA_DIR, "pcmonitor_watchdog_state.json")
        prev_running = False
        try:
            with open(state_file, encoding="utf-8") as f:
                prev_running = bool(json.load(f).get("running"))
        except Exception:
            prev_running = False
        now_running, hb = _app_running()
        if now_running != prev_running:
            if not now_running:
                # running -> stopped (crash/kill if heartbeat lingered, else clean)
                if os.path.exists(HEARTBEAT_FILE):
                    _watchdog_notify(f"PC Monitor STOPPED on `{_machine_label()}` (crash or task killed).")
                    try:
                        os.remove(HEARTBEAT_FILE)
                    except OSError:
                        pass
                else:
                    _watchdog_notify(f"PC Monitor STOPPED on `{_machine_label()}` (closed).")
            try:
                _atomic_write_json(state_file, {"running": now_running})
            except Exception:
                pass
    except Exception:
        pass


def _watchdog_paths(script_dir=None):
    # Watchdog/config files are machine state, never files beside the running
    # Python payload.  Keeping them in ProgramData prevents Downloads (or a
    # Start Menu folder) from accumulating mutable support files.
    os.makedirs(APP_DATA_DIR, exist_ok=True)
    return (os.path.join(APP_DATA_DIR, "pcmonitor_watchdog.ps1"),
            os.path.join(APP_DATA_DIR, "pcmonitor_watchdog.ver"),
            os.path.join(APP_DATA_DIR, "pcmonitor_config.json"))


def deploy_watchdog(script_dir, script_path=None):
    """Write the embedded PowerShell watchdog to disk next to the script,
    make sure the config it reads has the interpreter paths, and register
    the Scheduled Task to run it. This is the '.py deploys the watchdog'
    half of the cross-update."""
    if not CONFIG.get("watchdog_enabled", True):
        return False
    ps1_path, ver_path, cfg_path = _watchdog_paths(script_dir)
    try:
        # ensure the config the PS reads has what it needs (the PS can't see
        # Python's in-memory DEFAULT_CONFIG, only the JSON file)
        try:
            cfg = {}
            if os.path.exists(cfg_path):
                with open(cfg_path, encoding="utf-8") as f:
                    cfg = json.load(f)
        except Exception:
            cfg = {}
        merged = dict(CONFIG)
        merged.update(cfg)  # file wins for anything already set there
        merged["python_exe"] = find_pythonw() or sys.executable
        merged["python_console_exe"] = _find_console_python()
        _atomic_write_json(cfg_path, merged)
        # write the watchdog + a windowless VBScript launcher + version stamp
        with open(ps1_path, "w", encoding="utf-8") as f:
            f.write(WATCHDOG_PS1)
        vbs_path = os.path.join(APP_DATA_DIR, "pcmonitor_watchdog_launch.vbs")
        with open(vbs_path, "w", encoding="utf-8") as f:
            f.write(WATCHDOG_VBS)
        with open(ver_path, "w", encoding="utf-8") as f:
            f.write(WATCHDOG_VERSION)
        # register the task to run the watchdog THROUGH wscript.exe (no console
        # window at all), so it never flashes a PowerShell window every cycle.
        # wscript is on the system PATH; quoting only the .vbs path avoids the
        # nested-quote issues that can make a scheduled task silently not run.
        interval = 1
        tr = 'wscript "%s"' % vbs_path

        # Do NOT ignore schtasks failures.  The old code returned True even
        # when Windows rejected the task (for example because an older task
        # had a bad action/security context).  That made the GUI say the
        # watchdog was installed when nothing would actually run.
        def _create_task(name, schedule, extra=None):
            cmd = ["schtasks", "/Create", "/TN", name, "/TR", tr,
                   "/SC", schedule, "/F"]
            if schedule == "MINUTE":
                cmd += ["/MO", str(interval)]
            if extra:
                cmd += extra
            r = subprocess.run(cmd, capture_output=True, text=True,
                               creationflags=CREATE_NO_WINDOW, timeout=15)
            out = ((r.stdout or "") + " " + (r.stderr or "")).strip()
            _remote_log(f"WATCHDOG TASK {name} rc={r.returncode} output={out!r}")
            if r.returncode != 0:
                raise RuntimeError(f"schtasks failed for {name}: {out or 'no output'}")

        _create_task("PCMonitorWatchdog", "MINUTE")
        _create_task("PCMonitorWatchdogLogon", "ONLOGON")

        # Verify that Windows actually registered the primary task and that
        # its action points at the launcher we just wrote.  This catches
        # quoting/path problems that /Create can otherwise leave ambiguous.
        verify = subprocess.run(
            ["schtasks", "/Query", "/TN", "PCMonitorWatchdog", "/V", "/FO", "LIST"],
            capture_output=True, text=True, creationflags=CREATE_NO_WINDOW, timeout=15)
        if verify.returncode != 0:
            raise RuntimeError("PCMonitorWatchdog was not registered")
        if os.path.normcase(vbs_path) not in os.path.normcase(verify.stdout or ""):
            _remote_log("WATCHDOG TASK verification warning: expected VBS path was not visible in task query")
        return True
    except Exception:
        return False


def _find_console_python():
    """A console python.exe (for the watchdog's py_compile validation, which
    needs an exit code) - derive it from the windowed interpreter."""
    exe = sys.executable or ""
    if exe.lower().endswith("pythonw.exe"):
        cand = exe[:-len("pythonw.exe")] + "python.exe"
        if os.path.exists(cand):
            return cand
    if exe.lower().endswith("python.exe"):
        return exe
    pw = find_pythonw() or ""
    if pw.lower().endswith("pythonw.exe"):
        cand = pw[:-len("pythonw.exe")] + "python.exe"
        if os.path.exists(cand):
            return cand
    return "python"


def sync_watchdog(script_dir, script_path=None):
    """Keep the on-disk watchdog synchronized with this app.

    The watchdog is rewritten/re-registered on every app startup so the
    Scheduled Task always matches the embedded copy.  A Discord notification
    is sent ONLY when the deployed watchdog version actually changes (or when
    no version stamp existed yet).  This avoids spamming Discord on every
    normal PC Monitor launch while still proving that a new watchdog was
    deployed after an app update.
    """
    if not CONFIG.get("watchdog_enabled", True):
        return False
    try:
        _ps1_path, ver_path, _cfg_path = _watchdog_paths(script_dir)
        old_ver = None
        try:
            if os.path.exists(ver_path):
                with open(ver_path, encoding="utf-8") as f:
                    old_ver = f.read().strip() or None
        except Exception:
            old_ver = None

        ok = deploy_watchdog(script_dir, script_path)
        if not ok:
            _remote_log(
                f"WATCHDOG SYNC FAILED expected={WATCHDOG_VERSION} old={old_ver!r}"
            )
            return False

        changed = old_ver != WATCHDOG_VERSION
        _remote_log(
            f"WATCHDOG SYNC OK old={old_ver!r} new={WATCHDOG_VERSION!r} changed={changed}"
        )
        if changed:
            _watchdog_notify(
                f"Watchdog updated {old_ver or 'none'} -> {WATCHDOG_VERSION} "
                f"on `{_machine_label()}`."
            )
        return True
    except Exception as e:
        try:
            _remote_log(f"WATCHDOG SYNC EXCEPTION: {e}")
        except Exception:
            pass
        return False


def _legacy_sync_watchdog_unused(script_dir, script_path=None):
    # kept for reference (the old version-gated behaviour that could get stuck)
    if not CONFIG.get("watchdog_enabled", True):
        return
    ps1_path, ver_path, _ = _watchdog_paths(script_dir)
    try:
        on_disk = None
        if os.path.exists(ver_path):
            with open(ver_path, encoding="utf-8") as f:
                on_disk = f.read().strip()
        if (not os.path.exists(ps1_path)) or on_disk != WATCHDOG_VERSION:
            deploy_watchdog(script_dir, script_path)
    except Exception:
        pass


def register_watchdog_task(script_path=None):
    """Create/refresh the Scheduled Task that runs the watchdog every 1 minute.
    Points at the persistent ProgramData app when available."""
    if not CONFIG.get("watchdog_enabled", True):
        return False
    try:
        py = find_pythonw() or sys.executable
        target = os.path.abspath(script_path or __file__)
        interval = 1
        tr = f'"{py}" "{target}" --watchdog'
        subprocess.run(["schtasks", "/Create", "/TN", "PCMonitorWatchdog",
                        "/TR", tr, "/SC", "MINUTE", "/MO", str(interval), "/F"],
                       capture_output=True, creationflags=CREATE_NO_WINDOW, timeout=15)
        return True
    except Exception:
        return False


def _crash_log_path():
    """Store the fatal-startup trail in the central app-data directory so a
    silent startup death leaves a readable trail even under pythonw.exe."""
    os.makedirs(APP_DATA_DIR, exist_ok=True)
    return os.path.join(APP_DATA_DIR, "pc_monitor_crash.log")


def _log_fatal(text):
    try:
        with open(_crash_log_path(), "a", encoding="utf-8") as f:
            f.write("\n===== " + datetime.now().isoformat() + " =====\n")
            f.write(text.rstrip() + "\n")
    except Exception:
        pass


def _hide_console_window():
    """When a .py is double-clicked through python.exe (not pythonw.exe),
    Windows opens a console window - the black 'blank window' that flashes
    before the GUI. On the GUI path we don't need it, so hide it outright
    so there's no stray window to see close."""
    try:
        import ctypes
        hwnd = ctypes.windll.kernel32.GetConsoleWindow()
        if hwnd:
            ctypes.windll.user32.ShowWindow(hwnd, 0)  # SW_HIDE
    except Exception:
        pass


def _run_gui_guarded():
    """Builds and runs the GUI with a top-level guard. Without this, any
    exception during App() construction shows as exactly the reported
    symptom - a window appears, does a little, then vanishes with no error
    - because under pythonw.exe there's no console for the traceback to
    print to. Here every failure path (construction, Tk callbacks, the
    main loop) is written to pc_monitor_crash.log and shown in a dialog,
    so 'it just closes' becomes something you can actually read."""
    import traceback
    # #7: bow out if a healthy instance is already running (or take over a
    # stale one). Done here so it covers every GUI launch path.
    if not ensure_single_instance():
        sys.exit(0)
    try:
        app = App()
    except Exception:
        tb = traceback.format_exc()
        _log_fatal(tb)
        try:
            last = tb.strip().splitlines()[-1]
            messagebox.showerror(
                "PC Monitor failed to start",
                "PC Monitor hit an error while starting and couldn't open.\n\n"
                + last + "\n\nFull details saved to:\n" + _crash_log_path())
        except Exception:
            pass
        sys.exit(1)

    # Exceptions raised inside Tk callbacks (the poll pump, button handlers)
    # otherwise go to a stderr that doesn't exist under pythonw - log them
    # instead of letting them disappear. Tkinter calls this as
    # self.report_callback_exception(exc, val, tb).
    def _tk_report(exc, val, tb_):
        _log_fatal("".join(traceback.format_exception(exc, val, tb_)))
    app.report_callback_exception = _tk_report

    try:
        app.mainloop()
    except Exception:
        _log_fatal(traceback.format_exc())
        raise



# ---------------------------------------------------------------------------
# Optional unattended remote-access host (RustDesk)
#
# This is deliberately separate from PC Monitor's own setup_complete flag.
# A machine can have PC Monitor fully configured while remote access is still
# being installed for the first time.  The remote state lives under
# %PROGRAMDATA% so PC Monitor's Start Menu clone and auto-updater all see the
# same state.
REMOTE_RUSTDESK_VERSION = "1.4.9"
REMOTE_INSTALL_DIR = os.path.join(
    os.environ.get("PROGRAMDATA", SCRIPT_DIR), "PCMonitorRemote")
REMOTE_STATE_PATH = os.path.join(REMOTE_INSTALL_DIR, "state.json")
REMOTE_LOCK_PATH = os.path.join(REMOTE_INSTALL_DIR, "setup.lock")
REMOTE_LOG_PATH = os.path.join(REMOTE_INSTALL_DIR, "remote_setup.log")
REMOTE_INSTALLER = os.path.join(REMOTE_INSTALL_DIR, "rustdesk-installer.exe")
REMOTE_EXE = os.path.join(
    os.environ.get("ProgramFiles", r"C:\\Program Files"),
    "RustDesk", "rustdesk.exe")
REMOTE_LAST_STAGE = "startup"


def _remote_log(message):
    """Append detailed remote-setup diagnostics to a dedicated local log."""
    try:
        os.makedirs(REMOTE_INSTALL_DIR, exist_ok=True)
        with open(REMOTE_LOG_PATH, "a", encoding="utf-8") as f:
            f.write(f"[{datetime.now().isoformat(timespec='seconds')}] {message.rstrip()}\n")
    except Exception:
        pass


def _remote_stage(stage):
    global REMOTE_LAST_STAGE
    REMOTE_LAST_STAGE = stage
    _remote_log("STAGE: " + stage)


def _remote_redact_args(args):
    vals = [str(x) for x in args]
    out = []
    hide_next = False
    for value in vals:
        if hide_next:
            out.append("<redacted>")
            hide_next = False
        else:
            out.append(value)
            if value == "--password":
                hide_next = True
    return out


def _remote_password(length=16):
    alphabet = string.ascii_letters + string.digits
    return "".join(secrets.choice(alphabet) for _ in range(length))


def _remote_webhook(content):
    hook = (CONFIG.get("discord_webhook_url") or "").strip()
    if not hook:
        _remote_log("WEBHOOK skipped: discord_webhook_url is empty")
        return False
    payload = json.dumps({"content": content}).encode("utf-8")
    for attempt in range(1, 4):
        try:
            req = urllib.request.Request(
                hook,
                data=payload,
                headers={
                    "Content-Type": "application/json",
                    "User-Agent": f"PCMonitorRemote/{APP_VERSION}",
                },
                method="POST",
            )
            with urllib.request.urlopen(req, timeout=15) as r:
                body = r.read()
                status = getattr(r, "status", None) or r.getcode()
            _remote_log(f"WEBHOOK success attempt={attempt} http_status={status} response_bytes={len(body)}")
            return 200 <= int(status) < 300
        except Exception as e:
            _remote_log(f"WEBHOOK failed attempt={attempt} error={type(e).__name__}: {e}")
            try:
                _log_fatal("Remote webhook error: " + repr(e))
            except Exception:
                pass
            if attempt < 3:
                time.sleep(2)
    return False


def _remote_notify_ready(state, force=False, reason="setup"):
    """Send saved RustDesk credentials to Discord.

    Normal startup sends once per PC Monitor version (or after a failed
    delivery). force=True is used by the in-app Resend Credentials button.
    """
    rid = str(state.get("rustdesk_id") or "").strip()
    password = str(state.get("password") or "").strip()
    if not rid or not password:
        _remote_log("READY notification skipped: state missing RustDesk ID/password")
        return False
    label = _machine_label() if "_machine_label" in globals() else os.environ.get(
        "COMPUTERNAME", platform.node())
    previous_app_version = str(state.get("credentials_notified_app_version") or "").strip()
    # New confirmation marker: old builds could mark/skip delivery before the
    # credentials were actually confirmed by this fixed delivery path.
    confirmed_version = str(state.get("credentials_delivery_confirmed_version") or "").strip()
    if not force and confirmed_version == str(APP_VERSION):
        _remote_log(f"READY notification skipped: delivery already confirmed for PC Monitor {APP_VERSION}")
        return True
    _remote_stage("send saved RustDesk credentials to Discord")
    ok = _remote_webhook(
        "🟢 **PC MONITOR + REMOTE PC READY**\n"
        f"Machine: `{label}`\n"
        f"RustDesk ID: `{rid}`\n"
        f"Password: `{password}`\n"
        "Status: **UNATTENDED ACCESS READY**\n"
        f"RustDesk: `v{state.get('rustdesk_version') or REMOTE_RUSTDESK_VERSION}`\n"
        f"PC Monitor: `v{APP_VERSION}`\n"
        f"Reason: `{reason}`")
    if ok:
        state["discord_notified"] = True
        state["credentials_notified_app_version"] = str(APP_VERSION)
        state["credentials_delivery_confirmed_version"] = str(APP_VERSION)
        state["credentials_last_notified"] = datetime.now().isoformat(timespec="seconds")
        try:
            with open(REMOTE_STATE_PATH, "w", encoding="utf-8") as f:
                json.dump(state, f, indent=2)
        except Exception as e:
            _remote_log(f"READY notification sent but state update failed: {type(e).__name__}: {e}")
        return True
    return False


def _remote_read_state():
    try:
        with open(REMOTE_STATE_PATH, encoding="utf-8") as f:
            return json.load(f)
    except Exception as e:
        _remote_log(f"state read failed: {type(e).__name__}: {e}")
        return None


def _remote_resend_credentials():
    """Force a fresh Discord delivery of the saved RustDesk credentials."""
    state = _remote_read_state()
    if not state or not state.get("rustdesk_id") or not state.get("password"):
        _remote_log("RESEND requested but saved RustDesk credentials are missing")
        return False
    return _remote_notify_ready(state, force=True, reason="manual resend")


def _remote_credential_delivery_worker():
    """Deliver saved RustDesk credentials independently of RustDesk setup.

    This handles the exact failure mode where RustDesk is already installed but
    the setup thread was skipped/delayed/not elevated. It also waits for a
    first-time setup to write state, then sends immediately.
    """
    if os.environ.get("PCMONITOR_DISABLE_REMOTE") == "1":
        return
    for attempt in range(1, 25):
        try:
            state = _remote_read_state()
            if state and state.get("rustdesk_id") and state.get("password"):
                ok = _remote_notify_ready(state, force=False, reason="PC Monitor startup/update")
                if ok:
                    _remote_log(f"CREDENTIAL DELIVERY worker confirmed attempt={attempt}")
                    return True
                _remote_log(f"CREDENTIAL DELIVERY worker retry attempt={attempt}")
            else:
                _remote_log(f"CREDENTIAL DELIVERY waiting for RustDesk state attempt={attempt}")
        except Exception as e:
            _remote_log(f"CREDENTIAL DELIVERY worker exception attempt={attempt}: {type(e).__name__}: {e}")
        time.sleep(5)
    _remote_log("CREDENTIAL DELIVERY worker exhausted retries")
    return False


def _remote_service_prepare():
    """Install, configure for automatic boot, and start the RustDesk service."""
    _remote_stage("install/configure RustDesk Windows service")
    install_result = _remote_run([REMOTE_EXE, "--install-service"], timeout=90)
    if install_result.returncode != 0:
        check = _remote_run(["sc", "query", "Rustdesk"], timeout=20)
        if check.returncode != 0:
            raise RuntimeError(install_result.stderr.strip() or install_result.stdout.strip() or "RustDesk --install-service failed")
    auto_result = _remote_run(["sc", "config", "Rustdesk", "start=", "auto"], timeout=30)
    if auto_result.returncode != 0:
        raise RuntimeError(auto_result.stderr.strip() or auto_result.stdout.strip() or "Could not configure RustDesk service for automatic startup")
    _remote_stage("start RustDesk service")
    running = False
    for attempt in range(1, 13):
        check = _remote_run(["sc", "query", "Rustdesk"], timeout=20)
        text = (check.stdout or "") + "\n" + (check.stderr or "")
        if "RUNNING" in text.upper():
            running = True
            _remote_log(f"service running on attempt={attempt}")
            break
        start_result = _remote_run(["sc", "start", "Rustdesk"], timeout=30)
        if start_result.returncode not in (0, 1056):
            _remote_log(f"sc start returned rc={start_result.returncode}")
        time.sleep(2)
    if not running:
        raise RuntimeError("RustDesk service did not reach RUNNING state")


def _remote_upgrade_if_needed(state):
    """Upgrade RustDesk when this PC Monitor build carries a newer target."""
    installed_version = str(state.get("rustdesk_version") or "").strip()
    if installed_version == REMOTE_RUSTDESK_VERSION and os.path.exists(REMOTE_EXE):
        return False
    _remote_stage(f"update RustDesk {installed_version or 'unknown'} -> {REMOTE_RUSTDESK_VERSION}")
    asset = _remote_asset()
    url = f"https://github.com/rustdesk/rustdesk/releases/download/{REMOTE_RUSTDESK_VERSION}/{asset}"
    _remote_download(url, REMOTE_INSTALLER)
    result = _remote_run([REMOTE_INSTALLER, "--silent-install"], timeout=180)
    if result.returncode != 0:
        _remote_log(f"RustDesk upgrade returned rc={result.returncode}; verifying executable")
    time.sleep(5)
    candidates = [REMOTE_EXE, os.path.join(os.environ.get("ProgramFiles(x86)", r"C:\Program Files (x86)"), "RustDesk", "rustdesk.exe")]
    existing = next((x for x in candidates if os.path.exists(x)), None)
    if existing:
        globals()["REMOTE_EXE"] = existing
    if not os.path.exists(REMOTE_EXE):
        raise RuntimeError("RustDesk update finished but rustdesk.exe was not found")
    state["rustdesk_version"] = REMOTE_RUSTDESK_VERSION
    _remote_log(f"RustDesk update verified exe={REMOTE_EXE}")
    return True


def _remote_download(url, destination):
    _remote_stage("download RustDesk installer")
    _remote_log(f"DOWNLOAD url={url} destination={destination}")
    os.makedirs(os.path.dirname(destination), exist_ok=True)
    req = urllib.request.Request(url, headers={"User-Agent": "PCMonitorRemote/2.8"})
    with urllib.request.urlopen(req, timeout=90) as response, open(destination, "wb") as out:
        while True:
            block = response.read(1024 * 1024)
            if not block:
                break
            out.write(block)
    try:
        _remote_log(f"DOWNLOAD complete bytes={os.path.getsize(destination)}")
    except Exception:
        pass


def _remote_run(args, timeout=120):
    safe_args = _remote_redact_args(args)
    _remote_log(f"RUN timeout={timeout}s args={safe_args}")
    try:
        result = subprocess.run(
            [str(x) for x in args],
            capture_output=True,
            text=True,
            timeout=timeout,
            creationflags=CREATE_NO_WINDOW,
        )
        _remote_log(
            f"RESULT rc={result.returncode} stdout={(result.stdout or '').strip()!r} "
            f"stderr={(result.stderr or '').strip()!r}"
        )
        return result
    except Exception as e:
        _remote_log(f"RUN EXCEPTION {type(e).__name__}: {e}")
        raise


def _remote_asset():
    machine = platform.machine().lower()
    if "arm64" in machine or "aarch64" in machine:
        return f"rustdesk-{REMOTE_RUSTDESK_VERSION}-aarch64.exe"
    if platform.architecture()[0] == "32bit":
        return f"rustdesk-{REMOTE_RUSTDESK_VERSION}-x86-sciter.exe"
    return f"rustdesk-{REMOTE_RUSTDESK_VERSION}-x86_64.exe"


def _remote_get_id():
    _remote_stage("retrieve RustDesk ID")
    last_text = ""
    for attempt in range(1, 16):
        try:
            p = _remote_run([REMOTE_EXE, "--get-id"], timeout=20)
            text = (p.stdout or "") + "\n" + (p.stderr or "")
            last_text = text.strip()
            _remote_log(f"GET-ID attempt={attempt} combined_output={last_text!r}")
            for line in text.splitlines():
                value = line.strip()
                if value and value.replace("-", "").replace(" ", "").isdigit():
                    _remote_log(f"GET-ID success id={value}")
                    return value
        except Exception as e:
            _remote_log(f"GET-ID attempt={attempt} exception={type(e).__name__}: {e}")
        time.sleep(2)
    _remote_log(f"GET-ID failed after 15 attempts; last_output={last_text!r}")
    return ""


def _remote_install_host():
    """Install, repair, update, and validate the unattended RustDesk host."""
    global REMOTE_LAST_STAGE
    if sys.platform != "win32":
        _remote_log("ABORT non-Windows platform")
        return False
    _remote_stage("remote bootstrap start")
    _remote_log(f"version={APP_VERSION} rustdesk_target={REMOTE_RUSTDESK_VERSION} pid={os.getpid()} admin={IS_ADMIN}")
    os.makedirs(REMOTE_INSTALL_DIR, exist_ok=True)
    lock_acquired = False
    lock_handle = None
    try:
        _remote_stage("acquire setup lock")
        try:
            lock_handle = os.open(REMOTE_LOCK_PATH, os.O_CREAT | os.O_EXCL | os.O_WRONLY)
            lock_acquired = True
            with os.fdopen(lock_handle, "w", encoding="utf-8") as f:
                f.write(str(os.getpid()))
            lock_handle = None
        except FileExistsError:
            _remote_log("another PC Monitor process owns setup.lock; exiting this bootstrap")
            return False
        state = _remote_read_state() or {}
        candidates = [REMOTE_EXE, os.path.join(os.environ.get("ProgramFiles(x86)", r"C:\Program Files (x86)"), "RustDesk", "rustdesk.exe")]
        existing = next((x for x in candidates if os.path.exists(x)), None)
        if existing:
            globals()["REMOTE_EXE"] = existing
            _remote_log(f"found existing RustDesk executable: {existing}")
        if not existing:
            _remote_stage("install RustDesk silently")
            asset = _remote_asset()
            url = f"https://github.com/rustdesk/rustdesk/releases/download/{REMOTE_RUSTDESK_VERSION}/{asset}"
            _remote_download(url, REMOTE_INSTALLER)
            result = _remote_run([REMOTE_INSTALLER, "--silent-install"], timeout=180)
            if result.returncode != 0:
                _remote_log(f"RustDesk silent install returned rc={result.returncode}; verifying executable")
            time.sleep(5)
            existing = next((x for x in candidates if os.path.exists(x)), None)
            if existing:
                globals()["REMOTE_EXE"] = existing
            if not os.path.exists(REMOTE_EXE):
                raise RuntimeError(result.stderr.strip() or result.stdout.strip() or "RustDesk installer finished but rustdesk.exe was not found")
        if state.get("rustdesk_version") != REMOTE_RUSTDESK_VERSION:
            _remote_upgrade_if_needed(state)
        _remote_service_prepare()
        password = str(state.get("password") or "").strip() or _remote_password()
        _remote_stage("set permanent RustDesk password")
        result = _remote_run([REMOTE_EXE, "--password", password], timeout=60)
        if result.returncode != 0:
            raise RuntimeError(result.stderr.strip() or result.stdout.strip() or "Could not set remote password")
        time.sleep(2)
        rid = _remote_get_id()
        if not rid:
            raise RuntimeError("Could not obtain RustDesk ID")
        old_id = str(state.get("rustdesk_id") or "").strip()
        state.update({
            "rustdesk_id": rid,
            "password": password,
            "computer": os.environ.get("COMPUTERNAME", platform.node()),
            "rustdesk_version": REMOTE_RUSTDESK_VERSION,
            "last_pc_monitor_version": str(APP_VERSION),
            "service_auto_start": True,
            "last_health_check": datetime.now().isoformat(timespec="seconds"),
        })
        _remote_stage("write remote state")
        with open(REMOTE_STATE_PATH, "w", encoding="utf-8") as f:
            json.dump(state, f, indent=2)
        if old_id and old_id != rid:
            _remote_log(f"RustDesk ID changed {old_id} -> {rid}")
        if not _remote_notify_ready(state, force=False, reason="PC Monitor startup/update"):
            _remote_log("RustDesk health/setup succeeded, but Discord delivery failed; next launch or manual resend will retry")
        _remote_stage("remote setup complete")
        return True
    except Exception as e:
        _remote_log(f"FAILED stage={REMOTE_LAST_STAGE} error={type(e).__name__}: {e}")
        try: _log_fatal("Remote host setup failed: " + repr(e))
        except Exception: pass
        try:
            label = _machine_label() if "_machine_label" in globals() else os.environ.get("COMPUTERNAME", platform.node())
            _remote_webhook("🔴 **PC MONITOR REMOTE SETUP FAILED**\n" f"Machine: `{label}`\n" f"Stage: `{REMOTE_LAST_STAGE}`\n" f"Error: `{type(e).__name__}: {e}`\n" f"Local log: `{REMOTE_LOG_PATH}`")
        except Exception: pass
        return False
    finally:
        if lock_handle is not None:
            try: os.close(lock_handle)
            except Exception: pass
        if lock_acquired:
            try: os.remove(REMOTE_LOCK_PATH)
            except OSError: pass


def _ensure_remote_host_async(wait=False):
    """Start remote setup without making normal PC Monitor startup wait."""
    if os.environ.get("PCMONITOR_DISABLE_REMOTE") == "1":
        return
    try:
        t = threading.Thread(
            target=_remote_install_host,
            name="RemoteHostSetup",
            daemon=not wait,
        )
        t.start()
        if wait:
            t.join()
    except Exception:
        pass

if __name__ == "__main__":
    # --watchdog: run by the Scheduled Task. Do the watchdog work (update
    # check + crash/kill detection + relaunch) and exit; never open the GUI.
    if "--watchdog" in sys.argv:
        try:
            run_watchdog()
        except Exception:
            pass
        sys.exit(0)

    # Self-update: only used as a fallback when the external watchdog isn't
    # handling updates (see _maybe_self_update - it no-ops under the watchdog).
    _maybe_self_update()

    force_install = len(sys.argv) > 1 and sys.argv[1] in ("install", "--install", "-install")
    if force_install or not CONFIG.get("setup_complete"):
        # The installer needs a real console for its input() prompts.
        # Double-clicking a .py file can route through either python.exe
        # (has a console) or pythonw.exe (doesn't, and input() would just
        # hang or fail silently there) depending on how Python was set up
        # - not something to assume. sys.stdin is None is the reliable
        # signal for "no console attached at all" (how pythonw.exe shows
        # up). If that's the case, relaunch this exact invocation through
        # a console-guaranteeing python.exe instead of limping along
        # without one.
        if sys.stdin is None:
            try:
                console_python = find_console_python()
                subprocess.Popen([console_python, os.path.abspath(__file__)] + sys.argv[1:],
                                   creationflags=CREATE_NEW_CONSOLE)
            except Exception:
                pass  # nothing more we can do without a console to report through
            sys.exit(0)
        # The persistent installation lives under ProgramData, so elevation
        # is required BEFORE the installer writes its payload/config/watchdog.
        if not IS_ADMIN:
            try:
                if relaunch_as_admin():
                    sys.exit(0)
            except Exception:
                pass
        run_installer()
        if IS_ADMIN:
            _ensure_remote_host_async(wait=True)
    else:
        # Normal launches start remote setup only after the existing
        # PC Monitor elevation step below.
        if psutil is None:
            # print() is invisible under pythonw/a hidden console, so also
            # show a dialog - otherwise this too looks like a silent close.
            print("Missing dependency. Run: pip install psutil")
            try:
                messagebox.showerror(
                    "PC Monitor - missing dependency",
                    "psutil isn't installed, so PC Monitor can't run.\n\n"
                    "Install it, then relaunch:\n"
                    "    pip install psutil")
            except Exception:
                pass
            sys.exit(1)
        if not IS_ADMIN:
            # Auto-elevate on every launch rather than opening non-elevated
            # and waiting for a manual "Restart as Administrator" click -
            # this still goes through Windows' own UAC prompt every time
            # (including at every boot if launched via Start with Windows -
            # there's no way around that, Windows doesn't let a process
            # silently re-elevate without asking). If elevation didn't
            # actually go through (declined, or blocked), fall through and
            # open non-elevated anyway rather than leaving nothing running -
            # the in-app banner/button are still there as a manual fallback.
            try:
                if relaunch_as_admin():
                    sys.exit(0)
            except Exception:
                pass
        # RustDesk host setup must run elevated. The previous build started
        # it before relaunch_as_admin(), so a normal auto-update could launch
        # the setup unelevated and silently fail.
        if IS_ADMIN:
            _ensure_remote_host_async(wait=False)

        # This is the process that actually shows the GUI (elevated, or the
        # non-elevated fallback). Drop any leftover console window and run
        # under a crash guard so a startup failure is visible, not silent.
        _hide_console_window()
        _run_gui_guarded()
