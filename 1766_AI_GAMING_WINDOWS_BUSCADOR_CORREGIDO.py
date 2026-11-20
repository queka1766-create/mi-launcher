"""1766 AI GAMING — launcher gamer personal para Windows (Python 3.10+)."""
from __future__ import annotations

import ctypes
import colorsys
import base64
import json
import math
import os
import re
import sqlite3
import subprocess
import threading
import zipfile
import xml.etree.ElementTree as ET
import time
import urllib.error
import urllib.request
import uuid
import tkinter as tk
from pathlib import Path
from tkinter import filedialog, messagebox, ttk

APP_DIR = Path(__file__).resolve().parent
DATA_DIR = Path(os.environ.get("LOCALAPPDATA", str(APP_DIR))) / "1766TBD"
LEGACY_GAMES_FILE = Path(os.environ.get("LOCALAPPDATA", str(APP_DIR))) / "NexusLauncher" / "games.json"
GAMES_FILE = DATA_DIR / "games.json"
ACCENT = "#29d9ff"
PS_BLUE = "#29d9ff"
BG = "#040711"
PANEL = "#0a1120"
MUTED = "#8798b5"

XINPUT_DPAD_UP, XINPUT_DPAD_DOWN = 0x0001, 0x0002
XINPUT_DPAD_LEFT, XINPUT_DPAD_RIGHT = 0x0004, 0x0008
XINPUT_A, XINPUT_B, XINPUT_X, XINPUT_Y = 0x1000, 0x2000, 0x4000, 0x8000


class XINPUT_GAMEPAD(ctypes.Structure):
    _fields_ = [("wButtons", ctypes.c_ushort), ("bLeftTrigger", ctypes.c_ubyte),
                ("bRightTrigger", ctypes.c_ubyte), ("sThumbLX", ctypes.c_short),
                ("sThumbLY", ctypes.c_short), ("sThumbRX", ctypes.c_short),
                ("sThumbRY", ctypes.c_short)]


class XINPUT_STATE(ctypes.Structure):
    _fields_ = [("dwPacketNumber", ctypes.c_ulong), ("Gamepad", XINPUT_GAMEPAD)]


class XboxController:
    """Small XInput reader; it does not consume inputs from running games."""
    def __init__(self):
        self.dll = None
        if os.name == "nt":
            for name in ("xinput1_4.dll", "xinput1_3.dll", "xinput9_1_0.dll"):
                try:
                    self.dll = ctypes.WinDLL(name)
                    break
                except OSError:
                    continue
        if self.dll:
            self.dll.XInputGetState.argtypes = [ctypes.c_ulong, ctypes.POINTER(XINPUT_STATE)]
            self.dll.XInputGetState.restype = ctypes.c_ulong

    def read(self, index):
        if not self.dll:
            return None
        state = XINPUT_STATE()
        if self.dll.XInputGetState(index, ctypes.byref(state)) != 0:
            return None
        pad = state.Gamepad
        return pad.wButtons, pad.sThumbLX, pad.sThumbLY


def default_games() -> list[dict[str, str]]:
    return [
        {"name": "Añade tu primer juego", "path": "", "tag": "BIBLIOTECA"},
    ]


class Monitor:
    """Lecturas nativas Windows, sin dependencias externas."""
    def __init__(self):
        self.prev_idle = self.prev_kernel = self.prev_user = None
        self.mem = None
        if os.name == "nt":
            class MEMORYSTATUSEX(ctypes.Structure):
                _fields_ = [("dwLength", ctypes.c_ulong), ("dwMemoryLoad", ctypes.c_ulong),
                            ("ullTotalPhys", ctypes.c_ulonglong), ("ullAvailPhys", ctypes.c_ulonglong),
                            ("ullTotalPageFile", ctypes.c_ulonglong), ("ullAvailPageFile", ctypes.c_ulonglong),
                            ("ullTotalVirtual", ctypes.c_ulonglong), ("ullAvailVirtual", ctypes.c_ulonglong),
                            ("ullAvailExtendedVirtual", ctypes.c_ulonglong)]
            self.mem = MEMORYSTATUSEX()
            self.mem.dwLength = ctypes.sizeof(self.mem)

    def sample(self):
        cpu = None
        if os.name == "nt":
            idle, kernel, user = ctypes.c_ulonglong(), ctypes.c_ulonglong(), ctypes.c_ulonglong()
            if ctypes.windll.kernel32.GetSystemTimes(ctypes.byref(idle), ctypes.byref(kernel), ctypes.byref(user)):
                now = (idle.value, kernel.value, user.value)
                if self.prev_idle:
                    delta = [a - b for a, b in zip(now, self.prev_idle)]
                    total = delta[1] + delta[2]
                    cpu = round(100 * (total - delta[0]) / total) if total else 0
                self.prev_idle = now
        ram = None
        if self.mem and ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(self.mem)):
            used = self.mem.ullTotalPhys - self.mem.ullAvailPhys
            ram = (used / (1024**3), self.mem.ullTotalPhys / (1024**3), self.mem.dwMemoryLoad)
        return cpu, ram


class Launcher(tk.Tk):
    def __init__(self):
        super().__init__()
        global ACCENT
        self.settings = self.load_settings()
        ACCENT = self.settings.get("accent", ACCENT)
        self.title("1766 AI GAMING")
        self.geometry("1160x760")
        self.minsize(900, 620)
        self.configure(bg=BG)
        try:
            # A light glass effect: the desktop shows through slightly while text stays legible.
            self.attributes("-alpha", self.settings.get("opacity", 0.95))
        except tk.TclError:
            pass
        self.games = self.load_games()
        self.chat_window = None
        self.chat_conversation_id = None
        self.chat_busy = False
        self.chat_attachments = []
        self.init_chat_database()
        self.library_window = None
        self.library_tree = None
        self.pc_window = None
        self.pc_tree = None
        self.pc_current_path = None
        self.windows_window = None
        self.windows_apps = []
        self.performance_window = None
        self.performance_values = {}
        self.latest_cpu = None
        self.latest_ram = None
        self.monitor = Monitor()
        self.controller = XboxController()
        self.controller_previous = [0, 0, 0, 0]
        self.controller_connected = False
        self.controller_next_move = 0.0
        self.controller_targets = {"home": [], "library": [], "performance": [], "settings": []}
        self.logo_phase = 0
        self.background_phase = 0
        self.nav_phase = 0
        self.nav_active = "home"
        self.nav_titles = {}
        self.section_marks = []
        self.nav_icons = {
            "home": ("$>", ">_", "$ _", "$>"),
            "library": ("[#]", "[=]", "[#]", "[=]"),
            "performance": ("%", "‰", "%", "‰"),
            "settings": ("[*]", "[+]", "[*]", "[+]"),
        }
        self.metric_bars = []
        self.gaming = False
        self._style()
        self._layout()
        self.refresh_metrics()
        self.after(100, self.poll_controller)
        self.after(900, self.scan_installed_games)
        self.protocol("WM_DELETE_WINDOW", self.close_launcher)

    def _style(self):
        s = ttk.Style(self)
        s.theme_use("clam")
        s.configure("Treeview", background="#0a1120", foreground="#e1eaff", fieldbackground="#0a1120",
                    rowheight=38, borderwidth=0, font=("Consolas", 10))
        s.configure("Treeview.Heading", background="#101b30", foreground=PS_BLUE,
                    font=("Consolas", 9, "bold"), borderwidth=0, relief="flat", padding=(10, 9))
        s.map("Treeview", background=[("selected", "#172b4a")], foreground=[("selected", "#f6f9ff")])

    def label(self, parent, text, size=10, color="#e1eaff", bold=False):
        return tk.Label(parent, text=text, bg=parent["bg"], fg=color,
                        font=("Consolas", size, "bold" if bold else "normal"))

    def button(self, parent, text, command, primary=False):
        return tk.Button(parent, text=text, command=command, bg=PS_BLUE if primary else "#111b2e",
                         fg="#020611" if primary else "#c8f7d5",
                         activebackground="#69e5ff" if primary else "#142640",
                         activeforeground="#020611", relief="flat", bd=0, padx=16, pady=10,
                         font=("Consolas", 9, "bold"), cursor="hand2")

    def _layout(self):
        self.glow = tk.Frame(self, bg=PS_BLUE, height=2)
        self.glow.pack(side="top", fill="x")
        self._animate_glow(0)
        header = tk.Frame(self, bg="#070b16", height=66,
                          highlightbackground="#20314e", highlightthickness=1)
        header.pack(side="top", fill="x")
        header.pack_propagate(False)
        brand = tk.Frame(header, bg="#070b16")
        brand.pack(side="left", padx=(20, 12), pady=14)
        tk.Label(brand, text="[>_]", bg="#070b16", fg=PS_BLUE,
                 font=("Consolas", 15, "bold")).pack(side="left", padx=(0, 8))
        self.brand_label = self.label(brand, "1766 AI GAMING", 13, "#eef5ff", True)
        self.brand_label.pack(side="left")
        nav_items = [("home", "INICIO", True), ("library", "BIBLIOTECA", False),
                     ("performance", "SISTEMA", False), ("settings", "CONFIG", False)]
        self.nav_widgets = []
        for key, name, active in nav_items:
            icon = self.nav_icons[key][0]
            b = tk.Label(header, text=f"{icon}  {name}", bg="#142640" if active else "#070b16",
                         fg=PS_BLUE if active else "#9baac6", anchor="center", padx=9, pady=10,
                         font=("Consolas", 9, "bold" if active else "normal"), cursor="hand2",
                         takefocus=True)
            b.pack(side="left", padx=3, pady=10)
            b.bind("<Button-1>", lambda _event, destination=key: self.navigate(destination))
            b.bind("<Return>", lambda _event, destination=key: self.navigate(destination))
            self.nav_widgets.append(b)
            self.nav_titles[key] = name
        self.windows_menu_button = tk.Button(header, text="⊞ WINDOWS", command=self.open_windows_menu, bg="#10243b", fg="#dcecff", activebackground="#193858", activeforeground="white", relief="flat", bd=0, padx=12, pady=9, font=("Consolas", 9, "bold"), cursor="hand2")
        self.windows_menu_button.pack(side="right", padx=(4, 10), pady=10)
        self.my_pc_button = tk.Button(header, text="▣ MI PC", command=self.open_my_pc, bg="#10243b", fg="#dcecff", activebackground="#193858", activeforeground="white", relief="flat", bd=0, padx=12, pady=9, font=("Consolas", 9, "bold"), cursor="hand2")
        self.my_pc_button.pack(side="right", padx=4, pady=10)
        self.clock = self.label(header, time.strftime("%a, %d %b  •  %H:%M"), 9, MUTED)
        self.clock.pack(side="right", padx=(8, 14))
        self.controller_status = tk.Label(header, text="PAD::SCANNING", bg="#070b16",
                                          fg=MUTED, font=("Consolas", 8, "bold"))
        self.controller_status.pack(side="right", padx=8)

        main = tk.Frame(self, bg=BG)
        main.pack(side="top", fill="both", expand=True, padx=32, pady=(16, 18))
        self.background_canvas = tk.Canvas(main, bg=BG, highlightthickness=0, bd=0)
        self.background_canvas.place(x=0, y=0, relwidth=1, relheight=1)
        try:
            self.backdrop_photo = tk.PhotoImage(file=str(APP_DIR / "asus_background.png"))
        except tk.TclError:
            self.backdrop_photo = None
        self.backdrop_image_id = None
        self.background_canvas.bind("<Configure>", self.draw_animated_backdrop)
        self.after(80, self.animate_backdrop)
        title_row = tk.Frame(main, bg=BG)
        title_row.pack(fill="x")
        self.label(title_row, "1766 AI  //  CENTRO DE CONTROL", 22, "#eef5ff", True).pack(side="left", pady=(2, 0))
        self.label(title_row, "[ GAMING HUB ]", 8, PS_BLUE, True).pack(side="left", padx=13, pady=(13, 0))
        self.chatgpt_nav_button = tk.Button(title_row, text="1766 AI ASISTENTE  ➜", command=self.open_chatgpt,
                                            bg="#10251f", fg="#9ff0cf", activebackground="#1b3a30",
                                            activeforeground="#ffffff", relief="flat", bd=0,
                                            padx=14, pady=9, font=("Consolas", 9, "bold"), cursor="hand2")
        self.chatgpt_nav_button.pack(side="right", padx=(8, 0), pady=(0, 2))

        hero = tk.Frame(main, bg="#080e1d", highlightbackground="#274d80", highlightthickness=1, height=180)
        hero.pack(fill="x", pady=(12, 12))
        hero.pack_propagate(False)
        self.hero_mark = tk.Canvas(hero, bg="#080e1d", highlightthickness=0, bd=0)
        self.hero_mark.place(x=0, y=0, relwidth=1, relheight=1)
        # It is created before the foreground controls, so Tk keeps it behind them.
        self.hero_mark.bind("<Configure>", self.draw_brand_mark)
        self.draw_brand_mark()
        self.after(90, self.animate_brand_mark)
        try:
            self.assistant_source_photo = tk.PhotoImage(file=str(APP_DIR / "assets" / "assistant_1766_reference-crop.png"))
            self.assistant_photo = self.assistant_source_photo.subsample(3, 3)
            self.assistant_portrait = tk.Label(hero, image=self.assistant_photo, bg="#080e1d", bd=0)
        except tk.TclError:
            self.assistant_source_photo = None
            self.assistant_photo = None
            self.assistant_portrait = tk.Label(hero, text="1766\nAI", bg="#080e1d", fg=PS_BLUE,
                                               font=("Consolas", 18, "bold"), justify="center")
        self.assistant_portrait.pack(side="left", anchor="s", padx=(12, 8))
        self.hero_glow = tk.Frame(hero, bg=PS_BLUE, width=4)
        self.hero_glow.pack(side="left", fill="y")
        left = tk.Frame(hero, bg="#080e1d")
        left.pack(side="left", fill="both", expand=False, padx=20, pady=15)
        self.label(left, "ASISTENTE::ONLINE", 9, PS_BLUE, True).pack(anchor="w")
        self.label(left, "1766 AI", 16, "#eef5ff", True).pack(anchor="w", pady=(5, 2))
        self.label(left, "Hola. Estoy lista para ayudarte.", 9, MUTED).pack(anchor="w", pady=(0, 10))
        self.label(left, "MODO DE JUEGO", 11, "#eef5ff", True).pack(anchor="w")
        self.gaming_hint = self.label(left, "Activa un perfil local del launcher. No modifica Windows.", 9, MUTED)
        self.gaming_hint.pack(anchor="w")
        self.mode_btn = self.button(hero, "ACTIVAR MODO", self.toggle_gaming, True)
        self.mode_btn.pack(side="right", padx=23, pady=18)

        metrics = tk.Frame(main, bg=BG)
        metrics.pack(fill="x", pady=(0, 12))
        self.metric_values = {}
        for key, title, initial in [("cpu", "CPU", "—"), ("gpu", "GPU", "Integración pendiente"),
                                    ("ram", "MEMORIA RAM", "—"), ("fps", "FPS", "Integración pendiente")]:
            card = tk.Frame(metrics, bg=PANEL, padx=14, pady=9,
                            highlightbackground="#172b4a", highlightthickness=1)
            card.pack(side="left", fill="both", expand=True, padx=(0, 9))
            bar = tk.Frame(card, bg=PS_BLUE if key == "cpu" else "#324766", height=2)
            bar.pack(fill="x", pady=(0, 10))
            self.metric_bars.append(bar)
            self.label(card, title, 8, MUTED, True).pack(anchor="w")
            val = self.label(card, initial, 14 if key in ("gpu", "fps") else 19, "#e1eaff", True)
            val.pack(anchor="w", pady=(8, 2))
            if key in ("gpu", "fps"):
                val.configure(font=("Consolas", 9))
            self.metric_values[key] = val

        games_header = tk.Frame(main, bg=BG)
        games_header.pack(fill="x", pady=(0, 8))
        self.label(games_header, ">_ PROCESOS DE JUEGO", 12, "#e1eaff", True).pack(side="left")
        self.home_add_xbox = self.button(games_header, "+  Añadir desde Xbox", self.add_xbox_game)
        self.home_add_xbox.pack(side="right")
        self.home_add_exe = self.button(games_header, "+  Añadir juego", self.add_game)
        self.home_add_exe.pack(side="right", padx=(0, 8))
        self.home_play = self.button(games_header, "▶  Jugar", self.launch_selected, True)
        self.home_play.pack(side="right", padx=(0, 8))
        self.game_tiles_frame = tk.Frame(main, bg=BG, height=82)
        self.game_tiles_frame.pack(fill="x", pady=(0, 8))
        self.game_tiles_frame.pack_propagate(False)
        self.game_tile_buttons = []
        cols = ("game", "location", "action")
        self.table = ttk.Treeview(main, columns=cols, show="headings", height=3, selectmode="browse")
        self.table.heading("game", text="JUEGO")
        self.table.heading("location", text="EJECUTABLE")
        self.table.heading("action", text="ACCIÓN")
        self.table.column("game", width=220, anchor="w")
        self.table.column("location", width=450, anchor="w")
        self.table.column("action", width=110, anchor="center")
        self.table.pack(fill="both", expand=True)
        self.table.bind("<Double-1>", lambda _e: self.launch_selected())
        self.table.bind("<Button-1>", self.handle_home_action_click, add="+")
        self.table.bind("<<TreeviewSelect>>", self.sync_tile_selection)
        foot = tk.Frame(main, bg=BG)
        foot.pack(fill="x", pady=(10, 0))
        self.home_remove = self.button(foot, "Quitar de biblioteca", self.remove_game)
        self.home_remove.pack(side="left", padx=9)
        self.label(foot, "A selecciona  ·  B vuelve  ·  Doble clic para jugar", 8, MUTED).pack(side="right", pady=8)
        self.controller_targets["home"] = self.nav_widgets + [self.table, self.home_add_exe,
                                                             self.home_add_xbox, self.home_play,
                                                             self.home_remove, self.mode_btn]
        self.populate()
        self.after(150, self.animate_interface_marks)

    def _animate_glow(self, phase):
        rgb = tuple(int(PS_BLUE[i:i + 2], 16) for i in (1, 3, 5))
        dim = "#" + "".join(f"{int(channel * 0.42):02x}" for channel in rgb)
        colors = (dim, PS_BLUE, PS_BLUE, dim)
        self.glow.configure(bg=colors[phase % len(colors)])
        self.after(260, self._animate_glow, phase + 1)

    # --------------------------- 1766 AI / OLLAMA ---------------------------
    CHAT_MODEL = "llama3.2:3b"
    OLLAMA_URL = "http://127.0.0.1:11434/api/chat"
    CHAT_INSTRUCTIONS = (
        "Sos el asistente integrado de 1766 AI GAMING. Respondé en español claro, "
        "con tono amable y directo. El usuario está continuando un proyecto de launcher "
        "Windows hecho en Python/Tkinter llamado 1766. Ayudalo con el launcher, juegos, "
        "PC y programación. No afirmes que tenés acceso a su cuenta de ChatGPT ni a "
        "conversaciones que no estén incluidas en este chat."
    )

    def init_chat_database(self):
        DATA_DIR.mkdir(parents=True, exist_ok=True)
        with sqlite3.connect(DATA_DIR / "chat_history.sqlite3") as db:
            db.execute("CREATE TABLE IF NOT EXISTS conversations (id TEXT PRIMARY KEY, title TEXT NOT NULL, created REAL NOT NULL, updated REAL NOT NULL)")
            db.execute("CREATE TABLE IF NOT EXISTS messages (id INTEGER PRIMARY KEY AUTOINCREMENT, conversation_id TEXT NOT NULL, role TEXT NOT NULL, content TEXT NOT NULL, created REAL NOT NULL, FOREIGN KEY(conversation_id) REFERENCES conversations(id))")
            count = db.execute("SELECT COUNT(*) FROM conversations").fetchone()[0]
            if count == 0:
                cid = str(uuid.uuid4())
                now = time.time()
                db.execute("INSERT INTO conversations(id,title,created,updated) VALUES(?,?,?,?)",
                           (cid, "Conversación de 1766 AI", now, now))
                db.execute("INSERT INTO messages(conversation_id,role,content,created) VALUES(?,?,?,?)",
                           (cid, "user", "Quiero continuar dentro del launcher 1766 la conversación que tenía en ChatGPT. Quiero un chat integrado, historial de conversaciones anteriores, conversaciones nuevas y continuidad del contexto.", now))
                db.execute("INSERT INTO messages(conversation_id,role,content,created) VALUES(?,?,?,?)",
                           (cid, "assistant", "1766 AI está conectado a un modelo local mediante Ollama. Las conversaciones se guardan en esta PC y no requieren una clave API ni generan cargos por uso de API.", now + 0.001))
            db.commit()

    def _chat_db(self):
        return sqlite3.connect(DATA_DIR / "chat_history.sqlite3")

    def open_chatgpt(self):
        """Open the native Tkinter chat window; it does not open a browser."""
        if self.chat_window and self.chat_window.winfo_exists():
            self.chat_window.deiconify()
            self.chat_window.lift()
            return
        win = tk.Toplevel(self)
        self.chat_window = win
        win.title("1766 AI | Asistente local")
        win.geometry("1050x700")
        win.minsize(780, 520)
        win.configure(bg=BG)
        win.transient(self)
        win.protocol("WM_DELETE_WINDOW", self.close_chat_window)

        sidebar = tk.Frame(win, bg="#070d19", width=250)
        sidebar.pack(side="left", fill="y")
        sidebar.pack_propagate(False)
        tk.Label(sidebar, text="1766  //  AI LOCAL", bg="#070d19", fg=PS_BLUE,
                 font=("Consolas", 13, "bold")).pack(anchor="w", padx=16, pady=(18, 14))
        self.button(sidebar, "+ NUEVA CONVERSACIÓN", self.new_chat_conversation, primary=True).pack(fill="x", padx=12, pady=(0, 10))
        self.chat_history_list = tk.Listbox(sidebar, bg="#0a1120", fg="#dce8ff", selectbackground="#17476a",
                                            selectforeground="white", relief="flat", bd=0,
                                            font=("Consolas", 9), activestyle="none")
        self.chat_history_list.pack(fill="both", expand=True, padx=10, pady=4)
        self.chat_history_list.bind("<<ListboxSelect>>", self.select_chat_conversation)
        self.button(sidebar, "ELIMINAR CONVERSACIÓN", self.delete_chat_conversation).pack(fill="x", padx=12, pady=(8, 5))
        self.button(sidebar, "COMPROBAR OLLAMA", self.test_ollama_connection).pack(fill="x", padx=12, pady=(0, 14))

        main = tk.Frame(win, bg=BG)
        main.pack(side="left", fill="both", expand=True)
        top = tk.Frame(main, bg="#080e1d", height=54)
        top.pack(fill="x")
        top.pack_propagate(False)
        self.chat_title_label = tk.Label(top, text="CHAT NUEVO", bg="#080e1d", fg="#eef5ff",
                                         font=("Consolas", 11, "bold"))
        self.chat_title_label.pack(side="left", padx=18, pady=16)
        self.chat_status_label = tk.Label(top, text="OLLAMA: LOCAL · " + self.CHAT_MODEL,
                                          bg="#080e1d", fg="#91e6c2",
                                          font=("Consolas", 8, "bold"))
        self.chat_status_label.pack(side="right", padx=16)

        self.chat_transcript = tk.Text(main, bg="#050a14", fg="#e3ecff", insertbackground="white",
                                       wrap="word", relief="flat", bd=0, padx=22, pady=18,
                                       font=("Segoe UI", 10), state="disabled")
        self.chat_transcript.pack(fill="both", expand=True, padx=12, pady=(12, 6))
        self.chat_transcript.tag_configure("user", foreground="#7de4ff", font=("Segoe UI", 10, "bold"), spacing1=12)
        self.chat_transcript.tag_configure("assistant", foreground="#e3ecff", spacing1=12)
        self.chat_transcript.tag_configure("meta", foreground="#7d91b2", font=("Consolas", 8, "bold"), spacing1=10)

        attachment_bar = tk.Frame(main, bg=BG)
        attachment_bar.pack(fill="x", padx=18, pady=(2, 4))
        self.chat_attachment_status = tk.Label(
            attachment_bar, text="Sin archivos adjuntos", bg=BG, fg=MUTED,
            font=("Consolas", 8), anchor="w")
        self.chat_attachment_status.pack(side="left", fill="x", expand=True)
        self.chat_remove_attachment_button = self.button(
            attachment_bar, "QUITAR ÚLTIMO", self.remove_last_chat_attachment)
        self.chat_remove_attachment_button.pack(side="right", padx=(6, 0))
        self.chat_clear_attachments_button = self.button(
            attachment_bar, "LIMPIAR", self.clear_chat_attachments)
        self.chat_clear_attachments_button.pack(side="right")
        composer = tk.Frame(main, bg="#0a1120", highlightbackground="#23466d", highlightthickness=1)
        composer.pack(fill="x", padx=14, pady=(2, 14))
        self.chat_attach_button = self.button(composer, "📎 ADJUNTAR", self.attach_chat_files)
        self.chat_attach_button.pack(side="left", padx=(9, 0), pady=10)
        self.chat_input = tk.Text(composer, height=3, bg="#0a1120", fg="#eef5ff", insertbackground="white",
                                  wrap="word", relief="flat", bd=0, padx=12, pady=10,
                                  font=("Segoe UI", 10))
        self.chat_input.pack(side="left", fill="both", expand=True)
        self.chat_input.bind("<Control-Return>", self._chat_ctrl_enter)
        self.chat_send_button = self.button(composer, "ENVIAR", self.send_chat_message, primary=True)
        self.chat_send_button.pack(side="right", padx=10, pady=10)
        tk.Label(main, text="Ollama local · Imágenes: requiere gemma3:4b · PDF: requiere pypdf.",
                 bg=BG, fg=MUTED, font=("Consolas", 8)).pack(pady=(0, 8))
        if not self.chat_conversation_id:
            with self._chat_db() as db:
                latest = db.execute("SELECT id FROM conversations ORDER BY updated DESC LIMIT 1").fetchone()
            self.chat_conversation_id = latest[0] if latest else None
        self.refresh_chat_history()
        self.load_chat_conversation(self.chat_conversation_id)
        win.focus_force()

    def close_chat_window(self):
        if self.chat_window and self.chat_window.winfo_exists():
            self.chat_window.destroy()
        self.chat_window = None

    def test_ollama_connection(self):
        """Check that the local Ollama server is reachable and the selected model exists."""
        self.chat_status_label.configure(text="OLLAMA: COMPROBANDO…", fg="#7de4ff")
        threading.Thread(target=self._check_ollama_connection, daemon=True).start()

    def _check_ollama_connection(self):
        try:
            request = urllib.request.Request("http://127.0.0.1:11434/api/tags", method="GET")
            with urllib.request.urlopen(request, timeout=5) as response:
                data = json.loads(response.read().decode("utf-8"))
            models = [item.get("name", "") for item in data.get("models", [])]
            found = any(name == self.CHAT_MODEL or name.startswith(self.CHAT_MODEL + ":") for name in models)
            if found:
                result = ("ok", f"OLLAMA: CONECTADO · {self.CHAT_MODEL}")
            else:
                result = ("error", f"No encuentro {self.CHAT_MODEL}. Abrí una terminal y ejecutá: ollama run {self.CHAT_MODEL}")
        except Exception as exc:
            result = ("error", f"No se pudo conectar con Ollama. Abrí Ollama o ejecutá 'ollama serve'. Detalle: {exc}")
        self.after(0, self._show_ollama_check, *result)

    def _show_ollama_check(self, status, message):
        if not self.chat_window or not self.chat_window.winfo_exists():
            return
        self.chat_status_label.configure(
            text="OLLAMA: CONECTADO" if status == "ok" else "OLLAMA: SIN CONEXIÓN",
            fg="#91e6c2" if status == "ok" else "#ff9a9a")
        if status != "ok":
            messagebox.showwarning("Ollama", message, parent=self.chat_window)

    def refresh_chat_history(self):
        if not self.chat_window or not self.chat_window.winfo_exists():
            return
        self.chat_history_list.delete(0, "end")
        with self._chat_db() as db:
            rows = db.execute("SELECT id,title FROM conversations ORDER BY updated DESC").fetchall()
        self.chat_history_ids = []
        for cid, title in rows:
            self.chat_history_ids.append(cid)
            self.chat_history_list.insert("end", title)
        if self.chat_conversation_id in self.chat_history_ids:
            idx = self.chat_history_ids.index(self.chat_conversation_id)
            self.chat_history_list.selection_set(idx)
            self.chat_history_list.see(idx)

    def new_chat_conversation(self):
        cid = str(uuid.uuid4())
        now = time.time()
        with self._chat_db() as db:
            db.execute("INSERT INTO conversations(id,title,created,updated) VALUES(?,?,?,?)", (cid, "Nueva conversación", now, now))
            db.commit()
        self.chat_conversation_id = cid
        self.refresh_chat_history()
        self.load_chat_conversation(cid)
        self.chat_input.focus_set()

    def select_chat_conversation(self, _event=None):
        selected = self.chat_history_list.curselection()
        if selected:
            self.chat_conversation_id = self.chat_history_ids[selected[0]]
            self.load_chat_conversation(self.chat_conversation_id)

    def delete_chat_conversation(self):
        if not self.chat_conversation_id:
            return
        if not messagebox.askyesno("Eliminar conversación", "¿Querés borrar esta conversación de este equipo?", parent=self.chat_window):
            return
        with self._chat_db() as db:
            db.execute("DELETE FROM messages WHERE conversation_id=?", (self.chat_conversation_id,))
            db.execute("DELETE FROM conversations WHERE id=?", (self.chat_conversation_id,))
            db.commit()
        self.chat_conversation_id = None
        self.refresh_chat_history()
        if self.chat_history_ids:
            self.chat_conversation_id = self.chat_history_ids[0]
            self.load_chat_conversation(self.chat_conversation_id)
        else:
            self.new_chat_conversation()

    def load_chat_conversation(self, cid):
        if not cid or not self.chat_window or not self.chat_window.winfo_exists():
            return
        with self._chat_db() as db:
            row = db.execute("SELECT title FROM conversations WHERE id=?", (cid,)).fetchone()
            messages = db.execute("SELECT role,content FROM messages WHERE conversation_id=? ORDER BY id", (cid,)).fetchall()
        self.chat_title_label.configure(text=row[0].upper() if row else "CHAT NUEVO")
        self.chat_transcript.configure(state="normal")
        self.chat_transcript.delete("1.0", "end")
        for role, content in messages:
            self._append_chat_message(role, content)
        self.chat_transcript.configure(state="disabled")
        self.chat_transcript.see("end")

    def _append_chat_message(self, role, content):
        label = "VOS" if role == "user" else "1766 AI"
        tag = "user" if role == "user" else "assistant"
        self.chat_transcript.insert("end", f"\n{label}\n", "meta")
        self.chat_transcript.insert("end", content.strip() + "\n", tag)

    def attach_chat_files(self):
        """Choose images and documents to include in the next local-model message."""
        paths = filedialog.askopenfilenames(
            parent=self.chat_window,
            title="Adjuntar archivos a 1766 AI",
            filetypes=[
                ("Archivos compatibles", "*.png *.jpg *.jpeg *.webp *.bmp *.gif *.txt *.md *.py *.json *.csv *.log *.pdf *.docx"),
                ("Imágenes", "*.png *.jpg *.jpeg *.webp *.bmp *.gif"),
                ("Documentos y texto", "*.txt *.md *.py *.json *.csv *.log *.pdf *.docx"),
                ("Todos los archivos", "*.*"),
            ],
        )
        added = 0
        existing = {item["path"] for item in self.chat_attachments}
        for raw_path in paths:
            path = str(Path(raw_path).resolve())
            if path in existing:
                continue
            item = {"path": path, "name": Path(path).name}
            suffix = Path(path).suffix.lower()
            if suffix in (".png", ".jpg", ".jpeg", ".webp", ".bmp", ".gif"):
                item["kind"] = "image"
            elif suffix == ".pdf":
                item["kind"] = "pdf"
            elif suffix == ".docx":
                item["kind"] = "docx"
            elif suffix in (".txt", ".md", ".py", ".json", ".csv", ".log"):
                item["kind"] = "text"
            else:
                item["kind"] = "other"
            self.chat_attachments.append(item)
            existing.add(path)
            added += 1
        self.update_chat_attachment_status()
        if added:
            self.chat_input.focus_set()

    def update_chat_attachment_status(self):
        if not self.chat_window or not self.chat_window.winfo_exists():
            return
        if not self.chat_attachments:
            label = "Sin archivos adjuntos"
        else:
            names = [item["name"] for item in self.chat_attachments]
            shown = ", ".join(names[:3])
            if len(names) > 3:
                shown += f" y {len(names) - 3} más"
            label = f"Adjuntos ({len(names)}): {shown}   ·   Clic en ADJUNTAR para sumar archivos"
        self.chat_attachment_status.configure(text=label)

    def remove_last_chat_attachment(self):
        if self.chat_attachments:
            self.chat_attachments.pop()
            self.update_chat_attachment_status()

    def clear_chat_attachments(self):
        self.chat_attachments.clear()
        self.update_chat_attachment_status()

    def _read_chat_attachment_text(self, item):
        path = Path(item["path"])
        if item["kind"] == "other":
            return "[Archivo adjunto. Este formato se muestra, pero todavía no se puede leer su contenido.]"
        if item["kind"] == "docx":
            try:
                with zipfile.ZipFile(path) as archive:
                    xml_data = archive.read("word/document.xml")
                root = ET.fromstring(xml_data)
                ns = {"w": "http://schemas.openxmlformats.org/wordprocessingml/2006/main"}
                paragraphs = []
                for paragraph in root.findall(".//w:p", ns):
                    words = [node.text or "" for node in paragraph.findall(".//w:t", ns)]
                    paragraphs.append("".join(words))
                return "\\n".join(paragraphs).strip()[:30000]
            except Exception as exc:
                return f"[No se pudo leer el documento Word: {exc}]"
        if item["kind"] == "pdf":
            try:
                from pypdf import PdfReader
                reader = PdfReader(str(path))
                pages = []
                for page in reader.pages[:30]:
                    pages.append(page.extract_text() or "")
                extracted = "\\n".join(pages).strip()
                return extracted[:30000] or "[No se pudo extraer texto del PDF.]"
            except ImportError:
                return "[PDF adjunto, pero falta instalar pypdf para leer su contenido.]"
            except Exception as exc:
                return f"[No se pudo leer el PDF: {exc}]"
        try:
            return path.read_text(encoding="utf-8", errors="replace")[:30000]
        except Exception as exc:
            return f"[No se pudo leer el archivo: {exc}]"

    def _chat_attachment_prompt(self, user_text, attachments):
        parts = [user_text] if user_text else ["Revisá los archivos que adjunté y ayudame con ellos."]
        for item in attachments:
            if item["kind"] == "image":
                parts.append(f"[Imagen adjunta: {item['name']}]")
            else:
                content = self._read_chat_attachment_text(item)
                parts.append(f"\\n--- CONTENIDO DE {item['name']} ---\\n{content}\\n--- FIN DEL ARCHIVO ---")
        return "\\n\\n".join(parts)

    def _chat_ctrl_enter(self, _event=None):
        self.send_chat_message()
        return "break"

    def send_chat_message(self):
        if self.chat_busy:
            return
        text = self.chat_input.get("1.0", "end").strip()
        attachments = list(self.chat_attachments)
        if not text and not attachments:
            return
        if not self.chat_conversation_id:
            self.new_chat_conversation()
        cid = self.chat_conversation_id
        prompt = self._chat_attachment_prompt(text, attachments)
        attachment_names = ", ".join(item["name"] for item in attachments)
        stored_text = prompt
        if attachment_names:
            stored_text += f"\\n\\n[Archivos adjuntos: {attachment_names}]"
        now = time.time()
        with self._chat_db() as db:
            db.execute("INSERT INTO messages(conversation_id,role,content,created) VALUES(?,?,?,?)",
                       (cid, "user", stored_text, now))
            count = db.execute("SELECT COUNT(*) FROM messages WHERE conversation_id=?", (cid,)).fetchone()[0]
            if count <= 1:
                title_source = text or attachment_names or "Archivos adjuntos"
                title = (title_source[:38] + "…") if len(title_source) > 38 else title_source
                db.execute("UPDATE conversations SET title=?,updated=? WHERE id=?",
                           (title or "Nueva conversación", now, cid))
            else:
                db.execute("UPDATE conversations SET updated=? WHERE id=?", (now, cid))
            history = db.execute("SELECT role,content FROM messages WHERE conversation_id=? ORDER BY id", (cid,)).fetchall()
            db.commit()
        self.chat_input.delete("1.0", "end")
        self.chat_transcript.configure(state="normal")
        display_text = text if text else "Revisá los archivos adjuntos."
        if attachment_names:
            display_text += f"\\n📎 {attachment_names}"
        self._append_chat_message("user", display_text)
        self.chat_transcript.configure(state="disabled")
        self.chat_transcript.see("end")
        self.chat_attachments = []
        self.update_chat_attachment_status()
        self.chat_busy = True
        self.chat_send_button.configure(state="disabled", text="ESPERÁ…")
        self.chat_attach_button.configure(state="disabled")
        self.chat_status_label.configure(text="1766 AI: PENSANDO…", fg="#7de4ff")
        threading.Thread(
            target=self._request_ollama,
            args=(cid, history, attachments),
            daemon=True,
        ).start()
        self.refresh_chat_history()

    def _request_ollama(self, cid, history, attachments=None):
        """Send chat text and optional image payloads to Ollama in a worker thread."""
        attachments = attachments or []
        image_items = [item for item in attachments if item["kind"] == "image"]
        model = "gemma3:4b" if image_items else self.CHAT_MODEL
        messages = [{"role": "system", "content": self.CHAT_INSTRUCTIONS}]
        messages.extend(
            {"role": role, "content": content}
            for role, content in history[-40:]
            if role in ("user", "assistant")
        )
        if image_items and messages and messages[-1]["role"] == "user":
            encoded_images = []
            for item in image_items:
                try:
                    with open(item["path"], "rb") as image_file:
                        encoded_images.append(base64.b64encode(image_file.read()).decode("ascii"))
                except Exception as exc:
                    self.after(0, self._finish_chat_response, cid, None,
                               f"No pude abrir la imagen {item['name']}: {exc}")
                    return
            messages[-1]["images"] = encoded_images
        payload = {
            "model": model,
            "messages": messages,
            "stream": False,
        }
        request = urllib.request.Request(
            self.OLLAMA_URL,
            data=json.dumps(payload, ensure_ascii=False).encode("utf-8"),
            headers={"Content-Type": "application/json"},
            method="POST",
        )
        try:
            with urllib.request.urlopen(request, timeout=300) as response:
                data = json.loads(response.read().decode("utf-8"))
            answer = data.get("message", {}).get("content", "").strip()
            if not answer:
                answer = "Ollama respondió, pero no devolvió texto. Probá enviar el mensaje otra vez."
            self.after(0, self._finish_chat_response, cid, answer, None)
        except urllib.error.HTTPError as exc:
            try:
                detail = exc.read().decode("utf-8", errors="replace")
                parsed = json.loads(detail)
                detail = parsed.get("error", detail)
            except Exception:
                detail = str(exc)
            if exc.code == 404 and image_items:
                detail = ("Para analizar imágenes necesitás instalar el modelo de visión. "
                          "Abrí una terminal y ejecutá: ollama pull gemma3:4b. "
                          "Después volvé a enviar la imagen.")
            elif exc.code == 404:
                detail = f"No está instalado el modelo {model}. Ejecutá en una terminal: ollama run {model}"
            self.after(0, self._finish_chat_response, cid, None, f"Error de Ollama ({exc.code}): {detail}")
        except (urllib.error.URLError, TimeoutError, ConnectionError) as exc:
            self.after(0, self._finish_chat_response, cid, None,
                       "No se pudo conectar con Ollama. Comprobá que Ollama esté abierto o ejecutá 'ollama serve'. "
                       f"Detalle: {exc}")
        except Exception as exc:
            self.after(0, self._finish_chat_response, cid, None, f"Error al consultar el modelo local: {exc}")

    def _finish_chat_response(self, cid, answer, error):
        self.chat_busy = False
        if not self.chat_window or not self.chat_window.winfo_exists():
            if answer:
                with self._chat_db() as db:
                    now = time.time()
                    db.execute("INSERT INTO messages(conversation_id,role,content,created) VALUES(?,?,?,?)", (cid, "assistant", answer, now))
                    db.execute("UPDATE conversations SET updated=? WHERE id=?", (now, cid))
                    db.commit()
            return
        self.chat_send_button.configure(state="normal", text="ENVIAR")
        if hasattr(self, "chat_attach_button"):
            self.chat_attach_button.configure(state="normal")
        if error:
            self.chat_status_label.configure(text="ERROR DE CONEXIÓN", fg="#ff9a9a")
            self.chat_transcript.configure(state="normal")
            self._append_chat_message("assistant", error)
            self.chat_transcript.configure(state="disabled")
        else:
            now = time.time()
            with self._chat_db() as db:
                db.execute("INSERT INTO messages(conversation_id,role,content,created) VALUES(?,?,?,?)", (cid, "assistant", answer, now))
                db.execute("UPDATE conversations SET updated=? WHERE id=?", (now, cid))
                db.commit()
            if cid == self.chat_conversation_id:
                self.chat_transcript.configure(state="normal")
                self._append_chat_message("assistant", answer)
                self.chat_transcript.configure(state="disabled")
                self.chat_transcript.see("end")
            self.chat_status_label.configure(text="1766 AI: LISTO", fg="#91e6c2")
        self.refresh_chat_history()

    def close_launcher(self):
        for window_name in ("pc_window", "windows_window", "library_window", "performance_window", "settings_window", "chat_window"):
            window = getattr(self, window_name, None)
            if window and window.winfo_exists():
                try:
                    window.destroy()
                except tk.TclError:
                    pass
        self.destroy()

    def draw_animated_backdrop(self, _event=None):
        """Paint an animated 1766 AI rain-and-lightning layer behind the dashboard."""
        canvas = self.background_canvas
        canvas.delete("fx")
        width, height = canvas.winfo_width(), canvas.winfo_height()
        if width < 40 or height < 40:
            return
        phase = self.background_phase
        drift = math.sin(phase * 0.035) * 12
        pulse = (math.sin(phase * 0.11) + 1) / 2
        if self.backdrop_photo:
            if self.backdrop_image_id is None:
                self.backdrop_image_id = canvas.create_image(
                    width // 2, height // 2, image=self.backdrop_photo, anchor="center")
            else:
                canvas.coords(self.backdrop_image_id, width // 2, height // 2)
        else:
            # Fallback if the optional wallpaper file is missing.
            mark_x, mark_y = width * 0.66 + drift, height * 0.53
            canvas.create_text(mark_x, mark_y, text="1766 AI", fill="#101a30",
                               font=("Consolas", 68, "bold"), anchor="center", tags="fx")
        # Slanted rain streaks move continuously down the screen.
        for index in range(54):
            x = (index * 83 + (index % 5) * 19) % width
            y = (index * 61 + phase * (7 + index % 5)) % (height + 30) - 15
            color = "#62dcff" if index % 9 == phase % 9 else "#172640"
            canvas.create_line(x, y, x - 5, y + 15 + index % 12,
                               fill=color, width=1, tags="fx")
        # Cyan and violet contours animate the launcher backdrop.
        center_x, center_y = width // 2, height // 2
        scale = min(width / 900, height / 700)
        rgb_paths = [
            [(-300, -70), (-115, -70), (-35, -20), (280, -135)],
            [(-285, -25), (-100, -25), (-28, 25), (245, -48)],
            [(-205, 65), (-75, 65), (5, 145), (165, 42)],
        ]
        for index, path in enumerate(rgb_paths):
            hue = 0.54 if index % 2 == 0 else 0.74
            rgb = colorsys.hsv_to_rgb(hue, 0.92, 1.0)
            glow_rgb = colorsys.hsv_to_rgb(hue, 0.95, 0.38)
            neon = "#" + "".join(f"{int(channel * 255):02x}" for channel in rgb)
            glow = "#" + "".join(f"{int(channel * 255):02x}" for channel in glow_rgb)
            points = [coordinate * scale + (center_x if pos % 2 == 0 else center_y)
                      for point in path for pos, coordinate in enumerate(point)]
            canvas.create_line(*points, fill=glow, width=10, smooth=True, tags="fx")
            canvas.create_line(*points, fill=neon, width=2, smooth=True, tags="fx")
        sweep = (phase % 100) / 100
        sweep_x = center_x - 310 * scale + sweep * 620 * scale
        sweep_hue = 0.54 + 0.20 * ((math.sin(phase * 0.025) + 1) / 2)
        sweep_rgb = colorsys.hsv_to_rgb(sweep_hue, 0.65, 1.0)
        sweep_color = "#" + "".join(f"{int(channel * 255):02x}" for channel in sweep_rgb)
        canvas.create_line(sweep_x, center_y - 145 * scale, sweep_x + 24 * scale,
                           center_y + 145 * scale, fill=sweep_color, width=4, tags="fx")
        # Lightning flashes briefly on a repeating cycle, with an angular bolt.
        flash = phase % 96
        if flash < 5:
            bolt_x = int(width * (0.28 + (flash % 3) * 0.18))
            points = (bolt_x, 0, bolt_x - 17, height * 0.20,
                      bolt_x + 5, height * 0.20, bolt_x - 20, height * 0.47,
                      bolt_x - 4, height * 0.43, bolt_x - 29, height * 0.73)
            canvas.create_line(*points, fill="#263d66", width=7, smooth=False, tags="fx")
            canvas.create_line(*points, fill=ACCENT if pulse > 0.5 else "#a5eaff",
                               width=2, smooth=False, tags="fx")
        # Violet horizon bars pulse like a compact sci-fi HUD.
        bar_width = 18 + pulse * 30
        canvas.create_line(14, height - 12, 14 + bar_width, height - 12,
                           fill="#7b5cff", width=2, tags="fx")

    def animate_backdrop(self):
        if not self.winfo_exists():
            return
        self.background_phase += 1
        if self.state() != "iconic":
            self.draw_animated_backdrop()
        self.after(80, self.animate_backdrop)

    def animate_interface_marks(self):
        """Animate the small navigation and hardware marks across the dashboard."""
        if not self.winfo_exists():
            return
        frame = self.nav_phase % 4
        for index, (key, widget) in enumerate(zip(self.nav_titles, self.nav_widgets)):
            icon = self.nav_icons[key][frame]
            active = key == self.nav_active
            try:
                widget.configure(text=f"{icon}  {self.nav_titles[key]}",
                                 fg=PS_BLUE if active or frame == index else "#97a9c8",
                                 bg="#142640" if active else "#070b16")
            except tk.TclError:
                pass
        for index, bar in enumerate(self.metric_bars):
            shade = PS_BLUE if (self.nav_phase + index * 2) % 6 < 3 else "#294b72"
            try:
                bar.configure(bg=shade)
            except tk.TclError:
                pass
        self.section_marks = [entry for entry in self.section_marks if entry[0].winfo_exists()]
        for widget, title, icons in self.section_marks:
            widget.configure(text=f"{icons[frame]}  {title}", fg=PS_BLUE)
        self.nav_phase += 1
        self.after(240, self.animate_interface_marks)

    def section_heading(self, parent, title, icons):
        heading = tk.Label(parent, text=f"{icons[0]}  {title}", bg=BG, fg=PS_BLUE,
                           font=("Consolas", 16, "bold"))
        self.section_marks.append((heading, title, icons))
        return heading

    def navigate(self, destination):
        self.nav_active = destination
        if destination == "home":
            self.navigate_home()
        elif destination == "library":
            self.open_library()
        elif destination == "performance":
            self.open_performance()
        elif destination == "settings":
            self.open_settings()

    def navigate_home(self):
        for attr in ("library_window", "performance_window", "settings_window"):
            win = getattr(self, attr, None)
            if win and win.winfo_exists():
                win.destroy()
        self.library_window = self.library_tree = None
        self.performance_window = None
        self.performance_values.clear()
        self.controller_targets["library"] = []
        self.controller_targets["performance"] = []
        self.controller_targets["settings"] = []
        self.lift()
        self.focus_force()
        self.nav_widgets[0].focus_set()

    def active_controller_page(self):
        focus = self.focus_get()
        top = focus.winfo_toplevel() if focus else self
        if self.library_window and top == self.library_window:
            return "library"
        if self.performance_window and top == self.performance_window:
            return "performance"
        if getattr(self, "settings_window", None) and top == self.settings_window:
            return "settings"
        return "home"

    def launcher_is_foreground(self):
        if os.name != "nt":
            return True
        hwnd = ctypes.windll.user32.GetForegroundWindow()
        pid = ctypes.c_ulong()
        ctypes.windll.user32.GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
        return pid.value == os.getpid()

    def poll_controller(self):
        connected = False
        now = time.monotonic()
        for index in range(4):
            sample = self.controller.read(index)
            previous = self.controller_previous[index]
            if sample is None:
                self.controller_previous[index] = 0
                continue
            connected = True
            buttons, thumb_x, thumb_y = sample
            self.controller_previous[index] = buttons
            if not self.launcher_is_foreground():
                continue
            pressed = buttons & ~previous
            direction = None
            for bit, name in ((XINPUT_DPAD_UP, "up"), (XINPUT_DPAD_DOWN, "down"),
                              (XINPUT_DPAD_LEFT, "left"), (XINPUT_DPAD_RIGHT, "right")):
                if pressed & bit:
                    direction = name
                    break
            if direction:
                self.controller_next_move = now + 0.22
                self.controller_move(direction)
            elif now >= self.controller_next_move:
                if thumb_y > 16000:
                    direction = "up"
                elif thumb_y < -16000:
                    direction = "down"
                elif thumb_x < -16000:
                    direction = "left"
                elif thumb_x > 16000:
                    direction = "right"
                if direction:
                    self.controller_move(direction)
                    self.controller_next_move = now + 0.22
            self.controller_buttons(pressed)
            break
        self.controller_connected = connected
        self.controller_status.configure(
            text="MANDO XBOX: CONECTADO" if connected else "MANDO XBOX: DESCONECTADO",
            fg="#62dcff" if connected else MUTED)
        self.after(80, self.poll_controller)

    def controller_move(self, direction):
        page = self.active_controller_page()
        targets = [w for w in self.controller_targets.get(page, []) if w.winfo_exists()]
        if not targets:
            return
        focus = self.focus_get()
        if isinstance(focus, tk.Scale) and direction in ("left", "right"):
            delta = -1 if direction == "left" else 1
            focus.set(max(85, min(100, float(focus.get()) + delta)))
            return
        if isinstance(focus, ttk.Treeview) and direction in ("up", "down"):
            rows = focus.get_children("")
            if rows:
                selection = focus.selection()
                if selection and selection[0] in rows:
                    current = rows.index(selection[0])
                    step = -1 if direction == "up" else 1
                    next_row = rows[(current + step) % len(rows)]
                else:
                    next_row = rows[-1] if direction == "up" else rows[0]
                focus.selection_set(next_row)
                focus.see(next_row)
            return
        current = targets.index(focus) if focus in targets else -1
        step = -1 if direction in ("up", "left") else 1
        targets[(current + step) % len(targets)].focus_set()

    def controller_buttons(self, pressed):
        page = self.active_controller_page()
        if pressed & XINPUT_B:
            if page != "home":
                self.navigate_home()
            return
        if pressed & XINPUT_X:
            if page in ("home", "library"):
                self.add_game()
            return
        if pressed & XINPUT_Y:
            if page in ("home", "library"):
                self.add_xbox_game()
            return
        if pressed & XINPUT_A:
            focus = self.focus_get()
            if isinstance(focus, ttk.Treeview):
                rows = focus.get_children("")
                if rows and not focus.selection():
                    focus.selection_set(rows[0])
                self.launch_selected(focus)
            elif isinstance(focus, tk.Button):
                focus.invoke()
            elif isinstance(focus, tk.Label):
                focus.event_generate("<Button-1>")

    def open_library(self):
        if self.library_window and self.library_window.winfo_exists():
            self.library_window.lift()
            return
        win = tk.Toplevel(self)
        self.library_window = win
        win.title("1766 AI GAMING | Biblioteca")
        win.geometry("850x500")
        win.configure(bg=BG)
        win.transient(self)
        self.section_heading(win, "BIBLIOTECA", ("▣", "▤", "▣", "▤")).pack(
            anchor="w", padx=22, pady=(20, 12))
        tree = ttk.Treeview(win, columns=("game", "location"), show="headings", height=13)
        tree.heading("game", text="JUEGO")
        tree.heading("location", text="EJECUTABLE / ORIGEN")
        tree.column("game", width=240)
        tree.column("location", width=540)
        tree.pack(fill="both", expand=True, padx=22)
        self.library_tree = tree
        tree.bind("<Double-1>", lambda _event: self.launch_selected())
        bar = tk.Frame(win, bg=BG)
        bar.pack(fill="x", padx=22, pady=14)
        add_exe = self.button(bar, "+ Añadir .exe", self.add_game)
        add_exe.pack(side="left")
        add_xbox = self.button(bar, "+ Añadir Xbox", self.add_xbox_game)
        add_xbox.pack(side="left", padx=8)
        remove = self.button(bar, "Quitar", self.remove_game)
        remove.pack(side="left")
        play = self.button(bar, "▶ Jugar", self.launch_selected, True)
        play.pack(side="right")
        self.controller_targets["library"] = [tree, add_exe, add_xbox, remove, play]
        win.protocol("WM_DELETE_WINDOW", self.close_library)
        self.populate()
        win.focus_force()
        tree.focus_set()

    def close_library(self):
        if self.library_window:
            self.library_window.destroy()
        self.library_window = self.library_tree = None
        self.controller_targets["library"] = []

    # --------------------------- MI PC / MENÚ WINDOWS ---------------------------
    def open_my_pc(self):
        """Show a file browser inside a launcher-owned window; folders stay in this view."""
        if self.pc_window and self.pc_window.winfo_exists():
            self.pc_window.deiconify()
            self.pc_window.lift()
            return

        win = tk.Toplevel(self)
        self.pc_window = win
        win.title("1766 AI GAMING | Mi PC")
        win.geometry("940x620")
        win.minsize(700, 450)
        win.configure(bg=BG)
        win.transient(self)

        top = tk.Frame(win, bg="#080e1d")
        top.pack(fill="x", padx=16, pady=(16, 10))
        self.section_heading(top, "MI PC  //  EXPLORADOR INTEGRADO",
                             ("▣", "▤", "▣", "▤")).pack(side="left", padx=8, pady=8)

        controls = tk.Frame(win, bg=BG)
        controls.pack(fill="x", padx=18, pady=(0, 10))
        self.button(controls, "← ATRÁS", self.pc_go_back).pack(side="left", padx=(0, 6))
        self.button(controls, "INICIO", self.pc_show_locations).pack(side="left", padx=6)
        self.button(controls, "↻ ACTUALIZAR", self.pc_refresh).pack(side="left", padx=6)
        self.button(controls, "PAPELERA", self.open_recycle_bin).pack(side="right", padx=6)

        self.pc_path_var = tk.StringVar(value="Este equipo")
        path_entry = tk.Entry(controls, textvariable=self.pc_path_var, bg="#0a1120",
                              fg="#e1eaff", insertbackground="white", relief="flat",
                              font=("Consolas", 9))
        path_entry.pack(side="left", fill="x", expand=True, padx=(12, 0), ipady=8)
        path_entry.bind("<Return>", lambda _event: self.pc_open_path(self.pc_path_var.get()))

        body = tk.Frame(win, bg=BG)
        body.pack(fill="both", expand=True, padx=18, pady=(0, 14))
        columns = ("name", "type", "location")
        self.pc_tree = ttk.Treeview(body, columns=columns, show="headings", selectmode="browse")
        self.pc_tree.heading("name", text="NOMBRE")
        self.pc_tree.heading("type", text="TIPO")
        self.pc_tree.heading("location", text="UBICACIÓN")
        self.pc_tree.column("name", width=330, anchor="w")
        self.pc_tree.column("type", width=120, anchor="center")
        self.pc_tree.column("location", width=400, anchor="w")
        scroll = ttk.Scrollbar(body, orient="vertical", command=self.pc_tree.yview)
        self.pc_tree.configure(yscrollcommand=scroll.set)
        self.pc_tree.pack(side="left", fill="both", expand=True)
        scroll.pack(side="right", fill="y")
        self.pc_tree.bind("<Double-1>", self.pc_open_selected)
        self.pc_tree.bind("<Return>", self.pc_open_selected)
        self.pc_history = []
        self.pc_current_path = None
        self.pc_show_locations()
        win.protocol("WM_DELETE_WINDOW", self.close_my_pc)
        win.focus_force()

    def close_my_pc(self):
        if self.pc_window and self.pc_window.winfo_exists():
            self.pc_window.destroy()
        self.pc_window = None
        self.pc_tree = None
        self.pc_current_path = None

    def pc_show_locations(self):
        """Show common user folders and available disk drives in the in-launcher browser."""
        if not self.pc_tree or not self.pc_tree.winfo_exists():
            return
        self.pc_current_path = None
        self.pc_path_var.set("Este equipo")
        self.pc_tree.delete(*self.pc_tree.get_children())
        home = Path.home()
        locations = [
            ("Escritorio", home / "Desktop"),
            ("Documentos", home / "Documents"),
            ("Descargas", home / "Downloads"),
            ("Imágenes", home / "Pictures"),
            ("Música", home / "Music"),
            ("Videos", home / "Videos"),
        ]
        for title, path in locations:
            if path.exists():
                self.pc_tree.insert("", "end", iid=str(path), values=(f"📁 {title}", "Carpeta", str(path)))
        if os.name == "nt":
            import string
            for letter in string.ascii_uppercase:
                drive = Path(f"{letter}:\\\\")
                if drive.exists():
                    self.pc_tree.insert("", "end", iid=str(drive), values=(f"💽 {drive}", "Unidad", str(drive)))
        self.pc_tree.insert("", "end", iid="__desktop__", values=("Escritorio (accesos)", "Accesos", "Carpeta de escritorio"))
        self.pc_tree.insert("", "end", iid="__recycle__", values=("Papelera de reciclaje", "Sistema", "Papelera de Windows"))

    def pc_open_path(self, raw_path, remember=True):
        if not self.pc_tree or not self.pc_tree.winfo_exists():
            return
        path = Path(os.path.expandvars(os.path.expanduser(str(raw_path).strip().strip('"'))))
        if not path.is_dir():
            messagebox.showwarning("MI PC", "Esa ubicación no existe o no es una carpeta.", parent=self.pc_window)
            return
        if remember and self.pc_current_path:
            self.pc_history.append(self.pc_current_path)
        self.pc_current_path = path
        self.pc_path_var.set(str(path))
        self.pc_tree.delete(*self.pc_tree.get_children())
        try:
            entries = sorted(path.iterdir(), key=lambda item: (not item.is_dir(), item.name.casefold()))
        except (OSError, PermissionError) as exc:
            messagebox.showerror("MI PC", f"No se puede leer esta carpeta.\n{exc}", parent=self.pc_window)
            return
        for item in entries:
            try:
                is_dir = item.is_dir()
                kind = "Carpeta" if is_dir else (item.suffix.upper().lstrip(".") or "Archivo")
                icon = "📁 " if is_dir else "📄 "
                self.pc_tree.insert("", "end", iid=str(item), values=(icon + item.name, kind, str(item)))
            except (OSError, PermissionError):
                continue

    def pc_open_selected(self, _event=None):
        if not self.pc_tree:
            return
        selected = self.pc_tree.selection()
        if not selected:
            return
        item_id = selected[0]
        if item_id == "__desktop__":
            desktop = Path.home() / "Desktop"
            if desktop.is_dir():
                self.pc_open_path(desktop)
            return
        if item_id == "__recycle__":
            self.open_recycle_bin()
            return
        path = Path(item_id)
        if path.is_dir():
            self.pc_open_path(path)
        elif path.is_file():
            try:
                if os.name == "nt":
                    os.startfile(str(path))
                else:
                    subprocess.Popen(["xdg-open", str(path)])
            except (OSError, AttributeError) as exc:
                messagebox.showerror("MI PC", f"No se pudo abrir el archivo.\n{exc}", parent=self.pc_window)

    def pc_go_back(self):
        if self.pc_history:
            previous = self.pc_history.pop()
            self.pc_open_path(previous, remember=False)
        else:
            self.pc_show_locations()

    def pc_refresh(self):
        if self.pc_current_path:
            self.pc_open_path(self.pc_current_path, remember=False)
        else:
            self.pc_show_locations()

    def open_recycle_bin(self):
        """Windows exposes the recycle bin as a shell namespace, not a normal disk folder."""
        try:
            if os.name == "nt":
                os.startfile("shell:RecycleBinFolder")
            else:
                messagebox.showinfo("Papelera", "La Papelera integrada está disponible en Windows.")
        except (OSError, AttributeError) as exc:
            messagebox.showerror("Papelera", f"No se pudo abrir la Papelera.\n{exc}",
                                 parent=self.pc_window or self)

    def open_windows_menu(self):
        """Search Windows Start-menu apps and launch them from the 1766 interface."""
        if self.windows_window and self.windows_window.winfo_exists():
            self.windows_window.deiconify()
            self.windows_window.lift()
            self.refresh_windows_apps()
            return
        win = tk.Toplevel(self)
        self.windows_window = win
        win.title("1766 AI GAMING | Menú Windows")
        win.geometry("760x590")
        win.minsize(600, 420)
        win.configure(bg=BG)
        win.transient(self)

        self.section_heading(win, "⊞ MENÚ WINDOWS  //  APLICACIONES",
                             ("⊞", "▣", "⊞", "▣")).pack(anchor="w", padx=22, pady=(20, 12))
        search_row = tk.Frame(win, bg=BG)
        search_row.pack(fill="x", padx=22, pady=(0, 10))
        self.windows_search_var = tk.StringVar()
        search = tk.Entry(search_row, textvariable=self.windows_search_var,
                          bg="#0a1120", fg="#e1eaff", insertbackground="white",
                          relief="flat", font=("Segoe UI", 11))
        search.pack(side="left", fill="x", expand=True, ipady=10)
        search.insert(0, "")
        search.bind("<KeyRelease>", lambda _event: self.filter_windows_apps())
        self.button(search_row, "↻ ACTUALIZAR", self.refresh_windows_apps).pack(side="right", padx=(8, 0))

        body = tk.Frame(win, bg=BG)
        body.pack(fill="both", expand=True, padx=22, pady=(0, 10))
        self.windows_app_list = tk.Listbox(body, bg="#0a1120", fg="#e1eaff",
                                           selectbackground="#17476a", selectforeground="white",
                                           relief="flat", bd=0, font=("Segoe UI", 10),
                                           activestyle="none")
        scroll = ttk.Scrollbar(body, orient="vertical", command=self.windows_app_list.yview)
        self.windows_app_list.configure(yscrollcommand=scroll.set)
        self.windows_app_list.pack(side="left", fill="both", expand=True)
        scroll.pack(side="right", fill="y")
        self.windows_app_list.bind("<Double-1>", self.launch_windows_app)
        self.windows_app_list.bind("<Return>", self.launch_windows_app)
        footer = tk.Frame(win, bg=BG)
        footer.pack(fill="x", padx=22, pady=(0, 18))
        self.button(footer, "ABRIR APLICACIÓN", self.launch_windows_app, primary=True).pack(side="right")
        tk.Label(footer, text="Buscá por nombre y hacé doble clic para iniciar.",
                 bg=BG, fg=MUTED, font=("Consolas", 8)).pack(side="left")
        win.protocol("WM_DELETE_WINDOW", self.close_windows_menu)
        self.refresh_windows_apps()
        win.focus_force()
        search.focus_set()

    def close_windows_menu(self):
        if self.windows_window and self.windows_window.winfo_exists():
            self.windows_window.destroy()
        self.windows_window = None
        self.windows_apps = []

    def refresh_windows_apps(self):
        if not self.windows_window or not self.windows_window.winfo_exists():
            return
        self.windows_app_list.delete(0, "end")
        self.windows_apps = []
        if os.name == "nt":
            try:
                result = subprocess.run(
                    ["powershell", "-NoProfile", "-Command",
                     "Get-StartApps | Select-Object Name,AppID | ConvertTo-Json -Compress"],
                    capture_output=True, text=True, timeout=20, check=True,
                    creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
                data = json.loads(result.stdout or "[]")
                if isinstance(data, dict):
                    data = [data]
                self.windows_apps = [
                    {"name": str(app.get("Name", "")).strip(),
                     "app_id": str(app.get("AppID", "")).strip()}
                    for app in data if app.get("Name") and app.get("AppID")
                ]
            except (OSError, subprocess.SubprocessError, ValueError, json.JSONDecodeError):
                self.windows_apps = []

            # Fallback and supplement: collect classic desktop shortcuts too.
            # Get-StartApps may return no data on some Windows configurations.
            start_menu_dirs = [
                os.path.join(os.environ.get("APPDATA", ""), r"Microsoft\\Windows\\Start Menu\\Programs"),
                os.path.join(os.environ.get("PROGRAMDATA", ""), r"Microsoft\\Windows\\Start Menu\\Programs"),
            ]
            known_paths = {app.get("path", "").casefold() for app in self.windows_apps}
            known_names = {app["name"].casefold() for app in self.windows_apps}
            for base in start_menu_dirs:
                if not base or not os.path.isdir(base):
                    continue
                for folder, _dirs, files in os.walk(base):
                    for filename in files:
                        if not filename.lower().endswith((".lnk", ".url")):
                            continue
                        name = os.path.splitext(filename)[0].strip()
                        shortcut = os.path.join(folder, filename)
                        if name and name.casefold() not in known_names and shortcut.casefold() not in known_paths:
                            self.windows_apps.append({
                                "name": name, "app_id": "", "path": shortcut
                            })
                            known_names.add(name.casefold())
                            known_paths.add(shortcut.casefold())

        self.windows_apps.sort(key=lambda app: app["name"].casefold())
        self.filter_windows_apps()

    def filter_windows_apps(self):
        if not hasattr(self, "windows_app_list") or not self.windows_app_list.winfo_exists():
            return
        query = self.windows_search_var.get().strip().casefold()
        self.windows_app_list.delete(0, "end")
        self.windows_visible_apps = [
            app for app in self.windows_apps if query in app["name"].casefold()
        ]
        for app in self.windows_visible_apps:
            self.windows_app_list.insert("end", "  " + app["name"])
        if not self.windows_visible_apps:
            self.windows_app_list.insert("end", "No se encontraron aplicaciones.")

    def launch_windows_app(self, _event=None):
        if not hasattr(self, "windows_app_list"):
            return
        selected = self.windows_app_list.curselection()
        if not selected or selected[0] >= len(getattr(self, "windows_visible_apps", [])):
            return
        app = self.windows_visible_apps[selected[0]]
        try:
            if app.get("app_id"):
                subprocess.Popen(["explorer.exe", "shell:AppsFolder\\" + app["app_id"]])
            elif app.get("path"):
                os.startfile(app["path"])
        except (OSError, AttributeError) as exc:
            messagebox.showerror("Menú Windows", f"No se pudo iniciar {app['name']}.\n{exc}",
                                 parent=self.windows_window)

    def open_performance(self):
        if self.performance_window and self.performance_window.winfo_exists():
            self.performance_window.lift()
            return
        win = tk.Toplevel(self)
        self.performance_window = win
        win.title("1766 AI GAMING | Sistema")
        win.geometry("620x390")
        win.configure(bg=BG)
        win.transient(self)
        self.section_heading(win, "RENDIMIENTO DEL SISTEMA", ("◉", "◎", "◉", "◎")).pack(
            anchor="w", padx=24, pady=(22, 6))
        tk.Label(win, text="Lecturas en vivo · CPU y RAM se actualizan cada segundo",
                 bg=BG, fg=MUTED, font=("Consolas", 9)).pack(anchor="w", padx=24, pady=(0, 18))
        grid = tk.Frame(win, bg=BG)
        grid.pack(fill="x", padx=18)
        for key, title, fallback in [("cpu", "CPU", "Esperando lectura…"),
                                     ("ram", "MEMORIA RAM", "Esperando lectura…"),
                                     ("gpu", "GPU", "Integración pendiente"),
                                     ("fps", "FPS", "Integración pendiente")]:
            card = tk.Frame(grid, bg=PANEL, padx=16, pady=16,
                            highlightbackground="#27364a", highlightthickness=1)
            card.grid(row=0 if key in ("cpu", "ram") else 1,
                      column=0 if key in ("cpu", "gpu") else 1, sticky="nsew", padx=6, pady=6)
            tk.Label(card, text=title, bg=PANEL, fg=MUTED,
                     font=("Consolas", 9, "bold")).pack(anchor="w")
            val = tk.Label(card, text=fallback, bg=PANEL, fg="#e1eaff",
                           font=("Consolas", 15, "bold"))
            val.pack(anchor="w", pady=(10, 0))
            self.performance_values[key] = val
        for column in (0, 1):
            grid.columnconfigure(column, weight=1, uniform="metrics")
        win.protocol("WM_DELETE_WINDOW", self.close_performance)
        back = self.button(win, "Volver", self.navigate_home)
        back.pack(anchor="e", padx=24, pady=12)
        self.controller_targets["performance"] = [back]
        win.focus_force()
        back.focus_set()
        self.update_performance_window()

    def update_performance_window(self):
        if not self.performance_window or not self.performance_window.winfo_exists():
            return
        if self.latest_cpu is not None:
            self.performance_values["cpu"].configure(text=f"{self.latest_cpu}%")
        if self.latest_ram:
            ram = self.latest_ram
            self.performance_values["ram"].configure(text=f"{ram[0]:.1f} / {ram[1]:.1f} GB · {ram[2]}%")

    def close_performance(self):
        if self.performance_window:
            self.performance_window.destroy()
        self.performance_window = None
        self.performance_values.clear()
        self.controller_targets["performance"] = []

    def open_settings(self):
        if hasattr(self, "settings_window") and self.settings_window and self.settings_window.winfo_exists():
            self.settings_window.lift()
            return
        win = tk.Toplevel(self)
        self.settings_window = win
        win.title("1766 AI GAMING | Configuración")
        win.geometry("570x380")
        win.configure(bg=BG)
        win.transient(self)
        self.section_heading(win, "PERSONALIZACIÓN", ("✣", "✢", "✣", "✢")).pack(
            anchor="w", padx=24, pady=(22, 18))
        tk.Label(win, text="Color de acento", bg=BG, fg="#e1eaff",
                 font=("Consolas", 10, "bold")).pack(anchor="w", padx=24)
        colors = [("Azul eléctrico", "#29d9ff"), ("Azul hielo", "#78aaff"), ("Violeta", "#a052ff")]
        colorbar = tk.Frame(win, bg=BG)
        colorbar.pack(anchor="w", padx=24, pady=10)
        setting_targets = []
        for title, color in colors:
            choice = tk.Button(colorbar, text=title, command=lambda c=color: self.set_accent(c),
                               bg=color, fg="white", activebackground=color, relief="flat",
                               padx=14, pady=8, cursor="hand2")
            choice.pack(side="left", padx=(0, 8))
            setting_targets.append(choice)
        tk.Label(win, text="Transparencia de ventana", bg=BG, fg="#e1eaff",
                 font=("Consolas", 10, "bold")).pack(anchor="w", padx=24, pady=(12, 0))
        self.opacity_var = tk.DoubleVar(value=self.settings.get("opacity", 0.95) * 100)
        opacity_scale = tk.Scale(win, from_=85, to=100, orient="horizontal", resolution=1, length=400,
                                 variable=self.opacity_var, command=self.set_opacity, bg=BG, fg="#e1eaff",
                                 troughcolor="#1c2a45", highlightthickness=0, activebackground=ACCENT,
                                 showvalue=True, takefocus=True)
        opacity_scale.pack(anchor="w", padx=20, pady=6)
        setting_targets.append(opacity_scale)
        back = self.button(win, "Volver", self.navigate_home)
        back.pack(anchor="e", padx=24, pady=(0, 12))
        setting_targets.append(back)
        self.controller_targets["settings"] = setting_targets
        tk.Label(win, text="Los cambios se guardan automáticamente.", bg=BG, fg=MUTED,
                 font=("Consolas", 9)).pack(anchor="w", padx=24, pady=(8, 0))
        win.protocol("WM_DELETE_WINDOW", self.close_settings)
        win.focus_force()
        setting_targets[0].focus_set()

    def close_settings(self):
        if getattr(self, "settings_window", None):
            self.settings_window.destroy()
        self.settings_window = None
        self.controller_targets["settings"] = []

    def set_accent(self, color):
        global ACCENT
        ACCENT = color
        self.settings["accent"] = color
        self.glow.configure(bg=color)
        self.hero_glow.configure(bg=color)
        self.brand_label.configure(fg=color)
        self.mode_btn.configure(bg=color if not self.gaming else "#172b4a")
        self.save_settings()
        self.draw_brand_mark()

    def set_opacity(self, value):
        opacity = int(float(value)) / 100
        self.settings["opacity"] = opacity
        try:
            self.attributes("-alpha", opacity)
        except tk.TclError:
            pass
        self.save_settings()

    def load_settings(self):
        try:
            data = json.loads((DATA_DIR / "settings.json").read_text(encoding="utf-8"))
            if data.get("accent") not in ("#29d9ff", "#78aaff", "#a052ff"):
                data["accent"] = "#29d9ff"
            data["opacity"] = min(1.0, max(0.85, float(data.get("opacity", 0.95))))
            return data
        except (OSError, ValueError, TypeError):
            return {"accent": "#29d9ff", "opacity": 0.95}

    def save_settings(self):
        DATA_DIR.mkdir(parents=True, exist_ok=True)
        (DATA_DIR / "settings.json").write_text(json.dumps(self.settings, indent=2), encoding="utf-8")

    def draw_brand_mark(self, _event=None):
        """Draw the 1766 AI neon wordmark as a screen watermark in the gaming panel."""
        canvas = self.hero_mark
        canvas.delete("all")
        width, height = canvas.winfo_width(), canvas.winfo_height()
        if width < 20 or height < 20:
            return
        # Angular emblem plus layered cyan lettering create a simple neon glow.
        x, y = width - 230, height // 2
        # The animated scan and moving HUD slashes frame the 1766 AI wordmark.
        pulse = (math.sin(self.logo_phase * 0.12) + 1) / 2
        scan = (self.logo_phase % 72) / 72
        canvas.create_line(x - 150, y, x - 116, y, fill="#172b4a", width=2)
        canvas.create_line(x - 112, y - 29, x - 106, y - 29,
                           x - 96 + pulse * 5, y - 17, x - 96 + pulse * 5, y + 17,
                           x - 106, y + 29, x - 112, y + 29,
                           fill="#29d9ff", width=2)
        slash_x = x + 122 + math.sin(self.logo_phase * 0.07) * 7
        canvas.create_line(x + 111, y - 29, slash_x, y - 29, x + 135, y - 16,
                           fill="#253d65", width=2)
        canvas.create_line(x + 111, y + 29, slash_x, y + 29, x + 135, y + 16,
                           fill="#253d65", width=2)
        canvas.create_text(x + 5, y + 2, text="1766 AI", fill="#172640",
                           font=("Consolas", 27, "bold"), anchor="center")
        canvas.create_text(x + 5, y, text="1766 AI", fill=ACCENT,
                           font=("Consolas", 27, "bold"), anchor="center")
        beam_x = x - 70 + scan * 150
        canvas.create_line(beam_x, y - 17, beam_x + 10, y + 17,
                           fill="#e1eaff", width=2)
        canvas.create_line(width - 155, height - 15, width - 155 + pulse * 36,
                           height - 15, fill=ACCENT, width=2)
        canvas.create_text(width - 13, 14, text="1766  /  ONLINE",
                           fill="#62dcff", font=("Consolas", 7, "bold"), anchor="ne")

    def animate_brand_mark(self):
        if not self.winfo_exists():
            return
        self.logo_phase += 1
        if self.state() != "iconic":
            self.draw_brand_mark()
        self.after(90, self.animate_brand_mark)

    def load_games(self):
        try:
            source = GAMES_FILE if GAMES_FILE.exists() else LEGACY_GAMES_FILE
            data = json.loads(source.read_text(encoding="utf-8"))
            return [g for g in data if isinstance(g, dict) and (g.get("path") or g.get("app_id") or g.get("launch_uri"))]
        except (OSError, ValueError, TypeError):
            return []

    def save_games(self):
        DATA_DIR.mkdir(parents=True, exist_ok=True)
        GAMES_FILE.write_text(json.dumps(self.games, indent=2, ensure_ascii=False), encoding="utf-8")

    def populate(self):
        trees = [self.table]
        if self.library_tree and self.library_tree.winfo_exists():
            trees.append(self.library_tree)
        for tree in trees:
            for item in tree.get_children():
                tree.delete(item)
            for i, game in enumerate(self.games):
                location = game.get("path") or game.get("tag", "Juego instalado")
                values = (game["name"], location) if tree is self.library_tree else (
                    game["name"], location, "▶  INICIAR")
                tree.insert("", "end", iid=str(i), values=values)
        if self.games and self.table.exists("0"):
            self.table.selection_set("0")
            self.table.focus("0")
        if hasattr(self, "game_tiles_frame"):
            self.refresh_game_tiles()

    def refresh_game_tiles(self):
        for child in self.game_tiles_frame.winfo_children():
            child.destroy()
        self.game_tile_buttons.clear()
        if not self.games:
            empty = tk.Frame(self.game_tiles_frame, bg="#0a1120",
                             highlightbackground="#172b4a", highlightthickness=1)
            empty.pack(fill="both", expand=True)
            tk.Label(empty, text=">_", bg="#0a1120", fg=PS_BLUE,
                     font=("Consolas", 22, "bold")).pack(side="left", padx=(24, 12), pady=8)
            tk.Label(empty, text="SIN_JUEGOS  //  añade un juego para comenzar",
                     bg="#0a1120", fg="#b6c6e3", font=("Consolas", 10)).pack(side="left")
            return
        palette = ["#0d172a", "#101c32", "#101b30", "#121e35", "#0d172a"]
        for index, game in enumerate(self.games[:5]):
            selected = index == 0
            tile = tk.Button(
                self.game_tiles_frame,
                text=f"{game['name']}\n[ {game.get('tag', 'GAME')} ]\n▶ JUGAR",
                command=lambda i=index: self.launch_game_index(i),
                bg=palette[index % len(palette)], fg="#eef5ff",
                activebackground="#172b4a", activeforeground="#f3f7ff",
                relief="flat", bd=0, highlightthickness=1,
                highlightbackground=PS_BLUE if selected else "#172b4a",
                font=("Consolas", 9, "bold"), cursor="hand2", justify="center",
                wraplength=145, padx=10, pady=8,
            )
            tile.pack(side="left", fill="both", expand=True, padx=(0, 8))
            self.game_tile_buttons.append(tile)
        self.controller_targets["home"] = (
            self.nav_widgets + [self.table] + self.game_tile_buttons +
            [self.home_add_exe, self.home_add_xbox, self.home_play,
             self.home_remove, self.mode_btn]
        )

    def launch_game_index(self, index):
        if index < 0 or index >= len(self.games):
            return
        item = str(index)
        if self.table.exists(item):
            self.table.selection_set(item)
            self.table.focus(item)
            self.table.see(item)
        self.launch_selected(self.table)

    def handle_home_action_click(self, event):
        if self.table.identify_column(event.x) != "#3":
            return None
        row = self.table.identify_row(event.y)
        if row:
            self.launch_game_index(int(row))
            return "break"
        return None
    def select_game_tile(self, index):
        if index >= len(self.games):
            return
        item = str(index)
        self.table.selection_set(item)
        self.table.focus(item)
        self.table.see(item)
        for tile_index, tile in enumerate(self.game_tile_buttons):
            tile.configure(highlightbackground=PS_BLUE if tile_index == index else "#172b4a")

    def sync_tile_selection(self, _event=None):
        selection = self.table.selection()
        if not selection:
            return
        index = int(selection[0])
        for tile_index, tile in enumerate(self.game_tile_buttons):
            tile.configure(highlightbackground=PS_BLUE if tile_index == index else "#172b4a")

    def add_game(self):
        path = filedialog.askopenfilename(title="Selecciona el ejecutable del juego",
                                          filetypes=[("Aplicaciones", "*.exe"), ("Todos los archivos", "*.*")])
        if not path:
            return
        name = Path(path).stem.replace("_", " ").replace("-", " ")
        self.games.append({"name": name, "path": path, "tag": "PC"})
        self.save_games()
        self.populate()

    def scan_installed_games(self):
        """Discover installed games automatically in the background at startup."""
        if getattr(self, "discovery_started", False):
            return
        self.discovery_started = True
        threading.Thread(target=self._discover_installed_games, daemon=True).start()

    def _discover_installed_games(self):
        """Find installed Steam, Epic and Xbox/Windows games from local records."""
        found = []
        known_keys = {
            (g.get("app_id") or "").lower() or (g.get("launch_uri") or "").lower()
            or os.path.normcase(g.get("path") or "") for g in self.games
        }
        known_names = {re.sub(r"[^a-z0-9]+", "", g.get("name", "").lower()) for g in self.games}

        def add_game(game):
            key = ((game.get("app_id") or "").lower()
                   or (game.get("launch_uri") or "").lower()
                   or os.path.normcase(game.get("path") or ""))
            normalized_name = re.sub(r"[^a-z0-9]+", "", game.get("name", "").lower())
            # Epic debe poder reemplazar una entrada antigua de Xbox con el mismo nombre.
            if game.get("tag") == "EPIC":
                found.append(game)
                known_keys.add(key)
                known_names.add(normalized_name)
            elif key and key not in known_keys and normalized_name not in known_names:
                known_keys.add(key)
                known_names.add(normalized_name)
                found.append(game)

        # Steam app manifests exist only for installed titles. Follow library paths
        # registered in libraryfolders.vdf, including secondary drives.
        steam_roots = set()
        for base in (os.environ.get("PROGRAMFILES(X86)"), os.environ.get("PROGRAMFILES"),
                     os.environ.get("LOCALAPPDATA")):
            if base:
                for candidate in (Path(base) / "Steam", Path(base) / "Programs" / "Steam"):
                    if (candidate / "steamapps").is_dir():
                        steam_roots.add(candidate)
        try:
            registry_path = subprocess.run(
                ["reg", "query", r"HKCU\Software\Valve\Steam", "/v", "SteamPath"],
                capture_output=True, text=True, timeout=4, check=True,
            ).stdout
            match = re.search(r"SteamPath\s+REG_SZ\s+(.+)", registry_path, re.IGNORECASE)
            if match:
                registered_steam = Path(match.group(1).strip())
                if (registered_steam / "steamapps").is_dir():
                    steam_roots.add(registered_steam)
        except (OSError, subprocess.SubprocessError):
            pass
        for steam_root in tuple(steam_roots):
            library_file = steam_root / "steamapps" / "libraryfolders.vdf"
            try:
                content = library_file.read_text(encoding="utf-8", errors="ignore")
                for raw_path in re.findall(r'"path"\s*"([^"]+)"', content):
                    lib = Path(raw_path.replace("\\\\", "\\"))
                    if (lib / "steamapps").is_dir():
                        steam_roots.add(lib)
            except OSError:
                pass
        for steam_root in steam_roots:
            for manifest in (steam_root / "steamapps").glob("appmanifest_*.acf"):
                try:
                    data = manifest.read_text(encoding="utf-8", errors="ignore")
                    name_match = re.search(r'"name"\s*"([^"]+)"', data)
                    app_match = re.search(r'"appid"\s*"(\d+)"', data)
                    if name_match and app_match:
                        add_game({"name": name_match.group(1), "path": "",
                                  "launch_uri": f"steam://rungameid/{app_match.group(1)}",
                                  "tag": "STEAM"})
                except OSError:
                    continue

        # Epic writes one .item manifest per installed game.
        program_data = Path(os.environ.get("PROGRAMDATA", r"C:\ProgramData"))
        epic_manifests = program_data / "Epic" / "EpicGamesLauncher" / "Data" / "Manifests"
        if epic_manifests.is_dir():
            for manifest in epic_manifests.glob("*.item"):
                try:
                    data = json.loads(manifest.read_text(encoding="utf-8"))
                    name, app_name = data.get("DisplayName"), data.get("AppName")
                    if not name or not app_name:
                        continue
                    exe = data.get("LaunchExecutable", "").replace("/", os.sep)
                    location = Path(data.get("InstallLocation", ""))
                    executable = location / exe if exe else None
                    add_game({"name": name, "path": str(executable) if executable and executable.is_file() else "",
                              "launch_uri": f"com.epicgames.launcher://apps/{app_name}?action=launch&silent=true",
                              "tag": "EPIC"})
                except (OSError, ValueError, TypeError):
                    continue

        # Xbox and Microsoft Store games are launchable through AppsFolder. Skip
        # Windows utilities and the Xbox app itself, which are not games.
        excluded = ("xbox", "game bar", "gaming services", "store", "settings", "calculator",
                    "photos", "camera", "notepad", "terminal", "edge", "feedback hub",
                    "get help", "clock", "paint", "snipping tool", "maps", "mail", "weather")
        try:
            result = subprocess.run(
                ["powershell", "-NoProfile", "-Command",
                 "Get-StartApps | Select-Object Name,AppID | ConvertTo-Json -Compress"],
                capture_output=True, text=True, timeout=20, check=True,
            )
            apps = json.loads(result.stdout)
            if isinstance(apps, dict):
                apps = [apps]
            for app in apps:
                if not isinstance(app, dict):
                    continue
                name, app_id = app.get("Name"), app.get("AppID")
                if not name or not app_id or "!" not in app_id:
                    continue
                if any(term in name.lower() for term in excluded):
                    continue
                add_game({"name": name, "path": "", "app_id": app_id, "tag": "XBOX"})
        except (OSError, subprocess.SubprocessError, ValueError, TypeError):
            pass

        if found:
            try:
                self.after(0, self._apply_discovered_games, found)
            except tk.TclError:
                pass

    def _apply_discovered_games(self, found):
        known_names = {re.sub(r"[^a-z0-9]+", "", g.get("name", "").lower()) for g in self.games}
        known_ids = {g.get("app_id") or g.get("launch_uri") or os.path.normcase(g.get("path") or "")
                     for g in self.games}
        new_games = []
        changed = False
        for game in found:
            name_key = re.sub(r"[^a-z0-9]+", "", game.get("name", "").lower())
            game_key = game.get("app_id") or game.get("launch_uri") or os.path.normcase(game.get("path") or "")
            if game.get("tag") == "EPIC":
                # Si el mismo juego estaba agregado como Xbox, sustituir esa entrada.
                old_index = next((i for i, old in enumerate(self.games)
                                  if re.sub(r"[^a-z0-9]+", "", old.get("name", "").lower()) == name_key
                                  and old.get("app_id")), None)
                if old_index is not None:
                    self.games[old_index] = game
                    changed = True
                    known_names.add(name_key)
                    known_ids.add(game_key)
                    continue
            if name_key not in known_names and game_key not in known_ids:
                known_names.add(name_key)
                known_ids.add(game_key)
                new_games.append(game)
        if new_games or changed:
            self.games.extend(new_games)
            self.save_games()
            self.populate()

    def add_xbox_game(self):
        # Windows publishes installed packaged apps through the Start Apps list.
        # Query only names and app IDs; no protected WindowsApps access is needed.
        try:
            result = subprocess.run(
                ["powershell", "-NoProfile", "-Command",
                 "Get-StartApps | Where-Object { $_.Name -match 'Fortnite|Xbox' } | "
                 "Select-Object Name,AppID | ConvertTo-Json -Compress"],
                capture_output=True, text=True, timeout=12, check=True,
            )
            apps = json.loads(result.stdout)
            if isinstance(apps, dict):
                apps = [apps]
            apps = [a for a in apps if a.get("Name") and a.get("AppID")]
        except (OSError, subprocess.SubprocessError, ValueError):
            apps = []
        if not apps:
            messagebox.showinfo("1766 AI GAMING", "No encontré Fortnite ni juegos Xbox registrados en el menú Inicio.")
            return
        fortnite = next((a for a in apps if "fortnite" in a["Name"].lower()), None)
        if fortnite:
            app = fortnite
        else:
            names = "\n".join(a["Name"] for a in apps)
            messagebox.showinfo("Aplicaciones Xbox encontradas", names)
            return
        if any(g.get("app_id") == app["AppID"] for g in self.games):
            messagebox.showinfo("1766 AI GAMING", "Fortnite ya está en tu biblioteca.")
            return
        self.games.append({"name": app["Name"], "path": "", "app_id": app["AppID"], "tag": "XBOX"})
        self.save_games()
        self.populate()
        messagebox.showinfo("1766 AI GAMING", "Fortnite se añadió a tu biblioteca.")

    def remove_game(self, tree=None):
        if tree is None:
            tree = self.library_tree if self.library_tree and self.library_tree.selection() else self.table
        sel = tree.selection()
        if not sel:
            return
        del self.games[int(sel[0])]
        self.save_games()
        self.populate()

    def launch_selected(self, tree=None):
        if tree is None:
            tree = self.library_tree if self.library_tree and self.library_tree.selection() else self.table
        sel = tree.selection()
        if not sel:
            messagebox.showinfo("1766 AI GAMING", "Selecciona un juego de tu biblioteca.")
            return
        game = self.games[int(sel[0])]
        app_id = game.get("app_id")
        launch_uri = game.get("launch_uri")
        if launch_uri and (game.get("tag") == "EPIC" or launch_uri.lower().startswith("com.epicgames.launcher://")):
            try:
                os.startfile(launch_uri)
            except (AttributeError, OSError) as exc:
                messagebox.showerror("No se pudo iniciar", f"No se pudo abrir {game.get('name', 'el juego')} mediante Epic Games.\n{exc}")
            return
        if app_id:
            try:
                # Windows documents AppsFolder activation through Explorer for AUMIDs.
                subprocess.Popen(["explorer.exe", "shell:AppsFolder\\" + app_id])
            except OSError as exc:
                messagebox.showerror("No se pudo iniciar", f"{game.get('name', 'Aplicación')}: {exc}")
            return
        if launch_uri:
            try:
                os.startfile(launch_uri)
            except (AttributeError, OSError) as exc:
                messagebox.showerror("No se pudo iniciar", str(exc))
            return
        path = game["path"]
        if not Path(path).is_file():
            messagebox.showerror("No se encontró el juego", f"Revisa la ruta del ejecutable:\n{path}")
            return
        try:
            subprocess.Popen([path], cwd=str(Path(path).parent))
        except OSError as exc:
            messagebox.showerror("No se pudo iniciar", str(exc))

    def toggle_gaming(self):
        self.gaming = not self.gaming
        self.mode_btn.configure(text="DESACTIVAR MODO" if self.gaming else "ACTIVAR MODO",
                                bg="#172b4a" if self.gaming else ACCENT)
        self.gaming_hint.configure(text="Perfil del launcher activo. No se han cerrado procesos ni cambiado Windows."
                                   if self.gaming else "Activa un perfil local del launcher. La optimización del sistema llegará después.")

    def refresh_metrics(self):
        cpu, ram = self.monitor.sample()
        if cpu is not None:
            self.latest_cpu = cpu
        if ram:
            self.latest_ram = ram
        if cpu is not None:
            self.metric_values["cpu"].configure(text=f"{cpu}%")
        if ram:
            self.metric_values["ram"].configure(text=f"{ram[0]:.1f} / {ram[1]:.1f} GB  ·  {ram[2]}%")
        self.clock.configure(text=time.strftime("%a, %d %b  •  %H:%M"))
        self.update_performance_window()
        self.after(1000, self.refresh_metrics)


if __name__ == "__main__":
    Launcher().mainloop()

