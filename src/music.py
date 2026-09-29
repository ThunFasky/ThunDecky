import os
import sys
import time
import datetime
import pygame
import io
import threading
import math
import numpy as np
import json
import cv2
import shutil
import hashlib
import random
import ctypes
import ctypes.wintypes
from tkinter import filedialog, Tk

# --- Mutagen ---
import mutagen
from mutagen.mp3 import MP3
from mutagen.id3 import ID3, APIC
from mutagen.flac import FLAC
from mutagen.wave import WAVE
from mutagen.oggvorbis import OggVorbis
from mutagen.mp4 import MP4, MP4Cover
from mutagen.asf import ASF

from PIL import Image, ImageStat, ImageFilter

# --- MoviePy / FFmpeg ---
try:
    import imageio_ffmpeg
    os.environ["FFMPEG_BINARY"] = imageio_ffmpeg.get_ffmpeg_exe()
except Exception as e:
    print(f"FFmpeg setup error: {e}")

try:
    from moviepy import VideoFileClip, AudioFileClip
except ImportError:
    print("Warning: moviepy not installed. Video/M4A/WMA audio will not play.")
    VideoFileClip = None
    AudioFileClip = None

# --- 設定・定数 ---
APP_NAME = "ThunDecky"

SCREEN_SIZE = (600, 600)
BG_COLOR = (40, 40, 40)
SHADOW_COLOR = (20, 20, 20)  # 影の色
MAIN_COLOR = (247, 201, 4)
TEXT_COLOR = MAIN_COLOR
PANEL_FILL = (18, 18, 18)
PANEL_FILL_2 = (26, 26, 26)
SUB_LINE_COLOR = (95, 95, 95)
FAINT_ACCENT = (105, 84, 0)
STATE_FILE = "player_state.json"
TEMP_DIR = "temp_audio_cache"

THUMB_MAP_FILE = "thumb_map.json"
THUMB_DATA_DIR = "saved_thumbnails"
TRACK_VOLUME_MAP_FILE = "track_volume_map.json"

FONT_FILE_UI = os.path.join("assets", "fonts", "x14y20pxScoreDozer.ttf")
FONT_FILE_TITLE = os.path.join("assets", "fonts", "PixelMplus12-Bold.ttf")

ART_SIZE = 250
SIDE_ART_SIZE = 180
FRAME_GAP = 5
FRAME_WIDTH = 8
TRACK_VOL_X = 52
TRACK_VOL_TOP = 150
TRACK_VOL_BOTTOM = 355
MASTER_VOL_TOP = 405
MASTER_VOL_BOTTOM = 575
VOLUME_MIN_PERCENT = 1
VOLUME_MAX_PERCENT = 100
TRACK_VOLUME_STEP = 0.1          # 曲ごと音量の最小刻み（%）
MASTER_VOLUME_MIN = 0.0
MASTER_VOLUME_MAX = 25.0
MASTER_VOLUME_STEP = 0.25        # ←→キーでの増減刻み
MASTER_VOLUME_DRAG_STEP = 0.05   # ドラッグ時の最小刻み
VOLUME_SLIDER_CURVE = 2.0        # スライダー位置→値のカーブ（1=従来の直線。大きいほど下側=小音量域が細かくなる）
TRACK_VOLUME_WHEEL_STEP = 0.5    # 曲音量バー上でのホイール微調整の刻み（%）
MASTER_VOLUME_WHEEL_STEP = 0.05  # 全体音量バー上でのホイール微調整の刻み

# --- レイアウト（2カラム） ---
PANEL_X = 450                       # 右オレンジパネルの左端
LEFT_W = PANEL_X                    # 左ダーク領域の幅
ART_CENTER = (230, 255)            # 中央アートの中心
V_SPACING = 230                     # 縦カルーセルの曲間隔

# --- アプリ全体のオレンジ枠（ボーダーレス用） ---
BORDER_WIDTH = 3

ANIM_DURATION = 0.4
WHEEL_ANIM_DURATION = 0.22   # ホイール曲送りのアニメ時間（短め=キビキビ動く）
EASE_EXP = 4

# --- 操作感度 ---
ACTION_COOLDOWN = 0.25
SCROLL_INTERVAL = 0.25
HOLD_DELAY      = 0.5
AUDIO_LOAD_DELAY = 0.4

SHADOW_OFFSET = 4

# --- スワイプ操作（縦） ---
SWIPE_SPACING        = 230   # スワイプ追従感度（カルーセル間隔と同じ）
SWIPE_THRESHOLD      = 0.3   # 中央からこの割合を超えて離すと曲送り確定
CLICK_MOVE_TOLERANCE = 8     # この移動量未満ならクリック扱い（スワイプ無効）

# --- オーディオビジュアライザー（中央ジャケット左右） ---
VIS_NUM_BARS      = 24    # 片側のバー本数（上下に隙間なく積む）
VIS_MAX_LEN       = 58    # バーが外側へ伸びる最大長(px)
VIS_GAP_FROM_ART  = 16    # ジャケット枠外側からバー開始までの余白(px)
VIS_ANALYSIS_FPS  = 30    # スペクトル解析のフレームレート
VIS_SAMPLE_RATE   = 22050 # 解析用ダウンサンプルレート
VIS_FFT_WIN       = 2048  # FFT窓サイズ
VIS_ATTACK        = 0.55  # バーが伸びる時の追従係数（速い）
VIS_DECAY         = 0.18  # バーが縮む時の追従係数（遅い）


def resource_path(relative_path):
    try:
        base_path = sys._MEIPASS
    except Exception:
        base_path = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    return os.path.join(base_path, relative_path)


# --- ウィンドウ崩壊（黒帯）対策 ---------------------------------------------
WINDOW_LOG_FILE = "window_guard.log"


def log_window_event(msg):
    """ウィンドウ異常を検知/修復した時だけ追記する。再発時の原因特定用。"""
    try:
        with open(WINDOW_LOG_FILE, "a", encoding="utf-8") as f:
            f.write(f"{datetime.datetime.now():%Y-%m-%d %H:%M:%S} {msg}\n")
    except Exception:
        pass


def setup_windows_dpi():
    """set_mode より前に必ず呼ぶこと。

    プロセスを Per-Monitor-V2 DPI aware に固定する。
    宣言しないと EXE 化時（マニフェスト無し）は DPI 仮想化され、
      * OS がウィンドウを勝手に拡大する
      * GetClientRect が論理座標（=常に600x600）を返して監視が素通りする
    の二重苦で、600x600 の描画面との差分がそのまま黒帯になる。
    python.exe 直起動は元から PerMonitorV2 なので、EXE と挙動を揃える意味もある。
    """
    if sys.platform != "win32":
        return
    # SDL は video サブシステム初期化時にこの hint を読む。set_mode 後では効かない
    os.environ.setdefault("SDL_WINDOWS_DPI_AWARENESS", "permonitorv2")
    os.environ.setdefault("SDL_WINDOWS_DPI_SCALING", "0")

    user32 = ctypes.windll.user32
    # DPI_AWARENESS_CONTEXT_PER_MONITOR_AWARE_V2 = -4 (Win10 1703+)
    try:
        user32.SetProcessDpiAwarenessContext.argtypes = [ctypes.c_ssize_t]
        user32.SetProcessDpiAwarenessContext.restype = ctypes.c_bool
        if user32.SetProcessDpiAwarenessContext(-4):
            return
    except Exception:
        pass
    try:
        # PROCESS_PER_MONITOR_DPI_AWARE = 2 (Win8.1+)
        ctypes.windll.shcore.SetProcessDpiAwareness(2)
        return
    except Exception:
        pass
    try:
        user32.SetProcessDPIAware()
    except Exception:
        pass


# --- 幾何学模様クラス（60°固定・塗りつぶし四角＆FUIドット群） ---
class GeometricShape:
    TYPES = ["filled_square", "filled_square_small", "dot_grid", "single_dot", "ring"]

    def __init__(self, screen_w, screen_h):
        self.screen_w = screen_w
        self.screen_h = screen_h
        # 画面上では「左下 → 右上」に見える、水平から30°の傾き
        self.angle = math.radians(-30)
        self.reset_pos(initial=True)

    def reset_pos(self, initial=False):
        self.type = random.choice(self.TYPES)
        self.depth = random.random()

        # 全体的に以前より大きめ
        self.size = int(24 + self.depth * 82)
        self.alpha = int(20 + self.depth * 40)
        self.line_w = 1 if self.depth < 0.55 else 2
        self.color = (*MAIN_COLOR, self.alpha)

        # 図形の傾きと進行方向を完全に一致させる
        speed = 0.34 + self.depth * 1.05
        self.vx = speed * math.cos(self.angle)
        self.vy = speed * math.sin(self.angle)

        if initial:
            # 初期配置は画面全体に散らす
            self.x = random.uniform(-180, self.screen_w + 180)
            self.y = random.uniform(-120, self.screen_h + 120)
        else:
            # 進行方向は右上。流入する辺＝「下辺の全幅」と「左辺の全高」から
            # 再出現させ、画面全体を図形が流れるようにする
            if random.random() < 0.5:
                # 下辺（全幅）から上がってくる
                self.x = random.uniform(-120, self.screen_w + 60)
                self.y = random.uniform(self.screen_h + 20, self.screen_h + 160)
            else:
                # 左辺（全高）から入ってくる
                self.x = random.uniform(-200, -40)
                self.y = random.uniform(-60, self.screen_h + 60)

    def update(self):
        self.x += self.vx
        self.y += self.vy
        margin = 220
        if self.y < -margin or self.x > self.screen_w + margin:
            self.reset_pos(initial=False)

    def _rot(self, pts):
        c = math.cos(self.angle)
        s = math.sin(self.angle)
        cx, cy = self.x, self.y
        return [(cx + px * c - py * s, cy + px * s + py * c) for px, py in pts]

    def draw(self, surface):
        m = self.size + 28
        if self.x < -m or self.y < -m or self.x > self.screen_w + m or self.y > self.screen_h + m:
            return

        col = self.color
        lw = self.line_w
        half = self.size / 2
        ix, iy = int(self.x), int(self.y)

        if self.type == "filled_square":
            pts = self._rot([(-half, -half), (half, -half), (half, half), (-half, half)])
            pygame.draw.polygon(surface, col, pts)

        elif self.type == "filled_square_small":
            s = half * 0.62
            pts = self._rot([(-s, -s), (s, -s), (s, s), (-s, s)])
            pygame.draw.polygon(surface, col, pts)

        elif self.type == "ring":
            pygame.draw.circle(surface, col, (ix, iy), max(5, int(half * 0.72)), lw)

        elif self.type == "single_dot":
            pygame.draw.circle(surface, col, (ix, iy), max(1, int(half * 0.18)))

        elif self.type == "bar_stack":
            for i in (-1, 0, 1):
                bar = self._rot([
                    (-half * 0.60, i * 8 - 2),
                    ( half * 0.60, i * 8 - 2),
                    ( half * 0.60, i * 8 + 2),
                    (-half * 0.60, i * 8 + 2),
                ])
                pygame.draw.polygon(surface, col, bar)

        elif self.type == "dot_grid":
            spacing = max(10, int(self.size * 0.16))
            r = max(1, int(self.size * 0.035))
            cols = 5
            rows = 7
            x0 = -spacing * (cols - 1) / 2
            y0 = -spacing * (rows - 1) / 2
            for gy in range(rows):
                for gx in range(cols):
                    # 端を少し欠けさせて、FUIのパネルっぽい集合にする
                    if (gx, gy) in [(0, 0), (4, 6), (0, 6)] and self.depth < 0.65:
                        continue
                    p = self._rot([(x0 + gx * spacing, y0 + gy * spacing)])[0]
                    pygame.draw.circle(surface, col, (int(p[0]), int(p[1])), r)


class FineMusicChannel:
    """pygame.mixer.music 互換の再生ラッパー（高分解能音量版）。

    mixer.music の音量は SDL 内部で 0〜128 の整数に切り捨てられるため、
    「全体音量(最大0.25)×曲音量」のような小さなゲインは数段階しか表現できず、
    小音量域で急に調整が効かなくなる／無音に落ちる問題があった。
    ⚠️ Sound音量×Channel音量の二段掛けも SDL 内部で
    (chunk*channel)/128 と整数1個に畳み込まれるため解決にならない（実測済み）。
    そこで細かい側は「パンニング(Mix_SetPanning=Channel.set_volume(l,r))」を使う。
    パンは音量整数とは別レイヤーでサンプル値自体を 0〜255 段階で減衰させるため潰れず、
    Sound音量(0〜128) × パン(0〜255) ＝ 実質約32640段階の分解能になる。
    """

    def __init__(self, channel_id=0):
        self._channel = pygame.mixer.Channel(channel_id)
        self._sound = None        # 現在ロード中の曲（全体をデコード済み）
        self._play_obj = None     # 実際に再生中のSound（シーク時は途中からのスライス）
        self._raw = None          # シーク用の生データキャッシュ
        self._gain = 1.0
        self._paused = False
        self._play_start = None   # time.monotonic 基準の再生開始時刻
        self._pause_started = None
        self._paused_total = 0.0

    # --- mixer.music 互換API ---
    def set_endevent(self, event_type=None):
        if event_type is None:
            self._channel.set_endevent()
        else:
            self._channel.set_endevent(event_type)

    def load_from_sound(self, sound):
        # デコード済みSoundを差し替える（music.load と同様、現在の再生は止まる）
        self.stop()
        self._sound = sound
        self._play_obj = None
        self._raw = None

    def unload(self):
        self.stop()
        self._sound = None
        self._play_obj = None
        self._raw = None

    def play(self, start=0):
        if self._sound is None:
            return
        snd = self._sound
        if start and start > 0:
            snd = self._slice_from(start)
            if snd is None:
                snd = self._sound
        self._play_obj = snd
        self._apply_stage_volume()
        self._channel.play(snd)
        # パンニング（チャンネルエフェクト）は停止時に解除されることがあるため再生後にも適用する
        self._apply_stage_volume()
        self._play_start = time.monotonic()
        self._paused_total = 0.0
        self._pause_started = None
        self._paused = False

    def _slice_from(self, start_sec):
        # 生データを秒位置でスライスして途中再生用のSoundを作る
        init = pygame.mixer.get_init()
        if not init:
            return None
        freq, size, channels = init
        try:
            if self._raw is None:
                self._raw = self._sound.get_raw()
            frame_bytes = (abs(size) // 8) * channels
            # 末尾ギリギリ指定でも終了イベントが確実に飛ぶよう、最低0.2秒は残す
            min_tail = int(0.2 * freq) * frame_bytes
            offset = int(start_sec * freq) * frame_bytes
            offset = max(0, min(offset, len(self._raw) - min_tail))
            offset -= offset % frame_bytes
            if offset <= 0:
                return self._sound
            return pygame.mixer.Sound(buffer=self._raw[offset:])
        except Exception as e:
            print(f"Seek slice error: {e}")
            return None

    def stop(self):
        self._channel.stop()
        self._paused = False
        self._play_start = None
        self._pause_started = None

    def pause(self):
        if not self._paused:
            self._channel.pause()
            self._paused = True
            self._pause_started = time.monotonic()

    def unpause(self):
        if self._paused:
            self._channel.unpause()
            self._paused = False
            if self._pause_started is not None:
                self._paused_total += time.monotonic() - self._pause_started
                self._pause_started = None

    def fadeout(self, ms):
        self._channel.fadeout(ms)

    def get_busy(self):
        # music.get_busy と同じく「一時停止中はFalse」
        return bool(self._channel.get_busy()) and not self._paused

    def get_pos(self):
        # music.get_pos と同じく「再生開始からのms（開始オフセットは含まない）」。停止中は-1
        if self._play_start is None or not self._channel.get_busy():
            return -1
        now = self._pause_started if self._pause_started is not None else time.monotonic()
        elapsed = now - self._play_start - self._paused_total
        return int(max(0.0, elapsed) * 1000)

    def set_volume(self, gain):
        self._gain = max(0.0, min(float(gain), 1.0))
        self._apply_stage_volume()

    def _apply_stage_volume(self):
        # 目標ゲインを (chunk/128)*(pan/255) に分解する。
        # chunk は最小（=panが最大）になるよう選ぶと相対誤差が最小＆サンプル精度も最良。
        target = self._gain * 128.0 * 255.0
        if target <= 0.0:
            chunk_steps, pan_steps = 0, 0
        else:
            chunk_steps = min(128, max(1, int(math.ceil(target / 255.0 - 1e-9))))
            pan_steps = min(255, max(1, int(round(target / chunk_steps))))
        # pygame内部の (Uint8)(v*255)/(int)(v*128) の切り捨てで1段ずれないよう +0.5 を足して渡す
        chunk_vol = min(1.0, (chunk_steps + 0.5) / 128.0)
        pan_vol = min(1.0, (pan_steps + 0.5) / 255.0)
        if chunk_steps <= 0:
            chunk_vol = 0.0
        if pan_steps <= 0:
            pan_vol = 0.0
        if self._play_obj is not None:
            self._play_obj.set_volume(chunk_vol)
        if self._sound is not None and self._sound is not self._play_obj:
            self._sound.set_volume(chunk_vol)
        try:
            # 2引数版=Mix_SetPanning（サンプル値を0〜255で減衰。音量整数に畳み込まれない）
            self._channel.set_volume(pan_vol, pan_vol)
        except Exception:
            # パンニング不可の環境（モノラル出力等）は従来の128段階にフォールバック
            self._channel.set_volume(min(1.0, self._gain / max(chunk_vol, 1e-9)))


class SketchMusicPlayer:
    def __init__(self):
        # Windowsのタスクバーで独自アイコン/グループとして扱わせる（exeアイコンの反映を確実に）
        if sys.platform == "win32":
            try:
                ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(APP_NAME)
            except Exception:
                pass

        # DPI awareness は必ずウィンドウ生成前に確定させる（黒帯の根本対策）
        setup_windows_dpi()

        pygame.init()
        # 実行中のウィンドウ/タスクバーアイコン（set_mode より前に設定するのが推奨）
        try:
            icon_surf = pygame.image.load(resource_path(os.path.join("assets", "ui", "ThunDuckyAppIcon.png")))
            pygame.display.set_icon(icon_surf)
        except Exception as e:
            print(f"App icon load error: {e}")

        # タイトルバー（上部のバー）を消す → ボーダーレスウィンドウ
        self.screen = pygame.display.set_mode(SCREEN_SIZE, pygame.DOUBLEBUF | pygame.NOFRAME)
        pygame.display.set_caption(APP_NAME)
        self.clock = pygame.time.Clock()
        self.running = True

        # --- ボーダーレス時のウィンドウ移動用（Windows） ---
        self.is_windows = sys.platform == "win32"
        self.hwnd = None
        if self.is_windows:
            try:
                self.hwnd = pygame.display.get_wm_info()["window"]
            except Exception:
                self.hwnd = None
        self.window_dragging = False
        self.win_drag_cursor_start = (0, 0)
        self.win_drag_win_start = (0, 0)
        # OS操作（Win+↑の最大化・スナップ等）でウィンドウが600x600以外にされると、
        # SDLの描画領域(600x600)の外に過去フレームの残骸や黒領域が表示されて崩壊する。
        # → 最大化/リサイズをスタイルから禁止＋定期監視でサイズを強制復元する
        self._next_window_repair = 0.0
        if self.hwnd:
            self._lock_window_style()

        if not os.path.exists(TEMP_DIR): os.makedirs(TEMP_DIR)
        if not os.path.exists(THUMB_DATA_DIR): os.makedirs(THUMB_DATA_DIR)

        self.font_time = self.load_custom_font(resource_path(FONT_FILE_UI), 72, is_ui=True)
        self.font_date = self.load_custom_font(resource_path(FONT_FILE_UI), 22, is_ui=True)
        self.font_ui   = self.load_custom_font(resource_path(FONT_FILE_UI), 22, is_ui=True)
        self.font_small = self.load_custom_font(resource_path(FONT_FILE_UI), 16, is_ui=True)
        self.font_title = self.load_custom_font(resource_path(FONT_FILE_TITLE), 24, is_ui=False)
        self.font_vtitle = self.load_custom_font(resource_path(FONT_FILE_TITLE), 22, is_ui=False)

        # --- UI画像（128x128 → 表示サイズへ縮小） ---
        self.icon_loop_on  = self.load_ui_image(os.path.join("assets", "ui", "RoopUI_On.png"), 40)
        self.icon_loop_off = self.load_ui_image(os.path.join("assets", "ui", "RoopUI_Off.png"), 40)
        self.icon_trash    = self.load_ui_image(os.path.join("assets", "ui", "DustBox.png"), 40)
        self.icon_folder   = self.load_ui_image(os.path.join("assets", "ui", "FolderUI.png"), 40)
        # サムネイルが読み込めない曲のフォールバック画像（旧：透明）
        self.no_image_art  = self.load_ui_image(os.path.join("assets", "ui", "NoImage.png"), ART_SIZE)

        self.playlist = []
        self.original_playlist = []
        self.current_index = 0
        self.is_playing = False
        self.is_paused = False
        self.volume = 0.5
        self.loop_one = False

        self.art_cache = {}
        self.small_art_cache = {}
        self.duration_cache = {}
        # ジャケットの非同期デコード用（重い展開はワーカースレッド、サーフェス化のみメイン）
        self.art_pending = set()
        self.art_raw = {}
        self.art_lock = threading.Lock()
        self.art_generation = 0
        self._art_placeholder = None
        self.thumb_map = {}
        self.load_thumb_map()
        self.track_volume_map = {}
        self.load_track_volume_map()

        # --- ビジュアライザー用スペクトルデータ ---
        self.spectrum_cache = {}             # path -> (np.ndarray[frames, VIS_NUM_BARS], fps)
        self.spectrum_pending = set()        # 解析中のpath
        self.spectrum_lock = threading.Lock()
        self.vis_levels = np.zeros(VIS_NUM_BARS, dtype=float)  # 表示用に平滑化したバー高さ

        self.anim_timer = 0.0
        self.anim_duration = ANIM_DURATION
        self.visual_offset = 0.0
        self.move_direction = 0
        self.is_animating = False
        self.title_scroll_y = 0.0
        self.title_scroll_x = 0.0
        self.cur_title = "NO MUSIC"
        # スライドアニメは開始オフセット→目標オフセットを補間する
        self.anim_start_offset = 0.0
        self.anim_target_offset = 0.0
        self.play_after_animation = False

        # --- スワイプ操作の状態（縦） ---
        self.swiping = False
        self.swipe_start_pos = (0, 0)
        self.swipe_moved = False
        self.resume_after_scroll = False

        self.seeking = False
        self.seek_drag_ratio = 0.0
        self.last_seek_pos = 0
        self.track_volume_dragging = False

        self.mode = "PLAYER"
        self.crop_image_raw = None
        self.crop_scale = 1.0
        self.crop_offset = [0, 0]
        self.crop_dragging = False
        self.crop_drag_start = (0, 0)

        self.last_action_time = 0.0
        self.audio_lock = threading.Lock()
        self.audio_request_id = 0

        self.press_start_time = None
        self.next_scroll_time = 0.0
        self.audio_load_deadline = 0.0
        self.pending_audio_load = False

        self.trash_button_rect = pygame.Rect(0, 0, 0, 0)
        self.close_button_rect = pygame.Rect(0, 0, 0, 0)
        self.loop_button_rect = pygame.Rect(0, 0, 0, 0)
        self.vol_bar_rect = pygame.Rect(0, 0, 0, 0)
        self.next_box_rect = pygame.Rect(0, 0, 0, 0)
        self.prev_box_rect = pygame.Rect(0, 0, 0, 0)
        self.folder_button_rect = pygame.Rect(0, 0, 0, 0)
        self.play_button_rect = pygame.Rect(0, 0, 0, 0)
        self.seek_bar_rect = pygame.Rect(0, 0, 0, 0)
        self.vol_button_rect = pygame.Rect(0, 0, 0, 0)
        self.track_vol_bar_rect = pygame.Rect(0, 0, 0, 0)

        # 幾何学模様は左ダーク領域内だけで動かす
        self.shapes = [GeometricShape(LEFT_W, SCREEN_SIZE[1]) for _ in range(24)]
        self.bg_surface = pygame.Surface(SCREEN_SIZE, pygame.SRCALPHA)

        self.root = Tk()
        self.root.withdraw()

        pygame.mixer.init(frequency=44100)
        pygame.mixer.set_reserved(1)  # 音楽再生専用チャンネル（0番）を確保
        self.MUSIC_END = pygame.USEREVENT + 1
        self.music = FineMusicChannel(0)
        self.music.set_endevent(self.MUSIC_END)

        self.load_state()

    # --- ボーダーレスウィンドウの移動（Windows用） ---
    def _get_cursor_screen_pos(self):
        pt = ctypes.wintypes.POINT()
        ctypes.windll.user32.GetCursorPos(ctypes.byref(pt))
        return pt.x, pt.y

    def _get_window_pos(self):
        rect = ctypes.wintypes.RECT()
        ctypes.windll.user32.GetWindowRect(self.hwnd, ctypes.byref(rect))
        return rect.left, rect.top

    def _move_window(self, x, y):
        SWP_NOSIZE = 0x0001
        SWP_NOZORDER = 0x0004
        ctypes.windll.user32.SetWindowPos(
            self.hwnd, 0, int(x), int(y), 0, 0, SWP_NOSIZE | SWP_NOZORDER)

    def _lock_window_style(self):
        # 最大化ボタン相当（Win+↑）とリサイズ枠をウィンドウスタイルから除去。
        # ボーダーレスでもSDLウィンドウはOSの最大化/スナップ操作を受け付けてしまうため。
        # SetWindowLongW だけではキャッシュされた枠情報が残るので SWP_FRAMECHANGED で確定させる。
        GWL_STYLE = -16
        WS_MAXIMIZEBOX = 0x00010000
        WS_THICKFRAME = 0x00040000
        try:
            user32 = ctypes.windll.user32
            style = user32.GetWindowLongW(self.hwnd, GWL_STYLE)
            new_style = style & ~(WS_MAXIMIZEBOX | WS_THICKFRAME)
            if new_style == style:
                return
            user32.SetWindowLongW(self.hwnd, GWL_STYLE, new_style)
            SWP_NOMOVE = 0x0002
            SWP_NOSIZE = 0x0001
            SWP_NOZORDER = 0x0004
            SWP_FRAMECHANGED = 0x0020
            user32.SetWindowPos(self.hwnd, 0, 0, 0, 0, 0,
                                SWP_NOMOVE | SWP_NOSIZE | SWP_NOZORDER | SWP_FRAMECHANGED)
        except Exception:
            pass

    def _win_rects(self):
        """(クライアント領域, 外形) を物理ピクセルで返す。取得失敗時は None。"""
        try:
            user32 = ctypes.windll.user32
            cr = ctypes.wintypes.RECT()
            wr = ctypes.wintypes.RECT()
            user32.GetClientRect(self.hwnd, ctypes.byref(cr))
            user32.GetWindowRect(self.hwnd, ctypes.byref(wr))
            return ((cr.right - cr.left, cr.bottom - cr.top),
                    (wr.right - wr.left, wr.bottom - wr.top))
        except Exception:
            return None

    def _enforce_window_size(self):
        """OS操作/DPI変更でウィンドウが 600x600 から外れたら強制復元する。

        黒帯の直接原因は「OSウィンドウ > SDLの描画Surface」のズレ。
        ウィンドウを戻すだけでなく、SDL側のサイズと Surface のサイズも必ず突き合わせる。
        """
        if not (self.is_windows and self.hwnd):
            return
        # 修復が空振りし続けた場合に set_mode / ログ書き込みを連打しないためのスロットル
        now = time.time()
        if now < self._next_window_repair:
            return
        try:
            user32 = ctypes.windll.user32

            # 1) 最大化されていたら戻す
            if user32.IsZoomed(self.hwnd):
                user32.ShowWindow(self.hwnd, 9)  # SW_RESTORE
                log_window_event("maximized -> restored")

            # 2) OSウィンドウのサイズを物理ピクセルで検証（DPI aware 前提）
            rects = self._win_rects()
            if rects is not None:
                client, outer = rects
                # NOFRAMEウィンドウは外形=クライアント領域なのでどちらも600x600のはず
                if client != SCREEN_SIZE or outer != SCREEN_SIZE:
                    SWP_NOMOVE = 0x0002
                    SWP_NOZORDER = 0x0004
                    SWP_FRAMECHANGED = 0x0020
                    user32.SetWindowPos(self.hwnd, 0, 0, 0,
                                        SCREEN_SIZE[0], SCREEN_SIZE[1],
                                        SWP_NOMOVE | SWP_NOZORDER | SWP_FRAMECHANGED)
                    log_window_event(
                        f"window resized by OS: client={client} outer={outer} "
                        f"dpi={self._window_dpi()} -> forced {SCREEN_SIZE}")
                    self._lock_window_style()
                    self._next_window_repair = now + 0.5

            # 3) SDL側のズレを修復（ここが黒帯の実体）
            #    ウィンドウを戻してもSDLの内部サイズ/Surfaceが古いままだと黒が残る
            win_size = pygame.display.get_window_size()
            surf = pygame.display.get_surface()
            surf_size = surf.get_size() if surf is not None else (0, 0)
            if win_size != SCREEN_SIZE or surf_size != SCREEN_SIZE:
                log_window_event(
                    f"SDL desync: window={win_size} surface={surf_size} -> set_mode")
                self.screen = pygame.display.set_mode(
                    SCREEN_SIZE, pygame.DOUBLEBUF | pygame.NOFRAME)
                try:
                    self.hwnd = pygame.display.get_wm_info()["window"]
                except Exception:
                    pass
                self._lock_window_style()
                self._next_window_repair = now + 0.5
        except Exception as e:
            log_window_event(f"enforce error: {e!r}")
            self._next_window_repair = now + 1.0

    def _window_dpi(self):
        try:
            return ctypes.windll.user32.GetDpiForWindow(self.hwnd)
        except Exception:
            return -1

    def begin_window_drag(self):
        if not (self.is_windows and self.hwnd):
            return
        try:
            self.window_dragging = True
            self.win_drag_cursor_start = self._get_cursor_screen_pos()
            self.win_drag_win_start = self._get_window_pos()
        except Exception:
            self.window_dragging = False

    def update_window_drag(self):
        if not self.window_dragging:
            return
        try:
            cx, cy = self._get_cursor_screen_pos()
            dx = cx - self.win_drag_cursor_start[0]
            dy = cy - self.win_drag_cursor_start[1]
            self._move_window(self.win_drag_win_start[0] + dx,
                              self.win_drag_win_start[1] + dy)
        except Exception:
            pass

    def set_volume_safe(self, vol):
        # 0.0〜1.0 にクランプするだけ。デッドゾーンは設けず端まで滑らかに下げる
        self.volume = self.normalize_master_volume(vol)
        self.apply_effective_volume()

    def set_master_volume_value(self, value):
        self.volume = self.master_volume_to_value(value) / VOLUME_MAX_PERCENT
        self.apply_effective_volume()

    def clamp_track_percent(self, percent):
        # 曲ごと音量を TRACK_VOLUME_STEP 刻み・範囲内に丸める。
        # 整数値は int のまま保存して track_volume_map.json の旧形式と揃える
        try:
            p = float(percent)
        except (TypeError, ValueError):
            p = VOLUME_MAX_PERCENT
        p = round(round(p / TRACK_VOLUME_STEP) * TRACK_VOLUME_STEP, 1)
        p = max(VOLUME_MIN_PERCENT, min(p, VOLUME_MAX_PERCENT))
        return int(p) if p == int(p) else p

    def volume_to_percent(self, value):
        # 保存データ読み込み用。旧形式（0〜1の割合float）だけ%へ換算する
        try:
            raw = float(value)
        except (TypeError, ValueError):
            raw = VOLUME_MAX_PERCENT
        if 0.0 < raw < 1.0:
            raw *= 100.0
        return self.clamp_track_percent(raw)

    def master_volume_to_value(self, value):
        try:
            raw = float(value)
        except (TypeError, ValueError):
            raw = MASTER_VOLUME_MAX
        raw = max(MASTER_VOLUME_MIN, min(raw, MASTER_VOLUME_MAX))
        steps = round((raw - MASTER_VOLUME_MIN) / MASTER_VOLUME_DRAG_STEP)
        return round(MASTER_VOLUME_MIN + steps * MASTER_VOLUME_DRAG_STEP, 2)

    def normalize_master_volume(self, value):
        return self.master_volume_to_value(value) / VOLUME_MAX_PERCENT

    def get_master_volume_value(self):
        return self.master_volume_to_value(self.volume * VOLUME_MAX_PERCENT)

    # --- スライダー位置⇔値の変換（下側=小音量域ほど細かく動かせるカーブ） ---
    def slider_ratio_to_value(self, ratio, vmin, vmax):
        # ratio: 0=下端, 1=上端
        r = max(0.0, min(float(ratio), 1.0))
        return vmin + (vmax - vmin) * (r ** VOLUME_SLIDER_CURVE)

    def value_to_slider_ratio(self, value, vmin, vmax):
        if vmax <= vmin:
            return 0.0
        t = max(0.0, min((float(value) - vmin) / (vmax - vmin), 1.0))
        return t ** (1.0 / VOLUME_SLIDER_CURVE)

    def master_volume_value_from_y(self, y):
        track_h = MASTER_VOL_BOTTOM - MASTER_VOL_TOP
        if track_h <= 0:
            return MASTER_VOLUME_MAX
        ratio = 1.0 - max(0.0, min((y - MASTER_VOL_TOP) / track_h, 1.0))
        value = self.slider_ratio_to_value(ratio, MASTER_VOLUME_MIN, MASTER_VOLUME_MAX)
        return self.master_volume_to_value(value)

    def volume_percent_from_y(self, y, top, bottom):
        track_h = bottom - top
        if track_h <= 0:
            return VOLUME_MAX_PERCENT
        ratio = 1.0 - max(0.0, min((y - top) / track_h, 1.0))
        percent = self.slider_ratio_to_value(ratio, VOLUME_MIN_PERCENT, VOLUME_MAX_PERCENT)
        return self.clamp_track_percent(percent)

    def get_track_volume_percent(self, index=None):
        if not self.playlist:
            return VOLUME_MAX_PERCENT
        if index is None:
            index = self.current_index
        path = self.playlist[index % len(self.playlist)]
        return self.clamp_track_percent(self.track_volume_map.get(path, VOLUME_MAX_PERCENT))

    def get_track_volume(self, index=None):
        if not self.playlist:
            return 1.0
        return self.get_track_volume_percent(index) / VOLUME_MAX_PERCENT

    def get_visualizer_volume_scale(self):
        # アプリ内の最大音量（VOL 25・曲別100）をビジュアライザーの最大サイズとする。
        master_range = MASTER_VOLUME_MAX - MASTER_VOLUME_MIN
        if master_range <= 0:
            master_ratio = 0.0
        else:
            master_ratio = ((self.get_master_volume_value() - MASTER_VOLUME_MIN)
                            / master_range)
        scale = master_ratio * self.get_track_volume()
        return max(0.0, min(scale, 1.0))

    def set_current_track_volume(self, vol):
        if not self.playlist:
            return
        path = self.playlist[self.current_index % len(self.playlist)]
        self.track_volume_map[path] = self.clamp_track_percent(vol)
        self.apply_effective_volume()

    def set_current_track_volume_from_y(self, y):
        self.set_current_track_volume(self.volume_percent_from_y(y, TRACK_VOL_TOP, TRACK_VOL_BOTTOM))

    def set_master_volume_from_y(self, y):
        self.set_master_volume_value(self.master_volume_value_from_y(y))

    def apply_effective_volume(self):
        track_volume = self.get_track_volume() if self.playlist else 1.0
        self.music.set_volume(max(0.0, min(self.volume * track_volume, 1.0)))

    def stop_audio_playback(self, unload=False, cancel_pending=True):
        if cancel_pending:
            self.pending_audio_load = False
        with self.audio_lock:
            self.audio_request_id += 1
            self.music.set_endevent()
            self.music.stop()
            if unload:
                try:
                    self.music.unload()
                except:
                    pass
        self.is_playing = False
        self.is_paused = False

    def can_perform_action(self):
        now = time.time()
        if now - self.last_action_time > ACTION_COOLDOWN:
            self.last_action_time = now
            return True
        return False

    def load_thumb_map(self):
        if os.path.exists(THUMB_MAP_FILE):
            try:
                with open(THUMB_MAP_FILE, 'r', encoding='utf-8') as f:
                    self.thumb_map = json.load(f)
            except:
                self.thumb_map = {}

    def save_thumb_map(self):
        try:
            with open(THUMB_MAP_FILE, 'w', encoding='utf-8') as f:
                json.dump(self.thumb_map, f, ensure_ascii=False, indent=2)
        except: pass

    def load_track_volume_map(self):
        if os.path.exists(TRACK_VOLUME_MAP_FILE):
            try:
                with open(TRACK_VOLUME_MAP_FILE, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                self.track_volume_map = {
                    path: self.volume_to_percent(vol)
                    for path, vol in data.items()
                }
            except:
                self.track_volume_map = {}

    def save_track_volume_map(self):
        try:
            with open(TRACK_VOLUME_MAP_FILE, 'w', encoding='utf-8') as f:
                json.dump(self.track_volume_map, f, ensure_ascii=False, indent=2)
        except:
            pass

    def load_ui_image(self, relative_path, size):
        # UIフォルダのPNGを読み込み、指定サイズの正方形に縮小（失敗時はNone）
        try:
            img = pygame.image.load(resource_path(relative_path)).convert_alpha()
            return pygame.transform.smoothscale(img, (size, size))
        except Exception as e:
            print(f"UI image load error ({relative_path}): {e}")
            return None

    def load_custom_font(self, filename, size, is_ui=True):
        try:
            return pygame.font.Font(filename, size)
        except:
            if not is_ui:
                try: return pygame.font.SysFont("Meiryo UI", size, bold=True)
                except: return pygame.font.SysFont(None, size)
            return pygame.font.SysFont(None, size)

    def load_state(self):
        if os.path.exists(STATE_FILE):
            try:
                with open(STATE_FILE, 'r', encoding='utf-8') as f:
                    data = json.load(f)
                    last_folder = data.get("folder", "")
                    last_index = data.get("index", 0)
                    self.volume = data.get("volume", 0.5)
                    self.loop_one = data.get("loop_one", False)
                    self.set_volume_safe(self.volume)

                    if last_folder and os.path.exists(last_folder):
                        self.load_folder_path(last_folder)
                        if self.playlist:
                            self.current_index = last_index % len(self.playlist)
                            self.load_song_data_only(self.current_index)
                            self.apply_effective_volume()
            except Exception as e:
                print(f"Load state error: {e}")

    def save_state(self):
        current_file = self.playlist[self.current_index] if self.playlist else ""
        save_idx = 0
        if current_file and current_file in self.original_playlist:
            save_idx = self.original_playlist.index(current_file)

        data = {
            "folder": os.path.dirname(self.original_playlist[0]) if self.original_playlist else "",
            "index": save_idx,
            "volume": self.get_master_volume_value(),
            "loop_one": self.loop_one
        }
        try:
            with open(STATE_FILE, 'w', encoding='utf-8') as f:
                json.dump(data, f)
        except: pass

    def cleanup_temp(self):
        try:
            if os.path.exists(TEMP_DIR):
                shutil.rmtree(TEMP_DIR)
        except: pass

    def create_gradient_frame(self, colors, size):
        # 8色グラデーション：四隅＋上下左右の中点（計8色）を 3x3 グリッドに配置し、
        # 中央セルは8色の平均色にして全体をなめらかに補間する。
        # colors の並び順 = [左上, 上中, 右上, 右中, 右下, 下中, 左下, 左中]
        if len(colors) < 8:
            # 後方互換（旧4色キャッシュなど）：足りない分は先頭色で埋める
            colors = list(colors) + [colors[0]] * (8 - len(colors))
        tl, tm, tr, rm, br, bm, bl, lm = colors[:8]
        center = tuple(int(sum(ch) / 8) for ch in zip(tl, tm, tr, rm, br, bm, bl, lm))

        base = pygame.Surface((3, 3))
        base.set_at((0, 0), tl); base.set_at((1, 0), tm); base.set_at((2, 0), tr)
        base.set_at((0, 1), lm); base.set_at((1, 1), center); base.set_at((2, 1), rm)
        base.set_at((0, 2), bl); base.set_at((1, 2), bm); base.set_at((2, 2), br)
        return pygame.transform.smoothscale(base, (size, size))

    @staticmethod
    def extract_dominant_color(image):
        """ジャケット全体で最も多く使われている代表色を返す。"""
        try:
            sample = image.convert("RGBA")
            sample.thumbnail((64, 64), Image.LANCZOS)
            opaque_pixels = [
                (r, g, b) for r, g, b, a in sample.getdata()
                if a >= 64
            ]
            if not opaque_pixels:
                return MAIN_COLOR

            # 近い色をまとめてから、使用ピクセル数が最大の色を選ぶ。
            strip = Image.new("RGB", (len(opaque_pixels), 1))
            strip.putdata(opaque_pixels)
            quantized = strip.quantize(colors=12, method=Image.Quantize.MEDIANCUT)
            palette = quantized.getpalette()
            ranked = []
            for count, palette_index in quantized.getcolors() or []:
                offset = palette_index * 3
                color = tuple(palette[offset:offset + 3])
                luma = 0.2126 * color[0] + 0.7152 * color[1] + 0.0722 * color[2]
                ranked.append((count, color, luma))
            if not ranked:
                return MAIN_COLOR

            # 真っ黒・真っ白に近い背景は、他に有効な色がある場合のみ候補から外す。
            visible = [entry for entry in ranked if 24.0 <= entry[2] <= 245.0]
            _, color, luma = max(visible or ranked, key=lambda entry: entry[0])

            # 暗いジャケットでもバーが背景へ埋もれないよう、色相を保って最低輝度を確保する。
            if luma < 64.0:
                blend = (64.0 - luma) / max(1.0, 255.0 - luma)
                color = tuple(int(round(c + (255 - c) * blend)) for c in color)
            return color
        except Exception:
            return MAIN_COLOR

    @staticmethod
    def balance_visualizer_spectrum(values):
        """低音だけが長くならないよう、周波数帯ごとの表示感度を揃える。"""
        out = np.log1p(np.maximum(values, 0.0)).astype(np.float32, copy=False)
        if out.size == 0:
            return out

        global_peak = float(np.percentile(out, 99.0))
        if global_peak <= 1e-9:
            return np.zeros_like(out, dtype=np.float32)

        # 各帯域の通常時ピークを基準にする。全体ピークの6%を下限にして、
        # ほぼ無音の高域ノイズだけが過剰に増幅されるのを防ぐ。
        band_peaks = np.percentile(out, 95.0, axis=0)
        band_peaks = np.maximum(band_peaks, global_peak * 0.06)
        band_balanced = out / band_peaks
        global_balanced = out / global_peak

        # 帯域別補正を主にしつつ、元の低音・高音の強弱も少し残す。
        out = band_balanced * 0.82 + global_balanced * 0.18
        out = np.clip(out, 0.0, 1.0)
        # 小さい値を少し持ち上げ、下側の高域もデザイン上見える長さにする。
        return np.power(out, 0.78).astype(np.float32, copy=False)

    def analyze_spectrum(self, file_path):
        # 曲全体を一度だけFFT解析し、時間×周波数バンドのバー高さ配列を作ってキャッシュする。
        # 解析はバックグラウンドスレッドで行い、毎フレームは結果の参照だけにする。
        if AudioFileClip is None:
            return
        with self.spectrum_lock:
            if file_path in self.spectrum_cache or file_path in self.spectrum_pending:
                return
            self.spectrum_pending.add(file_path)

        def _work():
            try:
                clip = AudioFileClip(file_path)
                arr = clip.to_soundarray(fps=VIS_SAMPLE_RATE)
                clip.close()
                mono = arr.mean(axis=1) if arr.ndim > 1 else arr

                sr = VIS_SAMPLE_RATE
                win = VIS_FFT_WIN
                hop = max(1, sr // VIS_ANALYSIS_FPS)
                n = len(mono)
                num_frames = max(1, (n - win) // hop + 1)

                # 対数周波数バンド（約50Hz〜sr/2）に rfft のビンを割り当てる
                freqs = np.fft.rfftfreq(win, 1.0 / sr)
                edges = np.logspace(np.log10(50.0), np.log10(sr / 2.0), VIS_NUM_BARS + 1)
                bin_idx = [np.where((freqs >= edges[b]) & (freqs < edges[b + 1]))[0]
                           for b in range(VIS_NUM_BARS)]
                window = np.hanning(win)

                out = np.zeros((num_frames, VIS_NUM_BARS), dtype=np.float32)
                for fi in range(num_frames):
                    start = fi * hop
                    seg = mono[start:start + win]
                    if len(seg) < win:
                        seg = np.pad(seg, (0, win - len(seg)))
                    spec = np.abs(np.fft.rfft(seg * window))
                    for b in range(VIS_NUM_BARS):
                        idx = bin_idx[b]
                        if len(idx):
                            out[fi, b] = spec[idx].mean()

                # 対数圧縮＋帯域別正規化。低音域だけが長くなる偏りを抑える。
                out = self.balance_visualizer_spectrum(out)

                with self.spectrum_lock:
                    self.spectrum_cache[file_path] = (out, VIS_ANALYSIS_FPS)
            except Exception as e:
                print(f"Spectrum analysis error: {e}")
            finally:
                with self.spectrum_lock:
                    self.spectrum_pending.discard(file_path)

        threading.Thread(target=_work, daemon=True).start()

    def draw_visualizer(self):
        # 中央（再生中）ジャケットの左右に、横長バーを縦に隙間なく積んだスペクトルを描く。
        rect = self.current_art_rect
        if rect.width <= 0 or not self.playlist:
            return

        path = self.playlist[self.current_index % len(self.playlist)]
        with self.spectrum_lock:
            entry = self.spectrum_cache.get(path)

        playing = self.is_playing and not self.is_paused and self.music.get_busy()
        target = np.zeros(VIS_NUM_BARS, dtype=float)
        if playing:
            if entry is not None:
                spec, afps = entry
                cur_ms = self.music.get_pos()
                t = (cur_ms / 1000.0 + self.last_seek_pos) if cur_ms != -1 else 0.0
                fi = int(t * afps)
                if 0 <= fi < len(spec):
                    target = spec[fi].astype(float)
            else:
                # 解析がまだなら依頼（次フレーム以降で反映）
                self.analyze_spectrum(path)

        # 全体VOLと曲別音量の両方に合わせて、バーの長さも比例させる。
        target *= self.get_visualizer_volume_scale()

        # 平滑化：伸びる時は速く、縮む時はゆっくり
        for b in range(VIS_NUM_BARS):
            coeff = VIS_ATTACK if target[b] > self.vis_levels[b] else VIS_DECAY
            self.vis_levels[b] += (target[b] - self.vis_levels[b]) * coeff

        # バーが全部ほぼゼロなら描画スキップ
        if float(self.vis_levels.max()) < 0.01:
            return

        # 9番目はジャケット全体から抽出した代表色。旧キャッシュはテーマ色へフォールバックする。
        _, colors = self.get_art_data(self.current_index)
        visualizer_color = colors[8] if len(colors) >= 9 else MAIN_COLOR

        left_x = rect.left - VIS_GAP_FROM_ART     # 左バーの右端（ここから左へ伸びる）
        right_x = rect.right + VIS_GAP_FROM_ART    # 右バーの左端（ここから右へ伸びる）
        top = rect.top
        for b in range(VIS_NUM_BARS):
            # 端数を丸めて隣のバーと隙間が出ないように上下を連結する
            y0 = int(round(top + b * rect.height / VIS_NUM_BARS))
            y1 = int(round(top + (b + 1) * rect.height / VIS_NUM_BARS))
            h = max(1, y1 - y0)
            length = int(self.vis_levels[b] * VIS_MAX_LEN)
            if length < 1:
                continue
            # 影（テーマに合わせて右下方向）
            pygame.draw.rect(self.screen, SHADOW_COLOR,
                             (left_x - length + SHADOW_OFFSET, y0 + SHADOW_OFFSET, length, h))
            pygame.draw.rect(self.screen, SHADOW_COLOR,
                             (right_x + SHADOW_OFFSET, y0 + SHADOW_OFFSET, length, h))
            # 本体（左へ伸びる／右へ伸びる）
            pygame.draw.rect(self.screen, visualizer_color, (left_x - length, y0, length, h))
            pygame.draw.rect(self.screen, visualizer_color, (right_x, y0, length, h))

    def draw_track_volume_control(self):
        if not self.playlist:
            self.track_vol_bar_rect = pygame.Rect(0, 0, 0, 0)
            return

        track_h = TRACK_VOL_BOTTOM - TRACK_VOL_TOP
        x = TRACK_VOL_X
        ratio = self.value_to_slider_ratio(
            self.get_track_volume_percent(), VOLUME_MIN_PERCENT, VOLUME_MAX_PERCENT)
        knob_y = int(TRACK_VOL_TOP + track_h * (1.0 - ratio))

        pygame.draw.line(
            self.screen, SHADOW_COLOR,
            (x + SHADOW_OFFSET, TRACK_VOL_TOP + SHADOW_OFFSET),
            (x + SHADOW_OFFSET, TRACK_VOL_BOTTOM + SHADOW_OFFSET),
            5
        )
        pygame.draw.line(self.screen, MAIN_COLOR, (x, TRACK_VOL_TOP), (x, TRACK_VOL_BOTTOM), 5)

        knob = pygame.Rect(x - 14, knob_y - 12, 28, 24)
        pygame.draw.rect(self.screen, SHADOW_COLOR, knob.move(SHADOW_OFFSET, SHADOW_OFFSET), border_radius=3)
        pygame.draw.rect(self.screen, MAIN_COLOR, knob, border_radius=3)
        for n in range(3):
            ly = knob.top + 7 + n * 5
            pygame.draw.line(self.screen, BG_COLOR, (knob.left + 6, ly), (knob.right - 6, ly), 2)

        self.track_vol_bar_rect = pygame.Rect(x - 20, TRACK_VOL_TOP - 16, 40, track_h + 32)

    def get_duration(self, file_path):
        if file_path in self.duration_cache:
            return self.duration_cache[file_path]

        duration = 0.0
        try:
            ext = os.path.splitext(file_path)[1].lower()
            if ext == ".mp4":
                cap = cv2.VideoCapture(file_path)
                if cap.isOpened():
                    fps = cap.get(cv2.CAP_PROP_FPS)
                    frame_count = cap.get(cv2.CAP_PROP_FRAME_COUNT)
                    if fps > 0: duration = frame_count / fps
                    cap.release()
            elif ext == ".flac":
                f = FLAC(file_path)
                if f and f.info: duration = f.info.length
            elif ext == ".wav":
                f = WAVE(file_path)
                if f and f.info: duration = f.info.length
            elif ext == ".ogg":
                f = OggVorbis(file_path)
                if f and f.info: duration = f.info.length
            elif ext in [".m4a", ".aac"]:
                f = MP4(file_path)
                if f and f.info: duration = f.info.length
            elif ext == ".wma":
                f = ASF(file_path)
                if f and f.info: duration = f.info.length
            else:
                f = mutagen.File(file_path)
                if f and f.info: duration = f.info.length

            if (ext == ".mp3") and (duration < 3.0) and AudioFileClip:
                try:
                    clip = AudioFileClip(file_path)
                    duration = clip.duration
                    clip.close()
                except: pass
        except: pass

        if duration <= 0: duration = 1.0
        self.duration_cache[file_path] = duration
        return duration

    def get_art_data(self, index):
        # キャッシュ済みならそれを返す。未デコードならバックグラウンドで読み込みを開始し、
        # 完了までプレースホルダを返す（メインスレッドでのデコードはスクロール中のカクつきの原因）
        if not self.playlist: return None, [MAIN_COLOR] * 8
        idx = index % len(self.playlist)
        file_path = self.playlist[idx]

        if file_path in self.art_cache:
            return self.art_cache[file_path]

        with self.art_lock:
            raw = self.art_raw.pop(file_path, None)
            if raw is None and file_path not in self.art_pending:
                self.art_pending.add(file_path)
                threading.Thread(target=self._decode_art_worker,
                                 args=(file_path, self.art_generation), daemon=True).start()

        if raw is not None:
            # デコード完了分をpygameサーフェスへ変換してキャッシュ（軽い処理のみメインスレッド）
            data, size, mode, colors = raw
            art_surface = None
            if data is not None:
                try:
                    art_surface = pygame.image.frombytes(data, size, mode).convert_alpha()
                except Exception:
                    art_surface = None
            if art_surface is None:
                art_surface = self._get_placeholder_art()
            self.art_cache[file_path] = (art_surface, colors)
            return self.art_cache[file_path]

        return self._get_placeholder_art(), [MAIN_COLOR] * 8

    def _get_placeholder_art(self):
        if self.no_image_art is not None:
            return self.no_image_art
        if self._art_placeholder is None:
            self._art_placeholder = pygame.Surface((ART_SIZE, ART_SIZE), pygame.SRCALPHA)
            self._art_placeholder.fill((0, 0, 0, 0))
        return self._art_placeholder

    def invalidate_art_caches(self, file_path=None):
        # サムネ差し替え・フォルダ変更・削除時に呼ぶ。実行中のデコード結果は世代番号で無効化
        with self.art_lock:
            self.art_generation += 1
            if file_path is None:
                self.art_raw = {}
            else:
                self.art_raw.pop(file_path, None)
        if file_path is None:
            self.art_cache = {}
            self.small_art_cache = {}
        else:
            self.art_cache.pop(file_path, None)
            for k in [k for k in self.small_art_cache if k[0] == file_path]:
                del self.small_art_cache[k]

    def _decode_art_worker(self, file_path, generation):
        # PIL/mutagen/cv2 のみ使用（pygame呼び出し禁止＝スレッド安全のため）。
        # 結果は (bytes, size, mode, colors) で渡し、サーフェス化はメインスレッドが行う
        data = size = mode = None
        colors = [MAIN_COLOR] * 9
        img = None

        if file_path in self.thumb_map:
            custom_thumb_path = self.thumb_map[file_path]
            if os.path.exists(custom_thumb_path):
                try:
                    img = Image.open(custom_thumb_path)
                except: pass

        if img is None:
            try:
                ext = os.path.splitext(file_path)[1].lower()
                if ext == ".mp3":
                    audio = ID3(file_path)
                    for tag in audio.values():
                        if isinstance(tag, APIC):
                            img = Image.open(io.BytesIO(tag.data))
                            break
                elif ext == ".flac":
                    audio = FLAC(file_path)
                    if audio.pictures:
                        for p in audio.pictures:
                            if p.type == 3:
                                img = Image.open(io.BytesIO(p.data))
                                break
                        if img is None and len(audio.pictures) > 0:
                            img = Image.open(io.BytesIO(audio.pictures[0].data))
                elif ext == ".m4a":
                    audio = MP4(file_path)
                    if 'covr' in audio:
                        covers = audio['covr']
                        if covers:
                            img = Image.open(io.BytesIO(covers[0]))
                elif ext == ".mp4":
                    cap = cv2.VideoCapture(file_path)
                    if cap.isOpened():
                        total_frames = int(cap.get(cv2.CAP_PROP_FRAME_COUNT))
                        fps = cap.get(cv2.CAP_PROP_FPS)
                        target_frame = int(fps) if total_frames > fps else 0
                        cap.set(cv2.CAP_PROP_POS_FRAMES, target_frame)
                        ret, frame = cap.read()
                        if ret:
                            frame = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
                            img = Image.fromarray(frame)
                        cap.release()
            except: pass

        if img:
            try:
                target_size = ART_SIZE
                img_w, img_h = img.size
                aspect = img_w / img_h

                if aspect > 1:
                    new_h = target_size
                    new_w = int(new_h * aspect)
                else:
                    new_w = target_size
                    new_h = int(new_w / aspect)

                img = img.resize((new_w, new_h), Image.LANCZOS)

                left = (new_w - target_size) / 2
                top = (new_h - target_size) / 2
                right = (new_w + target_size) / 2
                bottom = (new_h + target_size) / 2
                img = img.crop((left, top, right, bottom))

                w, h = img.size
                cx, cy = w // 2, h // 2
                # [左上, 上中, 右上, 右中, 右下, 下中, 左下, 左中] の順で8点サンプリング
                sample_points = [
                    (0, 0), (cx, 0), (w - 1, 0), (w - 1, cy),
                    (w - 1, h - 1), (cx, h - 1), (0, h - 1), (0, cy),
                ]
                extracted_colors = []
                for pt in sample_points:
                    box = (max(0, pt[0] - 10), max(0, pt[1] - 10), min(w, pt[0] + 10), min(h, pt[1] + 10))
                    region = img.crop(box)
                    stat = ImageStat.Stat(region)
                    c = tuple(map(int, stat.mean[:3]))
                    extracted_colors.append(c)
                colors = extracted_colors + [self.extract_dominant_color(img)]

                if img.mode not in ("RGB", "RGBA"):
                    img = img.convert("RGBA")
                data, size, mode = img.tobytes(), img.size, img.mode
            except:
                data = None

        with self.art_lock:
            # サムネ差し替え等で世代が進んでいたら古い結果は捨てる
            if generation == self.art_generation:
                self.art_raw[file_path] = (data, size, mode, colors)
            self.art_pending.discard(file_path)

    def get_small_art(self, index, size):
        # 候補枠用の小さいジャケット（サイズ別にキャッシュ）
        if not self.playlist:
            return None
        idx = index % len(self.playlist)
        file_path = self.playlist[idx]
        key = (file_path, size)
        if key in self.small_art_cache:
            return self.small_art_cache[key]
        surf, _ = self.get_art_data(idx)
        small = pygame.transform.smoothscale(surf, (size, size))
        if file_path in self.art_cache:
            # 本デコード完了分のみキャッシュ（プレースホルダを永続化しない）
            self.small_art_cache[key] = small
        return small

    def load_folder_path(self, folder_path):
        extensions = ('.mp3', '.mp4', '.flac', '.wav', '.ogg', '.m4a', '.wma', '.aac', '.gif')
        self.original_playlist = [
            os.path.join(folder_path, f).replace("\\", "/") for f in os.listdir(folder_path)
            if f.lower().endswith(extensions)
        ]
        self.playlist = list(self.original_playlist)
        self.invalidate_art_caches()
        self.duration_cache = {}

    def load_folder(self):
        folder_path = filedialog.askdirectory()
        if folder_path:
            # 読み込み時は自動再生しない。前の曲が鳴っていれば止めてから差し替える
            self.stop_audio_playback(unload=True)
            self.load_folder_path(folder_path)
            if self.playlist:
                self.current_index = 0
                self.last_seek_pos = 0
                self.save_state()

    def delete_current_file(self):
        if not self.playlist: return
        target_path = self.playlist[self.current_index]
        was_playing = self.is_playing and not self.is_paused

        self.stop_audio_playback(unload=True)
        time.sleep(0.1)

        try:
            os.remove(target_path)
            self.playlist.pop(self.current_index)
            if target_path in self.original_playlist:
                self.original_playlist.remove(target_path)
            self.invalidate_art_caches(target_path)
            if target_path in self.duration_cache: del self.duration_cache[target_path]
            if target_path in self.track_volume_map:
                del self.track_volume_map[target_path]
                self.save_track_volume_map()

            if self.playlist:
                if self.current_index >= len(self.playlist):
                    self.current_index = 0
                if was_playing:
                    self.start_audio(self.current_index)
                else:
                    self.last_seek_pos = 0
            else:
                pygame.display.set_caption(f"{APP_NAME} - No Music")
        except PermissionError:
            print("Error: File is locked by OS. Could not delete.")
            if was_playing:
                self.start_audio(self.current_index)
        except Exception as e:
            print(f"Error deleting file: {e}")

    def load_song_data_only(self, index):
        self.current_index = index
        self.last_seek_pos = 0

    def prepare_audio_file(self, file_path):
        ext = os.path.splitext(file_path)[1].lower()
        if ext in [".wav", ".ogg"]:
            return file_path
        if ext in [".mp3", ".flac"]:
            duration = self.get_duration(file_path)
            if duration > 3.0:
                return file_path

        need_convert_exts = [".mp4", ".m4a", ".aac", ".wma", ".gif", ".mp3", ".flac"]
        if ext in need_convert_exts:
            if AudioFileClip is None:
                print(f"Cannot play this file because moviepy is unavailable: {file_path}")
                return None

            fname = os.path.basename(file_path)
            temp_wav = os.path.join(TEMP_DIR, fname + ".wav")
            if os.path.exists(temp_wav):
                return temp_wav
            try:
                if ext == ".mp4":
                    video = VideoFileClip(file_path)
                    if video.audio:
                        video.audio.write_audiofile(temp_wav, codec='pcm_s16le', logger=None)
                    video.close()
                else:
                    audio = AudioFileClip(file_path)
                    audio.write_audiofile(temp_wav, codec='pcm_s16le', logger=None)
                    audio.close()
                return temp_wav
            except Exception as e:
                print(f"Audio conversion error: {e}")
                return None
        return file_path

    def request_track_change(self, step):
        if not self.playlist: return
        # 連続スクロール中は pending_audio_load が「再生を再開する予定」の印を兼ねる
        was_playing = (self.is_playing and not self.is_paused) or self.pending_audio_load
        self.current_index = (self.current_index + step) % len(self.playlist)
        self.last_seek_pos = 0

        self.stop_audio_playback(unload=False)
        self.is_animating = False
        self.visual_offset = 0.0
        self.pending_audio_load = was_playing  # 停止中の曲変更では自動再生しない
        self.audio_load_deadline = time.time() + AUDIO_LOAD_DELAY

    def start_audio(self, index, fade=False, start_pos=0):
        if not self.playlist: return
        self.current_index = index % len(self.playlist)
        self.last_seek_pos = start_pos
        original_path = self.playlist[self.current_index]
        with self.audio_lock:
            self.audio_request_id += 1
            request_id = self.audio_request_id

        def _load():
            try:
                play_path = self.prepare_audio_file(original_path)
                if not play_path:
                    return

                # デコード（重い処理）はロックの外で行い、UI側の操作を止めない
                sound = pygame.mixer.Sound(play_path)

                with self.audio_lock:
                    if request_id != self.audio_request_id:
                        return

                    self.music.set_endevent()

                    if fade and self.music.get_busy():
                        self.music.fadeout(300)
                        time.sleep(0.3)

                    self.music.load_from_sound(sound)
                    self.apply_effective_volume()
                    self.music.play(start=start_pos)
                    self.music.set_endevent(self.MUSIC_END)
                    self.analyze_spectrum(original_path)
                    # ビジュアライザー用にスペクトルを事前解析（バックグラウンド）
                    self.analyze_spectrum(original_path)
            except Exception as e:
                print(f"Playback error: {e}")

        threading.Thread(target=_load, daemon=True).start()
        self.is_playing = True
        self.is_paused = False
        self.title_scroll_y = 0
        self.title_scroll_x = 0
        self.save_state()

    def _begin_offset_anim(self, target_offset, change_track_step=0, play_after=None,
                           duration=ANIM_DURATION):
        # 現在の visual_offset から target_offset まで補間アニメーションする。
        # change_track_step != 0 のときはその曲数ぶん（複数曲可）切り替える。
        self.anim_start_offset = self.visual_offset
        self.anim_target_offset = float(target_offset)
        self.anim_timer = 0.0
        self.anim_duration = duration
        self.is_animating = True
        if play_after is None:
            # 曲変更時：変更開始時点で再生中だった場合のみ切替先を自動再生する
            # （停止中・一時停止中に曲を変えても勝手に鳴らさない）
            self.play_after_animation = (change_track_step != 0
                                         and self.is_playing and not self.is_paused)
        else:
            self.play_after_animation = bool(play_after)
        if change_track_step != 0:
            # start_audio が current_index を新しい値に更新するため、
            # 描画側は base_idx = current_index - move_direction で元位置を復元する
            self.move_direction = change_track_step
            self.move_direction = change_track_step
            self.stop_audio_playback(unload=False)
        else:
            self.move_direction = 0

    def trigger_animation(self, direction):
        if self.is_animating: return
        d = 1 if direction == "next" else -1
        self._begin_offset_anim(float(d), change_track_step=d)

    def ease_out_quart(self, x):
        return 1 - pow(1 - x, 4)

    def update(self):
        dt = self.clock.get_time() / 1000.0
        current_time = time.time()

        if self.pending_audio_load and current_time > self.audio_load_deadline:
            self.start_audio(self.current_index)
            self.pending_audio_load = False

        for b in self.shapes:
            b.update()

        if self.is_animating:
            self.anim_timer += dt
            progress = min(self.anim_timer / max(self.anim_duration, 1e-6), 1.0)
            eased_t = self.ease_out_quart(progress)
            self.visual_offset = self.anim_start_offset + (self.anim_target_offset - self.anim_start_offset) * eased_t
            if progress >= 1.0: self.finish_animation()

        # 周辺曲のジャケットを先読み（未デコード分の非同期読み込みを起動するだけ＝軽い）
        if self.playlist:
            look = self.current_index + (self.move_direction if self.is_animating else 0)
            for off in (-2, -1, 0, 1, 2):
                self.get_art_data(look + off)

        # 現在曲タイトル（縦書き用に文字列だけ保持）
        fname = "NO MUSIC"
        if self.playlist:
            disp_idx = self.current_index
            fname = os.path.basename(self.playlist[disp_idx % len(self.playlist)])
            fname = os.path.splitext(fname)[0]
        self.cur_title = fname

    def finish_animation(self):
        step = self.move_direction
        play_after = self.play_after_animation
        if step != 0 and self.playlist:
            self.current_index = (self.current_index + step) % len(self.playlist)
            self.last_seek_pos = 0
        self.is_animating = False
        self.visual_offset = 0.0
        self.move_direction = 0
        self.anim_start_offset = 0.0
        self.anim_target_offset = 0.0
        self.play_after_animation = False
        self.title_scroll_y = 0
        if play_after and self.playlist:
            self.start_audio(self.current_index)

    def draw_text_with_shadow(self, font, text, color, x, y, shadow=SHADOW_COLOR):
        sh = font.render(text, True, shadow)
        self.screen.blit(sh, (x + SHADOW_OFFSET, y + SHADOW_OFFSET))
        surf = font.render(text, True, color)
        self.screen.blit(surf, (x, y))
        return surf

    def _chamfer_points(self, rect, cut=10):
        l, t, w, h = rect
        r = l + w
        b = t + h
        c = max(2, min(cut, w // 4, h // 4))
        return [
            (l + c, t),
            (r - c, t),
            (r, t + c),
            (r, b - c),
            (r - c, b),
            (l + c, b),
            (l, b - c),
            (l, t + c),
        ]

    def draw_tech_panel(self, rect, fill=PANEL_FILL, border=MAIN_COLOR, cut=10, shadow=True, inner=True):
        pts = self._chamfer_points(rect, cut)
        if shadow:
            shadow_pts = [(x + SHADOW_OFFSET, y + SHADOW_OFFSET) for x, y in pts]
            pygame.draw.polygon(self.screen, SHADOW_COLOR, shadow_pts)
        pygame.draw.polygon(self.screen, fill, pts)
        pygame.draw.polygon(self.screen, border, pts, 2)
        if inner and rect.width > 40 and rect.height > 24:
            inner_rect = rect.inflate(-10, -10)
            inner_pts = self._chamfer_points(inner_rect, max(4, cut - 4))
            pygame.draw.polygon(self.screen, SUB_LINE_COLOR, inner_pts, 1)

    def draw_preview_slot(self, rect, song_index):
        self.draw_tech_panel(rect, fill=PANEL_FILL, cut=10, shadow=False, inner=False)
        if not self.playlist:
            return
        art_pad = 7
        art_size = min(rect.width, rect.height) - art_pad * 2
        small = self.get_small_art(song_index, art_size)
        if small is not None:
            ax = rect.centerx - art_size // 2
            ay = rect.centery - art_size // 2
            self.screen.blit(small, (ax, ay))
            pygame.draw.rect(self.screen, MAIN_COLOR, (ax - 2, ay - 2, art_size + 4, art_size + 4), 1)

    def _dim_band(self, rect, alpha=76, radius=6):
        # 半透明の黒帯（30%≈76）。ジャケットとの重なりを見やすくする下地
        s = pygame.Surface((rect.width, rect.height), pygame.SRCALPHA)
        pygame.draw.rect(s, (0, 0, 0, alpha), s.get_rect(), border_radius=radius)
        self.screen.blit(s, (rect.x, rect.y))

    def _truncate(self, font, text, max_w):
        if font.size(text)[0] <= max_w:
            return text
        ell = "…"
        while text and font.size(text + ell)[0] > max_w:
            text = text[:-1]
        return text + ell

    def draw_candidate_box(self, rect, song_index, role_color=MAIN_COLOR):
        # 候補枠：影＋枠＋小ジャケット＋タイトル
        shadow_r = rect.move(SHADOW_OFFSET, SHADOW_OFFSET)
        pygame.draw.rect(self.screen, SHADOW_COLOR, shadow_r, 3, border_radius=4)
        pygame.draw.rect(self.screen, role_color, rect, 3, border_radius=4)
        # 角の飾りドット
        for cxp, cyp in [(rect.left + 6, rect.top + 6), (rect.right - 6, rect.top + 6),
                         (rect.left + 6, rect.bottom - 6), (rect.right - 6, rect.bottom - 6)]:
            pygame.draw.circle(self.screen, role_color, (cxp, cyp), 1)

        if not self.playlist:
            return
        art_sz = rect.height - 14
        small = self.get_small_art(song_index, art_sz)
        ax = rect.left + 8
        ay = rect.centery - art_sz // 2
        if small is not None:
            self.screen.blit(small, (ax, ay))
            pygame.draw.rect(self.screen, role_color, (ax, ay, art_sz, art_sz), 1)

        # タイトル
        fname = os.path.basename(self.playlist[song_index % len(self.playlist)])
        fname = os.path.splitext(fname)[0]
        text_x = ax + art_sz + 10
        max_w = rect.right - 8 - text_x
        fname = self._truncate(self.font_small, fname, max_w)
        ts = self.font_small.render(fname, True, role_color)
        self.screen.blit(ts, (text_x, rect.centery - ts.get_height() // 2))

    def draw_vertical_title(self, frame_rect):
        # アート右の縦長枠に曲タイトルを1文字ずつ縦積みで表示（長ければ縦スクロール）
        shadow_r = frame_rect.move(SHADOW_OFFSET, SHADOW_OFFSET)
        pygame.draw.rect(self.screen, SHADOW_COLOR, shadow_r, 3, border_radius=4)
        pygame.draw.rect(self.screen, MAIN_COLOR, frame_rect, 3, border_radius=4)

        title = self.cur_title or ""
        chars = list(title)
        if not chars:
            return
        line_h = self.font_vtitle.get_height() - 2
        total_h = line_h * len(chars)
        inner_top = frame_rect.top + 12
        inner_bottom = frame_rect.bottom - 12
        avail_h = inner_bottom - inner_top

        self.screen.set_clip(frame_rect.inflate(-6, -6))
        if total_h > avail_h:
            self.title_scroll_y -= 0.4
            if self.title_scroll_y < -total_h:
                self.title_scroll_y = avail_h
            start_y = inner_top + self.title_scroll_y
        else:
            start_y = frame_rect.centery - total_h // 2

        cx = frame_rect.centerx
        for i, ch in enumerate(chars):
            cs = self.font_vtitle.render(ch, True, MAIN_COLOR)
            self.screen.blit(cs, (cx - cs.get_width() // 2, int(start_y + i * line_h)))
        self.screen.set_clip(None)

    def draw_right_panel(self):
        # 右オレンジパネル（文字・図形はダーク色）
        panel = pygame.Rect(PANEL_X, 0, SCREEN_SIZE[0] - PANEL_X, SCREEN_SIZE[1])
        pygame.draw.rect(self.screen, MAIN_COLOR, panel)
        cx = PANEL_X + (SCREEN_SIZE[0] - PANEL_X) // 2  # パネル中央 x

        # 閉じる×（パネル右上・ダーク色）
        close_rect = pygame.Rect(SCREEN_SIZE[0] - 34, 10, 22, 22)
        ccx, ccy = close_rect.centerx, close_rect.centery
        arm = 8
        pygame.draw.line(self.screen, BG_COLOR, (ccx - arm, ccy - arm), (ccx + arm, ccy + arm), 4)
        pygame.draw.line(self.screen, BG_COLOR, (ccx - arm, ccy + arm), (ccx + arm, ccy - arm), 4)
        self.close_button_rect = close_rect

        now = datetime.datetime.now()
        # 時(HH)・分(MM)を縦積み
        hh = self.font_time.render(now.strftime("%H"), True, BG_COLOR)
        mm = self.font_time.render(now.strftime("%M"), True, BG_COLOR)
        self.screen.blit(hh, (cx - hh.get_width() // 2, 30))
        self.screen.blit(mm, (cx - mm.get_width() // 2, 118))

        # 区切り線（1本の実線。パネル内に収める）
        line_y = 210
        pygame.draw.line(self.screen, BG_COLOR, (PANEL_X + 14, line_y),
                         (SCREEN_SIZE[0] - 14, line_y), 2)

        # 日付・曜日（3行：年 / 月日 / 曜日）左揃え・パネル内に収める
        date_x = PANEL_X + 14
        y_year = self.font_date.render(now.strftime("%Y"), True, BG_COLOR)
        y_md   = self.font_date.render(now.strftime("%m/%d"), True, BG_COLOR)
        y_wd   = self.font_date.render(now.strftime("%a"), True, BG_COLOR)
        self.screen.blit(y_year, (date_x, 222))
        self.screen.blit(y_md,   (date_x, 248))
        self.screen.blit(y_wd,   (date_x, 274))

        # 音量スライダー（常時表示・縦・右端寄り）
        vol_cx = SCREEN_SIZE[0] - 30   # パネル右端寄り
        vol_cx = SCREEN_SIZE[0] - 30
        vol_label = self.font_ui.render("VOL", True, BG_COLOR)
        self.screen.blit(vol_label, (vol_cx - vol_label.get_width() // 2, 372))

        track_x = vol_cx
        track_top = MASTER_VOL_TOP
        track_bottom = MASTER_VOL_BOTTOM
        track_h = track_bottom - track_top
        # トラック
        pygame.draw.line(self.screen, BG_COLOR, (track_x, track_top), (track_x, track_bottom), 5)
        # 目盛り（左側）
        # ノブ（上=大）
        knob_y = int(track_top + track_h * (1.0 - self.value_to_slider_ratio(
            self.get_master_volume_value(), MASTER_VOLUME_MIN, MASTER_VOLUME_MAX)))
        knob = pygame.Rect(track_x - 14, knob_y - 12, 28, 24)
        pygame.draw.rect(self.screen, BG_COLOR, knob, border_radius=3)
        for n in range(3):
            ly = knob.top + 7 + n * 5
            pygame.draw.line(self.screen, MAIN_COLOR, (knob.left + 6, ly), (knob.right - 6, ly), 2)
        # 掴み判定（左右に広め）
        self.vol_bar_rect = pygame.Rect(track_x - 18, track_top - 12, 36, track_h + 24)

        self.vol_bar_rect = pygame.Rect(track_x - 18, track_top - 12, 36, track_h + 24)

    def draw_player(self):
        self.screen.fill(BG_COLOR)

        # 背景幾何学模様（左ダーク領域のみ）
        self.bg_surface.fill((0, 0, 0, 0))
        for b in sorted(self.shapes, key=lambda s: s.depth):
            b.draw(self.bg_surface)
        self.screen.blit(self.bg_surface, (0, 0), area=pygame.Rect(0, 0, LEFT_W, SCREEN_SIZE[1]))

        # 右パネル
        self.draw_right_panel()

        # File ボタン（FolderUI.png）
        file_text_x = 22
        file_text_y = 28
        if self.icon_folder is not None:
            fi_w, fi_h = self.icon_folder.get_size()
            self.screen.blit(self.icon_folder, (file_text_x, file_text_y))
            self.folder_button_rect = pygame.Rect(file_text_x, file_text_y, fi_w, fi_h)
        else:
            # フォールバック：旧「File」テキスト表示
            fs = self.draw_text_with_shadow(self.font_ui, "File", MAIN_COLOR, file_text_x, file_text_y)
            pygame.draw.line(
                self.screen,
                MAIN_COLOR,
                (file_text_x, file_text_y + fs.get_height() + 1),
                (file_text_x + fs.get_width(), file_text_y + fs.get_height() + 1),
                2
            )
            self.folder_button_rect = pygame.Rect(
                file_text_x - 4,
                file_text_y - 4,
                fs.get_width() + 12,
                fs.get_height() + 12
            )

        # 曲が未読み込み（プレイリスト空）の初期状態では、File／時計／VOL のみ表示し、
        # ジャケット・上下プレビュー枠・タイトルバー・再生/シーク・ループ・ゴミ箱は一切描画しない
        if not self.playlist:
            self.next_box_rect = pygame.Rect(0, 0, 0, 0)
            self.prev_box_rect = pygame.Rect(0, 0, 0, 0)
            self.play_button_rect = pygame.Rect(0, 0, 0, 0)
            self.seek_bar_rect = pygame.Rect(0, 0, 0, 0)
            self.loop_button_rect = pygame.Rect(0, 0, 0, 0)
            self.trash_button_rect = pygame.Rect(0, 0, 0, 0)
            self.current_art_rect = pygame.Rect(0, 0, 0, 0)
            # 外周枠
            pygame.draw.rect(self.screen, MAIN_COLOR, (0, 0, SCREEN_SIZE[0], SCREEN_SIZE[1]), BORDER_WIDTH)
            pygame.display.flip()
            return

        # 表示基準（アニメ中は元の中央曲を基準にする）
        base_idx = self.current_index
        base_idx = self.current_index
        self.next_box_rect = pygame.Rect(0, 0, 0, 0)
        self.prev_box_rect = pygame.Rect(0, 0, 0, 0)

        # 上下スロット（背景だけ固定して、実際のアートはカルーセル描画に任せる）
        top_slot = pygame.Rect(177, 7, 106, 106)
        bottom_slot = pygame.Rect(177, 487, 106, 106)
        self.draw_preview_slot(top_slot, base_idx + 1)
        self.draw_preview_slot(bottom_slot, base_idx - 1)

        # --- 縦カルーセル（旧アニメーション復活） ---
        center_x, center_y = ART_CENTER
        carousel_clip = pygame.Rect(75, 3, 320, 592)
        self.screen.set_clip(carousel_clip)

        center_i = int(round(self.visual_offset))
        draw_range = list(range(center_i - 2, center_i + 3))
        draw_range.sort(key=lambda i: -abs(i - self.visual_offset))

        self.current_art_rect = pygame.Rect(0, 0, 0, 0)
        for i in draw_range:
            real_idx = base_idx + i
            pos = i - self.visual_offset
            dist = abs(pos)
            if dist > 2.5:
                continue

            scale = 1.0 - min(dist, 1.0) * 0.28
            x = center_x
            y = center_y - pos * V_SPACING
            size = int(ART_SIZE * scale)
            if size < 10:
                continue

            surf, colors = self.get_art_data(real_idx)
            if surf is None:
                continue

            surf_scaled = pygame.transform.smoothscale(surf, (size, size))
            f_gap = int(FRAME_GAP * scale)
            f_w = int(FRAME_WIDTH * scale)
            frame_size = size + (f_gap + f_w) * 2
            grad = self.create_gradient_frame(colors, frame_size)

            rect_x = x - frame_size // 2
            rect_y = int(y - frame_size // 2)

            shadow_rect = pygame.Rect(rect_x + SHADOW_OFFSET, rect_y + SHADOW_OFFSET, frame_size, frame_size)
            pygame.draw.rect(self.screen, SHADOW_COLOR, shadow_rect)

            self.screen.blit(grad, (rect_x, rect_y))
            inner_size = size + f_gap * 2
            pygame.draw.rect(self.screen, BG_COLOR, (x - inner_size // 2, int(y - inner_size // 2), inner_size, inner_size))
            self.screen.blit(surf_scaled, (x - size // 2, int(y - size // 2)))

            if i == 0 and not self.is_animating:
                # 中央アート外側にテック枠を追加
                outer = pygame.Rect(x - size // 2 - 10, int(y - size // 2 - 10), size + 20, size + 20)
                self.draw_tech_panel(outer, fill=(10, 10, 10), cut=10, shadow=False, inner=False)
                self.screen.blit(grad, (rect_x, rect_y))
                pygame.draw.rect(self.screen, BG_COLOR, (x - inner_size // 2, int(y - inner_size // 2), inner_size, inner_size))
                self.screen.blit(surf_scaled, (x - size // 2, int(y - size // 2)))
                self.current_art_rect = pygame.Rect(x - size // 2, int(y - size // 2), size, size)

        self.screen.set_clip(None)

        # --- 中央ジャケット左右のオーディオビジュアライザー ---
        self.draw_visualizer()
        self.draw_track_volume_control()

        # --- 再生状況の計算 ---
        progress = 0.0
        current_time_str = "0:00"

        if self.playlist:
            target_idx_raw = self.current_index
            target_idx = target_idx_raw % len(self.playlist)
            target_path = self.playlist[target_idx]
            total = self.get_duration(target_path)

            if self.seeking:
                progress = self.seek_drag_ratio
                current_sec = total * progress
                current_time_str = f"{int(current_sec // 60)}:{int(current_sec % 60):02d}"
            elif self.music.get_busy() or self.is_paused:
                current_ms = self.music.get_pos()
                if current_ms != -1:
                    current = (current_ms / 1000) + self.last_seek_pos
                    progress = min(current / total, 1.0)
                    current_time_str = f"{int(current // 60)}:{int(current % 60):02d}"

        # --- タイトル＋再生バー共通パネル ---
        panel_x = 78
        panel_y = 403
        panel_w = 350
        panel_h = 96
        panel_rect = pygame.Rect(panel_x, panel_y, panel_w, panel_h)
        self.draw_tech_panel(panel_rect, fill=PANEL_FILL, cut=12, shadow=True, inner=True)

        # タイトル表示
        title_area = pygame.Rect(panel_x + 18, panel_y + 10, panel_w - 36, 24)
        self.screen.set_clip(title_area)
        self.cur_title_surf = self.font_title.render(self.cur_title, True, TEXT_COLOR)
        tw = self.cur_title_surf.get_width()

        if tw > title_area.width:
            self.title_scroll_x -= 0.5
            if self.title_scroll_x < -tw:
                self.title_scroll_x = title_area.width
            text_x = int(self.title_scroll_x) + title_area.x
        else:
            text_x = title_area.centerx - tw // 2

        sh = self.font_title.render(self.cur_title, True, SHADOW_COLOR)
        self.screen.blit(sh, (text_x + SHADOW_OFFSET, title_area.y + SHADOW_OFFSET))
        self.screen.blit(self.cur_title_surf, (text_x, title_area.y))
        self.screen.set_clip(None)

        pygame.draw.line(self.screen, SUB_LINE_COLOR, (panel_x + 16, panel_y + 40), (panel_x + panel_w - 16, panel_y + 40), 1)

        # 再生/一時停止ボタン
        ctrl_y = panel_y + 70
        play_btn_pos = (panel_x + 28, ctrl_y)

        if self.is_playing:
            btn_cx, btn_cy = play_btn_pos
            bar_w_btn = 6
            bar_h_btn = 20
            gap = 5
            pygame.draw.rect(self.screen, SHADOW_COLOR,
                             (btn_cx - gap - bar_w_btn / 2 + SHADOW_OFFSET, btn_cy - bar_h_btn / 2 + SHADOW_OFFSET, bar_w_btn, bar_h_btn))
            pygame.draw.rect(self.screen, SHADOW_COLOR,
                             (btn_cx + gap - bar_w_btn / 2 + SHADOW_OFFSET, btn_cy - bar_h_btn / 2 + SHADOW_OFFSET, bar_w_btn, bar_h_btn))
            pygame.draw.rect(self.screen, MAIN_COLOR,
                             (btn_cx - gap - bar_w_btn / 2, btn_cy - bar_h_btn / 2, bar_w_btn, bar_h_btn))
            pygame.draw.rect(self.screen, MAIN_COLOR,
                             (btn_cx + gap - bar_w_btn / 2, btn_cy - bar_h_btn / 2, bar_w_btn, bar_h_btn))
        else:
            pygame.draw.polygon(
                self.screen,
                SHADOW_COLOR,
                [
                    (play_btn_pos[0] - 8 + SHADOW_OFFSET, play_btn_pos[1] - 12 + SHADOW_OFFSET),
                    (play_btn_pos[0] + 12 + SHADOW_OFFSET, play_btn_pos[1] + SHADOW_OFFSET),
                    (play_btn_pos[0] - 8 + SHADOW_OFFSET, play_btn_pos[1] + 12 + SHADOW_OFFSET)
                ]
            )
            pygame.draw.polygon(
                self.screen,
                MAIN_COLOR,
                [
                    (play_btn_pos[0] - 8, play_btn_pos[1] - 12),
                    (play_btn_pos[0] + 12, play_btn_pos[1]),
                    (play_btn_pos[0] - 8, play_btn_pos[1] + 12)
                ]
            )
        self.play_button_rect = pygame.Rect(play_btn_pos[0] - 15, play_btn_pos[1] - 15, 30, 30)

        # シークバー
        bar_x = panel_x + 58
        bar_y = ctrl_y
        bar_w = 210
        pygame.draw.line(self.screen, SHADOW_COLOR,
                         (bar_x + SHADOW_OFFSET, bar_y + SHADOW_OFFSET),
                         (bar_x + bar_w + SHADOW_OFFSET, bar_y + SHADOW_OFFSET), 4)
        pygame.draw.line(self.screen, (85, 85, 85), (bar_x, bar_y), (bar_x + bar_w, bar_y), 4)
        pygame.draw.line(self.screen, MAIN_COLOR, (bar_x, bar_y), (bar_x + bar_w * progress, bar_y), 4)
        pygame.draw.circle(self.screen, MAIN_COLOR, (int(bar_x + bar_w * progress), bar_y), 7)
        self.seek_bar_rect = pygame.Rect(bar_x, bar_y - 10, bar_w, 20)
        self.draw_text_with_shadow(self.font_small, current_time_str, MAIN_COLOR, bar_x + bar_w + 12, bar_y - 8)

        # ループボタン（ON=RoopUI_On.png / OFF=RoopUI_Off.png）
        loop_cx, loop_cy = 44, 566
        icon_shadow = SHADOW_OFFSET
        loop_img = self.icon_loop_on if self.loop_one else self.icon_loop_off
        if loop_img is not None:
            liw, lih = loop_img.get_size()
            self.screen.blit(loop_img, (loop_cx - liw // 2, loop_cy - lih // 2))
        else:
            # フォールバック：旧自作ループアイコン
            loop_color = MAIN_COLOR if self.loop_one else (180, 145, 0)
            pygame.draw.arc(
                self.screen, SHADOW_COLOR,
                pygame.Rect(loop_cx - 14 + icon_shadow, loop_cy - 13 + icon_shadow, 25, 21),
                math.radians(30), math.radians(315), 3
            )
            pygame.draw.polygon(
                self.screen, SHADOW_COLOR,
                [
                    (loop_cx + 13 + icon_shadow, loop_cy - 3 + icon_shadow),
                    (loop_cx + 21 + icon_shadow, loop_cy - 3 + icon_shadow),
                    (loop_cx + 14 + icon_shadow, loop_cy + 5 + icon_shadow)
                ]
            )
            pygame.draw.arc(
                self.screen, loop_color,
                pygame.Rect(loop_cx - 14, loop_cy - 13, 25, 21),
                math.radians(30), math.radians(315), 3
            )
            pygame.draw.polygon(
                self.screen, loop_color,
                [
                    (loop_cx + 13, loop_cy - 3),
                    (loop_cx + 21, loop_cy - 3),
                    (loop_cx + 14, loop_cy + 5)
                ]
            )
            pygame.draw.line(self.screen, loop_color, (loop_cx - 10, loop_cy + 11), (loop_cx + 12, loop_cy + 11), 2)
            if self.loop_one:
                one = self.font_small.render("1", True, MAIN_COLOR)
                self.screen.blit(one, (loop_cx - one.get_width() // 2 + 1, loop_cy - 8))
        self.loop_button_rect = pygame.Rect(loop_cx - 22, loop_cy - 22, 44, 44)

        # 曲削除ボタン（DustBox.png）
        trash_cx, trash_cy = 414, 566
        if self.icon_trash is not None:
            tiw, tih = self.icon_trash.get_size()
            self.screen.blit(self.icon_trash, (trash_cx - tiw // 2, trash_cy - tih // 2))
        else:
            # フォールバック：旧自作ゴミ箱アイコン
            tx = trash_cx - 10
            ty = trash_cy - 12
            pygame.draw.line(self.screen, SHADOW_COLOR, (tx - 2 + icon_shadow, ty + 4 + icon_shadow), (tx + 22 + icon_shadow, ty + 4 + icon_shadow), 3)
            pygame.draw.rect(self.screen, SHADOW_COLOR, (tx + 2 + icon_shadow, ty + 6 + icon_shadow, 18, 22), 2)
            pygame.draw.rect(self.screen, SHADOW_COLOR, (tx + 7 + icon_shadow, ty + icon_shadow, 8, 5), 2)
            pygame.draw.line(self.screen, SHADOW_COLOR, (tx + 7 + icon_shadow, ty + 10 + icon_shadow), (tx + 7 + icon_shadow, ty + 24 + icon_shadow), 1)
            pygame.draw.line(self.screen, SHADOW_COLOR, (tx + 13 + icon_shadow, ty + 10 + icon_shadow), (tx + 13 + icon_shadow, ty + 24 + icon_shadow), 1)
            pygame.draw.line(self.screen, MAIN_COLOR, (tx - 2, ty + 4), (tx + 22, ty + 4), 3)
            pygame.draw.rect(self.screen, MAIN_COLOR, (tx + 2, ty + 6, 18, 22), 2)
            pygame.draw.rect(self.screen, MAIN_COLOR, (tx + 7, ty, 8, 5), 2)
            pygame.draw.line(self.screen, MAIN_COLOR, (tx + 7, ty + 10), (tx + 7, ty + 24), 1)
            pygame.draw.line(self.screen, MAIN_COLOR, (tx + 13, ty + 10), (tx + 13, ty + 24), 1)
            pygame.draw.line(self.screen, MAIN_COLOR, (tx + 19, ty + 10), (tx + 17, ty + 24), 1)
        self.trash_button_rect = pygame.Rect(trash_cx - 22, trash_cy - 22, 44, 44)

        # 外周枠
        pygame.draw.rect(self.screen, MAIN_COLOR, (0, 0, SCREEN_SIZE[0], SCREEN_SIZE[1]), BORDER_WIDTH)
        pygame.display.flip()

    # --- サムネイル編集用メソッド ---
    def start_crop_mode(self):
        file_path = filedialog.askopenfilename(filetypes=[("Images", "*.jpg;*.jpeg;*.png")])
        if not file_path: return
        try:
            self.crop_image_raw = Image.open(file_path)
            w, h = self.crop_image_raw.size
            # 切り取り枠(ART_SIZE)＝画像の短い方の辺になるよう初期倍率を決める。
            # これで開いた瞬間は「画像の中心・短辺サイズの正方形」が選択される
            # （ドラッグ移動・スクロール拡縮で任意に変更可能なのは従来通り）
            self.crop_scale = ART_SIZE / min(w, h)
            self.crop_offset = [SCREEN_SIZE[0] / 2 - w * self.crop_scale / 2, SCREEN_SIZE[1] / 2 - h * self.crop_scale / 2]
            self.mode = "CROP"
        except: pass

    def save_cropped_image(self):
        # サムネイル(別JPG)を保存するだけで音声ファイルには触れないため、
        # 再生は止めずそのまま継続させる（曲送り・再生位置リセットを起こさない）
        cx, cy = SCREEN_SIZE[0] // 2, SCREEN_SIZE[1] // 2
        half = ART_SIZE // 2
        x1 = (cx - half - self.crop_offset[0]) / self.crop_scale
        y1 = (cy - half - self.crop_offset[1]) / self.crop_scale
        x2 = (cx + half - self.crop_offset[0]) / self.crop_scale
        y2 = (cy + half - self.crop_offset[1]) / self.crop_scale

        try:
            cropped = self.crop_image_raw.crop((x1, y1, x2, y2))
            cropped = cropped.resize((500, 500), Image.LANCZOS)
            if cropped.mode == "RGBA":
                cropped = cropped.convert("RGB")

            safe_idx = self.current_index % len(self.playlist)
            current_path = self.playlist[safe_idx]

            hash_name = hashlib.md5(current_path.encode('utf-8')).hexdigest()
            save_filename = f"{hash_name}.jpg"
            save_path = os.path.join(THUMB_DATA_DIR, save_filename)
            cropped.save(save_path, format="JPEG", quality=90)

            self.thumb_map[current_path] = save_path
            self.save_thumb_map()

            self.invalidate_art_caches()
            self.get_art_data(safe_idx)  # 新サムネの非同期デコードを即開始

            print(f"Saved custom thumbnail for: {os.path.basename(current_path)}")

        except Exception as e:
            print(f"Save error: {e}")

        self.mode = "PLAYER"

    def draw_crop_mode(self):
        self.screen.fill(BG_COLOR)
        w, h = self.crop_image_raw.size
        disp_w = int(w * self.crop_scale)
        disp_h = int(h * self.crop_scale)

        raw_surf = pygame.image.fromstring(self.crop_image_raw.tobytes(), self.crop_image_raw.size, self.crop_image_raw.mode).convert()
        scaled_surf = pygame.transform.scale(raw_surf, (disp_w, disp_h))
        self.screen.blit(scaled_surf, self.crop_offset)

        cx, cy = SCREEN_SIZE[0] // 2, SCREEN_SIZE[1] // 2
        half = ART_SIZE // 2
        crop_rect = pygame.Rect(cx - half, cy - half, ART_SIZE, ART_SIZE)

        # 切り取り範囲の外側に半透明の黒マスクを重ねる（他の画像編集ソフト風）。
        # ※ pygame.draw.rect は表示Surfaceのalphaを無視して真っ黒になるため、
        #   SRCALPHA のオーバーレイを作り、切り取り範囲だけ透明に抜いて重ねる
        overlay = pygame.Surface(SCREEN_SIZE, pygame.SRCALPHA)
        overlay.fill((0, 0, 0, 150))
        overlay.fill((0, 0, 0, 0), crop_rect)
        self.screen.blit(overlay, (0, 0))
        pygame.draw.rect(self.screen, MAIN_COLOR, crop_rect, 2)

        msg = self.font_ui.render("Drag/Scroll. ENTER:Save ESC:Cancel", True, (255, 255, 255))
        self.screen.blit(msg, (SCREEN_SIZE[0] // 2 - msg.get_width() // 2, 50))

        pygame.draw.rect(self.screen, MAIN_COLOR, (0, 0, SCREEN_SIZE[0], SCREEN_SIZE[1]), BORDER_WIDTH)
        pygame.display.flip()

    def run(self):
        while self.running:
            current_time = time.time()

            # ウィンドウサイズの監視。崩壊状態からの自動復元。
            # Win32呼び出し数回だけなので毎フレームで回す（1秒毎だと最大1秒間 黒帯が見える）
            self._enforce_window_size()

            keys = pygame.key.get_pressed()
            mouse_pos = pygame.mouse.get_pos()

            # --- 長押し状態の判定（縦：↑=次 / ↓=前） ---
            is_holding_next = False
            is_holding_prev = False
            if not self.mode == "CROP" and self.playlist:
                if keys[pygame.K_UP]:
                    is_holding_next = True
                if keys[pygame.K_DOWN]:
                    is_holding_prev = True

            if is_holding_next or is_holding_prev:
                if self.press_start_time is None:
                    self.press_start_time = current_time
                if current_time - self.press_start_time > HOLD_DELAY:
                    if current_time > self.next_scroll_time:
                        direction = 0
                        if is_holding_next and not is_holding_prev:
                            direction = 1
                        elif is_holding_prev and not is_holding_next:
                            direction = -1
                        if direction != 0:
                            self.request_track_change(direction)
                            self.next_scroll_time = current_time + SCROLL_INTERVAL
            else:
                self.press_start_time = None

            for event in pygame.event.get():
                if event.type == pygame.QUIT:
                    self.save_state()
                    self.save_thumb_map()
                    self.save_track_volume_map()
                    self.cleanup_temp()
                    self.running = False

                # OS由来のウィンドウ/ディスプレイ変化は即座に復元する。
                # （モニタ間移動でのDPI変更、解像度変更、スナップ等）
                if event.type in (getattr(pygame, "WINDOWSIZECHANGED", -1),
                                  getattr(pygame, "WINDOWRESIZED", -1),
                                  getattr(pygame, "WINDOWMAXIMIZED", -1),
                                  getattr(pygame, "WINDOWDISPLAYCHANGED", -1),
                                  getattr(pygame, "VIDEORESIZE", -1)):
                    log_window_event(
                        f"event {pygame.event.event_name(event.type)} dpi={self._window_dpi()}")
                    self._enforce_window_size()

                if self.mode == "CROP":
                    if event.type == pygame.KEYDOWN:
                        if event.key == pygame.K_RETURN: self.save_cropped_image()
                        elif event.key == pygame.K_ESCAPE: self.mode = "PLAYER"
                    elif event.type == pygame.MOUSEBUTTONDOWN:
                        if event.button == 1:
                            self.crop_dragging = True
                            self.crop_drag_start = pygame.mouse.get_pos()
                        elif event.button == 4: self.crop_scale *= 1.1
                        elif event.button == 5: self.crop_scale *= 0.9
                    elif event.type == pygame.MOUSEBUTTONUP:
                        if event.button == 1: self.crop_dragging = False
                    elif event.type == pygame.MOUSEMOTION:
                        if self.crop_dragging:
                            mx, my = pygame.mouse.get_pos()
                            dx, dy = mx - self.crop_drag_start[0], my - self.crop_drag_start[1]
                            self.crop_offset[0] += dx
                            self.crop_offset[1] += dy
                            self.crop_drag_start = (mx, my)
                else:
                    if event.type == self.MUSIC_END:
                        if self.is_playing or self.music.get_busy():
                            if self.loop_one:
                                self.start_audio(self.current_index)
                            else:
                                self.trigger_animation("next")

                    elif event.type == pygame.KEYDOWN:
                        if not self.is_animating:
                            is_holding = (self.press_start_time is not None)
                            if event.key == pygame.K_UP:
                                if not is_holding and self.can_perform_action():
                                    self.trigger_animation("next")
                            elif event.key == pygame.K_DOWN:
                                if not is_holding and self.can_perform_action():
                                    self.trigger_animation("prev")
                            elif event.key == pygame.K_SPACE:
                                self.toggle_play()
                            elif event.key == pygame.K_RIGHT:
                                self.set_master_volume_value(self.get_master_volume_value() + MASTER_VOLUME_STEP)
                            elif event.key == pygame.K_LEFT:
                                self.set_master_volume_value(self.get_master_volume_value() - MASTER_VOLUME_STEP)

                    elif event.type == pygame.MOUSEWHEEL:
                        # 音量バーの上では微調整（小音量の追い込み用）
                        if event.y != 0 and self.track_vol_bar_rect.collidepoint(mouse_pos) and self.playlist:
                            step = TRACK_VOLUME_WHEEL_STEP if event.y > 0 else -TRACK_VOLUME_WHEEL_STEP
                            self.set_current_track_volume(self.get_track_volume_percent() + step)
                            self.save_track_volume_map()
                        elif event.y != 0 and self.vol_bar_rect.collidepoint(mouse_pos):
                            step = MASTER_VOLUME_WHEEL_STEP if event.y > 0 else -MASTER_VOLUME_WHEEL_STEP
                            self.set_master_volume_value(self.get_master_volume_value() + step)
                        # それ以外はホイール上=次の曲／下=前の曲（上の候補を引き込む）
                        # クールダウン無し・アニメ中の入力は破棄せず目標に加算して滑らかに連続スクロール
                        elif event.y != 0 and self.playlist and not self.seeking and not self.swiping:
                            d = 1 if event.y > 0 else -1
                            if self.is_animating:
                                # 進行中のアニメに歩数を追加（現在位置から新目標へ継続）
                                self.anim_start_offset = self.visual_offset
                                self.anim_target_offset += d
                                self.move_direction += d
                                self.anim_timer = 0.0
                                self.anim_duration = WHEEL_ANIM_DURATION
                            else:
                                self._begin_offset_anim(float(d), change_track_step=d,
                                                        duration=WHEEL_ANIM_DURATION)

                    elif event.type == pygame.MOUSEBUTTONDOWN:
                        if event.button == 1:
                            if self.close_button_rect.collidepoint(mouse_pos):
                                self.save_state()
                                self.save_thumb_map()
                                self.save_track_volume_map()
                                self.cleanup_temp()
                                self.running = False
                            elif self.folder_button_rect.collidepoint(mouse_pos):
                                self.load_folder()
                            elif self.play_button_rect.collidepoint(mouse_pos):
                                self.toggle_play()
                            elif self.loop_button_rect.collidepoint(mouse_pos):
                                self.loop_one = not self.loop_one
                            elif self.track_vol_bar_rect.collidepoint(mouse_pos) and self.playlist:
                                self.track_volume_dragging = True
                                self.set_current_track_volume_from_y(mouse_pos[1])
                            elif self.vol_bar_rect.collidepoint(mouse_pos):
                                self.set_master_volume_from_y(mouse_pos[1])
                            elif self.seek_bar_rect.collidepoint(mouse_pos) and self.playlist:
                                self.seeking = True
                                ratio = (mouse_pos[0] - self.seek_bar_rect.x) / self.seek_bar_rect.width
                                self.seek_drag_ratio = min(max(ratio, 0.0), 1.0)
                            elif self.next_box_rect.collidepoint(mouse_pos) and self.playlist:
                                if not self.is_animating and self.can_perform_action():
                                    self.trigger_animation("next")
                            elif self.prev_box_rect.collidepoint(mouse_pos) and self.playlist:
                                if not self.is_animating and self.can_perform_action():
                                    self.trigger_animation("prev")
                            elif self.trash_button_rect.collidepoint(mouse_pos):
                                if self.can_perform_action(): self.delete_current_file()
                            # 右パネルの時計エリア → ウィンドウ移動
                            elif mouse_pos[0] >= PANEL_X and mouse_pos[1] < 380:
                                self.begin_window_drag()
                            # 左領域の上部余白 → ウィンドウ移動
                            elif mouse_pos[1] < 90 and mouse_pos[0] < PANEL_X:
                                self.begin_window_drag()
                            # 中央エリア → スワイプ／クリック判定開始
                            else:
                                self.swiping = True
                                self.swipe_start_pos = mouse_pos
                                self.swipe_moved = False
                                self.resume_after_scroll = False

                    elif event.type == pygame.MOUSEBUTTONUP:
                        if event.button == 1:
                            self.window_dragging = False
                            if self.track_volume_dragging:
                                self.track_volume_dragging = False
                                self.save_track_volume_map()
                            elif self.seeking:
                                self.seeking = False
                                if self.playlist:
                                    try:
                                        idx = self.current_index
                                        target_path = self.playlist[idx % len(self.playlist)]
                                        total = self.get_duration(target_path)
                                        start_pos = total * self.seek_drag_ratio
                                        self.start_audio(self.current_index, fade=False, start_pos=start_pos)
                                    except: pass
                            elif self.swiping:
                                self.swiping = False
                                if self.swipe_moved and not self.is_animating and self.playlist:
                                    offset = self.visual_offset
                                    step = 0
                                    if abs(offset) >= SWIPE_THRESHOLD:
                                        step = int(round(offset))
                                        if step == 0:
                                            step = 1 if offset > 0 else -1
                                    # スワイプ開始時に再生中だった場合のみ切替先を再生（停止中は停止のまま）
                                    play_after = self.resume_after_scroll
                                    self.resume_after_scroll = False
                                    self._begin_offset_anim(float(step), change_track_step=step, play_after=play_after)
                                elif not self.swipe_moved:
                                    if self.current_art_rect.collidepoint(self.swipe_start_pos):
                                        if self.playlist: self.start_crop_mode()

                    elif event.type == pygame.MOUSEMOTION:
                        if self.window_dragging:
                            self.update_window_drag()
                        elif self.track_volume_dragging:
                            self.set_current_track_volume_from_y(mouse_pos[1])
                        elif self.seeking:
                            ratio = (mouse_pos[0] - self.seek_bar_rect.x) / self.seek_bar_rect.width
                            self.seek_drag_ratio = min(max(ratio, 0.0), 1.0)
                        elif self.swiping and not self.is_animating:
                            dy = mouse_pos[1] - self.swipe_start_pos[1]
                            if abs(dy) > CLICK_MOVE_TOLERANCE and not self.swipe_moved:
                                self.swipe_moved = True
                                self.resume_after_scroll = self.is_playing and not self.is_paused
                                self.stop_audio_playback(unload=False)
                            if self.swipe_moved:
                                # 下ドラッグで上の「次曲」が中央へ降りてくる
                                self.visual_offset = dy / SWIPE_SPACING
                        if (not self.track_volume_dragging and
                                pygame.mouse.get_pressed()[0] and self.vol_bar_rect.collidepoint(mouse_pos)):
                            self.set_master_volume_from_y(mouse_pos[1])

            if self.mode == "PLAYER":
                self.update()
                self.draw_player()
            else:
                self.draw_crop_mode()

            self.clock.tick(60)
        pygame.quit()

    def toggle_play(self):
        if not self.playlist: return
        if self.is_playing:
            self.music.pause()
            self.is_playing = False
            self.is_paused = True
        else:
            if self.is_paused:
                self.music.unpause()
                self.is_paused = False
                self.is_playing = True
            else:
                self.start_audio(self.current_index)


if __name__ == "__main__":
    player = SketchMusicPlayer()
    player.run()
