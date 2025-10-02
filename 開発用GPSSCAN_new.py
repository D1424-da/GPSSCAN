#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
測量写真リネームアプリケーション GPSSCAN
- SIMファイル（A01/A02/D00形式）読み込み
- 写真のGPS/EXIF情報抽出
- ドラッグ&ドロップによる写真マッチング
- 自動ファイル名生成（新規写真が-1/-2、既存写真を通し番号に変更）
- 測量座標系対応（X=北、Y=東）
"""

import os
import sys
import re
import math
import shutil
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, simpledialog
from datetime import datetime
import traceback

# 必要なライブラリのインポート
try:
    from PIL import Image, ExifTags
    import piexif
except ImportError:
    print("Pillowがインストールされていません。pip install Pillowを実行してください。")
    sys.exit(1)

try:
    import pandas as pd
except ImportError:
    print("pandasがインストールされていません。pip install pandasを実行してください。")
    sys.exit(1)

try:
    import cv2
except ImportError:
    print("opencv-pythonがインストールされていません。pip install opencv-pythonを実行してください。")
    sys.exit(1)

try:
    import numpy as np
except ImportError:
    print("numpyがインストールされていません。pip install numpyを実行してください。")
    sys.exit(1)

try:
    from skimage.metrics import structural_similarity as ssim
except ImportError:
    print("scikit-imageがインストールされていません。pip install scikit-imageを実行してください。")
    sys.exit(1)

try:
    from pyproj import Transformer
except ImportError:
    print("pyprojがインストールされていません。pip install pyprojを実行してください。")
    sys.exit(1)

try:
    import matplotlib
    matplotlib.use('TkAgg')
    import matplotlib.pyplot as plt
    from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg, NavigationToolbar2Tk
    from matplotlib.figure import Figure
except ImportError:
    print("matplotlibがインストールされていません。pip install matplotlibを実行してください。")
    sys.exit(1)

try:
    import exifread
except ImportError:
    print("exifreadがインストールされていません。pip install exifreadを実行してください。")
    sys.exit(1)

# 日本語フォント設定
def setup_japanese_font():
    """日本語フォントの設定"""
    try:
        import japanize_matplotlib
        print("japanize_matplotlib を使用します")
        return True
    except ImportError:
        print("japanize_matplotlibが見つかりません。フォールバック設定を使用します。")
        
    # フォールバック：システムフォントを探す
    import matplotlib.font_manager as fm
    
    japanese_fonts = ['Yu Gothic', 'MS Gothic', 'Meiryo', 'IPAexGothic', 'IPAGothic']
    
    for font_name in japanese_fonts:
        fonts = [f for f in fm.fontManager.ttflist if font_name in f.name]
        if fonts:
            plt.rcParams['font.family'] = fonts[0].name
            print(f"使用フォント: {fonts[0].name}")
            return True
    
    print("警告: 日本語フォントが見つかりません。文字化けする可能性があります。")
    return False


class GPSScanApp:
    """測量写真リネームアプリケーション メインクラス"""
    
    def __init__(self, root):
        """初期化"""
        self.root = root
        self.root.title("測量写真リネームアプリケーション GPSSCAN")
        self.root.geometry("1400x900")
        
        # 日本語フォント設定
        setup_japanese_font()
        
        # データ保持用変数
        self.sim_points = []  # SIMファイルの測量点データ
        self.landparcel_data = []  # 地番データ
        self.photo_gps_data = {}  # 写真のGPS/EXIF情報
        self.photo_directory = tk.StringVar()  # 写真フォルダパス
        self.sim_file_path = tk.StringVar()  # SIMファイルパス
        self.use_arbitrary_coordinates = tk.BooleanVar(value=False)  # 任意座標系使用フラグ
        self.use_point_name = tk.BooleanVar(value=False)  # 点名使用フラグ
        self.use_landscape_suffix = tk.BooleanVar(value=True)  # 遠景/近景サフィックス使用フラグ
        self.force_point_name_for_special = tk.BooleanVar(value=True)  # 基準点・引照点は点名強制
        self.coordinate_system = tk.IntVar(value=9)  # 平面直角座標系（1～19系、デフォルト9系：東京）
        self.use_gps_conversion = tk.BooleanVar(value=True)  # GPS座標変換を使用
        
        # ドラッグ&ドロップ用変数
        self.dragging_photo = None
        self.drag_start_x = None
        self.drag_start_y = None
        self.panning = False
        self.pan_start_x = None
        self.pan_start_y = None
        
        # 地図表示用変数
        self.figure = None
        self.ax = None
        self.canvas = None
        self.current_xlim = None
        self.current_ylim = None
        self.photo_scatter = None
        self.photo_points = []
        
        # マウスオーバープレビュー用
        self.hover_annotation = None
        self.hover_window = None
        self.last_hover_photo = None
        
        # 測量図の初期表示範囲を保存
        self.initial_xlim = None
        self.initial_ylim = None
        
        # ドラッグ方法の設定（メニュー作成前に初期化が必要）
        # 1=写真リストから, 2=配置図から
        self.drag_mode = tk.IntVar(value=1)  # ドラッグモード（デフォルト：写真リスト）
        
        # UI構築
        self.create_menu()
        self.create_widgets()
        
    def create_menu(self):
        """メニューバーの作成"""
        menubar = tk.Menu(self.root)
        self.root.config(menu=menubar)
        
        # ファイルメニュー
        file_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="ファイル", menu=file_menu)
        file_menu.add_command(label="SIMファイルを開く", command=self.load_sim_file)
        file_menu.add_command(label="写真フォルダを開く", command=self.load_photo_folder)
        file_menu.add_separator()
        file_menu.add_command(label="GPS座標で自動マッチング", command=self.auto_match_by_gps)
        file_menu.add_command(label="マッチング統計", command=self.show_statistics)
        file_menu.add_separator()
        file_menu.add_command(label="リネーム実行", command=self.rename_photos_to_new_folder)
        file_menu.add_separator()
        file_menu.add_command(label="終了", command=self.root.quit)
        
        # 設定メニュー
        settings_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="設定", menu=settings_menu)
        settings_menu.add_checkbutton(label="点名を使用", variable=self.use_point_name)
        settings_menu.add_checkbutton(label="遠景/近景サフィックス使用", variable=self.use_landscape_suffix)
        settings_menu.add_checkbutton(label="基準点・引照点は点名を強制", variable=self.force_point_name_for_special)
        settings_menu.add_separator()
        settings_menu.add_command(label="設定を保存", command=self.save_settings)
        settings_menu.add_command(label="設定を読み込み", command=self.load_settings)
        
        # ヘルプメニュー
        help_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="ヘルプ", menu=help_menu)
        help_menu.add_command(label="使い方", command=self.show_help)
        help_menu.add_command(label="バージョン情報", command=self.show_about)
    
    def create_widgets(self):
        """UIウィジェットの作成"""
        # メインフレーム
        main_frame = ttk.Frame(self.root)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # 上部：ファイル選択フレーム
        file_frame = ttk.LabelFrame(main_frame, text="ファイル選択", padding=10)
        file_frame.pack(fill=tk.X, padx=5, pady=5)
        
        # SIMファイル選択
        ttk.Label(file_frame, text="SIMファイル:").grid(row=0, column=0, sticky=tk.W, padx=5, pady=2)
        ttk.Entry(file_frame, textvariable=self.sim_file_path, width=60).grid(row=0, column=1, padx=5, pady=2)
        ttk.Button(file_frame, text="参照", command=self.load_sim_file).grid(row=0, column=2, padx=5, pady=2)
        
        # 写真フォルダ選択
        ttk.Label(file_frame, text="写真フォルダ:").grid(row=1, column=0, sticky=tk.W, padx=5, pady=2)
        ttk.Entry(file_frame, textvariable=self.photo_directory, width=60).grid(row=1, column=1, padx=5, pady=2)
        ttk.Button(file_frame, text="参照", command=self.load_photo_folder).grid(row=1, column=2, padx=5, pady=2)
        
        # 座標系設定
        coord_frame = ttk.LabelFrame(file_frame, text="座標系設定")
        coord_frame.grid(row=2, column=0, columnspan=3, sticky=tk.EW, padx=5, pady=5)
        
        self.gps_conversion_check = ttk.Checkbutton(
            coord_frame, 
            text="GPS座標を平面直角座標に変換", 
            variable=self.use_gps_conversion,
            command=self.on_gps_conversion_changed
        )
        self.gps_conversion_check.grid(row=0, column=0, sticky=tk.W, padx=5, pady=2)
        
        ttk.Label(coord_frame, text="座標系:").grid(row=0, column=1, sticky=tk.W, padx=(20, 5), pady=2)
        
        self.coord_combo = ttk.Combobox(
            coord_frame, 
            textvariable=self.coordinate_system, 
            values=list(range(1, 20)), 
            width=5,
            state="readonly"
        )
        self.coord_combo.grid(row=0, column=2, sticky=tk.W, pady=2)
        
        ttk.Label(coord_frame, text="系（1:長崎/鹿児島 ～ 9:東京 ～ 19:沖縄）").grid(row=0, column=3, sticky=tk.W, padx=5, pady=2)
        
        # 座標系情報ラベル
        self.coord_info_label = ttk.Label(coord_frame, text="", foreground="blue")
        self.coord_info_label.grid(row=1, column=0, columnspan=4, sticky=tk.W, padx=5, pady=2)
        
        # ドラッグ方法選択とリネーム実行ボタン
        action_frame = ttk.Frame(file_frame)
        action_frame.grid(row=3, column=0, columnspan=3, sticky=tk.EW, padx=5, pady=10)
        
        # ドラッグ方法選択
        drag_label_frame = ttk.LabelFrame(action_frame, text="ドラッグ方法", padding=5)
        drag_label_frame.pack(side=tk.LEFT, padx=(0, 10))
        
        ttk.Radiobutton(
            drag_label_frame, 
            text="写真リストからドラッグ", 
            variable=self.drag_mode, 
            value=1
        ).pack(side=tk.LEFT, padx=5)
        
        ttk.Radiobutton(
            drag_label_frame, 
            text="配置図からドラッグ", 
            variable=self.drag_mode, 
            value=2
        ).pack(side=tk.LEFT, padx=5)
        
        # リネーム実行ボタン
        ttk.Button(
            action_frame, 
            text="リネーム実行", 
            command=self.rename_photos_to_new_folder,
            style="Accent.TButton"
        ).pack(side=tk.RIGHT, padx=5)
        
        ttk.Button(
            action_frame, 
            text="GPS自動マッチング", 
            command=self.auto_match_by_gps
        ).pack(side=tk.RIGHT, padx=5)
        
        ttk.Button(
            action_frame, 
            text="マッチング統計", 
            command=self.show_statistics
        ).pack(side=tk.RIGHT, padx=5)
        
        # 中部：メインコンテンツ（左右分割）
        content_frame = ttk.Frame(main_frame)
        content_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # 左側：写真リスト
        left_frame = ttk.LabelFrame(content_frame, text="写真リスト", padding=10)
        left_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 5))
        
        # 写真リスト（TreeView）
        columns = ("元ファイル名", "新ファイル名", "撮影日時", "遠景/近景", "X座標", "Y座標", "マッチングポイント", "距離")
        self.photos_tree = ttk.Treeview(left_frame, columns=columns, show="headings", height=15)
        
        for col in columns:
            self.photos_tree.heading(col, text=col)
            if col == "元ファイル名":
                self.photos_tree.column(col, width=150)
            elif col == "新ファイル名":
                self.photos_tree.column(col, width=150)
            elif col == "撮影日時":
                self.photos_tree.column(col, width=130)
            elif col == "遠景/近景":
                self.photos_tree.column(col, width=80)
            elif col in ["X座標", "Y座標"]:
                self.photos_tree.column(col, width=100)
            elif col == "マッチングポイント":
                self.photos_tree.column(col, width=120)
            else:
                self.photos_tree.column(col, width=80)
        
        # スクロールバー
        tree_scroll = ttk.Scrollbar(left_frame, orient=tk.VERTICAL, command=self.photos_tree.yview)
        self.photos_tree.configure(yscrollcommand=tree_scroll.set)
        
        self.photos_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        tree_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        
        # 写真リストのコンテキストメニュー
        self.photos_tree.bind("<Button-3>", self.show_photo_context_menu)
        self.photos_tree.bind("<Double-1>", self.preview_photo)
        self.photos_tree.bind("<Motion>", self.on_tree_motion)  # マウスオーバープレビュー
        self.photos_tree.bind("<Leave>", self.on_tree_leave)  # マウスが離れた時
        
        # 右側：地図表示
        right_frame = ttk.LabelFrame(content_frame, text="地図表示", padding=10)
        right_frame.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)
        
        # 地図コントロールボタン
        map_control_frame = ttk.Frame(right_frame)
        map_control_frame.pack(fill=tk.X, pady=(0, 5))
        
        ttk.Button(map_control_frame, text="📍 測量図の位置に戻る", 
                  command=self.reset_map_view).pack(side=tk.LEFT, padx=5)
        
        # 操作説明ラベル（配置図の上部に独立表示）
        help_frame = ttk.Frame(right_frame, relief=tk.RIDGE, borderwidth=2)
        help_frame.pack(fill=tk.X, padx=5, pady=5)
        
        help_label = ttk.Label(
            help_frame, 
            text="【配置図操作】 右クリック+ドラッグ:パン移動\nマウスホイール:ズーム拡大/縮小 | 左クリック:写真選択",
            font=("", 9, "bold"),
            foreground="blue",
            background="lightyellow",
            padding=5,
            justify="left"
        )
        help_label.pack(fill=tk.X)
        
        # 地図表示エリア
        self.map_frame = ttk.Frame(right_frame)
        self.map_frame.pack(fill=tk.BOTH, expand=True)
        
        # 下部：ステータスバー
        status_frame = ttk.Frame(main_frame)
        status_frame.pack(fill=tk.X, padx=5, pady=5)
        
        self.status_label = ttk.Label(status_frame, text="準備完了", relief=tk.SUNKEN)
        self.status_label.pack(fill=tk.X)
        
    def load_sim_file(self):
        """SIMファイルの読み込み"""
        file_path = filedialog.askopenfilename(
            title="SIMファイルを選択",
            filetypes=[("SIMファイル", "*.sim"), ("全てのファイル", "*.*")]
        )
        
        if not file_path:
            return
        
        self.sim_file_path.set(file_path)
        self.status_label.config(text=f"SIMファイル読み込み中: {os.path.basename(file_path)}")
        
        try:
            self.load_sim_points(file_path)
            self.update_map()
            self.status_label.config(text=f"SIMファイル読み込み完了: {len(self.sim_points)}点")
            messagebox.showinfo("成功", f"{len(self.sim_points)}点の測量点を読み込みました")
        except Exception as e:
            self.status_label.config(text="SIMファイル読み込み失敗")
            messagebox.showerror("エラー", f"SIMファイルの読み込みに失敗しました:\n{str(e)}")
            print(f"SIMファイル読み込みエラー:\n{traceback.format_exc()}")
    
    def load_sim_points(self, file_path):
        """SIMファイルから測量点データを読み込む"""
        self.sim_points = []
        self.landparcel_data = []
        
        with open(file_path, 'r', encoding='shift_jis', errors='ignore') as f:
            lines = f.readlines()
        
        # 座標系判定用のフラグ
        has_negative = False
        
        i = 0
        while i < len(lines):
            line = lines[i].strip()
            
            # A01: 測量点データ（A01,点番,点名,X座標,Y座標,Z座標,...）
            if line.startswith('A01'):
                parts = line.split(',')
                if len(parts) >= 5:
                    try:
                        point_num = parts[1].strip()
                        point_name = parts[2].strip()
                        
                        # 空フィールドチェック付きでX,Y座標を取得
                        x_str = parts[3].strip()
                        y_str = parts[4].strip()
                        
                        if not x_str or not y_str:
                            print(f"A01行の座標が空です: {line}")
                            continue
                        
                        x_coord = float(x_str)  # X座標
                        y_coord = float(y_str)  # Y座標
                        
                        # Z座標（空の場合は0.0）
                        z_coord = 0.0
                        if len(parts) > 5:
                            z_str = parts[5].strip()
                            if z_str:
                                z_coord = float(z_str)
                        
                        # マイナス符号チェック
                        if x_coord < 0 or y_coord < 0:
                            has_negative = True
                        
                        self.sim_points.append({
                            '点番': point_num,
                            '点名': point_name,
                            'X座標': x_coord,
                            'Y座標': y_coord,
                            'Z座標': z_coord
                        })
                    except (ValueError, IndexError) as e:
                        print(f"A01行の解析エラー: {line}\n{e}")
            
            # A02: 旧形式地番データ
            elif line.startswith('A02'):
                parts = line.split(',')
                if len(parts) >= 4:
                    try:
                        landparcel_name = parts[2].strip()
                        point_count = int(parts[3].strip())
                        
                        coordinates = []
                        for j in range(point_count):
                            if i + 1 + j < len(lines):
                                coord_line = lines[i + 1 + j].strip()
                                coord_parts = coord_line.split(',')
                                if len(coord_parts) >= 2:
                                    y = float(coord_parts[0].strip())
                                    x = float(coord_parts[1].strip())
                                    coordinates.append((x, y))
                                    
                                    if x < 0 or y < 0:
                                        has_negative = True
                        
                        if coordinates:
                            self.landparcel_data.append({
                                '地番': landparcel_name,
                                '座標': coordinates
                            })
                        
                        i += point_count
                    except (ValueError, IndexError) as e:
                        print(f"A02行の解析エラー: {line}\n{e}")
            
            # D00: 新形式地番データ（B01点データ付き）
            elif line.startswith('D00'):
                try:
                    landparcel_info, lines_processed = self.parse_d00_landparcel(lines, i)
                    if landparcel_info:
                        self.landparcel_data.append(landparcel_info)
                        print(f"D00地番追加: {landparcel_info['地番']}, {len(landparcel_info['座標'])}点")
                        
                        # マイナス符号チェック
                        for x, y in landparcel_info['座標']:
                            if x < 0 or y < 0:
                                has_negative = True
                        
                        # 処理した行数分をスキップ
                        i += lines_processed
                        continue
                except Exception as e:
                    print(f"D00行の解析エラー: {line}\n{e}\n{traceback.format_exc()}")
            
            i += 1
        
        # 座標系の自動判定（改善版：座標値の範囲で判定）
        is_arbitrary = self.detect_coordinate_system_type()
        
        if is_arbitrary:
            self.use_arbitrary_coordinates.set(True)
            self.use_gps_conversion.set(False)
            self.coord_combo.config(state="disabled")
            self.gps_conversion_check.config(state="disabled")
            self.coord_info_label.config(
                text="⚠ 任意座標系（ローカル座標系）を検出しました。GPS変換を無効化しました。",
                foreground="red"
            )
            print("任意座標系として処理します（GPS変換無効）")
            messagebox.showinfo(
                "任意座標系検出",
                "SIMファイルに任意座標系（ローカル座標系）を検出しました。\n\n"
                "GPS座標変換を自動的に無効化しました。\n"
                "写真を地図上の測量点にドラッグ&ドロップして\n"
                "手動でマッチングしてください。"
            )
        else:
            self.use_arbitrary_coordinates.set(False)
            self.use_gps_conversion.set(True)
            self.coord_combo.config(state="readonly")
            self.gps_conversion_check.config(state="normal")
            
            # 座標系番号を自動推定
            detected_system = self.detect_coordinate_system_number()
            if detected_system:
                self.coordinate_system.set(detected_system)
                self.coord_info_label.config(
                    text=f"✓ 平面直角座標系 {detected_system}系 を検出しました。GPS座標を自動変換します。",
                    foreground="green"
                )
                print(f"平面直角座標系 {detected_system}系 として処理します（GPS変換有効）")
            else:
                self.coord_info_label.config(
                    text=f"✓ 平面直角座標系として処理します。座標系を確認してください（現在: {self.coordinate_system.get()}系）",
                    foreground="orange"
                )
                print(f"平面直角座標系として処理します（座標系: {self.coordinate_system.get()}系、GPS変換有効）")
        
        print(f"測量点: {len(self.sim_points)}点、地番: {len(self.landparcel_data)}筆 読み込み完了")
    
    def detect_coordinate_system_type(self):
        """座標系のタイプ判定（任意座標系 vs 平面直角座標系）"""
        if not self.sim_points:
            return False
        
        # 座標値の範囲をチェック
        x_coords = [p['X座標'] for p in self.sim_points]
        y_coords = [p['Y座標'] for p in self.sim_points]
        
        x_min, x_max = min(x_coords), max(x_coords)
        y_min, y_max = min(y_coords), max(y_coords)
        
        # 判定基準
        # 1. 座標値が非常に小さい（±5000m以内）→ 任意座標系の可能性が高い
        if abs(x_max) < 5000 and abs(x_min) < 5000 and abs(y_max) < 5000 and abs(y_min) < 5000:
            print(f"座標範囲が小さい（X: {x_min:.1f}～{x_max:.1f}, Y: {y_min:.1f}～{y_max:.1f}）→ 任意座標系")
            return True
        
        # 2. 座標値が平面直角座標系の範囲内（±300,000m）→ 平面直角座標系
        if (abs(x_min) < 300000 and abs(x_max) < 300000 and 
            abs(y_min) < 300000 and abs(y_max) < 300000):
            print(f"座標範囲が平面直角座標系の範囲内（X: {x_min:.1f}～{x_max:.1f}, Y: {y_min:.1f}～{y_max:.1f}）→ 平面直角座標系")
            return False
        
        # 3. それ以外は任意座標系として扱う（安全側）
        print(f"座標系の判定が困難（X: {x_min:.1f}～{x_max:.1f}, Y: {y_min:.1f}～{y_max:.1f}）→ 任意座標系として扱います")
        return True
    
    def detect_coordinate_system_number(self):
        """平面直角座標系の系番号を自動推定（1～19系）"""
        if not self.sim_points:
            return None
        
        # 座標値の平均を計算
        x_coords = [p['X座標'] for p in self.sim_points]
        y_coords = [p['Y座標'] for p in self.sim_points]
        
        avg_x = sum(x_coords) / len(x_coords)
        avg_y = sum(y_coords) / len(y_coords)
        
        print(f"座標の平均値: X={avg_x:.1f}, Y={avg_y:.1f}")
        
        # 各系の原点からの大まかな適用範囲（X, Y）
        # 参考: 国土地理院の平面直角座標系一覧
        system_ranges = {
            1: {'x_range': (-150000, 150000), 'y_range': (-150000, 100000), 'name': '長崎・鹿児島'},
            2: {'x_range': (-250000, 50000), 'y_range': (-150000, 100000), 'name': '福岡・佐賀・熊本・大分・宮崎・鹿児島'},
            3: {'x_range': (-150000, 150000), 'y_range': (-150000, 150000), 'name': '山口・島根・広島'},
            4: {'x_range': (-150000, 150000), 'y_range': (-150000, 150000), 'name': '香川・愛媛・徳島・高知'},
            5: {'x_range': (-150000, 150000), 'y_range': (-150000, 150000), 'name': '兵庫・鳥取・岡山'},
            6: {'x_range': (-150000, 150000), 'y_range': (-150000, 150000), 'name': '京都・大阪・福井・滋賀・三重・奈良・和歌山'},
            7: {'x_range': (-150000, 150000), 'y_range': (-150000, 150000), 'name': '石川・富山・岐阜・愛知'},
            8: {'x_range': (-150000, 150000), 'y_range': (-150000, 150000), 'name': '新潟・長野・山梨・静岡'},
            9: {'x_range': (-150000, 200000), 'y_range': (-150000, 150000), 'name': '東京（本州・伊豆諸島）'},
            10: {'x_range': (-150000, 150000), 'y_range': (-150000, 150000), 'name': '青森・秋田・山形・福島・群馬・栃木・茨城・埼玉・千葉・神奈川'},
            11: {'x_range': (-150000, 150000), 'y_range': (-150000, 150000), 'name': '北海道（小樽・岩見沢）'},
            12: {'x_range': (-150000, 150000), 'y_range': (-150000, 150000), 'name': '北海道（北見・網走）'},
            13: {'x_range': (-150000, 150000), 'y_range': (-150000, 150000), 'name': '北海道（釧路・根室）'},
            14: {'x_range': (-200000, 200000), 'y_range': (-200000, 200000), 'name': '東京（南方諸島）'},
            15: {'x_range': (-150000, 150000), 'y_range': (-150000, 150000), 'name': '沖縄（南西諸島西部）'},
            16: {'x_range': (-150000, 150000), 'y_range': (-150000, 150000), 'name': '沖縄（南西諸島東部）'},
            17: {'x_range': (-150000, 150000), 'y_range': (-150000, 150000), 'name': '未使用'},
            18: {'x_range': (-200000, 200000), 'y_range': (-200000, 200000), 'name': '東京（小笠原諸島）'},
            19: {'x_range': (-150000, 150000), 'y_range': (-150000, 150000), 'name': '沖縄（南大東島・北大東島）'},
        }
        
        # 座標値から系を推定
        candidates = []
        for system_num, ranges in system_ranges.items():
            if (ranges['x_range'][0] <= avg_x <= ranges['x_range'][1] and
                ranges['y_range'][0] <= avg_y <= ranges['y_range'][1]):
                candidates.append((system_num, ranges['name']))
        
        if candidates:
            # 複数候補がある場合は最初の候補を返す
            detected_system, region_name = candidates[0]
            print(f"座標系を推定: {detected_system}系（{region_name}）")
            if len(candidates) > 1:
                print(f"他の候補: {', '.join([f'{s}系（{n}）' for s, n in candidates[1:]])}")
            return detected_system
        
        print("座標系の自動推定ができませんでした")
        return None
    
    def parse_d00_landparcel(self, lines, start_index):
        """D00形式の地番データを解析（B01点番からA01座標を参照）
        
        D00形式:
        D00,種別,地番名,点数,...
        B01,点番,点名,（座標はA01セクションを参照）
        C03,距離,方向角,
        B01,点番,点名,
        ...
        D99（終了タグ）
        
        返り値: (landparcel_info, lines_processed)
        """
        line = lines[start_index].strip()
        parts = line.split(',')
        
        if len(parts) < 4:
            print(f"D00行のフィールド数不足: {line}")
            return None, 0
        
        try:
            # D00のフィールド
            # parts[0] = "D00"
            # parts[1] = 種別番号または区分
            # parts[2] = 地番名
            # parts[3] = 画地番号（点数ではない）
            landparcel_type = parts[1].strip() if len(parts) > 1 else ""
            landparcel_name = parts[2].strip()
            
            print(f"D00解析開始: 地番={landparcel_name}, 種別={landparcel_type}")
            
            # A01測量点データから座標を検索するための辞書を作成
            point_coord_map = {}
            for point in self.sim_points:
                point_coord_map[point['点番']] = (point['X座標'], point['Y座標'])
                if point['点名']:
                    point_coord_map[point['点名']] = (point['X座標'], point['Y座標'])
            
            # B01行から点番を読み取り、A01座標を参照
            # D99が来るまでまたは次のD00が来るまで全てのB01を収集
            coordinates = []
            i = start_index + 1
            
            while i < len(lines):
                b01_line = lines[i].strip()
                
                # 空行はスキップ
                if not b01_line:
                    i += 1
                    continue
                
                # D99で終了
                if b01_line.startswith('D99'):
                    print(f"D99終了タグ検出: {len(coordinates)}点収集")
                    break
                
                # 次のD00が来たら終了
                if b01_line.startswith('D00'):
                    print(f"次のD00検出: {len(coordinates)}点収集")
                    break
                
                # B01行を解析（点番と点名のみ、座標はA01から参照）
                if b01_line.startswith('B01'):
                    b01_parts = b01_line.split(',')
                    
                    # B01フィールド（このSIMファイルの形式）
                    # parts[0] = "B01"
                    # parts[1] = 点番
                    # parts[2] = 点名
                    # ※座標データはなし、A01セクションから参照
                    
                    if len(b01_parts) >= 2:
                        try:
                            point_num = b01_parts[1].strip()
                            point_name = b01_parts[2].strip() if len(b01_parts) > 2 else ""
                            
                            # A01座標データから該当する点の座標を検索
                            coord = None
                            
                            # 点番で検索
                            if point_num in point_coord_map:
                                coord = point_coord_map[point_num]
                            # 点名で検索
                            elif point_name and point_name in point_coord_map:
                                coord = point_coord_map[point_name]
                            
                            if coord:
                                x, y = coord
                                coordinates.append((x, y))
                                
                                # デバッグ情報（最初の3点と最後の1点のみ）
                                if len(coordinates) <= 3:
                                    print(f"  B01[{len(coordinates)}]: 点番={point_num}, 点名={point_name}, X={x:.2f}, Y={y:.2f}")
                            else:
                                print(f"警告: B01点番={point_num}, 点名={point_name} の座標がA01に見つかりません")
                            
                        except (ValueError, IndexError) as e:
                            print(f"B01解析エラー: {b01_line}\n{e}")
                    else:
                        print(f"B01フィールド数不足: {b01_line} (必要:2以上, 実際:{len(b01_parts)})")
                
                # C03行（距離・方向角）はスキップ
                elif b01_line.startswith('C03'):
                    pass  # 結線情報なのでスキップ
                
                i += 1
            
            # 処理した行数を計算
            lines_processed = i - start_index
            
            # 最後の点のデバッグ情報
            if len(coordinates) > 3:
                print(f"  ... ({len(coordinates) - 3}点省略)")
                # 最後の点を表示
                if coordinates:
                    last_coord = coordinates[-1]
                    print(f"  B01[{len(coordinates)}]: X={last_coord[0]:.2f}, Y={last_coord[1]:.2f}")
            
            if coordinates and len(coordinates) >= 3:
                print(f"D00解析成功: 地番={landparcel_name}, {len(coordinates)}点, {lines_processed}行処理")
                return ({
                    '地番': landparcel_name,
                    '種別': landparcel_type,
                    '座標': coordinates,
                    '点数': len(coordinates)
                }, lines_processed)
            else:
                print(f"D00解析失敗: 座標が不足（{len(coordinates)}点、最低3点必要）")
                return None, lines_processed
                
        except (ValueError, IndexError) as e:
            print(f"D00解析エラー: {line}\n{e}\n{traceback.format_exc()}")
        
        return None, 0
    
    def load_photo_folder(self):
        """写真フォルダの読み込み"""
        folder_path = filedialog.askdirectory(title="写真フォルダを選択")
        
        if not folder_path:
            return
        
        self.photo_directory.set(folder_path)
        self.status_label.config(text=f"写真読み込み中: {folder_path}")
        
        try:
            self.load_photos(folder_path)
            self.update_map()
            self.status_label.config(text=f"写真読み込み完了: {len(self.photo_gps_data)}枚")
            messagebox.showinfo("成功", f"{len(self.photo_gps_data)}枚の写真を読み込みました")
        except Exception as e:
            self.status_label.config(text="写真読み込み失敗")
            messagebox.showerror("エラー", f"写真の読み込みに失敗しました:\n{str(e)}")
            print(f"写真読み込みエラー:\n{traceback.format_exc()}")
    
    def load_photos(self, folder_path):
        """写真フォルダから写真情報を読み込む"""
        self.photo_gps_data = {}
        
        # TreeViewをクリア
        for item in self.photos_tree.get_children():
            self.photos_tree.delete(item)
        
        # 写真ファイルを検索
        photo_extensions = ['.jpg', '.jpeg', '.png', '.tif', '.tiff']
        photo_files = []
        
        for file in os.listdir(folder_path):
            if any(file.lower().endswith(ext) for ext in photo_extensions):
                photo_files.append(file)
        
        for photo_file in photo_files:
            photo_path = os.path.join(folder_path, photo_file)
            
            try:
                # EXIF情報取得
                exif_data = self.extract_exif_data(photo_path)
                
                # 元の座標を保存（後で復元用）
                if 'x_coord' in exif_data and 'y_coord' in exif_data:
                    exif_data['original_x_coord'] = exif_data['x_coord']
                    exif_data['original_y_coord'] = exif_data['y_coord']
                
                self.photo_gps_data[photo_file] = exif_data
                
                # TreeViewに追加
                self.photos_tree.insert('', tk.END, values=(
                    photo_file,  # 元ファイル名
                    "",  # 新ファイル名
                    exif_data.get('datetime', ''),  # 撮影日時
                    "不明",  # 遠景/近景
                    f"{exif_data.get('x_coord', 0):.3f}" if exif_data.get('x_coord') else "",  # X座標
                    f"{exif_data.get('y_coord', 0):.3f}" if exif_data.get('y_coord') else "",  # Y座標
                    "",  # マッチングポイント
                    ""  # 距離
                ))
            except Exception as e:
                print(f"写真 {photo_file} の読み込みエラー: {e}")
        
        print(f"{len(self.photo_gps_data)}枚の写真を読み込みました")
    
    def extract_exif_data(self, photo_path):
        """写真からEXIF/GPS情報を抽出"""
        exif_data = {}
        
        try:
            # PILでEXIF取得
            img = Image.open(photo_path)
            exif = img._getexif()
            
            if exif:
                # 撮影日時
                for tag_id, value in exif.items():
                    tag = ExifTags.TAGS.get(tag_id, tag_id)
                    if tag == 'DateTime':
                        exif_data['datetime'] = value
                    elif tag == 'GPSInfo':
                        gps_info = value
                        if gps_info:
                            lat = self.get_decimal_coordinates(gps_info.get(2), gps_info.get(1))
                            lon = self.get_decimal_coordinates(gps_info.get(4), gps_info.get(3))
                            
                            if lat and lon:
                                exif_data['lat'] = lat
                                exif_data['lon'] = lon
                                
                                # GPS変換が有効な場合のみ座標変換
                                if self.use_gps_conversion.get():
                                    try:
                                        # 選択された系に基づいてEPSGコードを計算
                                        # EPSG:6669～6687（1系～19系）
                                        epsg_code = 6668 + self.coordinate_system.get()
                                        
                                        transformer = Transformer.from_crs(
                                            "EPSG:4326", 
                                            f"EPSG:{epsg_code}", 
                                            always_xy=True
                                        )
                                        y, x = transformer.transform(lon, lat)
                                        exif_data['x_coord'] = x
                                        exif_data['y_coord'] = y
                                        print(f"GPS座標変換: ({lat:.6f}, {lon:.6f}) → ({x:.3f}, {y:.3f}) [{epsg_code}系]")
                                    except Exception as e:
                                        print(f"座標変換エラー: {e}")
                                else:
                                    print(f"GPS変換無効: 緯度={lat:.6f}, 経度={lon:.6f} （平面直角座標への変換をスキップ）")
        except Exception as e:
            print(f"EXIF読み込みエラー ({photo_path}): {e}")
        
        return exif_data
    
    def get_decimal_coordinates(self, coords, ref):
        """GPS座標をDMS形式から10進数に変換"""
        if not coords:
            return None
        
        try:
            degrees = float(coords[0])
            minutes = float(coords[1])
            seconds = float(coords[2])
            
            decimal = degrees + (minutes / 60.0) + (seconds / 3600.0)
            
            if ref in ['S', 'W']:
                decimal = -decimal
            
            return decimal
        except (TypeError, ValueError, IndexError):
            return None
    
    def update_map(self):
        """地図を更新して表示"""
        # 既存の図をクリア
        if self.canvas:
            self.canvas.get_tk_widget().destroy()
        
        # 新しい図を作成
        self.figure = Figure(figsize=(8, 6))
        self.ax = self.figure.add_subplot(111)
        
        # 測量点をプロット
        if self.sim_points:
            x_coords = [p['X座標'] for p in self.sim_points]
            y_coords = [p['Y座標'] for p in self.sim_points]
            
            # 測量座標系：X軸=北（縦）、Y軸=東（横）→ 表示はY(横)とX(縦)を入れ替える
            self.ax.scatter(y_coords, x_coords, c='blue', marker='o', s=50, label='測量点', zorder=3)
            
            # 点名表示
            for point in self.sim_points:
                label = point['点名'] if point['点名'] else point['点番']
                self.ax.annotate(label, (point['Y座標'], point['X座標']), 
                               fontsize=8, ha='left', va='bottom')
        
        # 地番（筆界）をプロット（修正版）
        if self.landparcel_data:
            first_landparcel = True
            
            for landparcel in self.landparcel_data:
                coords = landparcel['座標']
                if coords and len(coords) >= 3:
                    # 多角形を閉じる（既に閉じていない場合）
                    if coords[0] != coords[-1]:
                        coords_closed = coords + [coords[0]]
                    else:
                        coords_closed = coords
                    
                    # Y座標（東）を横軸、X座標（北）を縦軸に
                    y_coords = [c[1] for c in coords_closed]
                    x_coords = [c[0] for c in coords_closed]
                    
                    label = '地番境界' if first_landparcel else None
                    
                    # ポリゴン塗りつぶし
                    self.ax.fill(y_coords, x_coords, color='lightgreen', alpha=0.15, zorder=1)
                    
                    # 境界線描画
                    self.ax.plot(y_coords, x_coords, 'g-', linewidth=1.5, 
                               label=label, alpha=0.7, zorder=2)
                    
                    # 地番名を中央に表示
                    if len(y_coords) > 1:
                        center_y = sum(y_coords[:-1]) / (len(y_coords) - 1)
                        center_x = sum(x_coords[:-1]) / (len(x_coords) - 1)
                        
                        self.ax.annotate(
                            landparcel['地番'],
                            (center_y, center_x),
                            fontsize=9,
                            ha='center',
                            va='center',
                            bbox=dict(boxstyle="round,pad=0.4", fc="white", ec="green", alpha=0.8),
                            zorder=3
                        )
                    
                    first_landparcel = False
        
        # 写真位置をプロット（ピック可能に）
        self.photo_scatter = None
        photo_data = []
        
        # TreeViewから新ファイル名を取得するためのマッピングを作成
        new_filename_map = {}
        for item_id in self.photos_tree.get_children():
            values = self.photos_tree.item(item_id)['values']
            original_name = values[0]
            new_name = values[1]
            if new_name:  # 新ファイル名がある場合のみ
                new_filename_map[original_name] = new_name
        
        for photo_name, data in self.photo_gps_data.items():
            if 'x_coord' in data and 'y_coord' in data:
                photo_data.append({
                    'name': photo_name,
                    'x': data['x_coord'],
                    'y': data['y_coord'],
                    'new_name': new_filename_map.get(photo_name, "")  # 新ファイル名を追加
                })
        
        if photo_data:
            photo_y = [p['y'] for p in photo_data]
            photo_x = [p['x'] for p in photo_data]
            
            # picker=15でクリック検出範囲を15ピクセルに設定（クリックしやすく）
            self.photo_scatter = self.ax.scatter(
                photo_y, photo_x, 
                c='red', marker='x', s=100, 
                label='写真', zorder=4,
                picker=15
            )
            
            # 新ファイル名のラベルを表示
            for photo in photo_data:
                if photo['new_name']:  # 新ファイル名がある場合のみ表示
                    self.ax.text(photo['y'], photo['x'], f"  {photo['new_name']}", 
                               fontsize=8, color='red',
                               verticalalignment='center', horizontalalignment='left',
                               bbox=dict(boxstyle='round,pad=0.3', facecolor='white', 
                                       edgecolor='red', alpha=0.7), zorder=5)
            
            # 写真データを保存（ドラッグ用）
            self.photo_points = photo_data
        
        # 軸ラベル
        self.ax.set_xlabel('Y座標 (東)', fontsize=10)
        self.ax.set_ylabel('X座標 (北)', fontsize=10)
        self.ax.set_title('測量点・写真配置図', fontsize=12)
        
        self.ax.grid(True, alpha=0.3)
        self.ax.legend()
        self.ax.set_aspect('equal', adjustable='datalim')
        
        # 初期表示範囲を保存（初回のみ）
        if self.initial_xlim is None and self.initial_ylim is None:
            self.initial_xlim = self.ax.get_xlim()
            self.initial_ylim = self.ax.get_ylim()
        
        # ズーム状態を保存
        if self.current_xlim and self.current_ylim:
            self.ax.set_xlim(self.current_xlim)
            self.ax.set_ylim(self.current_ylim)
        
        # キャンバスに描画
        self.canvas = FigureCanvasTkAgg(self.figure, self.map_frame)
        self.canvas.draw()
        self.canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        
        # イベントハンドラー設定
        self.canvas.mpl_connect('button_press_event', self.on_map_click)
        self.canvas.mpl_connect('button_release_event', self.on_map_release)
        self.canvas.mpl_connect('motion_notify_event', self.on_map_motion)
        self.canvas.mpl_connect('scroll_event', self.on_map_scroll)
        self.canvas.mpl_connect('pick_event', self.on_photo_pick)  # 写真クリック検出
    
    def update_map_light(self):
        """地図を軽量更新（ズーム状態を保持）"""
        print(f"\n[DEBUG] ==== update_map_light開始 ====")
        if not self.ax:
            self.update_map()
            return
        
        # 現在のズーム状態を保存
        self.current_xlim = self.ax.get_xlim()
        self.current_ylim = self.ax.get_ylim()
        print(f"[DEBUG] ズーム状態保存: xlim={self.current_xlim}, ylim={self.current_ylim}")
        
        # 既存のマーカーをクリア（測量点と地番境界は残す）
        for artist in self.ax.get_children():
            if hasattr(artist, 'get_label'):
                label = artist.get_label()
                # 写真マーカー（×印）のみ削除
                if hasattr(artist, 'get_facecolors'):
                    try:
                        colors = artist.get_facecolors()
                        if len(colors) > 0:
                            # 青（測量点）と緑（地番境界）以外を削除
                            is_survey_point = np.allclose(colors[0][:3], [0, 0, 1], atol=0.1)  # 青
                            is_landparcel = False
                            if hasattr(artist, 'get_edgecolors'):
                                edge_colors = artist.get_edgecolors()
                                if len(edge_colors) > 0:
                                    is_landparcel = np.allclose(edge_colors[0][:3], [0, 0.5, 0], atol=0.1)  # 緑
                            
                            if not is_survey_point and not is_landparcel:
                                artist.remove()
                    except:
                        pass
        
        # 写真位置を再プロット
        photo_x = []
        photo_y = []
        photo_labels = []  # 新ファイル名のラベル
        photo_landscapes = []  # 遠景/近景の情報
        
        # TreeViewから新ファイル名と遠景/近景情報を取得するためのマッピングを作成
        new_filename_map = {}
        landscape_map = {}
        for item_id in self.photos_tree.get_children():
            values = self.photos_tree.item(item_id)['values']
            original_name = values[0]
            new_name = values[1]
            landscape = values[3]  # 遠景/近景
            if new_name:  # 新ファイル名がある場合のみ
                new_filename_map[original_name] = new_name
                landscape_map[original_name] = landscape
        
        print(f"[DEBUG] photo_gps_dataのエントリ数: {len(self.photo_gps_data)}")
        for photo_name, data in self.photo_gps_data.items():
            if 'x_coord' in data and 'y_coord' in data:
                photo_x.append(data['x_coord'])
                photo_y.append(data['y_coord'])
                
                # 新ファイル名を取得（なければ空文字）
                new_name = new_filename_map.get(photo_name, "")
                landscape = landscape_map.get(photo_name, "")
                photo_labels.append(new_name)
                photo_landscapes.append(landscape)
                
                print(f"[DEBUG] 写真プロット: {photo_name} → X={data['x_coord']:.2f}, Y={data['y_coord']:.2f}, 新ファイル名={new_name}, 景観={landscape}")
        
        print(f"[DEBUG] プロットする写真数: {len(photo_x)}件")
        if photo_x and photo_y:
            self.ax.scatter(photo_y, photo_x, c='red', marker='x', s=100, label='写真', zorder=4)
            
            # 新ファイル名のラベルを表示（遠景/近景で色分け）
            for i, (y, x, label, landscape) in enumerate(zip(photo_y, photo_x, photo_labels, photo_landscapes)):
                if label:  # 新ファイル名がある場合のみ表示
                    # 遠景/近景で色を変える
                    if landscape == "遠景":
                        label_text = f'  [遠] {label}'
                        edge_color = 'blue'
                        text_color = 'blue'
                    elif landscape == "近景":
                        label_text = f'  [近] {label}'
                        edge_color = 'red'
                        text_color = 'red'
                    else:
                        label_text = f'  {label}'
                        edge_color = 'gray'
                        text_color = 'gray'
                    
                    self.ax.text(y, x, label_text, fontsize=8, color=text_color, 
                               verticalalignment='center', horizontalalignment='left',
                               bbox=dict(boxstyle='round,pad=0.3', facecolor='white', 
                                       edgecolor=edge_color, alpha=0.7), zorder=5)
            
            print(f"[DEBUG] 写真マーカーとラベルをプロットしました")
        
        # ズーム状態を復元
        self.ax.set_xlim(self.current_xlim)
        self.ax.set_ylim(self.current_ylim)
        print(f"[DEBUG] ズーム状態復元完了")
        
        # 再描画
        self.canvas.draw()
        print(f"[DEBUG] ==== update_map_light終了 ====\n")
    
    def on_map_click(self, event):
        """地図クリックイベント"""
        print(f"[DEBUG] on_map_click: button={event.button}, xdata={event.xdata}, ydata={event.ydata}")
        
        if event.button == 1:  # 左クリック
            # ドラッグ開始チェック（写真選択状態）
            selected_items = self.photos_tree.selection()
            print(f"[DEBUG] 選択された写真: {len(selected_items)}件")
            print(f"[DEBUG] ドラッグモード: {self.drag_mode.get()} (1=リスト, 2=配置図)")
            
            # ドラッグモードが写真リスト(1)の場合
            if selected_items and self.drag_mode.get() == 1:
                photo_name = self.photos_tree.item(selected_items[0])['values'][0]
                
                # 既存のドラッグカーソルを削除
                if hasattr(self, 'drag_cursor_line') and self.drag_cursor_line:
                    try:
                        self.drag_cursor_line.remove()
                        self.canvas.draw_idle()
                        print("[DEBUG] 前回のドラッグカーソルを削除しました")
                    except:
                        pass
                    self.drag_cursor_line = None
                
                self.dragging_photo = photo_name
                self.drag_start_x = event.xdata
                self.drag_start_y = event.ydata
                print(f"[SUCCESS] 写真リストからドラッグ開始: {self.dragging_photo}")
                print(f"[DEBUG] ドラッグ開始座標: x={self.drag_start_x}, y={self.drag_start_y}")
            
            # ドラッグモードが配置図(2)の場合、クリック位置の近くに写真があるかチェック
            elif self.drag_mode.get() == 2 and event.xdata and event.ydata:
                print("[DEBUG] 配置図ドラッグモード: クリック位置近くの写真を探索")
                
                if hasattr(self, 'photo_points') and self.photo_points:
                    # クリック位置に最も近い写真を探す
                    min_distance = float('inf')
                    closest_photo = None
                    
                    # ピクセル単位での距離を計算（画面上での距離）
                    click_display = self.ax.transData.transform((event.xdata, event.ydata))
                    
                    for photo in self.photo_points:
                        # 写真の座標をピクセルに変換
                        photo_display = self.ax.transData.transform((photo['y'], photo['x']))
                        
                        # ピクセル距離を計算
                        pixel_dist = math.sqrt(
                            (click_display[0] - photo_display[0])**2 + 
                            (click_display[1] - photo_display[1])**2
                        )
                        
                        if pixel_dist < min_distance:
                            min_distance = pixel_dist
                            closest_photo = photo
                    
                    # 30ピクセル以内の写真を選択
                    if closest_photo and min_distance < 30:
                        print(f"[DEBUG] 写真発見: {closest_photo['name']} (距離: {min_distance:.1f}ピクセル)")
                        
                        # 既存のドラッグカーソルを削除
                        if hasattr(self, 'drag_cursor_line') and self.drag_cursor_line:
                            try:
                                self.drag_cursor_line.remove()
                                self.canvas.draw_idle()
                            except:
                                pass
                            self.drag_cursor_line = None
                        
                        # ドラッグ開始
                        self.dragging_photo = closest_photo['name']
                        self.drag_start_x = event.xdata
                        self.drag_start_y = event.ydata
                        print(f"[SUCCESS] 配置図の写真からドラッグ開始: {self.dragging_photo}")
                        print(f"[DEBUG] ドラッグ開始座標: x={self.drag_start_x}, y={self.drag_start_y}")
                    else:
                        print(f"[INFO] クリック位置に写真なし (最短距離: {min_distance:.1f}ピクセル)")
                else:
                    print("[INFO] 配置済み写真がありません")
            else:
                print("[INFO] 写真が選択されていません")
        
        elif event.button == 3:  # 右クリック
            print("[DEBUG] 右クリックパン開始")
            # パン開始
            self.panning = True
            self.pan_start_x = event.xdata
            self.pan_start_y = event.ydata
            # ディスプレイ座標（ピクセル）も保存
            if event.xdata is not None and event.ydata is not None:
                self.pan_start_display = self.ax.transData.transform((event.xdata, event.ydata))
    
    def on_map_release(self, event):
        """地図でマウスボタンを離した時の処理"""
        print(f"[DEBUG] on_map_release: button={event.button}, dragging_photo={getattr(self, 'dragging_photo', None)}")
        print(f"[DEBUG] ドロップ座標: xdata={event.xdata}, ydata={event.ydata}")
        
        if event.button == 1 and self.dragging_photo:  # 左クリック離し
            print(f"[SUCCESS] ドラッグ終了: {self.dragging_photo}")
            
            # ドラッグ距離を計算
            if event.xdata and event.ydata and self.drag_start_x and self.drag_start_y:
                drag_distance = math.sqrt(
                    (event.xdata - self.drag_start_x)**2 + 
                    (event.ydata - self.drag_start_y)**2
                )
                print(f"[DEBUG] ドラッグ距離: {drag_distance:.2f}m")
                print(f"[DEBUG] 開始: ({self.drag_start_x:.2f}, {self.drag_start_y:.2f})")
                print(f"[DEBUG] 終了: ({event.xdata:.2f}, {event.ydata:.2f})")
            
            # ドラッグカーソルを削除
            if hasattr(self, 'drag_cursor_line') and self.drag_cursor_line:
                try:
                    self.drag_cursor_line.remove()
                    self.canvas.draw_idle()
                except:
                    pass
                self.drag_cursor_line = None
            
            # ドラッグ中の写真名を保存（ダイアログで使用）
            dragging_photo_name = self.dragging_photo
            
            # ドラッグ&ドロップ完了
            if event.xdata and event.ydata:
                # 最も近い測量点を探す
                min_distance = float('inf')
                matched_point = None
                
                # 座標系変換：表示座標(Y, X) → 測量座標(X, Y)
                drop_x = event.ydata
                drop_y = event.xdata
                
                for point in self.sim_points:
                    distance = math.sqrt((point['X座標'] - drop_x) ** 2 + 
                                       (point['Y座標'] - drop_y) ** 2)
                    if distance < min_distance:
                        min_distance = distance
                        matched_point = point
                
                # ドラッグ状態を先にリセット（ダイアログ表示前）
                self.dragging_photo = None
                self.drag_start_x = None
                self.drag_start_y = None
                print("ドラッグ状態をリセットしました")
                
                if matched_point and min_distance < 50:  # 50m以内
                    print(f"マッチング成功: {matched_point['点名']} (距離: {min_distance:.2f}m)")
                    # 遠景/近景選択ダイアログ
                    self.show_landscape_dialog(dragging_photo_name, matched_point, min_distance)
                else:
                    print(f"マッチング失敗: 最短距離 {min_distance:.2f}m (50m以内の点がありません)")
            else:
                # マウスが地図外で離された場合
                self.dragging_photo = None
                self.drag_start_x = None
                self.drag_start_y = None
                print("地図外でドロップ、ドラッグ状態をリセット")
        
        elif event.button == 3:  # 右クリック離し
            self.panning = False
            self.pan_start_x = None
            self.pan_start_y = None
    
    def on_map_motion(self, event):
        """地図上でマウス移動（パン操作 + ドラッグ + マウスオーバープレビュー）"""
        # パン操作中（右クリックドラッグ）
        if self.panning:
            if event.xdata is not None and event.ydata is not None and \
               hasattr(self, 'pan_start_display'):
                # 現在のマウス位置をディスプレイ座標に変換
                current_display = self.ax.transData.transform((event.xdata, event.ydata))
                
                # ディスプレイ座標での移動量（ピクセル）
                dx_display = current_display[0] - self.pan_start_display[0]
                dy_display = current_display[1] - self.pan_start_display[1]
                
                # 現在の表示範囲を取得
                xlim = self.ax.get_xlim()
                ylim = self.ax.get_ylim()
                
                # 表示範囲の四隅をディスプレイ座標に変換
                disp_xlim = self.ax.transData.transform([(xlim[0], ylim[0]), (xlim[1], ylim[1])])
                
                # ディスプレイ座標で移動
                new_disp_xlim = [
                    [disp_xlim[0][0] + dx_display, disp_xlim[0][1] + dy_display],
                    [disp_xlim[1][0] + dx_display, disp_xlim[1][1] + dy_display]
                ]
                
                # ディスプレイ座標からデータ座標に変換
                new_data_lim = self.ax.transData.inverted().transform(new_disp_xlim)
                
                self.ax.set_xlim(new_data_lim[0][0], new_data_lim[1][0])
                self.ax.set_ylim(new_data_lim[0][1], new_data_lim[1][1])
                
                # 移動後の開始位置を更新
                self.pan_start_display = current_display
                
                # キャンバスを更新
                self.canvas.draw()
            return
        
        # 写真ドラッグ中（左クリックドラッグ）
        if self.dragging_photo:
            # 初回のみログ出力（頻繁なログを避ける）
            if not hasattr(self, '_drag_motion_logged'):
                print(f"[DEBUG] ドラッグ中: {self.dragging_photo}, x={event.xdata}, y={event.ydata}")
                self._drag_motion_logged = True
            
            self.hide_hover_preview()
            
            # ドラッグ中の視覚フィードバック：現在位置にカーソル表示
            if event.xdata and event.ydata:
                # 既存のカーソルを削除
                if hasattr(self, 'drag_cursor_line') and self.drag_cursor_line:
                    try:
                        self.drag_cursor_line.remove()
                    except:
                        pass
                
                # 新しいカーソルを描画（十字）
                self.drag_cursor_line = self.ax.plot(
                    [event.xdata], [event.ydata], 
                    'r+', markersize=15, markeredgewidth=2
                )[0]
                self.canvas.draw_idle()
                
                # カーソル描画確認（初回のみ）
                if not hasattr(self, '_cursor_drawn_logged'):
                    print(f"[DEBUG] 赤い十字カーソルを描画しました: ({event.xdata:.2f}, {event.ydata:.2f})")
                    self._cursor_drawn_logged = True
            
            return
        else:
            # ドラッグ中でない場合はフラグをリセット
            if hasattr(self, '_drag_motion_logged'):
                del self._drag_motion_logged
            if hasattr(self, '_cursor_drawn_logged'):
                del self._cursor_drawn_logged
        
        # マウスオーバープレビュー
        if event.inaxes == self.ax and event.xdata and event.ydata:
            self.show_hover_preview(event)
        else:
            self.hide_hover_preview()
    
    def on_map_scroll(self, event):
        """マウスホイールでズーム"""
        if event.xdata and event.ydata:
            scale_factor = 1.1 if event.button == 'down' else 0.9
            
            xlim = self.ax.get_xlim()
            ylim = self.ax.get_ylim()
            
            xdata = event.xdata
            ydata = event.ydata
            
            new_xlim = [xdata - (xdata - xlim[0]) * scale_factor,
                        xdata + (xlim[1] - xdata) * scale_factor]
            new_ylim = [ydata - (ydata - ylim[0]) * scale_factor,
                        ydata + (ylim[1] - ydata) * scale_factor]
            
            self.ax.set_xlim(new_xlim)
            self.ax.set_ylim(new_ylim)
            
            self.canvas.draw()
    
    def show_hover_preview(self, event):
        """マウスオーバーで写真プレビュー表示"""
        if not hasattr(self, 'photo_points') or not self.photo_points:
            return
        
        # マウスに最も近い写真を探す
        min_dist = 20  # ピクセル単位
        closest_photo = None
        
        for photo in self.photo_points:
            # データ座標 → ディスプレイ座標
            display_x, display_y = self.ax.transData.transform((photo['y'], photo['x']))
            mouse_x, mouse_y = self.ax.transData.transform((event.xdata, event.ydata))
            
            dist = math.sqrt((display_x - mouse_x)**2 + (display_y - mouse_y)**2)
            
            if dist < min_dist:
                min_dist = dist
                closest_photo = photo
        
        # 前回と同じ写真ならスキップ
        if hasattr(self, 'last_hover_photo') and closest_photo and \
           self.last_hover_photo == closest_photo['name']:
            return
        
        # プレビュー更新
        if closest_photo:
            self.last_hover_photo = closest_photo['name']
            self.display_hover_window(closest_photo['name'], event)
        else:
            self.hide_hover_preview()
    
    def display_hover_window(self, photo_name, event):
        """ホバー用の小さなプレビューウィンドウを表示"""
        # 既存のウィンドウを閉じる
        if self.hover_window and self.hover_window.winfo_exists():
            self.hover_window.destroy()
        
        photo_path = os.path.join(self.photo_directory.get(), photo_name)
        
        if not os.path.exists(photo_path):
            return
        
        try:
            # 小さなプレビューウィンドウ
            self.hover_window = tk.Toplevel(self.root)
            self.hover_window.overrideredirect(True)  # タイトルバーなし
            self.hover_window.attributes('-topmost', True)
            
            # マウス位置から少しオフセット
            x, y = self.root.winfo_pointerxy()
            self.hover_window.geometry(f"+{x+15}+{y+15}")
            
            # 画像読み込み
            img = Image.open(photo_path)
            img.thumbnail((200, 150), Image.LANCZOS)
            
            from PIL import ImageTk
            photo = ImageTk.PhotoImage(img)
            
            # フレーム（境界線付き）
            frame = tk.Frame(self.hover_window, bg="black", padx=2, pady=2)
            frame.pack()
            
            label = tk.Label(frame, image=photo, bg="white")
            label.image = photo
            label.pack()
            
            # ファイル名表示
            name_label = tk.Label(frame, text=photo_name, bg="lightyellow", 
                                 font=("", 8))
            name_label.pack(fill=tk.X)
            
        except Exception as e:
            print(f"ホバープレビューエラー: {e}")
            if self.hover_window:
                self.hover_window.destroy()
                self.hover_window = None
    
    def hide_hover_preview(self):
        """ホバープレビューを非表示"""
        if hasattr(self, 'hover_annotation') and self.hover_annotation:
            self.hover_annotation.remove()
            self.hover_annotation = None
            self.canvas.draw_idle()
        
        if hasattr(self, 'hover_window') and self.hover_window and \
           self.hover_window.winfo_exists():
            self.hover_window.destroy()
            self.hover_window = None
        
        self.last_hover_photo = None
    
    def reset_map_view(self):
        """地図表示を測量図の初期位置に戻す"""
        if self.ax and self.initial_xlim and self.initial_ylim:
            self.ax.set_xlim(self.initial_xlim)
            self.ax.set_ylim(self.initial_ylim)
            self.canvas.draw()
            self.status_label.config(text="地図表示を初期位置に戻しました")
        else:
            messagebox.showinfo("情報", "地図がまだ表示されていません")
    
    def on_tree_motion(self, event):
        """写真リストでマウスが動いた時にプレビュー表示"""
        # マウス位置の行を特定
        item = self.photos_tree.identify_row(event.y)
        
        if not item:
            self.hide_tree_hover_preview()
            return
        
        # 行のデータを取得
        values = self.photos_tree.item(item, 'values')
        if not values:
            self.hide_tree_hover_preview()
            return
        
        photo_name = values[0]  # 元ファイル名
        
        # 前回と同じ写真ならスキップ
        if hasattr(self, 'last_tree_hover_photo') and \
           self.last_tree_hover_photo == photo_name:
            return
        
        # プレビュー表示
        self.last_tree_hover_photo = photo_name
        self.display_tree_hover_window(photo_name)
    
    def on_tree_leave(self, event):
        """写真リストからマウスが離れた時"""
        self.hide_tree_hover_preview()
    
    def display_tree_hover_window(self, photo_name):
        """写真リスト用のホバープレビューウィンドウを表示"""
        # 既存のウィンドウを閉じる
        if hasattr(self, 'tree_hover_window') and self.tree_hover_window and \
           self.tree_hover_window.winfo_exists():
            self.tree_hover_window.destroy()
        
        photo_path = os.path.join(self.photo_directory.get(), photo_name)
        
        if not os.path.exists(photo_path):
            return
        
        try:
            # 小さなプレビューウィンドウ
            self.tree_hover_window = tk.Toplevel(self.root)
            self.tree_hover_window.overrideredirect(True)  # タイトルバーなし
            self.tree_hover_window.attributes('-topmost', True)
            
            # マウス位置から少しオフセット
            x, y = self.root.winfo_pointerxy()
            self.tree_hover_window.geometry(f"+{x+15}+{y+15}")
            
            # 画像読み込み
            img = Image.open(photo_path)
            img.thumbnail((200, 150), Image.LANCZOS)
            
            from PIL import ImageTk
            photo = ImageTk.PhotoImage(img)
            
            # フレーム（境界線付き）
            frame = tk.Frame(self.tree_hover_window, bg="black", padx=2, pady=2)
            frame.pack()
            
            label = tk.Label(frame, image=photo, bg="white")
            label.image = photo
            label.pack()
            
            # ファイル名表示
            name_label = tk.Label(frame, text=photo_name, bg="lightyellow", 
                                 font=("", 8))
            name_label.pack(fill=tk.X)
            
        except Exception as e:
            print(f"写真リストホバープレビューエラー: {e}")
            if hasattr(self, 'tree_hover_window') and self.tree_hover_window:
                self.tree_hover_window.destroy()
                self.tree_hover_window = None
    
    def hide_tree_hover_preview(self):
        """写真リスト用のホバープレビューを非表示"""
        if hasattr(self, 'tree_hover_window') and self.tree_hover_window and \
           self.tree_hover_window.winfo_exists():
            self.tree_hover_window.destroy()
            self.tree_hover_window = None
        
        if hasattr(self, 'last_tree_hover_photo'):
            self.last_tree_hover_photo = None
    
    def on_photo_pick(self, event):
        """地図上の写真（×印）がクリックされた時"""
        print(f"[DEBUG] on_photo_pick: button={event.mouseevent.button}, ind={event.ind}")
        print(f"[DEBUG] ドラッグモード: {self.drag_mode.get()} (1=リスト, 2=配置図)")
        
        if event.mouseevent.button != 1:  # 左クリックのみ
            print("[INFO] 左クリック以外なので無視")
            return
        
        # ドラッグモードが配置図(2)の場合のみ処理
        if self.drag_mode.get() != 2:
            print("[INFO] 配置図からのドラッグモードが選択されていません")
            return
        
        # クリックされた写真を特定
        ind = event.ind[0]
        print(f"[DEBUG] photo_pointsの数: {len(self.photo_points) if hasattr(self, 'photo_points') else 0}")
        
        if hasattr(self, 'photo_points') and ind < len(self.photo_points):
            clicked_photo = self.photo_points[ind]
            print(f"[DEBUG] クリックされた写真: {clicked_photo}")
            
            # 既存のドラッグカーソルを削除
            if hasattr(self, 'drag_cursor_line') and self.drag_cursor_line:
                try:
                    self.drag_cursor_line.remove()
                    self.canvas.draw_idle()
                    print("[DEBUG] 前回のドラッグカーソルを削除しました")
                except:
                    pass
                self.drag_cursor_line = None
            
            # ドラッグ開始
            self.dragging_photo = clicked_photo['name']
            self.drag_start_x = event.mouseevent.xdata
            self.drag_start_y = event.mouseevent.ydata
            
            print(f"[SUCCESS] 地図上の写真（×）からドラッグ開始: {self.dragging_photo}")
            print(f"[DEBUG] ドラッグ開始座標: x={self.drag_start_x}, y={self.drag_start_y}")
            
            # ホバープレビューを非表示
            self.hide_hover_preview()
        else:
            print(f"[ERROR] photo_pointsが存在しないか、インデックスが範囲外です")
    
    def show_landscape_dialog(self, photo_name, matched_point, matched_point_distance):
        """遠景/近景選択ダイアログ"""
        photo_landscape = None
        
        # ダイアログ作成
        landscape_dialog = tk.Toplevel(self.root)
        landscape_dialog.title("遠景/近景の選択")
        landscape_dialog.geometry("450x280")
        landscape_dialog.transient(self.root)
        landscape_dialog.grab_set()
        
        ttk.Label(landscape_dialog, text=f"写真: {photo_name}", font=("", 10)).pack(pady=10)
        ttk.Label(landscape_dialog, text=f"測量点: {matched_point['点名']} ({matched_point['点番']})", 
                 font=("", 10)).pack(pady=5)
        ttk.Label(landscape_dialog, text=f"距離: {matched_point_distance:.1f}m", 
                 font=("", 10)).pack(pady=5)
        
        landscape_var = tk.StringVar(value="近景")
        is_special_point = tk.BooleanVar(value=False)
        
        # 基準点・引照点チェック
        point_name = matched_point.get('点名', '').strip()
        if '基準点' in point_name or '引照点' in point_name:
            is_special_point.set(True)
        
        ttk.Label(landscape_dialog, text="写真の種類を選択してください:", font=("", 10, "bold")).pack(pady=10)
        
        ttk.Radiobutton(landscape_dialog, text="遠景", variable=landscape_var, value="遠景").pack()
        ttk.Radiobutton(landscape_dialog, text="近景", variable=landscape_var, value="近景").pack()
        
        def confirm_landscape():
            nonlocal photo_landscape
            photo_landscape = landscape_var.get()
            is_special = is_special_point.get()
            
            landscape_dialog.destroy()
            
            # 識別子を設定
            if is_special:
                identifier = matched_point['点名']
            else:
                identifier = matched_point['点名'] if self.use_point_name.get() else matched_point['点番']
            
            # 新しいファイル名を生成（重複チェック付き）
            original_filename = photo_name
            new_filename = self.create_filename(identifier, original_filename, photo_landscape, matched_point)
            
            # TreeViewで写真を探して更新
            for item_id in self.photos_tree.get_children():
                values = self.photos_tree.item(item_id)['values']
                if values[0] == photo_name:
                    # データを更新
                    values = list(values)
                    values[1] = new_filename  # 新ファイル名
                    values[3] = photo_landscape  # 遠景/近景を更新
                    values[6] = identifier  # マッチングポイント
                    values[7] = f"{matched_point_distance:.1f}m"  # 距離
                    
                    self.photos_tree.item(item_id, values=values)
                    break
            
            # GPS座標も更新
            if photo_name in self.photo_gps_data:
                self.photo_gps_data[photo_name]['x_coord'] = matched_point['X座標']
                self.photo_gps_data[photo_name]['y_coord'] = matched_point['Y座標']
            
            # 地図を軽量更新
            self.update_map_light()
            
            # 通知
            messagebox.showinfo("マッチング成功", 
                              f"写真「{photo_name}」を測量点「{identifier}」にマッチングしました。\n"
                              f"新しいファイル名: {new_filename}")
        
        ttk.Button(landscape_dialog, text="OK", command=confirm_landscape).pack(pady=10)
        
        # ダイアログを中央に配置
        landscape_dialog.update_idletasks()
        x = (landscape_dialog.winfo_screenwidth() // 2) - (landscape_dialog.winfo_width() // 2)
        y = (landscape_dialog.winfo_screenheight() // 2) - (landscape_dialog.winfo_height() // 2)
        landscape_dialog.geometry(f"+{x}+{y}")
        
        landscape_dialog.focus_set()
        landscape_dialog.grab_set()
        landscape_dialog.wait_window()
    
    def create_filename(self, identifier, original_filename, landscape_type, point_data=None):
        """新しいファイル名を生成（新規写真が-1/-2、既存写真を通し番号に変更）"""
        print(f"\n[DEBUG] ==== create_filename開始 ====")
        print(f"[DEBUG] identifier: {identifier}")
        print(f"[DEBUG] original_filename: {original_filename}")
        print(f"[DEBUG] landscape_type: {landscape_type}")
        
        name, ext = os.path.splitext(original_filename)
        
        # 基準点・引照点かどうかをチェック
        is_special_point = False
        if point_data is not None and self.force_point_name_for_special.get():
            point_name = point_data.get('点名', '').strip()
            if '基準点' in point_name or '引照点' in point_name:
                is_special_point = True
                identifier = point_name
                print(f"[DEBUG] 基準点/引照点検出: identifier変更 → {identifier}")
        
        # 遠景/近景サフィックスを使用する場合
        if self.use_landscape_suffix.get():
            print(f"[DEBUG] 遠景/近景サフィックス使用モード")
            if landscape_type == "不明":
                landscape_type = "近景"
                print(f"[DEBUG] 景観タイプ不明 → 近景に設定")
            
            suffix = "-1" if landscape_type == "遠景" else "-2"
            base_filename = f"{identifier}{suffix}{ext}"
            print(f"[DEBUG] 基本ファイル名: {base_filename}")
            
            # 同じ測量点・同じ景観タイプの既存写真を収集
            existing_photos = []
            print(f"[DEBUG] 既存写真を収集中...")
            print(f"[DEBUG] 検索条件: identifier='{identifier}' (型:{type(identifier).__name__}), landscape_type='{landscape_type}'")
            
            for item_id in self.photos_tree.get_children():
                values = self.photos_tree.item(item_id)['values']
                current_original = values[0]
                current_new = values[1]
                current_matching = values[6]
                current_landscape = values[3]
                
                # デバッグ: 全エントリをチェック
                if current_new:  # 新ファイル名がある写真のみログ出力
                    print(f"[DEBUG] チェック: {current_original[:30]}... → new='{current_new}', match='{current_matching}' (型:{type(current_matching).__name__}), land='{current_landscape}'")
                
                # identifier を文字列に変換して比較
                identifier_str = str(identifier)
                current_matching_str = str(current_matching)
                
                # 現在処理中の写真は除外、同じ測量点・同じ景観タイプのみ
                match_check = (current_matching_str == identifier_str)
                landscape_check = (current_landscape == landscape_type)
                not_same_check = (current_original != original_filename)
                
                if current_new:  # 新ファイル名がある写真のみ詳細ログ
                    print(f"[DEBUG]   → マッチング一致: {match_check}, 景観一致: {landscape_check}, 別ファイル: {not_same_check}")
                
                if match_check and landscape_check and not_same_check:
                    existing_photos.append({
                        'item_id': item_id,
                        'original': current_original,
                        'new': current_new,
                        'values': values
                    })
                    print(f"[DEBUG] ★ 既存写真発見: {current_original} → {current_new}")
            
            # 既存写真がある場合、それらを通し番号に変更
            if existing_photos:
                print(f"[DEBUG] 既存写真数: {len(existing_photos)}件")
                # 使用済み番号を収集（予約番号含む）
                used_numbers = set([1, 2])  # -1, -2は予約
                print(f"[DEBUG] 初期予約番号: {used_numbers}")
                
                # 既存の通し番号を収集
                for photo in existing_photos:
                    match = re.search(rf'{re.escape(identifier)}_(\d+){re.escape(ext)}$', photo['new'])
                    if match:
                        num = int(match.group(1))
                        used_numbers.add(num)
                        print(f"[DEBUG] 通し番号検出: {photo['new']} → 番号{num}")
                
                # 既存写真の新ファイル名を削除（リネーム候補から除外）
                print(f"[DEBUG] 既存写真の重複チェック開始...")
                for photo in existing_photos:
                    print(f"[DEBUG] チェック中: 既存写真の新ファイル名='{photo['new']}', 基本形='{base_filename}'")
                    # 基本形の写真を見つけたら、新ファイル名を空白に設定
                    if photo['new'] == base_filename:
                        print(f"[DEBUG] ★★★ 重複発見! {photo['new']} と新規ファイル名 {base_filename} が衝突 ★★★")
                        print(f"[DEBUG] 既存写真の元ファイル名: {photo['original']}")
                        print(f"[DEBUG] 既存写真の新ファイル名を削除: {photo['new']} → (空白)")
                        
                        # 写真の座標を元に戻す
                        original_photo_name = photo['original']
                        print(f"[DEBUG] 座標復元処理開始: {original_photo_name}")
                        
                        if original_photo_name in self.photo_gps_data:
                            print(f"[DEBUG] photo_gps_dataに存在します")
                            gps_data = self.photo_gps_data[original_photo_name]
                            print(f"[DEBUG] GPS情報のキー: {list(gps_data.keys())}")
                            
                            if 'original_x_coord' in gps_data and 'original_y_coord' in gps_data:
                                old_x = gps_data.get('x_coord', 0)
                                old_y = gps_data.get('y_coord', 0)
                                original_x = gps_data['original_x_coord']
                                original_y = gps_data['original_y_coord']
                                
                                print(f"[DEBUG] 現在の座標: X={old_x:.2f}, Y={old_y:.2f}")
                                print(f"[DEBUG] 元の座標: X={original_x:.2f}, Y={original_y:.2f}")
                                
                                gps_data['x_coord'] = original_x
                                gps_data['y_coord'] = original_y
                                
                                print(f"[DEBUG] ★★★ 座標を元に戻しました: ({old_x:.2f}, {old_y:.2f}) → ({original_x:.2f}, {original_y:.2f}) ★★★")
                            else:
                                print(f"[DEBUG] ⚠️ 元の座標情報が存在しません")
                                print(f"[DEBUG] original_x_coord存在: {'original_x_coord' in gps_data}")
                                print(f"[DEBUG] original_y_coord存在: {'original_y_coord' in gps_data}")
                        else:
                            print(f"[DEBUG] ⚠️ photo_gps_dataに存在しません")
                        
                        # TreeViewのみ更新（新ファイル名を空白に設定、マッチング情報もクリア）
                        print(f"[DEBUG] TreeView更新処理開始...")
                        updated_values = list(photo['values'])
                        print(f"[DEBUG] 更新前のvalues: {updated_values}")
                        
                        updated_values[1] = ""  # 新ファイル名を空白に
                        updated_values[6] = ""  # マッチングポイントをクリア
                        updated_values[7] = ""  # 距離をクリア
                        
                        print(f"[DEBUG] 更新後のvalues: {updated_values}")
                        self.photos_tree.item(photo['item_id'], values=updated_values)
                        print(f"[DEBUG] ★★★ TreeView更新完了: item_id={photo['item_id']}, 新ファイル名=(空白), マッチング情報クリア ★★★")
                    else:
                        print(f"[DEBUG] 一致せず、スキップ")
            
            # 新しい写真は基本形
            print(f"[DEBUG] 新規写真のファイル名: {base_filename}")
            print(f"[DEBUG] ==== create_filename終了 ====\n")
            return base_filename
        
        else:
            # サフィックスを使用しない場合
            print(f"[DEBUG] 遠景/近景サフィックス未使用モード")
            base_filename = f"{identifier}{ext}"
            print(f"[DEBUG] 基本ファイル名: {base_filename}")
            
            existing_photos = []
            print(f"[DEBUG] 既存写真を収集中...")
            print(f"[DEBUG] 検索条件: identifier='{identifier}' (型:{type(identifier).__name__})")
            
            for item_id in self.photos_tree.get_children():
                values = self.photos_tree.item(item_id)['values']
                current_original = values[0]
                current_new = values[1]
                current_matching = values[6]
                
                # デバッグ: 全エントリをチェック
                if current_new:  # 新ファイル名がある写真のみログ出力
                    print(f"[DEBUG] チェック: {current_original[:30]}... → new='{current_new}', match='{current_matching}' (型:{type(current_matching).__name__})")
                
                # identifier を文字列に変換して比較
                identifier_str = str(identifier)
                current_matching_str = str(current_matching)
                
                match_check = (current_matching_str == identifier_str)
                not_same_check = (current_original != original_filename)
                
                if current_new:  # 新ファイル名がある写真のみ詳細ログ
                    print(f"[DEBUG]   → マッチング一致: {match_check}, 別ファイル: {not_same_check}")
                
                if match_check and not_same_check:
                    existing_photos.append({
                        'item_id': item_id,
                        'original': current_original,
                        'new': current_new,
                        'values': values
                    })
                    print(f"[DEBUG] ★ 既存写真発見: {current_original} → {current_new}")
            
            if existing_photos:
                print(f"[DEBUG] 既存写真数: {len(existing_photos)}件")
                used_numbers = set()
                
                for photo in existing_photos:
                    match = re.search(rf'{re.escape(identifier)}_(\d+){re.escape(ext)}$', photo['new'])
                    if match:
                        num = int(match.group(1))
                        used_numbers.add(num)
                        print(f"[DEBUG] 通し番号検出: {photo['new']} → 番号{num}")
                
                print(f"[DEBUG] 既存写真の重複チェック開始...")
                for photo in existing_photos:
                    print(f"[DEBUG] チェック中: 既存写真の新ファイル名='{photo['new']}', 基本形='{base_filename}'")
                    if photo['new'] == base_filename:
                        print(f"[DEBUG] ★★★ 重複発見! {photo['new']} と新規ファイル名 {base_filename} が衝突 ★★★")
                        print(f"[DEBUG] 既存写真の元ファイル名: {photo['original']}")
                        print(f"[DEBUG] 既存写真の新ファイル名を削除: {photo['new']} → (空白)")
                        
                        # 写真の座標を元に戻す
                        original_photo_name = photo['original']
                        print(f"[DEBUG] 座標復元処理開始: {original_photo_name}")
                        
                        if original_photo_name in self.photo_gps_data:
                            print(f"[DEBUG] photo_gps_dataに存在します")
                            gps_data = self.photo_gps_data[original_photo_name]
                            print(f"[DEBUG] GPS情報のキー: {list(gps_data.keys())}")
                            
                            if 'original_x_coord' in gps_data and 'original_y_coord' in gps_data:
                                old_x = gps_data.get('x_coord', 0)
                                old_y = gps_data.get('y_coord', 0)
                                original_x = gps_data['original_x_coord']
                                original_y = gps_data['original_y_coord']
                                
                                print(f"[DEBUG] 現在の座標: X={old_x:.2f}, Y={old_y:.2f}")
                                print(f"[DEBUG] 元の座標: X={original_x:.2f}, Y={original_y:.2f}")
                                
                                gps_data['x_coord'] = original_x
                                gps_data['y_coord'] = original_y
                                
                                print(f"[DEBUG] ★★★ 座標を元に戻しました: ({old_x:.2f}, {old_y:.2f}) → ({original_x:.2f}, {original_y:.2f}) ★★★")
                            else:
                                print(f"[DEBUG] ⚠️ 元の座標情報が存在しません")
                                print(f"[DEBUG] original_x_coord存在: {'original_x_coord' in gps_data}")
                                print(f"[DEBUG] original_y_coord存在: {'original_y_coord' in gps_data}")
                        else:
                            print(f"[DEBUG] ⚠️ photo_gps_dataに存在しません")
                        
                        # TreeViewのみ更新（新ファイル名を空白に設定、マッチング情報もクリア）
                        print(f"[DEBUG] TreeView更新処理開始...")
                        updated_values = list(photo['values'])
                        print(f"[DEBUG] 更新前のvalues: {updated_values}")
                        
                        updated_values[1] = ""  # 新ファイル名を空白に
                        updated_values[6] = ""  # マッチングポイントをクリア
                        updated_values[7] = ""  # 距離をクリア
                        
                        print(f"[DEBUG] 更新後のvalues: {updated_values}")
                        self.photos_tree.item(photo['item_id'], values=updated_values)
                        print(f"[DEBUG] ★★★ TreeView更新完了: item_id={photo['item_id']}, 新ファイル名=(空白), マッチング情報クリア ★★★")
                    else:
                        print(f"[DEBUG] 一致せず、スキップ")
            
            print(f"[DEBUG] 新規写真のファイル名: {base_filename}")
            print(f"[DEBUG] ==== create_filename終了 ====\n")
            return base_filename
    
    def show_photo_context_menu(self, event):
        """写真リストのコンテキストメニューを表示"""
        item = self.photos_tree.identify_row(event.y)
        if item:
            self.photos_tree.selection_set(item)
            
            context_menu = tk.Menu(self.root, tearoff=0)
            context_menu.add_command(label="プレビュー", command=self.preview_photo)
            context_menu.add_separator()
            context_menu.add_command(label="マッチングを編集", command=self.edit_photo_matching)
            context_menu.add_command(label="マッチングを解除", command=self.unmatch_photo)
            
            context_menu.post(event.x_root, event.y_root)
    
    def preview_photo(self, event=None):
        """写真をプレビュー表示（EXIF情報付き）"""
        selected_items = self.photos_tree.selection()
        if not selected_items:
            return
        
        values = self.photos_tree.item(selected_items[0])['values']
        photo_name = values[0]
        photo_path = os.path.join(self.photo_directory.get(), photo_name)
        
        if not os.path.exists(photo_path):
            messagebox.showerror("エラー", f"写真ファイルが見つかりません:\n{photo_path}")
            return
        
        try:
            # プレビューウィンドウ
            preview_window = tk.Toplevel(self.root)
            preview_window.title(f"プレビュー: {photo_name}")
            preview_window.geometry("900x750")
            
            # 情報フレーム（上部）
            info_frame = ttk.LabelFrame(preview_window, text="写真情報", padding=10)
            info_frame.pack(fill=tk.X, padx=10, pady=10)
            
            ttk.Label(info_frame, text=f"ファイル名: {photo_name}", 
                     font=("", 10, "bold")).pack(anchor=tk.W)
            
            # マッチング情報
            if values[6]:  # マッチングポイント
                ttk.Label(info_frame, text=f"マッチング: {values[6]} ({values[3]})", 
                         foreground="blue", font=("", 9)).pack(anchor=tk.W, pady=2)
                ttk.Label(info_frame, text=f"距離: {values[7]}", 
                         foreground="green", font=("", 9)).pack(anchor=tk.W)
                if values[1]:  # 新ファイル名
                    ttk.Label(info_frame, text=f"新ファイル名: {values[1]}", 
                             foreground="purple", font=("", 9)).pack(anchor=tk.W, pady=2)
            else:
                ttk.Label(info_frame, text="マッチング: 未設定", 
                         foreground="red", font=("", 9)).pack(anchor=tk.W, pady=2)
            
            # EXIF情報
            if photo_name in self.photo_gps_data:
                data = self.photo_gps_data[photo_name]
                
                ttk.Separator(info_frame, orient='horizontal').pack(fill=tk.X, pady=5)
                
                if 'datetime' in data:
                    ttk.Label(info_frame, text=f"撮影日時: {data['datetime']}", 
                             font=("", 9)).pack(anchor=tk.W)
                
                if 'lat' in data and 'lon' in data:
                    ttk.Label(info_frame, 
                             text=f"GPS座標: 緯度 {data['lat']:.6f}°, 経度 {data['lon']:.6f}°",
                             font=("", 9)).pack(anchor=tk.W, pady=2)
                
                if 'x_coord' in data and 'y_coord' in data:
                    ttk.Label(info_frame, 
                             text=f"平面直角座標: X={data['x_coord']:.3f}m, Y={data['y_coord']:.3f}m",
                             font=("", 9)).pack(anchor=tk.W)
            
            # 画像表示フレーム
            img_frame = ttk.Frame(preview_window)
            img_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
            
            img = Image.open(photo_path)
            
            # ファイルサイズ情報
            file_size = os.path.getsize(photo_path) / 1024  # KB
            img_info = f"画像サイズ: {img.width}×{img.height}px, ファイルサイズ: {file_size:.1f}KB"
            ttk.Label(info_frame, text=img_info, font=("", 8), foreground="gray").pack(anchor=tk.W)
            
            # アスペクト比を維持してリサイズ
            max_width, max_height = 880, 550
            img.thumbnail((max_width, max_height), Image.LANCZOS)
            
            from PIL import ImageTk
            photo = ImageTk.PhotoImage(img)
            
            label = tk.Label(img_frame, image=photo, bg="gray")
            label.image = photo  # 参照を保持
            label.pack()
            
            # ボタンフレーム
            button_frame = ttk.Frame(preview_window)
            button_frame.pack(fill=tk.X, padx=10, pady=10)
            
            ttk.Button(button_frame, text="閉じる", 
                      command=preview_window.destroy).pack(side=tk.RIGHT, padx=5)
            
            if not values[6]:  # マッチング未設定
                ttk.Button(button_frame, text="測量点にマッチング", 
                          command=lambda: [preview_window.destroy(), 
                                         self.photos_tree.selection_set(selected_items[0]),
                                         self.photos_tree.focus(selected_items[0])]).pack(side=tk.LEFT, padx=5)
            
        except Exception as e:
            messagebox.showerror("エラー", f"写真のプレビューに失敗しました:\n{str(e)}")
            print(f"プレビューエラー詳細:\n{traceback.format_exc()}")
    
    def edit_photo_matching(self):
        """既にマッチング済みの写真のマッチング情報を編集"""
        selected_items = self.photos_tree.selection()
        if not selected_items:
            messagebox.showwarning("警告", "写真が選択されていません")
            return
        
        photo_item = selected_items[0]
        values = self.photos_tree.item(photo_item)['values']
        
        if not values[6]:  # マッチングポイントが空
            messagebox.showinfo("情報", "この写真はまだマッチングされていません")
            return
        
        # 編集ダイアログを表示
        edit_dialog = tk.Toplevel(self.root)
        edit_dialog.title("マッチング編集")
        edit_dialog.geometry("400x250")
        edit_dialog.transient(self.root)
        edit_dialog.grab_set()
        
        ttk.Label(edit_dialog, text=f"写真: {values[0]}", font=("", 10)).pack(pady=10)
        ttk.Label(edit_dialog, text=f"現在のマッチング: {values[6]}", font=("", 10)).pack(pady=5)
        
        # 遠景/近景変更
        ttk.Label(edit_dialog, text="遠景/近景:", font=("", 10)).pack(pady=5)
        landscape_var = tk.StringVar(value=values[3])
        ttk.Radiobutton(edit_dialog, text="遠景", variable=landscape_var, value="遠景").pack()
        ttk.Radiobutton(edit_dialog, text="近景", variable=landscape_var, value="近景").pack()
        
        def save_edit():
            new_landscape = landscape_var.get()
            
            # 新しいファイル名を生成
            identifier = values[6]
            original_filename = values[0]
            
            # 対応する測量点を探す
            matched_point = None
            for point in self.sim_points:
                point_id = point['点名'] if self.use_point_name.get() else point['点番']
                if point_id == identifier or point['点名'] == identifier:
                    matched_point = point
                    break
            
            if matched_point:
                new_filename = self.create_filename(identifier, original_filename, new_landscape, matched_point)
                
                # TreeView更新
                updated_values = list(values)
                updated_values[1] = new_filename
                updated_values[3] = new_landscape
                self.photos_tree.item(photo_item, values=updated_values)
                
                edit_dialog.destroy()
                messagebox.showinfo("成功", "マッチング情報を更新しました")
                self.update_map_light()
            else:
                messagebox.showerror("エラー", "対応する測量点が見つかりません")
        
        ttk.Button(edit_dialog, text="保存", command=save_edit).pack(pady=20)
        
        # ダイアログを中央に配置
        edit_dialog.update_idletasks()
        x = (edit_dialog.winfo_screenwidth() // 2) - (edit_dialog.winfo_width() // 2)
        y = (edit_dialog.winfo_screenheight() // 2) - (edit_dialog.winfo_height() // 2)
        edit_dialog.geometry(f"+{x}+{y}")
    
    def unmatch_photo(self):
        """写真のマッチングを解除"""
        selected_items = self.photos_tree.selection()
        if not selected_items:
            messagebox.showwarning("警告", "写真が選択されていません")
            return
        
        photo_item = selected_items[0]
        values = self.photos_tree.item(photo_item)['values']
        
        if not values[6]:  # マッチングポイントが空
            messagebox.showinfo("情報", "この写真はマッチングされていません")
            return
        
        if messagebox.askyesno("確認", f"写真「{values[0]}」のマッチングを解除しますか？"):
            # マッチング情報をクリア
            updated_values = list(values)
            updated_values[1] = ""  # 新ファイル名
            updated_values[3] = "不明"  # 遠景/近景
            updated_values[6] = ""  # マッチングポイント
            updated_values[7] = ""  # 距離
            
            self.photos_tree.item(photo_item, values=updated_values)
            
            messagebox.showinfo("成功", "マッチングを解除しました")
            self.update_map_light()
    
    def rename_photos_to_new_folder(self):
        """写真を新しいフォルダにリネームしてコピー"""
        if not self.photo_gps_data:
            messagebox.showwarning("警告", "写真が読み込まれていません")
            return
        
        # バックアップ確認ダイアログ
        create_backup = messagebox.askyesno(
            "バックアップ確認",
            "リネーム実行前に元のファイルのバックアップを作成しますか?\n\n"
            "「はい」: backup_YYYYMMDD_HHMMSSフォルダにバックアップを作成\n"
            "「いいえ」: バックアップなしでリネーム実行"
        )
        
        # バックアップ作成
        if create_backup:
            try:
                backup_folder = self.create_backup()
                messagebox.showinfo("完了", f"バックアップを作成しました:\n{backup_folder}")
            except Exception as e:
                messagebox.showerror("エラー", f"バックアップ作成に失敗しました:\n{str(e)}")
                return
        
        # リネーム対象の写真リストを作成
        rename_list = []
        for item_id in self.photos_tree.get_children():
            values = self.photos_tree.item(item_id)['values']
            if values[1]:  # 新ファイル名が設定されている
                # 元ファイル名（values[0]）が既にリネーム済みかチェック
                original_filename = values[0]
                new_filename = values[1]
                
                # 実際のファイルが存在するか確認
                src_exists = os.path.exists(os.path.join(self.photo_directory.get(), original_filename))
                
                rename_list.append({
                    'item_id': item_id,
                    'original': original_filename,
                    'new': new_filename,
                    'src_exists': src_exists
                })
        
        if not rename_list:
            messagebox.showwarning("警告", "リネーム対象の写真がありません")
            return
        
        # 出力フォルダを選択
        output_folder = filedialog.askdirectory(title="リネーム後の写真を保存するフォルダを選択")
        
        if not output_folder:
            return
        
        # リネーム実行
        success_count = 0
        error_list = []
        
        for item in rename_list:
            try:
                src_path = os.path.join(self.photo_directory.get(), item['original'])
                dst_path = os.path.join(output_folder, item['new'])
                
                if not os.path.exists(src_path):
                    error_list.append(f"{item['original']}: ファイルが見つかりません")
                    continue
                
                # ファイルコピー
                shutil.copy2(src_path, dst_path)
                success_count += 1
                
            except Exception as e:
                error_list.append(f"{item['original']}: {str(e)}")
        
        # 結果表示
        result_message = f"{success_count}枚の写真をリネームしました"
        
        if error_list:
            result_message += f"\n\nエラー ({len(error_list)}件):\n" + "\n".join(error_list[:5])
            if len(error_list) > 5:
                result_message += f"\n...他{len(error_list) - 5}件"
        
        messagebox.showinfo("完了", result_message)
    
    def auto_match_by_gps(self):
        """GPS座標に基づいて写真を自動マッチング"""
        if not self.sim_points or not self.photo_gps_data:
            messagebox.showwarning("警告", "測量点または写真が読み込まれていません")
            return
        
        if self.use_arbitrary_coordinates.get():
            messagebox.showinfo("情報", 
                              "任意座標系では自動マッチングは使用できません。\n"
                              "手動でドラッグ&ドロップしてマッチングしてください。")
            return
        
        if not self.use_gps_conversion.get():
            messagebox.showinfo("情報", 
                              "GPS座標変換が無効になっています。\n"
                              "座標系設定でGPS変換を有効にしてから実行してください。")
            return
        
        # マッチング距離の入力
        distance = simpledialog.askfloat(
            "GPS自動マッチング",
            "マッチング許容距離（メートル）を入力してください:\n\n"
            "この距離以内にある最も近い測量点に自動マッチングします。",
            initialvalue=10.0,
            minvalue=1.0,
            maxvalue=100.0
        )
        
        if not distance:
            return
        
        matched_count = 0
        skipped_count = 0
        no_gps_count = 0
        
        for item_id in self.photos_tree.get_children():
            values = list(self.photos_tree.item(item_id)['values'])
            photo_name = values[0]
            
            # 既にマッチング済みはスキップ
            if values[6]:
                skipped_count += 1
                continue
            
            if photo_name not in self.photo_gps_data:
                no_gps_count += 1
                continue
            
            data = self.photo_gps_data[photo_name]
            if 'x_coord' not in data or 'y_coord' not in data:
                no_gps_count += 1
                continue
            
            # 最も近い測量点を探す
            min_distance = float('inf')
            matched_point = None
            
            for point in self.sim_points:
                dist = math.sqrt((point['X座標'] - data['x_coord']) ** 2 + 
                               (point['Y座標'] - data['y_coord']) ** 2)
                if dist < min_distance:
                    min_distance = dist
                    matched_point = point
            
            if matched_point and min_distance <= distance:
                identifier = matched_point['点名'] if self.use_point_name.get() else matched_point['点番']
                
                # デフォルトで近景
                new_filename = self.create_filename(identifier, photo_name, "近景", matched_point)
                
                values[1] = new_filename
                values[3] = "近景"
                values[4] = f"{matched_point['X座標']:.3f}"
                values[5] = f"{matched_point['Y座標']:.3f}"
                values[6] = identifier
                values[7] = f"{min_distance:.1f}m"
                
                self.photos_tree.item(item_id, values=values)
                
                # GPS座標も更新
                self.photo_gps_data[photo_name]['x_coord'] = matched_point['X座標']
                self.photo_gps_data[photo_name]['y_coord'] = matched_point['Y座標']
                
                matched_count += 1
        
        # 結果表示
        result_msg = f"GPS自動マッチング完了\n\n"
        result_msg += f"マッチング成功: {matched_count}枚\n"
        if skipped_count > 0:
            result_msg += f"既にマッチング済み: {skipped_count}枚\n"
        if no_gps_count > 0:
            result_msg += f"GPS情報なし: {no_gps_count}枚\n"
        result_msg += f"\n許容距離: {distance}m以内"
        
        messagebox.showinfo("完了", result_msg)
        self.update_map_light()
    
    def show_statistics(self):
        """マッチング状況の統計を表示"""
        total = len(list(self.photos_tree.get_children()))
        matched = 0
        distant = 0
        close = 0
        
        for item_id in self.photos_tree.get_children():
            values = self.photos_tree.item(item_id)['values']
            if values[6]:  # マッチング済み
                matched += 1
                if values[3] == "遠景":
                    distant += 1
                elif values[3] == "近景":
                    close += 1
        
        unmatched = total - matched
        match_percent = (matched / total * 100) if total > 0 else 0
        
        stats_text = f"""
【マッチング状況】

総写真数: {total}枚
マッチング済み: {matched}枚 ({match_percent:.1f}%)
未マッチング: {unmatched}枚

内訳:
  遠景: {distant}枚
  近景: {close}枚

【測量データ】

測量点数: {len(self.sim_points)}点
地番数: {len(self.landparcel_data)}筆

【座標系】

{"任意座標系（ローカル座標系）" if self.use_arbitrary_coordinates.get() else f"平面直角座標系 {self.coordinate_system.get()}系"}
GPS変換: {"有効" if self.use_gps_conversion.get() else "無効"}
"""
        messagebox.showinfo("統計情報", stats_text)
    
    def save_settings(self):
        """設定をJSONファイルに保存"""
        settings = {
            'use_point_name': self.use_point_name.get(),
            'use_landscape_suffix': self.use_landscape_suffix.get(),
            'force_point_name_for_special': self.force_point_name_for_special.get(),
            'coordinate_system': self.coordinate_system.get(),
            'use_gps_conversion': self.use_gps_conversion.get(),
            'drag_mode': self.drag_mode.get()
        }
        
        try:
            import json
            settings_path = os.path.join(os.path.dirname(__file__), 'gpsscan_settings.json')
            with open(settings_path, 'w', encoding='utf-8') as f:
                json.dump(settings, f, indent=2, ensure_ascii=False)
            
            messagebox.showinfo("成功", f"設定を保存しました\n\n{settings_path}")
        except Exception as e:
            messagebox.showerror("エラー", f"設定の保存に失敗しました:\n{str(e)}")
    
    def load_settings(self):
        """設定をJSONファイルから読み込み"""
        try:
            import json
            settings_path = os.path.join(os.path.dirname(__file__), 'gpsscan_settings.json')
            
            if not os.path.exists(settings_path):
                messagebox.showinfo("情報", "設定ファイルが見つかりません\n\nデフォルト設定を使用します。")
                return
            
            with open(settings_path, 'r', encoding='utf-8') as f:
                settings = json.load(f)
            
            self.use_point_name.set(settings.get('use_point_name', False))
            self.use_landscape_suffix.set(settings.get('use_landscape_suffix', True))
            self.force_point_name_for_special.set(settings.get('force_point_name_for_special', True))
            self.coordinate_system.set(settings.get('coordinate_system', 9))
            self.drag_mode.set(settings.get('drag_mode', 1))
            
            # GPS変換は任意座標系でない場合のみ復元
            if not self.use_arbitrary_coordinates.get():
                self.use_gps_conversion.set(settings.get('use_gps_conversion', True))
            
            messagebox.showinfo("成功", f"設定を読み込みました\n\n{settings_path}")
        except Exception as e:
            messagebox.showerror("エラー", f"設定の読み込みに失敗しました:\n{str(e)}")
    
    def show_help(self):
        """使い方を表示"""
        help_text = """
【測量写真リネームアプリケーション GPSSCAN】

■ 基本的な使い方：
1. SIMファイルを読み込む（A01/A02/D00形式対応）
2. 写真フォルダを読み込む
3. 写真リストから写真を選択
4. 地図上の測量点にドラッグ&ドロップ
5. 遠景/近景を選択
6. 「リネーム実行」でファイルを出力

■ 地図操作：
- 左クリック+ドラッグ：写真を測量点に配置
- 右クリック+ドラッグ：地図をパン（移動）
- マウスホイール：ズームイン/アウト
- ダブルクリック：写真プレビュー

■ ファイル名ルール：
- 新規写真：基本形（境界01-1.jpg / 境界01-2.jpg）
- 追加写真：既存写真を通し番号に変更し、新規写真が基本形になる
- 遠景：-1、近景：-2
- 2枚目以降：_3, _4, _5...（測量点全体で通し番号）

■ 対応座標系：
- 平面直角座標系（自動判定）
- 任意座標系（マイナス座標を検出して自動切り替え）
- 測量座標系（X=北、Y=東）に対応
"""
        messagebox.showinfo("使い方", help_text)
    
    def on_gps_conversion_changed(self):
        """GPS変換設定が変更された時の処理"""
        if self.use_gps_conversion.get():
            self.coord_combo.config(state="readonly")
            print(f"GPS座標変換を有効化しました（{self.coordinate_system.get()}系）")
        else:
            self.coord_combo.config(state="disabled")
            print("GPS座標変換を無効化しました（任意座標系/手動マッチング）")
    
    def show_about(self):
        """バージョン情報を表示"""
        about_text = """
測量写真リネームアプリケーション GPSSCAN
Version 2.0

Copyright (c) 2025
"""
        messagebox.showinfo("バージョン情報", about_text)


def main():
    """メイン関数"""
    root = tk.Tk()
    app = GPSScanApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
