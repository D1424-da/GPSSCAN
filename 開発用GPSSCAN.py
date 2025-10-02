# -*- coding: utf-8 -*-
import math
import os
import re
import shutil
import time
import tkinter as tk
from datetime import datetime
from tkinter import filedialog, messagebox, ttk

import cv2
# matplotlibのバックエンドをTkAggに設定（Qt依存を避ける）
import matplotlib
import numpy as np
import pandas as pd
from PIL import Image
from PIL.ExifTags import GPSTAGS, TAGS
from pyproj import Transformer
from skimage.feature import graycomatrix, graycoprops

matplotlib.use('TkAgg')
# matplotlibで日本語を表示するためのフォント設定
import matplotlib.font_manager as fm
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from PIL import ImageTk

plt.rcParams['font.family'] = 'DejaVu Sans'  # デフォルトフォント
# 日本語フォントがある場合は使用（なければデフォルトフォント）
try:
    # Windowsの場合はMeiryo、MS Gothic等を試す
    japanese_fonts = ['Meiryo', 'MS Gothic', 'Yu Gothic', 'Hiragino Sans']
    for font in japanese_fonts:
        if font in [f.name for f in fm.fontManager.ttflist]:
            plt.rcParams['font.family'] = font
            break
except:
    pass


class PySimPhotoRenamerAdvanced:

    def __init__(self, root):
        self.root = root
        self.root.title("高度な測量写真リネーマー")
        self.root.geometry("900x900")

        # データ保持用の変数
        self.sim_file_path = tk.StringVar()
        self.photo_directory = tk.StringVar()
        self.points_df = None
        self.photos = []
        self.photo_gps_data = {}  # 写真ごとのGPS情報を保存
        self.photo_dates = {}  # 写真の撮影日時情報
        self.landparcels = []  # 画地データを保持

        # 座標系変換用パラメータ
        self.coord_system = tk.StringVar(value="2")  # デフォルトは2系
        self.coord_type = tk.StringVar(value="plane")  # 座標タイプの変数を追加

        # マッチング設定
        self.matching_distance = tk.DoubleVar(value=10.0)  # デフォルトは10メートル

        # 命名オプション
        self.use_point_name = tk.BooleanVar(value=True)  # デフォルトは点名を使用
        self.use_landscape_suffix = tk.BooleanVar(value=True)  # デフォルトは遠景近景サフィックスを使用

        # 並べ替えオプション
        self.sort_option = tk.StringVar(value="撮影日時")  # デフォルトは撮影日時順

        # UI作成
        self.create_ui()

    def create_ui(self):
        notebook = ttk.Notebook(self.root)
        notebook.pack(fill="both", expand=True, padx=10, pady=10)

        main_frame = ttk.Frame(notebook)
        map_frame = ttk.Frame(notebook)
        settings_frame = ttk.Frame(notebook)

        notebook.add(main_frame, text="メイン")
        notebook.add(map_frame, text="地図表示")
        notebook.add(settings_frame, text="設定")

        self.create_main_ui(main_frame)
        self.create_map_ui(map_frame)
        self.create_settings_ui(settings_frame)

    def create_main_ui(self, parent):
        # .simファイル選択
        tk.Label(parent, text=".simファイルを選択").pack(pady=5)
        sim_frame = tk.Frame(parent)
        sim_frame.pack(pady=5, fill=tk.X)

        tk.Button(sim_frame, text=".simファイル選択", command=self.select_sim_file).pack(side=tk.LEFT,
                                                                                   padx=5)
        tk.Label(sim_frame, textvariable=self.sim_file_path, wraplength=500).pack(side=tk.LEFT)

        # 写真ディレクトリ選択
        tk.Label(parent, text="写真フォルダを選択").pack(pady=5)
        photo_frame = tk.Frame(parent)
        photo_frame.pack(pady=5, fill=tk.X)

        tk.Button(photo_frame, text="写真フォルダ選択",
                  command=self.select_photo_directory).pack(side=tk.LEFT, padx=5)
        tk.Label(photo_frame, textvariable=self.photo_directory, wraplength=500).pack(side=tk.LEFT)

        # ポイント一覧
        points_frame = tk.Frame(parent)
        points_frame.pack(pady=5, fill=tk.BOTH, expand=True)

        tk.Label(points_frame, text="ポイント一覧").pack(pady=5)

        points_tree_frame = tk.Frame(points_frame)
        points_tree_frame.pack(fill=tk.BOTH, expand=True)

        self.points_tree = ttk.Treeview(points_tree_frame,
                                        columns=('点番', '点名', 'X座標', 'Y座標'),
                                        show='headings')
        self.points_tree.heading('点番', text='点番')
        self.points_tree.heading('点名', text='点名')
        self.points_tree.heading('X座標', text='X座標')
        self.points_tree.heading('Y座標', text='Y座標')

        self.points_tree.column('点番', width=50)
        self.points_tree.column('点名', width=100)
        self.points_tree.column('X座標', width=100)
        self.points_tree.column('Y座標', width=100)

        scrollbar_y = ttk.Scrollbar(points_tree_frame,
                                    orient="vertical",
                                    command=self.points_tree.yview)
        scrollbar_x = ttk.Scrollbar(points_tree_frame,
                                    orient="horizontal",
                                    command=self.points_tree.xview)
        self.points_tree.configure(yscrollcommand=scrollbar_y.set, xscrollcommand=scrollbar_x.set)

        scrollbar_y.pack(side="right", fill="y")
        scrollbar_x.pack(side="bottom", fill="x")
        self.points_tree.pack(side="left", fill="both", expand=True)

        # 写真一覧
        photos_frame = tk.Frame(parent)
        photos_frame.pack(pady=5, fill=tk.BOTH, expand=True)

        # 並べ替えオプション
        sort_frame = tk.Frame(photos_frame)
        sort_frame.pack(pady=5, fill=tk.X)

        tk.Label(sort_frame, text="並べ替え:").pack(side=tk.LEFT, padx=5)
        sort_options = ["撮影日時", "ファイル更新日時", "ファイル名"]
        sort_menu = ttk.Combobox(sort_frame,
                                 textvariable=self.sort_option,
                                 values=sort_options,
                                 width=15)
        sort_menu.pack(side=tk.LEFT, padx=5)
        tk.Button(sort_frame, text="並べ替え実行", command=self.sort_photos).pack(side=tk.LEFT, padx=5)

        tk.Label(photos_frame, text="写真一覧").pack(pady=5)

        photos_tree_frame = tk.Frame(photos_frame)
        photos_tree_frame.pack(fill=tk.BOTH, expand=True)

        self.photos_tree = ttk.Treeview(photos_tree_frame,
                                        columns=('元ファイル名', '新ファイル名', '撮影日時', '遠景/近景', 'X座標', 'Y座標',
                                                 'マッチングポイント', '距離(m)'),
                                        show='headings')
        self.photos_tree.heading('元ファイル名', text='元ファイル名')
        self.photos_tree.heading('新ファイル名', text='新ファイル名')
        self.photos_tree.heading('撮影日時', text='撮影日時')
        self.photos_tree.heading('遠景/近景', text='遠景/近景')
        self.photos_tree.heading('X座標', text='X座標')
        self.photos_tree.heading('Y座標', text='Y座標')
        self.photos_tree.heading('マッチングポイント', text='マッチングポイント')
        self.photos_tree.heading('距離(m)', text='距離(m)')

        self.photos_tree.column('元ファイル名', width=120)
        self.photos_tree.column('新ファイル名', width=120)
        self.photos_tree.column('撮影日時', width=140)
        self.photos_tree.column('遠景/近景', width=70)
        self.photos_tree.column('X座標', width=90)
        self.photos_tree.column('Y座標', width=90)
        self.photos_tree.column('マッチングポイント', width=100)
        self.photos_tree.column('距離(m)', width=70)

        photos_scrollbar_y = ttk.Scrollbar(photos_tree_frame,
                                           orient="vertical",
                                           command=self.photos_tree.yview)
        photos_scrollbar_x = ttk.Scrollbar(photos_tree_frame,
                                           orient="horizontal",
                                           command=self.photos_tree.xview)
        self.photos_tree.configure(yscrollcommand=photos_scrollbar_y.set,
                                   xscrollcommand=photos_scrollbar_x.set)

        photos_scrollbar_y.pack(side="right", fill="y")
        photos_scrollbar_x.pack(side="bottom", fill="x")
        self.photos_tree.pack(side="left", fill="both", expand=True)

        # ダブルクリックイベント追加
        self.photos_tree.bind("<Double-1>", self.on_photo_double_click)

        # コンテキストメニュー
        self.photo_context_menu = tk.Menu(self.root, tearoff=0)
        self.photo_context_menu.add_command(label="手動でポイントを選択", command=self.manually_select_point)
        self.photos_tree.bind("<Button-3>", self.show_photo_context_menu)

        # リネームボタン
        button_frame = tk.Frame(parent)
        button_frame.pack(pady=10)

        tk.Button(button_frame, text="GPS座標→XY座標へ変換",
                  command=self.convert_gps_to_xy).pack(side=tk.LEFT, padx=5)
        tk.Button(button_frame, text="XY座標でマッチング",
                  command=self.match_photos_to_points_xy).pack(side=tk.LEFT, padx=5)
        tk.Button(button_frame, text="写真を新規フォルダにリネーム",
                  command=self.rename_photos_to_new_folder).pack(side=tk.LEFT, padx=5)

        # 統合されたドラッグ＆ドロップのイベントを設定
        self.photos_tree.bind('<ButtonPress-1>', self.on_button_press)
        self.points_tree.bind('<ButtonPress-1>', self.on_button_press)
        self.photos_tree.bind('<ButtonRelease-1>', self.on_button_release)
        self.points_tree.bind('<ButtonRelease-1>', self.on_button_release)

    def on_photo_drag_start(self, event):
        """写真ツリーでのドラッグ開始"""
        if hasattr(self, 'dragged_point'):
            del self.dragged_point

        self.drag_start_widget = event.widget
        self.drag_start_item = self.drag_start_widget.identify_row(event.y)

        if self.drag_start_item:
            # ドラッグ中の写真情報を取得
            self.dragged_photo = self.photos_tree.item(self.drag_start_item)['values']

    def on_point_drop_photo(self, event):
        """写真をポイントツリーにドロップした際の処理"""
        # ドラッグ元が写真ツリーであることを確認
        if (not hasattr(self, 'drag_start_widget') or not hasattr(self, 'dragged_photo') or
                self.drag_start_widget != self.photos_tree):
            return

        # ドロップされたポイントアイテムを特定
        drop_widget = event.widget
        if drop_widget != self.points_tree:
            return

        drop_item = drop_widget.identify_row(event.y)
        if not drop_item:
            return

        # ポイントの情報を取得
        point_values = self.points_tree.item(drop_item)['values']

        # 写真の情報
        photo_name = self.dragged_photo[0]  # 元ファイル名
        landscape_type = self.dragged_photo[3]  # 遠景/近景

        # 点番または点名を取得
        identifier = point_values[1] if self.use_point_name.get() else point_values[0]

        # 新しいファイル名を生成
        new_filename = self.create_filename(identifier, photo_name, landscape_type)

        # 距離計算（可能な場合）
        distance_str = "手動選択"
        if photo_name in self.photo_gps_data and 'x_coord' in self.photo_gps_data[photo_name]:
            photo_x = self.photo_gps_data[photo_name]['x_coord']
            photo_y = self.photo_gps_data[photo_name]['y_coord']
            point_x = point_values[2]  # X座標
            point_y = point_values[3]  # Y座標
            try:
                # 文字列から浮動小数点に変換（.3fフォーマットが適用されている可能性あり）
                if isinstance(point_x, str):
                    point_x = float(point_x)
                if isinstance(point_y, str):
                    point_y = float(point_y)

                distance = self.calculate_xy_distance(photo_x, photo_y, point_x, point_y)
                distance_str = f"{distance:.1f}m (D&D)"
            except Exception as e:
                print(f"距離計算エラー: {e}")

        # 写真ツリーを更新
        for item_id in self.photos_tree.get_children():
            values = list(self.photos_tree.item(item_id)['values'])
            if values[0] == photo_name:  # 元ファイル名で一致確認
                values[1] = new_filename  # 新ファイル名
                values[6] = identifier  # マッチングポイント
                values[7] = distance_str  # 距離

                self.photos_tree.item(item_id, values=values)
                break

        # リセット
        del self.drag_start_widget
        del self.dragged_photo

        # 操作のフィードバック
        messagebox.showinfo("ドラッグ&ドロップ", f"写真「{photo_name}」を点「{identifier}」に割り当てました")

    def sort_photos(self):
        """写真を選択した条件で並べ替える"""
        items = [(self.photos_tree.item(item_id, "values"), item_id)
                 for item_id in self.photos_tree.get_children()]
        if not items:
            return

        sort_by = self.sort_option.get()

        if sort_by == "撮影日時":
            # 撮影日時で並べ替え
            items.sort(key=lambda x: self.photo_dates.get(x[0][0], datetime.max))
        elif sort_by == "ファイル更新日時":
            # ファイルの更新日時で並べ替え
            directory = self.photo_directory.get()
            items.sort(key=lambda x: os.path.getmtime(os.path.join(directory, x[0][0])))
        else:  # ファイル名
            # ファイル名で並べ替え
            items.sort(key=lambda x: x[0][0])

        # 一旦すべての項目を削除
        for item_id in self.photos_tree.get_children():
            self.photos_tree.delete(item_id)

        # 並べ替えた順番で再挿入
        for values, _ in items:
            self.photos_tree.insert('', 'end', values=values)

        messagebox.showinfo("並べ替え完了", f"写真を{sort_by}順に並べ替えました")

    def on_photo_double_click(self, event):
        """写真一覧のダブルクリックでポイント手動選択画面を開く"""
        item = self.photos_tree.identify('item', event.x, event.y)
        if item:
            self.photos_tree.selection_set(item)
            self.manually_select_point()

    def create_map_ui(self, parent):
        # 地図表示用のエリア
        self.fig, self.ax = plt.subplots(figsize=(8, 6))
        self.canvas = FigureCanvasTkAgg(self.fig, master=parent)
        self.canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)

        # マウスホイールによる拡大縮小を有効化
        self.fig.canvas.mpl_connect('scroll_event', self.on_scroll)

        # 地図更新ボタン
        button_frame = tk.Frame(parent)
        button_frame.pack(pady=10)

        tk.Button(button_frame, text="地図を更新", command=self.update_map).pack(side=tk.LEFT, padx=5)
        tk.Button(button_frame, text="表示をリセット", command=self.reset_map_view).pack(side=tk.LEFT,
                                                                                  padx=5)

    def on_scroll(self, event):
        """マウスホイールでの拡大縮小処理"""
        # 現在の表示範囲を取得
        x_min, x_max = self.ax.get_xlim()
        y_min, y_max = self.ax.get_ylim()

        # 拡大縮小の係数
        scale_factor = 0.9 if event.button == 'up' else 1.1

        # マウスポインタの位置を中心に拡大縮小
        x_center = event.xdata
        y_center = event.ydata

        # マウスが地図の外にある場合は処理しない
        if x_center is None or y_center is None:
            return

        # 新しい範囲を計算
        x_min_new = x_center - (x_center - x_min) * scale_factor
        x_max_new = x_center + (x_max - x_center) * scale_factor
        y_min_new = y_center - (y_center - y_min) * scale_factor
        y_max_new = y_center + (y_max - y_center) * scale_factor

        # 表示範囲を更新
        self.ax.set_xlim(x_min_new, x_max_new)
        self.ax.set_ylim(y_min_new, y_max_new)

        # グラフを再描画
        self.canvas.draw()

    def reset_map_view(self):
        """地図表示をリセット"""
        # XY座標に基づいて範囲を計算
        try:
            if self.points_df is not None and not self.points_df.empty or self.photo_gps_data:
                all_xs = []
                all_ys = []

                # 測量点の座標を追加
                if self.points_df is not None and not self.points_df.empty:
                    all_xs.extend(self.points_df['X座標'].tolist())
                    all_ys.extend(self.points_df['Y座標'].tolist())

                # 写真の座標を追加
                for photo_name, gps_data in self.photo_gps_data.items():
                    if 'x_coord' in gps_data and 'y_coord' in gps_data:
                        all_xs.append(gps_data['x_coord'])
                        all_ys.append(gps_data['y_coord'])

                if all_xs and all_ys:
                    # 範囲をちょっと広めに
                    x_margin = (max(all_xs) - min(all_xs)) * 0.1
                    y_margin = (max(all_ys) - min(all_ys)) * 0.1

                    self.ax.set_xlim(min(all_xs) - x_margin, max(all_xs) + x_margin)
                    self.ax.set_ylim(min(all_ys) - y_margin, max(all_ys) + y_margin)

                    # グラフを再描画
                    self.canvas.draw()
                    return

            messagebox.showinfo("情報", "表示をリセットするデータがありません")

        except Exception as e:
            print(f"表示リセットエラー: {e}")
            messagebox.showerror("エラー", "表示のリセット中にエラーが発生しました")

    def create_settings_ui(self, parent):
        # 設定フレーム
        settings_frame = tk.LabelFrame(parent, text="設定")
        settings_frame.pack(pady=10, padx=10, fill=tk.X)

        # 座標系設定
        coord_frame = tk.Frame(settings_frame)
        coord_frame.pack(pady=5, fill=tk.X)

        tk.Label(coord_frame, text="座標系:").pack(side=tk.LEFT, padx=5)

        coord_options = [
            "1", "2", "3", "4", "5", "6", "7", "8", "9", "10", "11", "12", "13", "14", "15", "16",
            "17", "18", "19"
        ]
        coord_menu = ttk.Combobox(coord_frame,
                                  textvariable=self.coord_system,
                                  values=coord_options,
                                  width=5)
        coord_menu.pack(side=tk.LEFT, padx=5)
        tk.Label(coord_frame, text="系").pack(side=tk.LEFT)

        # 座標タイプ設定
        coord_type_frame = tk.Frame(settings_frame)
        coord_type_frame.pack(pady=5, fill=tk.X)

        tk.Label(coord_type_frame, text="座標タイプ:").pack(side=tk.LEFT, padx=5)
        ttk.Radiobutton(coord_type_frame, text="平面直角座標", variable=self.coord_type,
                        value="plane").pack(side=tk.LEFT, padx=5)
        ttk.Radiobutton(coord_type_frame, text="緯度経度", variable=self.coord_type,
                        value="latlon").pack(side=tk.LEFT, padx=5)

        # マッチング距離設定
        distance_frame = tk.Frame(settings_frame)
        distance_frame.pack(pady=5, fill=tk.X)

        tk.Label(distance_frame, text="マッチング距離:").pack(side=tk.LEFT, padx=5)
        tk.Entry(distance_frame, textvariable=self.matching_distance, width=10).pack(side=tk.LEFT,
                                                                                     padx=5)
        tk.Label(distance_frame, text="メートル").pack(side=tk.LEFT)

        # 命名オプション
        naming_frame = tk.LabelFrame(parent, text="命名オプション")
        naming_frame.pack(pady=10, padx=10, fill=tk.X)

        point_type_frame = tk.Frame(naming_frame)
        point_type_frame.pack(pady=5, fill=tk.X)

        tk.Radiobutton(point_type_frame, text="点名を使用", variable=self.use_point_name,
                       value=True).pack(side=tk.LEFT, padx=5)
        tk.Radiobutton(point_type_frame, text="点番を使用", variable=self.use_point_name,
                       value=False).pack(side=tk.LEFT, padx=5)

        suffix_frame = tk.Frame(naming_frame)
        suffix_frame.pack(pady=5, fill=tk.X)

        tk.Checkbutton(suffix_frame, text="遠景近景サフィックス",
                       variable=self.use_landscape_suffix).pack(side=tk.LEFT, padx=5)

    def show_photo_context_menu(self, event):
        """写真の右クリックメニューを表示"""
        selected_items = self.photos_tree.selection()
        if selected_items:
            self.photo_context_menu.post(event.x_root, event.y_root)

    def manually_select_point(self):
        """選択した写真に手動でポイントを割り当て"""
        selected_items = self.photos_tree.selection()
        if not selected_items or self.points_df is None:
            return

        # 選択した写真のファイル名表示
        photo_filename = self.photos_tree.item(selected_items[0])['values'][0]
        current_landscape = self.photos_tree.item(selected_items[0])['values'][3]  # 遠景/近景が3列目

        # 手動選択ダイアログ
        dialog = tk.Toplevel(self.root)
        dialog.title("ポイント手動選択")
        dialog.geometry("950x700")  # ダイアログサイズを拡大
        dialog.minsize(950, 700)  # 最小サイズを設定して縮小を防止
        dialog.transient(self.root)
        dialog.grab_set()

        # メインフレーム作成（スクロール可能に）
        main_frame = tk.Frame(dialog)
        main_frame.pack(fill=tk.BOTH, expand=True)

        # ダイアログの上部フレーム（写真情報とプレビュー）
        top_frame = tk.Frame(main_frame)
        top_frame.pack(pady=10, fill=tk.X)

        # 写真情報
        info_frame = tk.Frame(top_frame)
        info_frame.pack(side=tk.LEFT, padx=10, fill=tk.Y)

        tk.Label(info_frame, text=f"写真: {photo_filename}", font=("", 12, "bold")).pack(anchor=tk.W,
                                                                                       pady=5)

        # 座標情報の表示
        gps_frame = tk.Frame(info_frame)
        gps_frame.pack(anchor=tk.W, pady=5)

        if photo_filename in self.photo_gps_data:
            # XY座標の表示
            if 'x_coord' in self.photo_gps_data[
                    photo_filename] and 'y_coord' in self.photo_gps_data[photo_filename]:
                x_coord = self.photo_gps_data[photo_filename]['x_coord']
                y_coord = self.photo_gps_data[photo_filename]['y_coord']
                tk.Label(gps_frame, text=f"X座標: {x_coord:.3f}", width=25,
                         anchor="w").pack(anchor=tk.W)
                tk.Label(gps_frame, text=f"Y座標: {y_coord:.3f}", width=25,
                         anchor="w").pack(anchor=tk.W)
            else:
                tk.Label(gps_frame, text="X座標: GPS座標の変換が必要", width=25, anchor="w").pack(anchor=tk.W)
                tk.Label(gps_frame, text="Y座標: GPS座標の変換が必要", width=25, anchor="w").pack(anchor=tk.W)
        else:
            tk.Label(gps_frame, text="GPS情報: なし").pack(anchor=tk.W)

        # 遠景/近景の選択
        landscape_var = tk.StringVar(value=current_landscape)
        landscape_frame = tk.Frame(info_frame)
        landscape_frame.pack(anchor=tk.W, pady=10)

        tk.Label(landscape_frame, text="遠景/近景:").pack(side=tk.LEFT, padx=(0, 10))
        tk.Radiobutton(landscape_frame, text="遠景", variable=landscape_var,
                       value="遠景").pack(side=tk.LEFT, padx=5)
        tk.Radiobutton(landscape_frame, text="近景", variable=landscape_var,
                       value="近景").pack(side=tk.LEFT, padx=5)

        # 画像プレビュー
        preview_frame = tk.Frame(top_frame, width=450, height=350, bd=1, relief=tk.SUNKEN)  # サイズ拡大
        preview_frame.pack(side=tk.RIGHT, padx=10, fill=tk.BOTH, expand=True)
        preview_frame.pack_propagate(False)  # フレームサイズを固定

        try:
            full_path = os.path.join(self.photo_directory.get(), photo_filename)

            # 画像の読み込みとリサイズ
            img = Image.open(full_path)
            img.thumbnail((430, 330))  # 画像サイズも調整
            photo_img = ImageTk.PhotoImage(img)

            # 画像ラベル
            img_label = tk.Label(preview_frame, image=photo_img)
            img_label.image = photo_img  # 参照を保持（ガベージコレクションを防ぐ）
            img_label.pack(pady=10, padx=10)
        except Exception as e:
            # 画像の読み込みに失敗した場合
            error_label = tk.Label(preview_frame, text=f"画像プレビューを読み込めませんでした\n{str(e)}", fg="red")
            error_label.pack(pady=10, padx=10, fill=tk.BOTH, expand=True)

        # 画像プレビュー枠の下にミニマップを追加
        minimap_frame = tk.Frame(top_frame, width=450, height=200, bd=1, relief=tk.SUNKEN)
        minimap_frame.pack(side=tk.RIGHT, padx=10, pady=(10, 0), fill=tk.X)

        # matplotlib のミニマップを作成
        fig, ax = plt.subplots(figsize=(4, 2))
        canvas = FigureCanvasTkAgg(fig, master=minimap_frame)
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)

        # 初期のミニマップ表示
        def init_minimap():
            """ミニマップの初期表示（順序付き結線処理付き）"""
            # 測量点のプロット
            if self.points_df is not None and not self.points_df.empty:
                ax.scatter(self.points_df['X座標'],
                           self.points_df['Y座標'],
                           color='blue',
                           marker='^',
                           label='測量点')

            # 選択した写真の位置をプロット(あれば)
            if photo_filename in self.photo_gps_data and 'x_coord' in self.photo_gps_data[
                    photo_filename]:
                photo_x = self.photo_gps_data[photo_filename]['x_coord']
                photo_y = self.photo_gps_data[photo_filename]['y_coord']
                ax.scatter([photo_x], [photo_y], color='red', marker='o', s=100, label='選択写真')

            # 画地データの結線表示（順序通りに）
            if hasattr(self, 'landparcels') and self.landparcels:
                for landparcel in self.landparcels:
                    points = landparcel['ポイント']
                    landparcel_coords = []

                    # 順序通りに座標を取得
                    for point_name in points:
                        point = self.points_df[(self.points_df['点名'] == point_name) |
                                               (self.points_df['点番'] == point_name)]
                        if not point.empty:
                            landparcel_coords.append((point.iloc[0]['X座標'], point.iloc[0]['Y座標']))

                    # 閉じた多角形として結線
                    if len(landparcel_coords) > 2:
                        landparcel_coords.append(landparcel_coords[0])
                        xs, ys = zip(*landparcel_coords)
                        ax.plot(xs, ys, color='green', linestyle='-', alpha=0.7)

                        # 各点に順序番号を表示
                        for i, (x, y) in enumerate(landparcel_coords[:-1]):
                            ax.annotate(str(i + 1), (x, y),
                                        fontsize=8,
                                        xytext=(3, 3),
                                        textcoords="offset points",
                                        color='green',
                                        fontweight='bold')

                        # 画地名を表示
                        center_x = sum(x for x, _ in landparcel_coords) / len(landparcel_coords)
                        center_y = sum(y for _, y in landparcel_coords) / len(landparcel_coords)
                        ax.annotate(landparcel['画地名'], (center_x, center_y),
                                    fontsize=8,
                                    ha='center',
                                    va='center')

            # グリッドと凡例を表示
            ax.grid(True)
            ax.legend(loc='upper right', fontsize=8)
            ax.set_title("測量点と画地データ", fontsize=10)

            # 範囲設定（写真を中心に）
            if photo_filename in self.photo_gps_data and 'x_coord' in self.photo_gps_data[
                    photo_filename]:
                photo_x = self.photo_gps_data[photo_filename]['x_coord']
                photo_y = self.photo_gps_data[photo_filename]['y_coord']

                # 表示範囲を写真を中心にして設定
                margin = 50  # 50メートルのマージン
                ax.set_xlim(photo_x - margin, photo_x + margin)
                ax.set_ylim(photo_y - margin, photo_y + margin)

            canvas.draw()

        # 下部フレーム（ポイントリストと画地データをタブで切り替え）
        bottom_frame = tk.Frame(main_frame)
        bottom_frame.pack(pady=10, fill=tk.BOTH, expand=True)

        # タブノートブックを作成
        tab_control = ttk.Notebook(bottom_frame)
        tab_control.pack(fill=tk.BOTH, expand=True)

        # ポイントタブと画地データタブ
        points_tab = ttk.Frame(tab_control)
        landparcels_tab = ttk.Frame(tab_control)

        tab_control.add(points_tab, text="測量点")
        tab_control.add(landparcels_tab, text="画地データ")

        # ポイントタブの内容 --------------------------
        tk.Label(points_tab, text="割り当てるポイントを選択（ダブルクリックで確定）:",
                 font=("", 11, "bold")).pack(anchor=tk.W, padx=10, pady=5)

        # 検索フレーム
        search_frame = tk.Frame(points_tab)
        search_frame.pack(pady=5, padx=10, fill=tk.X)

        tk.Label(search_frame, text="検索:").pack(side=tk.LEFT, padx=(0, 5))

        # search_varをローカル変数として定義
        search_var = tk.StringVar()
        search_entry = tk.Entry(search_frame, textvariable=search_var, width=20)
        search_entry.pack(side=tk.LEFT, padx=5)

        # ポイントリストを表示するフレーム
        list_frame = tk.Frame(points_tab)
        list_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)

        # ポイントリストのスクロールバー
        scrollbar = tk.Scrollbar(list_frame)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        # ポイントリストの表示（Treeviewを使用）
        columns = ('点番', '点名', 'X座標', 'Y座標')
        point_tree = ttk.Treeview(list_frame,
                                  columns=columns,
                                  show='headings',
                                  selectmode='browse',
                                  height=10)
        point_tree.pack(fill=tk.BOTH, expand=True)

        point_tree.heading('点番', text='点番')
        point_tree.heading('点名', text='点名')
        point_tree.heading('X座標', text='X座標')
        point_tree.heading('Y座標', text='Y座標')

        point_tree.column('点番', width=50)
        point_tree.column('点名', width=100)
        point_tree.column('X座標', width=100)
        point_tree.column('Y座標', width=100)

        scrollbar.config(command=point_tree.yview)
        point_tree.config(yscrollcommand=scrollbar.set)

        # ポイントデータをTreeviewに挿入
        for idx, row in self.points_df.iterrows():
            point_tree.insert('',
                              'end',
                              values=(row['点番'], row['点名'], f"{row['X座標']:.3f}",
                                      f"{row['Y座標']:.3f}"))

        # 画地データタブの内容 --------------------------
        tk.Label(landparcels_tab, text="割り当てる画地データを選択（ダブルクリックで確定）:",
                 font=("", 11, "bold")).pack(anchor=tk.W, padx=10, pady=5)

        # 画地データリストを表示するフレーム
        landparcel_frame = tk.Frame(landparcels_tab)
        landparcel_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)

        # 画地データリストのスクロールバー
        landparcel_scrollbar = tk.Scrollbar(landparcel_frame)
        landparcel_scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

        # 画地データリストの表示（Treeviewを使用）
        landparcel_columns = ('画地番号', '画地名', 'ポイント数')
        landparcel_tree = ttk.Treeview(landparcel_frame,
                                       columns=landparcel_columns,
                                       show='headings',
                                       selectmode='browse',
                                       height=10)
        landparcel_tree.pack(fill=tk.BOTH, expand=True)

        landparcel_tree.heading('画地番号', text='画地番号')
        landparcel_tree.heading('画地名', text='画地名')
        landparcel_tree.heading('ポイント数', text='ポイント数')

        landparcel_tree.column('画地番号', width=80)
        landparcel_tree.column('画地名', width=200)
        landparcel_tree.column('ポイント数', width=80)

        landparcel_scrollbar.config(command=landparcel_tree.yview)
        landparcel_tree.config(yscrollcommand=landparcel_scrollbar.set)

        # 画地データをTreeviewに挿入
        if hasattr(self, 'landparcels') and self.landparcels:
            for landparcel in self.landparcels:
                landparcel_tree.insert('',
                                       'end',
                                       values=(landparcel['画地番号'], landparcel['画地名'],
                                               len(landparcel['ポイント'])))

        # 距離情報表示ラベル - より目立つように設定
        info_label = tk.Label(bottom_frame,
                              text="",
                              font=("", 10),
                              bg="#f0f0f0",
                              relief=tk.RIDGE,
                              padx=5,
                              pady=5)
        info_label.pack(side=tk.TOP, pady=5, fill=tk.X, padx=10)

        # ボタンフレーム - 常に表示されるように下部に固定
        button_frame = tk.Frame(dialog, bg="#e0e0e0", height=60)
        button_frame.pack(side=tk.BOTTOM, fill=tk.X)

        # 初期ミニマップを表示
        init_minimap()

        # 検索機能
        def search_points(*args):
            search_text = search_var.get().lower()

            # 一度すべての項目を削除
            for item in point_tree.get_children():
                point_tree.delete(item)

            # 検索条件に合う項目だけを表示
            for idx, row in self.points_df.iterrows():
                if (search_text in str(row['点番']).lower() or search_text in str(row['点名']).lower()):
                    point_tree.insert('',
                                      'end',
                                      values=(row['点番'], row['点名'], f"{row['X座標']:.3f}",
                                              f"{row['Y座標']:.3f}"))

        # traceメソッドを正しく呼び出す
        search_var.trace_add("write", search_points)

        # 測量点との距離を計算する関数
        def calculate_distances():
            selected_items = point_tree.selection()
            if not selected_items:
                return

            # 選択されたポイントを取得
            selected_values = point_tree.item(selected_items[0])['values']
            selected_point = None

            # 点番と点名で一致するポイントを探す
            for _, point in self.points_df.iterrows():
                if (str(point['点番']) == str(selected_values[0]) and
                        str(point['点名']) == str(selected_values[1])):
                    selected_point = point
                    break

            if selected_point is None:
                return

            # 写真とポイントのXY座標距離を計算
            distance_xy_str = "不明"

            if photo_filename in self.photo_gps_data and 'x_coord' in self.photo_gps_data[
                    photo_filename]:
                photo_x = self.photo_gps_data[photo_filename]['x_coord']
                photo_y = self.photo_gps_data[photo_filename]['y_coord']
                distance_xy = self.calculate_xy_distance(photo_x, photo_y, selected_point['X座標'],
                                                         selected_point['Y座標'])
                distance_xy_str = f"{distance_xy:.1f}m"

            # 距離情報を表示 - 確定ボタンのテキストにも距離を表示
            info_label.config(
                text=
                f"点番:{selected_point['点番']} 点名:{selected_point['点名']} | XY座標での距離: {distance_xy_str}"
            )
            confirm_button.config(text=f"確定 (距離: {distance_xy_str})")

            # ミニマップ更新：選択したポイントをハイライト
            update_minimap_with_selected_point(selected_point)

        # ポイント選択時に距離を計算
        point_tree.bind("<<TreeviewSelect>>", lambda e: calculate_distances())

        # ミニマップを更新する関数（選択したポイントをハイライト表示）
        def update_minimap_with_selected_point(selected_point):
            ax.clear()

            # 測量点のプロット
            if self.points_df is not None and not self.points_df.empty:
                ax.scatter(self.points_df['X座標'],
                           self.points_df['Y座標'],
                           color='blue',
                           marker='^',
                           label='測量点',
                           alpha=0.5)  # 通常の点は透明度を下げる

            # 選択した写真の位置をプロット
            if photo_filename in self.photo_gps_data and 'x_coord' in self.photo_gps_data[
                    photo_filename]:
                photo_x = self.photo_gps_data[photo_filename]['x_coord']
                photo_y = self.photo_gps_data[photo_filename]['y_coord']
                ax.scatter([photo_x], [photo_y], color='red', marker='o', s=80, label='選択写真')

            # 選択したポイントをハイライト表示
            ax.scatter([selected_point['X座標']], [selected_point['Y座標']],
                       color='green',
                       marker='*',
                       s=200,
                       label='選択ポイント',
                       zorder=10)

            # 写真と選択ポイントを結ぶ線
            if photo_filename in self.photo_gps_data and 'x_coord' in self.photo_gps_data[
                    photo_filename]:
                photo_x = self.photo_gps_data[photo_filename]['x_coord']
                photo_y = self.photo_gps_data[photo_filename]['y_coord']
                ax.plot([photo_x, selected_point['X座標']], [photo_y, selected_point['Y座標']],
                        'r--',
                        linewidth=2,
                        alpha=0.7)

            # 画地データの結線表示（通常の表示）
            if hasattr(self, 'landparcels') and self.landparcels:
                for landparcel in self.landparcels:
                    points = landparcel['ポイント']
                    landparcel_coords = []

                    for point_name in points:
                        point = self.points_df[(self.points_df['点名'] == point_name) |
                                               (self.points_df['点番'] == point_name)]
                        if not point.empty:
                            landparcel_coords.append((point.iloc[0]['X座標'], point.iloc[0]['Y座標']))

                    if len(landparcel_coords) > 2:
                        landparcel_coords.append(landparcel_coords[0])
                        xs, ys = zip(*landparcel_coords)
                        ax.plot(xs, ys, color='green', linestyle='-', alpha=0.4)

            # グリッドと凡例を表示
            ax.grid(True)
            ax.legend(loc='upper right', fontsize=8)

            # タイトル更新
            ax.set_title(f"選択ポイント: {selected_point['点名']}", fontsize=10)

            # 選択したポイントと写真を含む範囲を表示
            if photo_filename in self.photo_gps_data and 'x_coord' in self.photo_gps_data[
                    photo_filename]:
                photo_x = self.photo_gps_data[photo_filename]['x_coord']
                photo_y = self.photo_gps_data[photo_filename]['y_coord']

                # 表示範囲をポイントと写真を含むように設定
                x_min = min(photo_x, selected_point['X座標'])
                x_max = max(photo_x, selected_point['X座標'])
                y_min = min(photo_y, selected_point['Y座標'])
                y_max = max(photo_y, selected_point['Y座標'])

                # マージンを追加
                x_margin = max(20, (x_max - x_min) * 0.3)
                y_margin = max(20, (y_max - y_min) * 0.3)

                ax.set_xlim(x_min - x_margin, x_max + x_margin)
                ax.set_ylim(y_min - y_margin, y_max + y_margin)

            canvas.draw()

        # 画地データ選択時の処理
        def on_landparcel_select(event):
            selected_items = landparcel_tree.selection()
            if not selected_items:
                return

            selected_values = landparcel_tree.item(selected_items[0])['values']
            selected_id = selected_values[0]  # 画地番号

            # 選択した画地データを取得
            selected_landparcel = None
            for landparcel in self.landparcels:
                if str(landparcel['画地番号']) == str(selected_id):
                    selected_landparcel = landparcel
                    break

            if selected_landparcel:
                update_minimap_with_selected_landparcel(selected_landparcel)

        # 画地データ選択時のミニマップ更新
        def update_minimap_with_selected_landparcel(selected_landparcel):
            ax.clear()

            # 測量点のプロット
            if self.points_df is not None and not self.points_df.empty:
                ax.scatter(self.points_df['X座標'],
                           self.points_df['Y座標'],
                           color='blue',
                           marker='^',
                           label='測量点',
                           alpha=0.3)  # 通常の点は透明度を下げる

            # 選択した写真の位置をプロット
            if photo_filename in self.photo_gps_data and 'x_coord' in self.photo_gps_data[
                    photo_filename]:
                photo_x = self.photo_gps_data[photo_filename]['x_coord']
                photo_y = self.photo_gps_data[photo_filename]['y_coord']
                ax.scatter([photo_x], [photo_y], color='red', marker='o', s=80, label='選択写真')

            # 画地データの結線表示（薄く表示）
            if hasattr(self, 'landparcels') and self.landparcels:
                for landparcel in self.landparcels:
                    points = landparcel['ポイント']
                    landparcel_coords = []

                    for point_name in points:
                        point = self.points_df[(self.points_df['点名'] == point_name) |
                                               (self.points_df['点番'] == point_name)]
                        if not point.empty:
                            landparcel_coords.append((point.iloc[0]['X座標'], point.iloc[0]['Y座標']))

                    if len(landparcel_coords) > 2:
                        landparcel_coords.append(landparcel_coords[0])
                        xs, ys = zip(*landparcel_coords)

                        # 選択された画地かどうかで色とスタイルを変える
                        if landparcel['画地番号'] == selected_landparcel['画地番号']:
                            ax.plot(xs, ys, color='green', linestyle='-', linewidth=2, alpha=1.0)

                            # 選択された画地のポイントをハイライト表示
                            point_xs = [x for x, _ in landparcel_coords[:-1]]
                            point_ys = [y for _, y in landparcel_coords[:-1]]
                            ax.scatter(point_xs,
                                       point_ys,
                                       color='green',
                                       marker='*',
                                       s=150,
                                       label='画地ポイント',
                                       zorder=10)

                            # ポイント名を表示
                            for i, (x, y) in enumerate(zip(point_xs, point_ys)):
                                if i < len(selected_landparcel['ポイント']):
                                    point_name = selected_landparcel['ポイント'][i]
                                    ax.annotate(point_name, (x, y),
                                                xytext=(5, 5),
                                                textcoords='offset points',
                                                fontsize=8,
                                                backgroundcolor='white',
                                                alpha=0.7)
                        else:
                            ax.plot(xs, ys, color='gray', linestyle='-', alpha=0.2)

            # グリッドと凡例を表示
            ax.grid(True)
            ax.legend(loc='upper right', fontsize=8)

            # タイトル更新
            ax.set_title(f"選択画地: {selected_landparcel['画地名']}", fontsize=10)

            # 選択した画地の範囲を表示
            landparcel_points = []
            for point_name in selected_landparcel['ポイント']:
                point = self.points_df[(self.points_df['点名'] == point_name) |
                                       (self.points_df['点番'] == point_name)]
                if not point.empty:
                    landparcel_points.append((point.iloc[0]['X座標'], point.iloc[0]['Y座標']))

            if landparcel_points:
                x_coords = [p[0] for p in landparcel_points]
                y_coords = [p[1] for p in landparcel_points]

                # 写真の座標も含める
                if photo_filename in self.photo_gps_data and 'x_coord' in self.photo_gps_data[
                        photo_filename]:
                    photo_x = self.photo_gps_data[photo_filename]['x_coord']
                    photo_y = self.photo_gps_data[photo_filename]['y_coord']
                    x_coords.append(photo_x)
                    y_coords.append(photo_y)

                # マージンを追加
                x_margin = (max(x_coords) - min(x_coords)) * 0.2
                y_margin = (max(y_coords) - min(y_coords)) * 0.2

                ax.set_xlim(min(x_coords) - x_margin, max(x_coords) + x_margin)
                ax.set_ylim(min(y_coords) - y_margin, max(y_coords) + y_margin)

            canvas.draw()

        # 画地データ選択イベントを設定
        landparcel_tree.bind("<<TreeviewSelect>>", on_landparcel_select)

        # 画地データダブルクリック時の処理
        def on_landparcel_double_click(event):
            selected_items = landparcel_tree.selection()
            if not selected_items:
                return

            selected_values = landparcel_tree.item(selected_items[0])['values']
            selected_id = selected_values[0]  # 画地番号

            # 選択した画地データから点を選択するダイアログを表示
            select_point_from_landparcel(selected_id)

        # 画地データから点を選択するダイアログ
        def select_point_from_landparcel(landparcel_id):
            # 選択した画地データを取得
            selected_landparcel = None
            for landparcel in self.landparcels:
                if str(landparcel['画地番号']) == str(landparcel_id):
                    selected_landparcel = landparcel
                    break

            if not selected_landparcel or not selected_landparcel['ポイント']:
                messagebox.showinfo("情報", "この画地にはポイントがありません")
                return

            # ダイアログを作成
            point_dialog = tk.Toplevel(dialog)
            point_dialog.title(f"画地「{selected_landparcel['画地名']}」からポイント選択")
            point_dialog.geometry("400x300")
            point_dialog.transient(dialog)
            point_dialog.grab_set()

            tk.Label(point_dialog,
                     text=f"画地「{selected_landparcel['画地名']}」に含まれるポイントから選択してください",
                     wraplength=380).pack(pady=10)

            # ポイントリストのフレーム
            list_frame = tk.Frame(point_dialog)
            list_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)

            # ポイントリストのスクロールバー
            scrollbar = tk.Scrollbar(list_frame)
            scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

            # ポイントリスト
            point_listbox = tk.Listbox(list_frame, yscrollcommand=scrollbar.set)
            point_listbox.pack(fill=tk.BOTH, expand=True)

            scrollbar.config(command=point_listbox.yview)

            # ポイントデータ格納用
            point_data = []

            # ポイントをリストに追加
            for point_name in selected_landparcel['ポイント']:
                point = self.points_df[(self.points_df['点名'] == point_name) |
                                       (self.points_df['点番'] == point_name)]

                if not point.empty:
                    point_id = point.iloc[0]['点番']
                    point_name = point.iloc[0]['点名']
                    x_coord = point.iloc[0]['X座標']
                    y_coord = point.iloc[0]['Y座標']

                    # 写真との距離を計算
                    distance_str = ""
                    if photo_filename in self.photo_gps_data and 'x_coord' in self.photo_gps_data[
                            photo_filename]:
                        photo_x = self.photo_gps_data[photo_filename]['x_coord']
                        photo_y = self.photo_gps_data[photo_filename]['y_coord']
                        distance = self.calculate_xy_distance(photo_x, photo_y, x_coord, y_coord)
                        distance_str = f" - {distance:.1f}m"

                    display_text = f"{point_id} - {point_name}{distance_str}"
                    point_listbox.insert(tk.END, display_text)
                    point_data.append((point_id, point_name))

            # ボタンフレーム
            button_frame = tk.Frame(point_dialog)
            button_frame.pack(pady=10)

            def on_point_confirm():
                selection = point_listbox.curselection()
                if selection:
                    idx = selection[0]
                    if 0 <= idx < len(point_data):
                        selected_point_id = point_data[idx][0]
                        selected_point_name = point_data[idx][1]

                        # ポイントツリーで該当するポイントを選択
                        for item_id in point_tree.get_children():
                            item_values = point_tree.item(item_id)['values']
                            if (str(item_values[0]) == str(selected_point_id) and
                                    str(item_values[1]) == str(selected_point_name)):
                                # 選択してスクロール
                                point_tree.selection_set(item_id)
                                point_tree.see(item_id)
                                # タブを測量点タブに切り替え
                                tab_control.select(0)
                                # 距離計算を実行
                                calculate_distances()
                                break

                    point_dialog.destroy()
                else:
                    messagebox.showwarning("警告", "ポイントが選択されていません")

            tk.Button(button_frame, text="選択", command=on_point_confirm,
                      width=10).pack(side=tk.LEFT, padx=5)
            tk.Button(button_frame, text="キャンセル", command=point_dialog.destroy,
                      width=10).pack(side=tk.LEFT, padx=5)

        # 画地データのダブルクリックイベントを設定
        landparcel_tree.bind("<Double-1>", on_landparcel_double_click)

        # 確定処理
        def confirm_selection():
            selected_items = point_tree.selection()
            if not selected_items:
                messagebox.showwarning("警告", "ポイントが選択されていません")
                return

            # 選択されたポイントを取得
            selected_values = point_tree.item(selected_items[0])['values']
            selected_point = None

            # 点番と点名で一致するポイントを探す
            for _, point in self.points_df.iterrows():
                if (str(point['点番']) == str(selected_values[0]) and
                        str(point['点名']) == str(selected_values[1])):
                    selected_point = point
                    break

            if selected_point is None:
                messagebox.showwarning("警告", "選択したポイントの情報が見つかりませんでした")
                return

            # 写真のデータを更新
            orig_photo_item_id = self.photos_tree.selection()[0]  # 元の写真リストでの選択項目
            current_values = list(self.photos_tree.item(orig_photo_item_id)['values'])

            # マッチングポイントと距離を更新
            point_identifier = selected_point['点名'] if self.use_point_name.get(
            ) else selected_point['点番']

            # XY座標での距離計算
            distance_str = "手動選択"
            if photo_filename in self.photo_gps_data and 'x_coord' in self.photo_gps_data[
                    photo_filename]:
                photo_x = self.photo_gps_data[photo_filename]['x_coord']
                photo_y = self.photo_gps_data[photo_filename]['y_coord']
                distance_xy = self.calculate_xy_distance(photo_x, photo_y, selected_point['X座標'],
                                                         selected_point['Y座標'])
                distance_str = f"{distance_xy:.1f}m (手動)"

            # 新しい遠景/近景タイプを反映
            current_values[3] = landscape_var.get()  # 遠景/近景列が3

            # マッチングポイントと距離情報を更新
            current_values[6] = point_identifier  # マッチングポイント列が6
            current_values[7] = distance_str  # 距離列が7

            # 新しいファイル名を更新
            new_filename = self.create_filename(point_identifier, photo_filename,
                                                landscape_var.get())
            current_values[1] = new_filename

            # ツリービューの更新
            self.photos_tree.item(orig_photo_item_id, values=current_values)

            dialog.destroy()

        def cancel_operation():
            dialog.destroy()

        # ポイントのダブルクリックで確定するイベント
        def on_point_double_click(event):
            confirm_selection()

        point_tree.bind("<Double-1>", on_point_double_click)

        # 確定・キャンセルボタン - ボタンフレーム内に配置して常に見えるようにする
        confirm_button = tk.Button(button_frame,
                                   text="確定",
                                   command=confirm_selection,
                                   width=20,
                                   height=2,
                                   bg="#4CAF50",
                                   fg="white",
                                   font=("", 10, "bold"))
        confirm_button.pack(side=tk.RIGHT, padx=20, pady=10)

        cancel_button = tk.Button(button_frame,
                                  text="キャンセル",
                                  command=cancel_operation,
                                  width=15,
                                  height=2,
                                  bg="#f44336",
                                  fg="white",
                                  font=("", 10))
        cancel_button.pack(side=tk.RIGHT, padx=5, pady=10)

        # 状態表示ラベル
        tk.Label(button_frame, text="ポイントを選択して確定してください", bg="#e0e0e0").pack(side=tk.LEFT, padx=20)

        # ドラッグ＆ドロップのために必要な変数とメソッド
        drag_data = {"item": None, "source": None}

        # ドラッグ開始
        def start_drag(event, tree, source_type):
            item = tree.identify_row(event.y)
            if item:
                drag_data["item"] = tree.item(item)["values"]
                drag_data["source"] = source_type

        # ドラッグ終了
        def stop_drag(event, target_tree, target_type):
            if drag_data["item"] is None or drag_data["source"] is None:
                return

            # ドロップ先のアイテムを特定
            item = target_tree.identify_row(event.y)
            if not item:
                return

            # 画地からポイントへのドラッグ
            if drag_data["source"] == "landparcel" and target_type == "point":
                landparcel_id = drag_data["item"][0]
                select_point_from_landparcel(landparcel_id)

            # ポイントから画地へのドラッグ（何もしない）
            # 必要に応じて実装

            # クリア
            drag_data["item"] = None
            drag_data["source"] = None

        # 画地リストのドラッグ開始
        landparcel_tree.bind("<ButtonPress-1>",
                             lambda event: start_drag(event, landparcel_tree, "landparcel"))

        # ポイントリストのドラッグ終了
        point_tree.bind("<ButtonRelease-1>", lambda event: stop_drag(event, point_tree, "point"))

    def select_sim_file(self):
        file_path = filedialog.askopenfilename(filetypes=[("SIMファイル", "*.sim")])
        if file_path:
            self.sim_file_path.set(file_path)
            self.load_sim_points(file_path)

    def load_sim_points(self, file_path):
        try:
            # 以前のポイントをクリア
            for i in self.points_tree.get_children():
                self.points_tree.delete(i)

            encodings = ['shift-jis', 'utf-8', 'cp932', 'euc-jp']

            for encoding in encodings:
                try:
                    with open(file_path, 'r', encoding=encoding) as file:
                        content = file.read()

                    # 測量点データの正規表現パターン
                    point_pattern = re.compile(
                        r'A01,\s*(\d+|[^\s,]+),\s*([^,]+),\s*(-?\d+\.\d+),\s*(-?\d+\.\d+)')

                    # 画地データの正規表現パターン（より柔軟に）
                    landparcel_pattern = re.compile(r'A02,\s*(\d+|[^\s,]+),\s*([^,]+),\s*(.+)$')

                    points = []
                    landparcels = []
                    landparcel_points = {}

                    # 測量点データの処理
                    for match in point_pattern.finditer(content):
                        point_num, point_name, x_coord, y_coord = match.groups()

                        points.append({
                            '点番': point_num,
                            '点名': point_name.strip(),
                            'X座標': float(x_coord),
                            'Y座標': float(y_coord)
                        })

                    # 画地データの処理
                    for match in landparcel_pattern.finditer(content):
                        landparcel_id, landparcel_name, point_list = match.groups()
                        points_in_landparcel = [p.strip() for p in point_list.split()]

                        landparcels.append({
                            '画地番号': landparcel_id,
                            '画地名': landparcel_name,
                            'ポイント': points_in_landparcel
                        })

                        landparcel_points[landparcel_id] = points_in_landparcel

                    if points:
                        self.points_df = pd.DataFrame(points)
                        self.landparcels = landparcels
                        self.landparcel_points = landparcel_points

                        # 座標タイプによって処理を分岐
                        if hasattr(self, 'coord_type') and self.coord_type.get() == "latlon":
                            # すでに緯度経度の場合：直接X/Y座標に変換
                            self.points_df['経度'] = self.points_df['X座標']  # 経度→X座標
                            self.points_df['緯度'] = self.points_df['Y座標']  # 緯度→Y座標
                            self.gps_to_xy_for_points()
                            print("緯度経度からXY座標に変換")
                        else:
                            # 平面直角座標の場合：そのまま使用
                            print("平面直角座標として直接使用")

                        # ポイント一覧をTreeviewに表示
                        for _, row in self.points_df.iterrows():
                            self.points_tree.insert('',
                                                    'end',
                                                    values=(row['点番'], row['点名'],
                                                            f"{row['X座標']:.3f}",
                                                            f"{row['Y座標']:.3f}"))

                        # 画地データのログ表示
                        if landparcels:
                            print(f"{len(landparcels)}件の画地データを読み込みました")
                            for lp in landparcels:
                                print(f"  画地: {lp['画地名']} - ポイント数: {len(lp['ポイント'])}")

                        # 地図を更新
                        self.update_map()

                        return
                except (UnicodeDecodeError, IOError):
                    continue
                except Exception as e:
                    messagebox.showerror("エラー", f"ファイル解析中にエラーが発生しました: {e}")
                    return

            messagebox.showerror("エラー", "ファイルを解析できませんでした。")

        except Exception as e:
            messagebox.showerror("エラー", str(e))

    def gps_to_xy_for_points(self):
        """ポイントの緯度経度をXY座標に変換（JGD2011）"""
        if self.points_df is None or '経度' not in self.points_df.columns or '緯度' not in self.points_df.columns:
            return

        try:
            # 選択された系に基づく平面直角座標系のEPSGコード（JGD2011）
            system = int(self.coord_system.get())
            epsg_code = 6668 + system

            # GPS座標系（WGS84）のEPSGコード
            gps_epsg = 4326

            # 座標変換器を作成（WGS84からJGD2011平面直角座標系へ）
            transformer = Transformer.from_crs(
                f"EPSG:{gps_epsg}",  # 入力：WGS84経緯度（GPS）
                f"EPSG:{epsg_code}",  # 出力：JGD2011平面直角座標系
                always_xy=True  # 常にlon,lat（度）からx,y（メートル）の順で変換
            )

            # 座標変換を実行
            xy_coords = []
            for _, row in self.points_df.iterrows():
                try:
                    # 経度をX座標、緯度をY座標に変換
                    x, y = transformer.transform(row['経度'], row['緯度'])
                    xy_coords.append((x, y))
                except Exception as e:
                    print(f"点の座標変換エラー: {e}")
                    xy_coords.append((None, None))

            # 変換結果をDataFrameに格納
            self.points_df['X座標'] = [coord[0] for coord in xy_coords]  # 経度→X座標
            self.points_df['Y座標'] = [coord[1] for coord in xy_coords]  # 緯度→Y座標

        except Exception as e:
            messagebox.showerror("変換エラー", f"緯度経度→XY座標変換中にエラーが発生しました: {e}")

    def convert_gps_to_xy(self):
        """GPS緯度経度を平面直角座標に変換（JGD2011に変換）"""
        if not self.photo_gps_data:
            messagebox.showinfo("情報", "変換するGPSデータがありません")
            return

        try:
            # 選択された系に基づく平面直角座標系のEPSGコード（JGD2011）
            system = int(self.coord_system.get())
            epsg_code = 6668 + system

            # GPS座標系（WGS84）のEPSGコード
            gps_epsg = 4326

            # 座標変換器を作成（WGS84からJGD2011平面直角座標系へ）
            transformer = Transformer.from_crs(
                f"EPSG:{gps_epsg}",  # 入力：WGS84経緯度（GPS）
                f"EPSG:{epsg_code}",  # 出力：JGD2011平面直角座標系
                always_xy=True  # 常にlon,lat（度）からx,y（メートル）の順で変換
            )

            # 写真のGPS座標を変換して保存
            converted_count = 0
            for photo_name, gps_data in self.photo_gps_data.items():
                lat = gps_data.get('latitude')
                lon = gps_data.get('longitude')

                if lat is not None and lon is not None:
                    try:
                        # 経度をX座標、緯度をY座標に変換
                        x, y = transformer.transform(lon, lat)

                        # 変換結果を保存
                        gps_data['x_coord'] = x  # 経度→X座標
                        gps_data['y_coord'] = y  # 緯度→Y座標
                        converted_count += 1
                    except Exception as e:
                        print(f"GPS座標変換エラー ({photo_name}): {e}")

            # TreeViewの更新
            for item_id in self.photos_tree.get_children():
                values = list(self.photos_tree.item(item_id)['values'])
                photo_name = values[0]

                if photo_name in self.photo_gps_data and 'x_coord' in self.photo_gps_data[
                        photo_name]:
                    # X座標、Y座標の列に値を設定
                    x_coord = self.photo_gps_data[photo_name]['x_coord']
                    y_coord = self.photo_gps_data[photo_name]['y_coord']

                    # 表示用にフォーマット
                    values[4] = f"{x_coord:.3f}"  # X座標（列インデックス4）
                    values[5] = f"{y_coord:.3f}"  # Y座標（列インデックス5）

                    self.photos_tree.item(item_id, values=values)

            messagebox.showinfo(
                "変換完了", f"{converted_count}枚の写真のGPS座標をXY座標（JGD2011）に変換しました\n系番号: {system}系")
            print("GPS座標をXY座標（JGD2011）に変換完了")

            # 地図を更新
            self.update_map()

        except Exception as e:
            messagebox.showerror("変換エラー", f"GPS座標の変換中にエラーが発生しました: {e}")

    def select_photo_directory(self):
        directory = filedialog.askdirectory()
        if directory:
            self.photo_directory.set(directory)
            self.load_photos(directory)

    def load_photos(self, directory):
        # 写真ファイルの読み込み
        photo_extensions = ['.jpg', '.jpeg', '.png', '.tif', '.tiff']
        self.photos = [
            f for f in os.listdir(directory) if os.path.splitext(f)[1].lower() in photo_extensions
        ]

        # 写真一覧とその遠景/近景をクリア
        for i in self.photos_tree.get_children():
            self.photos_tree.delete(i)

        # 写真ごとのGPSデータを格納する辞書をクリア
        self.photo_gps_data = {}
        self.photo_dates = {}

        # 写真一覧をTreeviewに表示
        for photo in self.photos:
            full_path = os.path.join(directory, photo)

            # GPS情報と撮影日時の取得
            exif_data = self.extract_exif_data(full_path)
            lat, lon = None, None
            date_time = None

            if exif_data:
                # GPS情報の取得
                gps_info = self.extract_gps_from_exif(exif_data)
                if gps_info and 'GPSLatitude' in gps_info and 'GPSLongitude' in gps_info:
                    y_coord = gps_info['GPSLatitude']
                    x_coord = gps_info['GPSLongitude']
                    self.photo_gps_data[photo] = {'latitude': y_coord, 'longitude': x_coord}
                # 撮影日時の取得
                if 'DateTimeOriginal' in exif_data:
                    date_time_str = exif_data['DateTimeOriginal']
                    try:
                        date_time = datetime.strptime(date_time_str, '%Y:%m:%d %H:%M:%S')
                        self.photo_dates[photo] = date_time
                    except:
                        date_time = None

            # 日時が取得できなければファイルの更新日時を使用
            if date_time is None:
                date_time = datetime.fromtimestamp(os.path.getmtime(full_path))
                self.photo_dates[photo] = date_time

            date_time_str = date_time.strftime('%Y/%m/%d %H:%M:%S') if date_time else "不明"

            # 画像の遠景/近景分類
            landscape_type = self.classify_landscape(full_path)

            # 初期状態での新ファイル名は元のものと同じ
            new_filename = photo

            # 写真一覧に追加
            self.photos_tree.insert(
                '',
                'end',
                values=(
                    photo,  # 元ファイル名
                    new_filename,  # 新ファイル名
                    date_time_str,  # 撮影日時
                    landscape_type,  # 遠景/近景
                    "",  # X座標
                    "",  # Y座標
                    "未マッチング",  # マッチングポイント
                    ""  # 距離(m)
                ))

        # 並べ替えを実行
        self.sort_photos()

        # GPS座標を平面直角座標に自動変換
        if self.photo_gps_data:
            self.convert_gps_to_xy()

        # 地図を更新
        self.update_map()

        # ポイントと写真のデータがあれば自動マッチング
        if self.points_df is not None and self.photos:
            self.match_photos_to_points_xy()  # XY座標でのマッチングを実行

    def extract_exif_data(self, image_path):
        """写真からEXIF情報を抽出"""
        try:
            image = Image.open(image_path)
            exif_data = {}

            if hasattr(image, '_getexif'):
                exif = image._getexif()
                if exif:
                    for tag, value in exif.items():
                        tag_name = TAGS.get(tag, tag)
                        exif_data[tag_name] = value

            return exif_data

        except Exception as e:
            print(f"EXIF抽出エラー: {e}")

        return None

    def extract_gps_from_exif(self, exif_data):
        """EXIF情報からGPS情報を抽出"""
        try:
            if 'GPSInfo' in exif_data:
                gps_info = {}

                for key, value in exif_data['GPSInfo'].items():
                    tag_name = GPSTAGS.get(key, key)
                    gps_info[tag_name] = value

                # 緯度経度を度分秒から10進数に変換
                if 'GPSLatitude' in gps_info and 'GPSLongitude' in gps_info:
                    lat_ref = gps_info.get('GPSLatitudeRef', 'N')
                    lon_ref = gps_info.get('GPSLongitudeRef', 'E')

                    lat = self.convert_to_decimal(gps_info['GPSLatitude'])
                    lon = self.convert_to_decimal(gps_info['GPSLongitude'])

                    if lat_ref == 'S':
                        lat = -lat
                    if lon_ref == 'W':
                        lon = -lon

                    gps_info['GPSLatitude'] = lat
                    gps_info['GPSLongitude'] = lon

                    return gps_info

        except Exception as e:
            print(f"GPS抽出エラー: {e}")

        return None

    def convert_to_decimal(self, dms):
        """度分秒形式の座標を10進数に変換"""
        # 度, 分, 秒
        degrees = dms[0]
        minutes = dms[1]
        seconds = dms[2]

        if isinstance(degrees, tuple):
            degrees = float(degrees[0]) / float(degrees[1])
        if isinstance(minutes, tuple):
            minutes = float(minutes[0]) / float(minutes[1])
        if isinstance(seconds, tuple):
            seconds = float(seconds[0]) / float(seconds[1])

        return degrees + (minutes / 60.0) + (seconds / 3600.0)

    def classify_landscape(self, image_path):
        """画像の遠景/近景を判定するメソッド"""
        try:
            # OpenCVで画像読み込み
            img = cv2.imread(image_path)
            height, width = img.shape[:2]

            # グレースケール変換
            gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)

            # エッジ検出（改良版）
            edges = cv2.Canny(gray, 50, 150)
            edge_count = np.sum(edges > 0)
            edge_density = edge_count / (height * width)

            # テクスチャ解析（Gray-Level Co-occurrence Matrix）
            glcm = graycomatrix(gray, [1], [0], levels=256, symmetric=True, normed=True)
            contrast = graycoprops(glcm, 'contrast')[0, 0]

            # 空の検出（HSVカラースペース）
            hsv = cv2.cvtColor(img, cv2.COLOR_BGR2HSV)
            sky_mask = cv2.inRange(hsv, (90, 50, 50), (130, 255, 255))
            sky_ratio = np.sum(sky_mask > 0) / (height * width)

            # 色彩の空間分布
            color_variance = np.var(img, axis=(0, 1)).mean()

            # 判定ロジック（多角的アプローチ）
            score = ((1 if edge_density < 0.05 else 0) +  # エッジの少なさ
                     (1 if contrast < 50 else 0) +  # テクスチャの単純さ
                     (1 if sky_ratio > 0.3 else 0) +  # 空の面積
                     (1 if color_variance < 30 else 0)  # 色彩の均一性
                    )

            return "遠景" if score >= 2 else "近景"

        except Exception as e:
            print(f"画像解析エラー: {e}")
            return "不明"

    def calculate_xy_distance(self, x1, y1, x2, y2):
        """平面直角座標間の距離を計算（メートル単位）"""
        try:
            if x1 is None or y1 is None or x2 is None or y2 is None:
                return float('inf')

            # ユークリッド距離
            return math.sqrt((x2 - x1)**2 + (y2 - y1)**2)

        except Exception:
            return float('inf')

    def create_filename(self, identifier, original_filename, landscape_type):
        """新しいファイル名を生成"""
        name, ext = os.path.splitext(original_filename)

        if self.use_landscape_suffix.get():
            suffix = "-1" if landscape_type == "遠景" else "-2"
            return f"{identifier}{suffix}{ext}"
        else:
            return f"{identifier}{ext}"

    def match_photos_to_points_xy(self):
        """写真と測量点をXY座標に基づいてマッチング"""
        if self.points_df is None:
            messagebox.showwarning("警告", "測量点データが不足しています")
            return

        # 変換されているかチェック
        no_coords = True
        for photo_name, gps_data in self.photo_gps_data.items():
            if 'x_coord' in gps_data:
                no_coords = False
                break

        if no_coords:
            result = messagebox.askyesno("確認", "写真のGPS座標がXY座標に変換されていません。変換を実行しますか？")
            if result:
                self.convert_gps_to_xy()
            else:
                return

        # マッチング確認ダイアログ
        confirm = messagebox.askyesno(
            "マッチング確認", f"XY座標を使用して写真とポイントをマッチングします。\n"
            f"マッチング距離: {self.matching_distance.get()}m\n"
            f"座標系: {self.coord_system.get()}系\n"
            f"続行しますか？")
        if not confirm:
            return

        max_distance = self.matching_distance.get()
        matched_count = 0

        for item_id in self.photos_tree.get_children():
            values = list(self.photos_tree.item(item_id)['values'])
            photo_name = values[0]
            landscape_type = values[3]  # 遠景/近景が3列目

            if photo_name in self.photo_gps_data and 'x_coord' in self.photo_gps_data[photo_name]:
                # 写真のX座標、Y座標を取得
                photo_x = self.photo_gps_data[photo_name]['x_coord']
                photo_y = self.photo_gps_data[photo_name]['y_coord']

                # 最も近い測量点を見つける
                closest_point = None
                min_distance = float('inf')

                for _, point in self.points_df.iterrows():
                    # 測量点のX座標、Y座標と比較
                    distance = self.calculate_xy_distance(photo_x, photo_y, point['X座標'],
                                                          point['Y座標'])

                    if distance < min_distance:
                        min_distance = distance
                        closest_point = point

                # 一定距離以内の点を関連付け
                if closest_point is not None and min_distance <= max_distance:
                    # 使用する識別子を選択
                    identifier = closest_point['点名'] if self.use_point_name.get(
                    ) else closest_point['点番']

                    # 新しいファイル名を生成
                    # 新しいファイル名を生成
                    new_filename = self.create_filename(identifier, photo_name, landscape_type)

                    # ツリービューを更新
                    values[1] = new_filename
                    values[6] = identifier  # マッチングポイント列が6
                    values[7] = f"{min_distance:.1f}m"  # 距離列が7

                    self.photos_tree.item(item_id, values=values)

                    matched_count += 1
                else:
                    # マッチング範囲外の場合
                    values[1] = photo_name  # 元のファイル名のまま
                    values[6] = "範囲外"  # マッチングポイント列が6
                    values[7] = f"{min_distance:.1f}m" if min_distance != float('inf') else "不明"

                    self.photos_tree.item(item_id, values=values)
            else:
                # XY座標がない場合
                values[1] = photo_name  # 元のファイル名のまま
                values[6] = "座標なし"  # マッチングポイント列が6
                values[7] = ""  # 距離列が7

                self.photos_tree.item(item_id, values=values)

        # 地図を更新
        self.update_map()

        if matched_count > 0:
            messagebox.showinfo("マッチング完了", f"{matched_count}枚の写真がXY座標でマッチングされました")
        else:
            messagebox.showwarning("マッチング", "マッチングできる写真がありませんでした")

    def rename_photos_to_new_folder(self):
        """マッチングされた写真を新規フォルダにリネームしてコピー"""
        if not self.photos:
            messagebox.showinfo("情報", "リネームする写真がありません")
            return

        # 写真のディレクトリ
        directory = self.photo_directory.get()
        if not directory:
            messagebox.showwarning("警告", "写真フォルダが選択されていません")
            return

        # 新規フォルダ作成
        time_str = time.strftime('%Y%m%d_%H%M%S')
        renamed_folder = os.path.join(directory, f"renamed_{time_str}")
        os.makedirs(renamed_folder, exist_ok=True)

        # リネームとコピー
        renamed_count = 0
        skipped_count = 0

        for item_id in self.photos_tree.get_children():
            values = self.photos_tree.item(item_id)['values']
            original_filename = values[0]
            new_filename = values[1]
            matching_point = values[6]

            # マッチングされたファイルのみコピー
            if matching_point not in ["未マッチング", "範囲外", "GPS情報なし", "座標なし"]:
                original_path = os.path.join(directory, original_filename)
                new_path = os.path.join(renamed_folder, new_filename)

                # 重複ファイル名の処理
                counter = 1
                base_new_filename = new_filename
                while os.path.exists(new_path):
                    name, ext = os.path.splitext(base_new_filename)
                    new_filename = f"{name}_{counter}{ext}"
                    new_path = os.path.join(renamed_folder, new_filename)
                    counter += 1

                try:
                    # ファイルをコピー
                    shutil.copy2(original_path, new_path)
                    renamed_count += 1
                except Exception as e:
                    messagebox.showerror("コピーエラー", f"ファイル {original_filename} のコピーに失敗しました: {e}")
            else:
                skipped_count += 1

        if renamed_count > 0:
            message = f"{renamed_count}枚の写真を新規フォルダ「{renamed_folder}」にコピーしました"
            if skipped_count > 0:
                message += f"\n{skipped_count}枚の写真はマッチングされていないためスキップしました"

            messagebox.showinfo("完了", message)

            # リネーム後の新しいフォルダを開く
            try:
                os.startfile(renamed_folder)
            except Exception:
                pass
        else:
            messagebox.showinfo("完了", "コピーする写真がありませんでした")

    # update_map メソッドの修正 - 画地データをトップ画面にも表示し、結線順を保持
    def update_map(self):
        """測量点と写真の位置を地図上に表示 (XY座標ベース)"""
        try:
            # 前の描画をクリア
            self.ax.clear()

            has_data = False

            # 測量点のプロット
            if self.points_df is not None and not self.points_df.empty:
                # XY座標でプロット（X座標, Y座標の順で）
                self.ax.scatter(self.points_df['X座標'],
                                self.points_df['Y座標'],
                                color='blue',
                                marker='^',
                                label='測量点',
                                zorder=2)

                # 点番または点名をラベル表示
                for _, point in self.points_df.iterrows():
                    label = point['点名'] if self.use_point_name.get() else point['点番']
                    self.ax.annotate(label, (point['X座標'], point['Y座標']),
                                     fontsize=8,
                                     xytext=(3, 3),
                                     textcoords='offset points')
                has_data = True

            # 写真の位置をプロット
            photo_positions = []
            for photo_name, gps_data in self.photo_gps_data.items():
                if 'x_coord' in gps_data and 'y_coord' in gps_data:
                    photo_positions.append((gps_data['x_coord'], gps_data['y_coord'], photo_name))

            if photo_positions:
                x_positions = [pos[0] for pos in photo_positions]
                y_positions = [pos[1] for pos in photo_positions]

                self.ax.scatter(x_positions,
                                y_positions,
                                color='red',
                                marker='o',
                                label='写真',
                                alpha=0.7,
                                zorder=1)
                has_data = True

            # 画地データの結線表示 - 取り込み順で結線する
            if hasattr(self, 'landparcels') and self.landparcels:
                for landparcel in self.landparcels:
                    points = landparcel['ポイント']
                    landparcel_coords = []

                    # 画地の各ポイントを取り込み順に処理
                    for point_name in points:
                        point = self.points_df[(self.points_df['点名'] == point_name) |
                                               (self.points_df['点番'] == point_name)]

                        if not point.empty:
                            landparcel_coords.append((point.iloc[0]['X座標'], point.iloc[0]['Y座標']))

                    # 閉じた多角形として結線（最後の点と最初の点を結ぶ）
                    if len(landparcel_coords) > 2:
                        # 最初の点に戻る閉じた線にする
                        landparcel_coords.append(landparcel_coords[0])
                        xs, ys = zip(*landparcel_coords)

                        # より見やすいスタイルで描画
                        self.ax.plot(xs, ys, color='green', linestyle='-', linewidth=2, alpha=0.7)

                        # 各点にマーカーと番号を表示
                        for i, (x, y) in enumerate(landparcel_coords[:-1]):  # 最後の点（最初と同じ）は除く
                            self.ax.plot(x, y, 'go', markersize=6)  # 緑の点
                            # 点の順番を表示
                            self.ax.annotate(str(i + 1), (x, y),
                                             xytext=(5, 5),
                                             textcoords='offset points',
                                             color='green',
                                             fontweight='bold')

                        # 画地名を表示
                        center_x = sum(x for x, _ in landparcel_coords) / len(landparcel_coords)
                        center_y = sum(y for _, y in landparcel_coords) / len(landparcel_coords)
                        self.ax.annotate(landparcel['画地名'], (center_x, center_y),
                                         fontsize=10,
                                         ha='center',
                                         va='center',
                                         bbox=dict(boxstyle="round,pad=0.3", fc="white", alpha=0.7))

            # 範囲設定
            if has_data:
                all_x = []
                all_y = []

                # 測量点の座標を追加
                if self.points_df is not None and not self.points_df.empty:
                    all_x.extend(self.points_df['X座標'].tolist())
                    all_y.extend(self.points_df['Y座標'].tolist())

                # 写真の座標を追加
                for pos in photo_positions:
                    all_x.append(pos[0])
                    all_y.append(pos[1])

                if all_x and all_y:
                    # 範囲をちょっと広めに
                    x_margin = (max(all_x) - min(all_x)) * 0.1
                    y_margin = (max(all_y) - min(all_y)) * 0.1

                    self.ax.set_xlim(min(all_x) - x_margin, max(all_x) + x_margin)
                    self.ax.set_ylim(min(all_y) - y_margin, max(all_y) + y_margin)

            # 凡例とグリッド
            if has_data:
                self.ax.legend()
            self.ax.grid(True)

            # タイトルと軸ラベル
            self.ax.set_title('測量点と写真の位置 (XY座標)')
            self.ax.set_xlabel('Y座標 (m)')
            self.ax.set_ylabel('X座標 (m)')

            # グラフを再描画
            self.canvas.draw()

        except Exception as e:
            print(f"地図更新エラー: {e}")
            messagebox.showerror("地図更新エラー", f"地図の更新中にエラーが発生しました: {e}")

    # GPS座標からXY座標への変換処理の修正 - X座標とY座標の入れ替え問題修正
    def convert_gps_to_xy(self):
        """GPS緯度経度を平面直角座標に変換（JGD2011に変換）"""
        if not self.photo_gps_data:
            messagebox.showinfo("情報", "変換するGPSデータがありません")
            return

        try:
            # 選択された系に基づく平面直角座標系のEPSGコード（JGD2011）
            system = int(self.coord_system.get())
            epsg_code = 6668 + system

            # GPS座標系（WGS84）のEPSGコード
            gps_epsg = 4326

            # 座標変換器を作成（WGS84からJGD2011平面直角座標系へ）
            transformer = Transformer.from_crs(
                f"EPSG:{gps_epsg}",  # 入力：WGS84経緯度（GPS）
                f"EPSG:{epsg_code}",  # 出力：JGD2011平面直角座標系
                always_xy=True  # 常にlon,lat（度）からx,y（メートル）の順で変換
            )

            # 写真のGPS座標を変換して保存
            converted_count = 0
            for photo_name, gps_data in self.photo_gps_data.items():
                lat = gps_data.get('latitude')
                lon = gps_data.get('longitude')

                if lat is not None and lon is not None:
                    try:
                        # 経度をX座標、緯度をY座標に変換
                        x, y = transformer.transform(lon, lat)

                        # 変換結果を正しい順序で保存
                        gps_data['x_coord'] = x  # 経度→X座標
                        gps_data['y_coord'] = y  # 緯度→Y座標
                        converted_count += 1
                    except Exception as e:
                        print(f"GPS座標変換エラー ({photo_name}): {e}")

            # TreeViewの更新
            for item_id in self.photos_tree.get_children():
                values = list(self.photos_tree.item(item_id)['values'])
                photo_name = values[0]

                if photo_name in self.photo_gps_data and 'x_coord' in self.photo_gps_data[
                        photo_name]:
                    # X座標、Y座標の列に値を設定
                    x_coord = self.photo_gps_data[photo_name]['x_coord']
                    y_coord = self.photo_gps_data[photo_name]['y_coord']

                    # 表示用にフォーマット
                    values[4] = f"{x_coord:.3f}"  # X座標（列インデックス4）
                    values[5] = f"{y_coord:.3f}"  # Y座標（列インデックス5）

                    self.photos_tree.item(item_id, values=values)

            messagebox.showinfo(
                "変換完了", f"{converted_count}枚の写真のGPS座標をXY座標（JGD2011）に変換しました\n系番号: {system}系")
            print("GPS座標をXY座標（JGD2011）に変換完了")

            # 地図を更新
            self.update_map()

        except Exception as e:
            messagebox.showerror("変換エラー", f"GPS座標の変換中にエラーが発生しました: {e}")

    def on_button_press(self, event):
        """ドラッグ開始処理（写真とポイント両方で使用）"""
        self.drag_start_widget = event.widget
        self.drag_start_item = self.drag_start_widget.identify_row(event.y)

        if not self.drag_start_item:
            return

        if self.drag_start_widget == self.photos_tree:
            # 写真からのドラッグ
            self.dragged_photo = self.photos_tree.item(self.drag_start_item)['values']
            if hasattr(self, 'dragged_point'):
                del self.dragged_point

        elif self.drag_start_widget == self.points_tree:
            # ポイントからのドラッグ
            self.dragged_point = self.points_tree.item(self.drag_start_item)['values']
            if hasattr(self, 'dragged_photo'):
                del self.dragged_photo

    def on_button_release(self, event):
        """ドロップ処理（写真とポイント両方で使用）"""
        drop_widget = event.widget
        drop_item = drop_widget.identify_row(event.y)

        if not drop_item or not hasattr(self, 'drag_start_widget'):
            return

        # 写真からポイントへのドラッグ
        if (hasattr(self, 'dragged_photo') and self.drag_start_widget == self.photos_tree and
                drop_widget == self.points_tree):
            # on_point_drop_photo の処理
            self.on_point_drop_photo(event)

        # ポイントから写真へのドラッグ
        elif (hasattr(self, 'dragged_point') and self.drag_start_widget == self.points_tree and
              drop_widget == self.photos_tree):
            # on_photo_drop の処理
            self.on_point_drop(event)

    def on_drag_start(self, event):
        # ドラッグ開始地点を記録
        self.drag_start_widget = event.widget
        self.drag_start_item = self.drag_start_widget.identify_row(event.y)

    def on_point_drag_start(self, event):
        # ポイントツリーでのドラッグ開始
        self.on_drag_start(event)
        # ドラッグ中のポイント情報を取得
        self.dragged_point = self.points_tree.item(self.drag_start_item)['values']

    def on_point_drop(self, event):
        # ドラッグ先が写真ツリーであることを確認
        if not hasattr(self, 'drag_start_widget') or not hasattr(self, 'dragged_point'):
            return

        # 写真ツリーにドロップされたか確認
        drop_widget = event.widget
        if drop_widget != self.photos_tree:
            return

        # ドロップされた写真アイテムを特定
        drop_item = drop_widget.identify_row(event.y)
        if not drop_item:
            return

        # 写真とポイントの情報を取得
        photo_values = list(self.photos_tree.item(drop_item)['values'])
        photo_name = photo_values[0]
        landscape_type = photo_values[3]

        # ポイント情報から識別子を作成
        identifier = self.dragged_point[1] if self.use_point_name.get() else self.dragged_point[0]

        # 新しいファイル名を生成
        new_filename = self.create_filename(identifier, photo_name, landscape_type)

        # 写真ツリーを更新
        photo_values[1] = new_filename  # 新ファイル名
        photo_values[6] = identifier  # マッチングポイント
        photo_values[7] = "手動選択"  # 距離

        self.photos_tree.item(drop_item, values=photo_values)

        # リセット
        del self.drag_start_widget
        del self.dragged_point

        # 操作のフィードバック
        messagebox.showinfo("ドラッグ&ドロップ", f"点「{identifier}」を写真「{photo_name}」に割り当てました")


def main():
    root = tk.Tk()
    app = PySimPhotoRenamerAdvanced(root)
    root.mainloop()


if __name__ == "__main__":
    main()
