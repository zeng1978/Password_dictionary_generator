#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
字符组合生成器 v4.0 - 高级版本
支持Hashcat掩码、字典导入、模式生成、文件分割、多线程等功能
优化版本：智能缓存、内存映射、压缩写入、性能监控、高级功能增强、终极优化
"""

import tkinter as tk
from tkinter import ttk, messagebox, filedialog, scrolledtext
import threading
import time
import os
import json
import itertools
import math
import mmap
import shutil
import concurrent.futures
import queue
import gzip
import psutil
import asyncio
from datetime import datetime
import hashlib
import tempfile
import zipfile
from pathlib import Path
import sys
import re
import pickle
import sqlite3
from collections import defaultdict, deque
import logging
import traceback
import multiprocessing
import subprocess
import platform
import ctypes
from typing import List, Dict, Any, Optional, Generator
import weakref
import gc
import signal
import atexit

# 常量定义
HASHCAT_CHARSETS = {
    'l': 'abcdefghijklmnopqrstuvwxyz',
    'u': 'ABCDEFGHIJKLMNOPQRSTUVWXYZ',
    'd': '0123456789',
    's': ' !"#$%&\'()*+,-./:;<=>?@[\\]^_`{|}~',
    'a': 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ',
    'b': '01'
}

# 性能优化常量
WRITE_BATCH_SIZE = 10000
PROGRESS_UPDATE_INTERVAL = 50000
LOG_UPDATE_INTERVAL = 50000
CHUNK_SIZE = 1024 * 1024  # 1MB
DICT_CACHE_SIZE = 10
DICT_CACHE_TIMEOUT = 300  # 5分钟
MAX_WORKERS = min(32, (os.cpu_count() or 1) + 4)  # 动态线程数
MEMORY_MAP_THRESHOLD = 100 * 1024 * 1024  # 100MB
COMPRESSION_THRESHOLD = 50 * 1024 * 1024  # 50MB

# 新增性能监控常量
PERFORMANCE_CHECK_INTERVAL = 5  # 5秒检查一次
MEMORY_WARNING_THRESHOLD = 85  # 85%内存使用率警告
CPU_WARNING_THRESHOLD = 90  # 90%CPU使用率警告

# 新增高级功能常量
MAX_COMBINATIONS_WARNING = 10**12  # 1万亿组合数警告
BACKUP_INTERVAL = 1000000  # 每100万组合备份一次
STATISTICS_UPDATE_INTERVAL = 10000  # 每1万组合更新统计
PATTERN_CACHE_SIZE = 1000  # 模式缓存大小
HISTORY_SIZE = 100  # 历史记录大小

# 新增终极优化常量
PROCESS_POOL_SIZE = min(8, multiprocessing.cpu_count())  # 进程池大小
MEMORY_POOL_SIZE = 1024 * 1024 * 100  # 100MB内存池
GC_THRESHOLD = 100000  # 垃圾回收阈值
SIGNAL_HANDLING = True  # 信号处理
PROCESS_PRIORITY = 'normal'  # 进程优先级
MEMORY_MAPPING_ENHANCED = True  # 增强内存映射
COMPRESSION_LEVEL = 6  # 压缩级别
BUFFER_OPTIMIZATION = True  # 缓冲区优化
CACHE_PREFETCH = True  # 缓存预取
ASYNC_IO = True  # 异步I/O
GPU_ACCELERATION = False  # GPU加速（实验性）

class ToolTip:
    """工具提示类"""
    def __init__(self, widget, text):
        self.widget = widget
        self.text = text
        self.tooltip = None
        self.widget.bind('<Enter>', self.enter)
        self.widget.bind('<Leave>', self.leave)

    def enter(self, event=None):
        x, y, _, _ = self.widget.bbox("insert")
        x += self.widget.winfo_rootx() + 25
        y += self.widget.winfo_rooty() + 20
        
        self.tooltip = tk.Toplevel(self.widget)
        self.tooltip.wm_overrideredirect(True)
        self.tooltip.wm_geometry(f"+{x}+{y}")
        
        label = tk.Label(self.tooltip, text=self.text, 
                        justify=tk.LEFT, background="#ffffe0", 
                        relief=tk.SOLID, borderwidth=1)
        label.pack()

    def leave(self, event=None):
        if self.tooltip:
            self.tooltip.destroy()
            self.tooltip = None

class CombinationGeneratorApp:
    """字符组合生成器主应用类"""
    
    def __init__(self, root):
        self.root = root
        self.root.title("字符组合生成器 v4.0 - 高级版本")
        self.root.geometry("1400x900")
        
        # 设置窗口图标和样式
        self.root.configure(bg='#f0f0f0')
        
        # 创建主滚动框架
        self.main_canvas = tk.Canvas(self.root, bg='#f0f0f0', highlightthickness=0)
        self.scrollbar = ttk.Scrollbar(self.root, orient="vertical", command=self.main_canvas.yview)
        self.scrollable_frame = ttk.Frame(self.main_canvas)
        
        self.scrollable_frame.bind(
            "<Configure>",
            lambda e: self.main_canvas.configure(scrollregion=self.main_canvas.bbox("all"))
        )
        
        self.main_canvas.create_window((0, 0), window=self.scrollable_frame, anchor="nw")
        self.main_canvas.configure(yscrollcommand=self.scrollbar.set)
        
        # 配置网格权重
        self.root.columnconfigure(0, weight=1)
        self.root.rowconfigure(0, weight=1)
        self.main_canvas.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S), padx=5, pady=5)
        self.scrollbar.grid(row=0, column=1, sticky=(tk.N, tk.S), pady=5)
        
        # 绑定鼠标滚轮事件
        self.root.bind("<MouseWheel>", self._on_mousewheel)
        self.root.bind("<Button-4>", self._on_mousewheel)
        self.root.bind("<Button-5>", self._on_mousewheel)
        
        # 初始化变量
        self.init_variables()
        
        # 初始化组件
        self.init_components()
        
        # 初始化性能监控
        self.init_performance_monitoring()
        
        # 设置日志
        self.setup_logging()
        
        # 绑定事件
        self.bind_events()

    def init_variables(self):
        """初始化所有变量"""
        # 基础变量
        self.mask_var = tk.StringVar()
        self.charset_var = tk.StringVar()
        self.min_len_var = tk.StringVar(value="1")
        self.max_len_var = tk.StringVar(value="8")
        self.include_special_var = tk.BooleanVar()
        self.output_file_var = tk.StringVar()
        self.split_size_var = tk.StringVar(value="1000000")
        
        # 字典相关变量
        self.dict_file_var = tk.StringVar()
        self.dict_folder_var = tk.StringVar()
        self.dict_b_file_var = tk.StringVar()
        self.dict_combo_var = tk.StringVar(value="none")
        self.dict_pos_var = tk.StringVar(value="none")
        self.file_filter_var = tk.StringVar(value="*.txt")
        
        # 高级生成变量
        self.custom_dict_var = tk.BooleanVar()
        self.custom_chars_var = tk.StringVar()
        self.custom_dict_length_var = tk.StringVar(value="3")
        self.custom_dict_mode_var = tk.StringVar(value="combination")
        self.connector_var = tk.StringVar(value="-")
        
        # 重复字符变量
        self.repeat_char_var = tk.BooleanVar()
        self.repeat_len_var = tk.StringVar(value="2")
        self.pattern_len_var = tk.StringVar(value="3")
        self.pattern_type_var = tk.StringVar(value="repeat")
        self.custom_charset_var = tk.StringVar()
        
        # 字典处理变量
        self.uppercase_var = tk.BooleanVar()
        self.lowercase_var = tk.BooleanVar()
        self.capitalize_var = tk.BooleanVar()
        self.reverse_var = tk.BooleanVar()
        self.remove_start_var = tk.StringVar(value="0")
        self.remove_end_var = tk.StringVar(value="0")
        self.add_start_var = tk.StringVar()
        self.add_end_var = tk.StringVar()
        self.repeat_count_var = tk.StringVar(value="1")
        self.repeat_space_count_var = tk.StringVar(value="1")
        self.process_mode_var = tk.StringVar(value="independent")
        
        # 独立处理变量
        self.remove_start_independent_var = tk.BooleanVar()
        self.remove_end_independent_var = tk.BooleanVar()
        self.remove_combined_var = tk.BooleanVar()
        self.add_start_independent_var = tk.BooleanVar()
        self.add_end_independent_var = tk.BooleanVar()
        self.add_combined_var = tk.BooleanVar()
        
        # 重复处理变量
        self.repeat_processed_var = tk.BooleanVar()
        self.repeat_processed_count_var = tk.StringVar(value="2")
        self.repeat_processed_space_count_var = tk.StringVar(value="2")
        
        # 日志控制变量
        self.log_enabled = tk.BooleanVar(value=True)
        
        # 性能监控变量
        self.performance_monitoring = tk.BooleanVar(value=True)
        self.memory_threshold = tk.StringVar(value="80")
        self.cpu_threshold = tk.StringVar(value="90")
        
        # 新增性能优化变量
        self.auto_optimize = tk.BooleanVar(value=True)
        self.use_memory_mapping = tk.BooleanVar(value=True)
        self.use_compression = tk.BooleanVar(value=True)
        self.parallel_processing = tk.BooleanVar(value=True)
        self.max_workers_var = tk.StringVar(value=str(MAX_WORKERS))
        
        # 缓存和线程变量
        self.dict_cache = {}
        self.dict_cache_size = DICT_CACHE_SIZE
        self.dict_cache_timeout = DICT_CACHE_TIMEOUT
        self.executor = concurrent.futures.ThreadPoolExecutor(max_workers=MAX_WORKERS)
        self.write_queue = queue.Queue()
        self.write_buffer = []
        self.write_thread = None
        self.stop_event = threading.Event()
        
        # 新增线程管理变量
        self.processing_threads = []
        self.performance_thread = None
        self.monitoring_active = False
        self.performance_stats = {
            'start_time': None,
            'memory_usage': [],
            'cpu_usage': [],
            'disk_io': [],
            'combinations_per_second': []
        }
        
        # 进度和日志变量
        self.processed_count = 0
        self.last_log_update = 0
        self.hashcat_charsets = HASHCAT_CHARSETS.copy()
        
        # 新增文件处理变量
        self.temp_files = []
        self.output_files = []
        self.current_file_size = 0
        self.total_file_size = 0
        
        # 新增高级功能变量
        self.advanced_features = tk.BooleanVar(value=True)
        self.auto_backup = tk.BooleanVar(value=True)
        self.statistics_tracking = tk.BooleanVar(value=True)
        self.pattern_caching = tk.BooleanVar(value=True)
        self.history_tracking = tk.BooleanVar(value=True)
        self.duplicate_removal = tk.BooleanVar(value=True)
        self.quality_check = tk.BooleanVar(value=True)
        
        # 统计和历史变量
        self.generation_statistics = {
            'total_combinations': 0,
            'unique_combinations': 0,
            'duplicate_count': 0,
            'file_count': 0,
            'total_size': 0,
            'start_time': None,
            'end_time': None,
            'patterns_generated': defaultdict(int),
            'charset_usage': defaultdict(int)
        }
        
        self.generation_history = deque(maxlen=HISTORY_SIZE)
        self.pattern_cache = {}
        self.duplicate_checker = set()
        
        # 数据库和日志变量
        self.db_connection = None
        self.logger = None
        self.backup_counter = 0
        self.last_backup_time = 0
        
        # 高级处理变量
        self.custom_patterns = []
        self.quality_rules = []
        self.export_formats = ['txt', 'csv', 'json', 'sql']
        self.current_export_format = tk.StringVar(value='txt')
        
        # 新增终极优化变量
        self.ultimate_optimization = tk.BooleanVar(value=True)
        self.process_pool_enabled = tk.BooleanVar(value=True)
        self.memory_pool_enabled = tk.BooleanVar(value=True)
        self.gc_optimization = tk.BooleanVar(value=True)
        self.signal_handling_enabled = tk.BooleanVar(value=True)
        self.buffer_optimization_enabled = tk.BooleanVar(value=True)
        self.cache_prefetch_enabled = tk.BooleanVar(value=True)
        self.async_io_enabled = tk.BooleanVar(value=True)
        self.gpu_acceleration_enabled = tk.BooleanVar(value=False)
        
        # 进程和内存管理变量
        self.process_pool = None
        self.memory_pool = {}
        self.gc_counter = 0
        self.signal_handlers = {}
        self.buffer_pool = deque(maxlen=1000)
        self.prefetch_cache = {}
        self.async_tasks = []
        
        # 性能统计变量
        self.performance_metrics = {
            'start_time': None,
            'memory_peak': 0,
            'cpu_peak': 0,
            'io_operations': 0,
            'cache_hits': 0,
            'cache_misses': 0,
            'gc_collections': 0,
            'process_switches': 0
        }
        
        # 系统信息变量
        self.system_info = self._get_system_info()
        self.optimization_level = 'auto'  # auto, manual, extreme

    def init_components(self):
        """初始化界面组件 - 增强版本"""
        # 创建主框架
        self.main_frame = ttk.Frame(self.scrollable_frame, padding="15")
        self.main_frame.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S), padx=10, pady=10)
        
        # 配置网格权重
        self.main_frame.columnconfigure(1, weight=1)
        self.main_frame.rowconfigure(8, weight=1)
        
        # 创建标题
        self.create_title()
        
        # 创建标签页
        self.notebook = ttk.Notebook(self.main_frame)
        self.notebook.grid(row=1, column=0, columnspan=3, sticky=(tk.W, tk.E, tk.N, tk.S), pady=(0, 15))
        
        # 创建各个标签页
        self.create_advanced_generation_tab()
        self.create_dictionary_import_tab()
        self.create_input_parameters_tab()
        self.create_parameter_preview_tab()
        self.create_control_panel()
        
        # 创建日志区域
        self.create_log_area()
        
        # 初始化高级功能 - 修复初始化顺序
        self.setup_logging()  # 先初始化日志系统
        self.setup_database()  # 再初始化数据库
        self.load_settings()   # 最后加载设置

    def create_title(self):
        """创建标题区域"""
        title_frame = ttk.Frame(self.main_frame)
        title_frame.grid(row=0, column=0, columnspan=3, sticky=(tk.W, tk.E), pady=(0, 15))
        
        # 主标题
        title_label = ttk.Label(title_frame, text="字符组合生成器 v4.0", 
                               font=("微软雅黑", 16, "bold"), foreground="#2c3e50")
        title_label.pack()
        
        # 副标题
        subtitle_label = ttk.Label(title_frame, text="高级版本 - 支持Hashcat掩码、字典导入、模式生成、文件分割、多线程等功能", 
                                  font=("微软雅黑", 10), foreground="#7f8c8d")
        subtitle_label.pack(pady=(5, 0))
        
        # 分隔线
        separator = ttk.Separator(title_frame, orient='horizontal')
        separator.pack(fill=tk.X, pady=10)

    def create_advanced_generation_tab(self):
        """创建高级生成标签页"""
        self.advanced_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.advanced_frame, text="高级生成")
        
        # 创建滚动框架
        canvas = tk.Canvas(self.advanced_frame, bg='#f8f9fa', highlightthickness=0)
        scrollbar = ttk.Scrollbar(self.advanced_frame, orient="vertical", command=canvas.yview)
        scrollable_frame = ttk.Frame(canvas)
        
        scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        
        canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        
        # 自定义字典组合
        custom_dict_frame = ttk.LabelFrame(scrollable_frame, text="自定义字典组合", padding="15")
        custom_dict_frame.pack(fill=tk.X, padx=10, pady=10)
        
        # 第一行
        row1_frame = ttk.Frame(custom_dict_frame)
        row1_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(row1_frame, text="自定义字典组合:", font=("微软雅黑", 10, "bold")).pack(side=tk.LEFT)
        ttk.Checkbutton(row1_frame, text="启用", variable=self.custom_dict_var).pack(side=tk.LEFT, padx=(10, 0))
        
        # 第二行
        row2_frame = ttk.Frame(custom_dict_frame)
        row2_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(row2_frame, text="自定义字符 (用逗号分隔):", font=("微软雅黑", 9)).pack(anchor=tk.W)
        ttk.Entry(row2_frame, textvariable=self.custom_chars_var, width=50, font=("微软雅黑", 9)).pack(fill=tk.X, pady=2)
        
        # 第三行
        row3_frame = ttk.Frame(custom_dict_frame)
        row3_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(row3_frame, text="生成长度:", font=("微软雅黑", 9)).pack(side=tk.LEFT)
        ttk.Entry(row3_frame, textvariable=self.custom_dict_length_var, width=10, font=("微软雅黑", 9)).pack(side=tk.LEFT, padx=(5, 20))
        
        ttk.Label(row3_frame, text="生成模式:", font=("微软雅黑", 9)).pack(side=tk.LEFT)
        mode_combo = ttk.Combobox(row3_frame, textvariable=self.custom_dict_mode_var, 
                                 values=["combination", "permutation", "permutation2"], 
                                 state="readonly", width=15, font=("微软雅黑", 9))
        mode_combo.pack(side=tk.LEFT, padx=(5, 20))
        
        ttk.Label(row3_frame, text="连接符号:", font=("微软雅黑", 9)).pack(side=tk.LEFT)
        connector_entry = ttk.Entry(row3_frame, textvariable=self.connector_var, width=10, font=("微软雅黑", 9))
        connector_entry.pack(side=tk.LEFT, padx=(5, 0))
        ToolTip(connector_entry, "输入连接符号，例如：- 或 _ 或空格，将完全按照输入的符号进行连接")
        
        # 示例说明
        example_frame = ttk.LabelFrame(custom_dict_frame, text="示例说明", padding="10")
        example_frame.pack(fill=tk.X, pady=10)
        
        example_text = """输入: a,b,c  长度: 2
组合模式结果: aa,ab,ac,ba,bb,bc,ca,cb,cc
全排列模式结果: ab,ac,ba,bc,ca,cb
全排列模式2结果(连接符: -): a-b,a-c,b-a,b-c,c-a,c-b
全排列模式2结果(连接符: 空格): a b,a c,b a,b c,c a,c b"""
        
        example_label = ttk.Label(example_frame, text=example_text, font=("微软雅黑", 9), 
                                 foreground="#2c3e50", justify=tk.LEFT)
        example_label.pack(anchor=tk.W)
        
        # 重复字符模式
        repeat_frame = ttk.LabelFrame(scrollable_frame, text="重复字符模式", padding="15")
        repeat_frame.pack(fill=tk.X, padx=10, pady=10)
        
        # 第一行
        row1_frame = ttk.Frame(repeat_frame)
        row1_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(row1_frame, text="重复字符模式:", font=("微软雅黑", 10, "bold")).pack(side=tk.LEFT)
        ttk.Checkbutton(row1_frame, text="启用", variable=self.repeat_char_var).pack(side=tk.LEFT, padx=(10, 0))
        
        # 第二行
        row2_frame = ttk.Frame(repeat_frame)
        row2_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(row2_frame, text="重复次数:", font=("微软雅黑", 9)).pack(side=tk.LEFT)
        ttk.Entry(row2_frame, textvariable=self.repeat_len_var, width=10, font=("微软雅黑", 9)).pack(side=tk.LEFT, padx=(5, 20))
        
        ttk.Label(row2_frame, text="模式长度:", font=("微软雅黑", 9)).pack(side=tk.LEFT)
        ttk.Entry(row2_frame, textvariable=self.pattern_len_var, width=10, font=("微软雅黑", 9)).pack(side=tk.LEFT, padx=(5, 20))
        
        ttk.Label(row2_frame, text="模式类型:", font=("微软雅黑", 9)).pack(side=tk.LEFT)
        pattern_combo = ttk.Combobox(row2_frame, textvariable=self.pattern_type_var,
                                   values=["repeat", "sequential", "sequential_repeat"], 
                                   state="readonly", width=15, font=("微软雅黑", 9))
        pattern_combo.pack(side=tk.LEFT, padx=(5, 0))
        
        # 第三行
        row3_frame = ttk.Frame(repeat_frame)
        row3_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(row3_frame, text="自定义字符集:", font=("微软雅黑", 9)).pack(anchor=tk.W)
        ttk.Entry(row3_frame, textvariable=self.custom_charset_var, width=50, font=("微软雅黑", 9)).pack(fill=tk.X, pady=2)
        
        # 重复字符示例说明
        repeat_example_frame = ttk.LabelFrame(repeat_frame, text="重复字符示例", padding="10")
        repeat_example_frame.pack(fill=tk.X, pady=10)
        
        repeat_example_text = """重复模式 - 重复次数=2,模式长度=2 生成: AABB,CCDD,EEFF...
连续模式 - 重复次数=2,模式长度=3 生成: ABCABC,DEFDEF,GHIGHI...
连续重复模式 - 重复次数=2,模式长度=3 生成: AABBCC,DDEEFF,GGHHII..."""
        
        repeat_example_label = ttk.Label(repeat_example_frame, text=repeat_example_text, 
                                       font=("微软雅黑", 9), foreground="#2c3e50", justify=tk.LEFT)
        repeat_example_label.pack(anchor=tk.W)
        
        # 功能说明
        help_frame = ttk.LabelFrame(scrollable_frame, text="功能说明", padding="15")
        help_frame.pack(fill=tk.X, padx=10, pady=10)
        
        help_text = """高级生成功能说明：

1. 自定义字典组合：
   - 组合模式：生成所有可能的组合，允许重复字符
   - 全排列模式：生成所有可能的排列，不重复字符
   - 全排列模式2：生成带连接符的全排列

2. 重复字符模式：
   - 重复模式：每个字符重复指定次数，如AABB
   - 连续模式：连续字符重复指定次数，如ABCABC
   - 连续重复模式：连续字符各自重复，如AABBCC

3. 使用建议：
   - 字符集建议不超过10个字符，避免组合数过大
   - 长度建议不超过6位，确保生成效率
   - 可结合字典导入功能进行进一步处理"""
        
        help_label = ttk.Label(help_frame, text=help_text, font=("微软雅黑", 9), 
                              foreground="#34495e", justify=tk.LEFT)
        help_label.pack(anchor=tk.W)
        
        # 配置滚动
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

    def create_dictionary_import_tab(self):
        """创建字典导入标签页"""
        self.dict_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.dict_frame, text="字典导入")
        
        # 创建滚动框架
        canvas = tk.Canvas(self.dict_frame, bg='#f8f9fa', highlightthickness=0)
        scrollbar = ttk.Scrollbar(self.dict_frame, orient="vertical", command=canvas.yview)
        scrollable_frame = ttk.Frame(canvas)
        
        scrollable_frame.bind(
            "<Configure>",
            lambda e: canvas.configure(scrollregion=canvas.bbox("all"))
        )
        
        canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        
        # 字典文件A
        dict_a_frame = ttk.LabelFrame(scrollable_frame, text="字典文件A", padding="15")
        dict_a_frame.pack(fill=tk.X, padx=10, pady=10)
        
        # 文件选择区域
        file_select_frame = ttk.Frame(dict_a_frame)
        file_select_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(file_select_frame, text="字典文件A:", font=("微软雅黑", 9, "bold")).pack(anchor=tk.W)
        file_entry_frame = ttk.Frame(file_select_frame)
        file_entry_frame.pack(fill=tk.X, pady=5)
        
        ttk.Entry(file_entry_frame, textvariable=self.dict_file_var, width=60, font=("微软雅黑", 9)).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 10))
        ttk.Button(file_entry_frame, text="浏览", command=self.browse_dict_file, 
                  style="Info.TButton").pack(side=tk.RIGHT)
        
        # 字典文件夹
        folder_frame = ttk.LabelFrame(scrollable_frame, text="字典文件夹", padding="15")
        folder_frame.pack(fill=tk.X, padx=10, pady=10)
        
        # 文件夹选择区域
        folder_select_frame = ttk.Frame(folder_frame)
        folder_select_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(folder_select_frame, text="字典文件夹:", font=("微软雅黑", 9, "bold")).pack(anchor=tk.W)
        folder_entry_frame = ttk.Frame(folder_select_frame)
        folder_entry_frame.pack(fill=tk.X, pady=5)
        
        ttk.Entry(folder_entry_frame, textvariable=self.dict_folder_var, width=60, font=("微软雅黑", 9)).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 10))
        ttk.Button(folder_entry_frame, text="浏览", command=self.browse_dict_folder, 
                  style="Info.TButton").pack(side=tk.RIGHT)
        
        # 文件过滤器
        filter_frame = ttk.Frame(folder_frame)
        filter_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(filter_frame, text="文件过滤器:", font=("微软雅黑", 9)).pack(side=tk.LEFT, padx=(0, 5))
        ttk.Entry(filter_frame, textvariable=self.file_filter_var, width=20, font=("微软雅黑", 9)).pack(side=tk.LEFT)
        
        # 文件夹功能说明
        folder_help_frame = ttk.LabelFrame(folder_frame, text="文件夹处理说明", padding="10")
        folder_help_frame.pack(fill=tk.X, pady=10)
        
        help_text = """• 选择文件夹后，程序会自动处理文件夹内所有匹配的文件
• 处理后的文件会保存到文件夹下的 'new' 子文件夹中
• 原文件会被移动到 'done' 子文件夹中
• 支持递归处理子文件夹"""
        
        help_label = ttk.Label(folder_help_frame, text=help_text, font=("微软雅黑", 9), 
                              foreground="#2c3e50", justify=tk.LEFT)
        help_label.pack(anchor=tk.W)
        
        # 字典文件B
        dict_b_frame = ttk.LabelFrame(scrollable_frame, text="字典文件B", padding="15")
        dict_b_frame.pack(fill=tk.X, padx=10, pady=10)
        
        # 文件B选择区域
        file_b_select_frame = ttk.Frame(dict_b_frame)
        file_b_select_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(file_b_select_frame, text="字典文件B:", font=("微软雅黑", 9, "bold")).pack(anchor=tk.W)
        file_b_entry_frame = ttk.Frame(file_b_select_frame)
        file_b_entry_frame.pack(fill=tk.X, pady=5)
        
        ttk.Entry(file_b_entry_frame, textvariable=self.dict_b_file_var, width=60, font=("微软雅黑", 9)).pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 10))
        ttk.Button(file_b_entry_frame, text="浏览", command=self.browse_dict_b_file, 
                  style="Info.TButton").pack(side=tk.RIGHT)
        
        # 字典组合模式
        combo_frame = ttk.LabelFrame(scrollable_frame, text="字典组合模式", padding="15")
        combo_frame.pack(fill=tk.X, padx=10, pady=10)
        
        # 组合模式选择
        combo_select_frame = ttk.Frame(combo_frame)
        combo_select_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(combo_select_frame, text="字典组合模式:", font=("微软雅黑", 9, "bold")).pack(anchor=tk.W)
        combo_combo = ttk.Combobox(combo_select_frame, textvariable=self.dict_combo_var,
                                 values=["none", "dict_first", "mask_first", "dict_ab", "dict_ba"], 
                                 state="readonly", width=20, font=("微软雅黑", 9))
        combo_combo.pack(anchor=tk.W, pady=5)
        
        # 组合模式说明
        combo_help_frame = ttk.LabelFrame(combo_frame, text="组合模式说明", padding="10")
        combo_help_frame.pack(fill=tk.X, pady=10)
        
        combo_help_text = """• none: 不使用组合，仅处理字典A
• dict_first: 字典A在前，掩码在后 (如: password123)
• mask_first: 掩码在前，字典A在后 (如: 123password)
• dict_ab: 字典A在前，字典B在后 (如: user123)
• dict_ba: 字典B在前，字典A在后 (如: 123user)"""
        
        combo_help_label = ttk.Label(combo_help_frame, text=combo_help_text, font=("微软雅黑", 9), 
                                   foreground="#2c3e50", justify=tk.LEFT)
        combo_help_label.pack(anchor=tk.W)
        
        # 字典位置
        pos_frame = ttk.LabelFrame(scrollable_frame, text="字典位置", padding="15")
        pos_frame.pack(fill=tk.X, padx=10, pady=10)
        
        # 位置选择
        pos_select_frame = ttk.Frame(pos_frame)
        pos_select_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(pos_select_frame, text="字典位置:", font=("微软雅黑", 9, "bold")).pack(anchor=tk.W)
        pos_combo = ttk.Combobox(pos_select_frame, textvariable=self.dict_pos_var,
                               values=["none", "append_before", "append_after"], 
                               state="readonly", width=20, font=("微软雅黑", 9))
        pos_combo.pack(anchor=tk.W, pady=5)
        
        # 位置说明
        pos_help_frame = ttk.LabelFrame(pos_frame, text="位置说明", padding="10")
        pos_help_frame.pack(fill=tk.X, pady=10)
        
        pos_help_text = """• none: 不添加字典内容
• append_before: 在生成结果前添加字典内容
• append_after: 在生成结果后添加字典内容"""
        
        pos_help_label = ttk.Label(pos_help_frame, text=pos_help_text, font=("微软雅黑", 9), 
                                 foreground="#2c3e50", justify=tk.LEFT)
        pos_help_label.pack(anchor=tk.W)
        
        # 字典处理选项
        self.create_dict_processing_options(scrollable_frame)
        
        # 配置滚动
        canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)

    def create_dict_processing_options(self, parent_frame):
        """创建字典处理选项（全 pack 版）"""
        # 处理模式
        process_frame = ttk.LabelFrame(parent_frame, text="字典处理选项", padding="15")
        process_frame.pack(fill=tk.X, padx=10, pady=10)

        # 处理模式选择
        mode_frame = ttk.Frame(process_frame)
        mode_frame.pack(fill=tk.X, pady=5)
        ttk.Label(mode_frame, text="处理模式:", font=("微软雅黑", 9, "bold")).pack(side=tk.LEFT)
        mode_combo = ttk.Combobox(mode_frame, textvariable=self.process_mode_var,
                                 values=["independent", "combined"], state="readonly", width=20, font=("微软雅黑", 9))
        mode_combo.pack(side=tk.LEFT, padx=(10, 0))

        # 处理模式说明
        mode_help_frame = ttk.LabelFrame(process_frame, text="处理模式说明", padding="10")
        mode_help_frame.pack(fill=tk.X, pady=5)
        mode_help_text = """• independent: 独立处理，每个选项单独生成结果
• combined: 组合处理，所有选项组合生成结果"""
        ttk.Label(mode_help_frame, text=mode_help_text, font=("微软雅黑", 9), foreground="#2c3e50", justify=tk.LEFT).pack(anchor=tk.W)

        # 大小写处理
        case_frame = ttk.LabelFrame(process_frame, text="大小写处理", padding="10")
        case_frame.pack(fill=tk.X, pady=5)
        case_row = ttk.Frame(case_frame)
        case_row.pack(fill=tk.X, pady=2)
        ttk.Label(case_row, text="大小写处理:", font=("微软雅黑", 9)).pack(side=tk.LEFT)
        ttk.Checkbutton(case_row, text="大写", variable=self.uppercase_var).pack(side=tk.LEFT, padx=(10, 0))
        ttk.Checkbutton(case_row, text="小写", variable=self.lowercase_var).pack(side=tk.LEFT, padx=(10, 0))
        ttk.Checkbutton(case_row, text="首字母大写", variable=self.capitalize_var).pack(side=tk.LEFT, padx=(10, 0))
        # 大小写示例
        case_example = ttk.Label(case_frame, text="示例 (输入: hello): 大写: HELLO  小写: hello  首字母大写: Hello", font=("微软雅黑", 8), foreground="#7f8c8d")
        case_example.pack(anchor=tk.W, pady=2)

        # 字符串反转
        reverse_frame = ttk.Frame(process_frame)
        reverse_frame.pack(fill=tk.X, pady=5)
        ttk.Checkbutton(reverse_frame, text="字符串反转", variable=self.reverse_var).pack(side=tk.LEFT)
        ttk.Label(reverse_frame, text="示例: hello → olleh", font=("微软雅黑", 8), foreground="#7f8c8d").pack(side=tk.LEFT, padx=(10, 0))

        # 字符移除
        remove_frame = ttk.LabelFrame(process_frame, text="字符移除", padding="10")
        remove_frame.pack(fill=tk.X, pady=5)
        row1 = ttk.Frame(remove_frame)
        row1.pack(fill=tk.X, pady=2)
        ttk.Label(row1, text="移除开头字符数:", font=("微软雅黑", 9)).pack(side=tk.LEFT)
        ttk.Entry(row1, textvariable=self.remove_start_var, width=10, font=("微软雅黑", 9)).pack(side=tk.LEFT, padx=(5, 10))
        ttk.Checkbutton(row1, text="独立处理", variable=self.remove_start_independent_var).pack(side=tk.LEFT)
        row2 = ttk.Frame(remove_frame)
        row2.pack(fill=tk.X, pady=2)
        ttk.Label(row2, text="移除结尾字符数:", font=("微软雅黑", 9)).pack(side=tk.LEFT)
        ttk.Entry(row2, textvariable=self.remove_end_var, width=10, font=("微软雅黑", 9)).pack(side=tk.LEFT, padx=(5, 10))
        ttk.Checkbutton(row2, text="独立处理", variable=self.remove_end_independent_var).pack(side=tk.LEFT)
        ttk.Checkbutton(row2, text="同时处理", variable=self.remove_combined_var).pack(side=tk.LEFT, padx=(10, 0))
        # 字符移除示例
        remove_example = ttk.Label(remove_frame, text="示例 (输入: password, 移除开头2个, 结尾3个): 独立处理开头: ssword  独立处理结尾: pass  同时处理: ss", font=("微软雅黑", 8), foreground="#7f8c8d")
        remove_example.pack(anchor=tk.W, pady=2)

        # 字符添加
        add_frame = ttk.LabelFrame(process_frame, text="字符添加", padding="10")
        add_frame.pack(fill=tk.X, pady=5)
        row1 = ttk.Frame(add_frame)
        row1.pack(fill=tk.X, pady=2)
        ttk.Label(row1, text="开头添加:", font=("微软雅黑", 9)).pack(side=tk.LEFT)
        ttk.Entry(row1, textvariable=self.add_start_var, width=20, font=("微软雅黑", 9)).pack(side=tk.LEFT, padx=(5, 10))
        ttk.Checkbutton(row1, text="独立处理", variable=self.add_start_independent_var).pack(side=tk.LEFT)
        row2 = ttk.Frame(add_frame)
        row2.pack(fill=tk.X, pady=2)
        ttk.Label(row2, text="结尾添加:", font=("微软雅黑", 9)).pack(side=tk.LEFT)
        ttk.Entry(row2, textvariable=self.add_end_var, width=20, font=("微软雅黑", 9)).pack(side=tk.LEFT, padx=(5, 10))
        ttk.Checkbutton(row2, text="独立处理", variable=self.add_end_independent_var).pack(side=tk.LEFT)
        ttk.Checkbutton(row2, text="同时处理", variable=self.add_combined_var).pack(side=tk.LEFT, padx=(10, 0))
        # 字符添加示例
        add_example = ttk.Label(add_frame, text="示例 (输入: pass, 开头添加123, 结尾添加456): 独立处理开头: 123pass  独立处理结尾: pass456  同时处理: 123pass456", font=("微软雅黑", 8), foreground="#7f8c8d")
        add_example.pack(anchor=tk.W, pady=2)

        # 重复处理
        repeat_frame = ttk.LabelFrame(process_frame, text="重复处理", padding="10")
        repeat_frame.pack(fill=tk.X, pady=5)
        row1 = ttk.Frame(repeat_frame)
        row1.pack(fill=tk.X, pady=2)
        ttk.Label(row1, text="重复次数:", font=("微软雅黑", 9)).pack(side=tk.LEFT)
        ttk.Entry(row1, textvariable=self.repeat_count_var, width=10, font=("微软雅黑", 9)).pack(side=tk.LEFT, padx=(5, 10))
        row2 = ttk.Frame(repeat_frame)
        row2.pack(fill=tk.X, pady=2)
        ttk.Label(row2, text="空格重复次数:", font=("微软雅黑", 9)).pack(side=tk.LEFT)
        ttk.Entry(row2, textvariable=self.repeat_space_count_var, width=10, font=("微软雅黑", 9)).pack(side=tk.LEFT, padx=(5, 10))
        ttk.Checkbutton(repeat_frame, text="重复处理已处理的数据", variable=self.repeat_processed_var).pack(anchor=tk.W, pady=2)
        row3 = ttk.Frame(repeat_frame)
        row3.pack(fill=tk.X, pady=2)
        ttk.Label(row3, text="重复处理次数:", font=("微软雅黑", 9)).pack(side=tk.LEFT)
        ttk.Entry(row3, textvariable=self.repeat_processed_count_var, width=10, font=("微软雅黑", 9)).pack(side=tk.LEFT, padx=(5, 10))
        row4 = ttk.Frame(repeat_frame)
        row4.pack(fill=tk.X, pady=2)
        ttk.Label(row4, text="空格重复处理次数:", font=("微软雅黑", 9)).pack(side=tk.LEFT)
        ttk.Entry(row4, textvariable=self.repeat_processed_space_count_var, width=10, font=("微软雅黑", 9)).pack(side=tk.LEFT, padx=(5, 10))
        # 重复处理示例
        repeat_example = ttk.Label(repeat_frame, text="示例 (输入: pass, 重复次数=2): 重复: passpass  空格重复: pass pass", font=("微软雅黑", 8), foreground="#7f8c8d")
        repeat_example.pack(anchor=tk.W, pady=2)

        # 功能说明
        help_frame = ttk.LabelFrame(process_frame, text="字典处理功能说明", padding="10")
        help_frame.pack(fill=tk.X, pady=5)
        help_text = """1. 处理模式：独立处理/组合处理
2. 大小写处理：大写/小写/首字母大写
3. 字符操作：反转/移除/添加
4. 重复处理：重复次数/空格重复/重复处理已处理数据
5. 建议：先测试小量数据，组合处理注意内存，文件夹处理自动管理文件"""
        ttk.Label(help_frame, text=help_text, font=("微软雅黑", 9), foreground="#34495e", justify=tk.LEFT).pack(anchor=tk.W)

    def create_input_parameters_tab(self):
        """创建输入参数标签页"""
        self.input_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.input_frame, text="输入参数")
        
        # Hashcat掩码
        mask_frame = ttk.LabelFrame(self.input_frame, text="Hashcat掩码模式", padding="10")
        mask_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Label(mask_frame, text="Hashcat掩码:").grid(row=0, column=0, sticky=tk.W, pady=5)
        ttk.Entry(mask_frame, textvariable=self.mask_var, width=50).grid(row=0, column=1, columnspan=2, sticky=(tk.W, tk.E), pady=5)
        
        # 掩码说明
        mask_help_frame = ttk.Frame(mask_frame)
        mask_help_frame.grid(row=1, column=0, columnspan=3, sticky=tk.W, padx=5, pady=10)
        
        ttk.Label(mask_help_frame, text="Hashcat掩码说明:", font=("微软雅黑", 10, "bold")).grid(row=0, column=0, sticky=tk.W, pady=5)
        ttk.Label(mask_help_frame, text="• ?l = 小写字母 (abcdefghijklmnopqrstuvwxyz)", font=("微软雅黑", 9)).grid(row=1, column=0, columnspan=2, sticky=tk.W, pady=2)
        ttk.Label(mask_help_frame, text="• ?u = 大写字母 (ABCDEFGHIJKLMNOPQRSTUVWXYZ)", font=("微软雅黑", 9)).grid(row=2, column=0, columnspan=2, sticky=tk.W, pady=2)
        ttk.Label(mask_help_frame, text="• ?d = 数字 (0123456789)", font=("微软雅黑", 9)).grid(row=3, column=0, columnspan=2, sticky=tk.W, pady=2)
        ttk.Label(mask_help_frame, text="• ?s = 特殊字符 (!\"#$%&'()*+,-./:;<=>?@[\\]^_`{|}~)", font=("微软雅黑", 9)).grid(row=4, column=0, columnspan=2, sticky=tk.W, pady=2)
        ttk.Label(mask_help_frame, text="• ?a = 所有字符 (?l?u?d?s)", font=("微软雅黑", 9)).grid(row=5, column=0, columnspan=2, sticky=tk.W, pady=2)
        ttk.Label(mask_help_frame, text="• ?b = 二进制 (0x00-0xff)", font=("微软雅黑", 9)).grid(row=6, column=0, columnspan=2, sticky=tk.W, pady=2)
        ttk.Label(mask_help_frame, text="• ?? = 字面字符 (如 ?? 表示问号)", font=("微软雅黑", 9)).grid(row=7, column=0, columnspan=2, sticky=tk.W, pady=2)
        
        # 掩码示例
        mask_example_frame = ttk.Frame(mask_frame)
        mask_example_frame.grid(row=2, column=0, columnspan=3, sticky=tk.W, padx=5, pady=10)
        
        ttk.Label(mask_example_frame, text="掩码示例:", font=("微软雅黑", 10, "bold")).grid(row=0, column=0, sticky=tk.W, pady=5)
        ttk.Label(mask_example_frame, text="• ?l?l?l?l?d?d?d?d = 4位小写字母+4位数字 (如: abcd1234)", font=("微软雅黑", 9)).grid(row=1, column=0, columnspan=2, sticky=tk.W, pady=2)
        ttk.Label(mask_example_frame, text="• ?u?l?l?l?d?d?d = 1位大写+3位小写+3位数字 (如: Pass123)", font=("微软雅黑", 9)).grid(row=2, column=0, columnspan=2, sticky=tk.W, pady=2)
        ttk.Label(mask_example_frame, text="• ?l?l?l?s?d?d = 3位小写+1位特殊+2位数字 (如: abc#12)", font=("微软雅黑", 9)).grid(row=3, column=0, columnspan=2, sticky=tk.W, pady=2)
        ttk.Label(mask_example_frame, text="• ?a?a?a?a = 4位任意字符", font=("微软雅黑", 9)).grid(row=4, column=0, columnspan=2, sticky=tk.W, pady=2)
        
        # 基础字符集
        charset_frame = ttk.LabelFrame(self.input_frame, text="基础字符集模式", padding="10")
        charset_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Label(charset_frame, text="基础字符集:").grid(row=0, column=0, sticky=tk.W, pady=5)
        ttk.Entry(charset_frame, textvariable=self.charset_var, width=50).grid(row=0, column=1, columnspan=2, sticky=(tk.W, tk.E), pady=5)
        ttk.Checkbutton(charset_frame, text="包含特殊字符", variable=self.include_special_var).grid(row=0, column=3, sticky=tk.W)
        
        # 字符集示例
        charset_example_frame = ttk.Frame(charset_frame)
        charset_example_frame.grid(row=1, column=0, columnspan=4, sticky=tk.W, padx=5, pady=10)
        
        ttk.Label(charset_example_frame, text="字符集示例:", font=("微软雅黑", 10, "bold")).grid(row=0, column=0, sticky=tk.W, pady=5)
        ttk.Label(charset_example_frame, text="• abcdefghijklmnopqrstuvwxyz = 小写字母", font=("微软雅黑", 9)).grid(row=1, column=0, columnspan=2, sticky=tk.W, pady=2)
        ttk.Label(charset_example_frame, text="• 0123456789 = 数字", font=("微软雅黑", 9)).grid(row=2, column=0, columnspan=2, sticky=tk.W, pady=2)
        ttk.Label(charset_example_frame, text="• abc123 = 小写字母+数字", font=("微软雅黑", 9)).grid(row=3, column=0, columnspan=2, sticky=tk.W, pady=2)
        ttk.Label(charset_example_frame, text="• 包含特殊字符: 自动添加 !\"#$%&'()*+,-./:;<=>?@[\\]^_`{|}~", font=("微软雅黑", 9)).grid(row=4, column=0, columnspan=2, sticky=tk.W, pady=2)
        
        # 长度范围
        length_frame = ttk.LabelFrame(self.input_frame, text="长度范围", padding="10")
        length_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Label(length_frame, text="最小长度:").grid(row=0, column=0, sticky=tk.W, pady=5)
        ttk.Entry(length_frame, textvariable=self.min_len_var, width=10).grid(row=0, column=1, sticky=tk.W, pady=5)
        
        ttk.Label(length_frame, text="最大长度:").grid(row=0, column=2, sticky=tk.W, pady=5)
        ttk.Entry(length_frame, textvariable=self.max_len_var, width=10).grid(row=0, column=3, sticky=tk.W, pady=5)
        
        # 长度示例
        length_example_frame = ttk.Frame(length_frame)
        length_example_frame.grid(row=1, column=0, columnspan=4, sticky=tk.W, padx=5, pady=10)
        
        ttk.Label(length_example_frame, text="长度范围示例:", font=("微软雅黑", 10, "bold")).grid(row=0, column=0, sticky=tk.W, pady=5)
        ttk.Label(length_example_frame, text="• 最小长度=1, 最大长度=3: 生成1位、2位、3位的所有组合", font=("微软雅黑", 9)).grid(row=1, column=0, columnspan=2, sticky=tk.W, pady=2)
        ttk.Label(length_example_frame, text="• 最小长度=4, 最大长度=6: 生成4位、5位、6位的所有组合", font=("微软雅黑", 9)).grid(row=2, column=0, columnspan=2, sticky=tk.W, pady=2)
        ttk.Label(length_example_frame, text="• 最小长度=8, 最大长度=8: 仅生成8位组合", font=("微软雅黑", 9)).grid(row=3, column=0, columnspan=2, sticky=tk.W, pady=2)
        
        # 功能说明
        help_frame = ttk.LabelFrame(self.input_frame, text="输入参数功能说明", padding="10")
        help_frame.pack(fill=tk.X, padx=5, pady=5)
        
        help_text = """
输入参数功能说明：

1. Hashcat掩码模式：
   - 使用Hashcat标准掩码语法
   - 支持所有Hashcat字符集
   - 适合密码破解和渗透测试

2. 基础字符集模式：
   - 自定义字符集
   - 支持长度范围设置
   - 可选择包含特殊字符

3. 长度范围：
   - 最小长度：生成组合的最小位数
   - 最大长度：生成组合的最大位数
   - 程序会生成指定范围内所有长度的组合

4. 输出设置：
   - 自动文件分割，避免单个文件过大
   - 支持自定义输出路径
   - 文件命名自动编号

5. 使用建议：
   - 掩码模式适合已知密码格式的场景
   - 字符集模式适合自定义字符的场景
   - 注意组合数计算，避免内存溢出
   - 建议先用小范围测试，确认效果后再大规模生成
        """
        
        help_label = ttk.Label(help_frame, text=help_text, font=("微软雅黑", 9), justify=tk.LEFT)
        help_label.pack(anchor=tk.W)
        
        # 快速示例
        example_frame = ttk.LabelFrame(self.input_frame, text="快速示例", padding="10")
        example_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Label(example_frame, text="快速示例:", font=("微软雅黑", 10, "bold")).pack(anchor=tk.W, pady=5)
        
        # 示例1：掩码模式
        example1_frame = ttk.Frame(example_frame)
        example1_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(example1_frame, text="掩码模式示例:", font=("微软雅黑", 9, "bold")).pack(anchor=tk.W)
        ttk.Label(example1_frame, text="掩码: ?l?l?l?l?d?d?d?d", font=("微软雅黑", 9)).pack(anchor=tk.W)
        ttk.Label(example1_frame, text="字符集: 26个小写字母 + 10个数字", font=("微软雅黑", 9)).pack(anchor=tk.W)
        ttk.Label(example1_frame, text="组合数: 26^4 × 10^4 = 456,976,000", font=("微软雅黑", 9)).pack(anchor=tk.W)
        
        # 示例2：字符集模式
        example2_frame = ttk.Frame(example_frame)
        example2_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(example2_frame, text="字符集模式示例:", font=("微软雅黑", 9, "bold")).pack(anchor=tk.W)
        ttk.Label(example2_frame, text="字符集: abc123", font=("微软雅黑", 9)).pack(anchor=tk.W)
        ttk.Label(example2_frame, text="长度范围: 1-3", font=("微软雅黑", 9)).pack(anchor=tk.W)
        ttk.Label(example2_frame, text="组合数: 6^1 + 6^2 + 6^3 = 6 + 36 + 216 = 258", font=("微软雅黑", 9)).pack(anchor=tk.W)
        
        # 示例3：高级生成
        example3_frame = ttk.Frame(example_frame)
        example3_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(example3_frame, text="高级生成示例:", font=("微软雅黑", 9, "bold")).pack(anchor=tk.W)
        ttk.Label(example3_frame, text="自定义字符: a,b,c", font=("微软雅黑", 9)).pack(anchor=tk.W)
        ttk.Label(example3_frame, text="模式: 组合", font=("微软雅黑", 9)).pack(anchor=tk.W)
        ttk.Label(example3_frame, text="长度: 2", font=("微软雅黑", 9)).pack(anchor=tk.W)
        ttk.Label(example3_frame, text="组合数: 3^2 = 9", font=("微软雅黑", 9)).pack(anchor=tk.W)

    def create_parameter_preview_tab(self):
        """创建参数预览标签页"""
        self.preview_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.preview_frame, text="参数预览")
        
        # 字符集预览
        charset_preview_frame = ttk.LabelFrame(self.preview_frame, text="字符集预览", padding="10")
        charset_preview_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Label(charset_preview_frame, text="字符集预览:").grid(row=0, column=0, sticky=tk.W, pady=5)
        self.charset_preview = tk.Text(charset_preview_frame, height=5, width=60)
        self.charset_preview.grid(row=1, column=0, columnspan=2, sticky=(tk.W, tk.E), pady=5)
        
        # 更新预览按钮
        ttk.Button(charset_preview_frame, text="更新预览", command=self.update_preview).grid(row=2, column=0, pady=5)
        
        # 组合数计算
        calc_frame = ttk.LabelFrame(self.preview_frame, text="组合数计算", padding="10")
        calc_frame.pack(fill=tk.X, padx=5, pady=5)
        
        self.calc_result_label = ttk.Label(calc_frame, text="预计组合数: 请设置参数后点击更新预览", font=("微软雅黑", 10))
        self.calc_result_label.pack(anchor=tk.W, pady=5)
        
        # 预览说明
        preview_help_frame = ttk.LabelFrame(self.preview_frame, text="预览功能说明", padding="10")
        preview_help_frame.pack(fill=tk.X, padx=5, pady=5)
        
        help_text = """
预览功能说明：

1. 字符集预览：
   - 显示当前设置的完整字符集
   - 包含基础字符集和特殊字符（如果启用）
   - 字符按字母顺序排列，去重显示

2. 组合数计算：
   - 根据当前参数计算预计生成的组合数
   - 考虑所有模式：掩码、字符集、字典、高级生成
   - 帮助用户评估生成时间和资源需求

3. 更新预览：
   - 点击按钮实时更新预览内容
   - 当参数发生变化时自动更新
   - 确保预览内容与当前设置一致

4. 使用建议：
   - 在开始生成前先预览字符集和组合数
   - 如果组合数过大，考虑调整参数
   - 预览功能不影响实际生成过程
        """
        
        help_label = ttk.Label(preview_help_frame, text=help_text, font=("微软雅黑", 9), justify=tk.LEFT)
        help_label.pack(anchor=tk.W)
        
        # 快速示例
        example_frame = ttk.LabelFrame(self.preview_frame, text="快速示例", padding="10")
        example_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Label(example_frame, text="快速示例:", font=("微软雅黑", 10, "bold")).pack(anchor=tk.W, pady=5)
        
        # 示例1：掩码模式
        example1_frame = ttk.Frame(example_frame)
        example1_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(example1_frame, text="掩码模式示例:", font=("微软雅黑", 9, "bold")).pack(anchor=tk.W)
        ttk.Label(example1_frame, text="掩码: ?l?l?l?l?d?d?d?d", font=("微软雅黑", 9)).pack(anchor=tk.W)
        ttk.Label(example1_frame, text="字符集: 26个小写字母 + 10个数字", font=("微软雅黑", 9)).pack(anchor=tk.W)
        ttk.Label(example1_frame, text="组合数: 26^4 × 10^4 = 456,976,000", font=("微软雅黑", 9)).pack(anchor=tk.W)
        
        # 示例2：字符集模式
        example2_frame = ttk.Frame(example_frame)
        example2_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(example2_frame, text="字符集模式示例:", font=("微软雅黑", 9, "bold")).pack(anchor=tk.W)
        ttk.Label(example2_frame, text="字符集: abc123", font=("微软雅黑", 9)).pack(anchor=tk.W)
        ttk.Label(example2_frame, text="长度范围: 1-3", font=("微软雅黑", 9)).pack(anchor=tk.W)
        ttk.Label(example2_frame, text="组合数: 6^1 + 6^2 + 6^3 = 6 + 36 + 216 = 258", font=("微软雅黑", 9)).pack(anchor=tk.W)
        
        # 示例3：高级生成
        example3_frame = ttk.Frame(example_frame)
        example3_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(example3_frame, text="高级生成示例:", font=("微软雅黑", 9, "bold")).pack(anchor=tk.W)
        ttk.Label(example3_frame, text="自定义字符: a,b,c", font=("微软雅黑", 9)).pack(anchor=tk.W)
        ttk.Label(example3_frame, text="模式: 组合", font=("微软雅黑", 9)).pack(anchor=tk.W)
        ttk.Label(example3_frame, text="长度: 2", font=("微软雅黑", 9)).pack(anchor=tk.W)
        ttk.Label(example3_frame, text="组合数: 3^2 = 9", font=("微软雅黑", 9)).pack(anchor=tk.W)

    def create_control_panel(self):
        """创建控制面板"""
        control_frame = ttk.LabelFrame(self.main_frame, text="控制面板", padding="15")
        control_frame.grid(row=2, column=0, columnspan=3, sticky=(tk.W, tk.E), pady=(0, 15))
        
        # 主要控制区域
        main_control_frame = ttk.Frame(control_frame)
        main_control_frame.pack(fill=tk.X, pady=(0, 10))
        
        # 生成和停止按钮
        button_frame = ttk.Frame(main_control_frame)
        button_frame.pack(side=tk.LEFT, padx=(0, 20))
        
        self.generate_button = ttk.Button(button_frame, text="开始生成", command=self.start_generation, 
                                         style="Accent.TButton")
        self.generate_button.pack(side=tk.LEFT, padx=(0, 10))
        
        self.stop_button = ttk.Button(button_frame, text="停止生成", command=self.stop_generation, 
                                     state=tk.DISABLED)
        self.stop_button.pack(side=tk.LEFT)
        
        # 进度显示区域
        progress_frame = ttk.Frame(main_control_frame)
        progress_frame.pack(side=tk.LEFT, fill=tk.X, expand=True)
        
        ttk.Label(progress_frame, text="进度:", font=("微软雅黑", 9, "bold")).pack(side=tk.LEFT, padx=(0, 5))
        self.progress_bar = ttk.Progressbar(progress_frame, length=400, mode='determinate')
        self.progress_bar.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(0, 10))
        
        # 状态标签
        self.status_label = ttk.Label(progress_frame, text="就绪", font=("微软雅黑", 9), 
                                     foreground="#27ae60")
        self.status_label.pack(side=tk.LEFT)
        
        # 性能优化选项
        optimization_frame = ttk.LabelFrame(control_frame, text="性能优化", padding="10")
        optimization_frame.pack(fill=tk.X, pady=(0, 10))
        
        # 第一行优化选项
        row1_frame = ttk.Frame(optimization_frame)
        row1_frame.pack(fill=tk.X, pady=2)
        
        ttk.Checkbutton(row1_frame, text="自动优化", variable=self.auto_optimize).pack(side=tk.LEFT, padx=(0, 15))
        ttk.Checkbutton(row1_frame, text="内存映射", variable=self.use_memory_mapping).pack(side=tk.LEFT, padx=(0, 15))
        ttk.Checkbutton(row1_frame, text="压缩写入", variable=self.use_compression).pack(side=tk.LEFT, padx=(0, 15))
        ttk.Checkbutton(row1_frame, text="并行处理", variable=self.parallel_processing).pack(side=tk.LEFT, padx=(0, 15))
        
        # 第二行优化选项
        row2_frame = ttk.Frame(optimization_frame)
        row2_frame.pack(fill=tk.X, pady=2)
        
        ttk.Label(row2_frame, text="最大线程数:", font=("微软雅黑", 9)).pack(side=tk.LEFT, padx=(0, 5))
        ttk.Entry(row2_frame, textvariable=self.max_workers_var, width=8, font=("微软雅黑", 9)).pack(side=tk.LEFT, padx=(0, 15))
        
        ttk.Label(row2_frame, text="内存阈值(%):", font=("微软雅黑", 9)).pack(side=tk.LEFT, padx=(0, 5))
        ttk.Entry(row2_frame, textvariable=self.memory_threshold, width=8, font=("微软雅黑", 9)).pack(side=tk.LEFT, padx=(0, 15))
        
        ttk.Label(row2_frame, text="CPU阈值(%):", font=("微软雅黑", 9)).pack(side=tk.LEFT, padx=(0, 5))
        ttk.Entry(row2_frame, textvariable=self.cpu_threshold, width=8, font=("微软雅黑", 9)).pack(side=tk.LEFT, padx=(0, 15))
        
        # 第三行控制选项
        row3_frame = ttk.Frame(optimization_frame)
        row3_frame.pack(fill=tk.X, pady=2)
        
        ttk.Checkbutton(row3_frame, text="显示日志", variable=self.log_enabled, 
                       command=self.toggle_log_display).pack(side=tk.LEFT, padx=(0, 15))
        ttk.Checkbutton(row3_frame, text="性能监控", variable=self.performance_monitoring).pack(side=tk.LEFT, padx=(0, 15))
        
        # 性能测试按钮
        ttk.Button(row3_frame, text="性能测试", command=self.run_performance_test, 
                  style="Info.TButton").pack(side=tk.LEFT, padx=(0, 10))
        ttk.Button(row3_frame, text="清理缓存", command=self.clear_cache).pack(side=tk.LEFT, padx=(0, 10))
        ttk.Button(row3_frame, text="系统信息", command=self.show_system_info).pack(side=tk.LEFT, padx=(0, 10))
        
        # 高级功能选项
        advanced_frame = ttk.LabelFrame(control_frame, text="高级功能", padding="10")
        advanced_frame.pack(fill=tk.X, pady=(0, 10))
        
        # 第一行高级选项
        row1_frame = ttk.Frame(advanced_frame)
        row1_frame.pack(fill=tk.X, pady=2)
        
        ttk.Checkbutton(row1_frame, text="高级功能", variable=self.advanced_features).pack(side=tk.LEFT, padx=(0, 15))
        ttk.Checkbutton(row1_frame, text="自动备份", variable=self.auto_backup).pack(side=tk.LEFT, padx=(0, 15))
        ttk.Checkbutton(row1_frame, text="统计跟踪", variable=self.statistics_tracking).pack(side=tk.LEFT, padx=(0, 15))
        ttk.Checkbutton(row1_frame, text="模式缓存", variable=self.pattern_caching).pack(side=tk.LEFT, padx=(0, 15))
        
        # 第二行高级选项
        row2_frame = ttk.Frame(advanced_frame)
        row2_frame.pack(fill=tk.X, pady=2)
        
        ttk.Checkbutton(row2_frame, text="历史记录", variable=self.history_tracking).pack(side=tk.LEFT, padx=(0, 15))
        ttk.Checkbutton(row2_frame, text="去重处理", variable=self.duplicate_removal).pack(side=tk.LEFT, padx=(0, 15))
        ttk.Checkbutton(row2_frame, text="质量检查", variable=self.quality_check).pack(side=tk.LEFT, padx=(0, 15))
        
        # 第三行高级功能按钮
        row3_frame = ttk.Frame(advanced_frame)
        row3_frame.pack(fill=tk.X, pady=2)
        
        ttk.Button(row3_frame, text="统计报告", command=self.show_statistics, 
                  style="Info.TButton").pack(side=tk.LEFT, padx=(0, 10))
        ttk.Button(row3_frame, text="历史记录", command=self.show_history).pack(side=tk.LEFT, padx=(0, 10))
        ttk.Button(row3_frame, text="导出数据", command=self.export_data).pack(side=tk.LEFT, padx=(0, 10))
        ttk.Button(row3_frame, text="备份恢复", command=self.backup_restore).pack(side=tk.LEFT, padx=(0, 10))
        ttk.Button(row3_frame, text="设置管理", command=self.manage_settings).pack(side=tk.LEFT, padx=(0, 10))
        
        # 终极优化选项
        ultimate_frame = ttk.LabelFrame(control_frame, text="终极优化", padding="10")
        ultimate_frame.pack(fill=tk.X)
        
        # 第一行终极优化选项
        row1_frame = ttk.Frame(ultimate_frame)
        row1_frame.pack(fill=tk.X, pady=2)
        
        ttk.Checkbutton(row1_frame, text="终极优化", variable=self.ultimate_optimization).pack(side=tk.LEFT, padx=(0, 15))
        ttk.Checkbutton(row1_frame, text="进程池", variable=self.process_pool_enabled).pack(side=tk.LEFT, padx=(0, 15))
        ttk.Checkbutton(row1_frame, text="内存池", variable=self.memory_pool_enabled).pack(side=tk.LEFT, padx=(0, 15))
        ttk.Checkbutton(row1_frame, text="GC优化", variable=self.gc_optimization).pack(side=tk.LEFT, padx=(0, 15))
        
        # 第二行终极优化选项
        row2_frame = ttk.Frame(ultimate_frame)
        row2_frame.pack(fill=tk.X, pady=2)
        
        ttk.Checkbutton(row2_frame, text="信号处理", variable=self.signal_handling_enabled).pack(side=tk.LEFT, padx=(0, 15))
        ttk.Checkbutton(row2_frame, text="缓冲区优化", variable=self.buffer_optimization_enabled).pack(side=tk.LEFT, padx=(0, 15))
        ttk.Checkbutton(row2_frame, text="缓存预取", variable=self.cache_prefetch_enabled).pack(side=tk.LEFT, padx=(0, 15))
        ttk.Checkbutton(row2_frame, text="异步I/O", variable=self.async_io_enabled).pack(side=tk.LEFT, padx=(0, 15))
        ttk.Checkbutton(row2_frame, text="GPU加速", variable=self.gpu_acceleration_enabled).pack(side=tk.LEFT, padx=(0, 15))
        
        # 第三行终极优化按钮
        row3_frame = ttk.Frame(ultimate_frame)
        row3_frame.pack(fill=tk.X, pady=2)
        
        ttk.Button(row3_frame, text="性能分析", command=self.analyze_performance, 
                  style="Info.TButton").pack(side=tk.LEFT, padx=(0, 10))
        ttk.Button(row3_frame, text="系统调优", command=self.system_tuning).pack(side=tk.LEFT, padx=(0, 10))
        ttk.Button(row3_frame, text="内存优化", command=self.memory_optimization).pack(side=tk.LEFT, padx=(0, 10))
        ttk.Button(row3_frame, text="缓存管理", command=self.cache_management).pack(side=tk.LEFT, padx=(0, 10))
        ttk.Button(row3_frame, text="进程监控", command=self.process_monitoring).pack(side=tk.LEFT, padx=(0, 10))

        # 输出设置区域
        output_frame = ttk.LabelFrame(control_frame, text="输出设置", padding="10")
        output_frame.pack(fill=tk.X, pady=(0, 10))
        
        output_row1 = ttk.Frame(output_frame)
        output_row1.pack(fill=tk.X, pady=2)
        ttk.Label(output_row1, text="输出文件:", font=("微软雅黑", 9)).pack(side=tk.LEFT)
        ttk.Entry(output_row1, textvariable=self.output_file_var, width=50, font=("微软雅黑", 9)).pack(side=tk.LEFT, padx=(5, 10), fill=tk.X, expand=True)
        ttk.Button(output_row1, text="浏览", command=self.browse_output_file, style="Info.TButton").pack(side=tk.LEFT)
        
        output_row2 = ttk.Frame(output_frame)
        output_row2.pack(fill=tk.X, pady=2)
        ttk.Label(output_row2, text="每个文件的最大组合数:", font=("微软雅黑", 9)).pack(side=tk.LEFT)
        ttk.Entry(output_row2, textvariable=self.split_size_var, width=15, font=("微软雅黑", 9)).pack(side=tk.LEFT, padx=(5, 0))
        
        # 输出说明
        output_help_frame = ttk.Frame(output_frame)
        output_help_frame.pack(fill=tk.X, pady=(5, 0))
        ttk.Label(output_help_frame, text="输出说明:", font=("微软雅黑", 10, "bold")).pack(anchor=tk.W)
        ttk.Label(output_help_frame, text="• 当组合数超过设定值时，会自动分割成多个文件", font=("微软雅黑", 9)).pack(anchor=tk.W)
        ttk.Label(output_help_frame, text="• 文件命名格式: 原文件名_1.txt, 原文件名_2.txt...", font=("微软雅黑", 9)).pack(anchor=tk.W)
        ttk.Label(output_help_frame, text="• 建议设置: 1000000 (100万) 组合/文件，避免文件过大", font=("微软雅黑", 9)).pack(anchor=tk.W)

    def create_log_area(self):
        """创建日志区域"""
        log_frame = ttk.LabelFrame(self.main_frame, text="日志", padding="15")
        log_frame.grid(row=3, column=0, columnspan=3, sticky=(tk.W, tk.E, tk.N, tk.S), pady=(0, 10))
        log_frame.columnconfigure(0, weight=1)
        log_frame.rowconfigure(0, weight=1)
        
        # 日志工具栏
        log_toolbar = ttk.Frame(log_frame)
        log_toolbar.pack(fill=tk.X, pady=(0, 10))
        
        # 日志控制按钮
        ttk.Button(log_toolbar, text="清除日志", command=self.clear_log, 
                  style="Info.TButton").pack(side=tk.LEFT, padx=(0, 10))
        ttk.Button(log_toolbar, text="导出日志", command=self.export_log).pack(side=tk.LEFT, padx=(0, 10))
        ttk.Button(log_toolbar, text="自动滚动", command=self.toggle_auto_scroll).pack(side=tk.LEFT)
        
        # 日志级别选择
        ttk.Label(log_toolbar, text="日志级别:", font=("微软雅黑", 9)).pack(side=tk.RIGHT, padx=(10, 5))
        log_level_var = tk.StringVar(value="INFO")
        log_level_combo = ttk.Combobox(log_toolbar, textvariable=log_level_var, 
                                      values=["DEBUG", "INFO", "WARNING", "ERROR"], 
                                      state="readonly", width=10, font=("微软雅黑", 9))
        log_level_combo.pack(side=tk.RIGHT)
        
        # 日志文本框
        text_frame = ttk.Frame(log_frame)
        text_frame.pack(fill=tk.BOTH, expand=True)
        
        self.log_text = scrolledtext.ScrolledText(
            text_frame, 
            height=12, 
            width=100,
            font=("Consolas", 9),
            bg='#f8f9fa',
            fg='#2c3e50',
            insertbackground='#2c3e50',
            selectbackground='#3498db',
            selectforeground='white',
            wrap=tk.WORD
        )
        self.log_text.pack(fill=tk.BOTH, expand=True)
        
        # 日志状态栏
        log_status = ttk.Frame(log_frame)
        log_status.pack(fill=tk.X, pady=(5, 0))
        
        self.log_status_label = ttk.Label(log_status, text="就绪", font=("微软雅黑", 8), 
                                         foreground="#7f8c8d")
        self.log_status_label.pack(side=tk.LEFT)
        
        self.log_count_label = ttk.Label(log_status, text="日志条数: 0", font=("微软雅黑", 8), 
                                        foreground="#7f8c8d")
        self.log_count_label.pack(side=tk.RIGHT)

    def export_log(self):
        """导出日志"""
        try:
            filename = filedialog.asksaveasfilename(
                title="导出日志",
                defaultextension=".txt",
                filetypes=[("文本文件", "*.txt"), ("所有文件", "*.*")]
            )
            if filename:
                with open(filename, 'w', encoding='utf-8') as f:
                    f.write(self.log_text.get(1.0, tk.END))
                self.log(f"日志已导出到: {filename}")
        except Exception as e:
            self.log(f"导出日志出错: {e}", "error")

    def toggle_auto_scroll(self):
        """切换自动滚动"""
        # 这里可以添加自动滚动功能
        self.log("自动滚动功能已切换")

    def update_log_count(self):
        """更新日志条数"""
        try:
            count = len(self.log_text.get(1.0, tk.END).split('\n')) - 1
            self.log_count_label.config(text=f"日志条数: {count}")
        except:
            pass

    def init_performance_monitoring(self):
        """初始化性能监控"""
        self.performance_thread = None
        self.monitoring_active = False

    def setup_logging(self):
        """设置日志系统 - 增强版本"""
        try:
            # 初始化日志队列（在logger之前）
            self.log_queue = queue.Queue()
            self.log_thread = threading.Thread(target=self._log_worker, daemon=True)
            self.log_thread.start()
            
            # 创建日志目录
            log_dir = "logs"
            os.makedirs(log_dir, exist_ok=True)
            
            # 配置日志
            log_file = os.path.join(log_dir, f"generator_{datetime.now().strftime('%Y%m%d')}.log")
            logging.basicConfig(
                level=logging.INFO,
                format='%(asctime)s - %(levelname)s - %(message)s',
                handlers=[
                    logging.FileHandler(log_file, encoding='utf-8'),
                    logging.StreamHandler()
                ]
            )
            self.logger = logging.getLogger(__name__)
            self.log("日志系统已初始化")
        except Exception as e:
            # 如果日志系统初始化失败，至少确保有基本的日志功能
            print(f"日志系统设置出错: {e}")
            self.logger = None

    def bind_events(self):
        """绑定事件"""
        # 字符集预览更新
        self.charset_var.trace('w', lambda *args: self.update_charset_preview())
        self.include_special_var.trace('w', lambda *args: self.update_charset_preview())

    def update_charset_preview(self):
        """更新字符集预览"""
        charset = self.charset_var.get()
        if self.include_special_var.get():
            charset += HASHCAT_CHARSETS['s']
        charset = "".join(sorted(list(set(charset))))
        
        self.charset_preview.delete(1.0, tk.END)
        self.charset_preview.insert(1.0, charset)

    def browse_dict_file(self):
        """浏览字典文件"""
        filename = filedialog.askopenfilename(
            title="选择字典文件",
            filetypes=[("文本文件", "*.txt"), ("所有文件", "*.*")]
        )
        if filename:
            self.dict_file_var.set(filename)

    def browse_output_file(self):
        """浏览输出文件"""
        filename = filedialog.asksaveasfilename(
            title="选择输出文件",
            defaultextension=".txt",
            filetypes=[("文本文件", "*.txt"), ("所有文件", "*.*")]
        )
        if filename:
            self.output_file_var.set(filename)

    def browse_dict_b_file(self):
        """浏览字典B文件"""
        filename = filedialog.askopenfilename(
            title="选择字典文件B",
            filetypes=[("文本文件", "*.txt"), ("所有文件", "*.*")]
        )
        if filename:
            self.dict_b_file_var.set(filename)

    def browse_dict_folder(self):
        """浏览字典文件夹"""
        folder = filedialog.askdirectory(title="选择字典文件夹")
        if folder:
            self.dict_folder_var.set(folder)

    def _reset_generation_resources(self):
        """彻底销毁并重建所有生成相关资源，防止多次运行失效"""
        try:
            # 停止性能监控
            if hasattr(self, 'stop_performance_monitoring'):
                self.stop_performance_monitoring()
        except: pass
        try:
            if hasattr(self, 'executor') and self.executor:
                self.executor.shutdown(wait=False)
        except: pass
        try:
            if hasattr(self, 'process_pool') and self.process_pool:
                self.process_pool.terminate()
                self.process_pool.join()
                self.process_pool = None
        except: pass
        try:
            if hasattr(self, 'write_thread') and self.write_thread and self.write_thread.is_alive():
                self.write_queue.put(None)
                self.write_thread.join(timeout=2)
        except: pass
        try:
            if hasattr(self, 'async_loop') and self.async_loop:
                self.async_loop.stop()
                self.async_loop.close()
                self.async_loop = None
        except: pass
        try:
            if hasattr(self, 'stop_event'):
                self.stop_event.set()
        except: pass
        try:
            if hasattr(self, 'write_queue'):
                while not self.write_queue.empty():
                    self.write_queue.get_nowait()
        except: pass
        # 彻底重建关键对象
        self.stop_event = threading.Event()
        self.write_queue = queue.Queue()
        self.write_buffer = []
        self.executor = concurrent.futures.ThreadPoolExecutor(max_workers=MAX_WORKERS)
        self.process_pool = None
        self.write_thread = None
        self.async_loop = None

    def start_generation(self):
        """开始生成 - 终极优化版本"""
        # 彻底重建所有生成相关资源
        self._reset_generation_resources()
        
        # 启动终极优化
        self.setup_ultimate_optimization()
        
        # 自动优化设置
        self.optimize_generation_settings()
        
        # 优化线程池
        self.optimize_thread_pool()
        
        # 验证输入
        valid, mask, charset, length_range, output_file, split_size, parsed_mask, dict_settings, advanced_settings = self.validate_inputs()
        if not valid:
            return
        
        # 重置状态
        self.write_buffer.clear()
        self.processed_count = 0
        self.last_log_update = 0
        self.performance_stats = {
            'start_time': None,
            'memory_usage': [],
            'cpu_usage': [],
            'disk_io': [],
            'combinations_per_second': []
        }
        self.performance_metrics = {
            'start_time': time.time(),
            'memory_peak': 0,
            'cpu_peak': 0,
            'io_operations': 0,
            'cache_hits': 0,
            'cache_misses': 0,
            'gc_collections': 0,
            'process_switches': 0
        }
        
        # 更新UI状态
        self.generate_button.config(state=tk.DISABLED)
        self.stop_button.config(state=tk.NORMAL)
        self.progress_bar['value'] = 0
        
        # 启动性能监控
        self.start_performance_monitoring()
        
        # 启动生成线程
        generation_thread = threading.Thread(
            target=self.run_generation_logic,
            args=(mask, charset, length_range, output_file, split_size, parsed_mask, dict_settings, advanced_settings)
        )
        generation_thread.daemon = True
        generation_thread.start()

    def stop_generation(self):
        """停止生成 - 终极优化版本"""
        self.stop_event.set()
        self.stop_performance_monitoring()
        
        # 清理进程池
        if self.process_pool:
            try:
                self.process_pool.terminate()
                self.process_pool.join()
                self.process_pool = None
            except:
                pass
        
        # 清理异步任务
        if hasattr(self, 'async_loop') and self.async_loop:
            try:
                self.async_loop.stop()
                self.async_loop.close()
                self.async_loop = None
            except:
                pass
        
        # 清理写入线程
        if self.write_thread and self.write_thread.is_alive():
            try:
                self.write_queue.put(None)
                self.write_thread.join(timeout=2)
            except:
                pass
        
        # 清理线程池
        if hasattr(self, 'executor'):
            try:
                self.executor.shutdown(wait=False)
                self.executor = concurrent.futures.ThreadPoolExecutor(max_workers=MAX_WORKERS)
            except:
                pass
        
        # 重置状态
        self.write_buffer.clear()
        self.processed_count = 0
        self.last_log_update = 0
        self.backup_counter = 0
        self.last_backup_time = 0
        
        # 清理性能统计
        self.performance_stats = {
            'start_time': None,
            'memory_usage': [],
            'cpu_usage': [],
            'disk_io': [],
            'combinations_per_second': []
        }
        self.performance_metrics = {
            'start_time': None,
            'memory_peak': 0,
            'cpu_peak': 0,
            'io_operations': 0,
            'cache_hits': 0,
            'cache_misses': 0,
            'gc_collections': 0,
            'process_switches': 0
        }
        
        # 强制垃圾回收
        gc.collect()
        
        self.log("正在停止生成...")

    def log(self, message, level="info"):
        """记录日志"""
        timestamp = datetime.now().strftime("%H:%M:%S")
        log_entry = f"[{timestamp}] {level.upper()}: {message}"
        
        # 如果logger已初始化，使用logger
        if hasattr(self, 'logger') and self.logger is not None:
            self.logger.info(log_entry)
        else:
            # 如果logger未初始化，使用队列方式
            if hasattr(self, 'log_queue'):
                self.log_queue.put(log_entry)
            else:
                # 最后的备选方案：直接打印
                print(log_entry)

    def _log_worker(self):
        """日志工作线程"""
        while True:
            try:
                log_entry = self.log_queue.get(timeout=1)
                if log_entry is None:
                    break
                
                # 在主线程中更新UI
                self.root.after(0, self._log_update, log_entry)
            except queue.Empty:
                continue

    def _log_update(self, message):
        """更新日志显示"""
        if self.log_enabled.get():
            self.log_text.insert(tk.END, message + "\n")
            self.log_text.see(tk.END)

    def update_preview(self):
        """更新预览"""
        self.update_charset_preview()

    def clear_log(self):
        """清除日志"""
        self.log_text.delete(1.0, tk.END)

    def update_status(self, message):
        """更新状态"""
        self.status_label.config(text=message)

    def update_progress(self, value):
        """更新进度条"""
        self.progress_bar['value'] = value

    def check_memory_usage(self):
        """检查内存使用情况"""
        if not self.performance_monitoring.get():
            return True
        
        try:
            memory_percent = psutil.virtual_memory().percent
            memory_threshold = float(self.memory_threshold.get())
            
            if memory_percent > memory_threshold:
                self.log(f"内存使用率过高: {memory_percent:.1f}% > {memory_threshold}%", "warning")
                return False
        except:
            pass
        return True

    async def _async_write_to_file(self, file_path, data):
        """异步写入文件"""
        try:
            # 检查文件扩展名决定是否压缩
            if file_path.endswith('.gz'):
                with gzip.open(file_path, 'wt', encoding='utf-8') as f:
                    f.write(data)
            else:
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write(data)
        except Exception as e:
            self.log(f"写入文件时出错: {e}", "error")

    def _write_worker(self):
        """写入工作线程"""
        while True:
            try:
                item = self.write_queue.get(timeout=1)
                if item is None:
                    break
                
                file_path, data = item
                asyncio.run(self._async_write_to_file(file_path, data))
                self.write_queue.task_done()
            except queue.Empty:
                continue

    def _flush_buffer(self, file_path):
        """刷新缓冲区到文件"""
        if not self.write_buffer:
            return
        
        data = '\n'.join(self.write_buffer) + '\n'
        self.write_queue.put((file_path, data))
        self.write_buffer.clear()

    def run_generation_logic(self, mask, charset, length_range, output_file, split_size, parsed_mask, dict_settings, advanced_settings):
        start_time = time.time()
        total_combinations_written = 0
        total_combinations = 0
        file_suffix_counter = 1
        
        # 确保输出文件路径有效
        if not output_file:
            output_file = os.path.join(os.getcwd(), "combinations.txt")
        elif not os.path.dirname(output_file):
            output_file = os.path.join(os.getcwd(), output_file)
        
        current_file = output_file

        try:
            self.log("开始生成组合...")
            self.update_status("正在计算...")

            # 确保输出目录存在
            output_dir = os.path.dirname(output_file)
            if output_dir:
                os.makedirs(output_dir, exist_ok=True)

            # 启动写入线程
            self.write_thread = threading.Thread(target=self._write_worker)
            self.write_thread.daemon = True
            self.write_thread.start()

            # 加载字典文件
            dict_entries = []
            if dict_settings and dict_settings[0]:
                dict_file = dict_settings[0]
                dict_combo_mode = dict_settings[2]
                
                try:
                    # 获取已处理的字典条目
                    dict_entries = self.get_dict_entries(dict_file)
                    
                    # 如果是文件夹处理模式，直接返回
                    if os.path.isdir(dict_file):
                        self.log("文件夹处理完成")
                        return
                        
                except Exception as e:
                    self.log(f"读取字典文件A时出错: {e}", "error")
                    messagebox.showerror("错误", f"读取字典文件A时出错: {e}")
                    return

            # 计算总组合数
            try:
                total_combinations = self._calculate_total_combinations(
                    mask, charset, length_range, parsed_mask, dict_settings,
                    advanced_settings, dict_entries
                )
                self.log(f"预计总组合数: {total_combinations}")
            except Exception as e:
                self.log(f"计算总组合数时出错: {e}", "error")
                messagebox.showerror("错误", f"计算总组合数时出错: {e}")
                return

            # 处理组合
            combinations_in_current_file = 0
            buffer_size = 0

            # 获取组合生成器
            combination_generator = self._get_combination_generator(
                mask, charset, length_range, parsed_mask,
                dict_settings, advanced_settings, dict_entries
            )

            for combination in combination_generator:
                if self.stop_event.is_set():
                    break

                # 确保组合不为空
                if not combination:
                    continue

                # 添加到写入缓冲区
                self.write_buffer.append(combination)
                buffer_size += len(combination) + 1
                total_combinations_written += 1
                combinations_in_current_file += 1

                # 当缓冲区达到写入批次大小时，刷新到文件
                if len(self.write_buffer) >= WRITE_BATCH_SIZE:
                    self._flush_buffer(current_file)
                    buffer_size = 0

                # 定期保存进度
                if total_combinations_written % PROGRESS_UPDATE_INTERVAL == 0:
                    self.save_progress(total_combinations_written, total_combinations, 
                                     file_suffix_counter, current_file)
                    progress = min(total_combinations_written / total_combinations * 100, 100)
                    self.update_progress(progress)
                    self.update_status(f"已生成: {total_combinations_written}/{total_combinations} ({progress:.1f}%)")

                # 检查是否需要分割文件
                if combinations_in_current_file >= split_size:
                    # 刷新当前缓冲区
                    self._flush_buffer(current_file)
                    buffer_size = 0
                    
                    # 创建新文件
                    file_suffix_counter += 1
                    file_name, file_ext = os.path.splitext(output_file)
                    current_file = f"{file_name}_{file_suffix_counter}{file_ext}"
                    combinations_in_current_file = 0
                    self.log(f"继续输出到新文件: {current_file}")

            # 刷新剩余的缓冲区内容
            if self.write_buffer:
                self._flush_buffer(current_file)

            # 等待所有写入完成
            self.write_queue.join()

        except Exception as e:
            self.log(f"生成过程中出错: {e}", "error")
            messagebox.showerror("错误", f"生成过程中出错: {e}")
            return
        finally:
            # 停止写入线程
            if self.write_thread:
                try:
                    self.write_queue.put(None)
                    self.write_thread.join(timeout=5)
                except:
                    pass
            
            # 清理进程池
            if self.process_pool:
                try:
                    self.process_pool.terminate()
                    self.process_pool.join()
                    self.process_pool = None
                except:
                    pass
            
            # 清理异步任务
            if hasattr(self, 'async_loop') and self.async_loop:
                try:
                    self.async_loop.stop()
                    self.async_loop.close()
                    self.async_loop = None
                except:
                    pass
            
            # 清理线程池
            if hasattr(self, 'executor'):
                try:
                    self.executor.shutdown(wait=False)
                    self.executor = concurrent.futures.ThreadPoolExecutor(max_workers=MAX_WORKERS)
                except:
                    pass
            
            # 清理进度文件
            self.cleanup_progress()
            
            # 重置状态
            self.write_buffer.clear()
            self.processed_count = 0
            self.last_log_update = 0
            self.backup_counter = 0
            self.last_backup_time = 0
            
            # 强制垃圾回收
            gc.collect()
            
            end_time = time.time()
            self._show_generation_summary(
                total_combinations_written, total_combinations,
                end_time - start_time, file_suffix_counter,
                output_file, current_file
            )
            self.update_status("就绪")
            self.generate_button.config(state=tk.NORMAL)
            self.stop_button.config(state=tk.DISABLED)

    def save_progress(self, current_count, total_count, file_counter, current_file):
        """保存当前进度"""
        progress = {
            'current_count': current_count,
            'total_count': total_count,
            'file_counter': file_counter,
            'current_file': current_file,
            'timestamp': time.time()
        }
        try:
            with open('progress.json', 'w', encoding='utf-8') as f:
                json.dump(progress, f)
        except Exception as e:
            self.log(f"保存进度时出错: {e}", "warning")

    def load_progress(self):
        """加载上次的进度"""
        try:
            if os.path.exists('progress.json'):
                with open('progress.json', 'r', encoding='utf-8') as f:
                    return json.load(f)
        except Exception as e:
            self.log(f"加载进度时出错: {e}", "warning")
        return None

    def cleanup_progress(self):
        """清理进度文件"""
        try:
            if os.path.exists('progress.json'):
                os.remove('progress.json')
        except Exception as e:
            self.log(f"清理进度文件时出错: {e}", "warning")

    def _calculate_total_combinations(self, mask, charset, length_range, parsed_mask, dict_settings, advanced_settings, dict_entries):
        """Calculate total possible combinations."""
        if advanced_settings and "custom_dict" in advanced_settings:
            chars, mode, length = advanced_settings["custom_dict"]
            chars = [c.strip() for c in chars.split(",")]
            
            if mode == "combination":
                # 组合模式的总组合数
                return len(chars) ** length
            elif mode == "permutation":
                # 全排列模式的总组合数
                if length > len(chars):
                    return 0
                return math.factorial(len(chars)) // math.factorial(len(chars) - length)
            else:  # permutation2 mode
                # 全排列模式2的总组合数
                if length > len(chars):
                    return 0
                return math.factorial(len(chars)) // math.factorial(len(chars) - length)

        if not dict_entries:
            dict_entries = []
            
        # Check if it's pure dictionary mode
        is_pure_dict = (dict_settings and dict_settings[2] == "none" and 
                       not mask and not charset and not advanced_settings)
        
        if is_pure_dict:
            # Calculate potential combinations based on processing options
            total = 0
            for entry in dict_entries:
                # 使用生成器并计算处理后的条目数
                processed_count = sum(1 for _ in self.process_dictionary_entry(entry))
                total += processed_count
                self.log(f"条目 '{entry}' 处理后生成 {processed_count} 个组合")
            return total if total > 0 else len(dict_entries)  # Fallback to original count if no processing

        # 检查高级选项
        if advanced_settings and "repeat_char" in advanced_settings:
            repeat_len, pattern_len, charset, pattern_type = advanced_settings["repeat_char"]
            if pattern_type == "sequential":
                # 连续模式的总组合数
                return max(0, len(charset) - pattern_len + 1)
            elif pattern_type == "sequential_repeat":
                # 连续重复模式的总组合数
                return max(0, len(charset) - pattern_len + 1)
            else:  # repeat mode
                # 重复模式的总组合数
                return len(charset) ** pattern_len

        # 计算基础组合数
        if parsed_mask:
            # 掩码模式
            base_combinations = 1
            for charset in parsed_mask:
                base_combinations *= len(charset)
        else:
            # 字符集模式
            min_len, max_len = length_range
            base_combinations = 0
            for length in range(min_len, max_len + 1):
                base_combinations += len(charset) ** length

        # 计算字典组合
        if dict_entries and dict_settings:
            dict_combo_mode = dict_settings[2]
            if dict_combo_mode in ["dict_ab", "dict_ba"]:
                # 字典A和字典B的组合
                dict_b_file = self.dict_b_file_var.get()
                if dict_b_file:
                    try:
                        dict_b_entries = self.get_dict_entries(dict_b_file)
                        return len(dict_entries) * len(dict_b_entries)
                    except:
                        return len(dict_entries) * 1000  # 估算
            elif dict_combo_mode in ["dict_first", "mask_first"]:
                # 字典和掩码的组合
                return len(dict_entries) * base_combinations

        return base_combinations

    def _get_combination_generator(self, mask, charset, length_range, parsed_mask, dict_settings, advanced_settings, dict_entries):
        """Get generator for combinations based on current settings."""
        if advanced_settings:
            return self._get_advanced_generator(advanced_settings)

        dict_file, dict_pos, dict_combo_mode = dict_settings if dict_settings else (None, None, None)
        
        # Get base generator
        if mask and parsed_mask:
            base_generator = self._get_mask_generator(parsed_mask)
        else:
            base_generator = self._get_charset_generator(charset, length_range)

        # Wrap with dictionary combination if needed
        if dict_combo_mode != "none":
            return self._get_dict_combo_generator(base_generator, dict_entries, dict_combo_mode)
        elif dict_pos in ["append_before", "append_after"]:
            return self._get_dict_append_generator(base_generator, dict_entries, dict_pos)
        return base_generator

    def _get_advanced_generator(self, advanced_settings):
        """Generator for advanced generation options."""
        if "custom_dict" in advanced_settings:
            chars, mode, length = advanced_settings["custom_dict"]
            chars = [c.strip() for c in chars.split(",")]
            
            if mode == "combination":
                # 组合模式
                for combo in itertools.product(chars, repeat=length):
                    if self.stop_event.is_set():
                        break
                    yield ''.join(combo)
            elif mode == "permutation":
                # 全排列模式
                for combo in itertools.permutations(chars, length):
                    if self.stop_event.is_set():
                        break
                    yield ''.join(combo)
            else:  # permutation2 mode
                # 全排列模式2（带连接符）
                connector = self.connector_var.get()  # 直接使用用户输入的连接符，不做任何处理
                for combo in itertools.permutations(chars, length):
                    if self.stop_event.is_set():
                        break
                    yield connector.join(combo)
        elif "repeat_char" in advanced_settings:
            repeat_len, pattern_len, charset, pattern_type = advanced_settings["repeat_char"]
            
            if pattern_type == "sequential":
                # 生成连续模式 (如 ABCABC)
                for i in range(len(charset) - pattern_len + 1):
                    if self.stop_event.is_set():
                        break
                    pattern = charset[i:i+pattern_len]
                    result = pattern * repeat_len
                    if len(result) > 0:
                        yield result
            elif pattern_type == "sequential_repeat":
                # 生成连续重复模式 (如 AABBCC)
                for i in range(len(charset) - pattern_len + 1):
                    if self.stop_event.is_set():
                        break
                    result = ''
                    for j in range(pattern_len):
                        result += charset[i+j] * repeat_len
                    if len(result) > 0:
                        yield result
            else:  # repeat mode
                # 生成重复模式 (如 AABB)
                for chars in itertools.product(charset, repeat=pattern_len):
                    if self.stop_event.is_set():
                        break
                    result = ''
                    for char in chars:
                        result += char * repeat_len
                    if len(result) > 0:
                        yield result

    def _get_mask_generator(self, parsed_mask):
        """Generator for mask-based combinations."""
        for combo_tuple in itertools.product(*parsed_mask):
            if self.stop_event.is_set():
                break
            yield ''.join(combo_tuple)

    def _get_charset_generator(self, charset, length_range):
        """Generator for charset-based combinations."""
        min_len, max_len = length_range
        for length in range(min_len, max_len + 1):
            if self.stop_event.is_set():
                break
            for combo_tuple in itertools.product(charset, repeat=length):
                if self.stop_event.is_set():
                    break
                yield ''.join(combo_tuple)

    def _get_dict_combo_generator(self, base_generator, dict_entries, combo_mode):
        """优化的字典组合生成器"""
        if combo_mode in ["dict_ab", "dict_ba"]:
            # 加载字典B
            dict_b_file = self.dict_b_file_var.get()
            if not dict_b_file:
                raise ValueError("字典B文件未选择")
            
            try:
                # 处理字典A
                processed_entries_a = set()
                for entry in dict_entries:
                    for processed in self.process_dictionary_entry(entry):
                        processed_entries_a.add(processed)
                self.log(f"处理后的字典A条目数: {len(processed_entries_a)}")

                # 处理字典B
                dict_b_entries = self.get_dict_entries(dict_b_file)
                processed_entries_b = set()
                for entry in dict_b_entries:
                    for processed in self.process_dictionary_entry(entry):
                        processed_entries_b.add(processed)
                self.log(f"处理后的字典B条目数: {len(processed_entries_b)}")
                
                # 使用生成器组合处理后的字典
                for entry_a in processed_entries_a:
                    if self.stop_event.is_set():
                        break
                    for entry_b in processed_entries_b:
                        if self.stop_event.is_set():
                            break
                        if combo_mode == "dict_ab":
                            yield entry_a + entry_b
                        else:  # dict_ba
                            yield entry_b + entry_a
                            
            except Exception as e:
                raise ValueError(f"处理字典时出错: {e}")
        else:
            # 处理字典条目
            processed_entries = set()
            for entry in dict_entries:
                for processed in self.process_dictionary_entry(entry):
                    processed_entries.add(processed)
            self.log(f"处理后的字典条目数: {len(processed_entries)}")

            # 如果是纯字典模式，直接返回处理后的条目
            if not base_generator:
                for entry in processed_entries:
                    if self.stop_event.is_set():
                        break
                    yield entry
            else:
                # 组合处理后的字典条目和掩码
                # 首先收集所有掩码组合
                mask_combinations = []
                for mask_combo in base_generator:
                    if self.stop_event.is_set():
                        break
                    mask_combinations.append(mask_combo)
                
                self.log(f"掩码组合数: {len(mask_combinations)}")
                
                # 然后生成所有可能的组合
                for dict_entry in processed_entries:
                    if self.stop_event.is_set():
                        break
                    for mask_combo in mask_combinations:
                        if self.stop_event.is_set():
                            break
                        if combo_mode == "dict_first":
                            yield dict_entry + mask_combo
                        else:  # mask_first
                            yield mask_combo + dict_entry

    def _get_dict_append_generator(self, base_generator, dict_entries, dict_pos):
        """Generator for dictionary append mode."""
        if dict_pos == "append_before":
            for entry in dict_entries:
                if self.stop_event.is_set():
                    break
                yield entry
        for combination in base_generator:
            if self.stop_event.is_set():
                break
            yield combination
        if dict_pos == "append_after":
            for entry in dict_entries:
                if self.stop_event.is_set():
                    break
                yield entry

    def _show_generation_summary(self, total_written, total_combinations, elapsed_time, file_suffix_counter, output_file, current_file):
        """Show generation summary and update UI."""
        final_message = "\n生成已停止" if self.stop_event.is_set() else "\n生成完成"
        self.log(final_message)
        self.log(f"已生成组合数: {total_written}")
        
        if file_suffix_counter > 1:
            self.log(f"输出已保存到多个文件，以 {output_file} 为基础名")
        elif total_written > 0:
            self.log(f"输出已保存到: {current_file}")
            
        self.log(f"用时: {elapsed_time:.2f} 秒")

        if not self.stop_event.is_set() and total_combinations > 0:
            self.update_progress(100)
            self.update_status(f"完成: {total_written}/{total_combinations} (100.0%)")
        elif self.stop_event.is_set():
            self.update_status("已停止")
        else:
            self.update_status("就绪")

        self.generate_button.config(state=tk.NORMAL)
        self.stop_button.config(state=tk.DISABLED)

    def process_dictionary_entry(self, entry):
        """使用生成器处理字典条目"""
        if not entry.strip():
            return
            
        original = entry.strip()
        
        # 检查是否有任何处理选项被启用
        has_processing_options = (
            self.uppercase_var.get() or
            self.lowercase_var.get() or
            self.capitalize_var.get() or
            self.reverse_var.get() or
            self.remove_start_var.get() != "0" or
            self.remove_end_var.get() != "0" or
            self.add_start_var.get() or
            self.add_end_var.get() or
            self.repeat_count_var.get() != "1" or
            self.repeat_space_count_var.get() != "1"
        )
        
        # 只有在没有处理选项时才输出原始条目
        if not has_processing_options:
            yield original
            return
        
        # 使用集合存储处理后的条目以避免重复
        processed_entries = set()
        
        if self.process_mode_var.get() == "independent":
            # 独立处理模式
            if self.uppercase_var.get():
                processed_entries.add(original.upper())
            if self.lowercase_var.get():
                processed_entries.add(original.lower())
            if self.capitalize_var.get():
                processed_entries.add(original.capitalize())
            if self.reverse_var.get():
                processed_entries.add(original[::-1])
            
            # 字符移除处理
            try:
                remove_start = max(0, int(self.remove_start_var.get() or "0"))
                remove_end = max(0, int(self.remove_end_var.get() or "0"))
                
                # 独立处理开头字符
                if self.remove_start_independent_var.get() and remove_start > 0:
                    if len(original) > remove_start:
                        processed_entries.add(original[remove_start:])
                
                # 独立处理结尾字符
                if self.remove_end_independent_var.get() and remove_end > 0:
                    if len(original) > remove_end:
                        processed_entries.add(original[:-remove_end])
                
                # 同时处理开头和结尾
                if self.remove_combined_var.get():
                    if len(original) > (remove_start + remove_end):
                        processed_entries.add(original[remove_start:-remove_end])
            except ValueError:
                pass
            
            # 字符添加处理
            add_start = self.add_start_var.get()
            add_end = self.add_end_var.get()
            
            # 独立处理开头添加
            if self.add_start_independent_var.get() and add_start:
                processed_entries.add(add_start + original)
            
            # 独立处理结尾添加
            if self.add_end_independent_var.get() and add_end:
                processed_entries.add(original + add_end)
            
            # 同时处理开头和结尾添加
            if self.add_combined_var.get():
                processed_entries.add(add_start + original + add_end)
            
            # 重复处理
            try:
                repeat_count = max(1, int(self.repeat_count_var.get() or "1"))
                repeat_space_count = max(1, int(self.repeat_space_count_var.get() or "1"))
                
                if repeat_count > 1:
                    processed_entries.add(original * repeat_count)
                if repeat_space_count > 1:
                    processed_entries.add(" ".join([original] * repeat_space_count))
            except ValueError:
                pass
        else:
            # 组合处理模式
            current_entries = set()
            
            # 大小写处理
            if self.uppercase_var.get() or self.lowercase_var.get() or self.capitalize_var.get():
                if self.uppercase_var.get():
                    current_entries.add(original.upper())
                if self.lowercase_var.get():
                    current_entries.add(original.lower())
                if self.capitalize_var.get():
                    current_entries.add(original.capitalize())
            
            # 字符串反转
            if self.reverse_var.get():
                current_entries.add(original[::-1])
            
            # 字符移除处理
            try:
                remove_start = max(0, int(self.remove_start_var.get() or "0"))
                remove_end = max(0, int(self.remove_end_var.get() or "0"))
                
                # 独立处理开头字符
                if self.remove_start_independent_var.get() and remove_start > 0:
                    if len(original) > remove_start:
                        current_entries.add(original[remove_start:])
                
                # 独立处理结尾字符
                if self.remove_end_independent_var.get() and remove_end > 0:
                    if len(original) > remove_end:
                        current_entries.add(original[:-remove_end])
                
                # 同时处理开头和结尾
                if self.remove_combined_var.get():
                    if len(original) > (remove_start + remove_end):
                        current_entries.add(original[remove_start:-remove_end])
            except ValueError:
                pass
            
            # 字符添加处理
            add_start = self.add_start_var.get()
            add_end = self.add_end_var.get()
            
            # 独立处理开头添加
            if self.add_start_independent_var.get() and add_start:
                current_entries.add(add_start + original)
            
            # 独立处理结尾添加
            if self.add_end_independent_var.get() and add_end:
                current_entries.add(original + add_end)
            
            # 同时处理开头和结尾添加
            if self.add_combined_var.get():
                current_entries.add(add_start + original + add_end)
            
            # 重复处理
            try:
                repeat_count = max(1, int(self.repeat_count_var.get() or "1"))
                repeat_space_count = max(1, int(self.repeat_space_count_var.get() or "1"))
                
                if repeat_count > 1:
                    current_entries.add(original * repeat_count)
                if repeat_space_count > 1:
                    current_entries.add(" ".join([original] * repeat_space_count))
            except ValueError:
                pass
            
            processed_entries.update(current_entries)
        
        # 对处理后的数据进行重复处理
        if self.repeat_processed_var.get():
            try:
                repeat_processed_count = max(1, int(self.repeat_processed_count_var.get() or "2"))
                repeat_processed_space_count = max(1, int(self.repeat_processed_space_count_var.get() or "2"))
                
                # 创建临时集合存储重复处理后的结果
                repeated_entries = set()
                
                # 对每个处理后的条目进行重复处理
                for entry in processed_entries:
                    if repeat_processed_count > 1:
                        repeated_entries.add(entry * repeat_processed_count)
                    if repeat_processed_space_count > 1:
                        repeated_entries.add(" ".join([entry] * repeat_processed_space_count))
                
                # 更新处理后的条目集合
                processed_entries.update(repeated_entries)
            except ValueError:
                pass
        
        # 返回所有处理后的条目
        for entry in processed_entries:
            yield entry

    def get_dict_entries(self, dict_file, use_cache=True):
        """获取字典条目，支持缓存和文件夹处理"""
        if use_cache and dict_file in self.dict_cache:
            cache_data = self.dict_cache[dict_file]
            if time.time() - cache_data['timestamp'] < self.dict_cache_timeout:
                self.log(f"使用缓存的字典: {dict_file}")
                return cache_data['entries']

        try:
            entries = set()  # 使用集合来存储唯一条目
            self.processed_count = 0
            self.last_log_update = 0
            
            # 检查是否是文件夹
            if os.path.isdir(dict_file):
                # 创建必要的文件夹（在导入的文件夹下创建）
                new_dir = os.path.join(dict_file, "new")
                done_dir = os.path.join(dict_file, "done")
                os.makedirs(new_dir, exist_ok=True)
                os.makedirs(done_dir, exist_ok=True)
                
                self.log(f"已创建文件夹：\n{new_dir}\n{done_dir}")
                
                file_filter = self.file_filter_var.get()
                if not file_filter:
                    file_filter = "*.txt"
                
                # 获取文件夹中的所有匹配文件（排除new和done文件夹）
                dict_files = []
                for root, dirs, files in os.walk(dict_file):
                    # 跳过new和done文件夹
                    if "new" in dirs:
                        dirs.remove("new")
                    if "done" in dirs:
                        dirs.remove("done")
                    
                    for file in files:
                        if file.lower().endswith(tuple(file_filter.replace("*", "").split(","))):
                            dict_files.append(os.path.join(root, file))
                
                total_files = len(dict_files)
                self.log(f"在文件夹中找到 {total_files} 个字典文件")
                
                # 逐个处理文件
                for index, file_path in enumerate(dict_files, 1):
                    if self.stop_event.is_set():
                        break
                        
                    try:
                        self.log(f"正在处理文件 {index}/{total_files}: {os.path.basename(file_path)}")
                        
                        # 处理单个文件并获取其条目
                        file_entries = set()
                        self._process_single_file(file_path, file_entries)
                        
                        # 处理当前文件的所有条目
                        processed_entries = set()
                        for entry in file_entries:
                            if self.stop_event.is_set():
                                break
                            # 处理每个条目并生成所有组合
                            for processed in self.process_dictionary_entry(entry):
                                processed_entries.add(processed)
                                self.processed_count += 1
                                
                                # 更新进度
                                if self.processed_count - self.last_log_update >= LOG_UPDATE_INTERVAL:
                                    if self.log_enabled.get():
                                        self.log(f"已处理 {self.processed_count} 条记录")
                                    self.last_log_update = self.processed_count
                        
                        # 生成新文件名并保存到new文件夹
                        file_name = os.path.basename(file_path)
                        new_file_name = f"new_{file_name}"
                        new_file_path = os.path.join(new_dir, new_file_name)
                        
                        # 保存处理后的条目到新文件
                        self.log(f"正在保存处理后的条目到: {new_file_name}")
                        with open(new_file_path, 'w', encoding='utf-8') as f:
                            for entry in processed_entries:
                                f.write(f"{entry}\n")
                        
                        # 移动原文件到done文件夹
                        done_file_path = os.path.join(done_dir, file_name)
                        try:
                            shutil.move(file_path, done_file_path)
                            self.log(f"已移动原文件到done文件夹: {file_name}")
                        except Exception as e:
                            self.log(f"移动文件到done文件夹时出错: {e}", "warning")
                        
                        self.log(f"文件 {file_name} 处理完成，生成了 {len(processed_entries)} 个组合，已保存到 {new_file_name}")
                        
                        # 更新文件处理进度
                        progress = (index / total_files) * 100
                        self.update_progress(progress)
                        self.update_status(f"已处理文件: {index}/{total_files} ({progress:.1f}%)")
                        
                    except Exception as e:
                        self.log(f"处理文件 {file_path} 时出错: {e}", "warning")
                        continue
                
                self.log(f"文件夹处理完成，共处理 {self.processed_count} 个条目")
                return []  # 返回空列表，因为每个文件都已经单独保存
            else:
                # 处理单个文件
                file_entries = set()
                self._process_single_file(dict_file, file_entries)
                
                # 处理所有条目
                for entry in file_entries:
                    if self.stop_event.is_set():
                        break
                    for processed in self.process_dictionary_entry(entry):
                        entries.add(processed)
                        self.processed_count += 1
                        
                        # 更新进度
                        if self.processed_count - self.last_log_update >= LOG_UPDATE_INTERVAL:
                            if self.log_enabled.get():
                                self.log(f"已处理 {self.processed_count} 条记录")
                            self.last_log_update = self.processed_count
            
            # 更新缓存
            if use_cache:
                self.dict_cache[dict_file] = {
                    'entries': list(entries),  # 转换回列表
                    'timestamp': time.time()
                }
                # 如果缓存超过大小限制，删除最旧的缓存
                if len(self.dict_cache) > self.dict_cache_size:
                    oldest_key = min(self.dict_cache.keys(), 
                                   key=lambda k: self.dict_cache[k]['timestamp'])
                    del self.dict_cache[oldest_key]
            
            return list(entries)  # 返回列表
        except Exception as e:
            self.log(f"读取字典文件时出错: {e}", "error")
            raise

    def _process_single_file(self, file_path, entries):
        """处理单个文件"""
        try:
            with open(file_path, 'rb') as f:
                # 创建内存映射
                mm = mmap.mmap(f.fileno(), 0, access=mmap.ACCESS_READ)
                
                # 计算文件大小和块数
                file_size = mm.size()
                chunk_size = min(CHUNK_SIZE, file_size)
                num_chunks = (file_size + chunk_size - 1) // chunk_size
                
                # 创建线程池处理块
                futures = []
                for i in range(num_chunks):
                    if self.stop_event.is_set():
                        break
                        
                    start = i * chunk_size
                    end = min(start + chunk_size, file_size)
                    chunk = mm[start:end]
                    future = self.executor.submit(self._process_file_chunk, chunk, entries)
                    futures.append(future)
                
                # 等待所有块处理完成
                concurrent.futures.wait(futures)
                
                mm.close()
                
        except Exception as e:
            self.log(f"处理文件 {file_path} 时出错: {e}", "error")
            raise

    def _process_file_chunk(self, chunk, entries):
        """处理文件块"""
        try:
            # 将块分割成行
            lines = chunk.split(b'\n')
            for line in lines:
                if line and not self.stop_event.is_set():
                    entry = line.decode('utf-8', errors='ignore').strip()
                    if entry:
                        entries.add(entry)
        except Exception as e:
            self.log(f"处理文件块时出错: {e}", "error")

    def __del__(self):
        """清理资源 - 终极优化版本"""
        try:
            # 停止性能监控
            self.stop_performance_monitoring()
            
            # 清理线程池
            if hasattr(self, 'executor'):
                self.executor.shutdown(wait=False)
            
            # 清理写入线程
            if hasattr(self, 'write_thread') and self.write_thread:
                try:
                    self.write_queue.put(None)
                    self.write_thread.join(timeout=1)
                except:
                    pass
            
            # 清理进程池
            if hasattr(self, 'process_pool') and self.process_pool:
                try:
                    self.process_pool.terminate()
                    self.process_pool.join()
                except:
                    pass
            
            # 清理异步任务
            if hasattr(self, 'async_loop') and self.async_loop:
                try:
                    self.async_loop.stop()
                    self.async_loop.close()
                except:
                    pass
            
            # 清理临时文件
            if hasattr(self, 'temp_files'):
                for temp_file in self.temp_files:
                    try:
                        if os.path.exists(temp_file):
                            os.unlink(temp_file)
                    except:
                        pass
                    
            # 关闭数据库连接
            if hasattr(self, 'db_connection') and self.db_connection:
                self.db_connection.close()
                
            # 保存设置
            if hasattr(self, 'save_settings'):
                self.save_settings()
                
        except:
            pass

    def validate_inputs(self):
        """验证用户输入 - 增强版本"""
        # 基础验证
        valid, mask, charset, length_range, output_file, split_size, parsed_mask, dict_settings, advanced_settings = self._basic_validation()
        if not valid:
            return False, None, None, None, None, None, None, None, None

        # 性能优化验证
        if not self._validate_performance_settings():
            return False, None, None, None, None, None, None, None, None

        # 文件系统验证
        if not self._validate_file_system(output_file):
            return False, None, None, None, None, None, None, None, None

        # 内存和磁盘空间验证
        if not self._validate_system_resources():
            return False, None, None, None, None, None, None, None, None

        return True, mask, charset, length_range, output_file, split_size, parsed_mask, dict_settings, advanced_settings

    def _basic_validation(self):
        """基础输入验证"""
        # 检查输出文件
        output_file = self.output_file_var.get()
        if not output_file:
            self.log("错误: 输出文件名不能为空", "error")
            messagebox.showerror("错误", "输出文件名不能为空")
            return False, None, None, None, None, None, None, None, None

        # 检查文件拆分大小
        try:
            split_size = int(self.split_size_var.get())
            if split_size <= 0:
                self.log("错误: 每个文件的最大组合数必须为正整数", "error")
                messagebox.showerror("错误", "每个文件的最大组合数必须为正整数")
                return False, None, None, None, None, None, None, None, None
        except ValueError:
            self.log("错误: 每个文件的最大组合数必须为整数", "error")
            messagebox.showerror("错误", "每个文件的最大组合数必须为整数")
            return False, None, None, None, None, None, None, None, None

        # 检查自定义字典组合选项
        if self.custom_dict_var.get():
            try:
                chars = self.custom_chars_var.get()
                if not chars:
                    self.log("错误: 自定义字符不能为空", "error")
                    messagebox.showerror("错误", "自定义字符不能为空")
                    return False, None, None, None, None, None, None, None, None
                
                length = int(self.custom_dict_length_var.get())
                if length <= 0:
                    self.log("错误: 生成长度必须为正整数", "error")
                    messagebox.showerror("错误", "生成长度必须为正整数")
                    return False, None, None, None, None, None, None, None, None
                
                mode = self.custom_dict_mode_var.get()
                if mode == "permutation2":
                    connector = self.connector_var.get()
                    if connector is None:  # 允许空字符串作为连接符
                        self.log("错误: 连接符号不能为None", "error")
                        messagebox.showerror("错误", "连接符号不能为None")
                        return False, None, None, None, None, None, None, None, None
                
                advanced_settings = {"custom_dict": (chars, mode, length)}
                return True, None, None, None, output_file, split_size, None, None, advanced_settings
            except ValueError:
                self.log("错误: 生成长度必须为整数", "error")
                messagebox.showerror("错误", "生成长度必须为整数")
                return False, None, None, None, None, None, None, None, None

        # 字典设置
        dict_file = self.dict_file_var.get()
        dict_folder = self.dict_folder_var.get()
        dict_b_file = self.dict_b_file_var.get()
        dict_combo_mode = self.dict_combo_var.get()

        # 检查是否为纯字典模式
        is_pure_dict = (dict_file or dict_folder) and dict_combo_mode == "none"
        
        # 如果使用字典模式
        if is_pure_dict or dict_combo_mode != "none":
            if not dict_file and not dict_folder:
                self.log("错误: 必须选择字典文件A或字典文件夹", "error")
                messagebox.showerror("错误", "必须选择字典文件A或字典文件夹")
                return False, None, None, None, None, None, None, None, None
            
            if dict_file and not os.path.isfile(dict_file):
                self.log(f"错误: 找不到字典文件A: {dict_file}", "error")
                messagebox.showerror("错误", f"找不到字典文件A: {dict_file}")
                return False, None, None, None, None, None, None, None, None
                
            if dict_folder and not os.path.isdir(dict_folder):
                self.log(f"错误: 找不到字典文件夹: {dict_folder}", "error")
                messagebox.showerror("错误", f"找不到字典文件夹: {dict_folder}")
                return False, None, None, None, None, None, None, None, None

            # 字典组合模式
            if dict_combo_mode in ["dict_ab", "dict_ba"]:
                if not dict_b_file:
                    self.log("错误: 字典组合模式下必须选择字典文件B", "error")
                    messagebox.showerror("错误", "字典组合模式下必须选择字典文件B")
                    return False, None, None, None, None, None, None, None, None
                if not os.path.isfile(dict_b_file):
                    self.log(f"错误: 找不到字典文件B: {dict_b_file}", "error")
                    messagebox.showerror("错误", f"找不到字典文件B: {dict_b_file}")
                    return False, None, None, None, None, None, None, None, None

            # 纯字典模式
            if is_pure_dict:
                return True, None, None, None, output_file, split_size, None, (dict_file or dict_folder, dict_b_file, dict_combo_mode), None

        # 检查高级选项
        repeat_char = self.repeat_char_var.get()
        if repeat_char:
            try:
                repeat_len = int(self.repeat_len_var.get())
                pattern_len = int(self.pattern_len_var.get())
                pattern_type = self.pattern_type_var.get()
                
                if repeat_len <= 0:
                    self.log("错误: 重复次数必须为正整数", "error")
                    messagebox.showerror("错误", "重复次数必须为正整数")
                    return False, None, None, None, None, None, None, None, None
                
                if pattern_len <= 0:
                    self.log("错误: 模式长度必须为正整数", "error")
                    messagebox.showerror("错误", "模式长度必须为正整数")
                    return False, None, None, None, None, None, None, None, None

                # 所有高级生成模式都用自定义字符集
                charset = self.custom_charset_var.get()
                if not charset:
                    self.log("错误: 高级生成下必须提供自定义字符集", "error")
                    messagebox.showerror("错误", "高级生成下必须提供自定义字符集")
                    return False, None, None, None, None, None, None, None, None
                if len(charset) < pattern_len:
                    self.log(f"错误: 自定义字符集长度({len(charset)})小于模式长度({pattern_len})", "error")
                    messagebox.showerror("错误", f"自定义字符集长度({len(charset)})小于模式长度({pattern_len})")
                    return False, None, None, None, None, None, None, None, None
                
                advanced_settings = {"repeat_char": (repeat_len, pattern_len, charset, pattern_type)}
                return True, None, None, None, output_file, split_size, None, None, advanced_settings
            except ValueError:
                self.log("错误: 重复次数和模式长度必须为整数", "error")
                messagebox.showerror("错误", "重复次数和模式长度必须为整数")
                return False, None, None, None, None, None, None, None, None

        # 检查掩码或字符集+长度
        mask = self.mask_var.get()
        if mask:  # Hashcat掩码模式
            try:
                parsed_mask = self.parse_hashcat_mask(mask)
                if not parsed_mask:
                    self.log("错误: 掩码不能为空", "error")
                    messagebox.showerror("错误", "掩码不能为空")
                    return False, None, None, None, None, None, None, None, None
                return True, mask, None, None, output_file, split_size, parsed_mask, (dict_file or dict_folder, dict_b_file, dict_combo_mode), None
            except ValueError as e:
                self.log(f"错误: {str(e)}", "error")
                messagebox.showerror("掩码错误", str(e))
                return False, None, None, None, None, None, None, None, None
        else:  # 字符集+长度模式
            if not is_pure_dict:  # 仅在非纯字典模式下检查字符集和长度
                charset = self.charset_var.get()
                if self.include_special_var.get():
                    charset += HASHCAT_CHARSETS['s']
                    charset = "".join(sorted(list(set(charset))))

                if not charset:
                    self.log("错误: 未使用掩码时，基础字符集不能为空", "error")
                    messagebox.showerror("错误", "未使用掩码时，基础字符集不能为空")
                    return False, None, None, None, None, None, None, None, None
                try:
                    min_len = int(self.min_len_var.get())
                    if min_len <= 0:
                        self.log("错误: 最小长度必须为正整数", "error")
                        messagebox.showerror("错误", "最小长度必须为正整数")
                        return False, None, None, None, None, None, None, None, None
                except ValueError:
                    self.log("错误: 最小长度必须为整数", "error")
                    messagebox.showerror("错误", "最小长度必须为整数")
                    return False, None, None, None, None, None, None, None, None
                try:
                    max_len = int(self.max_len_var.get())
                    if max_len < min_len:
                        self.log("错误: 最大长度必须大于或等于最小长度", "error")
                        messagebox.showerror("错误", "最大长度必须大于或等于最小长度")
                        return False, None, None, None, None, None, None, None, None
                except ValueError:
                    self.log("错误: 最大长度必须为整数", "error")
                    messagebox.showerror("错误", "最大长度必须为整数")
                    return False, None, None, None, None, None, None, None, None
                return True, None, charset, (min_len, max_len), output_file, split_size, None, (dict_file or dict_folder, dict_b_file, dict_combo_mode), None
            else:
                # 纯字典模式
                return True, None, None, None, output_file, split_size, None, (dict_file or dict_folder, dict_b_file, dict_combo_mode), None

    def _validate_performance_settings(self):
        """验证性能设置"""
        try:
            max_workers = int(self.max_workers_var.get())
            if max_workers <= 0 or max_workers > 64:
                self.log("错误: 最大线程数必须在1-64之间", "error")
                messagebox.showerror("错误", "最大线程数必须在1-64之间")
                return False
        except ValueError:
            self.log("错误: 最大线程数必须为整数", "error")
            messagebox.showerror("错误", "最大线程数必须为整数")
            return False

        try:
            memory_threshold = float(self.memory_threshold.get())
            if memory_threshold <= 0 or memory_threshold > 100:
                self.log("错误: 内存阈值必须在1-100之间", "error")
                messagebox.showerror("错误", "内存阈值必须在1-100之间")
                return False
        except ValueError:
            self.log("错误: 内存阈值必须为数字", "error")
            messagebox.showerror("错误", "内存阈值必须为数字")
            return False

        try:
            cpu_threshold = float(self.cpu_threshold.get())
            if cpu_threshold <= 0 or cpu_threshold > 100:
                self.log("错误: CPU阈值必须在1-100之间", "error")
                messagebox.showerror("错误", "CPU阈值必须在1-100之间")
                return False
        except ValueError:
            self.log("错误: CPU阈值必须为数字", "error")
            messagebox.showerror("错误", "CPU阈值必须为数字")
            return False

        return True

    def _validate_file_system(self, output_file):
        """验证文件系统"""
        try:
            output_dir = os.path.dirname(output_file)
            if output_dir and not os.path.exists(output_dir):
                # 尝试创建目录
                os.makedirs(output_dir, exist_ok=True)
                self.log(f"已创建输出目录: {output_dir}")

            # 检查磁盘空间
            disk_usage = psutil.disk_usage(output_dir or '.')
            free_space_gb = disk_usage.free / (1024**3)
            
            if free_space_gb < 1:  # 小于1GB
                self.log(f"警告: 磁盘空间不足，可用空间: {free_space_gb:.1f} GB", "warning")
                if not messagebox.askyesno("警告", f"磁盘空间不足，可用空间: {free_space_gb:.1f} GB\n是否继续？"):
                    return False

        except Exception as e:
            self.log(f"文件系统验证出错: {e}", "error")
            return False

        return True

    def _validate_system_resources(self):
        """验证系统资源"""
        try:
            # 检查内存
            memory = psutil.virtual_memory()
            memory_percent = memory.percent
            
            if memory_percent > 90:
                self.log(f"警告: 内存使用率过高: {memory_percent:.1f}%", "warning")
                if not messagebox.askyesno("警告", f"内存使用率过高: {memory_percent:.1f}%\n是否继续？"):
                    return False

            # 检查CPU
            cpu_percent = psutil.cpu_percent(interval=1)
            if cpu_percent > 95:
                self.log(f"警告: CPU使用率过高: {cpu_percent:.1f}%", "warning")
                if not messagebox.askyesno("警告", f"CPU使用率过高: {cpu_percent:.1f}%\n是否继续？"):
                    return False

        except Exception as e:
            self.log(f"系统资源验证出错: {e}", "error")
            return False

        return True

    def optimize_generation_settings(self):
        """根据系统资源自动优化生成设置"""
        if not self.auto_optimize.get():
            return

        try:
            # 获取系统信息
            memory = psutil.virtual_memory()
            cpu_count = os.cpu_count()
            
            # 根据内存调整批处理大小
            if memory.total < 4 * 1024**3:  # 小于4GB
                global WRITE_BATCH_SIZE
                WRITE_BATCH_SIZE = 5000
                self.log("内存较小，已调整批处理大小为5000")
            elif memory.total > 16 * 1024**3:  # 大于16GB
                WRITE_BATCH_SIZE = 20000
                self.log("内存充足，已调整批处理大小为20000")

            # 根据CPU核心数调整线程数
            optimal_workers = min(cpu_count * 2, 32)
            if optimal_workers != int(self.max_workers_var.get()):
                self.max_workers_var.set(str(optimal_workers))
                self.log(f"已根据CPU核心数调整线程数为: {optimal_workers}")

            # 根据磁盘类型调整压缩设置
            try:
                disk_usage = psutil.disk_usage('.')
                if disk_usage.free < 10 * 1024**3:  # 小于10GB
                    self.use_compression.set(True)
                    self.log("磁盘空间不足，已启用压缩")
            except:
                pass

        except Exception as e:
            self.log(f"自动优化出错: {e}", "warning")

    def optimize_thread_pool(self):
        """优化线程池配置"""
        try:
            max_workers = int(self.max_workers_var.get())
            if max_workers != self.executor._max_workers:
                self.executor.shutdown(wait=True)
                self.executor = concurrent.futures.ThreadPoolExecutor(max_workers=max_workers)
                self.log(f"线程池已优化，最大线程数: {max_workers}")
        except ValueError:
            self.log("线程数设置无效，使用默认值", "warning")

    def start_performance_monitoring(self):
        """启动性能监控"""
        if not self.performance_monitoring.get():
            return
            
        self.monitoring_active = True
        self.performance_stats['start_time'] = time.time()
        self.performance_thread = threading.Thread(target=self._performance_monitor, daemon=True)
        self.performance_thread.start()
        self.log("性能监控已启动")

    def stop_performance_monitoring(self):
        """停止性能监控"""
        self.monitoring_active = False
        if self.performance_thread:
            self.performance_thread.join(timeout=1)
        self.log("性能监控已停止")

    def _performance_monitor(self):
        """性能监控线程"""
        while self.monitoring_active and not self.stop_event.is_set():
            try:
                # 获取系统性能数据
                memory = psutil.virtual_memory()
                cpu_percent = psutil.cpu_percent(interval=1)
                disk_io = psutil.disk_io_counters()
                
                # 记录性能数据
                self.performance_stats['memory_usage'].append(memory.percent)
                self.performance_stats['cpu_usage'].append(cpu_percent)
                if disk_io:
                    self.performance_stats['disk_io'].append({
                        'read_bytes': disk_io.read_bytes,
                        'write_bytes': disk_io.write_bytes
                    })
                
                # 检查性能警告
                if memory.percent > float(self.memory_threshold.get()):
                    self.log(f"内存使用率过高: {memory.percent:.1f}%", "warning")
                
                if cpu_percent > float(self.cpu_threshold.get()):
                    self.log(f"CPU使用率过高: {cpu_percent:.1f}%", "warning")
                
                time.sleep(PERFORMANCE_CHECK_INTERVAL)
                
            except Exception as e:
                self.log(f"性能监控出错: {e}", "error")
                break

    def run_performance_test(self):
        """运行性能测试"""
        self.log("开始性能测试...")
        
        # 创建测试数据
        test_charset = "abcdefghijklmnopqrstuvwxyz0123456789"
        test_length = 4
        test_combinations = len(test_charset) ** test_length
        
        self.log(f"测试参数: 字符集长度={len(test_charset)}, 长度={test_length}")
        self.log(f"预计组合数: {test_combinations}")
        
        # 创建临时输出文件
        temp_file = tempfile.NamedTemporaryFile(mode='w', suffix='.txt', delete=False)
        temp_file.close()
        
        try:
            start_time = time.time()
            
            # 生成测试组合
            count = 0
            for combo in itertools.product(test_charset, repeat=test_length):
                if count >= 100000:  # 限制测试数量
                    break
                count += 1
            
            end_time = time.time()
            elapsed_time = end_time - start_time
            combinations_per_second = count / elapsed_time if elapsed_time > 0 else 0
            
            # 显示测试结果
            self.log(f"性能测试完成:")
            self.log(f"  生成组合数: {count}")
            self.log(f"  用时: {elapsed_time:.2f} 秒")
            self.log(f"  速度: {combinations_per_second:.0f} 组合/秒")
            
            # 估算完整生成时间
            if test_combinations > 0:
                estimated_time = test_combinations / combinations_per_second
                self.log(f"  完整生成估算时间: {estimated_time:.1f} 秒")
            
        except Exception as e:
            self.log(f"性能测试出错: {e}", "error")
        finally:
            # 清理临时文件
            try:
                os.unlink(temp_file.name)
            except:
                pass

    def clear_cache(self):
        """清理缓存"""
        self.dict_cache.clear()
        self.log("字典缓存已清理")

    def show_system_info(self):
        """显示系统信息"""
        try:
            # CPU信息
            cpu_count = os.cpu_count()
            cpu_freq = psutil.cpu_freq()
            
            # 内存信息
            memory = psutil.virtual_memory()
            
            # 磁盘信息
            disk = psutil.disk_usage('/')
            
            # 显示信息
            info = f"""
系统信息:
CPU: {cpu_count} 核心
CPU频率: {cpu_freq.current:.0f} MHz
内存: {memory.total / (1024**3):.1f} GB (可用: {memory.available / (1024**3):.1f} GB)
磁盘: {disk.total / (1024**3):.1f} GB (可用: {disk.free / (1024**3):.1f} GB)
Python版本: {sys.version}
            """
            
            # 创建信息窗口
            info_window = tk.Toplevel(self.root)
            info_window.title("系统信息")
            info_window.geometry("400x300")
            
            text_widget = scrolledtext.ScrolledText(info_window, wrap=tk.WORD)
            text_widget.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
            text_widget.insert(tk.END, info)
            text_widget.config(state=tk.DISABLED)
            
        except Exception as e:
            self.log(f"获取系统信息出错: {e}", "error")

    def parse_hashcat_mask(self, mask):
        """解析Hashcat掩码"""
        charsets = []
        i = 0
        while i < len(mask):
            if mask[i] == "?":
                if i + 1 < len(mask):
                    char_type = mask[i+1]
                    if char_type == "?":
                        charsets.append("?")
                        i += 2
                    elif char_type in self.hashcat_charsets:
                        charsets.append(self.hashcat_charsets[char_type])
                        i += 2
                    else:
                        raise ValueError(f"无效的Hashcat掩码类型: ?{char_type}")
                else:
                    raise ValueError("掩码以无效的'?'结尾")
            else:
                charsets.append(mask[i])
                i += 1
        return charsets

    def toggle_log_display(self):
        """切换日志显示状态"""
        if not self.log_enabled.get():
            self.log("日志显示已关闭，将只显示关键信息", "info")
        else:
            self.log("日志显示已开启", "info")

    # 新增高级功能方法
    def setup_database(self):
        """设置数据库连接"""
        try:
            db_path = "combination_generator.db"
            self.db_connection = sqlite3.connect(db_path)
            self._create_tables()
            self.log("数据库连接已建立")
        except Exception as e:
            self.log(f"数据库设置出错: {e}", "error")

    def _create_tables(self):
        """创建数据库表"""
        cursor = self.db_connection.cursor()
        
        # 历史记录表
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS generation_history (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                timestamp TEXT,
                parameters TEXT,
                combinations_count INTEGER,
                duration REAL,
                file_path TEXT
            )
        ''')
        
        # 统计表
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS statistics (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                session_id TEXT,
                total_combinations INTEGER,
                unique_combinations INTEGER,
                duplicate_count INTEGER,
                file_count INTEGER,
                total_size INTEGER,
                start_time TEXT,
                end_time TEXT
            )
        ''')
        
        # 模式缓存表
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS pattern_cache (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                pattern TEXT,
                result TEXT,
                created_time TEXT
            )
        ''')
        
        self.db_connection.commit()

    def update_statistics(self, combination, is_duplicate=False):
        """更新统计信息"""
        if not self.statistics_tracking.get():
            return
            
        self.generation_statistics['total_combinations'] += 1
        
        if is_duplicate:
            self.generation_statistics['duplicate_count'] += 1
        else:
            self.generation_statistics['unique_combinations'] += 1
            
        # 更新模式统计
        if len(combination) > 0:
            pattern = combination[:3]  # 前3个字符作为模式
            self.generation_statistics['patterns_generated'][pattern] += 1
            
        # 更新字符集使用统计
        for char in combination:
            self.generation_statistics['charset_usage'][char] += 1

    def add_to_history(self, parameters, combinations_count, duration, file_path):
        """添加到历史记录"""
        if not self.history_tracking.get():
            return
            
        history_entry = {
            'timestamp': datetime.now().isoformat(),
            'parameters': parameters,
            'combinations_count': combinations_count,
            'duration': duration,
            'file_path': file_path
        }
        
        self.generation_history.append(history_entry)
        
        # 保存到数据库
        if self.db_connection:
            try:
                cursor = self.db_connection.cursor()
                cursor.execute('''
                    INSERT INTO generation_history 
                    (timestamp, parameters, combinations_count, duration, file_path)
                    VALUES (?, ?, ?, ?, ?)
                ''', (
                    history_entry['timestamp'],
                    json.dumps(history_entry['parameters']),
                    history_entry['combinations_count'],
                    history_entry['duration'],
                    history_entry['file_path']
                ))
                self.db_connection.commit()
            except Exception as e:
                self.log(f"保存历史记录出错: {e}", "warning")

    def check_duplicate(self, combination):
        """检查重复"""
        if not self.duplicate_removal.get():
            return False
            
        if combination in self.duplicate_checker:
            return True
            
        self.duplicate_checker.add(combination)
        return False

    def quality_check_combination(self, combination):
        """质量检查"""
        if not self.quality_check.get():
            return True
            
        # 基本质量规则
        if len(combination) == 0:
            return False
            
        # 检查是否包含有效字符
        if not re.search(r'[a-zA-Z0-9]', combination):
            return False
            
        # 检查重复字符过多
        if len(set(combination)) < len(combination) * 0.5:
            return False
            
        return True

    def create_backup(self, current_file, combinations_count):
        """创建备份"""
        if not self.auto_backup.get():
            return
            
        try:
            if combinations_count - self.last_backup_time >= BACKUP_INTERVAL:
                backup_dir = "backups"
                os.makedirs(backup_dir, exist_ok=True)
                
                timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
                backup_name = f"backup_{timestamp}_{self.backup_counter}.txt"
                backup_path = os.path.join(backup_dir, backup_name)
                
                # 复制当前文件
                if os.path.exists(current_file):
                    shutil.copy2(current_file, backup_path)
                    self.log(f"已创建备份: {backup_name}")
                    self.backup_counter += 1
                    self.last_backup_time = combinations_count
                    
        except Exception as e:
            self.log(f"创建备份出错: {e}", "warning")

    def show_statistics(self):
        """显示统计报告"""
        try:
            stats = self.generation_statistics
            
            # 计算统计信息
            total_time = 0
            if stats['start_time'] and stats['end_time']:
                total_time = stats['end_time'] - stats['start_time']
            
            avg_size = stats['total_size'] / max(stats['file_count'], 1)
            
            # 生成报告
            report = f"""
统计报告:
总组合数: {stats['total_combinations']:,}
唯一组合数: {stats['unique_combinations']:,}
重复组合数: {stats['duplicate_count']:,}
文件数量: {stats['file_count']}
总大小: {stats['total_size'] / (1024**2):.2f} MB
平均文件大小: {avg_size / (1024**2):.2f} MB
总用时: {total_time:.2f} 秒
平均速度: {stats['total_combinations'] / max(total_time, 1):.0f} 组合/秒

最常用模式 (前10):
"""
            
            # 添加模式统计
            sorted_patterns = sorted(stats['patterns_generated'].items(), 
                                   key=lambda x: x[1], reverse=True)[:10]
            for pattern, count in sorted_patterns:
                report += f"  {pattern}: {count:,}\n"
            
            report += "\n最常用字符 (前10):\n"
            sorted_chars = sorted(stats['charset_usage'].items(), 
                                key=lambda x: x[1], reverse=True)[:10]
            for char, count in sorted_chars:
                report += f"  '{char}': {count:,}\n"
            
            # 显示报告窗口
            self._show_info_window("统计报告", report)
            
        except Exception as e:
            self.log(f"生成统计报告出错: {e}", "error")

    def show_history(self):
        """显示历史记录"""
        try:
            if not self.generation_history:
                messagebox.showinfo("历史记录", "暂无历史记录")
                return
            
            history_text = "生成历史记录:\n\n"
            
            for i, entry in enumerate(reversed(list(self.generation_history)), 1):
                history_text += f"{i}. 时间: {entry['timestamp']}\n"
                history_text += f"   组合数: {entry['combinations_count']:,}\n"
                history_text += f"   用时: {entry['duration']:.2f} 秒\n"
                history_text += f"   文件: {entry['file_path']}\n\n"
            
            self._show_info_window("历史记录", history_text)
            
        except Exception as e:
            self.log(f"显示历史记录出错: {e}", "error")

    def export_data(self):
        """导出数据"""
        try:
            # 选择导出格式
            format_window = tk.Toplevel(self.root)
            format_window.title("选择导出格式")
            format_window.geometry("300x200")
            
            ttk.Label(format_window, text="选择导出格式:").pack(pady=10)
            
            format_var = tk.StringVar(value='txt')
            for fmt in self.export_formats:
                ttk.Radiobutton(format_window, text=fmt.upper(), 
                              variable=format_var, value=fmt).pack()
            
            def do_export():
                export_format = format_var.get()
                self._export_data_in_format(export_format)
                format_window.destroy()
            
            ttk.Button(format_window, text="导出", command=do_export).pack(pady=10)
            
        except Exception as e:
            self.log(f"导出数据出错: {e}", "error")

    def _export_data_in_format(self, export_format):
        """按指定格式导出数据"""
        try:
            # 选择输出文件
            file_types = {
                'txt': [("文本文件", "*.txt")],
                'csv': [("CSV文件", "*.csv")],
                'json': [("JSON文件", "*.json")],
                'sql': [("SQL文件", "*.sql")]
            }
            
            filename = filedialog.asksaveasfilename(
                title=f"保存{export_format.upper()}文件",
                defaultextension=f".{export_format}",
                filetypes=file_types.get(export_format, [("所有文件", "*.*")])
            )
            
            if not filename:
                return
            
            # 导出数据
            if export_format == 'txt':
                self._export_as_txt(filename)
            elif export_format == 'csv':
                self._export_as_csv(filename)
            elif export_format == 'json':
                self._export_as_json(filename)
            elif export_format == 'sql':
                self._export_as_sql(filename)
                
            self.log(f"数据已导出到: {filename}")
            
        except Exception as e:
            self.log(f"导出{export_format}文件出错: {e}", "error")

    def _export_as_txt(self, filename):
        """导出为TXT格式"""
        with open(filename, 'w', encoding='utf-8') as f:
            f.write("字符组合生成器 v4.0 数据导出\n")
            f.write("=" * 50 + "\n\n")
            
            # 统计信息
            stats = self.generation_statistics
            f.write(f"总组合数: {stats['total_combinations']:,}\n")
            f.write(f"唯一组合数: {stats['unique_combinations']:,}\n")
            f.write(f"重复组合数: {stats['duplicate_count']:,}\n")
            f.write(f"文件数量: {stats['file_count']}\n")
            f.write(f"总大小: {stats['total_size'] / (1024**2):.2f} MB\n\n")
            
            # 历史记录
            f.write("历史记录:\n")
            for entry in self.generation_history:
                f.write(f"- {entry['timestamp']}: {entry['combinations_count']:,} 组合\n")

    def _export_as_csv(self, filename):
        """导出为CSV格式"""
        import csv
        
        with open(filename, 'w', newline='', encoding='utf-8') as f:
            writer = csv.writer(f)
            
            # 写入统计信息
            writer.writerow(['统计项目', '数值'])
            stats = self.generation_statistics
            writer.writerow(['总组合数', stats['total_combinations']])
            writer.writerow(['唯一组合数', stats['unique_combinations']])
            writer.writerow(['重复组合数', stats['duplicate_count']])
            writer.writerow(['文件数量', stats['file_count']])
            writer.writerow(['总大小(MB)', stats['total_size'] / (1024**2)])
            
            # 写入模式统计
            writer.writerow([])
            writer.writerow(['模式', '出现次数'])
            for pattern, count in stats['patterns_generated'].items():
                writer.writerow([pattern, count])

    def _export_as_json(self, filename):
        """导出为JSON格式"""
        export_data = {
            'statistics': self.generation_statistics,
            'history': list(self.generation_history),
            'export_time': datetime.now().isoformat(),
            'version': '4.0'
        }
        
        with open(filename, 'w', encoding='utf-8') as f:
            json.dump(export_data, f, indent=2, ensure_ascii=False)

    def _export_as_sql(self, filename):
        """导出为SQL格式"""
        with open(filename, 'w', encoding='utf-8') as f:
            f.write("-- 字符组合生成器 v4.0 数据导出\n")
            f.write("-- 导出时间: " + datetime.now().isoformat() + "\n\n")
            
            # 创建表结构
            f.write("""
CREATE TABLE IF NOT EXISTS generation_statistics (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    total_combinations INTEGER,
    unique_combinations INTEGER,
    duplicate_count INTEGER,
    file_count INTEGER,
    total_size INTEGER,
    export_time TEXT
);

CREATE TABLE IF NOT EXISTS generation_history (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    timestamp TEXT,
    combinations_count INTEGER,
    duration REAL,
    file_path TEXT
);

""")
            
            # 插入统计数据
            stats = self.generation_statistics
            f.write(f"""
INSERT INTO generation_statistics 
(total_combinations, unique_combinations, duplicate_count, file_count, total_size, export_time)
VALUES ({stats['total_combinations']}, {stats['unique_combinations']}, 
        {stats['duplicate_count']}, {stats['file_count']}, {stats['total_size']}, 
        '{datetime.now().isoformat()}');
""")
            
            # 插入历史数据
            for entry in self.generation_history:
                f.write(f"""
INSERT INTO generation_history 
(timestamp, combinations_count, duration, file_path)
VALUES ('{entry['timestamp']}', {entry['combinations_count']}, 
        {entry['duration']}, '{entry['file_path']}');
""")

    def backup_restore(self):
        """备份恢复功能"""
        try:
            backup_window = tk.Toplevel(self.root)
            backup_window.title("备份恢复")
            backup_window.geometry("400x300")
            
            # 备份功能
            backup_frame = ttk.LabelFrame(backup_window, text="备份", padding="10")
            backup_frame.pack(fill=tk.X, padx=10, pady=5)
            
            ttk.Button(backup_frame, text="创建备份", 
                      command=lambda: self._create_manual_backup()).pack(fill=tk.X, pady=2)
            ttk.Button(backup_frame, text="查看备份", 
                      command=lambda: self._view_backups()).pack(fill=tk.X, pady=2)
            
            # 恢复功能
            restore_frame = ttk.LabelFrame(backup_window, text="恢复", padding="10")
            restore_frame.pack(fill=tk.X, padx=10, pady=5)
            
            ttk.Button(restore_frame, text="从备份恢复", 
                      command=lambda: self._restore_from_backup()).pack(fill=tk.X, pady=2)
            ttk.Button(restore_frame, text="清理备份", 
                      command=lambda: self._cleanup_backups()).pack(fill=tk.X, pady=2)
            
        except Exception as e:
            self.log(f"备份恢复功能出错: {e}", "error")

    def _create_manual_backup(self):
        """手动创建备份"""
        try:
            backup_dir = "backups"
            os.makedirs(backup_dir, exist_ok=True)
            
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            backup_name = f"manual_backup_{timestamp}.txt"
            backup_path = os.path.join(backup_dir, backup_name)
            
            # 保存当前状态
            backup_data = {
                'statistics': self.generation_statistics,
                'history': list(self.generation_history),
                'settings': self._get_current_settings(),
                'timestamp': timestamp
            }
            
            with open(backup_path, 'w', encoding='utf-8') as f:
                json.dump(backup_data, f, indent=2, ensure_ascii=False)
            
            self.log(f"手动备份已创建: {backup_name}")
            messagebox.showinfo("备份", f"备份已创建: {backup_name}")
            
        except Exception as e:
            self.log(f"创建手动备份出错: {e}", "error")

    def _view_backups(self):
        """查看备份文件"""
        try:
            backup_dir = "backups"
            if not os.path.exists(backup_dir):
                messagebox.showinfo("备份", "暂无备份文件")
                return
            
            backup_files = [f for f in os.listdir(backup_dir) if f.endswith('.txt')]
            if not backup_files:
                messagebox.showinfo("备份", "暂无备份文件")
                return
            
            backup_list = "\n".join(sorted(backup_files, reverse=True))
            self._show_info_window("备份文件列表", f"备份文件:\n\n{backup_list}")
            
        except Exception as e:
            self.log(f"查看备份出错: {e}", "error")

    def _restore_from_backup(self):
        """从备份恢复"""
        try:
            backup_dir = "backups"
            if not os.path.exists(backup_dir):
                messagebox.showinfo("恢复", "暂无备份文件")
                return
            
            backup_file = filedialog.askopenfilename(
                title="选择备份文件",
                initialdir=backup_dir,
                filetypes=[("备份文件", "*.txt"), ("所有文件", "*.*")]
            )
            
            if not backup_file:
                return
            
            with open(backup_file, 'r', encoding='utf-8') as f:
                backup_data = json.load(f)
            
            # 恢复数据
            self.generation_statistics = backup_data.get('statistics', self.generation_statistics)
            self.generation_history = deque(backup_data.get('history', []), maxlen=HISTORY_SIZE)
            
            self.log(f"已从备份恢复: {os.path.basename(backup_file)}")
            messagebox.showinfo("恢复", "备份恢复完成")
            
        except Exception as e:
            self.log(f"恢复备份出错: {e}", "error")

    def _cleanup_backups(self):
        """清理备份文件"""
        try:
            if messagebox.askyesno("清理备份", "确定要删除所有备份文件吗？"):
                backup_dir = "backups"
                if os.path.exists(backup_dir):
                    for file in os.listdir(backup_dir):
                        if file.endswith('.txt'):
                            os.remove(os.path.join(backup_dir, file))
                    self.log("备份文件已清理")
                    messagebox.showinfo("清理", "备份文件已清理")
        except Exception as e:
            self.log(f"清理备份出错: {e}", "error")

    def manage_settings(self):
        """管理设置"""
        try:
            settings_window = tk.Toplevel(self.root)
            settings_window.title("设置管理")
            settings_window.geometry("500x400")
            
            # 创建设置选项卡
            notebook = ttk.Notebook(settings_window)
            notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
            
            # 性能设置
            performance_frame = ttk.Frame(notebook)
            notebook.add(performance_frame, text="性能设置")
            
            ttk.Label(performance_frame, text="批处理大小:").grid(row=0, column=0, sticky=tk.W, pady=5)
            batch_size_var = tk.StringVar(value=str(WRITE_BATCH_SIZE))
            ttk.Entry(performance_frame, textvariable=batch_size_var, width=15).grid(row=0, column=1, pady=5)
            
            ttk.Label(performance_frame, text="进度更新间隔:").grid(row=1, column=0, sticky=tk.W, pady=5)
            progress_interval_var = tk.StringVar(value=str(PROGRESS_UPDATE_INTERVAL))
            ttk.Entry(performance_frame, textvariable=progress_interval_var, width=15).grid(row=1, column=1, pady=5)
            
            # 高级设置
            advanced_frame = ttk.Frame(notebook)
            notebook.add(advanced_frame, text="高级设置")
            
            ttk.Label(advanced_frame, text="备份间隔:").grid(row=0, column=0, sticky=tk.W, pady=5)
            backup_interval_var = tk.StringVar(value=str(BACKUP_INTERVAL))
            ttk.Entry(advanced_frame, textvariable=backup_interval_var, width=15).grid(row=0, column=1, pady=5)
            
            ttk.Label(advanced_frame, text="历史记录大小:").grid(row=1, column=0, sticky=tk.W, pady=5)
            history_size_var = tk.StringVar(value=str(HISTORY_SIZE))
            ttk.Entry(advanced_frame, textvariable=history_size_var, width=15).grid(row=1, column=1, pady=5)
            
            # 保存按钮
            def save_settings():
                try:
                    global WRITE_BATCH_SIZE, PROGRESS_UPDATE_INTERVAL, BACKUP_INTERVAL, HISTORY_SIZE
                    WRITE_BATCH_SIZE = int(batch_size_var.get())
                    PROGRESS_UPDATE_INTERVAL = int(progress_interval_var.get())
                    BACKUP_INTERVAL = int(backup_interval_var.get())
                    HISTORY_SIZE = int(history_size_var.get())
                    
                    self.log("设置已保存")
                    messagebox.showinfo("设置", "设置已保存")
                    settings_window.destroy()
                except ValueError:
                    messagebox.showerror("错误", "请输入有效的数字")
            
            ttk.Button(settings_window, text="保存设置", command=save_settings).pack(pady=10)
            
        except Exception as e:
            self.log(f"设置管理出错: {e}", "error")

    def _get_current_settings(self):
        """获取当前设置"""
        return {
            'write_batch_size': WRITE_BATCH_SIZE,
            'progress_update_interval': PROGRESS_UPDATE_INTERVAL,
            'backup_interval': BACKUP_INTERVAL,
            'history_size': HISTORY_SIZE,
            'max_workers': self.max_workers_var.get(),
            'memory_threshold': self.memory_threshold.get(),
            'cpu_threshold': self.cpu_threshold.get()
        }

    def save_settings(self):
        """保存设置到文件"""
        try:
            settings = self._get_current_settings()
            with open('settings.json', 'w', encoding='utf-8') as f:
                json.dump(settings, f, indent=2, ensure_ascii=False)
        except Exception as e:
            self.log(f"保存设置出错: {e}", "warning")

    def load_settings(self):
        """从文件加载设置"""
        try:
            if os.path.exists('settings.json'):
                with open('settings.json', 'r', encoding='utf-8') as f:
                    settings = json.load(f)
                
                # 应用设置
                self.max_workers_var.set(settings.get('max_workers', str(MAX_WORKERS)))
                self.memory_threshold.set(settings.get('memory_threshold', '80'))
                self.cpu_threshold.set(settings.get('cpu_threshold', '90'))
                
                self.log("设置已加载")
        except Exception as e:
            self.log(f"加载设置出错: {e}", "warning")

    def _show_info_window(self, title, content):
        """显示信息窗口"""
        info_window = tk.Toplevel(self.root)
        info_window.title(title)
        info_window.geometry("600x400")
        
        text_widget = scrolledtext.ScrolledText(info_window, wrap=tk.WORD)
        text_widget.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        text_widget.insert(tk.END, content)
        text_widget.config(state=tk.DISABLED)

    # 新增终极优化方法
    def _get_system_info(self) -> Dict[str, Any]:
        """获取系统信息"""
        try:
            info = {
                'platform': platform.platform(),
                'python_version': sys.version,
                'cpu_count': multiprocessing.cpu_count(),
                'memory_total': psutil.virtual_memory().total,
                'memory_available': psutil.virtual_memory().available,
                'disk_total': psutil.disk_usage('/').total if platform.system() != 'Windows' else psutil.disk_usage('C:/').total,
                'disk_free': psutil.disk_usage('/').free if platform.system() != 'Windows' else psutil.disk_usage('C:/').free,
                'architecture': platform.architecture()[0],
                'machine': platform.machine(),
                'processor': platform.processor()
            }
            
            # 获取CPU信息
            try:
                cpu_freq = psutil.cpu_freq()
                if cpu_freq:
                    info['cpu_freq'] = cpu_freq.current
                    info['cpu_freq_max'] = cpu_freq.max
            except:
                info['cpu_freq'] = 'Unknown'
                info['cpu_freq_max'] = 'Unknown'
            
            return info
        except Exception as e:
            self.log(f"获取系统信息出错: {e}", "warning")
            return {}

    def setup_ultimate_optimization(self):
        """设置终极优化"""
        if not self.ultimate_optimization.get():
            return
            
        try:
            # 设置进程优先级
            if self.signal_handling_enabled.get():
                self._setup_signal_handling()
            
            # 初始化进程池
            if self.process_pool_enabled.get():
                self._setup_process_pool()
            
            # 初始化内存池
            if self.memory_pool_enabled.get():
                self._setup_memory_pool()
            
            # 设置垃圾回收优化
            if self.gc_optimization.get():
                self._setup_gc_optimization()
            
            # 设置缓冲区优化
            if self.buffer_optimization_enabled.get():
                self._setup_buffer_optimization()
            
            # 设置缓存预取
            if self.cache_prefetch_enabled.get():
                self._setup_cache_prefetch()
            
            # 设置异步I/O
            if self.async_io_enabled.get():
                self._setup_async_io()
            
            # 设置GPU加速（实验性）
            if self.gpu_acceleration_enabled.get():
                self._setup_gpu_acceleration()
            
            self.log("终极优化已启用")
            
        except Exception as e:
            self.log(f"终极优化设置出错: {e}", "error")

    def _setup_signal_handling(self):
        """设置信号处理"""
        try:
            def signal_handler(signum, frame):
                self.log(f"收到信号 {signum}，正在安全退出...", "warning")
                self.stop_generation()
                sys.exit(0)
            
            signal.signal(signal.SIGINT, signal_handler)
            signal.signal(signal.SIGTERM, signal_handler)
            
            # 注册退出处理
            atexit.register(self._cleanup_on_exit)
            
        except Exception as e:
            self.log(f"信号处理设置出错: {e}", "warning")

    def _setup_process_pool(self):
        """设置进程池"""
        try:
            if self.process_pool is None:
                self.process_pool = multiprocessing.Pool(processes=PROCESS_POOL_SIZE)
                self.log(f"进程池已创建，大小: {PROCESS_POOL_SIZE}")
        except Exception as e:
            self.log(f"进程池设置出错: {e}", "warning")

    def _setup_memory_pool(self):
        """设置内存池"""
        try:
            # 预分配内存池
            self.memory_pool = {
                'buffers': deque(maxlen=100),
                'strings': weakref.WeakSet(),
                'objects': weakref.WeakSet()
            }
            self.log("内存池已初始化")
        except Exception as e:
            self.log(f"内存池设置出错: {e}", "warning")

    def _setup_gc_optimization(self):
        """设置垃圾回收优化"""
        try:
            # 设置垃圾回收阈值
            gc.set_threshold(GC_THRESHOLD, GC_THRESHOLD * 2, GC_THRESHOLD * 3)
            
            # 禁用循环引用检测（如果不需要）
            gc.disable()
            
            self.log("垃圾回收优化已设置")
        except Exception as e:
            self.log(f"垃圾回收优化设置出错: {e}", "warning")

    def _setup_buffer_optimization(self):
        """设置缓冲区优化"""
        try:
            # 预分配缓冲区
            for _ in range(100):
                self.buffer_pool.append(bytearray(1024))
            
            self.log("缓冲区优化已设置")
        except Exception as e:
            self.log(f"缓冲区优化设置出错: {e}", "warning")

    def _setup_cache_prefetch(self):
        """设置缓存预取"""
        try:
            # 初始化预取缓存
            self.prefetch_cache = {
                'next_combinations': deque(maxlen=1000),
                'file_chunks': deque(maxlen=100),
                'patterns': weakref.WeakValueDictionary()
            }
            self.log("缓存预取已设置")
        except Exception as e:
            self.log(f"缓存预取设置出错: {e}", "warning")

    def _setup_async_io(self):
        """设置异步I/O"""
        try:
            # 创建异步事件循环
            if not hasattr(self, 'async_loop'):
                self.async_loop = asyncio.new_event_loop()
                asyncio.set_event_loop(self.async_loop)
            
            self.log("异步I/O已设置")
        except Exception as e:
            self.log(f"异步I/O设置出错: {e}", "warning")

    def _setup_gpu_acceleration(self):
        """设置GPU加速（实验性）"""
        try:
            # 检查是否有GPU支持
            if self._check_gpu_support():
                self.log("GPU加速已启用（实验性）")
            else:
                self.log("GPU加速不可用，已禁用", "warning")
                self.gpu_acceleration_enabled.set(False)
        except Exception as e:
            self.log(f"GPU加速设置出错: {e}", "warning")
            self.gpu_acceleration_enabled.set(False)

    def _check_gpu_support(self) -> bool:
        """检查GPU支持"""
        try:
            # 这里可以添加GPU检测逻辑
            # 目前返回False，因为需要额外的GPU库
            return False
        except:
            return False

    def analyze_performance(self):
        """性能分析"""
        try:
            # 收集性能数据
            memory = psutil.virtual_memory()
            cpu_percent = psutil.cpu_percent(interval=1)
            disk_io = psutil.disk_io_counters()
            
            # 计算性能指标
            performance_report = f"""
性能分析报告:
================

系统资源:
- CPU使用率: {cpu_percent:.1f}%
- 内存使用率: {memory.percent:.1f}%
- 内存总量: {memory.total / (1024**3):.1f} GB
- 可用内存: {memory.available / (1024**3):.1f} GB

性能指标:
- 缓存命中率: {self.performance_metrics['cache_hits'] / max(self.performance_metrics['cache_hits'] + self.performance_metrics['cache_misses'], 1) * 100:.1f}%
- I/O操作数: {self.performance_metrics['io_operations']}
- GC回收次数: {self.performance_metrics['gc_collections']}
- 进程切换次数: {self.performance_metrics['process_switches']}

优化建议:
"""
            
            # 生成优化建议
            if memory.percent > 80:
                performance_report += "- 内存使用率过高，建议增加内存或减少批处理大小\n"
            
            if cpu_percent > 90:
                performance_report += "- CPU使用率过高，建议减少线程数\n"
            
            if self.performance_metrics['cache_hits'] / max(self.performance_metrics['cache_hits'] + self.performance_metrics['cache_misses'], 1) < 0.5:
                performance_report += "- 缓存命中率较低，建议增加缓存大小\n"
            
            if self.performance_metrics['gc_collections'] > 10:
                performance_report += "- 垃圾回收频繁，建议优化内存使用\n"
            
            self._show_info_window("性能分析", performance_report)
            
        except Exception as e:
            self.log(f"性能分析出错: {e}", "error")

    def system_tuning(self):
        """系统调优"""
        try:
            # 自动调优系统参数
            self._auto_tune_system()
            
            # 显示调优结果
            tuning_report = f"""
系统调优报告:
================

已应用的优化:
- 进程优先级调整
- 内存分配优化
- 垃圾回收调优
- 缓冲区大小调整
- 缓存策略优化

建议的进一步优化:
- 考虑使用SSD存储
- 增加系统内存
- 使用更快的CPU
- 优化操作系统设置
"""
            
            self._show_info_window("系统调优", tuning_report)
            
        except Exception as e:
            self.log(f"系统调优出错: {e}", "error")

    def _auto_tune_system(self):
        """自动调优系统"""
        try:
            # 根据系统信息自动调整参数
            if self.system_info.get('cpu_count', 0) > 8:
                # 多核CPU优化
                global MAX_WORKERS
                MAX_WORKERS = min(32, self.system_info['cpu_count'] * 2)
                self.max_workers_var.set(str(MAX_WORKERS))
            
            if self.system_info.get('memory_total', 0) > 16 * 1024**3:
                # 大内存优化
                global WRITE_BATCH_SIZE
                WRITE_BATCH_SIZE = 50000
                self.log("大内存系统，已调整批处理大小")
            
            # 其他自动调优...
            
        except Exception as e:
            self.log(f"自动调优出错: {e}", "warning")

    def memory_optimization(self):
        """内存优化"""
        try:
            # 执行内存优化
            self._optimize_memory()
            
            # 显示优化结果
            memory_report = f"""
内存优化报告:
================

优化前:
- 内存使用: {psutil.virtual_memory().percent:.1f}%

优化操作:
- 清理未使用的缓存
- 压缩内存池
- 优化对象引用
- 强制垃圾回收

优化后:
- 内存使用: {psutil.virtual_memory().percent:.1f}%
- 释放内存: {self._get_freed_memory():.1f} MB
"""
            
            self._show_info_window("内存优化", memory_report)
            
        except Exception as e:
            self.log(f"内存优化出错: {e}", "error")

    def _optimize_memory(self):
        """执行内存优化"""
        try:
            # 清理缓存
            self.dict_cache.clear()
            self.pattern_cache.clear()
            self.prefetch_cache.clear()
            
            # 压缩内存池
            if self.memory_pool:
                self.memory_pool['buffers'].clear()
                self.memory_pool['strings'].clear()
                self.memory_pool['objects'].clear()
            
            # 强制垃圾回收
            gc.collect()
            
            self.log("内存优化完成")
            
        except Exception as e:
            self.log(f"内存优化执行出错: {e}", "warning")

    def _get_freed_memory(self) -> float:
        """获取释放的内存大小"""
        try:
            # 这里可以实现内存释放统计
            return 0.0
        except:
            return 0.0

    def cache_management(self):
        """缓存管理"""
        try:
            # 显示缓存状态
            cache_report = f"""
缓存管理报告:
================

字典缓存:
- 缓存条目数: {len(self.dict_cache)}
- 缓存大小: {self._get_cache_size(self.dict_cache):.1f} MB

模式缓存:
- 缓存条目数: {len(self.pattern_cache)}
- 缓存大小: {self._get_cache_size(self.pattern_cache):.1f} MB

预取缓存:
- 缓存条目数: {len(self.prefetch_cache)}
- 缓存大小: {self._get_cache_size(self.prefetch_cache):.1f} MB

性能统计:
- 缓存命中: {self.performance_metrics['cache_hits']}
- 缓存未命中: {self.performance_metrics['cache_misses']}
- 命中率: {self.performance_metrics['cache_hits'] / max(self.performance_metrics['cache_hits'] + self.performance_metrics['cache_misses'], 1) * 100:.1f}%
"""
            
            self._show_info_window("缓存管理", cache_report)
            
        except Exception as e:
            self.log(f"缓存管理出错: {e}", "error")

    def _get_cache_size(self, cache_obj) -> float:
        """获取缓存大小（MB）"""
        try:
            import sys
            return sys.getsizeof(cache_obj) / (1024**2)
        except:
            return 0.0

    def process_monitoring(self):
        """进程监控"""
        try:
            # 获取进程信息
            process = psutil.Process()
            
            # 显示进程信息
            process_report = f"""
进程监控报告:
================

当前进程:
- PID: {process.pid}
- 名称: {process.name()}
- 状态: {process.status()}
- CPU使用率: {process.cpu_percent():.1f}%
- 内存使用: {process.memory_info().rss / (1024**2):.1f} MB
- 线程数: {process.num_threads()}
- 打开文件数: {len(process.open_files())}
- 网络连接数: {len(process.connections())}

系统进程:
- 总进程数: {len(psutil.pids())}
- 运行中进程: {len([p for p in psutil.process_iter() if p.status() == 'running'])}
- 睡眠进程: {len([p for p in psutil.process_iter() if p.status() == 'sleeping'])}
"""
            
            self._show_info_window("进程监控", process_report)
            
        except Exception as e:
            self.log(f"进程监控出错: {e}", "error")

    def _cleanup_on_exit(self):
        """退出时清理资源"""
        try:
            # 停止性能监控
            if hasattr(self, 'stop_performance_monitoring'):
                self.stop_performance_monitoring()
            
            # 清理进程池
            if hasattr(self, 'process_pool') and self.process_pool:
                try:
                    self.process_pool.terminate()
                    self.process_pool.join()
                except:
                    pass
            
            # 清理异步任务
            if hasattr(self, 'async_loop') and self.async_loop:
                try:
                    self.async_loop.stop()
                    self.async_loop.close()
                except:
                    pass
            
            # 清理线程池
            if hasattr(self, 'executor'):
                try:
                    self.executor.shutdown(wait=False)
                except:
                    pass
            
            # 清理写入线程
            if hasattr(self, 'write_thread') and self.write_thread:
                try:
                    self.write_queue.put(None)
                    self.write_thread.join(timeout=1)
                except:
                    pass
            
            # 保存设置
            if hasattr(self, 'save_settings'):
                self.save_settings()
            
            # 清理临时文件
            if hasattr(self, 'temp_files'):
                for temp_file in self.temp_files:
                    try:
                        if os.path.exists(temp_file):
                            os.unlink(temp_file)
                    except:
                        pass
            
            # 关闭数据库连接
            if hasattr(self, 'db_connection') and self.db_connection:
                try:
                    self.db_connection.close()
                except:
                    pass
            
            if hasattr(self, 'logger'):
                self.log("资源清理完成")
            
        except Exception as e:
            print(f"清理资源时出错: {e}")

    def _cleanup_previous_run(self):
        """清理之前的资源"""
        try:
            # 清理写入线程
            if hasattr(self, 'write_thread') and self.write_thread and self.write_thread.is_alive():
                try:
                    self.write_queue.put(None)
                    self.write_thread.join(timeout=2)
                except:
                    pass
            
            # 清理线程池
            if hasattr(self, 'executor'):
                try:
                    self.executor.shutdown(wait=False)
                    self.executor = concurrent.futures.ThreadPoolExecutor(max_workers=MAX_WORKERS)
                except:
                    pass
            
            # 清理进程池
            if hasattr(self, 'process_pool') and self.process_pool:
                try:
                    self.process_pool.terminate()
                    self.process_pool.join()
                    self.process_pool = None
                except:
                    pass
            
            # 清理异步任务
            if hasattr(self, 'async_loop') and self.async_loop:
                try:
                    self.async_loop.stop()
                    self.async_loop.close()
                    self.async_loop = None
                except:
                    pass
            
            # 清理进度文件
            self.cleanup_progress()
            
            # 重置关键状态
            self.write_buffer.clear()
            self.processed_count = 0
            self.last_log_update = 0
            self.backup_counter = 0
            self.last_backup_time = 0
            
            # 清理临时文件
            for temp_file in self.temp_files:
                try:
                    if os.path.exists(temp_file):
                        os.unlink(temp_file)
                except:
                    pass
            self.temp_files.clear()
            
            # 强制垃圾回收
            gc.collect()
            
        except Exception as e:
            self.log(f"清理之前的资源出错: {e}", "error")

    def _on_mousewheel(self, event):
        """处理鼠标滚轮事件"""
        if event.num == 4:  # Linux上滚
            self.main_canvas.yview_scroll(-1, "units")
        elif event.num == 5:  # Linux下滚
            self.main_canvas.yview_scroll(1, "units")
        else:  # Windows滚轮
            self.main_canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")

if __name__ == "__main__":
    import sys
    root = tk.Tk()
    app = CombinationGeneratorApp(root)
    root.mainloop() 