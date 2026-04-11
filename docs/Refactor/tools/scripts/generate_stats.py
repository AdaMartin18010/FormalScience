#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
统计生成脚本 (generate_stats.py)

功能说明:
-----------
该脚本用于生成文档项目的统计报告，包括:
- 文档数量、大小统计
- 代码行数统计（按语言分类）
- 文件类型分布
- 目录结构分析
- 可视化报告生成

使用方法:
-----------
1. 生成当前目录的统计报告:
   python generate_stats.py

2. 统计指定目录:
   python generate_stats.py -d /path/to/project

3. 生成 HTML 可视化报告:
   python generate_stats.py -o stats.html -f html

4. 仅统计 Markdown 文件:
   python generate_stats.py --only-markdown

5. 包含详细的代码统计:
   python generate_stats.py --include-code

参数说明:
-----------
-d, --directory     指定要统计的目录（默认: 当前目录）
-o, --output        输出报告文件路径
-f, --format        报告格式: text, json, html（默认: text）
--only-markdown     仅统计 Markdown 文件
--include-code      包含详细的代码行数统计
--exclude           排除特定路径（可多次使用）
--top-n             显示前 N 个最大的文件（默认: 20）
-v, --verbose       显示详细输出
-h, --help          显示帮助信息

作者: FormalScience 文档工具链
版本: 1.0.0
"""

import argparse
import json
import os
import sys
from collections import defaultdict
from dataclasses import dataclass, field, asdict
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Tuple


@dataclass
class FileStats:
    """单个文件的统计信息"""
    path: str
    size: int
    lines: int
    file_type: str
    extension: str


@dataclass
class DirectoryStats:
    """目录统计信息"""
    path: str
    file_count: int = 0
    total_size: int = 0
    total_lines: int = 0


@dataclass
class ProjectStats:
    """项目整体统计信息"""
    scan_time: str = ""
    base_directory: str = ""
    
    # 总体统计
    total_files: int = 0
    total_directories: int = 0
    total_size_bytes: int = 0
    total_lines: int = 0
    
    # 文件类型统计
    files_by_type: Dict[str, int] = field(default_factory=dict)
    files_by_extension: Dict[str, int] = field(default_factory=dict)
    size_by_type: Dict[str, int] = field(default_factory=dict)
    lines_by_type: Dict[str, int] = field(default_factory=dict)
    
    # 详细统计
    largest_files: List[FileStats] = field(default_factory=list)
    directory_stats: List[DirectoryStats] = field(default_factory=list)
    
    # Markdown 特有统计
    markdown_files: int = 0
    markdown_size: int = 0
    markdown_lines: int = 0
    
    # 代码统计
    code_files: int = 0
    code_size: int = 0
    code_lines: int = 0
    code_by_language: Dict[str, Dict[str, int]] = field(default_factory=dict)


class StatsGenerator:
    """统计生成器"""
    
    # 文件类型分类
    FILE_TYPES = {
        'markdown': ['.md', '.markdown', '.mdown', '.mkd', '.mkdn'],
        'code': ['.py', '.js', '.ts', '.jsx', '.tsx', '.java', '.cpp', '.c', '.h',
                 '.hpp', '.cs', '.go', '.rs', '.rb', '.php', '.swift', '.kt',
                 '.scala', '.r', '.m', '.mm', '.pl', '.sh', '.bash', '.zsh',
                 '.ps1', '.sql', '.html', '.css', '.scss', '.sass', '.less',
                 '.xml', '.yaml', '.yml', '.toml', '.ini', '.cfg', '.conf'],
        'document': ['.pdf', '.doc', '.docx', '.txt', '.rtf', '.odt'],
        'image': ['.png', '.jpg', '.jpeg', '.gif', '.bmp', '.svg', '.ico', '.webp'],
        'data': ['.json', '.csv', '.xls', '.xlsx', '.db', '.sqlite'],
        'other': []
    }
    
    # 代码语言映射
    LANGUAGE_MAP = {
        '.py': 'Python',
        '.js': 'JavaScript',
        '.ts': 'TypeScript',
        '.jsx': 'React JSX',
        '.tsx': 'React TSX',
        '.java': 'Java',
        '.cpp': 'C++',
        '.c': 'C',
        '.h': 'C/C++ Header',
        '.hpp': 'C++ Header',
        '.cs': 'C#',
        '.go': 'Go',
        '.rs': 'Rust',
        '.rb': 'Ruby',
        '.php': 'PHP',
        '.swift': 'Swift',
        '.kt': 'Kotlin',
        '.scala': 'Scala',
        '.r': 'R',
        '.m': 'Objective-C',
        '.mm': 'Objective-C++',
        '.pl': 'Perl',
        '.sh': 'Shell',
        '.bash': 'Bash',
        '.zsh': 'Zsh',
        '.ps1': 'PowerShell',
        '.sql': 'SQL',
        '.html': 'HTML',
        '.css': 'CSS',
        '.scss': 'SCSS',
        '.sass': 'Sass',
        '.less': 'Less',
        '.xml': 'XML',
        '.yaml': 'YAML',
        '.yml': 'YAML',
        '.toml': 'TOML',
        '.ini': 'INI',
        '.cfg': 'Config',
        '.conf': 'Config',
    }
    
    def __init__(self, base_dir: Path, only_markdown: bool = False,
                 include_code: bool = False, exclude_paths: Optional[List[str]] = None,
                 top_n: int = 20):
        """
        初始化统计生成器
        
        Args:
            base_dir: 基础目录
            only_markdown: 是否仅统计 Markdown 文件
            include_code: 是否包含详细代码统计
            exclude_paths: 要排除的路径列表
            top_n: 显示前 N 个最大文件
        """
        self.base_dir = Path(base_dir).resolve()
        self.only_markdown = only_markdown
        self.include_code = include_code
        self.exclude_paths = exclude_paths or []
        self.top_n = top_n
        self.stats = ProjectStats()
        self.file_list: List[FileStats] = []
        self.dir_stats_dict: Dict[str, DirectoryStats] = {}
        
    def _should_exclude(self, path: Path) -> bool:
        """检查路径是否应该被排除"""
        path_str = str(path)
        # 排除隐藏目录
        if any(part.startswith('.') for part in path.parts):
            return True
        # 排除指定路径
        for exclude in self.exclude_paths:
            if exclude in path_str:
                return True
        return False
    
    def _get_file_type(self, extension: str) -> str:
        """根据扩展名获取文件类型"""
        ext_lower = extension.lower()
        for file_type, extensions in self.FILE_TYPES.items():
            if ext_lower in extensions:
                return file_type
        return 'other'
    
    def _count_lines(self, file_path: Path) -> int:
        """计算文件的行数"""
        try:
            with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                return sum(1 for _ in f)
        except Exception:
            return 0
    
    def _analyze_file(self, file_path: Path) -> Optional[FileStats]:
        """分析单个文件"""
        if self._should_exclude(file_path):
            return None
        
        extension = file_path.suffix.lower()
        file_type = self._get_file_type(extension)
        
        # 如果只统计 Markdown，跳过其他类型
        if self.only_markdown and file_type != 'markdown':
            return None
        
        size = file_path.stat().st_size
        lines = self._count_lines(file_path)
        
        rel_path = str(file_path.relative_to(self.base_dir))
        
        return FileStats(
            path=rel_path,
            size=size,
            lines=lines,
            file_type=file_type,
            extension=extension
        )
    
    def _update_directory_stats(self, file_path: Path, file_stats: FileStats):
        """更新目录统计"""
        rel_path = file_path.relative_to(self.base_dir)
        dir_path = rel_path.parent
        
        # 逐级更新目录统计
        current = Path()
        for part in dir_path.parts:
            current = current / part
            dir_str = str(current)
            
            if dir_str not in self.dir_stats_dict:
                self.dir_stats_dict[dir_str] = DirectoryStats(
                    path=dir_str,
                    file_count=0,
                    total_size=0,
                    total_lines=0
                )
            
            self.dir_stats_dict[dir_str].file_count += 1
            self.dir_stats_dict[dir_str].total_size += file_stats.size
            self.dir_stats_dict[dir_str].total_lines += file_stats.lines
    
    def run(self) -> ProjectStats:
        """运行统计"""
        self.stats.scan_time = datetime.now().isoformat()
        self.stats.base_directory = str(self.base_dir)
        
        # 遍历目录
        for root, dirs, files in os.walk(self.base_dir):
            root_path = Path(root)
            
            # 过滤目录
            dirs[:] = [d for d in dirs if not d.startswith('.') 
                      and not self._should_exclude(root_path / d)]
            
            self.stats.total_directories += len(dirs)
            
            for filename in files:
                file_path = root_path / filename
                
                try:
                    file_stats = self._analyze_file(file_path)
                    if file_stats:
                        self.file_list.append(file_stats)
                        self._update_directory_stats(file_path, file_stats)
                except Exception as e:
                    if self.include_code:
                        print(f"警告: 无法分析文件 {file_path}: {e}")
        
        # 计算总体统计
        self._calculate_totals()
        
        # 计算文件类型统计
        self._calculate_type_stats()
        
        # 计算代码统计
        if self.include_code:
            self._calculate_code_stats()
        
        # 排序并选择最大的文件
        self._calculate_top_files()
        
        # 目录统计
        self.stats.directory_stats = sorted(
            self.dir_stats_dict.values(),
            key=lambda x: x.total_size,
            reverse=True
        )[:20]  # 只保留前20个最大的目录
        
        return self.stats
    
    def _calculate_totals(self):
        """计算总体统计"""
        self.stats.total_files = len(self.file_list)
        self.stats.total_size_bytes = sum(f.size for f in self.file_list)
        self.stats.total_lines = sum(f.lines for f in self.file_list)
        
        # Markdown 统计
        md_files = [f for f in self.file_list if f.file_type == 'markdown']
        self.stats.markdown_files = len(md_files)
        self.stats.markdown_size = sum(f.size for f in md_files)
        self.stats.markdown_lines = sum(f.lines for f in md_files)
        
        # 代码文件统计
        code_files = [f for f in self.file_list if f.file_type == 'code']
        self.stats.code_files = len(code_files)
        self.stats.code_size = sum(f.size for f in code_files)
        self.stats.code_lines = sum(f.lines for f in code_files)
    
    def _calculate_type_stats(self):
        """计算文件类型统计"""
        for f in self.file_list:
            # 按类型统计
            self.stats.files_by_type[f.file_type] = \
                self.stats.files_by_type.get(f.file_type, 0) + 1
            self.stats.size_by_type[f.file_type] = \
                self.stats.size_by_type.get(f.file_type, 0) + f.size
            self.stats.lines_by_type[f.file_type] = \
                self.stats.lines_by_type.get(f.file_type, 0) + f.lines
            
            # 按扩展名统计
            self.stats.files_by_extension[f.extension] = \
                self.stats.files_by_extension.get(f.extension, 0) + 1
    
    def _calculate_code_stats(self):
        """计算代码统计"""
        code_files = [f for f in self.file_list if f.file_type == 'code']
        
        for f in code_files:
            lang = self.LANGUAGE_MAP.get(f.extension, 'Unknown')
            if lang not in self.stats.code_by_language:
                self.stats.code_by_language[lang] = {
                    'files': 0,
                    'lines': 0,
                    'size': 0
                }
            
            self.stats.code_by_language[lang]['files'] += 1
            self.stats.code_by_language[lang]['lines'] += f.lines
            self.stats.code_by_language[lang]['size'] += f.size
    
    def _calculate_top_files(self):
        """计算最大的文件"""
        sorted_files = sorted(self.file_list, key=lambda x: x.size, reverse=True)
        self.stats.largest_files = sorted_files[:self.top_n]
    
    def _format_size(self, size_bytes: int) -> str:
        """格式化文件大小"""
        for unit in ['B', 'KB', 'MB', 'GB', 'TB']:
            if size_bytes < 1024.0:
                return f"{size_bytes:.2f} {unit}"
            size_bytes /= 1024.0
        return f"{size_bytes:.2f} PB"
    
    def _format_number(self, num: int) -> str:
        """格式化数字"""
        return f"{num:,}"
    
    def print_report(self, verbose: bool = False):
        """打印报告到控制台"""
        print("\n" + "=" * 70)
        print("                     项目统计报告")
        print("=" * 70)
        print(f"扫描时间: {self.stats.scan_time}")
        print(f"基础目录: {self.stats.base_directory}")
        print("-" * 70)
        
        # 总体统计
        print("\n📊 总体统计:")
        print(f"  文件总数:     {self._format_number(self.stats.total_files)}")
        print(f"  目录总数:     {self._format_number(self.stats.total_directories)}")
        print(f"  总大小:       {self._format_size(self.stats.total_size_bytes)}")
        print(f"  总行数:       {self._format_number(self.stats.total_lines)}")
        
        # Markdown 统计
        if self.stats.markdown_files > 0:
            print("\n📝 Markdown 文档统计:")
            print(f"  文件数:       {self._format_number(self.stats.markdown_files)}")
            print(f"  总大小:       {self._format_size(self.stats.markdown_size)}")
            print(f"  总行数:       {self._format_number(self.stats.markdown_lines)}")
            if self.stats.markdown_files > 0:
                avg_lines = self.stats.markdown_lines / self.stats.markdown_files
                print(f"  平均行数:     {avg_lines:.1f}")
        
        # 代码统计
        if self.stats.code_files > 0:
            print("\n💻 代码文件统计:")
            print(f"  文件数:       {self._format_number(self.stats.code_files)}")
            print(f"  总大小:       {self._format_size(self.stats.code_size)}")
            print(f"  总行数:       {self._format_number(self.stats.code_lines)}")
        
        # 文件类型分布
        if self.stats.files_by_type:
            print("\n📁 文件类型分布:")
            sorted_types = sorted(
                self.stats.files_by_type.items(),
                key=lambda x: x[1],
                reverse=True
            )
            for file_type, count in sorted_types:
                size = self.stats.size_by_type.get(file_type, 0)
                lines = self.stats.lines_by_type.get(file_type, 0)
                print(f"  {file_type:12s}: {self._format_number(count):>8s} 文件, "
                      f"{self._format_size(size):>10s}, "
                      f"{self._format_number(lines):>10s} 行")
        
        # 代码语言统计
        if self.include_code and self.stats.code_by_language:
            print("\n🔧 编程语言统计:")
            sorted_langs = sorted(
                self.stats.code_by_language.items(),
                key=lambda x: x[1]['lines'],
                reverse=True
            )
            for lang, data in sorted_langs[:10]:  # 只显示前10
                print(f"  {lang:15s}: {self._format_number(data['files']):>6s} 文件, "
                      f"{self._format_number(data['lines']):>10s} 行, "
                      f"{self._format_size(data['size']):>10s}")
        
        # 最大的文件
        if self.stats.largest_files:
            print(f"\n📦 最大的 {self.top_n} 个文件:")
            for i, f in enumerate(self.stats.largest_files, 1):
                print(f"  {i:2d}. {f.path}")
                print(f"      大小: {self._format_size(f.size):>10s}, "
                      f"行数: {self._format_number(f.lines):>8s}, "
                      f"类型: {f.file_type}")
        
        # 最大的目录
        if verbose and self.stats.directory_stats:
            print(f"\n📂 最大的目录 (前 20):")
            for i, d in enumerate(self.stats.directory_stats, 1):
                print(f"  {i:2d}. {d.path}/")
                print(f"      文件: {self._format_number(d.file_count):>6s}, "
                      f"大小: {self._format_size(d.total_size):>10s}, "
                      f"行数: {self._format_number(d.total_lines):>8s}")
        
        print("\n" + "=" * 70)
    
    def save_report(self, output_path: str, format_type: str = 'text'):
        """保存报告到文件"""
        output_path = Path(output_path)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        if format_type == 'json':
            self._save_json_report(output_path)
        elif format_type == 'html':
            self._save_html_report(output_path)
        else:
            self._save_text_report(output_path)
        
        print(f"\n报告已保存到: {output_path}")
    
    def _save_json_report(self, output_path: Path):
        """保存 JSON 格式报告"""
        report_dict = {
            'scan_info': {
                'scan_time': self.stats.scan_time,
                'base_directory': self.stats.base_directory,
            },
            'summary': {
                'total_files': self.stats.total_files,
                'total_directories': self.stats.total_directories,
                'total_size_bytes': self.stats.total_size_bytes,
                'total_lines': self.stats.total_lines,
            },
            'markdown': {
                'files': self.stats.markdown_files,
                'size_bytes': self.stats.markdown_size,
                'lines': self.stats.markdown_lines,
            },
            'code': {
                'files': self.stats.code_files,
                'size_bytes': self.stats.code_size,
                'lines': self.stats.code_lines,
                'by_language': self.stats.code_by_language,
            },
            'file_types': {
                'by_type': self.stats.files_by_type,
                'by_extension': self.stats.files_by_extension,
            },
            'largest_files': [asdict(f) for f in self.stats.largest_files],
            'directory_stats': [asdict(d) for d in self.stats.directory_stats],
        }
        
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(report_dict, f, ensure_ascii=False, indent=2)
    
    def _save_text_report(self, output_path: Path):
        """保存文本格式报告"""
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write("=" * 70 + "\n")
            f.write("                     项目统计报告\n")
            f.write("=" * 70 + "\n")
            f.write(f"扫描时间: {self.stats.scan_time}\n")
            f.write(f"基础目录: {self.stats.base_directory}\n")
            f.write("-" * 70 + "\n\n")
            
            f.write("总体统计:\n")
            f.write(f"  文件总数:     {self._format_number(self.stats.total_files)}\n")
            f.write(f"  目录总数:     {self._format_number(self.stats.total_directories)}\n")
            f.write(f"  总大小:       {self._format_size(self.stats.total_size_bytes)}\n")
            f.write(f"  总行数:       {self._format_number(self.stats.total_lines)}\n\n")
            
            if self.stats.markdown_files > 0:
                f.write("Markdown 文档统计:\n")
                f.write(f"  文件数:       {self._format_number(self.stats.markdown_files)}\n")
                f.write(f"  总大小:       {self._format_size(self.stats.markdown_size)}\n")
                f.write(f"  总行数:       {self._format_number(self.stats.markdown_lines)}\n\n")
            
            if self.stats.files_by_type:
                f.write("文件类型分布:\n")
                for file_type, count in sorted(
                    self.stats.files_by_type.items(),
                    key=lambda x: x[1],
                    reverse=True
                ):
                    f.write(f"  {file_type}: {count}\n")
    
    def _save_html_report(self, output_path: Path):
        """保存 HTML 格式报告"""
        # 计算图表数据
        type_labels = list(self.stats.files_by_type.keys())
        type_data = list(self.stats.files_by_type.values())
        
        html_content = f"""<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>项目统计报告</title>
    <script src="https://cdn.jsdelivr.net/npm/chart.js"></script>
    <style>
        * {{ box-sizing: border-box; }}
        body {{
            font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;
            max-width: 1400px;
            margin: 0 auto;
            padding: 20px;
            background: #f5f7fa;
            color: #333;
        }}
        .header {{
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            color: white;
            padding: 40px;
            border-radius: 15px;
            margin-bottom: 30px;
            text-align: center;
        }}
        .header h1 {{ margin: 0 0 10px 0; font-size: 2.5em; }}
        .header p {{ margin: 0; opacity: 0.9; }}
        .stats-grid {{
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(250px, 1fr));
            gap: 20px;
            margin-bottom: 30px;
        }}
        .stat-card {{
            background: white;
            padding: 25px;
            border-radius: 12px;
            box-shadow: 0 4px 6px rgba(0,0,0,0.07);
            transition: transform 0.2s;
        }}
        .stat-card:hover {{ transform: translateY(-5px); }}
        .stat-card h3 {{
            margin: 0 0 15px 0;
            color: #666;
            font-size: 14px;
            text-transform: uppercase;
            letter-spacing: 1px;
        }}
        .stat-card .value {{
            font-size: 36px;
            font-weight: bold;
            color: #333;
        }}
        .stat-card .sub-value {{
            font-size: 14px;
            color: #999;
            margin-top: 5px;
        }}
        .chart-container {{
            background: white;
            padding: 25px;
            border-radius: 12px;
            box-shadow: 0 4px 6px rgba(0,0,0,0.07);
            margin-bottom: 30px;
        }}
        .chart-container h2 {{
            margin: 0 0 20px 0;
            color: #333;
            font-size: 1.5em;
        }}
        .chart-wrapper {{
            position: relative;
            height: 300px;
        }}
        .two-columns {{
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(400px, 1fr));
            gap: 30px;
        }}
        table {{
            width: 100%;
            border-collapse: collapse;
            margin-top: 15px;
        }}
        th, td {{
            padding: 12px;
            text-align: left;
            border-bottom: 1px solid #eee;
        }}
        th {{
            background: #f8f9fa;
            font-weight: 600;
            color: #666;
        }}
        tr:hover {{ background: #f8f9fa; }}
        .badge {{
            display: inline-block;
            padding: 4px 10px;
            border-radius: 20px;
            font-size: 12px;
            font-weight: 500;
        }}
        .badge-markdown {{ background: #e3f2fd; color: #1976d2; }}
        .badge-code {{ background: #f3e5f5; color: #7b1fa2; }}
        .badge-other {{ background: #f5f5f5; color: #666; }}
        .footer {{
            text-align: center;
            padding: 30px;
            color: #999;
            font-size: 14px;
        }}
    </style>
</head>
<body>
    <div class="header">
        <h1>📊 项目统计报告</h1>
        <p>扫描时间: {self.stats.scan_time}</p>
        <p>基础目录: {self.stats.base_directory}</p>
    </div>
    
    <div class="stats-grid">
        <div class="stat-card">
            <h3>文件总数</h3>
            <div class="value">{self._format_number(self.stats.total_files)}</div>
            <div class="sub-value">{self._format_number(self.stats.total_directories)} 个目录</div>
        </div>
        <div class="stat-card">
            <h3>总大小</h3>
            <div class="value">{self._format_size(self.stats.total_size_bytes)}</div>
            <div class="sub-value">{self._format_number(self.stats.total_lines)} 行</div>
        </div>
        <div class="stat-card">
            <h3>Markdown 文档</h3>
            <div class="value">{self._format_number(self.stats.markdown_files)}</div>
            <div class="sub-value">{self._format_size(self.stats.markdown_size)}</div>
        </div>
        <div class="stat-card">
            <h3>代码文件</h3>
            <div class="value">{self._format_number(self.stats.code_files)}</div>
            <div class="sub-value">{self._format_number(self.stats.code_lines)} 行代码</div>
        </div>
    </div>
    
    <div class="two-columns">
        <div class="chart-container">
            <h2>📁 文件类型分布</h2>
            <div class="chart-wrapper">
                <canvas id="typeChart"></canvas>
            </div>
        </div>
        <div class="chart-container">
            <h2>📝 文件扩展名分布 (Top 10)</h2>
            <div class="chart-wrapper">
                <canvas id="extChart"></canvas>
            </div>
        </div>
    </div>
    
    <div class="chart-container">
        <h2>📦 最大的 {self.top_n} 个文件</h2>
        <table>
            <thead>
                <tr>
                    <th>排名</th>
                    <th>文件路径</th>
                    <th>类型</th>
                    <th>大小</th>
                    <th>行数</th>
                </tr>
            </thead>
            <tbody>
"""
        
        for i, f in enumerate(self.stats.largest_files, 1):
            badge_class = f"badge-{f.file_type}" if f.file_type in ['markdown', 'code'] else 'badge-other'
            html_content += f"""
                <tr>
                    <td>{i}</td>
                    <td>{f.path}</td>
                    <td><span class="badge {badge_class}">{f.file_type}</span></td>
                    <td>{self._format_size(f.size)}</td>
                    <td>{self._format_number(f.lines)}</td>
                </tr>
"""
        
        html_content += f"""
            </tbody>
        </table>
    </div>
    
    <div class="footer">
        <p>由 FormalScience 统计生成器生成</p>
    </div>
    
    <script>
        // 文件类型分布图表
        const typeCtx = document.getElementById('typeChart').getContext('2d');
        new Chart(typeCtx, {{
            type: 'doughnut',
            data: {{
                labels: {json.dumps(type_labels)},
                datasets: [{{
                    data: {json.dumps(type_data)},
                    backgroundColor: [
                        '#667eea', '#764ba2', '#f093fb', '#f5576c',
                        '#4facfe', '#00f2fe', '#43e97b', '#fa709a'
                    ]
                }}]
            }},
            options: {{
                responsive: true,
                maintainAspectRatio: false,
                plugins: {{
                    legend: {{
                        position: 'right'
                    }}
                }}
            }}
        }});
        
        // 扩展名分布图表
        const extLabels = {json.dumps(list(self.stats.files_by_extension.keys())[:10])};
        const extData = {json.dumps(list(self.stats.files_by_extension.values())[:10])};
        
        const extCtx = document.getElementById('extChart').getContext('2d');
        new Chart(extCtx, {{
            type: 'bar',
            data: {{
                labels: extLabels,
                datasets: [{{
                    label: '文件数量',
                    data: extData,
                    backgroundColor: '#667eea'
                }}]
            }},
            options: {{
                responsive: true,
                maintainAspectRatio: false,
                scales: {{
                    y: {{
                        beginAtZero: true
                    }}
                }}
            }}
        }});
    </script>
</body>
</html>
"""
        
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(html_content)


def main():
    """主函数"""
    parser = argparse.ArgumentParser(
        description='生成文档项目统计报告',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
  %(prog)s                           # 统计当前目录
  %(prog)s -d ./docs                 # 统计指定目录
  %(prog)s -o stats.html -f html     # 生成 HTML 报告
  %(prog)s --only-markdown           # 仅统计 Markdown
  %(prog)s --include-code            # 包含详细代码统计
        """
    )
    
    parser.add_argument(
        '-d', '--directory',
        default='.',
        help='要统计的目录（默认: 当前目录）'
    )
    parser.add_argument(
        '-o', '--output',
        help='输出报告文件路径'
    )
    parser.add_argument(
        '-f', '--format',
        choices=['text', 'json', 'html'],
        default='text',
        help='报告格式（默认: text）'
    )
    parser.add_argument(
        '--only-markdown',
        action='store_true',
        help='仅统计 Markdown 文件'
    )
    parser.add_argument(
        '--include-code',
        action='store_true',
        help='包含详细的代码行数统计'
    )
    parser.add_argument(
        '--exclude',
        action='append',
        default=[],
        help='排除特定路径（可多次使用）'
    )
    parser.add_argument(
        '--top-n',
        type=int,
        default=20,
        help='显示前 N 个最大的文件（默认: 20）'
    )
    parser.add_argument(
        '-v', '--verbose',
        action='store_true',
        help='显示详细输出'
    )
    
    args = parser.parse_args()
    
    # 检查目录
    base_dir = Path(args.directory)
    if not base_dir.exists():
        print(f"错误: 目录不存在: {base_dir}", file=sys.stderr)
        sys.exit(1)
    
    if not base_dir.is_dir():
        print(f"错误: 不是目录: {base_dir}", file=sys.stderr)
        sys.exit(1)
    
    # 创建生成器并运行
    generator = StatsGenerator(
        base_dir=base_dir,
        only_markdown=args.only_markdown,
        include_code=args.include_code,
        exclude_paths=args.exclude,
        top_n=args.top_n
    )
    
    print(f"开始统计...")
    print(f"目录: {base_dir.resolve()}")
    
    stats = generator.run()
    
    # 打印报告
    generator.print_report(verbose=args.verbose)
    
    # 保存报告
    if args.output:
        generator.save_report(args.output, args.format)
    
    sys.exit(0)


if __name__ == '__main__':
    main()
