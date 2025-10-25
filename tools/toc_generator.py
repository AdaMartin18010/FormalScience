#!/usr/bin/env python3
"""
Formal Science TOC Generator
自动为markdown文档生成目录

Usage:
    python tools/toc_generator.py <file1.md> [file2.md ...]
    python tools/toc_generator.py Concept/*.md --max-level 3
    python tools/toc_generator.py --batch --dir Concept/
"""

import re
from pathlib import Path
from typing import List, Tuple
from dataclasses import dataclass
import argparse
import sys

try:
    from rich.console import Console
    from rich.progress import track
    HAS_RICH = True
except ImportError:
    HAS_RICH = False


@dataclass
class Header:
    """标题数据类"""
    level: int
    title: str
    anchor: str
    line_num: int


class TOCGenerator:
    """目录生成器"""
    
    def __init__(self, console=None):
        self.console = console if console else self._create_console()
        
        # TOC标记
        self.toc_start_marker = "<!-- TOC -->"
        self.toc_end_marker = "<!-- /TOC -->"
        
        # 标题模式
        self.header_pattern = re.compile(r'^(#{1,6})\s+(.+)$')
        
        # 统计
        self.processed_files = 0
        self.skipped_files = 0
        self.total_tocs = 0
    
    def _create_console(self):
        """创建控制台对象"""
        if HAS_RICH:
            return Console()
        else:
            class SimpleConsole:
                def print(self, *args, **kwargs):
                    print(*args)
            return SimpleConsole()
    
    def extract_headers(self, file: Path) -> List[Header]:
        """提取所有标题"""
        headers = []
        
        try:
            with open(file, 'r', encoding='utf-8') as f:
                for line_num, line in enumerate(f, 1):
                    match = self.header_pattern.match(line)
                    if match:
                        level = len(match.group(1))
                        title = match.group(2).strip()
                        
                        # 移除标题中的链接
                        title = self._clean_title(title)
                        
                        anchor = self.title_to_anchor(title)
                        headers.append(Header(level, title, anchor, line_num))
        except Exception as e:
            self.console.print(f"[red]错误: 无法读取文件 {file}: {e}[/red]")
        
        return headers
    
    @staticmethod
    def _clean_title(title: str) -> str:
        """清理标题文本"""
        # 移除markdown链接 [text](url)
        title = re.sub(r'\[([^\]]+)\]\([^\)]+\)', r'\1', title)
        
        # 移除行内代码标记
        title = re.sub(r'`([^`]+)`', r'\1', title)
        
        # 移除多余空格
        title = re.sub(r'\s+', ' ', title).strip()
        
        return title
    
    @staticmethod
    def title_to_anchor(title: str) -> str:
        """
        标题转锚点（与GitHub兼容）
        示例:
            "Hello World" -> "hello-world"
            "第一章 引言" -> "第一章-引言"
            "1. Introduction" -> "1-introduction"
        """
        # 移除emoji和特殊符号（保留中英文、数字、空格、连字符）
        cleaned = re.sub(r'[^\w\s\u4e00-\u9fff-]', '', title)
        
        # 转小写
        anchor = cleaned.strip().lower()
        
        # 空格和多个连字符替换为单个连字符
        anchor = re.sub(r'[\s_]+', '-', anchor)
        anchor = re.sub(r'-+', '-', anchor)
        
        return anchor.strip('-')
    
    def generate_toc(self, headers: List[Header], max_level: int = 4, 
                    start_level: int = 1) -> str:
        """
        生成目录字符串
        
        Args:
            headers: 标题列表
            max_level: 最大层级
            start_level: 起始层级（用于调整缩进）
        
        Returns:
            目录markdown文本
        """
        if not headers:
            return ""
        
        toc_lines = [self.toc_start_marker, ""]
        
        # 找到最小层级作为基准
        min_level = min(h.level for h in headers if h.level >= start_level)
        
        for header in headers:
            # 跳过标题级别过大的
            if header.level > max_level:
                continue
            
            # 跳过起始级别之前的
            if header.level < start_level:
                continue
            
            # 计算缩进
            indent_level = header.level - min_level
            indent = "  " * indent_level
            
            # 生成链接
            link = f"[{header.title}](#{header.anchor})"
            toc_lines.append(f"{indent}- {link}")
        
        toc_lines.extend(["", self.toc_end_marker, ""])
        
        return "\n".join(toc_lines)
    
    def has_existing_toc(self, content: str) -> bool:
        """检查是否已有目录"""
        return self.toc_start_marker in content
    
    def remove_existing_toc(self, content: str) -> str:
        """移除现有目录"""
        pattern = f"{re.escape(self.toc_start_marker)}.*?{re.escape(self.toc_end_marker)}"
        return re.sub(pattern, "", content, flags=re.DOTALL)
    
    def insert_toc(self, file: Path, toc: str, position: str = "after_title"):
        """
        插入目录到文件
        
        Args:
            file: 文件路径
            toc: 目录内容
            position: 插入位置 ('after_title' 或 'top')
        """
        try:
            with open(file, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            self.console.print(f"[red]错误: 无法读取 {file}: {e}[/red]")
            return False
        
        # 移除旧目录
        content = self.remove_existing_toc(content)
        
        # 确定插入位置
        if position == "after_title":
            # 在第一个一级标题后插入
            match = re.search(r'^#\s+.+$', content, re.MULTILINE)
            if match:
                insert_pos = match.end()
                # 跳过标题后的空行
                next_content = content[insert_pos:]
                empty_lines = re.match(r'\n*', next_content)
                if empty_lines:
                    insert_pos += len(empty_lines.group(0))
                
                content = content[:insert_pos] + "\n\n" + toc + "\n" + content[insert_pos:]
            else:
                # 没有一级标题，插入开头
                content = toc + "\n\n" + content
        else:
            # 插入开头
            content = toc + "\n\n" + content
        
        # 写回文件
        try:
            with open(file, 'w', encoding='utf-8') as f:
                f.write(content)
            return True
        except Exception as e:
            self.console.print(f"[red]错误: 无法写入 {file}: {e}[/red]")
            return False
    
    def process_file(self, file: Path, max_level: int = 4, 
                    min_headers: int = 3, force: bool = False,
                    dry_run: bool = False) -> bool:
        """
        处理单个文件
        
        Args:
            file: 文件路径
            max_level: 最大标题层级
            min_headers: 最小标题数量（少于此数量则跳过）
            force: 强制更新（即使已有TOC）
            dry_run: 预览模式（不实际修改文件）
        
        Returns:
            是否成功处理
        """
        if not file.exists():
            self.console.print(f"[yellow]跳过: 文件不存在 - {file}[/yellow]")
            self.skipped_files += 1
            return False
        
        # 提取标题
        headers = self.extract_headers(file)
        
        # 检查标题数量
        if len(headers) < min_headers:
            if HAS_RICH:
                self.console.print(f"[dim]跳过: {file.name} (标题数 {len(headers)} < {min_headers})[/dim]")
            else:
                print(f"跳过: {file.name} (标题数不足)")
            self.skipped_files += 1
            return False
        
        # 检查是否已有TOC
        try:
            with open(file, 'r', encoding='utf-8') as f:
                content = f.read()
            
            if self.has_existing_toc(content) and not force:
                if HAS_RICH:
                    self.console.print(f"[dim]跳过: {file.name} (已有TOC，使用--force强制更新)[/dim]")
                else:
                    print(f"跳过: {file.name} (已有TOC)")
                self.skipped_files += 1
                return False
        except Exception as e:
            self.console.print(f"[red]错误: {file.name} - {e}[/red]")
            self.skipped_files += 1
            return False
        
        # 生成TOC
        toc = self.generate_toc(headers, max_level)
        
        # 预览模式
        if dry_run:
            if HAS_RICH:
                self.console.print(f"[cyan]预览: {file.name}[/cyan]")
                self.console.print(f"[dim]{toc}[/dim]")
            else:
                print(f"\n预览: {file.name}")
                print(toc)
            return True
        
        # 插入TOC
        if self.insert_toc(file, toc):
            if HAS_RICH:
                self.console.print(f"[green]✓[/green] {file.name} (生成 {len(headers)} 项)")
            else:
                print(f"✓ {file.name} (生成 {len(headers)} 项)")
            self.processed_files += 1
            self.total_tocs += 1
            return True
        else:
            self.skipped_files += 1
            return False
    
    def process_batch(self, files: List[Path], **kwargs):
        """批量处理文件"""
        if HAS_RICH:
            file_iter = track(files, description="处理文件中...")
        else:
            file_iter = files
            print(f"处理 {len(files)} 个文件...")
        
        for file in file_iter:
            self.process_file(file, **kwargs)
    
    def print_summary(self):
        """打印处理摘要"""
        if HAS_RICH:
            self.console.print("\n[bold cyan]处理摘要[/bold cyan]")
            self.console.print(f"✓ 处理成功: [green]{self.processed_files}[/green]")
            self.console.print(f"⊗ 跳过文件: [yellow]{self.skipped_files}[/yellow]")
            self.console.print(f"📑 生成目录: [cyan]{self.total_tocs}[/cyan]")
        else:
            print("\n处理摘要:")
            print(f"✓ 处理成功: {self.processed_files}")
            print(f"⊗ 跳过文件: {self.skipped_files}")
            print(f"📑 生成目录: {self.total_tocs}")


def main():
    parser = argparse.ArgumentParser(
        description="为markdown文档自动生成目录",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例用法:
  python tools/toc_generator.py Concept/README.md           # 单个文件
  python tools/toc_generator.py Concept/*.md                # 批量处理
  python tools/toc_generator.py --batch --dir Concept/      # 扫描目录
  python tools/toc_generator.py file.md --max-level 3       # 限制层级
  python tools/toc_generator.py file.md --force             # 强制更新
  python tools/toc_generator.py file.md --dry-run           # 预览模式
        """
    )
    
    parser.add_argument(
        'files',
        nargs='*',
        type=Path,
        help='要处理的文件列表'
    )
    
    parser.add_argument(
        '--batch',
        action='store_true',
        help='批量模式：扫描目录下所有markdown文件'
    )
    
    parser.add_argument(
        '--dir',
        type=Path,
        default=Path('.'),
        help='批量模式下的扫描目录 (默认: 当前目录)'
    )
    
    parser.add_argument(
        '--max-level',
        type=int,
        default=4,
        help='最大标题层级 (默认: 4)'
    )
    
    parser.add_argument(
        '--min-headers',
        type=int,
        default=3,
        help='最小标题数量，少于此数量则跳过 (默认: 3)'
    )
    
    parser.add_argument(
        '--force',
        action='store_true',
        help='强制更新已有TOC'
    )
    
    parser.add_argument(
        '--dry-run',
        action='store_true',
        help='预览模式：只显示将生成的TOC，不修改文件'
    )
    
    args = parser.parse_args()
    
    # 收集文件列表
    files = []
    
    if args.batch:
        # 批量模式：扫描目录
        if not args.dir.exists():
            print(f"错误: 目录不存在: {args.dir}")
            sys.exit(1)
        
        files = list(args.dir.rglob("*.md"))
        
        # 排除一些特殊文件
        exclude_patterns = ['node_modules', '.git', '__pycache__', 'LINK_', 'PROGRESS_', 'REPORT_']
        files = [f for f in files if not any(p in str(f) for p in exclude_patterns)]
    
    elif args.files:
        # 指定文件
        files = args.files
    else:
        parser.print_help()
        sys.exit(0)
    
    if not files:
        print("未找到要处理的文件")
        sys.exit(0)
    
    # 创建生成器
    console = Console() if HAS_RICH else None
    generator = TOCGenerator(console)
    
    # 处理文件
    if len(files) == 1:
        # 单文件模式
        generator.process_file(
            files[0],
            max_level=args.max_level,
            min_headers=args.min_headers,
            force=args.force,
            dry_run=args.dry_run
        )
    else:
        # 批量模式
        generator.process_batch(
            files,
            max_level=args.max_level,
            min_headers=args.min_headers,
            force=args.force,
            dry_run=args.dry_run
        )
    
    # 打印摘要
    generator.print_summary()


if __name__ == "__main__":
    main()

