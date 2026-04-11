#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
内容搜索脚本 (search.py)

功能说明:
-----------
该脚本用于在 Markdown 文档中进行内容搜索，支持:
- 关键词搜索（支持正则表达式）
- 跨文件搜索
- 搜索结果格式化输出
- 上下文预览
- 搜索结果统计
- 导出搜索结果

使用方法:
-----------
1. 基本关键词搜索:
   python search.py "关键词"

2. 在指定目录搜索:
   python search.py "关键词" -d /path/to/docs

3. 使用正则表达式搜索:
   python search.py "pattern.*test" --regex

4. 显示上下文行:
   python search.py "关键词" -C 3

5. 搜索并导出结果:
   python search.py "关键词" -o results.json -f json

6. 仅搜索标题:
   python search.py "关键词" --in-headings

参数说明:
-----------
query               搜索关键词或正则表达式
-d, --directory     指定搜索目录（默认: 当前目录）
--regex             使用正则表达式搜索
-i, --ignore-case   忽略大小写
-w, --word-regexp   匹配完整单词
-C, --context       显示上下文行数（默认: 2）
--in-headings       仅在标题中搜索
--in-code           仅在代码块中搜索
--exclude-code      排除代码块
--file-pattern      指定文件匹配模式（默认: *.md）
--max-results       最大结果数（默认: 100）
-o, --output        输出结果到文件
-f, --format        输出格式: text, json, html（默认: text）
--exclude           排除特定路径（可多次使用）
-h, --help          显示帮助信息

搜索示例:
-----------
  # 搜索包含 "Rust" 的文档
  python search.py "Rust"
  
  # 搜索标题中包含 "设计" 的内容
  python search.py "设计" --in-headings
  
  # 搜索代码块中的函数定义
  python search.py "def \w+" --regex --in-code
  
  # 搜索并显示5行上下文
  python search.py "重要概念" -C 5

作者: FormalScience 文档工具链
版本: 1.0.0
"""

import argparse
import json
import os
import re
import sys
from dataclasses import dataclass, field, asdict
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple, Iterator


@dataclass
class SearchMatch:
    """搜索结果匹配项"""
    file_path: str
    line_number: int
    column_start: int
    column_end: int
    matched_text: str
    line_content: str
    context_before: List[str] = field(default_factory=list)
    context_after: List[str] = field(default_factory=list)


@dataclass
class FileResult:
    """单个文件的搜索结果"""
    file_path: str
    file_title: str = ""
    matches: List[SearchMatch] = field(default_factory=list)
    match_count: int = 0


@dataclass
class SearchReport:
    """搜索报告"""
    query: str = ""
    search_time: str = ""
    base_directory: str = ""
    total_files_searched: int = 0
    files_with_matches: int = 0
    total_matches: int = 0
    search_duration_ms: float = 0.0
    results: List[FileResult] = field(default_factory=list)


class ContentSearcher:
    """内容搜索器"""
    
    # Markdown 标题模式
    HEADING_PATTERN = re.compile(r'^#{1,6}\s+(.+)$', re.MULTILINE)
    
    # 代码块模式
    CODE_BLOCK_PATTERN = re.compile(r'```[\s\S]*?```')
    CODE_BLOCK_START = re.compile(r'^```')
    
    def __init__(self, base_dir: Path, query: str, use_regex: bool = False,
                 ignore_case: bool = True, word_regexp: bool = False,
                 context_lines: int = 2, in_headings: bool = False,
                 in_code: bool = False, exclude_code: bool = False,
                 file_pattern: str = '*.md', max_results: int = 100,
                 exclude_paths: Optional[List[str]] = None):
        """
        初始化内容搜索器
        
        Args:
            base_dir: 基础搜索目录
            query: 搜索关键词或正则表达式
            use_regex: 是否使用正则表达式
            ignore_case: 是否忽略大小写
            word_regexp: 是否匹配完整单词
            context_lines: 上下文行数
            in_headings: 是否仅在标题中搜索
            in_code: 是否仅在代码块中搜索
            exclude_code: 是否排除代码块
            file_pattern: 文件匹配模式
            max_results: 最大结果数
            exclude_paths: 要排除的路径列表
        """
        self.base_dir = Path(base_dir).resolve()
        self.query = query
        self.use_regex = use_regex
        self.ignore_case = ignore_case
        self.word_regexp = word_regexp
        self.context_lines = context_lines
        self.in_headings = in_headings
        self.in_code = in_code
        self.exclude_code = exclude_code
        self.file_pattern = file_pattern
        self.max_results = max_results
        self.exclude_paths = exclude_paths or []
        self.report = SearchReport()
        
        # 编译搜索模式
        self.search_pattern = self._compile_pattern()
        
    def _compile_pattern(self) -> re.Pattern:
        """编译搜索模式"""
        flags = re.MULTILINE
        if self.ignore_case:
            flags |= re.IGNORECASE
        
        if self.use_regex:
            pattern = self.query
        else:
            # 转义特殊字符
            pattern = re.escape(self.query)
        
        if self.word_regexp:
            pattern = r'\b' + pattern + r'\b'
        
        try:
            return re.compile(pattern, flags)
        except re.error as e:
            print(f"错误: 无效的正则表达式: {e}", file=sys.stderr)
            sys.exit(1)
    
    def _should_exclude(self, path: Path) -> bool:
        """检查路径是否应该被排除"""
        path_str = str(path)
        if any(part.startswith('.') for part in path.parts):
            return True
        for exclude in self.exclude_paths:
            if exclude in path_str:
                return True
        return False
    
    def _get_files(self) -> List[Path]:
        """获取要搜索的文件列表"""
        files = list(self.base_dir.rglob(self.file_pattern))
        return sorted([f for f in files if not self._should_exclude(f)])
    
    def _extract_title(self, content: str) -> str:
        """提取文档标题"""
        match = self.HEADING_PATTERN.search(content)
        if match:
            return match.group(1).strip()
        return ""
    
    def _is_in_code_block(self, lines: List[str], line_idx: int) -> bool:
        """检查指定行是否在代码块中"""
        in_code = False
        for i, line in enumerate(lines):
            if i > line_idx:
                break
            if self.CODE_BLOCK_START.match(line):
                in_code = not in_code
        return in_code
    
    def _get_context(self, lines: List[str], line_idx: int) -> Tuple[List[str], List[str]]:
        """获取上下文行"""
        start = max(0, line_idx - self.context_lines)
        end = min(len(lines), line_idx + self.context_lines + 1)
        
        before = lines[start:line_idx]
        after = lines[line_idx + 1:end]
        
        return before, after
    
    def _search_in_file(self, file_path: Path) -> Optional[FileResult]:
        """在单个文件中搜索"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                lines = content.split('\n')
        except Exception:
            return None
        
        title = self._extract_title(content)
        matches = []
        
        # 如果只搜索标题
        if self.in_headings:
            for line_num, line in enumerate(lines, 1):
                if self.HEADING_PATTERN.match(line):
                    for match in self.search_pattern.finditer(line):
                        before, after = self._get_context(lines, line_num - 1)
                        matches.append(SearchMatch(
                            file_path=str(file_path.relative_to(self.base_dir)),
                            line_number=line_num,
                            column_start=match.start(),
                            column_end=match.end(),
                            matched_text=match.group(),
                            line_content=line,
                            context_before=before,
                            context_after=after
                        ))
        else:
            # 搜索所有行
            for line_num, line in enumerate(lines, 1):
                # 检查是否在代码块中
                in_code_block = self._is_in_code_block(lines, line_num - 1)
                
                # 根据选项过滤
                if self.in_code and not in_code_block:
                    continue
                if self.exclude_code and in_code_block:
                    continue
                
                for match in self.search_pattern.finditer(line):
                    before, after = self._get_context(lines, line_num - 1)
                    matches.append(SearchMatch(
                        file_path=str(file_path.relative_to(self.base_dir)),
                        line_number=line_num,
                        column_start=match.start(),
                        column_end=match.end(),
                        matched_text=match.group(),
                        line_content=line,
                        context_before=before,
                        context_after=after
                    ))
        
        if matches:
            return FileResult(
                file_path=str(file_path.relative_to(self.base_dir)),
                file_title=title,
                matches=matches,
                match_count=len(matches)
            )
        
        return None
    
    def search(self) -> SearchReport:
        """执行搜索"""
        import time
        start_time = time.time()
        
        self.report.query = self.query
        self.report.search_time = datetime.now().isoformat()
        self.report.base_directory = str(self.base_dir)
        
        # 获取文件列表
        files = self._get_files()
        self.report.total_files_searched = len(files)
        
        # 搜索每个文件
        total_matches = 0
        for file_path in files:
            if total_matches >= self.max_results:
                break
            
            result = self._search_in_file(file_path)
            if result:
                self.report.results.append(result)
                self.report.files_with_matches += 1
                total_matches += result.match_count
        
        self.report.total_matches = total_matches
        self.report.search_duration_ms = (time.time() - start_time) * 1000
        
        return self.report
    
    def print_results(self, use_color: bool = True):
        """打印搜索结果"""
        # ANSI 颜色代码
        RESET = '\033[0m' if use_color else ''
        BOLD = '\033[1m' if use_color else ''
        RED = '\033[91m' if use_color else ''
        GREEN = '\033[92m' if use_color else ''
        YELLOW = '\033[93m' if use_color else ''
        CYAN = '\033[96m' if use_color else ''
        GRAY = '\033[90m' if use_color else ''
        
        print("\n" + "=" * 70)
        print(f"                     搜索结果")
        print("=" * 70)
        print(f"搜索关键词: {BOLD}{self.query}{RESET}")
        print(f"搜索目录: {self.report.base_directory}")
        print(f"搜索文件: {self.report.total_files_searched}")
        print(f"匹配文件: {GREEN}{self.report.files_with_matches}{RESET}")
        print(f"匹配次数: {YELLOW}{self.report.total_matches}{RESET}")
        print(f"耗时: {self.report.search_duration_ms:.2f} ms")
        print("=" * 70)
        
        if not self.report.results:
            print(f"\n{GRAY}未找到匹配项{RESET}")
            return
        
        print()
        for file_result in self.report.results:
            # 打印文件信息
            title_str = f" - {file_result.file_title}" if file_result.file_title else ""
            print(f"\n{CYAN}{file_result.file_path}{RESET}{GRAY}{title_str}{RESET}")
            print(f"{GRAY}{'-' * 70}{RESET}")
            
            # 打印匹配项
            for match in file_result.matches:
                # 上下文前
                for i, ctx_line in enumerate(match.context_before, 1):
                    line_num = match.line_number - len(match.context_before) + i - 1
                    print(f"{GRAY}{line_num:4d} | {ctx_line}{RESET}")
                
                # 匹配行
                highlighted = self._highlight_match(match.line_content, match.matched_text, use_color)
                print(f"{BOLD}{match.line_number:4d}{RESET} | {highlighted}")
                
                # 上下文后
                for i, ctx_line in enumerate(match.context_after, 1):
                    line_num = match.line_number + i
                    print(f"{GRAY}{line_num:4d} | {ctx_line}{RESET}")
                
                print()
        
        print("=" * 70)
    
    def _highlight_match(self, line: str, matched_text: str, use_color: bool) -> str:
        """高亮匹配文本"""
        if not use_color:
            return line
        
        RED = '\033[91m'
        RESET = '\033[0m'
        BOLD = '\033[1m'
        
        # 替换匹配文本为高亮版本
        highlighted = line.replace(
            matched_text,
            f"{BOLD}{RED}{matched_text}{RESET}"
        )
        return highlighted
    
    def save_results(self, output_path: str, format_type: str = 'text'):
        """保存搜索结果"""
        output_path = Path(output_path)
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        if format_type == 'json':
            self._save_json_results(output_path)
        elif format_type == 'html':
            self._save_html_results(output_path)
        else:
            self._save_text_results(output_path)
        
        print(f"\n结果已保存到: {output_path}")
    
    def _save_json_results(self, output_path: Path):
        """保存 JSON 格式结果"""
        report_dict = {
            'metadata': {
                'query': self.report.query,
                'search_time': self.report.search_time,
                'base_directory': self.report.base_directory,
                'total_files_searched': self.report.total_files_searched,
                'files_with_matches': self.report.files_with_matches,
                'total_matches': self.report.total_matches,
                'search_duration_ms': self.report.search_duration_ms,
            },
            'results': [
                {
                    'file_path': r.file_path,
                    'file_title': r.file_title,
                    'match_count': r.match_count,
                    'matches': [
                        {
                            'line_number': m.line_number,
                            'column_start': m.column_start,
                            'column_end': m.column_end,
                            'matched_text': m.matched_text,
                            'line_content': m.line_content,
                            'context_before': m.context_before,
                            'context_after': m.context_after,
                        }
                        for m in r.matches
                    ]
                }
                for r in self.report.results
            ]
        }
        
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(report_dict, f, ensure_ascii=False, indent=2)
    
    def _save_text_results(self, output_path: Path):
        """保存文本格式结果"""
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write("搜索结果\n")
            f.write("=" * 70 + "\n")
            f.write(f"搜索关键词: {self.report.query}\n")
            f.write(f"搜索时间: {self.report.search_time}\n")
            f.write(f"搜索文件: {self.report.total_files_searched}\n")
            f.write(f"匹配文件: {self.report.files_with_matches}\n")
            f.write(f"匹配次数: {self.report.total_matches}\n")
            f.write("=" * 70 + "\n\n")
            
            for file_result in self.report.results:
                f.write(f"\n文件: {file_result.file_path}\n")
                if file_result.file_title:
                    f.write(f"标题: {file_result.file_title}\n")
                f.write("-" * 70 + "\n")
                
                for match in file_result.matches:
                    f.write(f"\n行 {match.line_number}:\n")
                    for ctx_line in match.context_before:
                        f.write(f"  {ctx_line}\n")
                    f.write(f"> {match.line_content}\n")
                    for ctx_line in match.context_after:
                        f.write(f"  {ctx_line}\n")
    
    def _save_html_results(self, output_path: Path):
        """保存 HTML 格式结果"""
        html_content = f"""<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>搜索结果 - {self.report.query}</title>
    <style>
        body {{
            font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;
            max-width: 1200px;
            margin: 0 auto;
            padding: 20px;
            background: #f5f5f5;
            color: #333;
        }}
        .header {{
            background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
            color: white;
            padding: 30px;
            border-radius: 10px;
            margin-bottom: 20px;
        }}
        .stats {{
            display: grid;
            grid-template-columns: repeat(auto-fit, minmax(150px, 1fr));
            gap: 15px;
            margin-bottom: 20px;
        }}
        .stat-card {{
            background: white;
            padding: 20px;
            border-radius: 8px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        }}
        .file-result {{
            background: white;
            padding: 20px;
            border-radius: 8px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
            margin-bottom: 20px;
        }}
        .file-header {{
            border-bottom: 2px solid #eee;
            padding-bottom: 10px;
            margin-bottom: 15px;
        }}
        .file-path {{
            font-size: 18px;
            font-weight: bold;
            color: #667eea;
        }}
        .file-title {{
            color: #666;
            margin-top: 5px;
        }}
        .match {{
            background: #f8f9fa;
            padding: 15px;
            margin: 10px 0;
            border-radius: 5px;
            font-family: 'Consolas', 'Monaco', monospace;
            font-size: 14px;
        }}
        .line-number {{
            color: #999;
            display: inline-block;
            width: 40px;
        }}
        .context {{
            color: #666;
        }}
        .matched-line {{
            background: #fff3cd;
            padding: 2px 5px;
            border-left: 3px solid #ffc107;
        }}
        .highlight {{
            background: #ffeb3b;
            padding: 2px 4px;
            border-radius: 3px;
            font-weight: bold;
        }}
    </style>
</head>
<body>
    <div class="header">
        <h1>🔍 搜索结果</h1>
        <p>搜索关键词: <strong>{self.report.query}</strong></p>
        <p>搜索时间: {self.report.search_time}</p>
    </div>
    
    <div class="stats">
        <div class="stat-card">
            <h3>搜索文件</h3>
            <div class="value">{self.report.total_files_searched}</div>
        </div>
        <div class="stat-card">
            <h3>匹配文件</h3>
            <div class="value">{self.report.files_with_matches}</div>
        </div>
        <div class="stat-card">
            <h3>匹配次数</h3>
            <div class="value">{self.report.total_matches}</div>
        </div>
        <div class="stat-card">
            <h3>耗时</h3>
            <div class="value">{self.report.search_duration_ms:.2f} ms</div>
        </div>
    </div>
"""
        
        for file_result in self.report.results:
            title_display = f"<div class='file-title'>{file_result.file_title}</div>" if file_result.file_title else ""
            html_content += f"""
    <div class="file-result">
        <div class="file-header">
            <div class="file-path">📄 {file_result.file_path}</div>
            {title_display}
        </div>
"""
            for match in file_result.matches:
                html_content += '<div class="match">\n'
                
                # 上下文前
                for i, ctx_line in enumerate(match.context_before):
                    line_num = match.line_number - len(match.context_before) + i
                    html_content += f'<div class="context"><span class="line-number">{line_num:4d}</span> | {ctx_line}</div>\n'
                
                # 匹配行
                escaped_content = match.line_content.replace('<', '&lt;').replace('>', '&gt;')
                highlighted = escaped_content.replace(
                    match.matched_text,
                    f'<span class="highlight">{match.matched_text}</span>'
                )
                html_content += f'<div class="matched-line"><span class="line-number">{match.line_number:4d}</span> | {highlighted}</div>\n'
                
                # 上下文后
                for i, ctx_line in enumerate(match.context_after):
                    line_num = match.line_number + i + 1
                    html_content += f'<div class="context"><span class="line-number">{line_num:4d}</span> | {ctx_line}</div>\n'
                
                html_content += '</div>\n'
            
            html_content += '</div>\n'
        
        html_content += """
</body>
</html>
"""
        
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(html_content)


def main():
    """主函数"""
    parser = argparse.ArgumentParser(
        description='搜索 Markdown 文档内容',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
  %(prog)s "Rust"                     # 搜索关键词
  %(prog)s "pattern.*test" --regex   # 正则搜索
  %(prog)s "设计" --in-headings       # 仅搜索标题
  %(prog)s "函数" -C 3                # 显示3行上下文
  %(prog)s "AI" -o results.html -f html  # 导出HTML结果
        """
    )
    
    parser.add_argument(
        'query',
        help='搜索关键词或正则表达式'
    )
    parser.add_argument(
        '-d', '--directory',
        default='.',
        help='搜索目录（默认: 当前目录）'
    )
    parser.add_argument(
        '--regex',
        action='store_true',
        help='使用正则表达式搜索'
    )
    parser.add_argument(
        '-i', '--ignore-case',
        action='store_true',
        default=True,
        help='忽略大小写（默认）'
    )
    parser.add_argument(
        '-w', '--word-regexp',
        action='store_true',
        help='匹配完整单词'
    )
    parser.add_argument(
        '-C', '--context',
        type=int,
        default=2,
        help='显示上下文行数（默认: 2）'
    )
    parser.add_argument(
        '--in-headings',
        action='store_true',
        help='仅在标题中搜索'
    )
    parser.add_argument(
        '--in-code',
        action='store_true',
        help='仅在代码块中搜索'
    )
    parser.add_argument(
        '--exclude-code',
        action='store_true',
        help='排除代码块'
    )
    parser.add_argument(
        '--file-pattern',
        default='*.md',
        help='文件匹配模式（默认: *.md）'
    )
    parser.add_argument(
        '--max-results',
        type=int,
        default=100,
        help='最大结果数（默认: 100）'
    )
    parser.add_argument(
        '-o', '--output',
        help='输出结果到文件'
    )
    parser.add_argument(
        '-f', '--format',
        choices=['text', 'json', 'html'],
        default='text',
        help='输出格式（默认: text）'
    )
    parser.add_argument(
        '--exclude',
        action='append',
        default=[],
        help='排除特定路径（可多次使用）'
    )
    parser.add_argument(
        '--no-color',
        action='store_true',
        help='禁用彩色输出'
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
    
    # 检查互斥选项
    if args.in_code and args.exclude_code:
        print("错误: --in-code 和 --exclude-code 不能同时使用", file=sys.stderr)
        sys.exit(1)
    
    # 创建搜索器
    searcher = ContentSearcher(
        base_dir=base_dir,
        query=args.query,
        use_regex=args.regex,
        ignore_case=args.ignore_case,
        word_regexp=args.word_regexp,
        context_lines=args.context,
        in_headings=args.in_headings,
        in_code=args.in_code,
        exclude_code=args.exclude_code,
        file_pattern=args.file_pattern,
        max_results=args.max_results,
        exclude_paths=args.exclude
    )
    
    # 执行搜索
    report = searcher.search()
    
    # 打印结果
    searcher.print_results(use_color=not args.no_color and sys.stdout.isatty())
    
    # 保存结果
    if args.output:
        searcher.save_results(args.output, args.format)
    
    # 如果没有找到结果，返回非零退出码
    if report.total_matches == 0:
        sys.exit(1)
    
    sys.exit(0)


if __name__ == '__main__':
    main()
