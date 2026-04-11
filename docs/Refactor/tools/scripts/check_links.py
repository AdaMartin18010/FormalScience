#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
链接检查脚本 (check_links.py)

功能说明:
-----------
该脚本用于检查 Markdown 文档中的内部链接，识别并报告断开的链接，
生成详细的链接质量报告。支持检查以下类型的链接:
- 文档内锚点链接 (#section)
- 相对路径链接 (./file.md, ../file.md)
- 绝对路径链接 (/docs/file.md)

使用方法:
-----------
1. 检查当前目录下的所有 Markdown 文件:
   python check_links.py

2. 检查指定目录:
   python check_links.py -d /path/to/docs

3. 生成 JSON 格式的报告:
   python check_links.py -o report.json -f json

4. 显示详细输出:
   python check_links.py -v

5. 检查外部链接（较慢）:
   python check_links.py --check-external

参数说明:
-----------
-d, --directory    指定要检查的目录（默认: 当前目录）
-o, --output       输出报告文件路径
-f, --format       报告格式: text, json, html（默认: text）
-v, --verbose      显示详细输出
--check-external   同时检查外部 HTTP/HTTPS 链接（耗时较长）
--exclude          排除特定路径（可多次使用）
-h, --help         显示帮助信息

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
from typing import Dict, List, Optional, Set, Tuple
from urllib.parse import urlparse, urljoin


@dataclass
class LinkIssue:
    """表示一个链接问题"""
    file_path: str
    line_number: int
    link_text: str
    link_target: str
    issue_type: str  # 'broken', 'warning', 'external'
    message: str


@dataclass
class LinkReport:
    """链接检查报告"""
    total_files: int = 0
    total_links: int = 0
    valid_links: int = 0
    broken_links: int = 0
    external_links: int = 0
    issues: List[LinkIssue] = field(default_factory=list)
    checked_files: List[str] = field(default_factory=list)
    scan_time: str = ""


class LinkChecker:
    """Markdown 链接检查器"""
    
    # Markdown 链接正则表达式模式
    LINK_PATTERN = re.compile(
        r'\[([^\]]+)\]\(([^)]+)\)',  # [text](url)
        re.MULTILINE
    )
    
    # 锚点链接模式
    ANCHOR_PATTERN = re.compile(r'^#(.+)$')
    
    # 标题锚点生成规则
    HEADING_PATTERN = re.compile(r'^#{1,6}\s+(.+)$', re.MULTILINE)
    
    def __init__(self, base_dir: Path, check_external: bool = False, 
                 exclude_paths: Optional[List[str]] = None):
        """
        初始化链接检查器
        
        Args:
            base_dir: 基础文档目录
            check_external: 是否检查外部链接
            exclude_paths: 要排除的路径列表
        """
        self.base_dir = Path(base_dir).resolve()
        self.check_external = check_external
        self.exclude_paths = exclude_paths or []
        self.report = LinkReport()
        self.file_cache: Dict[str, str] = {}  # 缓存文件内容
        self.anchor_cache: Dict[str, Set[str]] = {}  # 缓存文件锚点
        
    def _should_exclude(self, path: Path) -> bool:
        """检查路径是否应该被排除"""
        path_str = str(path)
        for exclude in self.exclude_paths:
            if exclude in path_str:
                return True
        return False
    
    def _get_markdown_files(self) -> List[Path]:
        """获取所有 Markdown 文件"""
        md_files = []
        for ext in ['*.md', '*.MD', '*.markdown']:
            md_files.extend(self.base_dir.rglob(ext))
        
        # 过滤排除的路径
        md_files = [f for f in md_files if not self._should_exclude(f)]
        return sorted(md_files)
    
    def _load_file(self, file_path: Path) -> str:
        """加载文件内容（带缓存）"""
        str_path = str(file_path)
        if str_path not in self.file_cache:
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    self.file_cache[str_path] = f.read()
            except Exception as e:
                self.file_cache[str_path] = ""
        return self.file_cache[str_path]
    
    def _extract_anchors(self, content: str) -> Set[str]:
        """从内容中提取标题锚点"""
        anchors = set()
        for match in self.HEADING_PATTERN.finditer(content):
            heading = match.group(1).strip()
            # 生成 GitHub 风格的锚点
            anchor = self._generate_anchor(heading)
            anchors.add(anchor)
            anchors.add(heading.lower())
        return anchors
    
    def _generate_anchor(self, heading: str) -> str:
        """生成标题锚点"""
        # GitHub 风格锚点生成
        anchor = heading.lower()
        anchor = re.sub(r'[^\w\s-]', '', anchor)  # 移除特殊字符
        anchor = re.sub(r'\s+', '-', anchor)      # 空格替换为连字符
        anchor = anchor.strip('-')
        return anchor
    
    def _get_file_anchors(self, file_path: Path) -> Set[str]:
        """获取文件的锚点（带缓存）"""
        str_path = str(file_path)
        if str_path not in self.anchor_cache:
            content = self._load_file(file_path)
            self.anchor_cache[str_path] = self._extract_anchors(content)
        return self.anchor_cache[str_path]
    
    def _resolve_link(self, link_target: str, source_file: Path) -> Optional[Path]:
        """
        解析链接目标为实际文件路径
        
        Args:
            link_target: 链接目标字符串
            source_file: 源文件路径
            
        Returns:
            解析后的文件路径，如果无法解析则返回 None
        """
        # 移除锚点部分
        if '#' in link_target:
            link_target = link_target.split('#')[0]
        
        if not link_target:
            return source_file
        
        # 处理绝对路径
        if link_target.startswith('/'):
            target = self.base_dir / link_target.lstrip('/')
        else:
            # 处理相对路径
            target = source_file.parent / link_target
        
        # 尝试添加 .md 扩展名
        if not target.suffix:
            target = target.with_suffix('.md')
        
        return target.resolve() if target.exists() else None
    
    def _check_link(self, link_text: str, link_target: str, 
                    source_file: Path, line_number: int) -> Optional[LinkIssue]:
        """
        检查单个链接
        
        Args:
            link_text: 链接文本
            link_target: 链接目标
            source_file: 源文件路径
            line_number: 行号
            
        Returns:
            如果发现问题则返回 LinkIssue，否则返回 None
        """
        self.report.total_links += 1
        
        # 检查是否是外部链接
        if link_target.startswith(('http://', 'https://')):
            self.report.external_links += 1
            if self.check_external:
                return self._check_external_link(link_text, link_target, 
                                                  source_file, line_number)
            return None
        
        # 检查是否是邮件或特殊链接
        if link_target.startswith(('mailto:', 'tel:', 'javascript:')):
            self.report.valid_links += 1
            return None
        
        # 处理锚点链接
        anchor = None
        if '#' in link_target:
            parts = link_target.split('#', 1)
            link_target = parts[0]
            anchor = parts[1]
        
        # 确定目标文件
        if not link_target:
            # 纯锚点链接，指向当前文件
            target_file = source_file
        else:
            target_file = self._resolve_link(link_target, source_file)
        
        # 检查文件是否存在
        if target_file is None or not target_file.exists():
            self.report.broken_links += 1
            return LinkIssue(
                file_path=str(source_file.relative_to(self.base_dir)),
                line_number=line_number,
                link_text=link_text,
                link_target=link_target or f"#{anchor}" if anchor else "",
                issue_type='broken',
                message=f"目标文件不存在: {link_target}"
            )
        
        # 检查锚点是否存在
        if anchor:
            anchors = self._get_file_anchors(target_file)
            if anchor.lower() not in anchors and anchor not in anchors:
                self.report.broken_links += 1
                return LinkIssue(
                    file_path=str(source_file.relative_to(self.base_dir)),
                    line_number=line_number,
                    link_text=link_text,
                    link_target=link_target + f"#{anchor}",
                    issue_type='broken',
                    message=f"锚点不存在: #{anchor}"
                )
        
        self.report.valid_links += 1
        return None
    
    def _check_external_link(self, link_text: str, link_target: str,
                             source_file: Path, line_number: int) -> Optional[LinkIssue]:
        """检查外部链接（需要网络请求）"""
        try:
            import urllib.request
            import ssl
            
            # 创建 SSL 上下文（忽略证书验证）
            ctx = ssl.create_default_context()
            ctx.check_hostname = False
            ctx.verify_mode = ssl.CERT_NONE
            
            req = urllib.request.Request(
                link_target, 
                headers={'User-Agent': 'Mozilla/5.0 (LinkChecker/1.0)'}
            )
            
            with urllib.request.urlopen(req, timeout=10, context=ctx) as response:
                if response.status >= 400:
                    self.report.broken_links += 1
                    return LinkIssue(
                        file_path=str(source_file.relative_to(self.base_dir)),
                        line_number=line_number,
                        link_text=link_text,
                        link_target=link_target,
                        issue_type='broken',
                        message=f"HTTP {response.status}"
                    )
        except Exception as e:
            self.report.broken_links += 1
            return LinkIssue(
                file_path=str(source_file.relative_to(self.base_dir)),
                line_number=line_number,
                link_text=link_text,
                link_target=link_target,
                issue_type='warning',
                message=f"无法访问: {str(e)}"
            )
        
        self.report.valid_links += 1
        return None
    
    def check_file(self, file_path: Path) -> List[LinkIssue]:
        """
        检查单个文件中的所有链接
        
        Args:
            file_path: Markdown 文件路径
            
        Returns:
            发现的问题列表
        """
        issues = []
        content = self._load_file(file_path)
        lines = content.split('\n')
        
        # 记录文件
        rel_path = str(file_path.relative_to(self.base_dir))
        self.report.checked_files.append(rel_path)
        
        # 遍历每一行查找链接
        for line_num, line in enumerate(lines, 1):
            for match in self.LINK_PATTERN.finditer(line):
                link_text = match.group(1)
                link_target = match.group(2)
                
                issue = self._check_link(link_text, link_target, 
                                        file_path, line_num)
                if issue:
                    issues.append(issue)
        
        return issues
    
    def run(self) -> LinkReport:
        """
        运行链接检查
        
        Returns:
            链接检查报告
        """
        self.report.scan_time = datetime.now().isoformat()
        
        # 获取所有 Markdown 文件
        md_files = self._get_markdown_files()
        self.report.total_files = len(md_files)
        
        # 检查每个文件
        for file_path in md_files:
            issues = self.check_file(file_path)
            self.report.issues.extend(issues)
        
        return self.report
    
    def print_report(self, verbose: bool = False):
        """打印报告到控制台"""
        print("\n" + "=" * 70)
        print("                     链接检查报告")
        print("=" * 70)
        print(f"扫描时间: {self.report.scan_time}")
        print(f"基础目录: {self.base_dir}")
        print("-" * 70)
        print(f"扫描文件数: {self.report.total_files}")
        print(f"总链接数:   {self.report.total_links}")
        print(f"有效链接:   {self.report.valid_links} ({self._percentage(self.report.valid_links)}%)")
        print(f"损坏链接:   {self.report.broken_links} ({self._percentage(self.report.broken_links)}%)")
        print(f"外部链接:   {self.report.external_links}")
        print("=" * 70)
        
        if self.report.issues:
            print("\n发现的问题:")
            print("-" * 70)
            
            # 按文件分组
            issues_by_file: Dict[str, List[LinkIssue]] = {}
            for issue in self.report.issues:
                if issue.file_path not in issues_by_file:
                    issues_by_file[issue.file_path] = []
                issues_by_file[issue.file_path].append(issue)
            
            for file_path, issues in sorted(issues_by_file.items()):
                print(f"\n📄 {file_path}")
                for issue in issues:
                    icon = "❌" if issue.issue_type == 'broken' else "⚠️"
                    print(f"   {icon} 行 {issue.line_number}: [{issue.link_text}]({issue.link_target})")
                    print(f"      原因: {issue.message}")
        else:
            print("\n✅ 未发现链接问题！")
        
        if verbose and self.report.checked_files:
            print("\n" + "=" * 70)
            print("检查的文件列表:")
            for f in sorted(self.report.checked_files):
                print(f"  ✓ {f}")
        
        print("\n" + "=" * 70)
    
    def _percentage(self, value: int) -> float:
        """计算百分比"""
        if self.report.total_links == 0:
            return 0.0
        return round(value * 100 / self.report.total_links, 1)
    
    def save_report(self, output_path: str, format_type: str = 'text'):
        """
        保存报告到文件
        
        Args:
            output_path: 输出文件路径
            format_type: 报告格式 (text, json, html)
        """
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
                'scan_time': self.report.scan_time,
                'base_directory': str(self.base_dir),
                'total_files': self.report.total_files,
            },
            'statistics': {
                'total_links': self.report.total_links,
                'valid_links': self.report.valid_links,
                'broken_links': self.report.broken_links,
                'external_links': self.report.external_links,
            },
            'issues': [asdict(issue) for issue in self.report.issues],
            'checked_files': self.report.checked_files,
        }
        
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(report_dict, f, ensure_ascii=False, indent=2)
    
    def _save_text_report(self, output_path: Path):
        """保存文本格式报告"""
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write("=" * 70 + "\n")
            f.write("                     链接检查报告\n")
            f.write("=" * 70 + "\n")
            f.write(f"扫描时间: {self.report.scan_time}\n")
            f.write(f"基础目录: {self.base_dir}\n")
            f.write("-" * 70 + "\n")
            f.write(f"扫描文件数: {self.report.total_files}\n")
            f.write(f"总链接数:   {self.report.total_links}\n")
            f.write(f"有效链接:   {self.report.valid_links}\n")
            f.write(f"损坏链接:   {self.report.broken_links}\n")
            f.write(f"外部链接:   {self.report.external_links}\n")
            f.write("=" * 70 + "\n\n")
            
            if self.report.issues:
                f.write("发现的问题:\n")
                f.write("-" * 70 + "\n")
                
                issues_by_file: Dict[str, List[LinkIssue]] = {}
                for issue in self.report.issues:
                    if issue.file_path not in issues_by_file:
                        issues_by_file[issue.file_path] = []
                    issues_by_file[issue.file_path].append(issue)
                
                for file_path, issues in sorted(issues_by_file.items()):
                    f.write(f"\n文件: {file_path}\n")
                    for issue in issues:
                        f.write(f"  行 {issue.line_number}: [{issue.link_text}]({issue.link_target})\n")
                        f.write(f"    类型: {issue.issue_type}\n")
                        f.write(f"    原因: {issue.message}\n")
            else:
                f.write("未发现链接问题！\n")
    
    def _save_html_report(self, output_path: Path):
        """保存 HTML 格式报告"""
        html_content = f"""<!DOCTYPE html>
<html lang="zh-CN">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>链接检查报告</title>
    <style>
        body {{
            font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;
            max-width: 1200px;
            margin: 0 auto;
            padding: 20px;
            background: #f5f5f5;
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
            grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));
            gap: 15px;
            margin-bottom: 20px;
        }}
        .stat-card {{
            background: white;
            padding: 20px;
            border-radius: 8px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        }}
        .stat-card h3 {{
            margin: 0 0 10px 0;
            color: #666;
            font-size: 14px;
        }}
        .stat-card .value {{
            font-size: 32px;
            font-weight: bold;
            color: #333;
        }}
        .stat-card.valid .value {{ color: #28a745; }}
        .stat-card.broken .value {{ color: #dc3545; }}
        .issues {{
            background: white;
            padding: 20px;
            border-radius: 8px;
            box-shadow: 0 2px 4px rgba(0,0,0,0.1);
        }}
        .issue {{
            border-left: 4px solid #dc3545;
            padding: 15px;
            margin: 10px 0;
            background: #f8f9fa;
        }}
        .issue.warning {{
            border-left-color: #ffc107;
        }}
        .issue-file {{
            font-weight: bold;
            color: #333;
            margin-bottom: 5px;
        }}
        .issue-details {{
            color: #666;
            font-size: 14px;
        }}
        .success {{
            text-align: center;
            padding: 40px;
            color: #28a745;
        }}
        .success h2 {{
            font-size: 48px;
            margin: 0;
        }}
    </style>
</head>
<body>
    <div class="header">
        <h1>🔗 链接检查报告</h1>
        <p>扫描时间: {self.report.scan_time}</p>
        <p>基础目录: {self.base_dir}</p>
    </div>
    
    <div class="stats">
        <div class="stat-card">
            <h3>扫描文件数</h3>
            <div class="value">{self.report.total_files}</div>
        </div>
        <div class="stat-card">
            <h3>总链接数</h3>
            <div class="value">{self.report.total_links}</div>
        </div>
        <div class="stat-card valid">
            <h3>有效链接</h3>
            <div class="value">{self.report.valid_links}</div>
        </div>
        <div class="stat-card broken">
            <h3>损坏链接</h3>
            <div class="value">{self.report.broken_links}</div>
        </div>
    </div>
"""
        
        if self.report.issues:
            html_content += '    <div class="issues">\n        <h2>发现的问题</h2>\n'
            
            issues_by_file: Dict[str, List[LinkIssue]] = {}
            for issue in self.report.issues:
                if issue.file_path not in issues_by_file:
                    issues_by_file[issue.file_path] = []
                issues_by_file[issue.file_path].append(issue)
            
            for file_path, issues in sorted(issues_by_file.items()):
                for issue in issues:
                    issue_class = 'warning' if issue.issue_type == 'warning' else ''
                    html_content += f"""
        <div class="issue {issue_class}">
            <div class="issue-file">📄 {issue.file_path} (行 {issue.line_number})</div>
            <div class="issue-details">
                <strong>链接:</strong> [{issue.link_text}]({issue.link_target})<br>
                <strong>问题:</strong> {issue.message}
            </div>
        </div>
"""
            html_content += '    </div>\n'
        else:
            html_content += """
    <div class="issues success">
        <h2>✅</h2>
        <h3>未发现链接问题！</h3>
        <p>所有链接检查通过</p>
    </div>
"""
        
        html_content += """
</body>
</html>
"""
        
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(html_content)


def main():
    """主函数"""
    parser = argparse.ArgumentParser(
        description='检查 Markdown 文档中的链接',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
  %(prog)s                           # 检查当前目录
  %(prog)s -d ./docs                 # 检查指定目录
  %(prog)s -o report.json -f json    # 生成 JSON 报告
  %(prog)s -v                        # 显示详细输出
        """
    )
    
    parser.add_argument(
        '-d', '--directory',
        default='.',
        help='要检查的目录（默认: 当前目录）'
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
        '-v', '--verbose',
        action='store_true',
        help='显示详细输出'
    )
    parser.add_argument(
        '--check-external',
        action='store_true',
        help='检查外部 HTTP/HTTPS 链接（耗时较长）'
    )
    parser.add_argument(
        '--exclude',
        action='append',
        default=[],
        help='排除特定路径（可多次使用）'
    )
    
    args = parser.parse_args()
    
    # 检查目录是否存在
    base_dir = Path(args.directory)
    if not base_dir.exists():
        print(f"错误: 目录不存在: {base_dir}", file=sys.stderr)
        sys.exit(1)
    
    if not base_dir.is_dir():
        print(f"错误: 不是目录: {base_dir}", file=sys.stderr)
        sys.exit(1)
    
    # 创建检查器并运行
    checker = LinkChecker(
        base_dir=base_dir,
        check_external=args.check_external,
        exclude_paths=args.exclude
    )
    
    print(f"开始检查链接...")
    print(f"目录: {base_dir.resolve()}")
    
    report = checker.run()
    
    # 打印报告
    checker.print_report(verbose=args.verbose)
    
    # 保存报告
    if args.output:
        checker.save_report(args.output, args.format)
    
    # 如果有损坏的链接，返回非零退出码
    if report.broken_links > 0:
        sys.exit(1)
    
    sys.exit(0)


if __name__ == '__main__':
    main()
