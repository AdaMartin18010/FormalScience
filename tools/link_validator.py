#!/usr/bin/env python3
"""
Formal Science Link Validator
自动检查项目文档中的所有链接

Usage:
    python tools/link_validator.py
    python tools/link_validator.py --dir Concept/
    python tools/link_validator.py --fix (自动修复简单问题)
"""

import re
from pathlib import Path
from typing import List, Tuple, Dict, Optional
from dataclasses import dataclass
import argparse
import sys

try:
    from rich.console import Console
    from rich.table import Table
    from rich.progress import track
    HAS_RICH = True
except ImportError:
    HAS_RICH = False
    print("提示: 安装 rich 库可获得更好的显示效果: pip install rich")


@dataclass
class LinkIssue:
    """链接问题数据类"""
    file: Path
    line: int
    link_text: str
    link_url: str
    issue_type: str
    fix_suggestion: str = ""


class LinkValidator:
    """链接验证器"""
    
    def __init__(self, root_dir: Path, console=None):
        self.root_dir = root_dir
        self.console = console if console else self._create_console()
        self.issues: List[LinkIssue] = []
        
        # 链接模式
        self.link_pattern = re.compile(r'\[([^\]]+)\]\(([^\)]+)\)')
        
        # 标题模式（用于生成锚点）
        self.header_pattern = re.compile(r'^(#{1,6})\s+(.+)$', re.MULTILINE)
    
    def _create_console(self):
        """创建控制台对象"""
        if HAS_RICH:
            return Console()
        else:
            # 简单的控制台类
            class SimpleConsole:
                def print(self, *args, **kwargs):
                    print(*args)
            return SimpleConsole()
    
    def find_markdown_files(self) -> List[Path]:
        """查找所有markdown文件"""
        files = list(self.root_dir.rglob("*.md"))
        # 排除一些特殊目录
        exclude_dirs = {'.git', 'node_modules', '__pycache__'}
        files = [f for f in files if not any(e in f.parts for e in exclude_dirs)]
        return sorted(files)
    
    def extract_links(self, file: Path) -> List[Tuple[int, str, str]]:
        """
        提取文件中的所有链接
        返回: [(行号, 链接文本, 链接URL), ...]
        """
        links = []
        
        try:
            with open(file, 'r', encoding='utf-8') as f:
                for line_num, line in enumerate(f, 1):
                    for match in self.link_pattern.finditer(line):
                        link_text = match.group(1)
                        link_url = match.group(2)
                        links.append((line_num, link_text, link_url))
        except Exception as e:
            self.console.print(f"[red]错误: 无法读取文件 {file}: {e}[/red]")
        
        return links
    
    def validate_internal_link(self, source_file: Path, link_url: str) -> Tuple[bool, str]:
        """
        验证内部链接
        返回: (是否有效, 错误原因)
        """
        # 去除URL参数和片段
        if '#' in link_url:
            file_part, anchor = link_url.split('#', 1)
        else:
            file_part = link_url
            anchor = None
        
        if not file_part:
            # 纯锚点链接 #section (指向当前文件)
            return self.validate_anchor(source_file, anchor)
        
        # 解析相对路径
        if file_part.startswith('/'):
            # 绝对路径（从根目录）
            target_file = self.root_dir / file_part.lstrip('/')
        else:
            # 相对路径
            target_file = (source_file.parent / file_part).resolve()
        
        # 检查文件是否存在
        if not target_file.exists():
            return False, f"文件不存在: {file_part}"
        
        # 如果有锚点，验证锚点
        if anchor:
            valid, reason = self.validate_anchor(target_file, anchor)
            if not valid:
                return False, f"锚点无效: #{anchor}"
        
        return True, ""
    
    def validate_anchor(self, file: Path, anchor: str) -> Tuple[bool, str]:
        """
        验证锚点是否存在
        返回: (是否有效, 错误原因)
        """
        if not file.exists():
            return False, "文件不存在"
        
        try:
            with open(file, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            return False, f"无法读取文件: {e}"
        
        # 提取所有标题并转换为锚点
        headers = self.header_pattern.findall(content)
        valid_anchors = [self.title_to_anchor(title) for _, title in headers]
        
        # 同时检查原始锚点和小写版本
        anchor_lower = anchor.lower()
        if anchor in valid_anchors or anchor_lower in valid_anchors:
            return True, ""
        
        # 查找最相似的锚点（建议）
        similar = self._find_similar_anchor(anchor_lower, valid_anchors)
        if similar:
            return False, f"未找到锚点，是否想要: #{similar}"
        
        return False, "未找到对应的标题锚点"
    
    def title_to_anchor(self, title: str) -> str:
        """
        标题转锚点
        示例: "Hello World" -> "hello-world"
              "第一章 引言" -> "第一章-引言"
        """
        # 移除emoji和特殊符号
        # 保留中英文字符、数字、空格、连字符
        cleaned = re.sub(r'[^\w\s\u4e00-\u9fff-]', '', title)
        
        # 转小写，空格和多个连字符替换为单个连字符
        anchor = cleaned.strip().lower()
        anchor = re.sub(r'[\s_]+', '-', anchor)
        anchor = re.sub(r'-+', '-', anchor)
        
        return anchor.strip('-')
    
    def _find_similar_anchor(self, anchor: str, valid_anchors: List[str]) -> Optional[str]:
        """查找最相似的锚点（简单实现）"""
        # 简单的相似度：检查是否包含相同的关键词
        anchor_words = set(anchor.split('-'))
        
        best_match = None
        best_score = 0
        
        for valid in valid_anchors:
            valid_words = set(valid.split('-'))
            common = len(anchor_words & valid_words)
            if common > best_score:
                best_score = common
                best_match = valid
        
        return best_match if best_score > 0 else None
    
    def validate_all(self) -> Dict:
        """执行全面验证"""
        files = self.find_markdown_files()
        total_links = 0
        valid_links = 0
        
        if HAS_RICH:
            file_iter = track(files, description="扫描文件中...")
        else:
            file_iter = files
            print(f"扫描 {len(files)} 个文件...")
        
        for file in file_iter:
            links = self.extract_links(file)
            total_links += len(links)
            
            for line_num, link_text, link_url in links:
                # 跳过外部链接（http/https）
                if link_url.startswith(('http://', 'https://', 'mailto:', 'javascript:', 'ftp:')):
                    valid_links += 1
                    continue
                
                # 跳过图片链接（可选）
                if link_url.endswith(('.png', '.jpg', '.jpeg', '.gif', '.svg', '.webp')):
                    valid_links += 1
                    continue
                
                # 验证内部链接
                is_valid, reason = self.validate_internal_link(file, link_url)
                
                if is_valid:
                    valid_links += 1
                else:
                    self.issues.append(LinkIssue(
                        file=file,
                        line=line_num,
                        link_text=link_text,
                        link_url=link_url,
                        issue_type="broken_link",
                        fix_suggestion=reason
                    ))
        
        return {
            'total_files': len(files),
            'total_links': total_links,
            'valid_links': valid_links,
            'broken_links': len(self.issues)
        }
    
    def print_report(self, stats: Dict):
        """打印美化报告"""
        if HAS_RICH:
            self._print_rich_report(stats)
        else:
            self._print_simple_report(stats)
    
    def _print_rich_report(self, stats: Dict):
        """使用rich库打印美化报告"""
        self.console.print("\n[bold cyan]═══════════════════════════════════════[/bold cyan]")
        self.console.print("[bold cyan]        链接验证报告           [/bold cyan]")
        self.console.print("[bold cyan]═══════════════════════════════════════[/bold cyan]\n")
        
        self.console.print(f"📁 扫描文件: [bold]{stats['total_files']}[/bold]")
        self.console.print(f"🔗 总链接数: [bold]{stats['total_links']}[/bold]")
        self.console.print(f"✅ 有效链接: [bold green]{stats['valid_links']}[/bold green]")
        self.console.print(f"❌ 失效链接: [bold red]{stats['broken_links']}[/bold red]")
        
        if stats['total_links'] > 0:
            success_rate = stats['valid_links'] / stats['total_links'] * 100
            self.console.print(f"📊 成功率: [bold]{success_rate:.1f}%[/bold]")
        
        if self.issues:
            self.console.print(f"\n[bold red]发现 {len(self.issues)} 个失效链接:[/bold red]\n")
            
            # 按文件分组
            issues_by_file = {}
            for issue in self.issues:
                rel_path = issue.file.relative_to(self.root_dir)
                if rel_path not in issues_by_file:
                    issues_by_file[rel_path] = []
                issues_by_file[rel_path].append(issue)
            
            # 打印每个文件的问题
            for file_path, file_issues in sorted(issues_by_file.items())[:10]:  # 只显示前10个文件
                self.console.print(f"[cyan]📄 {file_path}[/cyan]")
                
                for issue in file_issues[:5]:  # 每个文件最多显示5个问题
                    self.console.print(f"  [yellow]第{issue.line}行[/yellow]: [{issue.link_text[:40]}]")
                    self.console.print(f"    [red]✗[/red] {issue.link_url}")
                    if issue.fix_suggestion:
                        self.console.print(f"    [dim]💡 {issue.fix_suggestion}[/dim]")
                
                if len(file_issues) > 5:
                    self.console.print(f"  [dim]... 还有 {len(file_issues) - 5} 个问题[/dim]")
                self.console.print()
            
            if len(issues_by_file) > 10:
                self.console.print(f"[dim]... 还有 {len(issues_by_file) - 10} 个文件有问题[/dim]\n")
        else:
            self.console.print("\n[bold green]🎉 所有链接都有效！文档质量优秀！[/bold green]\n")
    
    def _print_simple_report(self, stats: Dict):
        """简单文本报告（无rich库）"""
        print("\n" + "=" * 50)
        print("           链接验证报告")
        print("=" * 50 + "\n")
        
        print(f"扫描文件: {stats['total_files']}")
        print(f"总链接数: {stats['total_links']}")
        print(f"有效链接: {stats['valid_links']} ✓")
        print(f"失效链接: {stats['broken_links']} ✗")
        
        if stats['total_links'] > 0:
            success_rate = stats['valid_links'] / stats['total_links'] * 100
            print(f"成功率: {success_rate:.1f}%")
        
        if self.issues:
            print(f"\n发现 {len(self.issues)} 个失效链接:\n")
            
            for i, issue in enumerate(self.issues[:20], 1):  # 只显示前20个
                rel_path = issue.file.relative_to(self.root_dir)
                print(f"{i}. {rel_path} (第{issue.line}行)")
                print(f"   链接: [{issue.link_text[:40]}]({issue.link_url})")
                if issue.fix_suggestion:
                    print(f"   建议: {issue.fix_suggestion}")
                print()
            
            if len(self.issues) > 20:
                print(f"... 还有 {len(self.issues) - 20} 个问题\n")
        else:
            print("\n所有链接都有效！\n")
    
    def save_detailed_report(self, output_file: Path):
        """保存详细报告到文件"""
        with open(output_file, 'w', encoding='utf-8') as f:
            f.write("# 链接验证详细报告\n\n")
            f.write(f"**生成时间**: {self._get_timestamp()}\n\n")
            f.write("## 统计摘要\n\n")
            f.write(f"- 扫描文件数: {len(self.find_markdown_files())}\n")
            f.write(f"- 失效链接数: {len(self.issues)}\n\n")
            
            if self.issues:
                f.write("## 失效链接详情\n\n")
                
                # 按文件分组
                issues_by_file = {}
                for issue in self.issues:
                    rel_path = issue.file.relative_to(self.root_dir)
                    if rel_path not in issues_by_file:
                        issues_by_file[rel_path] = []
                    issues_by_file[rel_path].append(issue)
                
                for file_path, file_issues in sorted(issues_by_file.items()):
                    f.write(f"### {file_path}\n\n")
                    
                    for issue in file_issues:
                        f.write(f"**第{issue.line}行**:\n")
                        f.write(f"- 链接文本: `{issue.link_text}`\n")
                        f.write(f"- 链接URL: `{issue.link_url}`\n")
                        f.write(f"- 问题类型: {issue.issue_type}\n")
                        if issue.fix_suggestion:
                            f.write(f"- 修复建议: {issue.fix_suggestion}\n")
                        f.write("\n")
            else:
                f.write("✅ 所有链接都有效！\n")
        
        print(f"\n详细报告已保存到: {output_file}")
    
    @staticmethod
    def _get_timestamp():
        """获取当前时间戳"""
        from datetime import datetime
        return datetime.now().strftime("%Y-%m-%d %H:%M:%S")


def main():
    parser = argparse.ArgumentParser(
        description="验证Formal Science项目文档中的所有链接",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例用法:
  python tools/link_validator.py                    # 验证Concept/目录
  python tools/link_validator.py --dir docs/        # 验证docs/目录
  python tools/link_validator.py --report report.md # 保存详细报告
        """
    )
    
    parser.add_argument(
        '--dir',
        type=Path,
        default=Path('Concept'),
        help='要扫描的目录 (默认: Concept/)'
    )
    
    parser.add_argument(
        '--report',
        type=Path,
        help='保存详细报告的文件路径 (可选)'
    )
    
    args = parser.parse_args()
    
    # 检查目录是否存在
    if not args.dir.exists():
        print(f"错误: 目录不存在: {args.dir}")
        sys.exit(1)
    
    # 创建验证器
    console = Console() if HAS_RICH else None
    validator = LinkValidator(args.dir, console)
    
    # 执行验证
    if console:
        console.print("[bold]开始验证链接...[/bold]\n")
    else:
        print("开始验证链接...\n")
    
    stats = validator.validate_all()
    
    # 打印报告
    validator.print_report(stats)
    
    # 保存详细报告（如果指定）
    if args.report:
        validator.save_detailed_report(args.report)
    
    # 返回退出码（有失效链接时返回1）
    sys.exit(0 if stats['broken_links'] == 0 else 1)


if __name__ == "__main__":
    main()

