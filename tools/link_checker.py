#!/usr/bin/env python3
"""
断链扫描器 - 扫描Markdown文件中的断链
"""

import os
import re
import sys
from pathlib import Path
from collections import defaultdict
from urllib.parse import urlparse, unquote

class LinkChecker:
    def __init__(self, base_path):
        self.base_path = Path(base_path).resolve()
        self.all_files = set()
        self.all_anchors = defaultdict(set)  # file -> set of anchors
        self.broken_links = []
        self.total_links = 0
        
    def collect_all_files(self):
        """收集所有Markdown文件和它们的路径"""
        for ext in ['.md', '.markdown']:
            for f in self.base_path.rglob(f'*{ext}'):
                rel_path = f.relative_to(self.base_path)
                self.all_files.add(str(rel_path).replace('\\', '/'))
                self.all_files.add(str(rel_path).lower().replace('\\', '/'))
                
    def extract_anchors(self, content, file_path):
        """提取文件中的所有锚点"""
        # 标题锚点
        header_pattern = r'^#{1,6}\s+(.+)$'
        for match in re.finditer(header_pattern, content, re.MULTILINE):
            title = match.group(1).strip()
            anchor = self._title_to_anchor(title)
            self.all_anchors[str(file_path)].add(anchor)
            
        # HTML锚点
        anchor_pattern = r'<a[^>]+name=["\']([^"\']+)["\']'
        for match in re.finditer(anchor_pattern, content):
            self.all_anchors[str(file_path)].add(match.group(1))
            
        # 自定义锚点
        custom_anchor_pattern = r'\{#[\w-]+\}'
        for match in re.finditer(custom_anchor_pattern, content):
            anchor = match.group(0)[2:-1]  # 去掉 {# 和 }
            self.all_anchors[str(file_path)].add(anchor)
            
    def _title_to_anchor(self, title):
        """将标题转换为锚点"""
        # 移除Markdown标记
        title = re.sub(r'\[([^\]]+)\]\([^)]+\)', r'\1', title)
        title = re.sub(r'[#*_`]', '', title)
        # GitHub风格的锚点转换
        anchor = title.lower().strip()
        anchor = re.sub(r'[^\w\s-]', '', anchor)
        anchor = re.sub(r'\s+', '-', anchor)
        return anchor
        
    def extract_links(self, content):
        """提取所有Markdown链接"""
        links = []
        
        # Markdown链接 [text](url)
        md_pattern = r'\[([^\]]+)\]\(([^)]+)\)'
        for match in re.finditer(md_pattern, content):
            text, url = match.groups()
            if not url.startswith(('http://', 'https://', 'mailto:', 'tel:')):
                links.append({
                    'type': 'markdown',
                    'text': text,
                    'url': url,
                    'pos': match.start()
                })
                
        # 图片链接 ![alt](url)
        img_pattern = r'!\[([^\]]*)\]\(([^)]+)\)'
        for match in re.finditer(img_pattern, content):
            alt, url = match.groups()
            if not url.startswith(('http://', 'https://', 'data:')):
                links.append({
                    'type': 'image',
                    'text': alt,
                    'url': url,
                    'pos': match.start()
                })
                
        # HTML链接 <a href="url">
        html_pattern = r'<a[^>]+href=["\']([^"\']+)["\'][^>]*>'
        for match in re.finditer(html_pattern, content):
            url = match.group(1)
            if not url.startswith(('http://', 'https://', 'mailto:', 'tel:', '#')):
                links.append({
                    'type': 'html',
                    'text': '',
                    'url': url,
                    'pos': match.start()
                })
                
        return links
        
    def resolve_link(self, link_url, current_file):
        """解析链接为目标文件路径和锚点"""
        if link_url.startswith('#'):
            # 页内锚点
            target_file = str(current_file)
            anchor = link_url[1:]
        elif '#' in link_url:
            # 文件+锚点
            parts = link_url.split('#', 1)
            target_file = parts[0]
            anchor = parts[1]
        else:
            target_file = link_url
            anchor = None
            
        # 解析路径
        if target_file.startswith('/'):
            # 绝对路径
            resolved = self.base_path / target_file[1:]
        else:
            # 相对路径
            current_dir = (self.base_path / current_file).parent
            resolved = current_dir / target_file
            
        rel_path = resolved.relative_to(self.base_path)
        rel_path_str = str(rel_path).replace('\\', '/')
        
        return rel_path_str, anchor
        
    def check_link(self, link, current_file):
        """检查单个链接是否有效"""
        try:
            target_file, anchor = self.resolve_link(link['url'], current_file)
            
            # 检查文件是否存在
            target_file_lower = target_file.lower()
            file_exists = (target_file in self.all_files or 
                          target_file_lower in self.all_files)
            
            if not file_exists:
                # 尝试添加.md后缀
                if not target_file.endswith('.md'):
                    target_file_md = target_file + '.md'
                    target_file_md_lower = target_file_lower + '.md'
                    if (target_file_md in self.all_files or 
                        target_file_md_lower in self.all_files):
                        file_exists = True
                        target_file = target_file_md
                        
            if not file_exists:
                return False, f"文件不存在: {target_file}"
                
            # 检查锚点
            if anchor:
                target_anchors = self.all_anchors.get(target_file, set())
                if anchor not in target_anchors:
                    # 尝试查找类似锚点
                    anchor_lower = anchor.lower()
                    for a in target_anchors:
                        if a.lower() == anchor_lower:
                            return True, None
                    return False, f"锚点不存在: #{anchor}"
                    
            return True, None
            
        except Exception as e:
            return False, f"解析错误: {e}"
            
    def check_file(self, file_path):
        """检查单个文件中的所有链接"""
        try:
            content = file_path.read_text(encoding='utf-8')
            rel_path = file_path.relative_to(self.base_path)
            
            # 提取锚点
            self.extract_anchors(content, rel_path)
            
            # 提取并检查链接
            links = self.extract_links(content)
            self.total_links += len(links)
            
            for link in links:
                is_valid, error = self.check_link(link, rel_path)
                if not is_valid:
                    self.broken_links.append({
                        'file': str(rel_path).replace('\\', '/'),
                        'link_text': link['text'][:50] if link['text'] else '',
                        'url': link['url'],
                        'type': link['type'],
                        'error': error
                    })
                    
        except Exception as e:
            print(f"Error reading {file_path}: {e}")
            
    def check_all(self, target_dirs=None):
        """检查所有文件或指定目录"""
        self.collect_all_files()
        
        # 第一阶段：收集所有锚点
        if target_dirs:
            for target_dir in target_dirs:
                dir_path = self.base_path / target_dir
                if dir_path.exists():
                    for f in dir_path.rglob('*.md'):
                        try:
                            content = f.read_text(encoding='utf-8')
                            rel_path = f.relative_to(self.base_path)
                            self.extract_anchors(content, rel_path)
                        except:
                            pass
        else:
            for f in self.base_path.rglob('*.md'):
                try:
                    content = f.read_text(encoding='utf-8')
                    rel_path = f.relative_to(self.base_path)
                    self.extract_anchors(content, rel_path)
                except:
                    pass
                    
        # 第二阶段：检查链接
        if target_dirs:
            for target_dir in target_dirs:
                dir_path = self.base_path / target_dir
                if dir_path.exists():
                    for f in dir_path.rglob('*.md'):
                        self.check_file(f)
        else:
            for f in self.base_path.rglob('*.md'):
                self.check_file(f)
                
    def get_report(self, priority_dirs=None):
        """生成报告"""
        lines = []
        lines.append("=" * 80)
        lines.append("断链扫描报告")
        lines.append("=" * 80)
        lines.append(f"扫描时间: {os.popen('date /t').read().strip() if os.name == 'nt' else os.popen('date').read().strip()}")
        lines.append(f"基础路径: {self.base_path}")
        lines.append(f"总文件数: {len(self.all_files)}")
        lines.append(f"总链接数: {self.total_links}")
        lines.append(f"断链数: {len(self.broken_links)}")
        lines.append("")
        
        if priority_dirs:
            # 按优先级分组
            priority_links = defaultdict(list)
            other_links = []
            
            for link in self.broken_links:
                in_priority = False
                for i, pdir in enumerate(priority_dirs, 1):
                    if link['file'].startswith(pdir):
                        priority_links[f"优先级{i}"].append(link)
                        in_priority = True
                        break
                if not in_priority:
                    other_links.append(link)
                    
            for priority in sorted(priority_links.keys()):
                links = priority_links[priority]
                lines.append(f"\n{'=' * 80}")
                lines.append(f"{priority}: {len(links)}个断链")
                lines.append('=' * 80)
                
                # 按文件分组
                by_file = defaultdict(list)
                for link in links:
                    by_file[link['file']].append(link)
                    
                for file, file_links in sorted(by_file.items()):
                    lines.append(f"\n  文件: {file}")
                    for link in file_links:
                        lines.append(f"    - [{link['link_text']}] → {link['url']}")
                        lines.append(f"      错误: {link['error']}")
                        
            if other_links:
                lines.append(f"\n{'=' * 80}")
                lines.append(f"其他: {len(other_links)}个断链")
                lines.append('=' * 80)
                by_file = defaultdict(list)
                for link in other_links:
                    by_file[link['file']].append(link)
                for file, file_links in sorted(by_file.items())[:20]:  # 限制显示
                    lines.append(f"\n  文件: {file}")
                    for link in file_links[:5]:  # 限制每个文件的链接数
                        lines.append(f"    - [{link['link_text']}] → {link['url']}")
                        lines.append(f"      错误: {link['error']}")
                        
        else:
            # 简单列表
            by_file = defaultdict(list)
            for link in self.broken_links:
                by_file[link['file']].append(link)
                
            for file, file_links in sorted(by_file.items()):
                lines.append(f"\n文件: {file}")
                for link in file_links:
                    lines.append(f"  - [{link['link_text']}] → {link['url']}")
                    lines.append(f"    错误: {link['error']}")
                    
        return '\n'.join(lines)


def main():
    base_path = sys.argv[1] if len(sys.argv) > 1 else "."
    
    # 优先级目录
    priority_dirs = [
        "docs/Refactor/06_调度系统",
        "Composed/schedule_formal_view",
        "docs/Refactor/网络协议",
        "docs/Refactor/RFC标准",
        "docs/Refactor/01_数学基础",
        "docs/Refactor/05_形式化理论",
    ]
    
    checker = LinkChecker(base_path)
    checker.check_all(priority_dirs)
    
    report = checker.get_report(priority_dirs)
    print(report)
    
    # 保存报告
    report_path = Path(base_path) / ".reports" / "link_check_report_r6a.md"
    report_path.parent.mkdir(exist_ok=True)
    report_path.write_text(report, encoding='utf-8')
    print(f"\n\n报告已保存至: {report_path}")
    
    # 返回断链数量用于脚本判断
    return len(checker.broken_links)


if __name__ == "__main__":
    exit(main())
