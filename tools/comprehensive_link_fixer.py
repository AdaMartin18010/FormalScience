#!/usr/bin/env python3
"""
R6-A 全面断链修复工具
针对调度系统内部的断链进行批量修复
"""

import os
import re
from pathlib import Path
from collections import defaultdict

# 需要修复的链接映射
LINK_FIXES = {
    # FormalRE 链接 - 文件不存在，需要删除或替换
    '../../FormalRE/调度系统/实时调度核心理论.md': None,  # None 表示删除
    '../../FormalRE/算法复杂度/调度复杂度理论.md': None,
    '../../FormalRE/形式化方法/系统等价理论.md': None,
    '../../FormalRE/硬件/GPU调度模型.md': None,
    '../../FormalRE/硬件/AI加速器调度.md': None,
    '../../FormalRE/操作系统/内存调度理论.md': None,
    '../../FormalRE/操作系统/IO调度理论.md': None,
    '../../FormalRE/分布式系统/大数据调度理论.md': None,
    '../../FormalRE/分布式系统/跨层调度理论.md': None,
    
    # 调度系统内部文件映射 - 文件名变更
    './01.1_调度问题定义.md': './01.1_调度模型抽象.md',
    '../01_调度理论基础/01.1_调度问题定义.md': '../01_调度理论基础/01.1_调度模型抽象.md',
    
    './01.2_调度算法分析.md': './01.2_调度复杂性.md',
    '../01_调度理论基础/01.2_调度算法分析.md': '../01_调度理论基础/01.2_调度复杂性.md',
    
    './01.3_调度等价性.md': './01.3_调度分类学.md',
    '../01_调度理论基础/01.3_调度等价性.md': '../01_调度理论基础/01.3_调度分类学.md',
    
    '../02_硬件调度/02.2_内存调度.md': '../02_硬件调度/02.2_GPU调度.md',
    '../02_硬件调度/02.3_存储调度.md': '../02_硬件调度/02.3_加速器调度.md',
    
    '../03_OS调度/03.2_线程调度.md': '../03_OS调度/03.2_内存调度.md',
    '../03_OS调度/03.3_内存管理.md': '../03_OS调度/03.3_IO调度.md',
    
    '../04_分布式调度/04.2_数据流调度.md': '../04_分布式调度/04.2_大数据调度.md',
}

# 需要删除的链接模式（文件不存在且无替代）
BROKEN_PATTERNS = [
    r'../../FormalRE/.*\.md',
]


class ComprehensiveLinkFixer:
    def __init__(self, base_path):
        self.base_path = Path(base_path).resolve()
        self.all_files = set()
        self.broken_links = []
        self.fixed_links = []
        
    def scan_files(self):
        """扫描所有文件"""
        for f in self.base_path.rglob('*.md'):
            rel = str(f.relative_to(self.base_path)).replace('\\', '/')
            self.all_files.add(rel.lower())
            
    def file_exists(self, path):
        """检查文件是否存在"""
        return path.lower() in self.all_files
        
    def extract_links(self, content):
        """提取所有链接"""
        links = []
        pattern = r'\[([^\]]+)\]\(([^)]+)\)'
        for match in re.finditer(pattern, content):
            text, url = match.groups()
            # 跳过外部链接
            if url.startswith(('http://', 'https://', 'mailto:', 'tel:')):
                continue
            links.append({
                'text': text,
                'url': url,
                'start': match.start(),
                'end': match.end(),
                'full': match.group(0)
            })
        return links
        
    def resolve_link(self, url, current_file):
        """解析链接为相对路径"""
        # 分离锚点
        anchor = ''
        if '#' in url:
            url, anchor = url.split('#', 1)
            anchor = '#' + anchor
            
        if not url:
            return None, anchor
            
        # 解析路径
        current_dir = (self.base_path / current_file).parent
        if url.startswith('/'):
            target = self.base_path / url[1:]
        else:
            target = (current_dir / url).resolve()
            
        try:
            rel = target.relative_to(self.base_path)
            return str(rel).replace('\\', '/'), anchor
        except:
            return None, anchor
            
    def check_file(self, file_path):
        """检查单个文件"""
        try:
            content = file_path.read_text(encoding='utf-8')
            rel_path = str(file_path.relative_to(self.base_path)).replace('\\', '/')
            
            links = self.extract_links(content)
            broken = []
            
            for link in links:
                target_path, anchor = self.resolve_link(link['url'], rel_path)
                if target_path:
                    # 检查是否在修复映射中
                    if link['url'] in LINK_FIXES:
                        fixed_url = LINK_FIXES[link['url']]
                        if fixed_url:
                            broken.append({
                                **link,
                                'file': rel_path,
                                'type': 'fixable',
                                'fix': fixed_url + anchor if fixed_url else None
                            })
                        else:
                            broken.append({
                                **link,
                                'file': rel_path,
                                'type': 'removable'
                            })
                    elif not self.file_exists(target_path):
                        # 检查是否匹配移除模式
                        should_remove = False
                        for pattern in BROKEN_PATTERNS:
                            if re.match(pattern, link['url']):
                                should_remove = True
                                break
                                
                        broken.append({
                            **link,
                            'file': rel_path,
                            'type': 'removable' if should_remove else 'broken'
                        })
                        
            return broken
            
        except Exception as e:
            print(f"Error reading {file_path}: {e}")
            return []
            
    def scan_directory(self, directory):
        """扫描整个目录"""
        dir_path = self.base_path / directory
        if not dir_path.exists():
            return []
            
        all_broken = []
        for f in dir_path.rglob('*.md'):
            broken = self.check_file(f)
            all_broken.extend(broken)
            
        return all_broken
        
    def fix_file(self, file_path, dry_run=True):
        """修复单个文件"""
        try:
            content = file_path.read_text(encoding='utf-8')
            original = content
            rel_path = str(file_path.relative_to(self.base_path)).replace('\\', '/')
            
            changes = []
            
            def replace_link(match):
                text, url = match.groups()
                
                # 检查是否在修复映射中
                if url in LINK_FIXES:
                    fixed = LINK_FIXES[url]
                    if fixed:
                        changes.append({
                            'file': rel_path,
                            'text': text[:30],
                            'old': url,
                            'new': fixed,
                            'action': 'replace'
                        })
                        return f'[{text}]({fixed})'
                    else:
                        changes.append({
                            'file': rel_path,
                            'text': text[:30],
                            'old': url,
                            'new': None,
                            'action': 'remove'
                        })
                        return f'**{text}**'  # 保留文本，移除链接
                        
                # 检查是否匹配移除模式
                for pattern in BROKEN_PATTERNS:
                    if re.match(pattern, url):
                        changes.append({
                            'file': rel_path,
                            'text': text[:30],
                            'old': url,
                            'new': None,
                            'action': 'remove'
                        })
                        return f'**{text}**'
                        
                return match.group(0)
                
            new_content = re.sub(r'\[([^\]]+)\]\(([^)]+)\)', replace_link, content)
            
            if changes and not dry_run:
                file_path.write_text(new_content, encoding='utf-8')
                
            return changes
            
        except Exception as e:
            print(f"Error fixing {file_path}: {e}")
            return []
            
    def fix_directory(self, directory, dry_run=True):
        """修复整个目录"""
        dir_path = self.base_path / directory
        if not dir_path.exists():
            print(f"Directory not found: {directory}")
            return []
            
        all_changes = []
        files = list(dir_path.rglob('*.md'))
        print(f"Processing {len(files)} files in {directory}...")
        
        for f in files:
            changes = self.fix_file(f, dry_run)
            all_changes.extend(changes)
            
        return all_changes
        
    def generate_report(self, changes):
        """生成报告"""
        lines = []
        lines.append("# R6-A 断链修复报告")
        lines.append("")
        lines.append(f"**修复日期**: 2026-04-13")
        lines.append(f"**修复链接数**: {len(changes)}")
        lines.append("")
        
        if not changes:
            lines.append("未发现需要修复的断链。")
            return '\n'.join(lines)
            
        # 统计
        by_action = defaultdict(list)
        for c in changes:
            by_action[c['action']].append(c)
            
        lines.append("## 统计")
        lines.append("")
        for action, items in sorted(by_action.items()):
            lines.append(f"- {action}: {len(items)} 个")
        lines.append("")
        
        # 按文件分组
        by_file = defaultdict(list)
        for c in changes:
            by_file[c['file']].append(c)
            
        lines.append("## 修复详情")
        lines.append("")
        
        for file, file_changes in sorted(by_file.items()):
            lines.append(f"### {file}")
            for c in file_changes:
                if c['action'] == 'replace':
                    lines.append(f"- 替换: `[{c['text']}]` `{c['old']}` → `{c['new']}`")
                elif c['action'] == 'remove':
                    lines.append(f"- 删除: `[{c['text']}]` `{c['old']}`")
            lines.append("")
            
        return '\n'.join(lines)


def main():
    import sys
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    flags = [a for a in sys.argv[1:] if a.startswith('--')]
    
    base_path = args[0] if args else "."
    dry_run = '--apply' not in flags
    
    fixer = ComprehensiveLinkFixer(base_path)
    fixer.scan_files()
    
    print(f"基础路径: {fixer.base_path}")
    print(f"模式: {'干运行 (预览)' if dry_run else '实际修复'}")
    print(f"扫描到 {len(fixer.all_files)} 个文件")
    print("")
    
    # 修复优先级1: 调度系统
    changes = fixer.fix_directory("docs/Refactor/06_调度系统", dry_run)
    
    # 修复优先级2: 网络协议
    if '--p1-only' not in flags:
        changes2 = fixer.fix_directory("docs/Refactor/网络协议", dry_run)
        changes.extend(changes2)
        
    # 生成报告
    report = fixer.generate_report(changes)
    print(report)
    
    # 保存报告
    report_path = Path(base_path) / ".reports" / "r6a_comprehensive_fix_report.md"
    report_path.parent.mkdir(exist_ok=True)
    report_path.write_text(report, encoding='utf-8')
    print(f"\n报告已保存: {report_path}")
    
    if dry_run and changes:
        print(f"\n使用 --apply 参数执行实际修复")
        
    return len(changes)


if __name__ == "__main__":
    exit(main())
