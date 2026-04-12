#!/usr/bin/env python3
"""
修复Composed/schedule_formal_view目录的断链
主要问题：
1. 页内锚点链接格式问题（中文锚点）
2. 指向不存在目录的链接（如../06_调度模型/）
"""

import os
import re
from pathlib import Path
from collections import defaultdict

# 目录映射 - 将错误路径映射到正确路径
DIR_FIXES = {
    '../06_调度模型/': '../06_调度模型/' if False else None,  # 06_调度模型目录可能不存在
    '../03_OS抽象层/': '../03_OS抽象层/' if False else None,
    '../18_编译器调度优化/': '../18_编译器调度优化/' if False else None,
}


class ScheduleFormalViewFixer:
    def __init__(self, base_path):
        self.base_path = Path(base_path).resolve()
        self.all_files = set()
        self.changes = []
        
    def scan_files(self):
        """扫描所有文件"""
        for f in self.base_path.rglob('*.md'):
            rel = str(f.relative_to(self.base_path)).replace('\\', '/')
            self.all_files.add(rel.lower())
            
    def extract_links(self, content):
        """提取所有链接"""
        links = []
        pattern = r'\[([^\]]+)\]\(([^)]+)\)'
        for match in re.finditer(pattern, content):
            text, url = match.groups()
            if url.startswith(('http://', 'https://', 'mailto:', 'tel:')):
                continue
            links.append({
                'text': text,
                'url': url,
                'full': match.group(0),
                'start': match.start(),
                'end': match.end()
            })
        return links
        
    def check_file(self, file_path):
        """检查单个文件"""
        try:
            content = file_path.read_text(encoding='utf-8')
            rel_path = str(file_path.relative_to(self.base_path)).replace('\\', '/')
            
            links = self.extract_links(content)
            issues = []
            
            for link in links:
                url = link['url']
                
                # 检查是否是页内锚点（当前文件的锚点）
                if url.startswith('#'):
                    # 页内锚点，不需要修复
                    continue
                    
                # 分离锚点
                anchor = ''
                if '#' in url:
                    url_part, anchor = url.split('#', 1)
                    anchor = '#' + anchor
                else:
                    url_part = url
                    
                if not url_part:
                    continue
                    
                # 解析路径
                current_dir = (self.base_path / rel_path).parent
                if url_part.startswith('/'):
                    target = self.base_path / url_part[1:]
                else:
                    target = (current_dir / url_part).resolve()
                    
                try:
                    rel_target = str(target.relative_to(self.base_path)).replace('\\', '/')
                    
                    # 检查文件是否存在
                    if not rel_target.lower() in self.all_files:
                        issues.append({
                            **link,
                            'file': rel_path,
                            'resolved': rel_target,
                            'type': 'missing_file'
                        })
                except Exception as e:
                    issues.append({
                        **link,
                        'file': rel_path,
                        'error': str(e),
                        'type': 'resolve_error'
                    })
                    
            return issues
            
        except Exception as e:
            print(f"Error reading {file_path}: {e}")
            return []
            
    def scan_directory(self, directory):
        """扫描目录"""
        dir_path = self.base_path / directory
        if not dir_path.exists():
            return []
            
        all_issues = []
        for f in dir_path.rglob('*.md'):
            issues = self.check_file(f)
            all_issues.extend(issues)
            
        return all_issues
        
    def generate_report(self, issues):
        """生成报告"""
        lines = []
        lines.append("# Composed/schedule_formal_view 断链扫描报告")
        lines.append("")
        lines.append(f"**扫描日期**: 2026-04-13")
        lines.append(f"**断链数量**: {len(issues)}")
        lines.append("")
        
        if not issues:
            lines.append("未发现断链。")
            return '\n'.join(lines)
            
        # 按类型分组
        by_type = defaultdict(list)
        for issue in issues:
            by_type[issue['type']].append(issue)
            
        lines.append("## 统计")
        lines.append("")
        for t, items in sorted(by_type.items()):
            lines.append(f"- {t}: {len(items)} 个")
        lines.append("")
        
        # 按文件分组
        by_file = defaultdict(list)
        for issue in issues:
            by_file[issue['file']].append(issue)
            
        lines.append("## 断链详情（前50个）")
        lines.append("")
        
        count = 0
        for file, file_issues in sorted(by_file.items()):
            lines.append(f"### {file}")
            for issue in file_issues:
                if count >= 50:
                    lines.append("- ... (更多断链省略)")
                    break
                if issue['type'] == 'missing_file':
                    lines.append(f"- `[{issue['text'][:30]}]` → `{issue['url']}` (文件不存在: {issue.get('resolved', 'N/A')})")
                else:
                    lines.append(f"- `[{issue['text'][:30]}]` → `{issue['url']}` (错误: {issue.get('error', 'N/A')})")
                count += 1
            if count >= 50:
                break
            lines.append("")
            
        return '\n'.join(lines)


def main():
    import sys
    base_path = sys.argv[1] if len(sys.argv) > 1 else "."
    
    fixer = ScheduleFormalViewFixer(base_path)
    fixer.scan_files()
    
    print(f"基础路径: {fixer.base_path}")
    print(f"扫描到 {len(fixer.all_files)} 个文件")
    print("")
    
    # 扫描 schedule_formal_view
    issues = fixer.scan_directory("Composed/schedule_formal_view")
    
    # 生成报告
    report = fixer.generate_report(issues)
    print(report)
    
    # 保存报告
    report_path = Path(base_path) / ".reports" / "schedule_formal_view_issues.md"
    report_path.parent.mkdir(exist_ok=True)
    report_path.write_text(report, encoding='utf-8')
    print(f"\n报告已保存: {report_path}")
    
    return len(issues)


if __name__ == "__main__":
    exit(main())
