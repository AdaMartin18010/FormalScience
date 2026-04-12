#!/usr/bin/env python3
"""
修复版链接检查工具 - 正确处理Windows路径
"""

import os
import re
import json
from pathlib import Path
from collections import defaultdict
from urllib.parse import urlparse

class LinkCheckerFixed:
    def __init__(self, base_path):
        self.base_path = Path(base_path).resolve()
        self.refactor_path = self.base_path / "docs" / "Refactor"
        self.broken_links = []
        self.valid_links = []
        
    def scan_and_validate(self):
        md_files = list(self.refactor_path.rglob("*.md"))
        print(f"扫描到 {len(md_files)} 个Markdown文件")
        
        for md_file in md_files:
            self._check_file(md_file)
        
        return len(self.broken_links)
    
    def _check_file(self, file_path):
        try:
            content = file_path.read_text(encoding='utf-8')
            lines = content.split('\n')
            
            # 获取从Refactor开始的相对路径，统一使用正斜杠
            try:
                rel_path = file_path.relative_to(self.refactor_path)
                rel_path_str = str(rel_path).replace('\\', '/')
            except ValueError:
                return
            
            for line_num, line in enumerate(lines, 1):
                # 匹配Markdown链接
                pattern = r'\[([^\]]+)\]\(([^\s")]+)(?:\s+"[^"]*")?\)'
                matches = re.finditer(pattern, line)
                
                for match in matches:
                    link_text = match.group(1)
                    link_target = match.group(2)
                    
                    # 跳过锚点链接和URL
                    if link_target.startswith('#') and not link_target.startswith('#/'):
                        continue
                    if link_target.startswith('http://') or link_target.startswith('https://'):
                        continue
                    if link_target.startswith('mailto:'):
                        continue
                    
                    # 检查内部链接
                    self._validate_internal_link(
                        rel_path_str, link_text, link_target, line_num
                    )
                    
        except Exception as e:
            print(f"错误读取 {file_path}: {e}")
    
    def _validate_internal_link(self, source, link_text, target, line_num):
        """验证单个内部链接"""
        # 处理锚点
        if '#' in target:
            target_path, anchor = target.split('#', 1)
        else:
            target_path = target
            anchor = None
        
        # 计算完整目标路径
        if target_path.startswith('/'):
            # 绝对路径（从Refactor根目录）
            full_target = self.refactor_path / target_path.lstrip('/')
        else:
            # 相对路径
            source_dir = self.refactor_path / os.path.dirname(source)
            full_target = source_dir / target_path
        
        # 规范化路径
        full_target = Path(os.path.normpath(str(full_target)))
        
        # 检查文件是否存在
        if not full_target.exists():
            self.broken_links.append({
                "source": source,
                "link_text": link_text[:50],
                "target": target,
                "line": line_num,
                "resolved_path": str(full_target.relative_to(self.base_path)).replace('\\', '/'),
                "reason": "文件不存在"
            })
        else:
            self.valid_links.append({
                "source": source,
                "target": target,
                "line": line_num
            })

    def generate_detailed_report(self):
        """生成详细报告"""
        # 分类统计
        categories = defaultdict(list)
        
        for link in self.broken_links:
            target = link['target']
            
            if 'path/to' in target or 'doc-a' in target or 'doc-b' in target:
                categories['模板占位符'].append(link)
            elif target.startswith('../'):
                categories['父目录引用'].append(link)
            elif './' in target:
                categories['相对路径引用'].append(link)
            else:
                categories['其他'].append(link)
        
        report = {
            "total_files_scanned": len(list(self.refactor_path.rglob("*.md"))),
            "total_broken_links": len(self.broken_links),
            "total_valid_links": len(self.valid_links),
            "categories": {
                k: len(v) for k, v in categories.items()
            },
            "broken_links_sample": self.broken_links[:100],
            "files_with_most_broken": self._get_problem_files()
        }
        
        # 保存报告
        report_path = self.refactor_path / '.reports' / 'link_check_detailed.json'
        report_path.parent.mkdir(parents=True, exist_ok=True)
        with open(report_path, 'w', encoding='utf-8') as f:
            json.dump(report, f, ensure_ascii=False, indent=2)
        
        print(f"\n详细报告已保存: {report_path}")
        
        # 打印摘要
        print("\n" + "="*60)
        print("分类统计")
        print("="*60)
        for cat, count in report['categories'].items():
            print(f"  {cat}: {count}")
        
        return report
    
    def _get_problem_files(self, n=20):
        """获取问题最严重的文件"""
        file_counts = defaultdict(int)
        for link in self.broken_links:
            file_counts[link['source']] += 1
        return sorted(file_counts.items(), key=lambda x: x[1], reverse=True)[:n]

if __name__ == "__main__":
    import sys
    
    script_dir = Path(__file__).parent
    project_root = script_dir.parent
    
    print("="*60)
    print("FormalScience 链接检查（修复版）")
    print("="*60)
    
    checker = LinkCheckerFixed(project_root)
    broken_count = checker.scan_and_validate()
    report = checker.generate_detailed_report()
    
    print("\n" + "="*60)
    print("问题最严重的文件")
    print("="*60)
    for file, count in report['files_with_most_broken']:
        print(f"  {file}: {count} 个无效链接")
    
    print(f"\n总计: {broken_count} 个无效链接 / {report['total_valid_links']} 个有效链接")
    
    sys.exit(0 if broken_count == 0 else 1)
