#!/usr/bin/env python3
"""
批量TOC生成工具
自动为Markdown文档生成并插入目录（Table of Contents）
支持双语格式和多级标题
"""

import os
import re
from pathlib import Path
from typing import List, Dict, Tuple
import json

class TOCGenerator:
    def __init__(self):
        self.toc_pattern = re.compile(r'##\s*目录\s*\|\s*Table of Contents', re.IGNORECASE)
        self.heading_pattern = re.compile(r'^(#{1,6})\s+(.+)$')
        
    def has_toc(self, content: str) -> bool:
        """检查文档是否已有TOC"""
        return bool(self.toc_pattern.search(content))
    
    def extract_headings(self, content: str) -> List[Dict]:
        """提取所有标题"""
        lines = content.split('\n')
        headings = []
        
        for i, line in enumerate(lines, 1):
            match = self.heading_pattern.match(line)
            if match:
                level = len(match.group(1))
                title = match.group(2).strip()
                
                # 跳过TOC标题本身
                if level == 2 and self.toc_pattern.search(line):
                    continue
                
                # 跳过元数据行（如果在文档开头的前10行）
                if i <= 10 and ('版本' in title or '状态' in title or '时间' in title):
                    continue
                
                headings.append({
                    'line': i,
                    'level': level,
                    'title': title,
                    'raw': line
                })
        
        return headings
    
    def generate_anchor(self, title: str) -> str:
        """生成GitHub风格的锚点"""
        # 移除特殊字符，保留中英文、数字、空格、下划线
        anchor = re.sub(r'[^\w\s\u4e00-\u9fff-]', '', title)
        # 转小写
        anchor = anchor.lower()
        # 空格转连字符
        anchor = anchor.replace(' ', '-')
        # 移除多余的连字符
        anchor = re.sub(r'-+', '-', anchor)
        anchor = anchor.strip('-')
        return anchor
    
    def generate_toc_item(self, heading: Dict) -> str:
        """生成单个TOC条目"""
        level = heading['level']
        title = heading['title']
        anchor = self.generate_anchor(title)
        
        # 缩进（level 1 不显示，从level 2开始）
        indent = '  ' * (level - 2) if level >= 2 else ''
        
        # 生成链接
        toc_line = f"{indent}- [{title}](#{anchor})"
        
        return toc_line
    
    def generate_toc(self, headings: List[Dict]) -> str:
        """生成完整的TOC"""
        toc_lines = []
        toc_lines.append("## 目录 | Table of Contents")
        toc_lines.append("")
        
        for heading in headings:
            # 只包含level 1-4的标题
            if heading['level'] <= 4:
                toc_lines.append(self.generate_toc_item(heading))
        
        toc_lines.append("")
        toc_lines.append("---")
        toc_lines.append("")
        
        return '\n'.join(toc_lines)
    
    def insert_toc(self, content: str, toc: str) -> str:
        """在文档中插入TOC"""
        lines = content.split('\n')
        
        # 找到第一个H2标题的位置（主标题H1之后）
        insert_pos = 0
        found_h1 = False
        
        for i, line in enumerate(lines):
            if line.startswith('# ') and not found_h1:
                found_h1 = True
                insert_pos = i + 1
                continue
            
            # 如果已经找到H1，且当前是第一个内容行
            if found_h1 and line.strip() and not line.startswith('---'):
                insert_pos = i
                break
        
        # 如果找不到合适的位置，插入在开头
        if insert_pos == 0:
            insert_pos = 3  # 留出标题和空行
        
        # 插入TOC
        new_lines = lines[:insert_pos] + toc.split('\n') + lines[insert_pos:]
        
        return '\n'.join(new_lines)
    
    def process_file(self, file_path: Path, dry_run: bool = False) -> Dict:
        """处理单个文件"""
        result = {
            'path': str(file_path),
            'status': 'unchanged',
            'message': ''
        }
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # 检查是否已有TOC
            if self.has_toc(content):
                result['status'] = 'skipped'
                result['message'] = '已有TOC'
                return result
            
            # 提取标题
            headings = self.extract_headings(content)
            
            if not headings:
                result['status'] = 'skipped'
                result['message'] = '无标题'
                return result
            
            if len(headings) < 2:
                result['status'] = 'skipped'
                result['message'] = '标题太少'
                return result
            
            # 生成TOC
            toc = self.generate_toc(headings)
            
            # 插入TOC
            new_content = self.insert_toc(content, toc)
            
            # 写入文件（除非是dry run）
            if not dry_run:
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write(new_content)
                result['status'] = 'added'
                result['message'] = f'添加TOC，包含{len(headings)}个标题'
            else:
                result['status'] = 'would_add'
                result['message'] = f'将添加TOC，包含{len(headings)}个标题'
            
            result['heading_count'] = len(headings)
            
        except Exception as e:
            result['status'] = 'error'
            result['message'] = str(e)
        
        return result
    
    def process_directory(self, dir_path: Path, pattern: str = '*.md', 
                          exclude_patterns: List[str] = None, 
                          dry_run: bool = False) -> List[Dict]:
        """批量处理目录"""
        if exclude_patterns is None:
            exclude_patterns = ['README.md', 'GLOSSARY.md', 'FAQ.md', 
                              'LEARNING_PATHS.md', '*REPORT*.md', 
                              '*SUMMARY*.md', '*COMPLETION*.md']
        
        results = []
        
        for md_file in sorted(dir_path.rglob(pattern)):
            # 检查排除规则
            should_exclude = False
            for exclude_pattern in exclude_patterns:
                if '*' in exclude_pattern:
                    # 简单的通配符匹配
                    regex = exclude_pattern.replace('*', '.*')
                    if re.search(regex, md_file.name, re.IGNORECASE):
                        should_exclude = True
                        break
                elif md_file.name == exclude_pattern:
                    should_exclude = True
                    break
            
            if should_exclude:
                continue
            
            result = self.process_file(md_file, dry_run=dry_run)
            results.append(result)
            
            # 打印进度
            status_icon = {
                'added': '✅',
                'would_add': '🔄',
                'skipped': '⏭️',
                'unchanged': '-',
                'error': '❌'
            }.get(result['status'], '?')
            
            print(f"{status_icon} {result['status']:12} {md_file.name:60} {result['message']}")
        
        return results
    
    def generate_report(self, results: List[Dict], output_file: str):
        """生成处理报告"""
        report = []
        report.append("# 批量TOC生成报告\n")
        report.append(f"**生成时间**: {__import__('datetime').datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
        report.append(f"**处理文件数**: {len(results)}\n\n")
        report.append("---\n\n")
        
        # 统计
        status_counts = {}
        for r in results:
            status = r['status']
            status_counts[status] = status_counts.get(status, 0) + 1
        
        report.append("## 📊 处理统计\n\n")
        for status, count in sorted(status_counts.items()):
            icon = {
                'added': '✅ 已添加',
                'would_add': '🔄 将添加',
                'skipped': '⏭️ 已跳过',
                'unchanged': '- 未变化',
                'error': '❌ 错误'
            }.get(status, status)
            report.append(f"- **{icon}**: {count} 个\n")
        report.append("\n")
        
        # 成功添加的文件
        added = [r for r in results if r['status'] in ['added', 'would_add']]
        if added:
            report.append(f"## ✅ 成功处理的文档 ({len(added)}个)\n\n")
            for r in added:
                msg = r.get('message', '')
                report.append(f"- `{r['path']}` - {msg}\n")
            report.append("\n")
        
        # 跳过的文件
        skipped = [r for r in results if r['status'] == 'skipped']
        if skipped:
            report.append(f"## ⏭️ 跳过的文档 ({len(skipped)}个)\n\n")
            for r in skipped:
                msg = r.get('message', '')
                report.append(f"- `{r['path']}` - {msg}\n")
            report.append("\n")
        
        # 错误的文件
        errors = [r for r in results if r['status'] == 'error']
        if errors:
            report.append(f"## ❌ 处理错误 ({len(errors)}个)\n\n")
            for r in errors:
                report.append(f"- `{r['path']}`\n")
                report.append(f"  - 错误: {r['message']}\n")
            report.append("\n")
        
        # 写入文件
        with open(output_file, 'w', encoding='utf-8') as f:
            f.writelines(report)
        
        print(f"\n报告已生成: {output_file}")

def main():
    import argparse
    
    parser = argparse.ArgumentParser(description='批量为Markdown文档生成TOC')
    parser.add_argument('directory', help='要处理的目录')
    parser.add_argument('--dry-run', action='store_true', help='预览模式，不实际修改文件')
    parser.add_argument('--exclude', nargs='+', help='要排除的文件模式', default=[])
    parser.add_argument('--output', default='TOC_GENERATION_REPORT.md', help='报告输出文件')
    
    args = parser.parse_args()
    
    generator = TOCGenerator()
    
    dir_path = Path(args.directory)
    if not dir_path.exists():
        print(f"错误：目录 {dir_path} 不存在")
        return
    
    print(f"{'=' * 80}")
    print(f"批量TOC生成工具")
    print(f"{'=' * 80}")
    print(f"目标目录: {dir_path}")
    print(f"模式: {'预览模式' if args.dry_run else '执行模式'}")
    print(f"{'=' * 80}\n")
    
    # 处理文件
    results = generator.process_directory(dir_path, exclude_patterns=args.exclude, dry_run=args.dry_run)
    
    # 生成报告
    generator.generate_report(results, args.output)
    
    # 总结
    print(f"\n{'=' * 80}")
    print(f"处理完成！")
    print(f"{'=' * 80}")
    added_count = len([r for r in results if r['status'] in ['added', 'would_add']])
    print(f"{'预计' if args.dry_run else '已'}添加TOC: {added_count} 个文档")
    print(f"详细报告: {args.output}")

if __name__ == '__main__':
    main()

