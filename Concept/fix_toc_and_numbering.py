#!/usr/bin/env python3
"""
修复 Markdown 文件的目录和序号问题
- 自动生成缺失的目录
- 修复主题与子主题序号不一致的问题
"""

import os
import re
from pathlib import Path
from typing import List, Tuple, Optional

class MarkdownTOCFixer:
    def __init__(self, base_path: str):
        self.base_path = Path(base_path)
        self.issues = []
        self.fixed = []
        
    def extract_headings(self, content: str) -> List[Tuple[int, str, str]]:
        """提取所有标题 (level, text, anchor)"""
        headings = []
        lines = content.split('\n')
        
        for line in lines:
            # 跳过代码块中的内容
            if line.strip().startswith('```'):
                continue
                
            match = re.match(r'^(#{1,6})\s+(.+)$', line)
            if match:
                level = len(match.group(1))
                text = match.group(2).strip()
                # 移除可能的 emoji 和特殊字符，生成 anchor
                anchor = self.generate_anchor(text)
                headings.append((level, text, anchor))
        
        return headings
    
    def generate_anchor(self, text: str) -> str:
        """生成 GitHub 风格的 anchor"""
        # 移除特殊字符，保留中英文、数字、空格、下划线
        text = re.sub(r'[^\w\s\u4e00-\u9fff_-]', '', text)
        # 转换为小写，空格替换为连字符
        anchor = text.lower().replace(' ', '-').replace('_', '-')
        # 移除多余的连字符
        anchor = re.sub(r'-+', '-', anchor)
        return anchor.strip('-')
    
    def find_toc_section(self, content: str) -> Optional[Tuple[int, int]]:
        """查找现有的目录部分 (start_line, end_line)"""
        lines = content.split('\n')
        
        # 常见的目录标题模式
        toc_patterns = [
            r'^##\s*📋\s*目录',
            r'^##\s*目录',
            r'^##\s*Table of Contents',
            r'^##\s*📖\s*目录',
            r'^<details>.*目录.*</details>',
        ]
        
        start_line = None
        for i, line in enumerate(lines):
            for pattern in toc_patterns:
                if re.search(pattern, line, re.IGNORECASE):
                    start_line = i
                    break
            if start_line is not None:
                break
        
        if start_line is None:
            return None
        
        # 查找目录结束位置（下一个非列表行或下一个 ## 标题）
        end_line = start_line + 1
        for i in range(start_line + 1, len(lines)):
            line = lines[i].strip()
            # 遇到下一个主标题或分隔符，目录结束
            if line.startswith('##') and not line.startswith('###'):
                end_line = i
                break
            if line.startswith('---') and i > start_line + 2:
                end_line = i
                break
            if line.startswith('<details>') or line.startswith('</details>'):
                end_line = i + 1
                break
        
        return (start_line, end_line)
    
    def generate_toc(self, headings: List[Tuple[int, str, str]], 
                     skip_first: bool = True) -> str:
        """生成目录内容"""
        if not headings:
            return ""
        
        toc_lines = ["## 📋 目录\n"]
        
        # 跳过第一个标题（通常是文件标题）
        start_idx = 1 if skip_first and headings else 0
        
        for level, text, anchor in headings[start_idx:]:
            # 只包含 2-4 级标题
            if level < 2 or level > 4:
                continue
            
            indent = "  " * (level - 2)
            toc_lines.append(f"{indent}- [{text}](#{anchor})")
        
        toc_lines.append("")
        return "\n".join(toc_lines)
    
    def check_numbering_consistency(self, content: str) -> List[str]:
        """检查序号一致性"""
        issues = []
        lines = content.split('\n')
        
        # 检查标题序号模式
        numbered_headings = []
        for i, line in enumerate(lines):
            match = re.match(r'^(#{2,6})\s+(\d+\.)+\s*(.+)$', line)
            if match:
                level = len(match.group(1))
                number = match.group(2)
                text = match.group(3)
                numbered_headings.append((i, level, number, text))
        
        if not numbered_headings:
            return issues
        
        # 检查序号连续性
        level_counters = {}
        for i, (line_num, level, number, text) in enumerate(numbered_headings):
            parts = [int(x) for x in number.rstrip('.').split('.')]
            
            if level not in level_counters:
                level_counters[level] = []
            
            level_counters[level].append((line_num, parts, text))
            
            # 简单检查：同级标题序号应该递增
            if len(level_counters[level]) > 1:
                prev_parts = level_counters[level][-2][1]
                curr_parts = parts
                
                # 检查最后一位是否递增
                if len(curr_parts) == len(prev_parts):
                    if curr_parts[-1] != prev_parts[-1] + 1:
                        issues.append(f"Line {line_num+1}: 序号不连续 {'.'.join(map(str, prev_parts))} -> {'.'.join(map(str, curr_parts))}")
        
        return issues
    
    def needs_toc(self, content: str, headings: List[Tuple[int, str, str]]) -> bool:
        """判断是否需要添加目录"""
        # 如果标题数量 >= 5，建议添加目录
        if len(headings) >= 5:
            return True
        
        # 如果文件超过 500 行，建议添加目录
        if len(content.split('\n')) >= 500:
            return True
        
        return False
    
    def insert_toc(self, content: str, toc: str) -> str:
        """在适当位置插入目录"""
        lines = content.split('\n')
        
        # 查找插入位置：在元数据块之后，第一个 ## 标题之前
        insert_pos = 0
        in_metadata = False
        
        for i, line in enumerate(lines):
            # 检测元数据块
            if i == 0 and line.strip().startswith('>'):
                in_metadata = True
            
            if in_metadata:
                # 元数据块结束
                if line.strip() == '---':
                    insert_pos = i + 1
                    break
                if not line.strip().startswith('>') and line.strip() != '':
                    in_metadata = False
            
            # 找到第一个 ## 标题
            if line.startswith('## '):
                insert_pos = i
                break
        
        # 插入目录
        lines.insert(insert_pos, '\n---\n')
        lines.insert(insert_pos + 1, toc)
        lines.insert(insert_pos + 2, '\n---\n')
        
        return '\n'.join(lines)
    
    def fix_file(self, filepath: Path) -> dict:
        """修复单个文件"""
        result = {
            'path': str(filepath.relative_to(self.base_path)),
            'has_toc': False,
            'needs_toc': False,
            'toc_updated': False,
            'numbering_issues': [],
            'action': 'skip'
        }
        
        try:
            with open(filepath, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # 提取标题
            headings = self.extract_headings(content)
            
            if not headings:
                result['action'] = 'skip - no headings'
                return result
            
            # 检查是否已有目录
            toc_section = self.find_toc_section(content)
            result['has_toc'] = toc_section is not None
            
            # 检查是否需要目录
            result['needs_toc'] = self.needs_toc(content, headings)
            
            # 检查序号一致性
            result['numbering_issues'] = self.check_numbering_consistency(content)
            
            # 决定是否需要修复
            needs_fix = False
            new_content = content
            
            # 情况1：需要目录但没有
            if result['needs_toc'] and not result['has_toc']:
                toc = self.generate_toc(headings)
                new_content = self.insert_toc(new_content, toc)
                result['toc_updated'] = True
                result['action'] = 'added TOC'
                needs_fix = True
            
            # 情况2：已有目录，更新
            elif result['has_toc']:
                toc = self.generate_toc(headings)
                lines = new_content.split('\n')
                start, end = toc_section
                
                # 替换旧目录
                new_lines = lines[:start] + toc.split('\n') + lines[end:]
                new_content = '\n'.join(new_lines)
                result['toc_updated'] = True
                result['action'] = 'updated TOC'
                needs_fix = True
            
            # 保存修改
            if needs_fix:
                with open(filepath, 'w', encoding='utf-8') as f:
                    f.write(new_content)
                self.fixed.append(result)
            
            # 记录问题
            if result['numbering_issues']:
                self.issues.append(result)
            
            return result
            
        except Exception as e:
            result['action'] = f'error: {str(e)}'
            return result
    
    def scan_and_fix(self, dry_run: bool = False) -> dict:
        """扫描并修复所有 Markdown 文件"""
        stats = {
            'total': 0,
            'fixed': 0,
            'issues': 0,
            'skipped': 0
        }
        
        results = []
        
        # 递归遍历所有 .md 文件
        for md_file in self.base_path.rglob('*.md'):
            # 跳过某些特殊文件
            if any(skip in str(md_file) for skip in [
                'node_modules', '.git', 'venv', '__pycache__'
            ]):
                continue
            
            stats['total'] += 1
            
            if not dry_run:
                result = self.fix_file(md_file)
                results.append(result)
                
                if result['action'].startswith('added') or result['action'].startswith('updated'):
                    stats['fixed'] += 1
                elif result['numbering_issues']:
                    stats['issues'] += 1
                else:
                    stats['skipped'] += 1
        
        return {
            'stats': stats,
            'results': results,
            'fixed_files': self.fixed,
            'issue_files': self.issues
        }

def main():
    import json
    
    # 获取 Concept 目录的路径
    base_path = Path(__file__).parent
    
    print("=" * 80)
    print("Markdown 目录和序号修复工具")
    print("=" * 80)
    print(f"\n扫描目录: {base_path}")
    print("\n开始处理...\n")
    
    fixer = MarkdownTOCFixer(str(base_path))
    report = fixer.scan_and_fix(dry_run=False)
    
    # 输出统计
    print("\n" + "=" * 80)
    print("处理完成！")
    print("=" * 80)
    print(f"\n总文件数: {report['stats']['total']}")
    print(f"已修复: {report['stats']['fixed']}")
    print(f"有问题: {report['stats']['issues']}")
    print(f"跳过: {report['stats']['skipped']}")
    
    # 输出修复的文件
    if report['fixed_files']:
        print("\n" + "-" * 80)
        print("已修复的文件:")
        print("-" * 80)
        for item in report['fixed_files'][:20]:  # 只显示前20个
            print(f"  ✅ {item['path']} - {item['action']}")
        if len(report['fixed_files']) > 20:
            print(f"  ... 还有 {len(report['fixed_files']) - 20} 个文件")
    
    # 输出有序号问题的文件
    if report['issue_files']:
        print("\n" + "-" * 80)
        print("发现序号问题的文件（需要手动检查）:")
        print("-" * 80)
        for item in report['issue_files'][:10]:
            print(f"  ⚠️  {item['path']}")
            for issue in item['numbering_issues'][:3]:
                print(f"     - {issue}")
        if len(report['issue_files']) > 10:
            print(f"  ... 还有 {len(report['issue_files']) - 10} 个文件")
    
    # 保存详细报告
    report_file = base_path / 'TOC_FIX_REPORT.json'
    with open(report_file, 'w', encoding='utf-8') as f:
        json.dump(report, f, ensure_ascii=False, indent=2)
    
    print(f"\n详细报告已保存到: {report_file}")
    print("\n" + "=" * 80)

if __name__ == '__main__':
    main()

