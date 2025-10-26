#!/usr/bin/env python3
"""
文档结构和目录序号分析工具
分析所有Markdown文档的：
1. 目录结构（TOC）
2. 标题层级和序号规范
3. 内容长度
4. 内容质量指标
"""

import os
import re
from pathlib import Path
from typing import Dict, List, Tuple
import json

class DocumentAnalyzer:
    def __init__(self, root_dir: str):
        self.root_dir = Path(root_dir)
        self.results = []
        
    def analyze_file(self, file_path: Path) -> Dict:
        """分析单个文档"""
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        lines = content.split('\n')
        
        # 基本信息
        info = {
            'path': str(file_path.relative_to(self.root_dir)),
            'total_lines': len(lines),
            'has_toc': False,
            'headings': [],
            'heading_issues': [],
            'content_length': len(content),
            'substantive_lines': 0,
        }
        
        # 检测TOC
        toc_pattern = re.compile(r'##\s*目录\s*\|\s*Table of Contents', re.IGNORECASE)
        for line in lines:
            if toc_pattern.search(line):
                info['has_toc'] = True
                break
        
        # 分析标题
        heading_pattern = re.compile(r'^(#{1,6})\s+(.+)$')
        for i, line in enumerate(lines, 1):
            match = heading_pattern.match(line)
            if match:
                level = len(match.group(1))
                title = match.group(2).strip()
                
                # 检测序号
                numbering = None
                # 匹配 "1.", "1.1", "1.1.1" 等格式
                num_match = re.match(r'^(\d+(?:\.\d+)*\.?)\s+(.+)$', title)
                if num_match:
                    numbering = num_match.group(1)
                    title_text = num_match.group(2)
                else:
                    title_text = title
                
                info['headings'].append({
                    'line': i,
                    'level': level,
                    'numbering': numbering,
                    'title': title_text,
                    'raw': title
                })
        
        # 检测标题层级问题
        prev_level = 0
        for h in info['headings']:
            if h['level'] > prev_level + 1 and prev_level > 0:
                info['heading_issues'].append({
                    'line': h['line'],
                    'issue': 'level_jump',
                    'detail': f"从 {prev_level} 级跳到 {h['level']} 级"
                })
            prev_level = h['level']
        
        # 统计实质内容行数（排除空行、标题、分隔线、元数据）
        for line in lines:
            line = line.strip()
            if line and not line.startswith('#') and line != '---' and not line.startswith('**') and len(line) > 10:
                info['substantive_lines'] += 1
        
        # 评估内容充实度
        if info['substantive_lines'] < 200:
            info['content_status'] = 'insufficient'
        elif info['substantive_lines'] < 400:
            info['content_status'] = 'moderate'
        else:
            info['content_status'] = 'sufficient'
        
        return info
    
    def analyze_directory(self, perspective_dir: str) -> List[Dict]:
        """分析整个视角目录"""
        target_dir = self.root_dir / perspective_dir
        results = []
        
        for md_file in sorted(target_dir.rglob('*.md')):
            # 跳过元文档
            if md_file.name in ['README.md', 'GLOSSARY.md', 'FAQ.md', 'LEARNING_PATHS.md']:
                continue
            
            try:
                info = self.analyze_file(md_file)
                results.append(info)
            except Exception as e:
                print(f"Error analyzing {md_file}: {e}")
        
        return results
    
    def check_numbering_consistency(self, headings: List[Dict]) -> List[str]:
        """检查序号一致性"""
        issues = []
        
        # 检查是否混用有序号和无序号
        has_numbering = any(h['numbering'] for h in headings if h['level'] == 2)
        all_numbered = all(h['numbering'] for h in headings if h['level'] == 2)
        
        if has_numbering and not all_numbered:
            issues.append("混用有序号和无序号的二级标题")
        
        # 检查序号连续性
        level2_numbers = []
        for h in headings:
            if h['level'] == 2 and h['numbering']:
                try:
                    num = int(h['numbering'].rstrip('.').split('.')[0])
                    level2_numbers.append(num)
                except:
                    pass
        
        if level2_numbers:
            for i in range(len(level2_numbers) - 1):
                if level2_numbers[i+1] != level2_numbers[i] + 1:
                    issues.append(f"序号不连续: {level2_numbers[i]} -> {level2_numbers[i+1]}")
        
        return issues
    
    def generate_report(self, results: List[Dict], output_file: str):
        """生成分析报告"""
        report = []
        report.append("# 文档结构和序号分析报告\n")
        report.append(f"**分析时间**: {__import__('datetime').datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
        report.append(f"**分析文档数**: {len(results)}\n\n")
        report.append("---\n\n")
        
        # 统计
        no_toc = [r for r in results if not r['has_toc']]
        insufficient = [r for r in results if r['content_status'] == 'insufficient']
        heading_issues = [r for r in results if r['heading_issues']]
        
        report.append("## 📊 总体统计\n\n")
        report.append(f"- **总文档数**: {len(results)}\n")
        report.append(f"- **缺少TOC**: {len(no_toc)} 个\n")
        report.append(f"- **内容不足**: {len(insufficient)} 个\n")
        report.append(f"- **标题问题**: {len(heading_issues)} 个\n\n")
        
        # 缺少TOC的文档
        if no_toc:
            report.append("## ❌ 缺少目录的文档\n\n")
            for r in no_toc:
                report.append(f"- `{r['path']}` ({r['total_lines']} 行)\n")
            report.append("\n")
        
        # 内容不足的文档
        if insufficient:
            report.append("## ⚠️ 内容不足的文档\n\n")
            for r in insufficient:
                report.append(f"- `{r['path']}` (实质内容: {r['substantive_lines']} 行)\n")
            report.append("\n")
        
        # 标题结构问题
        if heading_issues:
            report.append("## 🔍 标题结构问题\n\n")
            for r in heading_issues:
                report.append(f"### {r['path']}\n\n")
                for issue in r['heading_issues']:
                    report.append(f"- 行 {issue['line']}: {issue['detail']}\n")
                report.append("\n")
        
        # 详细标题分析
        report.append("## 📋 标题结构详情\n\n")
        for r in results[:10]:  # 只显示前10个作为示例
            report.append(f"### {r['path']}\n\n")
            report.append(f"- 总行数: {r['total_lines']}\n")
            report.append(f"- 实质内容: {r['substantive_lines']} 行\n")
            report.append(f"- 有TOC: {'✅' if r['has_toc'] else '❌'}\n")
            report.append(f"- 标题数: {len(r['headings'])}\n\n")
            
            if r['headings']:
                report.append("标题层级:\n\n")
                for h in r['headings'][:15]:  # 只显示前15个标题
                    indent = "  " * (h['level'] - 1)
                    numbering = h['numbering'] or "无序号"
                    report.append(f"{indent}- L{h['level']}: {numbering} {h['title']}\n")
                report.append("\n")
        
        # 写入文件
        output_path = self.root_dir / output_file
        with open(output_path, 'w', encoding='utf-8') as f:
            f.writelines(report)
        
        print(f"报告已生成: {output_path}")
        
        # 同时生成JSON数据
        json_path = output_path.with_suffix('.json')
        with open(json_path, 'w', encoding='utf-8') as f:
            json.dump(results, f, ensure_ascii=False, indent=2)
        print(f"JSON数据已生成: {json_path}")

def main():
    analyzer = DocumentAnalyzer('.')
    
    perspectives = [
        'AI_model_Perspective',
        'FormalLanguage_Perspective',
        'Information_Theory_Perspective'
    ]
    
    all_results = []
    
    for perspective in perspectives:
        print(f"正在分析 {perspective}...")
        results = analyzer.analyze_directory(perspective)
        all_results.extend(results)
        print(f"  完成: {len(results)} 个文档")
    
    print(f"\n总计分析: {len(all_results)} 个文档")
    
    # 生成报告
    analyzer.generate_report(all_results, 'DOCUMENT_STRUCTURE_ANALYSIS_REPORT.md')

if __name__ == '__main__':
    main()

