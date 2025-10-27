#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
文档质量分析工具
分析 Concept/ 目录下所有 markdown 文档的质量问题：
1. 是否有目录（TOC）
2. 内容长度是否充足
3. 本地链接格式是否正确
"""

import os
import re
from pathlib import Path
from typing import List, Dict, Tuple

def has_toc(content: str) -> bool:
    """检查文档是否有目录"""
    # 检查常见的目录标记
    toc_patterns = [
        r'^##?\s+目录',
        r'^##?\s+Table of Contents',
        r'^##?\s+TOC',
        r'^\s*-\s+\[.*\]\(#.*\)',  # markdown 链接到标题
    ]
    
    lines = content.split('\n')
    for i, line in enumerate(lines[:50]):  # 只检查前50行
        for pattern in toc_patterns:
            if re.match(pattern, line, re.IGNORECASE):
                return True
        # 如果连续有3个以上的内部链接，认为是目录
        if i < len(lines) - 3:
            links = 0
            for j in range(i, min(i+10, len(lines))):
                if re.match(r'^\s*-\s+\[', lines[j]):
                    links += 1
            if links >= 3:
                return True
    return False

def count_content_lines(content: str) -> int:
    """计算有效内容行数（排除空行和注释）"""
    lines = content.split('\n')
    count = 0
    for line in lines:
        stripped = line.strip()
        if stripped and not stripped.startswith('<!--'):
            count += 1
    return count

def check_local_links(content: str, file_path: str) -> List[str]:
    """检查本地链接格式问题"""
    issues = []
    
    # 查找所有 markdown 链接
    link_pattern = r'\[([^\]]+)\]\(([^\)]+)\)'
    matches = re.finditer(link_pattern, content)
    
    for match in matches:
        link_text = match.group(1)
        link_target = match.group(2)
        
        # 跳过外部链接
        if link_target.startswith('http://') or link_target.startswith('https://'):
            continue
        
        # 跳过锚点链接
        if link_target.startswith('#'):
            continue
        
        # 检查相对路径链接
        if '/' in link_target or '\\' in link_target:
            # 检查文件是否存在
            base_dir = os.path.dirname(file_path)
            target_path = os.path.join(base_dir, link_target.split('#')[0])
            target_path = os.path.normpath(target_path)
            
            if not os.path.exists(target_path):
                issues.append(f"断链: [{link_text}]({link_target})")
    
    return issues

def analyze_document(file_path: str) -> Dict:
    """分析单个文档"""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
    except Exception as e:
        return {
            'path': file_path,
            'error': str(e)
        }
    
    # 获取文件大小
    file_size = os.path.getsize(file_path)
    
    # 计算内容行数
    content_lines = count_content_lines(content)
    
    # 检查是否有目录
    has_table_of_contents = has_toc(content)
    
    # 检查链接
    link_issues = check_local_links(content, file_path)
    
    # 判断内容是否充足（少于50行认为内容不足）
    insufficient_content = content_lines < 50
    
    return {
        'path': file_path,
        'size': file_size,
        'lines': content_lines,
        'has_toc': has_table_of_contents,
        'insufficient_content': insufficient_content,
        'link_issues': link_issues,
        'has_issues': not has_table_of_contents or insufficient_content or len(link_issues) > 0
    }

def analyze_all_docs(root_dir: str) -> List[Dict]:
    """分析所有文档"""
    results = []
    
    # 排除的目录和文件
    exclude_dirs = {'.git', 'node_modules', '__pycache__'}
    exclude_files = {
        'analyze_docs.py',
        'PROGRESS_', 'REPORT', 'SUMMARY', 'COMPLETION',
        'ADVANCEMENT', 'IMPROVEMENT', 'UPDATE', 'FINAL',
        'REDUNDANCY', 'OPTIMIZATION', 'QUALITY', 'ASSESSMENT',
        'MILESTONE', 'SESSION', 'KICKOFF', 'PHASE'
    }
    
    for root, dirs, files in os.walk(root_dir):
        # 排除特定目录
        dirs[:] = [d for d in dirs if d not in exclude_dirs]
        
        for file in files:
            if not file.endswith('.md'):
                continue
            
            # 跳过报告和进度文件
            skip = False
            for pattern in exclude_files:
                if pattern in file.upper():
                    skip = True
                    break
            if skip:
                continue
            
            file_path = os.path.join(root, file)
            rel_path = os.path.relpath(file_path, root_dir)
            
            result = analyze_document(file_path)
            result['rel_path'] = rel_path
            results.append(result)
    
    return results

def generate_report(results: List[Dict], output_file: str):
    """生成分析报告"""
    # 统计
    total = len(results)
    no_toc = sum(1 for r in results if not r.get('has_toc', True))
    insufficient = sum(1 for r in results if r.get('insufficient_content', False))
    has_link_issues = sum(1 for r in results if r.get('link_issues', []))
    
    # 分类问题文件
    no_toc_files = [r for r in results if not r.get('has_toc', True)]
    insufficient_files = [r for r in results if r.get('insufficient_content', False)]
    link_issue_files = [r for r in results if r.get('link_issues', [])]
    
    # 生成报告
    report = []
    report.append("# 文档质量分析报告")
    report.append("")
    report.append(f"生成时间: {__import__('datetime').datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    report.append("")
    
    report.append("## 总体统计")
    report.append("")
    report.append(f"- 总文档数: {total}")
    report.append(f"- 缺少目录: {no_toc} ({no_toc*100//max(total,1)}%)")
    report.append(f"- 内容不足: {insufficient} ({insufficient*100//max(total,1)}%)")
    report.append(f"- 链接问题: {has_link_issues} ({has_link_issues*100//max(total,1)}%)")
    report.append("")
    
    # 缺少目录的文件
    if no_toc_files:
        report.append("## 缺少目录的文档")
        report.append("")
        report.append("以下文档缺少目录（TOC）：")
        report.append("")
        for r in sorted(no_toc_files, key=lambda x: x['rel_path']):
            report.append(f"- `{r['rel_path']}` ({r['lines']} 行)")
        report.append("")
    
    # 内容不足的文件
    if insufficient_files:
        report.append("## 内容不足的文档")
        report.append("")
        report.append("以下文档内容不足（少于50行）：")
        report.append("")
        for r in sorted(insufficient_files, key=lambda x: x['lines']):
            report.append(f"- `{r['rel_path']}` ({r['lines']} 行)")
        report.append("")
    
    # 链接问题
    if link_issue_files:
        report.append("## 链接问题的文档")
        report.append("")
        for r in sorted(link_issue_files, key=lambda x: x['rel_path']):
            report.append(f"### {r['rel_path']}")
            report.append("")
            for issue in r['link_issues']:
                report.append(f"- {issue}")
            report.append("")
    
    # 写入文件
    with open(output_file, 'w', encoding='utf-8') as f:
        f.write('\n'.join(report))
    
    print(f"报告已生成: {output_file}")
    print(f"\n总文档数: {total}")
    print(f"缺少目录: {no_toc}")
    print(f"内容不足: {insufficient}")
    print(f"链接问题: {has_link_issues}")

if __name__ == '__main__':
    root_dir = '.'
    results = analyze_all_docs(root_dir)
    generate_report(results, 'DOCUMENT_ANALYSIS_REPORT.md')

