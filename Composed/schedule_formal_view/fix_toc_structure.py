#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
统一Markdown文件的目录结构
确保：
1. 每个文件有且只有一个目录
2. 主题与子主题编号一致
3. 目录结构统一
"""

import os
import re
from pathlib import Path

def extract_file_number(filename):
    """从文件名提取编号，如 01.1_CPU微架构.md -> (1, 1)"""
    match = re.match(r'(\d+)\.(\d+)_', filename)
    if match:
        return (int(match.group(1)), int(match.group(2)))
    return None

def parse_toc(content):
    """解析目录内容，返回目录行列表"""
    lines = content.split('\n')
    toc_start = -1
    toc_end = -1
    
    for i, line in enumerate(lines):
        if line.strip() == '## 📋 目录':
            toc_start = i
        elif toc_start >= 0 and line.strip() == '---' and i > toc_start + 2:
            toc_end = i
            break
    
    if toc_start >= 0 and toc_end > toc_start:
        return lines[toc_start:toc_end], toc_start, toc_end
    return None, -1, -1

def extract_title_number(title_line):
    """从标题行提取编号，如 # 6.2 OS内核调度 -> (6, 2)"""
    match = re.match(r'#\s+(\d+)\.(\d+)\s+', title_line)
    if match:
        return (int(match.group(1)), int(match.group(2)))
    return None

def fix_toc_numbering(toc_lines, file_num):
    """修复目录编号，确保与文件编号一致"""
    if not file_num:
        return toc_lines
    
    file_series, file_sub = file_num
    
    fixed_lines = []
    for line in toc_lines:
        # 跳过空行和目录标题
        if not line.strip() or line.strip() == '## 📋 目录' or line.strip().startswith('- [📋 目录]'):
            fixed_lines.append(line)
            continue
        
        # 匹配目录项，如 - [6.1 CFS调度器形式化](#61-cfs调度器形式化)
        match = re.match(r'(\s*)- \[(\d+)\.(\d+)\s+(.+?)\]\(#(.+?)\)', line)
        if match:
            indent = match.group(1)
            toc_series = int(match.group(2))
            toc_sub = int(match.group(3))
            title = match.group(4)
            anchor = match.group(5)
            
            # 如果目录编号与文件编号不一致，修复它
            if toc_series != file_series:
                # 修复为正确的编号
                new_series = file_series
                new_sub = toc_sub
                new_line = f"{indent}- [{new_series}.{new_sub} {title}](#{anchor})"
                fixed_lines.append(new_line)
            else:
                fixed_lines.append(line)
        else:
            fixed_lines.append(line)
    
    return fixed_lines

def fix_content_headers(content, file_num):
    """修复内容中的标题编号，确保与文件编号一致"""
    if not file_num:
        return content
    
    file_series, file_sub = file_num
    lines = content.split('\n')
    fixed_lines = []
    
    for line in lines:
        # 匹配标题，如 ## 6.1 CFS调度器形式化
        match = re.match(r'(#{2,})\s+(\d+)\.(\d+)\s+(.+?)$', line)
        if match:
            level = match.group(1)
            header_series = int(match.group(2))
            header_sub = int(match.group(3))
            title = match.group(4)
            
            # 如果标题编号与文件编号不一致，修复它
            if header_series != file_series:
                new_series = file_series
                new_sub = header_sub
                fixed_lines.append(f"{level} {new_series}.{new_sub} {title}")
            else:
                fixed_lines.append(line)
        else:
            fixed_lines.append(line)
    
    return '\n'.join(fixed_lines)

def process_file(filepath):
    """处理单个文件"""
    print(f"处理文件: {filepath}")
    
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # 提取文件编号
    filename = os.path.basename(filepath)
    file_num = extract_file_number(filename)
    
    if not file_num:
        print(f"  跳过：无法提取文件编号")
        return False
    
    # 提取标题编号
    lines = content.split('\n')
    title_num = None
    for line in lines[:10]:  # 检查前10行
        if line.startswith('#'):
            title_num = extract_title_number(line)
            break
    
    if not title_num:
        print(f"  跳过：无法提取标题编号")
        return False
    
    # 检查标题编号与文件编号是否一致
    if title_num != file_num:
        print(f"  警告：标题编号 {title_num} 与文件编号 {file_num} 不一致")
        # 修复标题
        content = re.sub(
            rf'^#\s+{title_num[0]}\.{title_num[1]}\s+',
            f'# {file_num[0]}.{file_num[1]} ',
            content,
            flags=re.MULTILINE
        )
    
    # 解析并修复目录
    toc_lines, toc_start, toc_end = parse_toc(content)
    if toc_lines:
        fixed_toc = fix_toc_numbering(toc_lines, file_num)
        
        # 替换目录
        lines = content.split('\n')
        new_lines = lines[:toc_start] + fixed_toc + lines[toc_end:]
        content = '\n'.join(new_lines)
    
    # 修复内容中的标题编号
    content = fix_content_headers(content, file_num)
    
    # 写回文件
    with open(filepath, 'w', encoding='utf-8') as f:
        f.write(content)
    
    print(f"  完成：已修复目录和标题编号")
    return True

def main():
    """主函数"""
    base_dir = Path(__file__).parent
    
    # 查找所有markdown文件
    md_files = list(base_dir.rglob('*.md'))
    
    # 排除README和总览文件
    exclude_patterns = ['README.md', '总览.md', '总结.md', '说明.md', '指南.md', '报告.md', '备份.md']
    md_files = [f for f in md_files if not any(p in f.name for p in exclude_patterns)]
    
    print(f"找到 {len(md_files)} 个markdown文件")
    
    processed = 0
    for md_file in sorted(md_files):
        if process_file(md_file):
            processed += 1
    
    print(f"\n处理完成：共处理 {processed} 个文件")

if __name__ == '__main__':
    main()
