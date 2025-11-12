#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
简化Markdown文件的目录结构
去掉前导序号，只保留标题名称，使目录更简洁
"""

import os
import re
from pathlib import Path

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

def simplify_toc_line(line):
    """简化目录行，去掉前导序号"""
    # 匹配目录项，如 - [1.1.1 执行引擎](#111-执行引擎)
    match = re.match(r'(\s*)- \[(\d+\.\d+(?:\.\d+)*)\s+(.+?)\]\(#(.+?)\)', line)
    if match:
        indent = match.group(1)
        number = match.group(2)
        title = match.group(3)
        anchor = match.group(4)
        
        # 去掉前导序号，只保留标题
        new_line = f"{indent}- [{title}](#{anchor})"
        return new_line
    
    # 如果不是带编号的目录项，保持原样
    return line

def simplify_toc(toc_lines):
    """简化整个目录"""
    simplified = []
    for line in toc_lines:
        simplified.append(simplify_toc_line(line))
    return simplified

def process_file(filepath):
    """处理单个文件"""
    print(f"处理文件: {filepath}")
    
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # 解析并简化目录
    toc_lines, toc_start, toc_end = parse_toc(content)
    if toc_lines:
        simplified_toc = simplify_toc(toc_lines)
        
        # 替换目录
        lines = content.split('\n')
        new_lines = lines[:toc_start] + simplified_toc + lines[toc_end:]
        content = '\n'.join(new_lines)
        
        # 写回文件
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(content)
        
        print(f"  完成：已简化目录")
        return True
    else:
        print(f"  跳过：未找到目录")
        return False

def main():
    """主函数"""
    base_dir = Path(__file__).parent
    
    # 查找所有markdown文件
    md_files = list(base_dir.rglob('*.md'))
    
    # 排除README和总览文件
    exclude_patterns = ['README.md', '总览.md', '总结.md', '说明.md', '指南.md', '报告.md', '备份.md', 'fix_toc', 'simplify_toc']
    md_files = [f for f in md_files if not any(p in f.name for p in exclude_patterns)]
    
    print(f"找到 {len(md_files)} 个markdown文件")
    
    processed = 0
    for md_file in sorted(md_files):
        if process_file(md_file):
            processed += 1
    
    print(f"\n处理完成：共处理 {processed} 个文件")

if __name__ == '__main__':
    main()
