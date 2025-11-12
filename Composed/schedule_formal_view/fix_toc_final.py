#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
最终版：统一Markdown文件的目录结构
确保：
1. 每个文件有且只有一个目录
2. 主题与子主题编号一致
3. 子主题编号从文件编号开始（如文件1.1，子主题从1.1.1开始）
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

def fix_toc_numbering(toc_lines, file_num):
    """修复目录编号，确保子主题从文件编号开始"""
    if not file_num:
        return toc_lines
    
    file_series, file_sub = file_num
    fixed_lines = []
    sub_index = 1  # 子主题索引从1开始
    
    for line in toc_lines:
        # 跳过空行和目录标题
        if not line.strip() or line.strip() == '## 📋 目录' or line.strip().startswith('- [📋 目录]'):
            fixed_lines.append(line)
            continue
        
        # 计算缩进级别
        indent = len(line) - len(line.lstrip())
        indent_level = indent // 2  # 假设每级缩进2个空格
        
        # 匹配目录项
        match = re.match(r'(\s*)- \[(\d+)(?:\.(\d+))?(?:\.(\d+))?\s+(.+?)\]\(#(.+?)\)', line)
        if match:
            indent_str = match.group(1)
            toc_series = int(match.group(2))
            toc_sub = int(match.group(3)) if match.group(3) else None
            toc_subsub = int(match.group(4)) if match.group(4) else None
            title = match.group(5)
            anchor = match.group(6)
            
            if indent_level == 0:
                # 顶级标题，应该是文件标题本身，保持不变
                fixed_lines.append(line)
            elif indent_level == 1:
                # 一级子主题，应该是 file_series.file_sub.sub_index
                new_num = f"{file_series}.{file_sub}.{sub_index}"
                new_line = f"{indent_str}- [{new_num} {title}](#{anchor})"
                fixed_lines.append(new_line)
                sub_index += 1
            elif indent_level == 2:
                # 二级子主题，需要找到父主题的编号
                parent_sub = sub_index - 1
                subsub_index = toc_subsub if toc_subsub else 1
                new_num = f"{file_series}.{file_sub}.{parent_sub}.{subsub_index}"
                new_line = f"{indent_str}- [{new_num} {title}](#{anchor})"
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
    sub_index = 1
    in_toc = False
    
    for i, line in enumerate(lines):
        # 跳过目录部分
        if '## 📋 目录' in line:
            in_toc = True
        elif in_toc and line.strip() == '---':
            in_toc = False
        
        # 匹配标题
        match = re.match(r'(#{2,})\s+(\d+)(?:\.(\d+))?(?:\.(\d+))?\s+(.+?)$', line)
        if match and not in_toc:
            level = match.group(1)
            header_series = int(match.group(2))
            header_sub = int(match.group(3)) if match.group(3) else None
            header_subsub = int(match.group(4)) if match.group(4) else None
            title = match.group(5)
            
            level_count = len(level)
            
            if level_count == 2:
                # 二级标题，应该是 file_series.file_sub.sub_index
                if header_series != file_series or (header_sub and header_sub != file_sub):
                    new_num = f"{file_series}.{file_sub}.{sub_index}"
                    fixed_lines.append(f"{level} {new_num} {title}")
                    sub_index += 1
                elif header_series == file_series and header_sub == file_sub:
                    # 已经是正确的格式，但需要更新sub_index
                    fixed_lines.append(line)
                    sub_index += 1
                else:
                    fixed_lines.append(line)
            elif level_count == 3:
                # 三级标题，应该是 file_series.file_sub.parent_sub.subsub_index
                if header_series != file_series or (header_sub and header_sub != file_sub):
                    parent_sub = sub_index - 1
                    subsub_index = header_subsub if header_subsub else 1
                    new_num = f"{file_series}.{file_sub}.{parent_sub}.{subsub_index}"
                    fixed_lines.append(f"{level} {new_num} {title}")
                else:
                    fixed_lines.append(line)
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
    exclude_patterns = ['README.md', '总览.md', '总结.md', '说明.md', '指南.md', '报告.md', '备份.md', 'fix_toc']
    md_files = [f for f in md_files if not any(p in f.name for p in exclude_patterns)]
    
    print(f"找到 {len(md_files)} 个markdown文件")
    
    processed = 0
    for md_file in sorted(md_files):
        if process_file(md_file):
            processed += 1
    
    print(f"\n处理完成：共处理 {processed} 个文件")

if __name__ == '__main__':
    main()
