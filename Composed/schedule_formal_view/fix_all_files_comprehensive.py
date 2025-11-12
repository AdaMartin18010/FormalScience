#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
全面递归扫描并修复所有markdown文件的目录和内容编号
确保格式统一：
- 一级子主题：不带点号（如 1 执行引擎）
- 二级子主题：带点号（如 1.1 超标量流水线）
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

def generate_anchor(text):
    """生成锚点链接（基于文本）"""
    anchor = text.lower()
    anchor = re.sub(r'[^\w\s-]', '', anchor)
    anchor = re.sub(r'\s+', '-', anchor)
    return anchor

def parse_toc(content):
    """解析目录内容"""
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

def extract_content_headers(content):
    """提取内容中的标题，返回标题列表"""
    headers = []
    lines = content.split('\n')
    in_toc = False
    
    for line in lines:
        if '## 📋 目录' in line:
            in_toc = True
        elif in_toc and line.strip() == '---':
            in_toc = False
            continue
        
        if in_toc:
            continue
        
        # 匹配标题，如 ## 1 执行引擎 或 ### 1.1 超标量流水线
        match = re.match(r'(#{2,})\s+(\d+(?:\.\d+)*)\s+(.+?)$', line)
        if match:
            level = len(match.group(1))
            number = match.group(2)
            title = match.group(3)
            headers.append((level, number, title))
    
    return headers

def format_toc_number(number, level):
    """格式化目录编号
    - 一级子主题（level=2）：不带点号（如 1）
    - 二级子主题（level=3）：带点号（如 1.1）
    """
    if level == 2:
        # 一级子主题：去掉点号，只保留数字
        if '.' in number:
            return number.split('.')[0]
        return number
    elif level == 3:
        # 二级子主题：保留点号格式
        return number
    return number

def simplify_number(number_str, file_num):
    """简化编号，去掉文件编号前缀"""
    if not file_num:
        return number_str
    
    file_series, file_sub = file_num
    file_prefix = f"{file_series}.{file_sub}."
    
    # 如果编号以文件前缀开头，去掉前缀
    if number_str.startswith(file_prefix):
        simplified = number_str[len(file_prefix):]
        return simplified
    
    return number_str

def fix_toc_with_headers(toc_lines, content_headers, file_num):
    """根据内容标题修复目录"""
    fixed_lines = []
    header_index = 0
    
    for line in toc_lines:
        # 跳过空行和目录标题
        if not line.strip() or line.strip() == '## 📋 目录' or line.strip().startswith('- [📋 目录]'):
            fixed_lines.append(line)
            continue
        
        # 匹配目录项
        match = re.match(r'(\s*)- \[(.+?)\]\(#(.+?)\)', line)
        if match:
            indent = match.group(1)
            title_text = match.group(2)
            old_anchor = match.group(3)
            
            # 计算缩进级别（每2个空格为一级）
            indent_level = len(indent) // 2
            
            # 找到对应的标题
            if header_index < len(content_headers):
                level, number, title = content_headers[header_index]
                
                # 如果缩进级别匹配（目录缩进级别 + 1 = 标题级别）
                if level == indent_level + 1:
                    # 简化编号（去掉文件编号前缀）
                    simplified_number = simplify_number(number, file_num)
                    
                    # 格式化编号
                    formatted_number = format_toc_number(simplified_number, level)
                    
                    # 生成新的目录项
                    if formatted_number:
                        new_title = f"{formatted_number} {title}"
                    else:
                        new_title = title
                    
                    new_anchor = generate_anchor(new_title)
                    new_line = f"{indent}- [{new_title}](#{new_anchor})"
                    fixed_lines.append(new_line)
                    header_index += 1
                else:
                    fixed_lines.append(line)
            else:
                fixed_lines.append(line)
        else:
            fixed_lines.append(line)
    
    return fixed_lines

def fix_content_headers(content, file_num):
    """修复内容中的标题编号，确保格式正确"""
    if not file_num:
        return content
    
    file_series, file_sub = file_num
    file_prefix = f"{file_series}.{file_sub}."
    lines = content.split('\n')
    fixed_lines = []
    in_toc = False
    
    for line in lines:
        # 跳过目录部分
        if '## 📋 目录' in line:
            in_toc = True
        elif in_toc and line.strip() == '---':
            in_toc = False
        
        if in_toc:
            fixed_lines.append(line)
            continue
        
        # 匹配标题，如 ## 1.1.1 执行引擎 或 ### 1.1.1.1 超标量流水线
        match = re.match(r'(#{2,})\s+(\d+(?:\.\d+)*)\s+(.+?)$', line)
        if match:
            level = len(match.group(1))
            number = match.group(2)
            title = match.group(3)
            
            # 去掉文件编号前缀
            if number.startswith(file_prefix):
                simplified_number = number[len(file_prefix):]
            else:
                simplified_number = number
            
            # 格式化编号
            formatted_number = format_toc_number(simplified_number, level)
            
            # 生成新标题
            if formatted_number:
                new_line = f"{'#' * level} {formatted_number} {title}"
            else:
                new_line = f"{'#' * level} {title}"
            
            fixed_lines.append(new_line)
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
    
    # 先修复内容中的标题编号
    content = fix_content_headers(content, file_num)
    
    # 提取内容中的标题
    content_headers = extract_content_headers(content)
    
    if not content_headers:
        print(f"  跳过：未找到标题")
        return False
    
    # 解析并修复目录
    toc_lines, toc_start, toc_end = parse_toc(content)
    if toc_lines:
        fixed_toc = fix_toc_with_headers(toc_lines, content_headers, file_num)
        
        # 替换目录
        lines = content.split('\n')
        new_lines = lines[:toc_start] + fixed_toc + lines[toc_end:]
        content = '\n'.join(new_lines)
        
        # 写回文件
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(content)
        
        print(f"  完成：已修复子主题编号格式")
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
    exclude_patterns = ['README.md', '总览.md', '总结.md', '说明.md', '指南.md', '报告.md', '备份.md', 
                        'fix_toc', 'simplify_toc', 'simplify_subsection', 'fix_anchors', 'fix_toc_numbers', 
                        'fix_all_subsection_numbers', 'fix_all_files_comprehensive', 
                        'schedule_formal_view.md', 'schedule_formal_view_重构版.md']
    md_files = [f for f in md_files if not any(p in f.name for p in exclude_patterns)]
    
    print(f"找到 {len(md_files)} 个markdown文件")
    print("")
    
    processed = 0
    skipped = 0
    for md_file in sorted(md_files):
        if process_file(md_file):
            processed += 1
        else:
            skipped += 1
    
    print(f"\n{'='*60}")
    print(f"处理完成：共处理 {processed} 个文件，跳过 {skipped} 个文件")
    print(f"{'='*60}")

if __name__ == '__main__':
    main()
