#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
专门修复Concept目录下的markdown文件
处理格式：一级标题不带点号，二级标题带点号
"""

import os
import re
from pathlib import Path

def extract_file_number(filename):
    """从文件名提取编号，如 04.2_Continuous_Representation_Theory.md -> (4, 2)"""
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
        if '## 📋 目录' in line or '## 目录' in line:
            toc_start = i
        elif toc_start >= 0 and line.strip() == '---' and i > toc_start + 2:
            toc_end = i
            break
    
    if toc_start >= 0 and toc_end > toc_start:
        return lines[toc_start:toc_end], toc_start, toc_end
    return None, -1, -1

def extract_content_headers(content):
    """提取内容中的标题"""
    headers = []
    lines = content.split('\n')
    in_toc = False
    
    for line in lines:
        if '## 📋 目录' in line or '## 目录' in line:
            in_toc = True
        elif in_toc and line.strip() == '---':
            in_toc = False
            continue
        
        if in_toc:
            continue
        
        # 匹配标题，如 ## 1 引言 或 ### 1.1 核心思想
        match = re.match(r'(#{2,})\s+(\d+(?:\.\d+)*)?\s*(.+?)$', line)
        if match:
            level = len(match.group(1))
            number = match.group(2) if match.group(2) else None
            title = match.group(3).strip()
            
            # 跳过特殊标题
            if title in ['📋 目录', '目录', '导航 | Navigation', '相关主题 | Related Topics', 
                        '参考文献', 'References']:
                continue
            
            headers.append((level, number, title))
    
    return headers

def assign_numbers_to_headers(headers, file_num):
    """为标题分配编号"""
    numbered_headers = []
    current_numbers = {}
    
    for level, number, title in headers:
        if number:
            # 已有编号，简化它
            if file_num:
                file_series, file_sub = file_num
                file_prefix = f"{file_series}.{file_sub}."
                if number.startswith(file_prefix):
                    number = number[len(file_prefix):]
            numbered_headers.append((level, number, title))
            current_numbers[level] = number
            # 重置更高级别的编号
            for l in range(level + 1, 10):
                if l in current_numbers:
                    del current_numbers[l]
        else:
            # 没有编号，分配一个
            if level == 2:
                if level not in current_numbers:
                    current_numbers[level] = "1"
                else:
                    current_numbers[level] = str(int(current_numbers[level]) + 1)
            elif level == 3:
                if level - 1 in current_numbers:
                    parent_num = current_numbers[level - 1]
                    if level in current_numbers:
                        parts = current_numbers[level].split('.')
                        if len(parts) == 2:
                            current_numbers[level] = f"{parent_num}.{int(parts[1]) + 1}"
                        else:
                            current_numbers[level] = f"{parent_num}.1"
                    else:
                        current_numbers[level] = f"{parent_num}.1"
                else:
                    current_numbers[level] = "1.1"
            else:
                # 更深层级
                parent_level = level - 1
                if parent_level in current_numbers:
                    parent_num = current_numbers[parent_level]
                    if level in current_numbers:
                        parts = current_numbers[level].split('.')
                        parts[-1] = str(int(parts[-1]) + 1)
                        current_numbers[level] = '.'.join(parts)
                    else:
                        current_numbers[level] = f"{parent_num}.1"
                else:
                    current_numbers[level] = "1"
            
            numbered_headers.append((level, current_numbers[level], title))
            # 重置更高级别的编号
            for l in range(level + 1, 10):
                if l in current_numbers:
                    del current_numbers[l]
    
    return numbered_headers

def format_toc_number(number, level):
    """格式化目录编号"""
    if not number:
        return None
    
    if level == 2:
        # 一级子主题：不带点号
        if '.' in number:
            return number.split('.')[0]
        return number
    elif level == 3:
        # 二级子主题：带点号
        return number
    return number

def fix_toc_with_headers(toc_lines, content_headers, file_num):
    """根据内容标题修复目录"""
    numbered_headers = assign_numbers_to_headers(content_headers, file_num)
    
    fixed_lines = []
    header_index = 0
    seen_titles = set()  # 避免重复
    
    for line in toc_lines:
        if not line.strip() or '## 📋 目录' in line or '## 目录' in line:
            fixed_lines.append(line)
            continue
        
        match = re.match(r'(\s*)- \[(.+?)\]\(#(.+?)\)', line)
        if match:
            indent = match.group(1)
            title_text = match.group(2)
            old_anchor = match.group(3)
            
            indent_level = len(indent) // 2
            
            if header_index < len(numbered_headers):
                level, number, title = numbered_headers[header_index]
                
                if level == indent_level + 1:
                    # 检查是否重复
                    title_key = (level, title)
                    if title_key in seen_titles:
                        # 跳过重复的标题
                        header_index += 1
                        if header_index < len(numbered_headers):
                            level, number, title = numbered_headers[header_index]
                        else:
                            fixed_lines.append(line)
                            continue
                    
                    seen_titles.add(title_key)
                    
                    formatted_number = format_toc_number(number, level)
                    
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
    """修复内容中的标题编号"""
    headers = extract_content_headers(content)
    numbered_headers = assign_numbers_to_headers(headers, file_num)
    
    lines = content.split('\n')
    fixed_lines = []
    in_toc = False
    header_index = 0
    
    for line in lines:
        if '## 📋 目录' in line or '## 目录' in line:
            in_toc = True
        elif in_toc and line.strip() == '---':
            in_toc = False
        
        if in_toc:
            fixed_lines.append(line)
            continue
        
        match = re.match(r'(#{2,})\s+(\d+(?:\.\d+)*)?\s*(.+?)$', line)
        if match:
            level = len(match.group(1))
            old_number = match.group(2) if match.group(2) else None
            title = match.group(3).strip()
            
            if title in ['📋 目录', '目录', '导航 | Navigation', '相关主题 | Related Topics', 
                        '参考文献', 'References']:
                fixed_lines.append(line)
                continue
            
            if header_index < len(numbered_headers):
                h_level, h_number, h_title = numbered_headers[header_index]
                if h_level == level and h_title == title:
                    formatted_number = format_toc_number(h_number, level)
                    
                    if formatted_number:
                        new_line = f"{'#' * level} {formatted_number} {title}"
                    else:
                        new_line = f"{'#' * level} {title}"
                    
                    fixed_lines.append(new_line)
                    header_index += 1
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
    
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
    except Exception as e:
        print(f"  错误：无法读取文件 - {e}")
        return False
    
    filename = os.path.basename(filepath)
    file_num = extract_file_number(filename)
    
    content = fix_content_headers(content, file_num)
    content_headers = extract_content_headers(content)
    
    if not content_headers:
        print(f"  跳过：未找到标题")
        return False
    
    toc_lines, toc_start, toc_end = parse_toc(content)
    if toc_lines:
        fixed_toc = fix_toc_with_headers(toc_lines, content_headers, file_num)
        
        lines = content.split('\n')
        new_lines = lines[:toc_start] + fixed_toc + lines[toc_end:]
        content = '\n'.join(new_lines)
        
        try:
            with open(filepath, 'w', encoding='utf-8') as f:
                f.write(content)
            print(f"  完成：已修复子主题编号格式")
            return True
        except Exception as e:
            print(f"  错误：无法写入文件 - {e}")
            return False
    else:
        print(f"  跳过：未找到目录")
        return False

def main():
    """主函数"""
    base_dir = Path(__file__).parent
    
    # 只处理Concept目录
    concept_dir = base_dir / 'Concept'
    if not concept_dir.exists():
        print(f"错误：找不到Concept目录")
        return
    
    md_files = list(concept_dir.rglob('*.md'))
    
    exclude_patterns = ['README.md', '总览.md', '总结.md', '说明.md', '指南.md', '报告.md', 
                        '备份.md', 'fix_', 'simplify_', 'batch_', 'generate_', 'link_', 
                        'structure_', 'toc_', 'requirements.txt']
    
    md_files = [f for f in md_files if not any(p in f.name for p in exclude_patterns)]
    
    print(f"找到 {len(md_files)} 个markdown文件")
    print("")
    
    processed = 0
    skipped = 0
    errors = 0
    
    for md_file in sorted(md_files):
        try:
            if process_file(md_file):
                processed += 1
            else:
                skipped += 1
        except Exception as e:
            print(f"  错误：处理文件时出错 - {e}")
            errors += 1
    
    print(f"\n{'='*60}")
    print(f"处理完成：")
    print(f"  - 成功处理：{processed} 个文件")
    print(f"  - 跳过：{skipped} 个文件")
    print(f"  - 错误：{errors} 个文件")
    print(f"{'='*60}")

if __name__ == '__main__':
    main()
