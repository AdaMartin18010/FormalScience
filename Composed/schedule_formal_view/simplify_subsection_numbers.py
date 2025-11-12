#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
简化子主题编号
将子主题编号从文件编号前缀改为从1开始
例如：1.1.1 -> 1, 1.1.2 -> 2, 1.1.1.1 -> 1.1
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

def generate_anchor(title):
    """生成锚点链接（基于标题）"""
    # 转换为小写，替换空格为连字符，移除特殊字符
    anchor = title.lower()
    anchor = re.sub(r'[^\w\s-]', '', anchor)
    anchor = re.sub(r'\s+', '-', anchor)
    return anchor

def simplify_toc_line(line, file_num):
    """简化目录行，去掉文件编号前缀"""
    if not file_num:
        return line
    
    file_series, file_sub = file_num
    
    # 匹配目录项，如 - [1.1.1 执行引擎](#111-执行引擎)
    match = re.match(r'(\s*)- \[(\d+\.\d+(?:\.\d+)*)\s+(.+?)\]\(#(.+?)\)', line)
    if match:
        indent = match.group(1)
        number = match.group(2)
        title = match.group(3)
        anchor = match.group(4)
        
        # 简化编号
        simplified_number = simplify_number(number, file_num)
        
        # 如果简化后编号为空，只保留标题
        if simplified_number == number:
            # 编号没有文件前缀，保持原样
            return line
        
        # 生成新的锚点（基于简化后的标题）
        if simplified_number:
            new_title = f"{simplified_number} {title}"
        else:
            new_title = title
        
        new_anchor = generate_anchor(new_title)
        new_line = f"{indent}- [{new_title}](#{new_anchor})"
        return new_line
    
    return line

def simplify_toc(toc_lines, file_num):
    """简化整个目录"""
    simplified = []
    for line in toc_lines:
        simplified.append(simplify_toc_line(line, file_num))
    return simplified

def simplify_content_headers(content, file_num):
    """简化内容中的标题编号"""
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
        
        # 匹配标题，如 ## 1.1.1 执行引擎
        match = re.match(r'(#{2,})\s+(\d+\.\d+(?:\.\d+)*)\s+(.+?)$', line)
        if match:
            level = match.group(1)
            number = match.group(2)
            title = match.group(3)
            
            # 简化编号
            simplified_number = simplify_number(number, file_num)
            
            if simplified_number != number:
                # 编号被简化了
                if simplified_number:
                    new_line = f"{level} {simplified_number} {title}"
                else:
                    new_line = f"{level} {title}"
                fixed_lines.append(new_line)
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
    
    # 解析并简化目录
    toc_lines, toc_start, toc_end = parse_toc(content)
    if toc_lines:
        simplified_toc = simplify_toc(toc_lines, file_num)
        
        # 替换目录
        lines = content.split('\n')
        new_lines = lines[:toc_start] + simplified_toc + lines[toc_end:]
        content = '\n'.join(new_lines)
    
    # 简化内容中的标题编号
    content = simplify_content_headers(content, file_num)
    
    # 写回文件
    with open(filepath, 'w', encoding='utf-8') as f:
        f.write(content)
    
    print(f"  完成：已简化子主题编号")
    return True

def main():
    """主函数"""
    base_dir = Path(__file__).parent
    
    # 查找所有markdown文件
    md_files = list(base_dir.rglob('*.md'))
    
    # 排除README和总览文件
    exclude_patterns = ['README.md', '总览.md', '总结.md', '说明.md', '指南.md', '报告.md', '备份.md', 'fix_toc', 'simplify_toc', 'simplify_subsection']
    md_files = [f for f in md_files if not any(p in f.name for p in exclude_patterns)]
    
    print(f"找到 {len(md_files)} 个markdown文件")
    
    processed = 0
    for md_file in sorted(md_files):
        if process_file(md_file):
            processed += 1
    
    print(f"\n处理完成：共处理 {processed} 个文件")

if __name__ == '__main__':
    main()
