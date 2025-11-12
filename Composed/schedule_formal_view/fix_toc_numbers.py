#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
修复目录编号，确保目录中的编号与内容中的标题编号一致
子主题编号从1开始，不包含文件编号前缀
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
    # 转换为小写，替换空格为连字符，移除特殊字符
    anchor = text.lower()
    anchor = re.sub(r'[^\w\s-]', '', anchor)
    anchor = re.sub(r'\s+', '-', anchor)
    return anchor

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
        
        # 匹配标题，如 ## 1 执行引擎 或 ## 1.1 超标量流水线
        match = re.match(r'(#{2,})\s+(\d+(?:\.\d+)*)\s+(.+?)$', line)
        if match:
            level = len(match.group(1))
            number = match.group(2)
            title = match.group(3)
            headers.append((level, number, title))
    
    return headers

def fix_toc_with_headers(toc_lines, content_headers):
    """根据内容标题修复目录"""
    fixed_lines = []
    header_index = 0
    
    for line in toc_lines:
        # 跳过空行和目录标题
        if not line.strip() or line.strip() == '## 📋 目录' or line.strip().startswith('- [📋 目录]'):
            fixed_lines.append(line)
            continue
        
        # 匹配目录项，如 - [1 执行引擎](#1-执行引擎) 或 - [执行引擎](#执行引擎)
        match = re.match(r'(\s*)- \[(.+?)\]\(#(.+?)\)', line)
        if match:
            indent = match.group(1)
            title_text = match.group(2)
            old_anchor = match.group(3)
            
            # 计算缩进级别
            indent_level = len(indent) // 2
            
            # 找到对应的标题
            if header_index < len(content_headers):
                level, number, title = content_headers[header_index]
                
                # 如果缩进级别匹配，使用标题的编号
                if level == indent_level + 1:  # 目录缩进级别 + 1 = 标题级别
                    # 生成新的目录项
                    new_title = f"{number} {title}" if number else title
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

def process_file(filepath):
    """处理单个文件"""
    print(f"处理文件: {filepath}")
    
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # 提取内容中的标题
    content_headers = extract_content_headers(content)
    
    if not content_headers:
        print(f"  跳过：未找到标题")
        return False
    
    # 解析并修复目录
    toc_lines, toc_start, toc_end = parse_toc(content)
    if toc_lines:
        fixed_toc = fix_toc_with_headers(toc_lines, content_headers)
        
        # 替换目录
        lines = content.split('\n')
        new_lines = lines[:toc_start] + fixed_toc + lines[toc_end:]
        content = '\n'.join(new_lines)
        
        # 写回文件
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(content)
        
        print(f"  完成：已修复目录编号")
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
    exclude_patterns = ['README.md', '总览.md', '总结.md', '说明.md', '指南.md', '报告.md', '备份.md', 'fix_toc', 'simplify_toc', 'simplify_subsection', 'fix_anchors', 'fix_toc_numbers']
    md_files = [f for f in md_files if not any(p in f.name for p in exclude_patterns)]
    
    print(f"找到 {len(md_files)} 个markdown文件")
    
    processed = 0
    for md_file in sorted(md_files):
        if process_file(md_file):
            processed += 1
    
    print(f"\n处理完成：共处理 {processed} 个文件")

if __name__ == '__main__':
    main()
