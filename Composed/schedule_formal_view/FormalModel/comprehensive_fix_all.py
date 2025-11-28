#!/usr/bin/env python3
"""
全面修复所有Markdown文件的目录结构和章节编号
"""
import os
import re
from pathlib import Path
from typing import List, Tuple, Dict

def extract_all_headings(content: str) -> List[Tuple[int, str, str]]:
    """提取所有标题"""
    headings = []
    lines = content.split('\n')
    
    for line in lines:
        match = re.match(r'^(#{1,6})\s+(.+)$', line)
        if match:
            level = len(match.group(1))
            text = match.group(2).strip()
            # 移除编号（如果存在）
            text_clean = re.sub(r'^\d+\.?\d*\.?\d*\.?\d*\.?\s*', '', text)
            # 生成锚点ID
            anchor = re.sub(r'[^\w\s-]', '', text_clean.lower())
            anchor = re.sub(r'[-\s]+', '-', anchor)
            anchor = anchor.strip('-')
            headings.append((level, text, anchor))
    
    return headings

def generate_clean_toc(headings: List[Tuple[int, str, str]], start_level: int = 2) -> str:
    """生成干净的目录结构"""
    toc_lines = []
    
    for level, text, anchor in headings:
        if level < start_level:
            continue
        
        indent = (level - start_level) * 2
        toc_line = ' ' * indent + f'- [{text}](#{anchor})'
        toc_lines.append(toc_line)
    
    return '\n'.join(toc_lines)

def fix_file_comprehensive(file_path: str) -> bool:
    """全面修复单个文件"""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
    except Exception as e:
        print(f"错误: 无法读取文件 {file_path}: {e}")
        return False
    
    # 查找目录部分
    toc_pattern = r'(## 📋 目录\s*\n\n)(.*?)(\n\n---)'
    match = re.search(toc_pattern, content, re.DOTALL)
    
    if not match:
        return True  # 没有目录，跳过
    
    # 提取所有标题
    headings = extract_all_headings(content)
    
    if len(headings) < 2:
        return True  # 标题太少，跳过
    
    # 生成新目录
    new_toc = generate_clean_toc(headings, start_level=2)
    
    # 替换目录部分
    new_content = content[:match.start(1)] + match.group(1) + new_toc + match.group(3) + content[match.end(3):]
    
    # 写回文件
    try:
        with open(file_path, 'w', encoding='utf-8') as f:
            f.write(new_content)
        return True
    except Exception as e:
        print(f"错误: 无法写入文件 {file_path}: {e}")
        return False

def main():
    """主函数"""
    base_dir = Path(__file__).parent
    md_files = []
    
    exclude_files = ['schedule_model.md', 'README.md', 'fix_toc_structure.py', 
                     'fix_section_numbering.py', 'remove_duplicate_sections.py',
                     'comprehensive_fix_all.py', '内容对比检查报告.md',
                     '文件拆分完成总结.md', '文件拆分进度报告.md']
    
    for root, dirs, files in os.walk(base_dir):
        for file in files:
            if file.endswith('.md') and file not in exclude_files:
                file_path = os.path.join(root, file)
                md_files.append(file_path)
    
    print(f"找到 {len(md_files)} 个Markdown文件")
    print("开始全面修复目录结构...\n")
    
    fixed_count = 0
    
    for file_path in sorted(md_files):
        rel_path = os.path.relpath(file_path, base_dir)
        if fix_file_comprehensive(file_path):
            print(f"✅ 已修复: {rel_path}")
            fixed_count += 1
    
    print(f"\n完成！成功修复: {fixed_count} 个文件")

if __name__ == '__main__':
    main()
