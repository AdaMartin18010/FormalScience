#!/usr/bin/env python3
"""
全面修复Concept目录下Markdown文件的所有格式和结构问题
参考格式：Composed/formal_lang_view/01_核心概念映射/01.1_基本类型单元.md
"""

import os
import re
from pathlib import Path
from typing import List, Tuple

def extract_file_number(filename):
    """从文件名提取编号，如 01.4_Meaning_Construction_Process.md -> 01.4"""
    match = re.match(r'(\d+\.\d+)_', filename)
    if match:
        return match.group(1)
    return None

def get_theme_from_path(filepath):
    """从文件路径推断主题"""
    parts = Path(filepath).parts
    if 'FormalLanguage_Perspective' in parts:
        return '形式语言视角'
    elif 'AI_model_Perspective' in parts:
        return 'AI模型视角'
    elif 'Software_Perspective' in parts:
        return '软件视角'
    elif 'Program_Algorithm_Perspective' in parts:
        return '程序算法视角'
    elif 'Information_Theory_Perspective' in parts:
        return '信息论视角'
    elif 'Wasm_Perspective' in parts:
        return 'Wasm视角'
    else:
        return '形式语言视角'  # 默认值

def extract_title_from_filename(filename):
    """从文件名提取标题"""
    match = re.match(r'\d+\.\d+_(.+)\.md', filename)
    if match:
        title = match.group(1).replace('_', ' ')
        # 简化标题
        title = re.sub(r':.*$', '', title)
        title = re.sub(r'：.*$', '', title)
        return title
    return None

def fix_duplicate_metadata(content):
    """修复重复的元数据"""
    lines = content.split('\n')
    result = []
    seen_subtopic = False
    seen_theme = False
    i = 0
    
    while i < len(lines):
        line = lines[i]
        
        # 检查是否是重复的元数据
        if re.match(r'> \*\*子主题编号\*\*:', line):
            if not seen_subtopic:
                result.append(line)
                seen_subtopic = True
            # 跳过重复的
            i += 1
            continue
        elif re.match(r'> \*\*主题\*\*:', line):
            if not seen_theme:
                result.append(line)
                seen_theme = True
            # 跳过重复的
            i += 1
            continue
        else:
            result.append(line)
            i += 1
    
    return '\n'.join(result)

def fix_title_format(content, filepath):
    """修复标题格式"""
    filename = Path(filepath).name
    file_number = extract_file_number(filename)
    title_text = extract_title_from_filename(filename)
    
    if not file_number or not title_text:
        return content
    
    # 生成新标题：去掉前导零，如 01.4 -> 1.4
    clean_number = file_number.lstrip('0').lstrip('.')
    if not clean_number:
        clean_number = file_number
    
    new_title = f"# {clean_number} {title_text}"
    
    # 替换第一行的标题
    content = re.sub(r'^# .+$', new_title, content, count=1, flags=re.MULTILINE)
    
    return content

def fix_metadata(content, filepath):
    """修复元数据格式"""
    filename = Path(filepath).name
    file_number = extract_file_number(filename)
    theme = get_theme_from_path(filepath)
    
    if not file_number:
        return content
    
    new_metadata = f"> **子主题编号**: {file_number}\n> **主题**: {theme}"
    
    # 先删除所有现有的子主题编号和主题行
    content = re.sub(r'> \*\*子主题编号\*\*:.*\n', '', content)
    content = re.sub(r'> \*\*主题\*\*:.*\n', '', content)
    
    # 查找标题后的位置插入元数据
    # 在标题后、第一个空行前插入
    pattern = r'(^# .+$\n)(\n)?'
    replacement = rf'\1\n{new_metadata}\n'
    
    if not re.search(r'> \*\*子主题编号\*\*:', content):
        content = re.sub(pattern, replacement, content, count=1, flags=re.MULTILINE)
    
    return content

def fix_section_numbers(content):
    """修复章节编号格式，去掉空格"""
    # 修复 ## 数字 . 标题 格式为 ## 数字 标题
    content = re.sub(r'^## (\d+) \. ', r'## \1 ', content, flags=re.MULTILINE)
    # 修复 ### 数字 . 标题
    content = re.sub(r'^### (\d+) \. ', r'### \1 ', content, flags=re.MULTILINE)
    return content

def fix_toc_structure(content):
    """修复目录结构"""
    # 查找目录部分
    toc_start = content.find('## 📋 目录')
    if toc_start == -1:
        toc_start = content.find('## 目录')
    if toc_start == -1:
        return content
    
    # 找到目录结束位置（下一个##标题）
    toc_end = content.find('\n## ', toc_start + 10)
    if toc_end == -1:
        toc_end = len(content)
    
    toc_section = content[toc_start:toc_end]
    rest = content[toc_end:]
    
    # 修复目录中的链接格式
    # 将 [标题](#链接) 格式统一
    def fix_toc_link(match):
        full_link = match.group(0)
        # 如果链接格式正确，保持原样
        if re.search(r'\(#[^\)]+\)', full_link):
            return full_link
        return full_link
    
    # 简化：保持目录原样，只修复明显的错误
    # 主要问题在章节编号，目录会在章节修复后自动更新
    
    return content

def fix_duplicate_section_numbers(content):
    """修复重复的章节编号"""
    lines = content.split('\n')
    result = []
    section_counter = {}  # 跟踪每个级别的计数器
    
    for line in lines:
        # 检查是否是章节标题
        match = re.match(r'^(#{1,6})\s+(\d+)(\.\d+)*\s+(.+)$', line)
        if match:
            level = len(match.group(1))
            number_part = match.group(2)
            title = match.group(4)
            
            # 重置下级计数器
            for l in range(level + 1, 7):
                section_counter[l] = 0
            
            # 更新当前级别计数器
            if level not in section_counter:
                section_counter[level] = 0
            section_counter[level] += 1
            
            # 生成新的编号
            if level == 2:  # ## 级别
                new_number = str(section_counter[level])
                new_line = f"## {new_number} {title}"
            elif level == 3:  # ### 级别
                parent_num = section_counter.get(2, 1)
                new_number = f"{parent_num}.{section_counter[level]}"
                new_line = f"### {new_number} {title}"
            elif level == 4:  # #### 级别
                parent_num = section_counter.get(2, 1)
                sub_num = section_counter.get(3, 1)
                new_number = f"{parent_num}.{sub_num}.{section_counter[level]}"
                new_line = f"#### {new_number} {title}"
            else:
                new_line = line
            
            result.append(new_line)
        else:
            result.append(line)
    
    return '\n'.join(result)

def process_file(filepath):
    """处理单个文件"""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
        
        original_content = content
        
        # 1. 修复重复的元数据
        content = fix_duplicate_metadata(content)
        
        # 2. 修复标题格式
        content = fix_title_format(content, filepath)
        
        # 3. 修复元数据
        content = fix_metadata(content, filepath)
        
        # 4. 修复章节编号格式（去掉空格）
        content = fix_section_numbers(content)
        
        # 注意：不自动修复章节编号重复，因为这可能破坏现有结构
        # 需要人工检查
        
        if content != original_content:
            with open(filepath, 'w', encoding='utf-8') as f:
                f.write(content)
            print(f"✓ 已修复: {filepath}")
            return True
        else:
            print(f"- 无需修复: {filepath}")
            return False
    except Exception as e:
        print(f"✗ 错误处理 {filepath}: {e}")
        import traceback
        traceback.print_exc()
        return False

def main():
    """主函数"""
    base_dir = Path(__file__).parent
    
    # 查找所有需要处理的文件
    pattern = re.compile(r'^\d+\.\d+_.+\.md$')
    files_to_fix = []
    
    for root, dirs, files in os.walk(base_dir):
        # 跳过某些目录
        if 'node_modules' in root or '.git' in root:
            continue
        
        for file in files:
            if pattern.match(file):
                filepath = Path(root) / file
                files_to_fix.append(filepath)
    
    print(f"找到 {len(files_to_fix)} 个文件需要检查...\n")
    
    fixed_count = 0
    for filepath in sorted(files_to_fix):
        if process_file(filepath):
            fixed_count += 1
    
    print(f"\n完成！修复了 {fixed_count}/{len(files_to_fix)} 个文件")

if __name__ == '__main__':
    main()
