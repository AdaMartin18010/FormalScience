#!/usr/bin/env python3
"""
删除Markdown文件中的重复章节，保留最新版本
"""
import os
import re
from pathlib import Path
from typing import List, Tuple, Dict, Set

def find_duplicate_sections(content: str) -> List[Tuple[str, int, int]]:
    """查找重复的章节标题"""
    lines = content.split('\n')
    section_titles = {}  # {title: [(start_line, end_line), ...]}
    current_section = None
    current_start = None
    
    for i, line in enumerate(lines):
        # 匹配章节标题（### 或 ####）
        match = re.match(r'^(#{3,4})\s+(\d+\.?\d*\.?\d*\.?\d*)\s*(.+)$', line)
        if match:
            level = len(match.group(1))
            number = match.group(2)
            title = match.group(3).strip()
            
            # 保存上一个章节
            if current_section:
                section_key = f"{current_section[0]}:{current_section[1]}"
                if section_key not in section_titles:
                    section_titles[section_key] = []
                section_titles[section_key].append((current_start, i - 1))
            
            # 开始新章节
            current_section = (number, title)
            current_start = i
    
    # 保存最后一个章节
    if current_section:
        section_key = f"{current_section[0]}:{current_section[1]}"
        if section_key not in section_titles:
            section_titles[section_key] = []
        section_titles[section_key].append((current_start, len(lines) - 1))
    
    # 找出重复的章节（同一标题出现多次）
    duplicates = []
    for key, positions in section_titles.items():
        if len(positions) > 1:
            # 保留最后一个，删除前面的
            for pos in positions[:-1]:
                duplicates.append((key, pos[0], pos[1]))
    
    return duplicates

def remove_duplicate_sections(file_path: str) -> bool:
    """删除文件中的重复章节"""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
    except Exception as e:
        print(f"错误: 无法读取文件 {file_path}: {e}")
        return False
    
    # 分离头部和正文
    parts = content.split('\n---\n', 1)
    if len(parts) < 2:
        return False
    
    header = parts[0]
    body = parts[1]
    
    # 查找重复章节
    duplicates = find_duplicate_sections(body)
    
    if not duplicates:
        return True  # 没有重复，无需修改
    
    # 从后往前删除（保持行号不变）
    lines = body.split('\n')
    lines_to_remove = set()
    
    for key, start, end in duplicates:
        for i in range(start, end + 1):
            lines_to_remove.add(i)
    
    # 重建内容
    new_lines = [line for i, line in enumerate(lines) if i not in lines_to_remove]
    new_body = '\n'.join(new_lines)
    
    # 重新组合
    new_content = header + '\n---\n' + new_body
    
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
    
    # 收集所有Markdown文件
    exclude_files = ['schedule_model.md', 'README.md', 'fix_toc_structure.py', 
                     'fix_section_numbering.py', 'remove_duplicate_sections.py',
                     '内容对比检查报告.md', '文件拆分完成总结.md', '文件拆分进度报告.md']
    
    for root, dirs, files in os.walk(base_dir):
        for file in files:
            if file.endswith('.md') and file not in exclude_files:
                file_path = os.path.join(root, file)
                md_files.append(file_path)
    
    print(f"找到 {len(md_files)} 个Markdown文件")
    print("开始删除重复章节...\n")
    
    fixed_count = 0
    no_duplicates = 0
    
    for file_path in sorted(md_files):
        rel_path = os.path.relpath(file_path, base_dir)
        if remove_duplicate_sections(file_path):
            # 检查是否真的有重复
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            parts = content.split('\n---\n', 1)
            if len(parts) >= 2:
                duplicates = find_duplicate_sections(parts[1])
                if duplicates:
                    print(f"✅ 已删除重复: {rel_path} ({len(duplicates)}个重复章节)")
                    fixed_count += 1
                else:
                    no_duplicates += 1
        else:
            print(f"❌ 处理失败: {rel_path}")
    
    print(f"\n完成！删除重复: {fixed_count}, 无重复: {no_duplicates}")
    print("\n注意: 删除重复后需要重新运行 fix_section_numbering.py 和 fix_toc_structure.py")

if __name__ == '__main__':
    main()
