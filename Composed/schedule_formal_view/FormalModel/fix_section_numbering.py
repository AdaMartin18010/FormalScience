#!/usr/bin/env python3
"""
修复Markdown文件中的章节编号重复和不一致问题
"""
import os
import re
from pathlib import Path
from typing import List, Tuple, Dict

def fix_section_numbering(content: str) -> str:
    """修复章节编号，确保连续且不重复"""
    lines = content.split('\n')
    result = []
    section_counters = {}  # 每个级别的计数器 {level: counter}
    
    i = 0
    while i < len(lines):
        line = lines[i]
        
        # 匹配Markdown标题
        match = re.match(r'^(#{2,6})\s+(\d+\.?\d*\.?\d*\.?\d*)\s*(.+)$', line)
        if match:
            level = len(match.group(1))
            old_number = match.group(2)
            title = match.group(3).strip()
            
            # 初始化计数器
            if level not in section_counters:
                section_counters[level] = 0
            
            # 重置子级计数器
            for l in range(level + 1, 7):
                if l in section_counters:
                    section_counters[l] = 0
            
            # 生成新编号
            if level == 2:  # ## 级别
                section_counters[level] += 1
                new_number = str(section_counters[level])
            elif level == 3:  # ### 级别
                parent_num = section_counters.get(level - 1, 1)
                section_counters[level] += 1
                new_number = f"{parent_num}.{section_counters[level]}"
            elif level == 4:  # #### 级别
                parent_level_2 = section_counters.get(level - 2, 1)
                parent_level_3 = section_counters.get(level - 1, 1)
                section_counters[level] += 1
                new_number = f"{parent_level_2}.{parent_level_3}.{section_counters[level]}"
            else:
                # 保持原样
                new_number = old_number
            
            # 替换编号
            new_line = f"{'#' * level} {new_number}. {title}"
            result.append(new_line)
        else:
            result.append(line)
        
        i += 1
    
    return '\n'.join(result)

def fix_file_numbering(file_path: str) -> bool:
    """修复单个文件的章节编号"""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
    except Exception as e:
        print(f"错误: 无法读取文件 {file_path}: {e}")
        return False
    
    # 跳过目录部分（在第一个---之后才开始修复）
    parts = content.split('\n---\n', 1)
    if len(parts) < 2:
        return False
    
    header = parts[0]
    body = parts[1]
    
    # 修复正文部分的编号
    fixed_body = fix_section_numbering(body)
    
    # 重新组合
    new_content = header + '\n---\n' + fixed_body
    
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
    
    # 收集所有Markdown文件（排除特定文件）
    exclude_files = ['schedule_model.md', 'README.md', 'fix_toc_structure.py', 
                     'fix_section_numbering.py', '内容对比检查报告.md',
                     '文件拆分完成总结.md', '文件拆分进度报告.md']
    
    for root, dirs, files in os.walk(base_dir):
        for file in files:
            if file.endswith('.md') and file not in exclude_files:
                file_path = os.path.join(root, file)
                md_files.append(file_path)
    
    print(f"找到 {len(md_files)} 个Markdown文件")
    print("开始修复章节编号...\n")
    
    fixed_count = 0
    failed_count = 0
    
    for file_path in sorted(md_files):
        rel_path = os.path.relpath(file_path, base_dir)
        if fix_file_numbering(file_path):
            print(f"✅ 已修复: {rel_path}")
            fixed_count += 1
        else:
            print(f"❌ 修复失败: {rel_path}")
            failed_count += 1
    
    print(f"\n完成！成功: {fixed_count}, 失败: {failed_count}")
    print("\n注意: 修复后需要重新运行 fix_toc_structure.py 来更新目录")

if __name__ == '__main__':
    main()
