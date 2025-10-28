#!/usr/bin/env python3
"""
修复重复目录(TOC)的脚本
删除简略版目录，保留详细版目录
"""

import os
import re
from pathlib import Path

def fix_duplicate_toc(file_path):
    """修复单个文件的重复目录"""
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # 查找所有 "## 目录" 的位置
    toc_pattern = r'^## 目录.*?$'
    matches = list(re.finditer(toc_pattern, content, re.MULTILINE))
    
    if len(matches) <= 1:
        return False  # 没有重复,跳过
    
    print(f"处理: {file_path.name} - 发现{len(matches)}个目录")
    
    # 找到第一个目录的开始和结束位置
    # 第一个目录通常以 "## 目录 | Table of Contents" 开头
    # 紧跟着一个列表,然后是 "---" 分隔符
    
    # 找第一个目录的结束位置（查找第一个 "---" 后的 "## 目录"）
    first_toc_start = matches[0].start()
    
    # 找到第一个目录后的第一个 "---" 分隔符
    separator_pattern = r'^---\s*$'
    separators = list(re.finditer(separator_pattern, content[first_toc_start:], re.MULTILINE))
    
    if not separators:
        print(f"  警告: 未找到分隔符，跳过")
        return False
    
    # 第一个目录的结束位置是第一个分隔符之后
    first_toc_end = first_toc_start + separators[0].end()
    
    # 删除第一个目录及其分隔符
    new_content = content[:first_toc_start] + content[first_toc_end:]
    
    # 保存修改
    with open(file_path, 'w', encoding='utf-8') as f:
        f.write(new_content)
    
    print(f"  ✅ 已删除第一个目录")
    return True

def main():
    """主函数"""
    concept_dir = Path(__file__).parent.parent / "Concept" / "Information_Theory_Perspective"
    
    if not concept_dir.exists():
        print(f"错误: 目录不存在: {concept_dir}")
        return
    
    fixed_count = 0
    total_count = 0
    
    # 遍历所有章节目录
    for chapter_dir in sorted(concept_dir.glob("*_*")):
        if not chapter_dir.is_dir():
            continue
        
        print(f"\n检查章节: {chapter_dir.name}")
        
        # 遍历该章节下的所有md文件
        for md_file in sorted(chapter_dir.glob("*.md")):
            if not re.match(r'^\d+\.\d+', md_file.name):
                continue  # 跳过非章节文件
            
            total_count += 1
            if fix_duplicate_toc(md_file):
                fixed_count += 1
    
    print(f"\n\n总结:")
    print(f"  检查文件: {total_count}")
    print(f"  修复文件: {fixed_count}")
    print(f"  完成率: {fixed_count/total_count*100:.1f}%")

if __name__ == "__main__":
    main()

