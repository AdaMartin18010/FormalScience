#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
批量修复broken_links_report.txt中报告的链接问题
"""

import os
import re
import sys
from pathlib import Path

# 目录映射表（错误的路径 -> 正确的路径）
DIRECTORY_MAPPING = {
    "01_Type_Theory": "04_Type_Theory",
    "02_Control_Theory": "07_Control_Theory", 
    "03_Formal_Language": "03_Formal_Language_Theory",
    "04_Petri_Net_Theory": "05_Formal_Model_Theory/06.3_Petri_Net_Theory",
    "05_Distributed_Systems_Theory": "11_Distributed_Systems_Theory",
    "06_Mathematics": "02_Mathematical_Foundations",
    "07_Philosophy_of_Science": "01_Philosophical_Foundations/01.1_Philosophy_of_Science",
    "08_Software_Engineering": "09_Software_Engineering_Theory",
    "09_Programming_Language_Theory": "08_Programming_Language_Theory",
    "10_Formal_Model_Theory": "05_Formal_Model_Theory"
}

def fix_links_in_file(file_path):
    """修复单个文件中的链接"""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        original_content = content
        
        # 修复目录路径
        for old_path, new_path in DIRECTORY_MAPPING.items():
            # 修复相对路径链接
            pattern = rf'\[([^\]]+)\]\(\.?/?{old_path}([^)]*)\)'
            replacement = rf'[\1]({new_path}\2)'
            content = re.sub(pattern, replacement, content)
            
            # 修复绝对路径链接
            pattern = rf'\[([^\]]+)\]\(\.?/?docs/Refactor/{old_path}([^)]*)\)'
            replacement = rf'[\1]({new_path}\2)'
            content = re.sub(pattern, replacement, content)
        
        # 如果内容有变化，写回文件
        if content != original_content:
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(content)
            print(f"✅ 已修复: {file_path}")
            return True
        else:
            print(f"⏭️  无需修复: {file_path}")
            return False
            
    except Exception as e:
        print(f"❌ 修复失败: {file_path} - {e}")
        return False

def scan_and_fix_directory(directory_path):
    """扫描目录并修复所有markdown文件中的链接"""
    fixed_count = 0
    total_count = 0
    
    for root, dirs, files in os.walk(directory_path):
        for file in files:
            if file.endswith('.md'):
                file_path = os.path.join(root, file)
                total_count += 1
                if fix_links_in_file(file_path):
                    fixed_count += 1
    
    print(f"\n📊 修复统计:")
    print(f"   总文件数: {total_count}")
    print(f"   修复文件数: {fixed_count}")
    print(f"   修复率: {fixed_count/total_count*100:.1f}%")

def main():
    """主函数"""
    refactor_dir = Path(".")
    
    if not refactor_dir.exists():
        print("❌ 错误: 当前目录不存在")
        sys.exit(1)
    
    print("🔧 开始批量修复broken_links_report.txt中报告的链接问题...")
    print(f"📁 扫描目录: {refactor_dir}")
    
    scan_and_fix_directory(refactor_dir)
    
    print("\n✅ 链接修复完成!")

if __name__ == "__main__":
    main() 