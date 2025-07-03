#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
脚本名称：link_fixer.py
用途：批量修复知识库中的 Markdown 链接错误。
用法：python link_fixer.py [参数]
主要参数：
    --dry-run      仅检查不修改
    --fix          自动修复链接
说明：请根据实际需求扩展功能，并配合 Meta/README.md 说明文档使用。

链接修复工具 (Link Fixer)
用于检测和修复Markdown文件中的断链问题

用法:
    python link_fixer.py [--fix] [--report] [directory]

参数:
    --fix       执行修复操作（默认只检测不修复）
    --report    生成断链报告
    directory   要处理的目录（默认为当前目录）
"""

import os
import re
import sys
import argparse
from pathlib import Path
from collections import defaultdict

# 链接正则表达式
MD_LINK_PATTERN = re.compile(r'\[([^\]]+)\]\(([^)]+)\)')
# 相对路径正则表达式
RELATIVE_PATH_PATTERN = re.compile(r'^(?!http|ftp|mailto)([^#]+)(?:#.*)?$')

# 目录映射表（旧路径 -> 新路径）
DIRECTORY_MAPPING = {
    # 示例：旧目录结构到新目录结构的映射
    "01_Type_Theory": "05_Type_Theory",
    "02_Control_Theory": "03_Control_Theory",
    "03_Formal_Language": "04_Formal_Language_Theory",
    "04_Petri_Net_Theory": "06_Formal_Model_Theory/06.3_Petri_Net_Theory",
    "05_Distributed_Systems_Theory": "10_Distributed_Systems_Theory",
    "06_Mathematics": "02_Mathematical_Foundations",
    "07_Philosophy_of_Science": "01_Philosophical_Foundations/01.1_Philosophy_of_Science",
    "08_Software_Engineering": "08_Software_Engineering_Theory",
    "09_Programming_Language_Theory": "07_Programming_Language_Theory",
    "10_Formal_Model_Theory": "06_Formal_Model_Theory",
    "12_Context_System": "16_Cross_Domain_Synthesis",
    "13_Context_System": "16_Cross_Domain_Synthesis"
}

# 文件映射表（旧文件名 -> 新文件名）
FILE_MAPPING = {
    # 示例：旧文件名到新文件名的映射
    "统一目录结构规范.md": "目录编号规范化执行方案_20250117.md",
    "重构执行计划_20250115.md": "目录编号规范化执行方案_20250117.md",
    "重构进度统计_20250110.md": "重构进度更新_20250117.md",
    "上下文管理规范.md": "16_Cross_Domain_Synthesis/Context_Management_Specification.md",
    "上下文系统架构.md": "16_Cross_Domain_Synthesis/Architecture.md",
}

def find_markdown_files(directory):
    """查找指定目录下的所有Markdown文件"""
    md_files = []
    for root, _, files in os.walk(directory):
        for file in files:
            if file.endswith('.md'):
                md_files.append(os.path.join(root, file))
    return md_files

def check_link_exists(base_dir, link_path):
    """检查链接是否存在"""
    full_path = os.path.normpath(os.path.join(base_dir, link_path))
    return os.path.exists(full_path)

def fix_link(link, base_dir):
    """修复链接"""
    # 分离锚点
    if '#' in link:
        path, anchor = link.split('#', 1)
        anchor = '#' + anchor
    else:
        path = link
        anchor = ''
    
    # 检查目录映射
    for old_dir, new_dir in DIRECTORY_MAPPING.items():
        if path.startswith(old_dir + '/') or path == old_dir:
            path = path.replace(old_dir, new_dir, 1)
            break
    
    # 检查文件映射
    base_name = os.path.basename(path)
    if base_name in FILE_MAPPING:
        path = os.path.join(os.path.dirname(path), FILE_MAPPING[base_name])
    
    # 组合修复后的链接
    fixed_link = path + anchor
    
    # 检查修复后的链接是否存在
    if check_link_exists(base_dir, path):
        return fixed_link, True
    else:
        return fixed_link, False

def process_file(file_path, base_dir, fix_mode=False):
    """处理单个Markdown文件"""
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    broken_links = []
    fixed_links = []
    
    def replace_link(match):
        text = match.group(1)
        link = match.group(2)
        
        # 忽略外部链接
        if link.startswith(('http://', 'https://', 'ftp://', 'mailto:')):
            return match.group(0)
        
        # 检查相对路径链接
        relative_match = RELATIVE_PATH_PATTERN.match(link)
        if relative_match:
            path = relative_match.group(1)
            fixed_link, exists = fix_link(path, base_dir)
            
            if not exists:
                broken_links.append((link, fixed_link))
            else:
                fixed_links.append((link, fixed_link))
            
            # 如果启用修复模式，则替换链接
            if fix_mode:
                if '#' in link:
                    path, anchor = link.split('#', 1)
                    return f'[{text}]({fixed_link})'
                else:
                    return f'[{text}]({fixed_link})'
        
        return match.group(0)
    
    # 处理文件中的所有链接
    new_content = MD_LINK_PATTERN.sub(replace_link, content)
    
    # 如果启用修复模式且有修改，则写回文件
    if fix_mode and new_content != content:
        with open(file_path, 'w', encoding='utf-8') as f:
            f.write(new_content)
    
    return {
        'file': file_path,
        'broken_links': broken_links,
        'fixed_links': fixed_links
    }

def generate_report(results, output_file):
    """生成断链报告"""
    with open(output_file, 'w', encoding='utf-8') as f:
        for result in results:
            file_path = result['file']
            broken_links = result['broken_links']
            
            if broken_links:
                for old_link, new_link in broken_links:
                    f.write(f"{file_path} -> {old_link} (建议修改为: {new_link})\n")

def main():
    parser = argparse.ArgumentParser(description='链接修复工具')
    parser.add_argument('--fix', action='store_true', help='执行修复操作')
    parser.add_argument('--report', action='store_true', help='生成断链报告')
    parser.add_argument('directory', nargs='?', default='.', help='要处理的目录')
    
    args = parser.parse_args()
    
    # 获取基础目录的绝对路径
    base_dir = os.path.abspath(args.directory)
    
    # 查找所有Markdown文件
    md_files = find_markdown_files(args.directory)
    print(f"找到 {len(md_files)} 个Markdown文件")
    
    # 处理文件
    results = []
    for file in md_files:
        result = process_file(file, base_dir, args.fix)
        results.append(result)
        
        # 输出进度
        broken_count = len(result['broken_links'])
        fixed_count = len(result['fixed_links'])
        
        if broken_count > 0 or fixed_count > 0:
            print(f"{file}: 发现 {broken_count} 个断链, 修复 {fixed_count} 个链接")
    
    # 统计结果
    total_broken = sum(len(r['broken_links']) for r in results)
    total_fixed = sum(len(r['fixed_links']) for r in results)
    
    print(f"\n总计: 发现 {total_broken} 个断链, 修复 {total_fixed} 个链接")
    
    # 生成报告
    if args.report:
        report_file = os.path.join(base_dir, 'link_fix_report.txt')
        generate_report(results, report_file)
        print(f"报告已生成: {report_file}")

if __name__ == '__main__':
    main() 