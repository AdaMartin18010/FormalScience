#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
批判性分析补充工具
用于自动化批判性分析内容的补充

用法:
    python 批判性分析补充工具.py [--check] [--apply] [directory]

参数:
    --check     只检查缺失批判性分析的文件，不进行修改
    --apply     应用模板补充批判性分析内容
    directory   要处理的目录（默认为当前目录）
"""

import os
import re
import sys
import argparse
from pathlib import Path

# 批判性分析部分标记
CRITICAL_ANALYSIS_MARKER = re.compile(r'^#+\s*批判性分析', re.MULTILINE)
# 批判性分析占位符
PLACEHOLDER_PATTERN = re.compile(r'#+\s*批判性分析\s*\n+\s*-\s*本节内容待补充.*', re.MULTILINE | re.DOTALL)
# 文档结尾模式
DOC_END_PATTERN = re.compile(r'\n*$')

# 批判性分析模板路径
TEMPLATE_PATH = 'docs/Refactor/批判性分析模板.md'

def load_template():
    """加载批判性分析模板"""
    try:
        with open(TEMPLATE_PATH, 'r', encoding='utf-8') as f:
            content = f.read()
            # 提取模板主体内容（去掉标题和使用说明）
            template_parts = content.split('## 使用说明')
            if len(template_parts) > 1:
                return template_parts[0].strip()
            return content.strip()
    except FileNotFoundError:
        print(f"错误: 找不到模板文件 {TEMPLATE_PATH}")
        return None

def customize_template(template, file_path):
    """根据文件内容定制模板"""
    # 从文件名提取主题
    topic = os.path.basename(file_path).replace('.md', '').split('_')[-1]
    
    # 读取文件内容以获取更多上下文
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
            
        # 提取标题（如果有）
        title_match = re.search(r'^#\s+(.+)$', content, re.MULTILINE)
        if title_match:
            topic = title_match.group(1)
        
        # 简单替换模板中的通用术语
        template = template.replace('本主题', f'"{topic}"')
        
        return template
    except Exception as e:
        print(f"警告: 定制模板时出错: {e}")
        return template

def find_markdown_files(directory):
    """查找指定目录下的所有Markdown文件"""
    md_files = []
    for root, _, files in os.walk(directory):
        for file in files:
            if file.endswith('.md') and not file.startswith('README') and not file == '批判性分析模板.md':
                md_files.append(os.path.join(root, file))
    return md_files

def check_critical_analysis(file_path):
    """检查文件是否缺少批判性分析部分"""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
            
        # 检查是否有批判性分析部分
        if CRITICAL_ANALYSIS_MARKER.search(content):
            # 检查是否只有占位符
            if PLACEHOLDER_PATTERN.search(content):
                return "placeholder"
            return "exists"
        return "missing"
    except Exception as e:
        print(f"警告: 检查文件时出错 {file_path}: {e}")
        return "error"

def apply_template(file_path, template):
    """应用模板到文件"""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # 定制模板
        customized_template = customize_template(template, file_path)
        
        # 如果有占位符，替换占位符
        if PLACEHOLDER_PATTERN.search(content):
            new_content = PLACEHOLDER_PATTERN.sub(f'## 批判性分析\n\n{customized_template}', content)
        else:
            # 否则添加到文件末尾
            new_content = DOC_END_PATTERN.sub(f'\n\n## 批判性分析\n\n{customized_template}\n', content)
        
        # 写回文件
        with open(file_path, 'w', encoding='utf-8') as f:
            f.write(new_content)
        
        return True
    except Exception as e:
        print(f"错误: 应用模板时出错 {file_path}: {e}")
        return False

def main():
    parser = argparse.ArgumentParser(description='批判性分析补充工具')
    parser.add_argument('--check', action='store_true', help='只检查缺失批判性分析的文件')
    parser.add_argument('--apply', action='store_true', help='应用模板补充批判性分析内容')
    parser.add_argument('directory', nargs='?', default='.', help='要处理的目录')
    
    args = parser.parse_args()
    
    # 加载模板
    template = load_template()
    if not template and args.apply:
        print("错误: 无法应用模板，因为模板加载失败")
        return
    
    # 查找所有Markdown文件
    md_files = find_markdown_files(args.directory)
    print(f"找到 {len(md_files)} 个Markdown文件")
    
    # 检查文件
    missing_files = []
    placeholder_files = []
    
    for file in md_files:
        status = check_critical_analysis(file)
        if status == "missing":
            missing_files.append(file)
            print(f"缺失: {file}")
        elif status == "placeholder":
            placeholder_files.append(file)
            print(f"占位符: {file}")
    
    print(f"\n总计: {len(missing_files)} 个文件缺失批判性分析, {len(placeholder_files)} 个文件有占位符")
    
    # 应用模板
    if args.apply:
        applied_count = 0
        
        # 先处理有占位符的文件
        for file in placeholder_files:
            print(f"应用模板到: {file}")
            if apply_template(file, template):
                applied_count += 1
        
        # 再处理缺失的文件
        for file in missing_files:
            print(f"应用模板到: {file}")
            if apply_template(file, template):
                applied_count += 1
        
        print(f"\n成功应用模板到 {applied_count} 个文件")

if __name__ == '__main__':
    main() 