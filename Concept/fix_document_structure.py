#!/usr/bin/env python3
"""
批量修复Concept目录下Markdown文件的标题格式、元数据和章节编号
参考格式：Composed/formal_lang_view/01_核心概念映射/01.1_基本类型单元.md
"""

import os
import re
from pathlib import Path

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

def fix_title_and_metadata(content, filepath):
    """修复标题和元数据"""
    filename = Path(filepath).name
    file_number = extract_file_number(filename)
    
    if not file_number:
        return content
    
    # 提取标题（去掉编号和扩展名）
    title_match = re.match(r'(\d+\.\d+)_(.+)\.md', filename)
    if title_match:
        title_text = title_match.group(2).replace('_', ' ')
        # 简化标题，只保留核心部分
        title_text = re.sub(r':.*$', '', title_text)  # 去掉冒号后的内容
        title_text = re.sub(r'：.*$', '', title_text)  # 去掉中文冒号后的内容
        new_title = f"# {file_number.replace('0', '').lstrip('.')} {title_text}"
    else:
        new_title = f"# {file_number.replace('0', '').lstrip('.')}"
    
    theme = get_theme_from_path(filepath)
    
    # 准备新的元数据
    new_metadata = f"> **子主题编号**: {file_number}\n> **主题**: {theme}\n"
    
    # 修复标题
    content = re.sub(r'^# .+$', new_title, content, count=1, flags=re.MULTILINE)
    
    # 修复元数据
    # 先检查是否已经有子主题编号，如果有就跳过
    if re.search(r'> \*\*\*子主题编号\*\*:', content):
        # 已经修复过，跳过
        pass
    # 查找现有的元数据块（文档版本或其他格式）
    elif re.search(r'> \*\*文档版本\*\*:', content):
        # 替换文档版本为子主题编号和主题
        content = re.sub(
            r'> \*\*文档版本\*\*:.*?\n',
            new_metadata,
            content,
            count=1
        )
    elif re.search(r'> \*\*子主题编号\*\*:', content):
        # 如果已经有子主题编号但格式不对，更新它
        content = re.sub(
            r'> \*\*子主题编号\*\*:.*?\n> \*\*主题\*\*:.*?\n',
            new_metadata,
            content,
            count=1
        )
    else:
        # 如果没有元数据，在标题后添加
        content = re.sub(
            r'(^# .+$\n)',
            rf'\1\n{new_metadata}',
            content,
            count=1,
            flags=re.MULTILINE
        )
    
    return content

def fix_section_numbers(content):
    """修复章节编号格式，去掉空格"""
    # 修复 ## 数字 . 标题 格式为 ## 数字 标题
    content = re.sub(r'^## (\d+) \. ', r'## \1 ', content, flags=re.MULTILINE)
    return content

def fix_toc_links(content):
    """修复目录中的链接"""
    # 修复目录中的章节链接格式
    content = re.sub(
        r'- \[(\d+) \. ([^\]]+)\]\(#\d+--[^\)]+\)',
        r'- [\1 \2](#\1-\2)',
        content
    )
    # 简化链接锚点生成
    def make_anchor(text):
        # 移除编号和空格，生成锚点
        text = re.sub(r'^\d+\.?\s*', '', text)
        text = text.lower().replace(' ', '-').replace('：', '').replace(':', '')
        return re.sub(r'[^\w\-]', '', text)
    
    return content

def process_file(filepath):
    """处理单个文件"""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
        
        original_content = content
        
        # 修复标题和元数据
        content = fix_title_and_metadata(content, filepath)
        
        # 修复章节编号
        content = fix_section_numbers(content)
        
        # 修复目录链接（如果需要）
        # content = fix_toc_links(content)
        
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
    
    print(f"找到 {len(files_to_fix)} 个文件需要检查...")
    
    fixed_count = 0
    for filepath in files_to_fix:
        if process_file(filepath):
            fixed_count += 1
    
    print(f"\n完成！修复了 {fixed_count}/{len(files_to_fix)} 个文件")

if __name__ == '__main__':
    main()
