#!/usr/bin/env python3
"""
修复所有Markdown文件的目录结构和章节编号一致性问题
"""
import os
import re
from pathlib import Path
from typing import List, Tuple, Dict

def extract_headings(content: str) -> List[Tuple[int, str, str]]:
    """提取所有标题，返回(级别, 标题文本, 锚点ID)"""
    headings = []
    lines = content.split('\n')
    
    for line in lines:
        # 匹配Markdown标题
        match = re.match(r'^(#{1,6})\s+(.+)$', line)
        if match:
            level = len(match.group(1))
            text = match.group(2).strip()
            # 生成锚点ID（Markdown标准方式）
            anchor = re.sub(r'[^\w\s-]', '', text.lower())
            anchor = re.sub(r'[-\s]+', '-', anchor)
            anchor = anchor.strip('-')
            headings.append((level, text, anchor))
    
    return headings

def generate_toc(headings: List[Tuple[int, str, str]], start_level: int = 2) -> str:
    """生成目录结构"""
    toc_lines = []
    indent_stack = [0]  # 缩进级别栈
    
    for level, text, anchor in headings:
        # 跳过文件标题（level 1）
        if level < start_level:
            continue
        
        # 计算缩进
        current_indent = (level - start_level) * 2
        
        # 生成目录项
        toc_line = ' ' * current_indent + f'- [{text}](#{anchor})'
        toc_lines.append(toc_line)
    
    return '\n'.join(toc_lines)

def fix_file_toc(file_path: str) -> bool:
    """修复单个文件的目录结构"""
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
        print(f"警告: {file_path} 中没有找到目录部分")
        return False
    
    # 提取所有标题
    headings = extract_headings(content)
    
    if len(headings) < 2:
        print(f"警告: {file_path} 中标题太少")
        return False
    
    # 生成新目录
    new_toc = generate_toc(headings, start_level=2)
    
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
    """主函数：遍历所有Markdown文件并修复"""
    base_dir = Path(__file__).parent
    md_files = []
    
    # 收集所有Markdown文件（排除schedule_model.md和README.md）
    for root, dirs, files in os.walk(base_dir):
        for file in files:
            if file.endswith('.md') and file not in ['schedule_model.md', 'README.md']:
                file_path = os.path.join(root, file)
                md_files.append(file_path)
    
    print(f"找到 {len(md_files)} 个Markdown文件")
    print("开始修复目录结构...\n")
    
    fixed_count = 0
    failed_count = 0
    
    for file_path in sorted(md_files):
        rel_path = os.path.relpath(file_path, base_dir)
        if fix_file_toc(file_path):
            print(f"✅ 已修复: {rel_path}")
            fixed_count += 1
        else:
            print(f"❌ 修复失败: {rel_path}")
            failed_count += 1
    
    print(f"\n完成！成功: {fixed_count}, 失败: {failed_count}")

if __name__ == '__main__':
    main()
