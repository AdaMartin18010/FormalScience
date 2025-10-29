#!/usr/bin/env python3
"""
批量为 Program_Algorithm_Perspective 文档添加目录（TOC）
"""

import re
import os
from pathlib import Path
from typing import List, Tuple

def extract_headings(content: str) -> List[Tuple[int, str, str]]:
    """
    提取Markdown文档中的标题
    返回: [(level, title, anchor), ...]
    """
    headings = []
    lines = content.split('\n')
    
    for line in lines:
        # 匹配 Markdown 标题
        match = re.match(r'^(#{1,6})\s+(.+)$', line)
        if match:
            level = len(match.group(1))
            title = match.group(2).strip()
            
            # 跳过主标题（#）
            if level == 1:
                continue
            
            # 生成锚点
            anchor = title.lower()
            # 移除特殊字符，保留中文、英文、数字、空格
            anchor = re.sub(r'[^\w\s\u4e00-\u9fff-]', '', anchor)
            # 将空格替换为连字符
            anchor = re.sub(r'\s+', '-', anchor)
            
            headings.append((level, title, anchor))
    
    return headings

def generate_toc(headings: List[Tuple[int, str, str]]) -> str:
    """
    根据标题列表生成TOC
    """
    if not headings:
        return ""
    
    toc_lines = ["## 📚 目录", ""]
    
    for level, title, anchor in headings:
        indent = "  " * (level - 2)  # level 2 不缩进，level 3 缩进2空格
        toc_line = f"{indent}- [{title}](#{anchor})"
        toc_lines.append(toc_line)
    
    toc_lines.append("")
    toc_lines.append("---")
    toc_lines.append("")
    
    return '\n'.join(toc_lines)

def has_toc(content: str) -> bool:
    """
    检查文档是否已有目录
    """
    # 检查是否有目录标记
    if re.search(r'^## 📚 目录', content, re.MULTILINE):
        return True
    if re.search(r'^## 目录', content, re.MULTILINE):
        return True
    return False

def add_toc_to_file(file_path: Path, dry_run: bool = False) -> bool:
    """
    为单个文件添加TOC
    返回是否成功
    """
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # 检查是否已有TOC
        if has_toc(content):
            print(f"  ✓ 已有TOC: {file_path.name}")
            return True
        
        # 提取标题
        headings = extract_headings(content)
        
        if len(headings) < 2:
            print(f"  ⚠ 标题太少，跳过: {file_path.name} ({len(headings)} headings)")
            return False
        
        # 生成TOC
        toc = generate_toc(headings)
        
        # 在第一个 ## 标题之前插入TOC
        lines = content.split('\n')
        insert_index = 0
        
        for i, line in enumerate(lines):
            if re.match(r'^## [^\s]', line):
                insert_index = i
                break
        
        # 插入TOC
        new_lines = lines[:insert_index] + toc.split('\n') + lines[insert_index:]
        new_content = '\n'.join(new_lines)
        
        if not dry_run:
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(new_content)
            print(f"  ✅ 已添加TOC: {file_path.name} ({len(headings)} headings)")
        else:
            print(f"  [Dry Run] 将添加TOC: {file_path.name} ({len(headings)} headings)")
        
        return True
        
    except Exception as e:
        print(f"  ❌ 错误: {file_path.name} - {str(e)}")
        return False

def main():
    """
    主函数
    """
    base_dir = Path(__file__).parent
    
    # 要处理的目录
    subdirs = [
        "01_Formal_Semantics",
        "02_Design_Patterns",
        "03_Algorithm_Complexity",
        "04_Architecture_Patterns",
        "05_Formal_Verification"
    ]
    
    print("=" * 60)
    print("批量添加 TOC 工具")
    print("=" * 60)
    
    total_files = 0
    success_files = 0
    
    for subdir in subdirs:
        dir_path = base_dir / subdir
        
        if not dir_path.exists():
            print(f"\n⚠️  目录不存在: {subdir}")
            continue
        
        print(f"\n📁 处理目录: {subdir}")
        print("-" * 60)
        
        md_files = sorted(dir_path.glob("*.md"))
        
        for md_file in md_files:
            total_files += 1
            if add_toc_to_file(md_file, dry_run=False):
                success_files += 1
    
    print("\n" + "=" * 60)
    print(f"完成! 成功: {success_files}/{total_files}")
    print("=" * 60)

if __name__ == "__main__":
    main()

