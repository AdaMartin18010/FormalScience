#!/usr/bin/env python3
"""
为Markdown文件生成目录（Table of Contents）
"""

import re
from pathlib import Path
from typing import List, Tuple

def extract_headings(content: str) -> List[Tuple[int, str, str]]:
    """
    从Markdown内容中提取标题
    返回：[(level, text, anchor), ...]
    """
    headings = []
    lines = content.split('\n')
    
    in_code_block = False
    
    for line in lines:
        # 跳过代码块
        if line.strip().startswith('```'):
            in_code_block = not in_code_block
            continue
        
        if in_code_block:
            continue
        
        # 匹配标题：# 标题 或 ## 标题
        match = re.match(r'^(#{1,6})\s+(.+)$', line)
        if match:
            level = len(match.group(1))
            text = match.group(2).strip()
            
            # 跳过第一个主标题（#）
            if level == 1:
                continue
            
            # 生成anchor链接（GitHub风格）
            anchor = text.lower()
            anchor = re.sub(r'[^\w\s\-\u4e00-\u9fff]', '', anchor)  # 保留中文
            anchor = re.sub(r'\s+', '-', anchor)
            anchor = anchor.strip('-')
            
            headings.append((level, text, anchor))
    
    return headings

def generate_toc(headings: List[Tuple[int, str, str]]) -> str:
    """
    根据标题列表生成目录
    """
    if not headings:
        return ""
    
    toc_lines = ["## 目录 | Table of Contents", ""]
    
    # 找到最小level作为基准
    min_level = min(h[0] for h in headings)
    
    for level, text, anchor in headings:
        indent = "  " * (level - min_level)
        toc_lines.append(f"{indent}- [{text}](#{anchor})")
    
    toc_lines.append("")
    toc_lines.append("---")
    toc_lines.append("")
    
    return "\n".join(toc_lines)

def insert_toc(content: str) -> str:
    """
    在文档中插入目录
    - 如果已有目录，替换之
    - 如果没有，插入到元数据块之后
    """
    lines = content.split('\n')
    
    # 检查是否已经有目录
    has_toc = False
    toc_start = -1
    toc_end = -1
    
    for i, line in enumerate(lines):
        if re.match(r'^##\s+(目录|Table of Contents)', line):
            has_toc = True
            toc_start = i
            # 找到目录结束位置（下一个---或下一个##标题）
            for j in range(i + 1, len(lines)):
                if lines[j].strip() == '---' or lines[j].startswith('## '):
                    toc_end = j
                    break
            break
    
    # 提取标题
    headings = extract_headings(content)
    
    # 生成新目录
    new_toc = generate_toc(headings)
    
    if not new_toc:
        return content
    
    if has_toc:
        # 替换现有目录
        new_lines = lines[:toc_start] + new_toc.split('\n') + lines[toc_end+1:]
        return '\n'.join(new_lines)
    else:
        # 插入新目录到元数据块之后
        # 找到第一个---之后的位置
        insert_pos = 0
        dash_count = 0
        for i, line in enumerate(lines):
            if line.strip() == '---':
                dash_count += 1
                if dash_count == 1:
                    insert_pos = i + 1
                    break
        
        if insert_pos == 0:
            # 没找到---，插入到文件开头之后
            insert_pos = 1
        
        # 在插入位置之后添加空行
        while insert_pos < len(lines) and lines[insert_pos].strip() == '':
            insert_pos += 1
        
        new_lines = (lines[:insert_pos] + 
                    [''] +
                    new_toc.split('\n') + 
                    lines[insert_pos:])
        return '\n'.join(new_lines)

def process_file(filepath: Path, dry_run: bool = True) -> bool:
    """
    处理单个文件
    返回：是否进行了修改
    """
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
        
        new_content = insert_toc(content)
        
        if new_content != content:
            if not dry_run:
                with open(filepath, 'w', encoding='utf-8') as f:
                    f.write(new_content)
            return True
        return False
    except Exception as e:
        print(f"错误处理文件 {filepath}: {e}")
        return False

def main():
    import sys
    
    if len(sys.argv) < 2:
        print("用法: python generate_toc.py <文件或目录> [--apply]")
        print("  --apply: 实际应用修改（否则为预览模式）")
        sys.exit(1)
    
    target = Path(sys.argv[1])
    dry_run = '--apply' not in sys.argv
    
    if dry_run:
        print("🔍 预览模式（不会修改文件）")
        print("   使用 --apply 参数来实际应用修改\n")
    else:
        print("✏️  应用模式（将修改文件）\n")
    
    files_to_process = []
    
    if target.is_file():
        files_to_process = [target]
    elif target.is_dir():
        files_to_process = list(target.rglob("*.md"))
        # 过滤掉特殊文件
        files_to_process = [f for f in files_to_process 
                           if f.name not in ['README.md', 'FAQ.md', 'GLOSSARY.md',
                                           'QUICK_REFERENCE.md', 'LEARNING_PATHS.md',
                                           '00_Master_Index.md', 'COMPLETION_SUMMARY.md']]
    else:
        print(f"错误: {target} 不存在")
        sys.exit(1)
    
    modified_count = 0
    
    for filepath in files_to_process:
        if process_file(filepath, dry_run):
            modified_count += 1
            print(f"{'[预览]' if dry_run else '[修改]'} {filepath.relative_to(target.parent)}")
    
    print(f"\n总计: {len(files_to_process)} 个文件, {modified_count} 个需要修改")
    
    if dry_run and modified_count > 0:
        print("\n使用 --apply 参数来实际应用这些修改")

if __name__ == "__main__":
    main()

