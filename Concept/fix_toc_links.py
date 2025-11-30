#!/usr/bin/env python3
"""
修复目录中的章节链接格式
"""

import os
import re
from pathlib import Path

def fix_toc_links(content):
    """修复目录中的章节链接格式"""
    # 修复 "数字 . 标题" 格式为 "数字 标题"
    content = re.sub(
        r'- \[(\d+) \. ([^\]]+)\]\(#(\d+)--([^\)]+)\)',
        r'- [\1 \2](#\3-\4)',
        content
    )
    # 修复 "数字 . 标题" 格式（无链接）
    content = re.sub(
        r'- \[(\d+) \. ([^\]]+)\]',
        r'- [\1 \2]',
        content
    )
    return content

def process_file(filepath):
    """处理单个文件"""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
        
        original = content
        content = fix_toc_links(content)
        
        if content != original:
            with open(filepath, 'w', encoding='utf-8') as f:
                f.write(content)
            return True
        return False
    except Exception as e:
        print(f"✗ 错误: {filepath}: {e}")
        return False

def main():
    base_dir = Path(__file__).parent
    pattern = re.compile(r'^\d+\.\d+_.+\.md$')
    files = []
    
    for root, dirs, filenames in os.walk(base_dir):
        if 'node_modules' in root or '.git' in root:
            continue
        for f in filenames:
            if pattern.match(f):
                files.append(Path(root) / f)
    
    print(f"检查 {len(files)} 个文件...\n")
    
    fixed = 0
    for filepath in sorted(files):
        if process_file(filepath):
            print(f"✓ {filepath.name}")
            fixed += 1
    
    print(f"\n完成！修复了 {fixed}/{len(files)} 个文件")

if __name__ == '__main__':
    main()
