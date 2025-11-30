#!/usr/bin/env python3
"""
修复代码块结束标记：将 ```text 改为 ```
只修复成对的第二个（结束标记），保留开始标记的 ```text
"""

import os
import re
from pathlib import Path

def fix_codeblock_endings(content):
    """修复代码块结束标记：只修复结束标记，保留开始标记"""
    lines = content.split('\n')
    result = []
    in_codeblock = False
    codeblock_start_type = None
    
    for i, line in enumerate(lines):
        # 检查是否是代码块开始标记
        start_match = re.match(r'^```(\w+)?\s*$', line)
        if start_match and not in_codeblock:
            in_codeblock = True
            codeblock_start_type = start_match.group(1)  # 可能是 text 或其他
            result.append(line)  # 保留开始标记（包括 ```text）
        # 检查是否是代码块结束标记
        elif in_codeblock and re.match(r'^```(\w+)?\s*$', line):
            # 结束标记应该只是 ```，不管开始标记是什么
            result.append('```')
            in_codeblock = False
            codeblock_start_type = None
        else:
            result.append(line)
    
    return '\n'.join(result)

def process_file(filepath):
    """处理单个文件"""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
        
        original = content
        content = fix_codeblock_endings(content)
        
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
