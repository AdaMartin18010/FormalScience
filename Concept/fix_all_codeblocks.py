#!/usr/bin/env python3
"""
全面修复代码块格式：
1. 确保开始标记是 ```text（如果原来是 ```）
2. 确保结束标记是 ```（不是 ```text）
"""

import os
import re
from pathlib import Path

def fix_codeblocks(content):
    """修复所有代码块格式"""
    lines = content.split('\n')
    result = []
    in_codeblock = False
    codeblock_start_line = -1
    
    for i, line in enumerate(lines):
        # 检查是否是代码块开始标记
        if re.match(r'^```(\w+)?\s*$', line):
            if not in_codeblock:
                # 开始标记
                in_codeblock = True
                codeblock_start_line = i
                # 如果开始标记是 ```，改为 ```text
                if re.match(r'^```\s*$', line):
                    result.append('```text')
                else:
                    result.append(line)
            else:
                # 结束标记：应该是 ```，不是 ```text
                result.append('```')
                in_codeblock = False
                codeblock_start_line = -1
        else:
            result.append(line)
    
    return '\n'.join(result)

def process_file(filepath):
    """处理单个文件"""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
        
        original = content
        content = fix_codeblocks(content)
        
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
