#!/usr/bin/env python3
"""批量修复Markdown格式问题"""

import re
import sys
from pathlib import Path

def fix_code_blocks_language(content):
    """修复缺少语言标识的代码块"""
    # 匹配没有语言标识的代码块
    pattern = r'```\n((?:(?!```).|\n)*?)```'
    
    def replacer(match):
        code_content = match.group(1)
        # 判断代码块类型
        if any(keyword in code_content for keyword in ['function', 'const', 'let', 'var', '=>']):
            return f'```javascript\n{code_content}```'
        elif any(keyword in code_content for keyword in ['def ', 'import ', 'class ', 'print(']):
            return f'```python\n{code_content}```'
        elif any(keyword in code_content for keyword in ['apiVersion:', 'kind:', 'metadata:']):
            return f'```yaml\n{code_content}```'
        elif any(keyword in code_content for keyword in ['package ', 'func ', 'type ']):
            return f'```go\n{code_content}```'
        elif any(keyword in code_content for keyword in ['public class', 'private ', 'void ']):
            return f'```java\n{code_content}```'
        else:
            return f'```text\n{code_content}```'
    
    return re.sub(pattern, replacer, content)

def add_blank_lines_around_code(content):
    """在代码块周围添加空行"""
    lines = content.split('\n')
    result = []
    prev_was_fence = False
    in_fence = False
    
    for i, line in enumerate(lines):
        is_fence = line.strip().startswith('```')
        
        if is_fence:
            if not in_fence:  # 开始代码块
                # 如果前一行不是空行且不是列表项，添加空行
                if result and result[-1].strip() and not result[-1].strip().startswith(('-', '*', '1.')):
                    result.append('')
                in_fence = True
            else:  # 结束代码块
                in_fence = False
            result.append(line)
        else:
            if prev_was_fence and not in_fence and line.strip():
                # 代码块后面如果不是空行，添加空行
                if not result[-1].strip():
                    result.append(line)
                else:
                    result.append('')
                    result.append(line)
            else:
                result.append(line)
        
        prev_was_fence = is_fence and in_fence
    
    return '\n'.join(result)

def add_blank_lines_around_lists(content):
    """在列表周围添加空行"""
    lines = content.split('\n')
    result = []
    prev_was_list = False
    
    for i, line in enumerate(lines):
        is_list = line.strip().startswith(('-', '*', '1.', '2.', '3.'))
        
        if is_list and not prev_was_list:
            # 列表开始，前面添加空行
            if result and result[-1].strip():
                result.append('')
        elif not is_list and prev_was_list:
            # 列表结束，后面添加空行
            result.append(line)
            if line.strip() and i < len(lines) - 1:
                result.append('')
                prev_was_list = False
                continue
        
        result.append(line)
        prev_was_list = is_list
    
    return '\n'.join(result)

def fix_ordered_list_prefixes(content):
    """修复有序列表前缀"""
    lines = content.split('\n')
    result = []
    list_counter = 1
    in_list = False
    
    for line in lines:
        if re.match(r'^\d+\.\s', line):
            # 这是一个有序列表项
            indent = len(line) - len(line.lstrip())
            rest = re.sub(r'^\d+\.\s', '', line.lstrip())
            result.append(' ' * indent + f'{list_counter}. {rest}')
            list_counter += 1
            in_list = True
        else:
            if in_list and not line.strip():
                # 列表结束
                list_counter = 1
                in_list = False
            result.append(line)
    
    return '\n'.join(result)

def add_blank_lines_around_headings(content):
    """在标题周围添加空行"""
    lines = content.split('\n')
    result = []
    
    for i, line in enumerate(lines):
        is_heading = line.startswith('#')
        
        if is_heading:
            # 标题前添加空行
            if result and result[-1].strip():
                result.append('')
            result.append(line)
            # 标题后添加空行
            if i < len(lines) - 1 and lines[i + 1].strip():
                result.append('')
        else:
            result.append(line)
    
    return '\n'.join(result)

def main():
    if len(sys.argv) < 2:
        print("Usage: python batch_fix_markdown.py <file_path>")
        sys.exit(1)
    
    file_path = Path(sys.argv[1])
    if not file_path.exists():
        print(f"File not found: {file_path}")
        sys.exit(1)
    
    # 读取文件
    content = file_path.read_text(encoding='utf-8')
    
    # 应用修复
    content = fix_code_blocks_language(content)
    content = add_blank_lines_around_code(content)
    content = add_blank_lines_around_lists(content)
    content = add_blank_lines_around_headings(content)
    
    # 写回文件
    file_path.write_text(content, encoding='utf-8')
    print(f"Fixed: {file_path}")

if __name__ == '__main__':
    main()

