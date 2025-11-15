#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
修复文件中的编号不一致问题
"""

import re
from pathlib import Path

def fix_file_numbering(filepath):
    """修复文件中的标题编号"""
    print(f"处理文件: {filepath}")
    
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
    except Exception as e:
        print(f"  错误：无法读取文件 - {e}")
        return False
    
    lines = content.split('\n')
    fixed_lines = []
    in_toc = False
    current_numbers = {}
    
    for line in lines:
        # 跳过目录部分
        if '## 📋 目录' in line or '## 目录' in line:
            in_toc = True
        elif in_toc and line.strip() == '---':
            in_toc = False
            continue
        
        if in_toc:
            fixed_lines.append(line)
            continue
        
        # 匹配标题
        match = re.match(r'(#{2,})\s+(\d+(?:\.\d+)*)?\s*([^\d\s].*?)$', line)
        if match:
            level = len(match.group(1))
            old_number = match.group(2) if match.group(2) else None
            title = match.group(3).strip()
            
            # 跳过特殊标题和主标题
            skip_patterns = ['📋 目录', '目录', '目录 | Table of Contents', '导航 | Navigation', 
                            '相关主题 | Related Topics', '参考文献', 'References', '导航']
            if any(pattern in title for pattern in skip_patterns) or level == 1:
                fixed_lines.append(line)
                continue
            
            # 分配新编号
            if level == 2:
                # 一级子主题：不带点号
                if level not in current_numbers:
                    current_numbers[level] = 1
                else:
                    current_numbers[level] += 1
                
                # 重置所有子级编号
                for l in range(level + 1, 10):
                    if l in current_numbers:
                        del current_numbers[l]
                
                new_number = str(current_numbers[level])
                new_line = f"{'#' * level} {new_number} {title}"
                fixed_lines.append(new_line)
                
            elif level == 3:
                # 二级子主题：带点号
                parent_level = level - 1
                if parent_level in current_numbers:
                    parent_num = str(current_numbers[parent_level])
                else:
                    parent_num = "1"
                
                if level not in current_numbers:
                    current_numbers[level] = 1
                else:
                    current_numbers[level] += 1
                
                # 重置更深层级
                for l in range(level + 1, 10):
                    if l in current_numbers:
                        del current_numbers[l]
                
                new_number = f"{parent_num}.{current_numbers[level]}"
                new_line = f"{'#' * level} {new_number} {title}"
                fixed_lines.append(new_line)
            else:
                # 更深层级
                parent_level = level - 1
                if parent_level in current_numbers:
                    parent_num = str(current_numbers[parent_level])
                else:
                    parent_num = "1"
                
                if level not in current_numbers:
                    current_numbers[level] = 1
                else:
                    current_numbers[level] += 1
                
                # 重置更深层级
                for l in range(level + 1, 10):
                    if l in current_numbers:
                        del current_numbers[l]
                
                # 构建层级编号
                parts = [parent_num]
                for l in range(3, level + 1):
                    if l in current_numbers:
                        parts.append(str(current_numbers[l]))
                    else:
                        parts.append("1")
                
                new_number = '.'.join(parts)
                new_line = f"{'#' * level} {new_number} {title}"
                fixed_lines.append(new_line)
        else:
            fixed_lines.append(line)
    
    # 写回文件
    try:
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write('\n'.join(fixed_lines))
        print(f"  完成：已修复标题编号")
        return True
    except Exception as e:
        print(f"  错误：无法写入文件 - {e}")
        return False

def main():
    """主函数"""
    base_dir = Path(__file__).parent
    
    target_files = [
        'Concept/Software_Perspective/10_Future_Directions/10.1_Intent_Driven_Programming.md',
        'Concept/Software_Perspective/10_Future_Directions/10.2_AI_Assisted_Software_Engineering.md',
        'Concept/Software_Perspective/10_Future_Directions/10.3_Quantum_Computing_Integration.md',
        'Concept/Software_Perspective/10_Future_Directions/10.5_Consciousness_Machine_Integration.md',
    ]
    
    print(f"找到 {len(target_files)} 个文件需要处理")
    print("")
    
    processed = 0
    errors = 0
    
    for file_path in target_files:
        filepath = base_dir / file_path
        if not filepath.exists():
            print(f"  跳过：文件不存在 - {filepath}")
            continue
        
        try:
            if fix_file_numbering(filepath):
                processed += 1
        except Exception as e:
            print(f"  错误：处理文件时出错 - {e}")
            errors += 1
    
    print(f"\n{'='*60}")
    print(f"处理完成：")
    print(f"  - 成功处理：{processed} 个文件")
    print(f"  - 错误：{errors} 个文件")
    print(f"{'='*60}")

if __name__ == '__main__':
    main()
