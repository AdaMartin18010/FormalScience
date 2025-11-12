#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
最终修复目录格式
确保格式统一：
- 一级子主题：不带点号（如 1 引言）
- 二级子主题：带点号（如 1.1 核心思想）
- 移除emoji和多余空格
"""

import os
import re
from pathlib import Path

def clean_title(title):
    """清理标题，移除emoji和多余空格"""
    # 移除emoji（保留中文字符、数字、字母、标点）
    title = re.sub(r'[^\w\s\u4e00-\u9fff\-\(\)\[\]：，。、]', '', title)
    # 移除多余空格
    title = re.sub(r'\s+', ' ', title)
    return title.strip()

def generate_anchor(text):
    """生成锚点链接"""
    anchor = text.lower()
    # 移除特殊字符，保留中文字符
    anchor = re.sub(r'[^\w\s\u4e00-\u9fff-]', '', anchor)
    anchor = re.sub(r'\s+', '-', anchor)
    anchor = anchor.strip('-')
    return anchor

def extract_content_headers(content):
    """提取内容中的标题"""
    headers = []
    lines = content.split('\n')
    in_toc = False
    skip_patterns = ['📋 目录', '目录', '目录 | Table of Contents', '导航 | Navigation', 
                    '相关主题 | Related Topics', '参考文献', 'References', 'FAQ', 
                    'Glossary', 'Quick Reference', 'Learning Paths', 'Master Index']
    
    for line in lines:
        # 检测目录区域
        if '## 📋 目录' in line or '## 目录' in line or '## 目录 | Table of Contents' in line:
            in_toc = True
        elif in_toc and line.strip() == '---':
            in_toc = False
            continue
        
        if in_toc:
            continue
        
        # 匹配标题，如 ## 1 引言 或 ### 1.1 核心思想
        # 也匹配带emoji的标题，如 ## 1 ️⃣ RNN vs Transformer
        match = re.match(r'(#{2,})\s+(\d+(?:\.\d+)*)?\s*([^\d\s].*?)$', line)
        if match:
            level = len(match.group(1))
            number = match.group(2) if match.group(2) else None
            title = match.group(3).strip()
            
            # 跳过特殊标题和主标题
            if any(pattern in title for pattern in skip_patterns) or level == 1:
                continue
            
            # 清理标题
            clean_title_text = clean_title(title)
            if clean_title_text:
                headers.append((level, number, clean_title_text, title))
    
    return headers

def normalize_number(number, level, parent_number=None):
    """规范化编号"""
    if not number:
        return None
    
    # 移除文件前缀（如果有）
    if '.' in number:
        parts = number.split('.')
        # 如果第一部分是文件编号，移除它
        if len(parts) > 1:
            # 检查是否是文件编号格式（如 2.2.1）
            if len(parts) >= 3:
                # 可能是文件编号，尝试移除
                number = '.'.join(parts[1:])
    
    if level == 2:
        # 一级子主题：不带点号
        if '.' in number:
            return number.split('.')[0]
        return number
    elif level == 3:
        # 二级子主题：带点号
        if parent_number:
            if '.' in number:
                return number
            else:
                return f"{parent_number}.{number}"
        else:
            if '.' in number:
                return number
            else:
                return f"1.{number}"
    return number

def assign_numbers_to_headers(headers):
    """为标题分配正确的编号"""
    numbered_headers = []
    current_numbers = {}
    
    for level, number, clean_title, original_title in headers:
        if level == 2:
            # 一级子主题
            if level not in current_numbers:
                current_numbers[level] = 1
            else:
                current_numbers[level] += 1
            
            # 重置所有子级编号
            for l in range(level + 1, 10):
                if l in current_numbers:
                    del current_numbers[l]
            
            final_number = str(current_numbers[level])
            numbered_headers.append((level, final_number, clean_title, original_title))
            
        elif level == 3:
            # 二级子主题
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
            
            final_number = f"{parent_num}.{current_numbers[level]}"
            numbered_headers.append((level, final_number, clean_title, original_title))
        else:
            # 更深层级（三级及以上）
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
            
            final_number = '.'.join(parts)
            numbered_headers.append((level, final_number, clean_title, original_title))
    
    return numbered_headers

def generate_toc(headers):
    """生成目录"""
    numbered_headers = assign_numbers_to_headers(headers)
    
    if not numbered_headers:
        return None
    
    toc_lines = ["## 📋 目录", ""]
    
    for level, number, clean_title, original_title in numbered_headers:
        indent = "  " * (level - 2)  # level 2 不缩进，level 3 缩进2个空格
        
        if level == 2:
            # 一级子主题：不带点号
            toc_title = f"{number} {clean_title}"
        else:
            # 二级及以上子主题：带点号
            toc_title = f"{number} {clean_title}"
        
        anchor = generate_anchor(toc_title)
        toc_lines.append(f"{indent}- [{toc_title}](#{anchor})")
    
    toc_lines.append("")
    toc_lines.append("---")
    toc_lines.append("")
    
    return '\n'.join(toc_lines)

def fix_content_headers(content, headers):
    """修复内容中的标题编号"""
    numbered_headers = assign_numbers_to_headers(headers)
    
    lines = content.split('\n')
    fixed_lines = []
    in_toc = False
    header_index = 0
    
    for line in lines:
        # 跳过目录部分
        if '## 📋 目录' in line or '## 目录' in line or '## 目录 | Table of Contents' in line:
            in_toc = True
        elif in_toc and line.strip() == '---':
            in_toc = False
            continue
        
        if in_toc:
            fixed_lines.append(line)
            continue
        
        # 匹配标题（包括带emoji的）
        match = re.match(r'(#{2,})\s+(\d+(?:\.\d+)*)?\s*([^\d\s].*?)$', line)
        if match:
            level = len(match.group(1))
            old_number = match.group(2) if match.group(2) else None
            title = match.group(3).strip()
            
            # 跳过特殊标题和主标题
            skip_patterns = ['📋 目录', '目录', '目录 | Table of Contents', '导航 | Navigation', 
                            '相关主题 | Related Topics', '参考文献', 'References']
            if any(pattern in title for pattern in skip_patterns) or level == 1:
                fixed_lines.append(line)
                continue
            
            # 找到对应的编号标题
            if header_index < len(numbered_headers):
                h_level, h_number, h_clean_title, h_original_title = numbered_headers[header_index]
                # 清理标题用于匹配
                clean_title_text = clean_title(title)
                
                if h_level == level and h_clean_title == clean_title_text:
                    # 使用清理后的标题
                    new_line = f"{'#' * level} {h_number} {h_clean_title}"
                    fixed_lines.append(new_line)
                    header_index += 1
                else:
                    fixed_lines.append(line)
            else:
                fixed_lines.append(line)
        else:
            fixed_lines.append(line)
    
    return '\n'.join(fixed_lines)

def process_file(filepath):
    """处理单个文件"""
    print(f"处理文件: {filepath}")
    
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
    except Exception as e:
        print(f"  错误：无法读取文件 - {e}")
        return False
    
    # 提取标题
    headers = extract_content_headers(content)
    
    if not headers:
        print(f"  跳过：未找到标题")
        return False
    
    # 修复内容中的标题编号
    content = fix_content_headers(content, headers)
    
    # 重新提取标题（因为内容已更新）
    headers = extract_content_headers(content)
    
    # 生成或更新目录
    toc = generate_toc(headers)
    
    if not toc:
        print(f"  跳过：无法生成目录")
        return False
    
    # 插入或替换目录
    lines = content.split('\n')
    
    # 找到现有目录位置并替换
    toc_start = -1
    toc_end = -1
    
    for i, line in enumerate(lines):
        if '## 📋 目录' in line or '## 目录' in line or '## 目录 | Table of Contents' in line:
            toc_start = i
        elif toc_start >= 0 and line.strip() == '---' and i > toc_start + 2:
            toc_end = i
            break
    
    if toc_start >= 0 and toc_end > toc_start:
        new_lines = lines[:toc_start] + toc.split('\n') + lines[toc_end + 1:]
        content = '\n'.join(new_lines)
    else:
        # 如果找不到目录，在第一个标题前插入
        first_header = -1
        for i, line in enumerate(lines):
            if re.match(r'^##\s+\d', line) or (re.match(r'^##\s+[^#]', line) and '目录' not in line):
                first_header = i
                break
        if first_header >= 0:
            new_lines = lines[:first_header] + toc.split('\n') + lines[first_header:]
            content = '\n'.join(new_lines)
        else:
            print(f"  警告：无法找到插入位置")
            return False
    
    # 写回文件
    try:
        with open(filepath, 'w', encoding='utf-8') as f:
            f.write(content)
        print(f"  完成：已更新目录")
        return True
    except Exception as e:
        print(f"  错误：无法写入文件 - {e}")
        return False

def main():
    """主函数"""
    base_dir = Path(__file__).parent
    
    # 指定要处理的文件
    target_files = [
        'Concept/AI_model_Perspective/02_Neural_Network_Theory/02.2_RNN_Transformer_Architecture.md',
        'Concept/AI_model_Perspective/02_Neural_Network_Theory/02.4_Transformer_Architecture.md',
        'Concept/AI_model_Perspective/02_Neural_Network_Theory/02.5_Universal_Approximation_Theorem.md',
        'Concept/AI_model_Perspective/03_Language_Models/03.4_Token_Generation_Mechanisms.md',
        'Concept/AI_model_Perspective/03_Language_Models/03.5_Embedding_Vector_Spaces.md',
        'Concept/AI_model_Perspective/03_Language_Models/03.6_Context_Window_Memory.md',
        'Concept/AI_model_Perspective/04_Semantic_Models/04.2_Continuous_Representation_Theory.md',
        'Concept/AI_model_Perspective/04_Semantic_Models/04.3_Distributional_Semantics.md',
        'Concept/AI_model_Perspective/04_Semantic_Models/04.4_Semantic_Similarity_Metrics.md',
        'Concept/AI_model_Perspective/04_Semantic_Models/04.5_Multimodal_Semantic_Integration.md',
        'Concept/AI_model_Perspective/04_Semantic_Models/04.6_Huang_Semantic_Model_Analysis.md',
        'Concept/AI_model_Perspective/05_Learning_Theory/05.2_Gold_Learnability_Theory.md',
    ]
    
    print(f"找到 {len(target_files)} 个文件需要处理")
    print("")
    
    processed = 0
    skipped = 0
    errors = 0
    
    for file_path in target_files:
        filepath = base_dir / file_path
        if not filepath.exists():
            print(f"  跳过：文件不存在 - {filepath}")
            skipped += 1
            continue
        
        try:
            if process_file(filepath):
                processed += 1
            else:
                skipped += 1
        except Exception as e:
            print(f"  错误：处理文件时出错 - {e}")
            errors += 1
    
    print(f"\n{'='*60}")
    print(f"处理完成：")
    print(f"  - 成功处理：{processed} 个文件")
    print(f"  - 跳过：{skipped} 个文件")
    print(f"  - 错误：{errors} 个文件")
    print(f"{'='*60}")

if __name__ == '__main__':
    main()
