#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
全面递归检查并修复所有markdown文件的目录格式
要求：
- 一级子主题：不带点号（如 1 引言）
- 二级子主题：带点号（如 1.1 核心思想）
- 每个文件只有一个目录
- 目录和内容编号保持一致
"""

import os
import re
from pathlib import Path
from collections import defaultdict

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
                    'Glossary', 'Quick Reference', 'Learning Paths', 'Master Index',
                    '上一篇', '下一篇', '返回目录']
    
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

def assign_numbers_to_headers(headers):
    """为标题分配正确的编号"""
    numbered_headers = []
    current_numbers = {}
    
    for level, number, clean_title, original_title in headers:
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
            
            final_number = str(current_numbers[level])
            numbered_headers.append((level, final_number, clean_title, original_title))
            
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

def count_toc_sections(content):
    """统计目录部分的数量"""
    toc_count = 0
    lines = content.split('\n')
    
    for line in lines:
        if '## 📋 目录' in line or '## 目录' in line or '## 目录 | Table of Contents' in line:
            toc_count += 1
    
    return toc_count

def process_file(filepath):
    """处理单个文件"""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            content = f.read()
    except Exception as e:
        return {'error': f'无法读取文件: {e}'}
    
    issues = []
    needs_fix = False
    
    # 检查是否有多个目录
    toc_count = count_toc_sections(content)
    if toc_count > 1:
        issues.append(f'发现 {toc_count} 个目录部分（应该只有1个）')
        needs_fix = True
    elif toc_count == 0:
        issues.append('没有找到目录')
        needs_fix = True
    
    # 提取标题
    headers = extract_content_headers(content)
    
    if not headers:
        return {'skipped': '未找到标题', 'issues': issues}
    
    # 检查标题格式
    for level, number, clean_title, original_title in headers:
        if level == 2 and number and '.' in number:
            issues.append(f'一级子主题不应带点号: {number} {clean_title}')
            needs_fix = True
    
    if needs_fix or toc_count != 1:
        # 需要修复
        try:
            # 删除重复目录
            if toc_count > 1:
                lines = content.split('\n')
                new_lines = []
                toc_found = False
                in_toc = False
                
                for i, line in enumerate(lines):
                    if '## 📋 目录' in line or '## 目录' in line or '## 目录 | Table of Contents' in line:
                        if not toc_found:
                            toc_found = True
                            in_toc = True
                            new_lines.append(line)
                        else:
                            # 跳过重复的目录
                            in_toc = True
                            continue
                    elif in_toc and line.strip() == '---' and i > 0:
                        in_toc = False
                        if toc_found:
                            new_lines.append(line)
                    elif not in_toc or not toc_found:
                        new_lines.append(line)
                
                content = '\n'.join(new_lines)
            
            # 修复内容中的标题编号
            content = fix_content_headers(content, extract_content_headers(content))
            
            # 重新提取标题（因为内容已更新）
            headers = extract_content_headers(content)
            
            # 生成或更新目录
            toc = generate_toc(headers)
            
            if toc:
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
                        return {'error': '无法找到插入位置', 'issues': issues}
                
                # 写回文件
                try:
                    with open(filepath, 'w', encoding='utf-8') as f:
                        f.write(content)
                    return {'fixed': True, 'issues': issues}
                except Exception as e:
                    return {'error': f'无法写入文件: {e}', 'issues': issues}
            else:
                return {'error': '无法生成目录', 'issues': issues}
        except Exception as e:
            return {'error': f'修复时出错: {e}', 'issues': issues}
    else:
        return {'ok': True, 'issues': issues}

def scan_markdown_files(root_dir):
    """递归扫描所有markdown文件"""
    markdown_files = []
    for root, dirs, files in os.walk(root_dir):
        # 跳过一些目录
        dirs[:] = [d for d in dirs if not d.startswith('.') and d not in ['node_modules', '__pycache__']]
        
        for file in files:
            if file.endswith('.md'):
                markdown_files.append(os.path.join(root, file))
    
    return markdown_files

def main():
    """主函数"""
    base_dir = Path(__file__).parent
    
    print("=" * 60)
    print("全面递归检查所有markdown文件的目录格式")
    print("=" * 60)
    print()
    
    # 扫描所有markdown文件
    print("正在扫描markdown文件...")
    markdown_files = scan_markdown_files(base_dir)
    print(f"找到 {len(markdown_files)} 个markdown文件")
    print()
    
    stats = {
        'total': len(markdown_files),
        'ok': 0,
        'fixed': 0,
        'skipped': 0,
        'errors': 0
    }
    
    results = defaultdict(list)
    
    for filepath in markdown_files:
        rel_path = os.path.relpath(filepath, base_dir)
        result = process_file(filepath)
        
        if 'ok' in result:
            stats['ok'] += 1
            results['ok'].append(rel_path)
        elif 'fixed' in result:
            stats['fixed'] += 1
            results['fixed'].append(rel_path)
            if result.get('issues'):
                print(f"✅ 已修复: {rel_path}")
                for issue in result['issues']:
                    print(f"   - {issue}")
        elif 'skipped' in result:
            stats['skipped'] += 1
            results['skipped'].append(rel_path)
        elif 'error' in result:
            stats['errors'] += 1
            results['errors'].append(rel_path)
            print(f"❌ 错误: {rel_path}")
            print(f"   - {result['error']}")
    
    print()
    print("=" * 60)
    print("处理完成统计")
    print("=" * 60)
    print(f"总文件数: {stats['total']}")
    print(f"✅ 正常: {stats['ok']}")
    print(f"🔧 已修复: {stats['fixed']}")
    print(f"⏭️  跳过: {stats['skipped']}")
    print(f"❌ 错误: {stats['errors']}")
    print()
    
    if results['fixed']:
        print(f"已修复的文件 ({len(results['fixed'])}):")
        for f in results['fixed'][:10]:  # 只显示前10个
            print(f"  - {f}")
        if len(results['fixed']) > 10:
            print(f"  ... 还有 {len(results['fixed']) - 10} 个文件")
        print()
    
    if results['errors']:
        print(f"错误的文件 ({len(results['errors'])}):")
        for f in results['errors'][:10]:  # 只显示前10个
            print(f"  - {f}")
        if len(results['errors']) > 10:
            print(f"  ... 还有 {len(results['errors']) - 10} 个文件")
        print()

if __name__ == '__main__':
    main()
