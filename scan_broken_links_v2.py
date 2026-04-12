#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
扫描当前断链情况 - 改进版（排除数学公式）
"""

import os
import re
import json
from pathlib import Path
from collections import defaultdict

def find_markdown_files(root_dir):
    """查找所有markdown文件"""
    md_files = []
    for dirpath, dirnames, filenames in os.walk(root_dir):
        if '.git' in dirpath:
            continue
        for filename in filenames:
            if filename.endswith('.md'):
                md_files.append(os.path.join(dirpath, filename))
    return md_files

def remove_math_formulas(content):
    """移除数学公式，避免误判"""
    # 移除行内数学公式 $...$
    content = re.sub(r'\$[^\$]+\$', ' MATH ', content)
    # 移除块级数学公式 $$...$$
    content = re.sub(r'\$\$[^\$]+\$\$', ' MATH_BLOCK ', content)
    # 移除 LaTeX 命令 \command{...}
    content = re.sub(r'\\[a-zA-Z]+\{[^}]*\}', ' LATEX ', content)
    return content

def extract_links(content, file_path):
    """提取markdown中的所有链接"""
    links = []
    
    # 先移除数学公式
    content_no_math = remove_math_formulas(content)
    
    # 匹配 [text](url) 格式
    pattern = r'\[([^\]]+)\]\(([^)]+)\)'
    matches = re.finditer(pattern, content_no_math)
    
    for match in matches:
        text = match.group(1)
        url = match.group(2)
        
        # 跳过 LaTeX 公式中的内容
        if url.startswith('\\') and len(url) < 50:
            # 可能是LaTeX命令，跳过
            continue
        
        # 跳过纯数学符号
        if re.match(r'^[\\\{\}\^_\-\w\s\[\]\|\(\)]+$', url) and len(url) < 30:
            # 可能是数学表达式，检查是否在原内容中被$包围
            start = match.start()
            context = content_no_math[max(0, start-10):min(len(content_no_math), start+len(match.group(0))+10)]
            if 'MATH' in context:
                continue
        
        # 获取行号（在原内容中）
        start = match.start()
        line_num = content_no_math[:start].count('\n') + 1
        
        links.append({
            'text': text,
            'url': url,
            'line': line_num,
            'full_match': match.group(0)
        })
    
    return links

def check_link_validity(link, base_dir, file_path):
    """检查链接是否有效"""
    url = link['url']
    
    # 跳过外部链接
    if url.startswith('http://') or url.startswith('https://') or url.startswith('//'):
        return {'valid': True, 'type': 'external'}
    
    # 跳过邮件链接
    if url.startswith('mailto:'):
        return {'valid': True, 'type': 'mailto'}
    
    # 跳过锚点链接（只包含#）
    if url.startswith('#'):
        return {'valid': True, 'type': 'anchor'}
    
    # 跳过图片和其他资源
    if any(url.endswith(ext) for ext in ['.png', '.jpg', '.jpeg', '.gif', '.svg', '.pdf', '.zip']):
        return {'valid': True, 'type': 'asset'}
    
    # 跳过单字符链接（可能是脚注标记等）
    if len(url) <= 1:
        return {'valid': True, 'type': 'short'}
    
    # 处理相对路径
    file_dir = os.path.dirname(file_path)
    
    # 移除锚点部分
    url_without_anchor = url.split('#')[0]
    
    # 检查是否是目录链接（以/结尾）
    if url_without_anchor.endswith('/'):
        target_path = os.path.normpath(os.path.join(file_dir, url_without_anchor))
        if os.path.isdir(target_path):
            readme_exists = os.path.exists(os.path.join(target_path, 'README.md'))
            index_exists = os.path.exists(os.path.join(target_path, '_index.md'))
            
            if readme_exists:
                return {
                    'valid': False, 
                    'type': 'directory_link',
                    'fixed_url': url.replace('/', '/README.md') if url.endswith('/') else url + '/README.md'
                }
            elif index_exists:
                return {
                    'valid': False, 
                    'type': 'directory_link',
                    'fixed_url': url.replace('/', '/_index.md') if url.endswith('/') else url + '/_index.md'
                }
            else:
                return {'valid': False, 'type': 'directory_without_index'}
        else:
            return {'valid': False, 'type': 'directory_not_exist'}
    
    # 检查文件链接
    target_path = os.path.normpath(os.path.join(file_dir, url_without_anchor))
    
    if os.path.exists(target_path):
        return {'valid': True, 'type': 'file'}
    else:
        # 检查是否缺少.md扩展名
        with_md = target_path + '.md'
        if os.path.exists(with_md):
            return {
                'valid': False, 
                'type': 'missing_md_extension',
                'fixed_url': url + '.md' if not '#' in url else url.split('#')[0] + '.md' + '#' + url.split('#')[1]
            }
        return {'valid': False, 'type': 'file_not_found'}

def main():
    print('=' * 60)
    print('扫描断链情况（改进版）')
    print('=' * 60)
    
    root_dir = '.'
    print('\n正在查找所有 Markdown 文件...')
    md_files = find_markdown_files(root_dir)
    print(f'找到 {len(md_files)} 个 Markdown 文件')
    
    all_links = []
    broken_links = []
    directory_links = []
    file_not_found_links = []
    missing_extension_links = []
    
    print('\n正在分析链接...')
    for i, file_path in enumerate(md_files):
        if i % 100 == 0:
            print(f'  已处理 {i}/{len(md_files)} 个文件...', end='\r')
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            print(f'\n  无法读取文件 {file_path}: {e}')
            continue
        
        links = extract_links(content, file_path)
        
        for link in links:
            all_links.append({
                'file': file_path,
                **link
            })
            
            result = check_link_validity(link, root_dir, file_path)
            
            if not result['valid']:
                broken_info = {
                    'file': file_path,
                    **link,
                    'error_type': result['type'],
                    'fixed_url': result.get('fixed_url', '')
                }
                broken_links.append(broken_info)
                
                if result['type'] == 'directory_link':
                    directory_links.append(broken_info)
                elif result['type'] == 'file_not_found':
                    file_not_found_links.append(broken_info)
                elif result['type'] == 'missing_md_extension':
                    missing_extension_links.append(broken_info)
    
    print(f'\n\n{"=" * 60}')
    print('扫描结果')
    print('=' * 60)
    print(f'\n总链接数: {len(all_links)}')
    print(f'断链总数: {len(broken_links)}')
    print(f'\n断链类型分布:')
    print(f'  - 目录链接: {len(directory_links)}')
    print(f'  - 文件不存在: {len(file_not_found_links)}')
    print(f'  - 缺少.md扩展名: {len(missing_extension_links)}')
    
    # 按文件统计
    broken_by_file = defaultdict(int)
    for link in broken_links:
        broken_by_file[link['file']] += 1
    
    print(f'\n断链最多的文件（前15个）:')
    for file_path, count in sorted(broken_by_file.items(), key=lambda x: -x[1])[:15]:
        print(f'  {file_path}: {count} 个')
    
    # 保存详细结果
    result = {
        'total_files': len(md_files),
        'total_links': len(all_links),
        'broken_links': len(broken_links),
        'directory_links': directory_links,
        'file_not_found': file_not_found_links,
        'missing_extension': missing_extension_links
    }
    
    with open('current_broken_links_v2.json', 'w', encoding='utf-8') as f:
        json.dump(result, f, ensure_ascii=False, indent=2)
    
    print(f'\n详细结果已保存到: current_broken_links_v2.json')
    print('=' * 60)

if __name__ == '__main__':
    main()
