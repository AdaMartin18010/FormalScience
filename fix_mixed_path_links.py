#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
修复混合路径格式的链接
"""

import json
import os
import re
from collections import defaultdict

# 加载当前断链数据
with open('current_broken_links.json', 'r', encoding='utf-8') as f:
    broken_data = json.load(f)

print('=' * 70)
print('修复混合路径格式链接')
print('=' * 70)

stats = {
    'mixed_path_fixed': 0,
    'errors': []
}

file_not_found = broken_data.get('file_not_found', [])

# 找出混合路径的链接
mixed_path_links = []
for item in file_not_found:
    url = item['url']
    # 检查是否同时包含 / 和 \，或者包含\
    if ('/' in url and '\\' in url) or '\\' in url:
        # 将反斜杠替换为正斜杠
        fixed_url = url.replace('\\', '/')
        # 检查修复后的路径是否存在
        file_dir = os.path.dirname(item['file'])
        target_path = os.path.normpath(os.path.join(file_dir, fixed_url))
        
        if os.path.exists(target_path):
            mixed_path_links.append({
                'original': item,
                'fixed_url': fixed_url,
                'target_exists': True
            })
        else:
            mixed_path_links.append({
                'original': item,
                'fixed_url': fixed_url,
                'target_exists': False
            })

print(f'\n发现 {len(mixed_path_links)} 个混合路径链接')
exists_count = sum(1 for item in mixed_path_links if item['target_exists'])
print(f'其中 {exists_count} 个修复后目标文件存在')

# 按文件分组
links_by_file = defaultdict(list)
for item in mixed_path_links:
    if item['target_exists']:  # 只修复目标存在的链接
        links_by_file[item['original']['file']].append(item)

print(f'\n分布在 {len(links_by_file)} 个文件中')

# 修复链接
for file_path, items in links_by_file.items():
    if not os.path.exists(file_path):
        print(f'  跳过: 文件不存在 {file_path}')
        continue
    
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        original_content = content
        fixed_count = 0
        
        for item_info in items:
            item = item_info['original']
            fixed_url = item_info['fixed_url']
            full_match = item['full_match']
            original_url = item['url']
            
            # 构建新的链接
            new_full_match = full_match.replace(original_url, fixed_url)
            
            if full_match in content:
                content = content.replace(full_match, new_full_match)
                fixed_count += 1
                stats['mixed_path_fixed'] += 1
            else:
                # 尝试其他方式匹配
                text = item['text']
                pattern = re.escape(f'[{text}](') + re.escape(original_url) + ')'
                new_link = f'[{text}]({fixed_url})'
                new_content, count = re.subn(pattern, new_link, content)
                if count > 0:
                    content = new_content
                    fixed_count += count
                    stats['mixed_path_fixed'] += count
        
        if fixed_count > 0:
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(content)
            print(f'  ✓ {file_path}: 修复了 {fixed_count} 个混合路径链接')
        
    except Exception as e:
        stats['errors'].append(f'{file_path}: {str(e)}')
        print(f'  ✗ {file_path}: 错误 - {e}')

# 生成报告
print('\n' + '=' * 70)
print(f'混合路径链接已修复: {stats["mixed_path_fixed"]}')
print(f'错误数: {len(stats["errors"])}')
print('=' * 70)
