#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
综合断链修复脚本
"""

import json
import os
import re
from pathlib import Path
from collections import defaultdict

# 加载当前断链数据
with open('current_broken_links.json', 'r', encoding='utf-8') as f:
    broken_data = json.load(f)

print('=' * 70)
print('FormalScience 项目断链综合修复')
print('=' * 70)

stats = {
    'malformed_fixed': 0,
    'placeholder_removed': 0,
    'cross_dir_fixed': 0,
    'errors': []
}

# ========== 1. 修复格式错误的链接 ==========
print('\n[阶段 1] 修复格式错误的链接...')
print('-' * 70)

# 查找形式如 "01_核心概念映射READMEmd" 的链接
malformed_pattern = re.compile(r'^(\d{2}_[^/]+)(READMEmd)$')

def fix_malformed_url(url):
    """修复格式错误的URL"""
    match = malformed_pattern.match(url)
    if match:
        dir_name = match.group(1)
        return f'./{dir_name}/README.md'
    
    # 检查其他模式
    # 如 "011_基本类型单元md" → "./01.1_基本类型单元.md"
    subfile_pattern = re.compile(r'^0(\d)(\d)_(.+?)md$')
    subfile_match = subfile_pattern.match(url)
    if subfile_match:
        chapter = subfile_match.group(1)
        section = subfile_match.group(2)
        name = subfile_match.group(3)
        return f'./{chapter}{section}_{name}.md'
    
    return None

# 按文件处理
file_not_found = broken_data.get('file_not_found', [])
files_to_fix = defaultdict(list)

for item in file_not_found:
    url = item['url']
    fixed = fix_malformed_url(url)
    if fixed:
        files_to_fix[item['file']].append({
            'original': item,
            'fixed_url': fixed
        })

print(f'发现 {len(files_to_fix)} 个文件包含格式错误的链接')

for file_path, items in files_to_fix.items():
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
            
            # 构建新的链接
            text = item['text']
            new_link = f'[{text}]({fixed_url})'
            
            if full_match in content:
                content = content.replace(full_match, new_link)
                fixed_count += 1
                stats['malformed_fixed'] += 1
        
        if fixed_count > 0:
            # 写入修复后的内容
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(content)
            print(f'  ✓ {file_path}: 修复了 {fixed_count} 个格式错误链接')
        
    except Exception as e:
        stats['errors'].append(f'{file_path}: {str(e)}')
        print(f'  ✗ {file_path}: 错误 - {e}')

# ========== 2. 修复/移除占位符链接 ==========
print('\n[阶段 2] 处理占位符链接...')
print('-' * 70)

# 定义占位符模式
placeholder_patterns = [
    (r'\[([^\]]+)\]\(链接地址\)', r'\1'),  # [文本](链接地址) → 文本
    (r'\[([^\]]+)\]\(URL\)', r'\1'),      # [文本](URL) → 文本
    (r'\[([^\]]+)\]\(相对路径\)', r'\1'), # [文本](相对路径) → 文本
    (r'\[([^\]]+)\]\(\./路径\)', r'\1'),  # [文本](./路径) → 文本
]

placeholder_files = defaultdict(int)
for item in file_not_found:
    url = item['url']
    if url in ['链接地址', 'URL', '相对路径', './路径', '路径']:
        placeholder_files[item['file']] += 1

print(f'发现 {len(placeholder_files)} 个文件包含占位符链接')

for file_path in placeholder_files:
    if not os.path.exists(file_path):
        continue
    
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        original_content = content
        fixed_count = 0
        
        for pattern, replacement in placeholder_patterns:
            new_content, count = re.subn(pattern, replacement, content)
            if count > 0:
                content = new_content
                fixed_count += count
                stats['placeholder_removed'] += count
        
        if fixed_count > 0:
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(content)
            print(f'  ✓ {file_path}: 移除了 {fixed_count} 个占位符链接')
        
    except Exception as e:
        stats['errors'].append(f'{file_path}: {str(e)}')

# ========== 3. 分析跨目录引用错误 ==========
print('\n[阶段 3] 分析跨目录引用错误...')
print('-' * 70)

# 查找常见的跨目录引用问题
cross_dir_issues = []
for item in file_not_found:
    url = item['url']
    if '../' in url or (url.startswith('./') and 'README.md' in url):
        # 检查是否是跨目录引用
        file_dir = os.path.dirname(item['file'])
        target_path = os.path.normpath(os.path.join(file_dir, url))
        
        if not os.path.exists(target_path):
            # 尝试查找实际文件位置
            filename = os.path.basename(url)
            # 在项目中搜索该文件
            cross_dir_issues.append({
                'file': item['file'],
                'url': url,
                'line': item['line'],
                'text': item['text'],
                'expected': target_path
            })

print(f'发现 {len(cross_dir_issues)} 个可能的跨目录引用错误')

# 按文件分组显示前10个
issues_by_file = defaultdict(list)
for issue in cross_dir_issues:
    issues_by_file[issue['file']].append(issue)

print('\n前10个文件中的跨目录引用错误:')
for file_path, issues in list(issues_by_file.items())[:10]:
    print(f'\n  {file_path}:')
    for issue in issues[:3]:
        print(f'    行{issue["line"]}: [{issue["text"]}]({issue["url"]})')

# ========== 4. 生成修复报告 ==========
print('\n[阶段 4] 生成修复报告...')
print('-' * 70)

report = f"""# FormalScience 项目断链修复报告

## 执行时间
{__file__}

## 修复统计

| 类型 | 数量 |
|------|------|
| 格式错误链接已修复 | {stats['malformed_fixed']} |
| 占位符链接已移除 | {stats['placeholder_removed']} |
| 跨目录引用错误（待修复） | {len(cross_dir_issues)} |
| 错误数 | {len(stats['errors'])} |

## 详细情况

### 1. 格式错误链接修复
修复了形如 `01_核心概念映射READMEmd` → `./01_核心概念映射/README.md` 的链接。

### 2. 占位符链接处理
将形如 `[文本](链接地址)` 的占位符链接转换为纯文本 `文本`。

### 3. 跨目录引用错误
发现 {len(cross_dir_issues)} 个跨目录引用错误，需要人工检查：
- 确认文件是否被移动或重命名
- 确认链接路径是否正确

### 4. 主要问题文件
"""

# 添加问题最多的文件
for file_path, count in sorted(placeholder_files.items(), key=lambda x: -x[1])[:10]:
    report += f'- {file_path}: {count} 个占位符\n'

report += "\n## 建议\n\n1. 对于跨目录引用错误，建议：\n"
report += "   - 使用全局搜索找到文件实际位置\n"
report += "   - 修正相对路径\n"
report += "   - 或者将链接改为纯文本\n\n"
report += "2. 对于缺失的文件，建议：\n"
report += "   - 创建空文档作为占位\n"
report += "   - 或者删除无效链接\n"

# 写入报告
report_path = 'BROKEN_LINKS_FIX_REPORT_CURRENT.md'
with open(report_path, 'w', encoding='utf-8') as f:
    f.write(report)

print(f'修复报告已保存到: {report_path}')
print('\n' + '=' * 70)
print(f'格式错误链接修复: {stats["malformed_fixed"]}')
print(f'占位符链接移除: {stats["placeholder_removed"]}')
print(f'跨目录引用错误（待修复）: {len(cross_dir_issues)}')
print(f'错误数: {len(stats["errors"])}')
print('=' * 70)
