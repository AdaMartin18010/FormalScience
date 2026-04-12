#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
修复剩余断链的脚本
"""

import json
import os
import re
from pathlib import Path
from collections import defaultdict

# 加载断链详情
with open('broken_links_details.json', 'r', encoding='utf-8') as f:
    data = json.load(f)

print('=' * 60)
print('FormalScience 项目断链修复脚本')
print('=' * 60)

# 统计修复情况
stats = {
    'directory_links_fixed': 0,
    'file_not_found_checked': 0,
    'anchor_fixed': 0,
    'errors': []
}

# ========== 1. 修复目录链接 ==========
print('\n[阶段 1] 修复目录链接...')
print('-' * 40)

directory_links = data.get('directory_links', [])
print(f'共发现 {len(directory_links)} 个目录链接需要修复')

# 按文件分组
dir_links_by_file = defaultdict(list)
for item in directory_links:
    dir_links_by_file[item['file']].append(item)

print(f'分布在 {len(dir_links_by_file)} 个文件中')

# 检查目标目录是否存在相应的README.md
for file_path, items in dir_links_by_file.items():
    if not os.path.exists(file_path):
        # 尝试其他路径格式
        alt_path = file_path.replace('\\', '/')
        if os.path.exists(alt_path):
            file_path = alt_path
        else:
            print(f'  跳过: 文件不存在 {file_path}')
            continue
    
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
        
        original_content = content
        fixed_count = 0
        
        for item in items:
            full_match = item.get('full_match', '')
            url = item.get('url', '')
            fixed_url = item.get('fixed_url', '')
            
            if not full_match or not fixed_url:
                continue
            
            # 构建新的链接
            # 从 full_match 中提取显示文本和URL
            match = re.match(r'\[([^\]]+)\]\(([^)]+)\)', full_match)
            if match:
                text = match.group(1)
                # 确保 fixed_url 是相对于当前文件的正确路径
                new_link = f'[{text}]({fixed_url})'
                
                if full_match in content:
                    content = content.replace(full_match, new_link)
                    fixed_count += 1
                    stats['directory_links_fixed'] += 1
                else:
                    # 尝试只匹配URL部分
                    escaped_url = re.escape(url)
                    pattern = rf'\[([^\]]+)\]\({escaped_url}\)'
                    replacement = rf'[\1]({fixed_url})'
                    new_content, count = re.subn(pattern, replacement, content)
                    if count > 0:
                        content = new_content
                        fixed_count += count
                        stats['directory_links_fixed'] += count
        
        if fixed_count > 0:
            # 备份原文件
            backup_path = file_path + '.bak'
            with open(backup_path, 'w', encoding='utf-8') as f:
                f.write(original_content)
            
            # 写入修复后的内容
            with open(file_path, 'w', encoding='utf-8') as f:
                f.write(content)
            print(f'  ✓ {file_path}: 修复了 {fixed_count} 个目录链接')
        
    except Exception as e:
        stats['errors'].append(f'{file_path}: {str(e)}')
        print(f'  ✗ {file_path}: 错误 - {e}')

# ========== 2. 检查文件不存在的链接 ==========
print('\n[阶段 2] 分析文件不存在的链接...')
print('-' * 40)

file_not_found = data.get('file_not_found', [])
print(f'共发现 {len(file_not_found)} 个文件不存在的链接')

# 按文件分组
file_not_found_by_file = defaultdict(list)
for item in file_not_found:
    file_not_found_by_file[item['file']].append(item)

print(f'分布在 {len(file_not_found_by_file)} 个文件中')

# 分析哪些可能是真正的断链，哪些可能是路径问题
potential_fixes = []
for file_path, items in file_not_found_by_file.items():
    for item in items:
        url = item.get('url', '')
        # 跳过明显的占位符
        if url in ['链接地址', 'URL', '相对路径', '文件.md', './文件.md#章节锚点']:
            continue
        # 检查是否是相对路径
        if url.startswith('./') or url.startswith('../'):
            potential_fixes.append(item)

print(f'其中 {len(potential_fixes)} 个可能是可修复的相对路径链接')

# ========== 3. 生成修复报告 ==========
print('\n[阶段 3] 生成修复报告...')
print('-' * 40)

report = f"""# FormalScience 项目断链修复报告

## 执行时间
{os.path.basename(__file__)}

## 修复统计

| 类型 | 数量 |
|------|------|
| 目录链接已修复 | {stats['directory_links_fixed']} |
| 文件不存在链接已检查 | {len(file_not_found)} |
| 错误数 | {len(stats['errors'])} |

## 详细情况

### 1. 目录链接修复
- 共处理 {len(directory_links)} 个目录链接
- 成功修复 {stats['directory_links_fixed']} 个
- 分布在 {len(dir_links_by_file)} 个文件中

### 2. 文件不存在链接
- 共发现 {len(file_not_found)} 个文件不存在的链接
- 分布在 {len(file_not_found_by_file)} 个文件中
- 其中约 {len(potential_fixes)} 个可能是可修复的相对路径链接

### 3. 错误
"""

if stats['errors']:
    report += '\n修复过程中遇到的错误:\n'
    for error in stats['errors'][:20]:  # 只显示前20个错误
        report += f'- {error}\n'
else:
    report += '\n无错误\n'

report += f"""
## 建议

1. 对于文件不存在的链接，需要人工检查：
   - 确认文件是否被移动或重命名
   - 确认链接路径是否正确
   - 确认是否需要创建缺失的文件

2. 修复方法：
   - 目录链接已自动修复为指向 README.md
   - 对于跨目录引用错误，需要手动修正路径
   - 对于锚点不存在的链接，需要创建对应锚点或删除锚点部分

## 文件备份

原文件已备份为 .bak 文件，如需恢复可执行：
```bash
find . -name "*.bak" -exec sh -c 'mv "$1" "${{1%.bak}}"' _ {{}} \;
```
"""

# 写入报告
report_path = 'BROKEN_LINKS_FIX_REPORT.md'
with open(report_path, 'w', encoding='utf-8') as f:
    f.write(report)

print(f'修复报告已保存到: {report_path}')
print('\n' + '=' * 60)
print(f'目录链接修复: {stats["directory_links_fixed"]} / {len(directory_links)}')
print(f'错误数: {len(stats["errors"])}')
print('=' * 60)
