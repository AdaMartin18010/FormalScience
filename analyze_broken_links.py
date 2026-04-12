#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
断链分析和修复脚本
"""

import json
import os
import re
from pathlib import Path
from collections import defaultdict

# 加载断链详情
with open('broken_links_details.json', 'r', encoding='utf-8') as f:
    data = json.load(f)

print('=== 断链统计 ===')
for key, items in data.items():
    print(f'{key}: {len(items)} 个')

# 显示目录链接的前20个
print('\n=== 目录链接示例（前20个）===')
for item in data.get('directory_links', [])[:20]:
    print(f"  文件: {item['file']}")
    print(f"  行: {item['line']}, URL: {item['url']}")
    print(f"  完整匹配: {item.get('full_match', 'N/A')}")
    print(f"  建议修复: {item.get('fixed_url', 'N/A')}")
    print()

# 按文件统计断链
print('\n=== 目录链接按文件分布 ===')
file_counts = defaultdict(int)
for item in data.get('directory_links', []):
    file_counts[item['file']] += 1

for file, count in sorted(file_counts.items(), key=lambda x: -x[1])[:15]:
    print(f'  {file}: {count} 个')

# 检查文件不存在类型的断链
print('\n=== 文件不存在类型示例（前15个）===')
for item in data.get('file_not_found', [])[:15]:
    print(f"  文件: {item['file']}")
    print(f"  行: {item['line']}, URL: {item['url']}")
    print()
