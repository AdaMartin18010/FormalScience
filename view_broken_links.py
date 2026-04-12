#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import json

with open('current_broken_links.json', 'r', encoding='utf-8') as f:
    data = json.load(f)

print('断链类型分布:')
print(f"  文件不存在: {len(data['file_not_found'])}")

print('\n\n前30个文件不存在的链接:')
for item in data['file_not_found'][:30]:
    print(f"  文件: {item['file']}")
    print(f"    行: {item['line']}, URL: {item['url']}")
    print(f"    文本: {item['text']}")
    print()

# 统计URL模式
print('\n\n常见断链URL模式（前20个）:')
from collections import Counter
url_patterns = Counter()
for item in data['file_not_found']:
    url = item['url']
    # 简化URL以统计模式
    if '../' in url:
        url_patterns['包含../的相对路径'] += 1
    elif './' in url:
        url_patterns['包含./的相对路径'] += 1
    elif url.startswith('#'):
        url_patterns['纯锚点链接'] += 1
    else:
        url_patterns[url] += 1

for pattern, count in url_patterns.most_common(20):
    print(f"  {pattern}: {count} 次")
