#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import json
import os

with open('current_broken_links.json', 'r', encoding='utf-8') as f:
    data = json.load(f)

# 查看混合路径链接
print('混合路径链接示例（前15个）:')
count = 0
for item in data['file_not_found']:
    url = item['url']
    if '\\' in url:
        print(f"  文件: {item['file']}")
        print(f"  URL: {url}")
        print(f"  文本: {item['text']}")
        
        # 检查修复后的路径
        fixed_url = url.replace('\\', '/')
        file_dir = os.path.dirname(item['file'])
        target_path = os.path.normpath(os.path.join(file_dir, fixed_url))
        print(f"  预期路径: {target_path}")
        print(f"  存在: {os.path.exists(target_path)}")
        print()
        count += 1
        if count >= 15:
            break
