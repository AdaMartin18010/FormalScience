#!/usr/bin/env python3
import json
from pathlib import Path

# 加载断链数据
with open('broken_links_data.json', 'r', encoding='utf-8') as f:
    data = json.load(f)

fixed = 0

for link in data['broken_links']:
    source = link['source']
    target = link['target']
    link_text = link['link_text']
    
    source_path = Path(source)
    if not source_path.exists():
        continue
    
    content = source_path.read_text(encoding='utf-8')
    original = content
    
    # 修复思维导图锚点 - 移除锚点
    if '思维导图与知识矩阵.md' in target and '#' in target:
        old = f']({target})'
        new = f']({target.split("#")[0]})'
        content = content.replace(old, new)
    
    # 修复 schedule_formal_view 锚点
    elif 'schedule_formal_view.md' in target and '#' in target:
        old = f']({target})'
        new = '](README.md)'
        content = content.replace(old, new)
    
    # 修复 LINUX_OS_PRINCIPLES
    elif 'LINUX_OS_PRINCIPLES.md' in target:
        old = f'[{link_text}]({target})'
        content = content.replace(old, link_text)
    
    if content != original:
        source_path.write_text(content, encoding='utf-8')
        fixed += 1
        print(f'✓ {source}')

print(f'\n修复完成: {fixed}')
