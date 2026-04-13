import re, os
from pathlib import Path

files = []
for fp in Path('Composed').rglob('*.md'):
    try:
        content = fp.read_text(encoding='utf-8')
        if re.search(r'status:\s*"?待完善"?', content):
            files.append((str(fp), len(content), 'placeholder' in content.lower() or '自动生成' in content or '内容待补充' in content))
    except Exception:
        pass

print(f'Total Composed placeholders: {len(files)}')
for fp, size, is_auto in files:
    tag = 'AUTO' if is_auto else 'MANUAL'
    print(f'{size:>8} [{tag}] {fp}')
