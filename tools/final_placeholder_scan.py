import re
from pathlib import Path

total = 0
for base in ['docs/Refactor', 'Concept', 'Composed', 'FormalRE', 'view', 'Engineer', 'Tech']:
    if not Path(base).exists():
        continue
    count = 0
    files = []
    for fp in Path(base).rglob('*.md'):
        try:
            content = fp.read_text(encoding='utf-8')
            if re.search(r'status:\s*"?待完善"?', content):
                count += 1
                files.append(str(fp))
        except Exception:
            pass
    total += count
    print(f'{base}: {count} placeholders')
    if count > 0:
        for f in files[:5]:
            print(f'  - {f}')

print(f'Total placeholders: {total}')
