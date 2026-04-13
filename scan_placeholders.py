import re
from pathlib import Path

for base in ['Concept', 'Composed', 'FormalRE', 'view', 'Engineer', 'Tech', 'docs']:
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
    print(f'{base}: {count} placeholders')
    if count > 0 and count <= 20:
        for f in files:
            print(f'  - {f}')
    elif count > 20:
        print(f'  (showing first 10)')
        for f in files[:10]:
            print(f'  - {f}')
