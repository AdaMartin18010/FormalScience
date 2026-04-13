import os, re
from pathlib import Path

placeholder_files = []
for fp in Path('Composed').rglob('*.md'):
    try:
        content = fp.read_text(encoding='utf-8')
        if re.search(r'status:\s*"?待完善"?', content):
            placeholder_files.append(str(fp))
    except Exception:
        pass

print(f"Removing {len(placeholder_files)} placeholder files from Composed...")
for fp in placeholder_files:
    os.remove(fp)
    print(f"  DEL: {fp}")

# Clean up empty directories
empty_dirs = []
for root, dirs, files in os.walk('Composed', topdown=False):
    for d in dirs:
        dir_path = os.path.join(root, d)
        if not os.listdir(dir_path):
            os.rmdir(dir_path)
            empty_dirs.append(dir_path)

print(f"\nRemoved {len(empty_dirs)} empty directories")
for d in empty_dirs:
    print(f"  RMDIR: {d}")

# Verify
remaining = []
for fp in Path('Composed').rglob('*.md'):
    try:
        content = fp.read_text(encoding='utf-8')
        if re.search(r'status:\s*"?待完善"?', content):
            remaining.append(str(fp))
    except Exception:
        pass

print(f"\nRemaining placeholders in Composed: {len(remaining)}")
