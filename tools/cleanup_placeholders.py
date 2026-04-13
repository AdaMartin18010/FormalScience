import os, re, shutil
from pathlib import Path

top_levels = {
    '01_数学基础', '02_形式语言', '03_编程范式', '04_软件工程',
    '05_形式化理论', '06_调度系统', '07_交叉视角', '08_附录',
    '09_统计学', '10_信息论', '11_系统科学', '12_决策与博弈论',
    '13_认知科学形式模型', '14_形式语言学', '15_社会科学形式化',
    'Matter', 'FormalRE', 'RFC标准', '网络协议'
}

# Phase 1: Remove all placeholder files in duplicate nested directories
duplicate_placeholder_files = []
other_placeholder_files = []
for fp in Path('docs/Refactor').rglob('*.md'):
    try:
        content = fp.read_text(encoding='utf-8')
        if re.search(r'status:\s*"?待完善"?', content):
            rel = os.path.relpath(str(fp), 'docs/Refactor')
            parts = os.path.dirname(rel).split(os.sep)
            nested_tops = [p for p in parts[1:] if p in top_levels]
            if nested_tops:
                duplicate_placeholder_files.append(str(fp))
            else:
                other_placeholder_files.append(str(fp))
    except Exception:
        pass

print(f"Removing {len(duplicate_placeholder_files)} placeholder files in duplicate nested dirs...")
for fp in duplicate_placeholder_files:
    os.remove(fp)
    print(f"  DEL: {fp}")

print(f"\nRemoving {len(other_placeholder_files)} other placeholder files...")
for fp in other_placeholder_files:
    os.remove(fp)
    print(f"  DEL: {fp}")

# Phase 2: Remove the 2 duplicate real content files (canonical versions already exist)
duplicate_real_files = [
    'docs/Refactor/06_调度系统/04_分布式调度/04_软件工程/04_分布式系统/04.1_一致性模型.md',
    'docs/Refactor/06_调度系统/04_分布式调度/04_软件工程/04_分布式系统/04.2_共识算法.md',
]

print(f"\nRemoving {len(duplicate_real_files)} duplicate real content files...")
for fp in duplicate_real_files:
    if os.path.exists(fp):
        os.remove(fp)
        print(f"  DEL: {fp}")

# Phase 3: Clean up empty directories (bottom-up)
empty_dirs = []
for root, dirs, files in os.walk('docs/Refactor', topdown=False):
    for d in dirs:
        dir_path = os.path.join(root, d)
        # Check if empty
        if not os.listdir(dir_path):
            os.rmdir(dir_path)
            empty_dirs.append(dir_path)

print(f"\nRemoved {len(empty_dirs)} empty directories")
for d in empty_dirs[:20]:
    print(f"  RMDIR: {d}")
if len(empty_dirs) > 20:
    print(f"  ... and {len(empty_dirs) - 20} more")

# Verification
remaining = []
for fp in Path('docs/Refactor').rglob('*.md'):
    try:
        content = fp.read_text(encoding='utf-8')
        if re.search(r'status:\s*"?待完善"?', content):
            remaining.append(str(fp))
    except Exception:
        pass

print(f"\nRemaining placeholder files in docs/Refactor: {len(remaining)}")
for fp in remaining:
    print(f"  REMAIN: {fp}")
