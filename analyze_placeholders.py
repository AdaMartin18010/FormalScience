import os, re
from pathlib import Path

top_levels = {
    '01_数学基础', '02_形式语言', '03_编程范式', '04_软件工程',
    '05_形式化理论', '06_调度系统', '07_交叉视角', '08_附录',
    '09_统计学', '10_信息论', '11_系统科学', '12_决策与博弈论',
    '13_认知科学形式模型', '14_形式语言学', '15_社会科学形式化',
    'Matter', 'FormalRE', 'RFC标准', '网络协议'
}

placeholder_all = []
for fp in Path('docs/Refactor').rglob('*.md'):
    try:
        content = fp.read_text(encoding='utf-8')
        if re.search(r'status:\s*"?待完善"?', content):
            placeholder_all.append(str(fp))
    except Exception:
        pass

in_duplicate = []
not_in_duplicate = []
for fp in placeholder_all:
    rel = os.path.relpath(fp, 'docs/Refactor')
    parts = os.path.dirname(rel).split(os.sep)
    nested_tops = [p for p in parts[1:] if p in top_levels]
    if nested_tops:
        in_duplicate.append(fp)
    else:
        not_in_duplicate.append(fp)

print(f'All placeholders: {len(placeholder_all)}')
print(f'In duplicate dirs: {len(in_duplicate)}')
print(f'NOT in duplicate dirs: {len(not_in_duplicate)}')
print('--- Non-duplicate placeholders ---')
for fp in not_in_duplicate:
    print(fp)
