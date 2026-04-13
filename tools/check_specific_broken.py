import json
import sys

with open('current_broken_links_v2.json', 'r', encoding='utf-8') as f:
    data = json.load(f)

fnf = data.get('file_not_found', [])

targets = [
    '.\\docs\\Refactor\\exercises\\README.md',
    '.\\docs\\Refactor\\06_调度系统\\05_形式化证明\\_index.md',
    '.\\view\\concept\\理念分析与扩展分析\\文件关联体系设计.md',
    '.\\Concept\\Software_Perspective\\00_Master_Index.md',
    '.\\Concept\\Software_Perspective\\LEARNING_PATHS.md',
    '.\\Concept\\QUICK_START.md',
    '.\\Concept\\TuningCompute\\02_技术实施指南与最佳实践.md',
    '.\\Composed\\跨视角引用规范.md',
    '.\\docs\\Matter\\FormalModel\\Model\\Math\\Algebra\\从范畴论视角审视代数.md',
]

for t in targets:
    items = [item for item in fnf if item['file'] == t]
    print(f'{t}: {len(items)} broken links')
    for item in items:
        print(f'  {item["url"]}')
    print()
