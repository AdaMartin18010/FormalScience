import os
from pathlib import Path

# Patterns to delete in Composed/schedule_formal_view/
remove_patterns = [
    '*完成报告*.md',
    '*完成总结*.md',
    '*进度总结*.md',
    '*充实计划*.md',
    '*实施方案*.md',
    '*执行报告*.md',
    '*增强说明*.md',
    '*增强完成报告*.md',
    '*内容填充*.md',
    '*内容补充*.md',
    '*内容扩展*.md',
    '*整合view文件*.md',
    '*主题扩展完成*.md',
    '*基础调度层文档完善*.md',
    '*严谨性增强*.md',
    '*结构说明*.md',
    '*使用指南*.md',
    '*文档质量检查清单*.md',
    '*重复文件归档说明*.md',
    '*文件映射计划*.md',
    '*改进完善计划*.md',
    '*整合完成总结*.md',
    '*整合进度报告*.md',
    '*原理梳理*.md',
    'schedule_formal_view_原始备份.md',
    'schedule_formal_view_语义对齐版.md',
    'schedule_formal_view_重构版.md',
    'schedule_view_全面梳理与扩展.md',
]

base = Path('Composed/schedule_formal_view')
deleted = []

for pattern in remove_patterns:
    for fp in base.glob(pattern):
        if fp.is_file():
            os.remove(fp)
            deleted.append(str(fp))

# Also cleanup view/ subdirectory intermediate files
view_dir = base / 'view'
if view_dir.exists():
    view_patterns = [
        'schedule_formal_view.md',
        'schedule_formal_view_重构版.md',
        'schedule_formal_view_原始备份.md',
        'schedule_formal_view_语义对齐版.md',
        'schedule_view_全面梳理与扩展.md',
        '*主题梳理*.md',
        '*view文件夹*.md',
        '*全面梳理*.md',
        '*最终完成*.md',
        '*改进完善计划*.md',
        '*整合完成总结*.md',
        '*整合进度报告*.md',
        '*文件映射计划*.md',
        '*文档完整性检查清单*.md',
        '*重复文件归档说明*.md',
        '*归纳总结*.md',
        '*实践案例汇总*.md',
        '*技术选型指南*.md',
        '2025年技术趋势*.md',
    ]
    for pattern in view_patterns:
        for fp in view_dir.glob(pattern):
            if fp.is_file():
                os.remove(fp)
                deleted.append(str(fp))

# Remove empty directories
empty_dirs = []
for root, dirs, files in os.walk(base, topdown=False):
    for d in dirs:
        dir_path = os.path.join(root, d)
        if not os.listdir(dir_path):
            os.rmdir(dir_path)
            empty_dirs.append(dir_path)

print(f'Deleted {len(deleted)} intermediate files')
for f in deleted[:20]:
    print(f'  DEL: {f}')
if len(deleted) > 20:
    print(f'  ... and {len(deleted)-20} more')

print(f'Removed {len(empty_dirs)} empty directories')
for d in empty_dirs:
    print(f'  RMDIR: {d}')
