import os
from pathlib import Path

# 1. Cleanup Composed/schedule_formal_view/view/
view_dir = Path('Composed/schedule_formal_view/view')
patterns = [
    '*原理梳理*.md',
    'schedule_formal_view_原始备份.md',
    'schedule_formal_view_语义对齐版.md',
    'schedule_formal_view_重构版.md',
    'schedule_view_全面梳理与扩展.md',
    '主题梳理*.md',
    'view文件夹*.md',
    '全面梳理*.md',
    '最终完成*.md',
    '改进完善计划.md',
    '整合完成总结.md',
    '整合进度报告.md',
    '文件映射计划.md',
    '文档完整性检查清单.md',
    '重复文件归档说明.md',
    '归纳总结.md',
    '实践案例汇总.md',
    '技术选型指南.md',
    '2025年技术趋势完整索引.md',
    '2025年技术趋势更新总结.md',
]

deleted = 0
for pattern in patterns:
    for fp in view_dir.glob(pattern):
        if fp.is_file():
            os.remove(fp)
            print(f'DEL view: {fp.name}')
            deleted += 1

# 2. Cleanup Composed/schedule_formal_view/ root
root_dir = Path('Composed/schedule_formal_view')
root_patterns = [
    '基础调度层文档完善完成报告.md',
    '交叉引用索引.md',
    '结构说明.md',
    '进度总结.md',
    '论证脉络总览.md',
    '内容补充完善计划与方案.md',
    '内容充实执行报告_2025-12-02.md',
    '内容扩展与充实计划_2025-12-02.md',
    '内容填充实施方案.md',
    '使用指南.md',
    '完成总结.md',
    '文档导航索引.md',
    '文档质量检查清单.md',
    '项目全面完成最终报告.md',
    '项目完成总结.md',
    '严谨性增强说明.md',
    '增强完成报告.md',
    '整合view文件到分层目录.md',
    '主题扩展完成报告.md',
    '主题扩展完成总结.md',
    '调度领域扩展进度.md',
]

for pattern in root_patterns:
    fp = root_dir / pattern
    if fp.exists():
        os.remove(fp)
        print(f'DEL root: {fp.name}')
        deleted += 1

print(f'Total deleted: {deleted}')
