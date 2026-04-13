import os
from pathlib import Path

view_dir = Path('Composed/schedule_formal_view/view')

# Explicit list of every intermediate file that must go
files_to_delete = [
    '00_调度原理核心理论梳理.md',
    '01_硬件层调度原理梳理.md',
    '02_系统总线层调度原理梳理.md',
    '03_OS抽象层调度原理梳理.md',
    '04_虚拟化容器化沙盒化调度原理梳理.md',
    '05_分布式系统调度原理梳理.md',
    '06_编程模型层调度原理梳理.md',
    '07_性能优化与安全调度原理梳理.md',
    '08_技术演进与对标调度原理梳理.md',
    '09_形式化理论与证明调度原理梳理.md',
    '10_AI驱动调度原理梳理.md',
    '11_企业架构调度原理梳理.md',
    '12_跨层次调度协同原理梳理.md',
    'schedule_formal_view.md',
    'schedule_formal_view_原始备份.md',
    'schedule_formal_view_语义对齐版.md',
    'schedule_formal_view_重构版.md',
    'schedule_view_全面梳理与扩展.md',
    '主题梳理完成总结_2025-11-14.md',
    '主题梳理工作完成确认_2025-11-14.md',
    '主题梳理文件使用指南.md',
    '主题梳理文件快速导航.md',
    '主题梳理文件索引.md',
    'view文件夹主题梳理最终报告_2025-11-14.md',
    'view文件夹全面梳理总结_2025-11-14.md',
    'view文件夹内容对齐计划.md',
    'view文件夹对齐总结.md',
    '全面梳理完成总结_2025-11-14.md',
    '全面梳理总结_2025-11-14.md',
    '最终完成总结.md',
    '最终完成报告_2025-11-14.md',
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

for fname in files_to_delete:
    fp = view_dir / fname
    if fp.exists():
        os.remove(fp)
        print(f'DEL: {fname}')
    else:
        print(f'ALREADY_GONE: {fname}')

# Verify remaining
remaining = [f.name for f in view_dir.iterdir() if f.is_file()]
print(f'\nRemaining files in view/: {len(remaining)}')
for r in remaining:
    print(f'  {r}')
