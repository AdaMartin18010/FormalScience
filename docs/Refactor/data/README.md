# Formal Science 数据集

本目录包含形式科学相关的示例数据集，用于教学、测试和基准评估。

## 目录结构

```
data/
├── README.md              # 本文件
├── scheduling/            # 调度数据集
│   ├── README.md
│   ├── task_sets.json     # 任务集示例
│   ├── schedules.json     # 调度结果
│   └── metrics.json       # 性能指标
├── type_checking/         # 类型检查数据集
│   ├── README.md
│   ├── type_expressions.json
│   ├── error_cases.json
│   └── test_cases.json
├── petri_nets/            # Petri网数据集
│   ├── README.md
│   ├── models.json        # 经典网络模型
│   ├── state_spaces.json  # 状态空间数据
│   └── reachability.json  # 可达性分析
└── benchmarks/            # 基准测试数据
    ├── README.md
    ├── performance_results.csv
    ├── comparison_data.json
    └── trends.json
```

## 数据格式说明

### JSON 数据

所有JSON数据文件使用UTF-8编码，遵循标准JSON格式规范。

### CSV 数据

CSV文件使用UTF-8编码，逗号分隔，包含表头行。

## 使用指南

1. **调度数据集**: 用于调度算法开发和测试
2. **类型检查数据集**: 用于类型系统验证和教学
3. **Petri网数据集**: 用于并发系统建模和分析
4. **基准测试数据**: 用于性能评估和对比

## 数据版本

- 版本: 1.0.0
- 创建日期: 2026-04-11
- 数据量: 约500+ 条记录

## 许可证

本数据集仅供学习和研究使用。
