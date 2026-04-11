# 基准测试数据集

本数据集包含形式科学相关算法的性能测试结果、对比数据和历史趋势。

## 文件说明

| 文件名 | 格式 | 说明 |
|--------|------|------|
| `performance_results.csv` | CSV | 性能测试结果 |
| `comparison_data.json` | JSON | 算法对比数据 |
| `trends.json` | JSON | 历史趋势数据 |
| `scalability.csv` | CSV | 可扩展性测试结果 |

## 测试环境

### 硬件配置
- CPU: Intel Core i7-12700H @ 2.3GHz
- 内存: 32GB DDR4
- 存储: NVMe SSD

### 软件配置
- OS: Windows 11 / WSL2 Ubuntu 22.04
- Rust: 1.75.0
- Python: 3.11
- Node.js: 20.0

## 测试类别

1. **调度算法**: RM, EDF, LLF, Partitioned-EDF
2. **类型推断**: HM算法，依赖类型检查
3. **Petri网分析**: 可达性、模型检测
4. **SAT/SMT求解**: 约束求解性能

## 度量指标

- 执行时间 (ms/μs)
- 内存使用 (MB)
- CPU利用率 (%)
- 吞吐量 (ops/s)

## 使用示例

```python
import pandas as pd
import json

# 加载性能数据
df = pd.read_csv('performance_results.csv')

# 按算法分组统计
algo_stats = df.groupby('algorithm')['execution_time_ms'].agg(['mean', 'std', 'min', 'max'])
```

## 数据更新

- 更新频率: 每次重大版本发布
- 历史保留: 最近20个版本
