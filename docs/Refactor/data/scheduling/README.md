# 调度数据集

本数据集包含各类调度问题的示例数据和结果，用于调度算法的开发、测试和评估。

## 文件说明

| 文件名 | 格式 | 说明 |
|--------|------|------|
| `task_sets.json` | JSON | 任务集定义示例 |
| `schedules.json` | JSON | 调度结果示例 |
| `metrics.json` | JSON | 性能指标数据 |
| `workloads.csv` | CSV | 工作负载数据 |

## 任务模型

### 实时任务参数

```json
{
  "id": "任务ID",
  "period": "周期 (ms)",
  "wcet": "最坏执行时间 (ms)",
  "deadline": "截止时间 (ms)",
  "priority": "优先级",
  "type": "任务类型 (periodic/sporadic/aperiodic)"
}
```

### 调度算法

数据集涵盖以下算法：

1. **Rate Monotonic (RM)** - 速率单调
2. **Earliest Deadline First (EDF)** - 最早截止时间优先
3. **Least Laxity First (LLF)** - 最小松弛度优先
4. **Fixed Priority** - 固定优先级
5. **Round Robin** - 时间片轮转

## 使用示例

```python
import json

# 加载任务集
with open('task_sets.json', 'r', encoding='utf-8') as f:
    task_sets = json.load(f)

# 查找特定任务集
rtos_tasks = [ts for ts in task_sets['task_sets']
              if ts['category'] == 'rtos']
```

## 数据来源

- 合成数据: 基于理论模型生成
- 实际数据: 基于嵌入式系统 traces
