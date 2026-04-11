# Petri网数据集

本数据集包含Petri网的经典模型、状态空间数据和可达性分析结果。

## 文件说明

| 文件名 | 格式 | 说明 |
|--------|------|------|
| `models.json` | JSON | 经典Petri网模型 |
| `state_spaces.json` | JSON | 状态空间数据 |
| `reachability.json` | JSON | 可达性分析结果 |
| `properties.csv` | CSV | 模型属性汇总 |

## Petri网基础

### 定义
一个Petri网是一个五元组 N = (P, T, F, W, M₀)，其中：
- P: 库所(Place)集合
- T: 变迁(Transition)集合
- F: 流关系
- W: 权重函数
- M₀: 初始标识

### 分析技术

1. **可达性分析** - 确定可达标识集
2. **有界性分析** - 检查库所容量限制
3. **活性分析** - 检测死锁和活锁
4. **不变量分析** - P-不变量和T-不变量

## 模型分类

- **经典模型**: 哲学家就餐、生产者-消费者、读者-写者
- **工作流网**: 顺序、并行、选择、循环模式
- **实时系统**: 时间约束模型
- **故障模型**: 容错和恢复机制

## 使用示例

```python
import json

# 加载Petri网模型
with open('models.json', 'r') as f:
    models = json.load(f)

# 获取特定模型
philosophers = [m for m in models['models'] 
                if m['name'] == 'Dining Philosophers'][0]
```

## 可视化

模型可以使用Graphviz或专用Petri网工具进行可视化。
