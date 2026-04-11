# 类型检查数据集

本数据集包含类型系统的示例数据，用于类型检查算法验证、教学和测试。

## 文件说明

| 文件名 | 格式 | 说明 |
|--------|------|------|
| `type_expressions.json` | JSON | 类型表达式示例 |
| `error_cases.json` | JSON | 类型错误案例 |
| `test_cases.json` | JSON | 测试用例集合 |
| `inference_examples.csv` | CSV | 类型推断示例 |

## 类型系统特性

数据集涵盖的类型系统特性：

1. **简单类型**
   - 基本类型: Int, Bool, String, Float
   - 函数类型: A → B
   - 元组类型: A × B

2. **参数多态**
   - 类型变量: α, β
   - 全称量化: ∀α.τ
   - Hindley-Milner 类型推断

3. **子类型**
   - 记录子类型
   - 函数子类型
   - 宽度/深度子类型

4. **依赖类型**
   - 依赖函数: (x:A) → B(x)
   - 依赖对: (x:A) × B(x)
   - 索引类型

## 使用示例

```python
import json

# 加载类型表达式
with open('type_expressions.json', 'r') as f:
    types = json.load(f)

# 验证特定类型
func_type = types['expressions'][0]
print(f"Type: {func_type['notation']}")
```

## 数据规范

- 类型表示: 使用标准数学符号
- 错误代码: ERR001-ERR999
- 难度等级: beginner, intermediate, advanced
