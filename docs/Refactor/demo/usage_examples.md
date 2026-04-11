# 使用示例

本文档提供 FormalScience 项目的详细使用示例，帮助您快速上手。

---

## 📖 如何阅读文档

### 1. 文档阅读流程

```
开始
  ↓
阅读 README.md（了解项目概况）
  ↓
阅读入门指南（基础概念）
  ↓
浏览文档结构（了解组织方式）
  ↓
查看示例代码（实践理解）
  ↓
完成练习（巩固知识）
  ↓
进阶学习（深入主题）
```

### 2. 文档类型说明

| 文档类型 | 用途 | 示例 |
|---------|------|------|
| 概念文档 | 解释理论基础 | `docs/Concept/*.md` |
| 教程文档 | 手把手教学 | `docs/Tutorial/*.md` |
| API 文档 | 参考手册 | 函数/类说明 |
| 示例代码 | 实际应用 | `examples/` 目录 |

### 3. 阅读技巧

**技巧 1: 使用大纲视图**
```markdown
# 文档标题
## 1. 概述
## 2. 核心概念
## 3. 使用示例
## 4. 总结
```

**技巧 2: 重点关注代码块**
```python
# 这是示例代码，通常包含关键用法
result = formal_science.calculate(input_data)
print(result)
```

**技巧 3: 查看相关链接**
> 📎 相关文档: [核心概念](../Concept/core_concepts.md)

---

## 🖥️ 如何运行代码

### 环境准备

```bash
# 1. 克隆项目
git clone https://github.com/your-repo/FormalScience.git
cd FormalScience

# 2. 创建虚拟环境（推荐）
python -m venv venv
source venv/bin/activate  # Linux/Mac
# 或
venv\Scripts\activate     # Windows

# 3. 安装依赖
pip install -r requirements.txt
```

### 运行示例

#### 示例 1: 基础计算

```python
# examples/basic_calculation.py
from formal_science import Calculator

# 创建计算器实例
calc = Calculator()

# 执行计算
result = calc.compute("2 + 2 * 3")
print(f"计算结果: {result}")  # 输出: 8
```

**运行命令:**
```bash
python examples/basic_calculation.py
```

#### 示例 2: 逻辑推理

```python
# examples/logic_reasoning.py
from formal_science import LogicEngine

# 初始化逻辑引擎
engine = LogicEngine()

# 定义前提
premises = [
    "所有人都是会死的",
    "苏格拉底是人"
]

# 推理结论
conclusion = engine.reason(premises, "苏格拉底")
print(f"结论: {conclusion}")  # 输出: 苏格拉底是会死的
```

**运行命令:**
```bash
python examples/logic_reasoning.py
```

#### 示例 3: 形式验证

```python
# examples/formal_verification.py
from formal_science import Verifier

# 创建验证器
verifier = Verifier()

# 验证定理
theorem = "∀x (P(x) → Q(x)) ∧ P(a) → Q(a)"
is_valid = verifier.verify(theorem)

print(f"定理有效: {is_valid}")  # 输出: True
```

### 常见问题

| 问题 | 原因 | 解决方案 |
|------|------|----------|
| `ModuleNotFoundError` | 未安装依赖 | 运行 `pip install -r requirements.txt` |
| `ImportError` | 路径问题 | 确保在项目根目录运行 |
| 运行时错误 | 数据格式错误 | 检查输入数据格式 |

---

## 🛠️ 如何使用工具

### 工具清单

#### 1. 交互式计算器

```bash
# 启动交互式计算器
python tools/interactive_calc.py

# 示例会话
>>> 2 + 3
5
>>> sin(pi/2)
1.0
>>> solve(x^2 - 4 = 0)
x = 2 或 x = -2
```

#### 2. 文档生成器

```bash
# 生成 HTML 文档
python tools/doc_generator.py --format html --output docs/build/

# 生成 PDF 文档
python tools/doc_generator.py --format pdf --output docs/build/
```

#### 3. 代码检查工具

```bash
# 检查代码风格
python tools/lint_checker.py src/

# 运行测试
python tools/test_runner.py
```

### 高级用法

#### 批处理模式

```python
# 批量处理文件
from formal_science.tools import BatchProcessor

processor = BatchProcessor(
    input_dir="data/input/",
    output_dir="data/output/",
    operation="verify"
)
processor.run()
```

#### 自定义配置

```json
{
  "calculation": {
    "precision": 10,
    "timeout": 30
  },
  "logging": {
    "level": "INFO",
    "file": "logs/app.log"
  }
}
```

---

## 📸 截图占位符

### 界面截图

#### 1. 主界面
![主界面截图](screenshots/main_interface.png)
*图 1: 项目主界面，显示导航菜单和快捷入口*

#### 2. 代码编辑器
![代码编辑器截图](screenshots/code_editor.png)
*图 2: 集成代码编辑器，支持语法高亮和自动补全*

#### 3. 结果展示
![结果展示截图](screenshots/results_display.png)
*图 3: 计算结果展示界面，包含可视化图表*

#### 4. 文档浏览器
![文档浏览器截图](screenshots/doc_browser.png)
*图 4: 文档浏览器，支持全文搜索*

#### 5. 设置面板
![设置面板截图](screenshots/settings_panel.png)
*图 5: 设置面板，可自定义各种选项*

### 需要补充的截图

- [ ] 安装过程截图
- [ ] 第一个程序运行截图
- [ ] 调试界面截图
- [ ] 错误处理截图
- [ ] 性能分析截图

---

## 💡 最佳实践

### DO ✅

- 始终使用虚拟环境
- 阅读文档后再运行代码
- 从简单示例开始
- 记录学习笔记
- 参与社区讨论

### DON'T ❌

- 跳过环境配置直接运行
- 在不理解的情况下复制代码
- 忽略错误信息
- 忘记备份重要数据

---

## 📚 相关资源

- [工作流演示](workflow_demo.md) - 完整的学习路径
- [API 文档](../Reference/api_reference.md) - 详细 API 说明
- [FAQ](../FAQ.md) - 常见问题解答
- [贡献指南](../Contributing.md) - 如何参与项目
