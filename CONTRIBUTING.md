# 贡献指南

感谢您对 FormalScience 项目的关注！本指南将帮助您了解如何为项目做出贡献。

## 📋 目录

- [行为准则](#行为准则)
- [如何贡献](#如何贡献)
- [开发环境设置](#开发环境设置)
- [文档规范](#文档规范)
- [代码规范](#代码规范)
- [提交指南](#提交指南)
- [审查流程](#审查流程)

## 行为准则

- 保持尊重和专业的态度
- 欢迎新手，耐心解答问题
- 专注于建设性的技术讨论
- 尊重不同的观点和背景

## 如何贡献

### 报告问题

如果您发现了问题或有改进建议：

1. 先搜索现有 Issue，避免重复提交
2. 使用 Issue 模板创建新 Issue
3. 提供清晰的标题和详细描述
4. 如有必要，附上复现步骤或示例

### 提交代码

1. Fork 本仓库
2. 创建功能分支 (`git checkout -b feature/amazing-feature`)
3. 提交更改 (`git commit -m 'Add amazing feature'`)
4. 推送到分支 (`git push origin feature/amazing-feature`)
5. 创建 Pull Request

### 改进文档

文档改进同样重要！您可以：

- 修正拼写和语法错误
- 改进表述清晰度
- 添加示例和解释
- 更新过时的内容
- 翻译文档

## 开发环境设置

### 基础工具

```bash
# 克隆仓库
git clone https://github.com/username/FormalScience.git
cd FormalScience

# 配置 Git
git config user.name "Your Name"
git config user.email "your.email@example.com"
```

### 可选依赖

根据您的贡献类型，可能需要安装：

```bash
# Python 工具
pip install -r requirements.txt

# Rust 工具链
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh

# Lean 4
# 请参考 https://leanprover.github.io/lean4/doc/setup.html
```

## 文档规范

### Markdown 格式

- 使用 UTF-8 编码
- 使用 LF 换行符
- 行长度建议不超过 100 字符
- 使用 `-` 作为无序列表标记
- 代码块需指定语言

### 数学内容

- 行内公式使用 `$...$`
- 独立公式使用 `$$...$$`
- 复杂公式使用编号环境

```markdown
行内公式: $E = mc^2$

独立公式:
$$\int_{-\infty}^{\infty} e^{-x^2} dx = \sqrt{\pi}$$
```

### 文档结构

```markdown
# 标题

## 概述

简要介绍主题。

## 正文

详细内容...

## 参考

- 链接1
- 链接2
```

## 代码规范

### Python

- 遵循 PEP 8
- 使用 4 空格缩进
- 添加类型注解
- 编写文档字符串

```python
def calculate(x: float, y: float) -> float:
    """
    计算两个数的和。
    
    Args:
        x: 第一个数
        y: 第二个数
        
    Returns:
        两数之和
    """
    return x + y
```

### Rust

- 使用 `rustfmt` 格式化
- 使用 `clippy` 检查
- 添加文档注释

```rust
/// 计算斐波那契数列的第 n 项
/// 
/// # Examples
/// 
/// ```
/// assert_eq!(fib(10), 55);
/// ```
pub fn fib(n: u32) -> u32 {
    match n {
        0 => 0,
        1 => 1,
        _ => fib(n - 1) + fib(n - 2),
    }
}
```

### Lean

- 使用有意义的定理名称
- 添加注释解释证明思路
- 保持证明简洁

```lean
-- 自然数的加法交换律
theorem add_comm (a b : Nat) : a + b = b + a := by
  induction a with
  | zero => simp
  | succ n ih => simp [ih]
```

## 提交指南

### Commit Message 格式

```
<type>: <subject>

<body>

<footer>
```

#### Type

- `feat`: 新功能
- `fix`: 修复
- `docs`: 文档
- `style`: 格式（不影响代码运行的变动）
- `refactor`: 重构
- `test`: 测试
- `chore`: 构建过程或辅助工具的变动

#### Subject

- 不超过 50 个字符
- 使用祈使语气（"Add" 而非 "Added"）
- 首字母大写
- 末尾不加句号

#### Body

- 可选，用于详细说明
- 每行不超过 72 字符
- 解释为什么做这些更改

#### 示例

```
docs: 添加集合论基础文档

- 包含基本概念定义
- 添加常用定理证明
- 补充参考资料链接

Fixes #123
```

### 分支命名

- `feature/description` - 新功能
- `fix/description` - Bug 修复
- `docs/description` - 文档更新
- `refactor/description` - 重构

## 审查流程

1. 所有提交都需要通过自动化检查
2. 至少需要一位维护者审查
3. 审查者可能会要求修改
4. 通过审查后将被合并

### 审查检查清单

- [ ] 代码符合项目规范
- [ ] 文档已同步更新
- [ ] 无敏感信息泄露
- [ ] 无大文件提交
- [ ] 提交信息清晰

## 获取帮助

- 查看 [README.md](README.md)
- 在 Issue 中提问
- 参与讨论

## 致谢

再次感谢您的贡献！每一份努力都让形式科学知识体系更加完善。
