# 贡献指南

感谢你考虑为 FormalScience 项目做出贡献！本指南将帮助你了解如何参与项目开发。

---

## 📋 目录

1. [如何贡献](#如何贡献)
2. [编写规范](#编写规范)
3. [审核流程](#审核流程)
4. [开发环境](#开发环境)
5. [提交规范](#提交规范)

---

## 如何贡献

### 贡献方式

我们欢迎以下形式的贡献：

- 📝 **内容修正** - 修复错别字、语法错误或事实错误
- 📚 **内容扩充** - 添加新的知识点、示例或解释
- 💻 **代码示例** - 提供 Rust/Haskell/Lean 代码示例
- 🐛 **问题报告** - 报告内容错误或不清晰之处
- 💡 **功能建议** - 提出改进建议或新主题建议
- 🌐 **翻译** - 协助内容翻译和本地化

### 贡献步骤

#### 1. 准备工作

```bash
# Fork 项目仓库
git clone https://github.com/your-username/FormalScience.git
cd FormalScience/docs/Refactor

# 创建新分支
git checkout -b feature/your-feature-name
```

#### 2. 进行修改

- 根据下面的编写规范编辑内容
- 确保所有链接和引用正确
- 本地预览检查格式

#### 3. 提交更改

```bash
# 添加更改
git add .

# 提交（遵循提交规范）
git commit -m "docs: 添加XXX内容"

# 推送到你的仓库
git push origin feature/your-feature-name
```

#### 4. 创建 Pull Request

- 在项目主页点击 "New Pull Request"
- 填写 PR 描述，说明更改内容
- 关联相关 Issue（如有）

---

## 编写规范

### 文件组织

```
docs/Refactor/
├── XX_模块名/           # 模块目录
│   ├── XX_主题/        # 子主题目录
│   │   └── XX.X_文件名.md
│   └── _index.md       # 模块索引
├── cases/              # 案例分析
├── examples/           # 代码示例
│   ├── rust/
│   ├── haskell/
│   └── lean/
├── exercises/          # 练习题
├── tools/              # 工具文档
└── visual/             # 可视化文档
```

### Markdown 规范

#### 标题层级

```markdown
# 一级标题 - 文章主标题（仅一个）

## 二级标题 - 主要章节

### 三级标题 - 子章节

#### 四级标题 - 小节
```

#### 数学公式

- 行内公式使用 `$...$`
- 块级公式使用 `$$...$$`
- 公式必须可渲染（支持 KaTeX）

```markdown
行内公式: $E = mc^2$

块级公式:
$$\sum_{i=1}^{n} x_i = x_1 + x_2 + \cdots + x_n$$
```

#### 代码块

- 必须指定语言
- Rust 代码需要可通过编译（除非专门展示错误）

```markdown
```rust
fn main() {
    println!("Hello, FormalScience!");
}
```
```

#### 链接规范

- 内部链接使用相对路径
- 外部链接必须包含协议

```markdown
[内部链接](./01_数学基础/_index.md)
[外部链接](https://example.com)
```

### 内容风格

#### 语言风格

- 使用简体中文（zh-CN）
- 专业术语首次出现标注英文
- 避免口语化表达

#### 示例

```markdown
**类型系统(Type System)** 是编程语言中用于定义程序结构的一套规则。
类型系统可以在编译时检测错误，提高代码的可靠性。
```

#### 内容结构

每篇文档应包含：

1. **标题** - 清晰描述主题
2. **简介** - 2-3 段概述
3. **正文** - 分章节详细说明
4. **示例** - 代码或数学示例
5. **总结** - 要点回顾
6. **参考** - 相关链接和文献

### 代码规范

#### Rust 代码

```rust
// 使用 cargo fmt 格式化
// 包含完整可运行示例

/// 文档注释说明功能
/// 
/// # 示例
/// ```
/// let result = add(2, 3);
/// assert_eq!(result, 5);
/// ```
pub fn add(a: i32, b: i32) -> i32 {
    a + b
}

fn main() {
    // 主函数示例
    let sum = add(10, 20);
    println!("Sum: {}", sum);
}
```

#### Haskell 代码

```haskell
-- 模块声明
module Example where

-- 类型签名
add :: Num a => a -> a -> a
add a b = a + b

-- 主函数
main :: IO ()
main = do
    let result = add 10 20
    putStrLn $ "Result: " ++ show result
```

#### Lean 代码

```lean
-- 定理证明示例
lemma add_commutative (a b : ℕ) : a + b = b + a :=
by
  induction a with
  | zero => simp
  | succ n ih => simp [ih]
```

---

## 审核流程

### 审核阶段

```
提交 PR
    ↓
自动检查（CI）
    ↓
内容审核 → 可能需要修改
    ↓
技术审核 → 可能需要修改
    ↓
合并到主分支
```

### 审核标准

#### 内容审核

- [ ] 内容准确性 - 事实和概念正确
- [ ] 完整性 - 覆盖必要的知识点
- [ ] 清晰度 - 易于理解
- [ ] 一致性 - 与现有内容风格一致

#### 技术审核

- [ ] 代码可运行 - 所有代码示例可编译/运行
- [ ] 链接有效 - 所有内部和外部链接有效
- [ ] 格式正确 - Markdown 格式规范
- [ ] 数学正确 - 公式和证明正确

### 审核时间

- 简单修改：1-3 天
- 内容添加：3-7 天
- 重大变更：7-14 天

---

## 开发环境

### 推荐工具

| 用途 | 工具 |
|------|------|
| 编辑器 | VS Code + Markdown 插件 |
| Markdown 检查 | markdownlint |
| 拼写检查 | Code Spell Checker |
| 数学预览 | Markdown Math |
| Git 客户端 | GitHub Desktop / Fork |

### VS Code 配置

`.vscode/settings.json`:

```json
{
  "editor.wordWrap": "on",
  "editor.rulers": [80, 120],
  "markdownlint.config": {
    "MD013": { "line_length": 120 },
    "MD024": { "siblings_only": true }
  }
}
```

### 本地预览

```bash
# 安装 markdown 服务器
npm install -g markdown-preview

# 启动预览
markdown-preview docs/Refactor
```

---

## 提交规范

### Commit Message 格式

```
<type>(<scope>): <subject>

<body>

<footer>
```

#### Type 类型

| 类型 | 说明 |
|------|------|
| `docs` | 文档内容修改 |
| `fix` | 错误修正 |
| `feat` | 新功能/新内容 |
| `refactor` | 重构（不改变内容含义）|
| `style` | 格式调整 |
| `chore` | 构建/工具变更 |

#### Scope 范围

- `math` - 数学基础
- `formal` - 形式语言
- `pl` - 编程范式
- `se` - 软件工程
- `theory` - 形式化理论
- `scheduler` - 调度系统
- `cross` - 交叉视角
- `case` - 案例
- `example` - 示例

#### 示例

```
docs(math): 添加群论同态内容

- 添加群同态定义
- 补充同态基本定理
- 添加示例和图示

Closes #123
```

### PR 标题规范

```
[<类型>] <简要描述>
```

示例：
- `[Docs] 完善调度系统负载均衡内容`
- `[Fix] 修正类型论章节错别字`
- `[Feat] 添加量子计算调度案例`

---

## 🙏 致谢

感谢所有贡献者的付出！你的贡献将帮助更多人学习形式科学。

如有任何问题，欢迎：
- 提交 [Issue](https://github.com/formalscience/knowledge-base/issues)
- 发送邮件至：contributors@formalscience.org

---

*最后更新: 2026-04-11*
