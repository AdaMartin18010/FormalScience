# Lean 4 形式化数学示例库

本目录包含使用 Lean 4 编写的形式化数学示例，展示如何将数学概念和算法严格地形式化。

## 文件说明

| 文件 | 内容 | 对应理论 |
|------|------|----------|
| `basic.lean` | 基础数学定义（自然数、整数、实数、代数结构） | 数论、代数基础 |
| `type_theory.lean` | 类型论构造（依赖类型、归纳类型、命题逻辑） | 类型论基础 |
| `category.lean` | 范畴论基本概念（范畴、函子、自然变换） | 范畴论 |
| `scheduler.lean` | 调度算法的形式化证明 | 调度理论 |

## 运行要求

- Lean 4 (版本 ≥ 4.5.0)
- Lake 构建工具

## 安装与运行

```bash
# 安装 Lean 4 (使用 elan)
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# 创建新项目
lake new my_math math
cd my_math

# 复制示例文件到项目
# 然后构建
lake build

# 交互式检查
lake env lean --server
```

## 验证单个文件

```bash
lean --run basic.lean
```

## 学习路径

1. **入门**: 从 `basic.lean` 开始，了解 Lean 的基本语法
2. **进阶**: 阅读 `type_theory.lean`，理解依赖类型系统
3. **应用**: 查看 `category.lean`，学习抽象数学的形式化
4. **实战**: 研究 `scheduler.lean`，了解算法证明技巧

## 相关资源

- [Lean 4 官方文档](https://leanprover.github.io/lean4/doc/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
