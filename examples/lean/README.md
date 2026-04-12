# FormalScience 项目 Lean 4 代码示例

本目录包含 FormalScience 项目中关键数学定理和形式化定义的 Lean 4 代码示例。

## 文件结构

### 数学基础部分

| 文件名 | 内容 | 对应文档 |
|--------|------|----------|
| `01_SetTheory.lean` | 集合论基本运算（并、交、补、幂集）、外延公理、Cantor定理 | FormalRE/01_形式系统详解/01.5_集合论ZF-ZFC.md |
| `02_Logic.lean` | 数理逻辑（命题逻辑连接词、谓词逻辑、量词、经典逻辑原理） | 形式系统详解/01.5_集合论ZF-ZFC.md |
| `03_GroupTheory.lean` | 群论基本定义（群、子群、同态）、基本定理 | FormalRE/01_形式系统详解/01.6_范畴论基础.md |
| `04_LinearAlgebra.lean` | 线性代数（向量空间、线性映射、矩阵表示） | FormalRE/01_形式系统详解/01.6_范畴论基础.md |
| `11_Relations.lean` | 关系理论（等价关系、偏序、良基关系、闭包） | - |
| `12_NatArithmetic.lean` | 自然数算术（Peano公理、加法乘法、归纳法） | - |

### 形式语言部分

| 文件名 | 内容 | 对应文档 |
|--------|------|----------|
| `05_TypeTheory.lean` | 类型论（简单类型、依赖类型、Π/Σ类型、Curry-Howard对应、归纳类型） | FormalRE/01_形式系统详解/01.7_类型论与依赖类型.md |
| `06_LambdaCalculus.lean` | λ演算（语法、α转换、β归约、Church编码、Y组合子、Church-Rosser定理） | FormalRE/01_形式系统详解/01.3_Lambda演算.md |
| `07_CategoryTheory.lean` | 范畴论（范畴、函子、自然变换、极限、CCC） | FormalRE/01_形式系统详解/01.6_范畴论基础.md |

### 调度系统部分

| 文件名 | 内容 | 对应文档 |
|--------|------|----------|
| `08_Scheduling.lean` | 调度问题形式化（任务定义、调度方案、等价性、优化目标、SPT/EDD算法） | 调度系统相关文档 |

### 形式化理论部分

| 文件名 | 内容 | 对应文档 |
|--------|------|----------|
| `09_PetriNets.lean` | Petri网（定义、使能触发、可达性、有界性、活性、VAS） | FormalRE/01_形式系统详解/01.2_Petri网理论.md |
| `10_TemporalLogic.lean` | 时序逻辑（Kripke结构、LTL、CTL、模型检验框架） | 形式化理论相关文档 |

## 统计

- **总文件数**: 12 个
- **总代码行数**: 约 3000+ 行
- **覆盖主题**:
  - ✅ 集合论基本运算（并、交、补、幂集）
  - ✅ 数理逻辑（命题逻辑、谓词逻辑）
  - ✅ 群论基本定义（群、子群、同态）
  - ✅ 线性代数（向量空间、线性映射）
  - ✅ 类型论（简单类型、依赖类型、Π/Σ类型）
  - ✅ λ演算（语法、归约、类型、Church编码）
  - ✅ 范畴论基础（范畴、函子、自然变换）
  - ✅ 调度问题形式化定义
  - ✅ 调度算法正确性证明框架
  - ✅ 调度等价性证明
  - ✅ 时序逻辑（LTL/CTL）
  - ✅ Petri网性质证明

## 使用方法

### 安装 Lean 4

1. 安装 Lean 4 工具链：
```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

2. 创建新项目：
```bash
lake new my_project
```

3. 添加 Mathlib 依赖（在 `lakefile.lean` 中）。

### 编译代码

```bash
lake build
```

### 交互式开发

使用 VS Code 安装 Lean 4 扩展，打开 `.lean` 文件进行交互式证明。

## 代码特点

1. **完整的定理陈述**：每个文件包含完整的形式化定义和定理陈述
2. **详细的注释**：代码中包含大量解释性注释
3. **对应文档**：每个文件都与项目中的 Markdown 文档对应
4. **可编译**：所有代码都经过语法检查，符合 Lean 4 规范
5. **层次清晰**：从基础到高级，循序渐进

## 证明风格

本项目采用以下证明风格：

- **声明式证明**：使用 `theorem` 和 `def` 明确定义概念
- **结构化证明**：使用 `by` 块和结构化策略（如 `apply`, `intro`, `exact`）
- **数学严谨**：遵循数学定义和定理的标准形式化
- **可读性优先**：代码结构清晰，注释详细

## 扩展阅读

- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Functional Programming in Lean](https://leanprover.github.io/functional_programming_in_lean/)

## 许可证

本代码示例作为 FormalScience 项目的一部分，遵循项目整体许可证。
