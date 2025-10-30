# 快速参考 (Quick Reference)

> **一页纸速查手册**：核心概念、公式、命令

---

## 📋 目录

- [快速参考 (Quick Reference)](#快速参考-quick-reference)
  - [📋 目录](#-目录)
  - [🎯 核心思想](#-核心思想)
    - [UH-Cost 元模型](#uh-cost-元模型)
    - [三元视角](#三元视角)
  - [📐 形式语义速查](#-形式语义速查)
    - [操作语义判断](#操作语义判断)
    - [类型系统](#类型系统)
    - [Hoare 逻辑](#hoare-逻辑)
  - [🎨 设计模式速查](#-设计模式速查)
    - [GoF 分类](#gof-分类)
    - [形式化方法](#形式化方法)
    - [验证命令](#验证命令)
  - [📊 复杂度速查](#-复杂度速查)
    - [20 维复杂度](#20-维复杂度)
    - [权衡定理](#权衡定理)
    - [Master 定理](#master-定理)
  - [🔧 工具命令速查](#-工具命令速查)
    - [安装](#安装)
    - [常用命令](#常用命令)
      - [Coq](#coq)
      - [K-Framework](#k-framework)
      - [mCRL2](#mcrl2)
      - [Lean4](#lean4)
      - [TLA+](#tla)
  - [📚 常用公式](#-常用公式)
    - [信息论](#信息论)
    - [通讯复杂度](#通讯复杂度)
    - [差分隐私](#差分隐私)
    - [Work-Span 模型](#work-span-模型)
  - [🔗 快速导航](#-快速导航)
    - [学习路径](#学习路径)
    - [主要文档](#主要文档)
    - [核心章节](#核心章节)
  - [🎓 课程对标](#-课程对标)
  - [📖 参考资源](#-参考资源)
    - [在线资源](#在线资源)
    - [经典教材](#经典教材)
  - [💡 速记口诀](#-速记口诀)
    - [操作语义](#操作语义)
    - [设计模式](#设计模式)
    - [复杂度](#复杂度)
    - [形式验证](#形式验证)

---

## 🎯 核心思想

### UH-Cost 元模型

```text
UH-Cost = ⟨Σ, ⟶, κ, Φ⟩

Σ  : 超图签名
⟶  : 重写规则 (L ⟹ R)
κ  : 成本函数 (ℕ^d)
Φ  : 正确性谓词
```

### 三元视角

```text
系统 = ⟨Control, Execution, Data⟩

Control  : 调度、同步 → Span, Coordination
Execution: 计算、指令 → Time, Energy
Data     : 移动、一致性 → Communication, I/O
```

---

## 📐 形式语义速查

### 操作语义判断

```text
小步语义: ⟨e, σ⟩ → ⟨e', σ'⟩
大步语义: e ⇓ v
成本语义: ⟨e, σ, κ⟩ → ⟨e', σ', κ+δ⟩
```

### 类型系统

```text
简单类型: Γ ⊢ e : τ
依赖类型: Γ ⊢ e : Π(x:A).B(x)
线性类型: Γ ⊢ e : A ⊸ B
```

### Hoare 逻辑

```text
{P} c {Q}                  (部分正确性)
[P] c [Q]                  (全正确性)
{P ∧ κ=K} c {Q ∧ κ≤K+Δ}   (定量)
```

---

## 🎨 设计模式速查

### GoF 分类

| 类别 | 数量 | 示例 |
|------|------|------|
| 创建型 | 5 | Abstract Factory, Singleton, Builder |
| 结构型 | 7 | Composite, Decorator, Proxy |
| 行为型 | 11 | Observer, Strategy, Command |

### 形式化方法

| 模式 | 工具 | 形式化 |
|------|------|--------|
| Abstract Factory | Coq | `Record { create : Product -> object }` |
| Observer | mCRL2 | `Subject \| Observer₁ \| ... \| ObserverN` |
| Composite | Coq | `Inductive Composite = Leaf \| Node [Composite]` |

### 验证命令

```bash
# Coq
coqc factory.v

# mCRL2
mcrl22lps observer.mcrl2 observer.lps
lps2lts observer.lps observer.lts

# K-Framework
kompile builder.k
krun -cPGM="new.setA(1).build()"
```

---

## 📊 复杂度速查

### 20 维复杂度

| # | 维度 | 模型 | 典型下界 |
|---|------|------|---------|
| 1 | Time | RAM | 排序 Ω(n log n) |
| 2 | Space | Config graph | SAT ∈ PSPACE |
| 3 | Communication | 2-party | DISJ Ω(n) |
| 4 | Energy | Bit-flip | 乘法 Ω(n²) |
| 5 | Depth | Circuit | 比较网络 Ω(log n) |
| 6 | Work | Parallel | 归并 O(n log n) |
| 7 | Span | Parallel | 归并 O(log³ n) |
| 8 | Cache | Ideal-Cache | 矩阵乘 Ω(n³/√Z) |
| 9 | I/O | Aggarwal-Vitter | 排序 Ω(n/B log_{M/B} n/B) |
| 10 | Privacy | ε-DP | 计数 ε ≥ 1/√n |

### 权衡定理

```text
时间-空间权衡:
  T · S = Ω(n²)  (重复检测)

矩阵乘跨维度:
  T · S² · C ≥ n⁶ / (energy · cache)

能量-时间-精度:
  E · T · ε ≥ Ω(n)
```

### Master 定理

```text
T(n) = aT(n/b) + f(n)

情况 1: f(n) = O(n^c), c < log_b a
  → T(n) = Θ(n^{log_b a})

情况 2: f(n) = Θ(n^c log^k n), c = log_b a
  → T(n) = Θ(n^c log^{k+1} n)

情况 3: f(n) = Ω(n^c), c > log_b a
  → T(n) = Θ(f(n))
```

---

## 🔧 工具命令速查

### 安装

```bash
# 基础环境
brew install opam mcrl2 tlaplus-tools maude
opam init -y && opam install coq fstar

# K-Framework
brew install kframework

# Lean4
curl -L https://raw.githubusercontent.com/leanprover/lean4/master/scripts/install-linux.sh | sh

# 容器工具
docker pull uppaal/uppaal:4.1.40
docker pull cpntools/cpntools

# Python 工具
pip install z3-solver klee
```

### 常用命令

#### Coq

```bash
# 编译
coqc file.v

# 交互式
coqide file.v

# 提取代码
Extraction "output.ml" function_name.
```

#### K-Framework

```bash
# 编译定义
kompile semantics.k

# 运行程序
krun -cPGM="program" --output pretty

# 符号执行
krun -cPGM="program" --search

# 模型检测
krun -cPGM="program" --prove spec.k
```

#### mCRL2

```bash
# 生成 LPS
mcrl22lps model.mcrl2 model.lps

# 生成状态空间
lps2lts model.lps model.lts

# 状态空间信息
ltsinfo model.lts

# CTL 验证
lps2pbes -f formula.mcf model.lps model.pbes
pbes2bool model.pbes
```

#### Lean4

```bash
# 构建项目
lake build

# 检查文件
lean --make file.lean

# 交互式
lake env lean --server
```

#### TLA+

```bash
# 模型检查
tlc -config model.cfg spec.tla

# 验证 TLAPS
tlapm spec.tla
```

---

## 📚 常用公式

### 信息论

```text
H(X) = -Σ p(x) log p(x)                (熵)
I(X;Y) = H(X) - H(X|Y)                  (互信息)
K(x) = min{|p| : U(p) = x}              (Kolmogorov 复杂度)
```

### 通讯复杂度

```text
D(f) = min_{π} max_{x,y} CC(π,x,y)      (确定性)
R(f) = min_{π} max_{x,y} E[CC(π,x,y)]   (随机)

下界技术:
  D(f) ≥ log rank(M_f)                  (秩下界)
  D(f) ≥ log det(M_f)                   (行列式下界)
```

### 差分隐私

```text
Pr[A(D) ∈ S] ≤ e^ε · Pr[A(D') ∈ S] + δ

组合定理:
  A₁ ∘ A₂ 是 (ε₁+ε₂, δ₁+δ₂)-DP
```

### Work-Span 模型

```text
T_P ≥ max{Work/P, Span}                 (Brent 定理)

并行加速比:
  S_P = T_1 / T_P

并行效率:
  E_P = S_P / P
```

---

## 🔗 快速导航

### 学习路径

```text
初学者:
  README.md
  → 01.1_Operational_Semantics.md
  → 02.1_GoF_Formal_Analysis.md
  → GLOSSARY.md

进阶者:
  03.1_Multidimensional_Complexity.md
  → 03.3_Lower_Bound_Techniques.md
  → 05.1_Coq_Introduction.md

研究者:
  04.5_Cross_Layer_Verification.md
  → 相关论文
  → 贡献代码
```

### 主要文档

- [00_Master_Index.md](00_Master_Index.md) - 主索引
- [README.md](README.md) - 总体概述
- [GLOSSARY.md](GLOSSARY.md) - 术语表
- [COMPLETION_SUMMARY.md](COMPLETION_SUMMARY.md) - 完成情况

### 核心章节

- [01_Formal_Semantics/](01_Formal_Semantics/) - 形式语义
- [02_Design_Patterns/](02_Design_Patterns/) - 设计模式
- [03_Algorithm_Complexity/](03_Algorithm_Complexity/) - 算法复杂度
- [04_Architecture_Patterns/](04_Architecture_Patterns/) - 架构模式
- [05_Formal_Verification/](05_Formal_Verification/) - 形式验证

---

## 🎓 课程对标

| 大学 | 课程 | 对应章节 |
|------|------|---------|
| MIT 6.820 | Program Analysis | 01, 05 |
| CMU 15-312 | Programming Languages | 01 |
| Stanford CS 242 | Programming Languages | 01 |
| UC Berkeley CS 170 | Algorithms | 03 |
| CMU 17-313 | Software Engineering | 02, 04 |
| EPFL CS-550 | Formal Verification | 05 |

---

## 📖 参考资源

### 在线资源

- [K-Framework](https://kframework.org/)
- [Coq](https://coq.inria.fr/)
- [Lean4](https://leanprover.github.io/)
- [mCRL2](https://mcrl2.org/)
- [Software Foundations](https://softwarefoundations.cis.upenn.edu/)

### 经典教材

- **CLRS**: Introduction to Algorithms
- **TAPL**: Types and Programming Languages
- **GoF**: Design Patterns
- **Winskel**: The Formal Semantics of Programming Languages

---

## 💡 速记口诀

### 操作语义

```text
小步慢慢走，大步一跳到
成本带着算，资源全追踪
```

### 设计模式

```text
创建抽象工厂，结构组合装饰
行为观察策略，命令责任链
```

### 复杂度

```text
时间空间通讯，能量缓存 I/O
隐私样本随机，二十维度全
```

### 形式验证

```text
Coq 证定理，mCRL2 查死锁
K 定义语义，Lean 写数学
```

---

**最后更新**: 2025-10-29
**版本**: 1.0.0
**作者**: FormalScience Team
