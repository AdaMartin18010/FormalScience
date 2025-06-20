# 06. 拓扑学基础 (Topology)

## 目录

1. [点集拓扑](#1-点集拓扑)
2. [代数拓扑](#2-代数拓扑)
3. [微分拓扑](#3-微分拓扑)
4. [同伦论](#4-同伦论)
5. [纤维丛理论](#5-纤维丛理论)
6. [拓扑不变量](#6-拓扑不变量)
7. [拓扑公理化](#7-拓扑公理化)
8. [拓扑证明与自动化](#8-拓扑证明与自动化)
9. [应用与算法](#9-应用与算法)

## 1. 点集拓扑

### 1.1 拓扑空间

**定义 1.1.1** (拓扑空间)
拓扑空间是二元组 $(X, \mathcal{T})$，其中 $X$ 是集合，$\mathcal{T}$ 是 $X$ 的子集族，满足：
1. $\emptyset, X \in \mathcal{T}$
2. 任意并封闭：$\{U_i\}_{i \in I} \subseteq \mathcal{T} \implies \bigcup_{i \in I} U_i \in \mathcal{T}$
3. 有限交封闭：$U_1, U_2 \in \mathcal{T} \implies U_1 \cap U_2 \in \mathcal{T}$

**定义 1.1.2** (开集与闭集)
- 开集：$\mathcal{T}$ 中的元素
- 闭集：开集的补集

### 1.2 连续映射

**定义 1.2.1** (连续映射)
$f: X \to Y$ 连续当且仅当对任意开集 $V \subseteq Y$，$f^{-1}(V)$ 是开集。

**定理 1.2.1** (连续映射的等价条件)
$f$ 连续当且仅当对任意闭集 $F \subseteq Y$，$f^{-1}(F)$ 是闭集。

### 1.3 紧致性与连通性

**定义 1.3.1** (紧致空间)
拓扑空间 $X$ 紧致当且仅当每个开覆盖都有有限子覆盖。

**定义 1.3.2** (连通空间)
拓扑空间 $X$ 连通当且仅当 $X$ 不能表示为两个非空开集的不交并。

**定理 1.3.1** (海涅-博雷尔定理)
$\mathbb{R}^n$ 的子集紧致当且仅当它是有界闭集。

### 1.4 分离公理

**定义 1.4.1** (Hausdorff空间)
拓扑空间 $X$ 是 Hausdorff 的，当且仅当对任意不同点 $x, y$，存在不相交的开集 $U, V$ 使得 $x \in U, y \in V$。

**定义 1.4.2** (正规空间)
拓扑空间 $X$ 正规当且仅当对任意不相交的闭集 $A, B$，存在不相交的开集 $U, V$ 使得 $A \subseteq U, B \subseteq V$。

## 2. 代数拓扑

### 2.1 基本群

**定义 2.1.1** (道路)
道路是连续映射 $\alpha: [0,1] \to X$。

**定义 2.1.2** (道路同伦)
道路 $\alpha, \beta$ 同伦当且仅当存在连续映射 $H: [0,1] \times [0,1] \to X$ 使得 $H(t,0) = \alpha(t), H(t,1) = \beta(t)$。

**定义 2.1.3** (基本群)
$\pi_1(X,x_0)$ 是以 $x_0$ 为基点的道路同伦类的群。

**定理 2.1.1** (基本群的性质)
1. $\pi_1(S^1) \cong \mathbb{Z}$
2. $\pi_1(S^n) = 0$ 对 $n > 1$

### 2.2 同调群

**定义 2.2.1** (奇异同调)
$H_n(X)$ 是 $X$ 的第 $n$ 个奇异同调群。

**定理 2.2.1** (同调群的性质)
1. $H_0(X) \cong \mathbb{Z}^k$，其中 $k$ 是连通分支数
2. $H_n(S^n) \cong \mathbb{Z}$
3. $H_n(S^m) = 0$ 对 $n \neq 0, m$

## 3. 微分拓扑

### 3.1 流形

**定义 3.1.1** (拓扑流形)
$n$ 维拓扑流形是局部同胚于 $\mathbb{R}^n$ 的 Hausdorff 空间。

**定义 3.1.2** (微分流形)
微分流形是带有微分结构的拓扑流形。

**定理 3.1.1** (Whitney嵌入定理)
每个 $n$ 维微分流形可嵌入到 $\mathbb{R}^{2n}$ 中。

### 3.2 切丛与余切丛

**定义 3.2.1** (切空间)
$T_pM$ 是流形 $M$ 在点 $p$ 处的切空间。

**定义 3.2.2** (切丛)
$TM = \bigcup_{p \in M} T_pM$ 是 $M$ 的切丛。

## 4. 同伦论

### 4.1 同伦等价

**定义 4.1.1** (同伦等价)
空间 $X, Y$ 同伦等价当且仅当存在连续映射 $f: X \to Y, g: Y \to X$ 使得 $g \circ f \simeq \text{id}_X, f \circ g \simeq \text{id}_Y$。

**定理 4.1.1** (同伦不变性)
同伦等价的空间具有相同的同伦群。

### 4.2 纤维化

**定义 4.2.1** (纤维化)
映射 $p: E \to B$ 是纤维化当且仅当具有同伦提升性质。

**定理 4.2.1** (长正合序列)
纤维化 $F \to E \to B$ 诱导长正合序列：
$$\cdots \to \pi_n(F) \to \pi_n(E) \to \pi_n(B) \to \pi_{n-1}(F) \to \cdots$$

## 5. 纤维丛理论

### 5.1 主丛

**定义 5.1.1** (主丛)
主 $G$-丛是带有群 $G$ 自由作用的纤维丛。

**定理 5.1.1** (分类定理)
主 $G$-丛的分类由 $BG$ 的同伦类给出。

### 5.2 向量丛

**定义 5.2.1** (向量丛)
向量丛是纤维为向量空间的纤维丛。

**定理 5.2.1** (Whitney和)
向量丛的 Whitney 和保持同伦类。

## 6. 拓扑不变量

### 6.1 欧拉示性数

**定义 6.1.1** (欧拉示性数)
$\chi(X) = \sum_{n=0}^{\infty} (-1)^n \text{rank}(H_n(X))$

**定理 6.1.1** (欧拉示性数的性质)
1. $\chi(S^n) = 1 + (-1)^n$
2. $\chi(X \times Y) = \chi(X) \cdot \chi(Y)$

### 6.2 陈类

**定义 6.2.1** (陈类)
复向量丛的陈类是上同调类 $c_i(E) \in H^{2i}(X)$。

**定理 6.2.1** (陈类的性质)
1. $c_0(E) = 1$
2. $c_i(E \oplus F) = \sum_{j=0}^i c_j(E) \cup c_{i-j}(F)$

## 7. 拓扑公理化

### 7.1 公理系统

**定义 7.1.1** (拓扑公理)
开集族满足的三条公理。

**定理 7.1.1** (公理的独立性)
某些公理不能由其他公理推出。

## 8. 拓扑证明与自动化

### 8.1 形式化证明

```lean
-- Lean 4 证明示例：基本群的性质
-- 省略具体 Lean 代码实现
```

### 8.2 计算机辅助证明
- Coq/Lean/Isabelle 等证明助手

## 9. 应用与算法

### 9.1 计算拓扑
- 持久同调、Morse理论

### 9.2 数据科学
- 拓扑数据分析、流形学习

### 9.3 物理应用
- 规范理论、弦理论

## 参考文献

1. Munkres, J. R. (2000). *Topology*. Prentice Hall.
2. Hatcher, A. (2002). *Algebraic Topology*. Cambridge University Press.
3. Milnor, J. W. (1997). *Topology from the Differentiable Viewpoint*. Princeton University Press.
4. Spanier, E. H. (1994). *Algebraic Topology*. Springer.
5. Bott, R., & Tu, L. W. (1982). *Differential Forms in Algebraic Topology*. Springer.

## 交叉引用

- [01_Philosophical_Foundations/01_Epistemological_Foundations.md](../01_Philosophical_Foundations/01_Epistemological_Foundations.md) - 数学知识的认识论基础
- [02_Mathematical_Foundations/01_Set_Theory.md](01_Set_Theory.md) - 集合论基础
- [02_Mathematical_Foundations/03_Algebra.md](03_Algebra.md) - 代数基础
- [02_Mathematical_Foundations/05_Analysis.md](05_Analysis.md) - 数学分析基础
- [03_Logic_Theory/01_Propositional_Logic.md](../03_Logic_Theory/01_Propositional_Logic.md) - 逻辑推理基础
- [05_Type_Theory/01_Type_Theory_Foundations.md](../05_Type_Theory/01_Type_Theory_Foundations.md) - 类型理论基础
