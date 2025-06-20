# 6. 拓扑基础 (Topology Foundations)

## 6.1 概述

拓扑学研究空间的连续性、连通性和形状的本质属性，是现代数学和形式科学的重要分支。

## 6.2 拓扑空间

### 6.2.1 拓扑空间定义

**定义 6.1** (拓扑空间)
设 $X$ 是集合，$\mathcal{T}$ 是 $X$ 的子集族，若满足：
1. $\emptyset, X \in \mathcal{T}$
2. 任意并、有限交封闭
则 $(X, \mathcal{T})$ 称为拓扑空间。

### 6.2.2 开集与闭集

**定义 6.2** (开集)
$U \in \mathcal{T}$ 称为开集。

**定义 6.3** (闭集)
$F \subseteq X$ 称为闭集，当且仅当 $X \setminus F$ 是开集。

### 6.2.3 基与子基

**定义 6.4** (基)
$\mathcal{B} \subseteq \mathcal{T}$，若任意 $U \in \mathcal{T}$，$\forall x \in U, \exists B \in \mathcal{B}, x \in B \subseteq U$，则 $\mathcal{B}$ 为基。

**定义 6.5** (子基)
$\mathcal{S}$ 是子基，若 $\mathcal{T}$ 是 $\mathcal{S}$ 的有限交和任意并生成。

## 6.3 连通性与紧致性

### 6.3.1 连通空间

**定义 6.6** (连通空间)
$(X, \mathcal{T})$ 不可分为两个非空开集的并，称为连通。

### 6.3.2 紧空间

**定义 6.7** (紧空间)
任意开覆盖有有限子覆盖。

**定理 6.1** (海涅-博雷尔定理)
$\mathbb{R}^n$ 中闭有界集是紧的。

## 6.4 连续映射与同胚

### 6.4.1 连续映射

**定义 6.8** (连续映射)
$f: X \to Y$ 连续，当且仅当 $\forall V \subseteq Y$ 开集，$f^{-1}(V)$ 是开集。

### 6.4.2 同胚

**定义 6.9** (同胚)
$f: X \to Y$ 是同胚，若 $f$ 双射且连续，$f^{-1}$ 也连续。

## 6.5 基本不变量

### 6.5.1 基本群

**定义 6.10** (基本群)
$\pi_1(X, x_0)$ 是以 $x_0$ 为基点的回路同伦类群。

### 6.5.2 同伦等价

**定义 6.11** (同伦等价)
$X, Y$ 存在连续映射 $f: X \to Y, g: Y \to X$，$g \circ f \simeq id_X, f \circ g \simeq id_Y$，则 $X, Y$ 同伦等价。

## 6.6 拓扑在计算机科学中的应用

### 6.6.1 数据分析与拓扑数据分析
- 持久同调
- 数据流形学习

### 6.6.2 网络科学
- 网络连通性
- 网络同构

### 6.6.3 形式化证明

```lean
-- Lean 中的拓扑空间
import topology.basic

-- 连续映射定义
def is_continuous {X Y : Type*} [topological_space X] [topological_space Y]
  (f : X → Y) := continuous f

-- 海涅-博雷尔定理
lemma heine_borel (S : set ℝ) :
  is_compact S ↔ is_closed S ∧ bounded S :=
begin
  -- 证明实现
  sorry
end
```

## 6.7 总结

拓扑为现代数学、数据科学、网络科学等领域提供了空间结构和不变量理论基础。

## 参考文献

1. Munkres, J. R. (2000). *Topology*. Prentice Hall.
2. Hatcher, A. (2002). *Algebraic topology*. Cambridge University Press.
3. Ghrist, R. (2014). *Elementary applied topology*. Createspace.
4. Edelsbrunner, H., & Harer, J. (2010). *Computational topology: An introduction*. American Mathematical Society.

---

**更新时间**: 2024-12-21  
**版本**: 1.0  
**作者**: FormalScience Team 