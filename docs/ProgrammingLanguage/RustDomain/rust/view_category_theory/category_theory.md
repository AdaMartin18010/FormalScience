# 范畴论（Category Theory）理论基础与形式化推理

```text
<think>
我需要按照用户的要求重新组织内容，
将焦点放在范畴论（Category Theory）自身的核心内容和形式化推理上，
特别强调知识点、定理、推理、推论、证明和隐含意义。
我将保持原始结构，
但更加突出范畴论的理论基础、形式化定义和数学论证。

需要集中在以下方面：
1. 范畴论的基本定义和概念
2. 核心定理和形式化推理
3. 严格的数学证明
4. 概念间的逻辑关联
5. 范畴论结构的形式化描述
6. 定理的隐含意义和理论启示

我将使用更多的数学符号和形式化语言，减少应用示例的比重，而增加理论推导和证明的篇幅。
</think>
```

## 目录

- [范畴论（Category Theory）理论基础与形式化推理](#范畴论category-theory理论基础与形式化推理)
  - [目录](#目录)
  - [1. 范畴论基础定义](#1-范畴论基础定义)
    - [1.1 范畴的形式化定义](#11-范畴的形式化定义)
    - [1.2 态射与组合律](#12-态射与组合律)
    - [1.3 同构与等价关系](#13-同构与等价关系)
    - [1.4 特殊对象与态射](#14-特殊对象与态射)
  - [2. 函子理论](#2-函子理论)
    - [2.1 函子的定义与性质](#21-函子的定义与性质)
    - [2.2 函子范畴](#22-函子范畴)
    - [2.3 特殊函子类型](#23-特殊函子类型)
    - [2.4 表示函子](#24-表示函子)
  - [3. 自然变换](#3-自然变换)
    - [3.1 自然变换的形式化定义](#31-自然变换的形式化定义)
    - [3.2 自然同构](#32-自然同构)
    - [3.3 交换图与自然性条件](#33-交换图与自然性条件)
    - [3.4 水平与垂直组合](#34-水平与垂直组合)
  - [4. 伴随函子](#4-伴随函子)
    - [4.1 伴随函子的定义与性质](#41-伴随函子的定义与性质)
    - [4.2 单位与余单位变换](#42-单位与余单位变换)
    - [4.3 伴随对的等价表示](#43-伴随对的等价表示)
    - [4.4 伴随函子基本定理](#44-伴随函子基本定理)
  - [5. 极限理论](#5-极限理论)
    - [5.1 图与函子](#51-图与函子)
    - [5.2 极限的普遍性质](#52-极限的普遍性质)
    - [5.3 余极限](#53-余极限)
    - [5.4 极限的存在条件](#54-极限的存在条件)
  - [6. 单子与余单子](#6-单子与余单子)
    - [6.1 单子的代数定义](#61-单子的代数定义)
    - [6.2 克莱斯利范畴](#62-克莱斯利范畴)
    - [6.3 单子代数与余代数](#63-单子代数与余代数)
    - [6.4 单子的组合定理](#64-单子的组合定理)
  - [7. 高级定理与推论](#7-高级定理与推论)
    - [7.1 Yoneda引理及其证明](#71-yoneda引理及其证明)
    - [7.2 可表函子定理](#72-可表函子定理)
    - [7.3 伴随函数定理](#73-伴随函数定理)
    - [7.4 巴尔加定理](#74-巴尔加定理)
  - [8. 笛卡尔闭范畴](#8-笛卡尔闭范畴)
    - [8.1 笛卡尔积与终对象](#81-笛卡尔积与终对象)
    - [8.2 指数对象与内部Hom](#82-指数对象与内部hom)
    - [8.3 闭性质与柯里化](#83-闭性质与柯里化)
    - [8.4 笛卡尔闭范畴的性质定理](#84-笛卡尔闭范畴的性质定理)

## 1. 范畴论基础定义

### 1.1 范畴的形式化定义

**定义 1.1.1**：一个范畴 \(\mathcal{C}\) 由以下组成：

- 对象的集合 \(\text{Obj}(\mathcal{C})\)
- 对于每对对象 \(A, B \in \text{Obj}(\mathcal{C})\)，态射的集合 \(\text{Hom}_{\mathcal{C}}(A, B)\)
- 对于每个对象 \(A\)，恒等态射 \(\text{id}_A \in \text{Hom}_{\mathcal{C}}(A, A)\)
- 组合运算 \(\circ\)，将态射 \(f \in \text{Hom}_{\mathcal{C}}(A, B)\) 和 \(g \in \text{Hom}_{\mathcal{C}}(B, C)\) 映射到 \(g \circ f \in \text{Hom}_{\mathcal{C}}(A, C)\)

满足以下公理：

- 结合律：对于态射 \(f: A \to B\)，\(g: B \to C\)，\(h: C \to D\)，有 \(h \circ (g \circ f) = (h \circ g) \circ f\)
- 单位律：对于任何态射 \(f: A \to B\)，有 \(f \circ \text{id}_A = f\) 且 \(\text{id}_B \circ f = f\)

**例 1.1.2**：集合范畴 \(\mathbf{Set}\)，其中对象是集合，态射是函数，组合是函数组合。

**例 1.1.3**：拓扑空间范畴 \(\mathbf{Top}\)，其中对象是拓扑空间，态射是连续映射。

**命题 1.1.4**：任何偏序集 \((P, \leq)\) 可视为范畴，其中对象是 \(P\) 中的元素，且当且仅当 \(a \leq b\) 时存在唯一态射 \(a \to b\)。

### 1.2 态射与组合律

**定义 1.2.1**：态射 \(f: A \to B\) 是同构，如果存在态射 \(g: B \to A\)，使得 \(g \circ f = \text{id}_A\) 且 \(f \circ g = \text{id}_B\)。记 \(A \cong B\)。

**定义 1.2.2**：态射 \(f: A \to B\) 是单态射（单射，monomorphism），如果对任何对象 \(Z\) 和任何态射 \(g, h: Z \to A\)，若 \(f \circ g = f \circ h\)，则 \(g = h\)。

**定义 1.2.3**：态射 \(f: A \to B\) 是满态射（满射，epimorphism），如果对任何对象 \(Z\) 和任何态射 \(g, h: B \to Z\)，若 \(g \circ f = h \circ f\)，则 \(g = h\)。

**定理 1.2.4**：在 \(\mathbf{Set}\) 中，单态射等价于单射函数，满态射等价于满射函数。

**证明**：

1. 单态射 ⇔ 单射：
   设 \(f: A \to B\) 是函数。
   - (⇒) 假设 \(f\) 是单态射，对于任意 \(a, a' \in A\)，若 \(f(a) = f(a')\)，考虑两个函数 \(g, h: \{\*\} \to A\)，其中 \(g(\*) = a\)，\(h(\*) = a'\)。由于 \(f \circ g = f \circ h\)，由单态射性质得 \(g = h\)，因此 \(a = a'\)，所以 \(f\) 是单射。

   - (⇐) 假设 \(f\) 是单射，对于任意函数 \(g, h: Z \to A\)，若 \(f \circ g = f \circ h\)，则对任意 \(z \in Z\)，有 \(f(g(z)) = f(h(z))\)。由 \(f\) 的单射性得 \(g(z) = h(z)\)，因此 \(g = h\)，所以 \(f\) 是单态射。

2. 满态射 ⇔ 满射：类似地证明。

**命题 1.2.5**：态射的组合保持单态射和满态射性质：

- 如果 \(f: A \to B\) 和 \(g: B \to C\) 都是单态射，则 \(g \circ f: A \to C\) 也是单态射。
- 如果 \(f: A \to B\) 和 \(g: B \to C\) 都是满态射，则 \(g \circ f: A \to C\) 也是满态射。

### 1.3 同构与等价关系

**定义 1.3.1**：对象 \(A\) 和 \(B\) 称为同构的，如果存在同构态射 \(f: A \to B\)。

**定理 1.3.2**：同构关系 \(\cong\) 是对象集合上的等价关系。

**证明**：

1. 自反性：对任意对象 \(A\)，恒等态射 \(\text{id}_A: A \to A\) 是同构，因为 \(\text{id}_A \circ \text{id}_A = \text{id}_A\)。
2. 对称性：若 \(A \cong B\) 通过同构 \(f: A \to B\)，则存在 \(g: B \to A\) 使得 \(g \circ f = \text{id}_A\) 且 \(f \circ g = \text{id}_B\)，所以 \(B \cong A\) 通过同构 \(g\)。
3. 传递性：若 \(A \cong B\) 通过同构 \(f: A \to B\)，且 \(B \cong C\) 通过同构 \(h: B \to C\)，则 \(h \circ f: A \to C\) 是同构，其逆为 \(f^{-1} \circ h^{-1}: C \to A\)。

**定义 1.3.3**：范畴 \(\mathcal{C}\) 和 \(\mathcal{D}\) 称为等价的，记作 \(\mathcal{C} \simeq \mathcal{D}\)，如果存在函子 \(F: \mathcal{C} \to \mathcal{D}\) 和 \(G: \mathcal{D} \to \mathcal{C}\)，使得 \(G \circ F \cong \text{Id}_{\mathcal{C}}\) 且 \(F \circ G \cong \text{Id}_{\mathcal{D}}\)，其中 \(\cong\) 表示自然同构。

### 1.4 特殊对象与态射

**定义 1.4.1**：对象 \(T\) 是范畴 \(\mathcal{C}\) 中的终对象（terminal object），如果对于 \(\mathcal{C}\) 中的每个对象 \(A\)，存在唯一的态射 \(A \to T\)。

**定义 1.4.2**：对象 \(I\) 是范畴 \(\mathcal{C}\) 中的始对象（initial object），如果对于 \(\mathcal{C}\) 中的每个对象 \(A\)，存在唯一的态射 \(I \to A\)。

**定义 1.4.3**：对象 \(Z\) 是范畴 \(\mathcal{C}\) 中的零对象（zero object），如果它既是始对象又是终对象。

**定理 1.4.4**：如果终对象存在，则它在同构意义下是唯一的。

**证明**：假设 \(T\) 和 \(T'\) 都是终对象。由终对象定义，存在唯一态射 \(f: T \to T'\) 和 \(g: T' \to T\)。考虑组合 \(g \circ f: T \to T\)，由于终对象性质，从 \(T\) 到 \(T\) 的唯一态射是 \(\text{id}_T\)，所以 \(g \circ f = \text{id}_T\)。类似地，\(f \circ g = \text{id}_{T'}\)。因此 \(T \cong T'\)。

**定义 1.4.5**：态射 \(e: A \to B\) 是分裂单态射（split monomorphism），如果存在态射 \(r: B \to A\) 使得 \(r \circ e = \text{id}_A\)。

**定义 1.4.6**：态射 \(p: A \to B\) 是分裂满态射（split epimorphism），如果存在态射 \(s: B \to A\) 使得 \(p \circ s = \text{id}_B\)。

**命题 1.4.7**：每个分裂单态射都是单态射，每个分裂满态射都是满态射。

## 2. 函子理论

### 2.1 函子的定义与性质

**定义 2.1.1**：给定范畴 \(\mathcal{C}\) 和 \(\mathcal{D}\)，函子 \(F: \mathcal{C} \to \mathcal{D}\) 包括：

- 对象映射：将 \(\mathcal{C}\) 中的每个对象 \(A\) 映射到 \(\mathcal{D}\) 中的对象 \(F(A)\)
- 态射映射：将每个态射 \(f: A \to B\) 映射到态射 \(F(f): F(A) \to F(B)\)

满足以下条件：

- 保持恒等态射：\(F(\text{id}_A) = \text{id}_{F(A)}\)
- 保持组合：\(F(g \circ f) = F(g) \circ F(f)\)

**定义 2.1.2**：函子 \(F: \mathcal{C} \to \mathcal{D}\) 是满函子（full functor），如果对于任何 \(A, B \in \mathcal{C}\)，映射 \(F_{A,B}: \text{Hom}_{\mathcal{C}}(A, B) \to \text{Hom}_{\mathcal{D}}(F(A), F(B))\) 是满射。

**定义 2.1.3**：函子 \(F: \mathcal{C} \to \mathcal{D}\) 是忠实函子（faithful functor），如果对于任何 \(A, B \in \mathcal{C}\)，映射 \(F_{A,B}: \text{Hom}_{\mathcal{C}}(A, B) \to \text{Hom}_{\mathcal{D}}(F(A), F(B))\) 是单射。

**定义 2.1.4**：函子 \(F: \mathcal{C} \to \mathcal{D}\) 是本质满（essentially surjective），如果对于 \(\mathcal{D}\) 中的每个对象 \(D\)，存在 \(\mathcal{C}\) 中的对象 \(C\)，使得 \(F(C) \cong D\)。

**定理 2.1.5**：范畴等价可通过函子性质表征：范畴 \(\mathcal{C}\) 和 \(\mathcal{D}\) 等价，当且仅当存在函子 \(F: \mathcal{C} \to \mathcal{D}\)，它既是满函子，又是忠实函子，且本质满。

**证明**：

- (⇒) 假设 \(\mathcal{C} \simeq \mathcal{D}\)，存在函子 \(F: \mathcal{C} \to \mathcal{D}\) 和 \(G: \mathcal{D} \to \mathcal{C}\) 及自然同构 \(\eta: \text{Id}_{\mathcal{C}} \Rightarrow G \circ F\) 和 \(\epsilon: F \circ G \Rightarrow \text{Id}_{\mathcal{D}}\)。对于任意 \(A, B \in \mathcal{C}\) 和态射 \(g: F(A) \to F(B)\)，可构造 \(f = \eta_B^{-1} \circ G(g) \circ \eta_A: A \to B\)，可证明 \(F(f) = g\)，所以 \(F\) 是满函子。类似可证明 \(F\) 是忠实函子和本质满的。
- (⇐) 假设 \(F\) 满足条件，可构造伪逆函子 \(G: \mathcal{D} \to \mathcal{C}\) 及相应的自然变换，证明它们满足范畴等价的条件。

### 2.2 函子范畴

**定义 2.2.1**：给定范畴 \(\mathcal{C}\) 和 \(\mathcal{D}\)，函子范畴 \(\mathcal{D}^{\mathcal{C}}\) 的对象是函子 \(F: \mathcal{C} \to \mathcal{D}\)，态射是自然变换 \(\alpha: F \Rightarrow G\)。

**定理 2.2.2**：函子范畴 \(\mathcal{D}^{\mathcal{C}}\) 构成一个合法的范畴，其中态射组合是自然变换的垂直组合。

**证明**：需验证自然变换的垂直组合满足结合律，以及恒等自然变换 \(\text{id}_F\) 的分量 \((\text{id}_F)_A = \text{id}_{F(A)}\) 满足单位律。

**命题 2.2.3**：如果 \(\mathcal{D}\) 有极限（或余极限），则 \(\mathcal{D}^{\mathcal{C}}\) 也有逐点定义的极限（或余极限）。

### 2.3 特殊函子类型

**定义 2.3.1**：对偶函子（contravariant functor）\(F: \mathcal{C}^{op} \to \mathcal{D}\) 将 \(\mathcal{C}\) 中的态射 \(f: A \to B\) 映射到 \(\mathcal{D}\) 中的态射 \(F(f): F(B) \to F(A)\)，逆转了态射方向。

**定义 2.3.2**：自函子（endofunctor）是从范畴到其自身的函子 \(F: \mathcal{C} \to \mathcal{C}\)。

**定义 2.3.3**：恒等函子 \(\text{Id}_{\mathcal{C}}: \mathcal{C} \to \mathcal{C}\) 将每个对象和态射映射到其自身。

**定义 2.3.4**：常值函子 \(\Delta_D: \mathcal{C} \to \mathcal{D}\) 将 \(\mathcal{C}\) 的所有对象映射到 \(\mathcal{D}\) 中的固定对象 \(D\)，所有态射映射到 \(\text{id}_D\)。

**定义 2.3.5**：遗忘函子（forgetful functor）通常从结构丰富的范畴到结构较少的范畴，"遗忘"了一些结构。

### 2.4 表示函子

**定义 2.4.1**：对于范畴 \(\mathcal{C}\) 中的对象 \(A\)，共变Hom函子 \(\text{Hom}_{\mathcal{C}}(A, -): \mathcal{C} \to \mathbf{Set}\) 将每个对象 \(B\) 映射到集合 \(\text{Hom}_{\mathcal{C}}(A, B)\)，将态射 \(f: B \to C\) 映射到函数 \(f_*: \text{Hom}_{\mathcal{C}}(A, B) \to \text{Hom}_{\mathcal{C}}(A, C)\)，其中 \(f_*(g) = f \circ g\)。

**定义 2.4.2**：对于范畴 \(\mathcal{C}\) 中的对象 \(B\)，反变Hom函子 \(\text{Hom}_{\mathcal{C}}(-, B): \mathcal{C}^{op} \to \mathbf{Set}\) 将每个对象 \(A\) 映射到集合 \(\text{Hom}_{\mathcal{C}}(A, B)\)，将态射 \(f: A \to C\) 映射到函数 \(f^\*: \text{Hom}_{\mathcal{C}}(C, B) \to \text{Hom}_{\mathcal{C}}(A, B)\)，其中 \(f^*(g) = g \circ f\)。

**定义 2.4.3**：函子 \(F: \mathcal{C} \to \mathbf{Set}\) 是可表示的（representable），如果存在 \(\mathcal{C}\) 中的对象 \(A\)，使得 \(F \cong \text{Hom}_{\mathcal{C}}(A, -)\)。

## 3. 自然变换

### 3.1 自然变换的形式化定义

**定义 3.1.1**：给定函子 \(F, G: \mathcal{C} \to \mathcal{D}\)，自然变换 \(\alpha: F \Rightarrow G\) 是一族态射的集合 \(\{\alpha_A: F(A) \to G(A) \mid A \in \mathcal{C}\}\)，对于 \(\mathcal{C}\) 中的每个态射 \(f: A \to B\)，下图交换：

\[
\begin{CD}
F(A) @>{\alpha_A}>> G(A) \\
@V{F(f)}VV @VV{G(f)}V \\
F(B) @>>{\alpha_B}> G(B)
\end{CD}
\]

即 \(G(f) \circ \alpha_A = \alpha_B \circ F(f)\)。

**定义 3.1.2**：自然变换的分量 \(\alpha_A\) 是从 \(F(A)\) 到 \(G(A)\) 的态射。

**命题 3.1.3**：自然变换的自然性条件保证了结构的一致性变换，不依赖于具体的对象选择。

### 3.2 自然同构

**定义 3.2.1**：自然变换 \(\alpha: F \Rightarrow G\) 是自然同构，如果对于每个对象 \(A\)，分量 \(\alpha_A: F(A) \to G(A)\) 是同构。记作 \(F \cong G\)。

**定理 3.2.2**：给定自然同构 \(\alpha: F \Rightarrow G\)，存在自然同构 \(\alpha^{-1}: G \Rightarrow F\)，使得 \(\alpha^{-1}_A = (\alpha_A)^{-1}\)。

**证明**：对于每个对象 \(A\)，由于 \(\alpha_A\) 是同构，\((\alpha_A)^{-1}\) 存在。需要证明 \(\alpha^{-1}\) 满足自然性条件。对于任意态射 \(f: A \to B\)，有 \(G(f) \circ \alpha_A = \alpha_B \circ F(f)\)。两边同时应用 \((\alpha_B)^{-1}\) 和 \((\alpha_A)^{-1}\)，得到 \((\alpha_B)^{-1} \circ G(f) = F(f) \circ (\alpha_A)^{-1}\)，即 \(F(f) \circ \alpha^{-1}_A = \alpha^{-1}_B \circ G(f)\)，这正是 \(\alpha^{-1}\) 的自然性条件。

### 3.3 交换图与自然性条件

**定义 3.3.1**：交换图是表示等式关系的图形，其中每条路径代表一个组合态射，两条不同路径表示相等的组合态射。

**定理 3.3.2**：自然性条件可通过交换图直观表示，这是验证自然变换的核心工具。

**证明方法**：利用交换图跟踪态射组合，验证不同路径导致相同结果。

### 3.4 水平与垂直组合

**定义 3.4.1**：给定自然变换 \(\alpha: F \Rightarrow G\) 和 \(\beta: G \Rightarrow H\)，其中 \(F, G, H: \mathcal{C} \to \mathcal{D}\)，它们的垂直组合 \(\beta \circ \alpha: F \Rightarrow H\) 定义为 \((\beta \circ \alpha)_A = \beta_A \circ \alpha_A\)。

**定义 3.4.2**：给定自然变换 \(\alpha: F \Rightarrow G\)，其中 \(F, G: \mathcal{C} \to \mathcal{D}\)，和 \(\beta: H \Rightarrow K\)，其中 \(H, K: \mathcal{D} \to \mathcal{E}\)，它们的水平组合 \(\beta \* \alpha: H \circ F \Rightarrow K \circ G\) 定义为 \((\beta \* \alpha)_A = \beta_{G(A)} \circ H(\alpha_A) = K(\alpha_A) \circ \beta_{F(A)}\)。

**定理 3.4.3**（交换定律）：水平组合和垂直组合满足交换律：\((\beta' \circ \beta) \* (\alpha' \circ \alpha) = (\beta' \* \alpha') \circ (\beta \* \alpha)\)。

**证明**：通过分量级别的计算，跟踪态射组合并验证等式。

## 4. 伴随函子

### 4.1 伴随函子的定义与性质

**定义 4.1.1**：函子 \(F: \mathcal{C} \to \mathcal{D}\) 和 \(G: \mathcal{D} \to \mathcal{C}\) 形成伴随对（adjunction），记作 \(F \dashv G\)，如果对于所有对象 \(A \in \mathcal{C}\) 和 \(B \in \mathcal{D}\)，存在自然双射：
\[ \text{Hom}_{\mathcal{D}}(F(A), B) \cong \text{Hom}_{\mathcal{C}}(A, G(B)) \]

**定义 4.1.2**：在伴随对 \(F \dashv G\) 中，\(F\) 称为左伴随，\(G\) 称为右伴随。

**命题 4.1.3**：伴随函子提供了一种正式机制，使得某一范畴中的构造能在另一范畴中找到对应物。

### 4.2 单位与余单位变换

**定义 4.2.1**：给定伴随对 \(F \dashv G\)，单位自然变换 \(\eta: \text{Id}_{\mathcal{C}} \Rightarrow G \circ F\) 对于每个 \(A \in \mathcal{C}\) 给出态射 \(\eta_A: A \to G(F(A))\)。

**定义 4.2.2**：给定伴随对 \(F \dashv G\)，余单位自然变换 \(\epsilon: F \circ G \Rightarrow \text{Id}_{\mathcal{D}}\) 对于每个 \(B \in \mathcal{D}\) 给出态射 \(\epsilon_B: F(G(B)) \to B\)。

**命题 4.2.3**：单位和余单位自然变换满足三角恒等式：
\[ (G\epsilon) \circ (\eta G) = \text{id}_G \quad \text{和} \quad (\epsilon F) \circ (F\eta) = \text{id}_F \]

### 4.3 伴随对的等价表示

**定理 4.3.1**：以下条件等价：

1. 存在伴随对 \(F \dashv G\)
2. 存在单位 \(\eta: \text{Id}_{\mathcal{C}} \Rightarrow G \circ F\) 和余单位 \(\epsilon: F \circ G \Rightarrow \text{Id}_{\mathcal{D}}\)，满足三角恒等式
3. 对于每个 \(A \in \mathcal{C}\)，函子 \(\text{Hom}_{\mathcal{D}}(F(A), -)\) 可表示为 \(\text{Hom}_{\mathcal{C}}(A, G(-))\)

**证明**：证明三个条件之间的等价性，通常通过构造相应的自然变换和验证其性质。

### 4.4 伴随函子基本定理

**定理 4.4.1**（伴随函子基本定理）：如果函子 \(G: \mathcal{D} \to \mathcal{C}\) 有左伴随，则其保持所有极限；如果 \(F: \mathcal{C} \to \mathcal{D}\) 有右伴随，则其保持所有余极限。

**证明**：假设 \(F \dashv G\)，需要证明 \(G\) 保持极限。考虑图 \(J\) 和函子 \(D: J \to \mathcal{D}\)，假设 \(\lim D\) 存在。需要证明 \(G(\lim D) \cong \lim (G \circ D)\)。

利用伴随性质，对于任何 \(C \in \mathcal{C}\)，有：
\[ \text{Hom}_{\mathcal{C}}(C, G(\lim D)) \cong \text{Hom}_{\mathcal{D}}(F(C), \lim D) \cong \lim \text{Hom}_{\mathcal{D}}(F(C), D(-)) \cong \lim \text{Hom}_{\mathcal{C}}(C, G(D(-))) \cong \text{Hom}_{\mathcal{C}}(C, \lim (G \circ D)) \]

由Yoneda引理，\(G(\lim D) \cong \lim (G \circ D)\)，因此 \(G\) 保持极限。

类似地证明 \(F\) 保持余极限。

## 5. 极限理论

### 5.1 图与函子

**定义 5.1.1**：小范畴 \(J\) 称为图（diagram），函子 \(D: J \to \mathcal{C}\) 称为 \(\mathcal{C}\) 中的 \(J\) 形图。

**定义 5.1.2**：图 \(J\) 可以是任何小范畴，常见的包括离散范畴、有序集、箭头范畴等。

**例 5.1.3**：产品图是由两个对象组成的离散范畴；等化器图是由两个对象和两个并行态射组成的范畴。

### 5.2 极限的普遍性质

**定义 5.2.1**：给定图 \(D: J \to \mathcal{C}\)，锥（cone）是一个对象 \(L\) 和一族态射 \(\{\pi_j: L \to D(j) \mid j \in J\}\)，使得对于 \(J\) 中的每个态射 \(f: j \to k\)，有 \(D(f) \circ \pi_j = \pi_k\)。

**定义 5.2.2**：图 \(D: J \to \mathcal{C}\) 的极限（limit）是一个锥 \((L, \{\pi_j\})\)，使得对于任何其他锥 \((N, \{\nu_j\})\)，存在唯一的态射 \(u: N \to L\)，使得对所有 \(j \in J\)，有 \(\pi_j \circ u = \nu_j\)。

**定理 5.2.3**：极限的普遍性质保证了它是所有锥中最"经济"的表示。

**证明**：通过普遍性质的定义直接得出。如果存在两个极限 \((L, \{\pi_j\})\) 和 \((L', \{\pi'_j\})\)，由普遍性质可得到唯一态射 \(u: L \to L'\) 和 \(v: L' \to L\)，满足 \(\pi'_j \circ u = \pi_j\) 和 \(\pi_j \circ v = \pi'_j\)。可以证明 \(v \circ u = \text{id}_L\) 和 \(u \circ v = \text{id}_{L'}\)，因此 \(L \cong L'\)。由于恒等态射 \(\text{id}_L: L \to L\) 满足 \(\pi_j \circ \text{id}_L = \pi_j\)，而由普遍性质，满足此条件的态射唯一，所以 \(v \circ u = \text{id}_L\)。类似地，\(u \circ v = \text{id}_{L'}\)。

**例 5.2.4**：在 \(\mathbf{Set}\) 中，两个对象 \(A\) 和 \(B\) 的极限是笛卡尔积 \(A \times B\)，配有投影 \(\pi_A: A \times B \to A\) 和 \(\pi_B: A \times B \to B\)。

**定理 5.2.5**：设 \(D, E: J \to \mathcal{C}\) 是两个形状相同的图，\(\alpha: D \Rightarrow E\) 是自然变换。如果 \(\lim D\) 和 \(\lim E\) 存在，则存在唯一态射 \(\lim \alpha: \lim D \to \lim E\)，使得对所有 \(j \in J\)，有 \(\pi^E_j \circ (\lim \alpha) = \alpha_j \circ \pi^D_j\)。

**证明**：考虑锥 \((L_D, \{\pi^D_j\})\) 作为 \(D\) 的极限，我们可以构造一个 \(E\) 的锥 \((L_D, \{\alpha_j \circ \pi^D_j\})\)。由 \(E\) 的极限 \((L_E, \{\pi^E_j\})\) 的普遍性质，存在唯一态射 \(u: L_D \to L_E\)，满足对所有 \(j \in J\)，\(\pi^E_j \circ u = \alpha_j \circ \pi^D_j\)。定义 \(\lim \alpha = u\)。

### 5.3 余极限

**定义 5.3.1**：给定图 \(D: J \to \mathcal{C}\)，余锥（cocone）是一个对象 \(C\) 和一族态射 \(\{\iota_j: D(j) \to C \mid j \in J\}\)，使得对于 \(J\) 中的每个态射 \(f: j \to k\)，有 \(\iota_k \circ D(f) = \iota_j\)。

**定义 5.3.2**：图 \(D: J \to \mathcal{C}\) 的余极限（colimit）是一个余锥 \((C, \{\iota_j\})\)，使得对于任何其他余锥 \((N, \{\nu_j\})\)，存在唯一的态射 \(u: C \to N\)，使得对所有 \(j \in J\)，有 \(u \circ \iota_j = \nu_j\)。

**命题 5.3.3**：余极限是极限的对偶概念，可以通过在对偶范畴中考虑极限来定义：\(\text{colim}_{\mathcal{C}} D = (\lim_{\mathcal{C}^{op}} D^{op})^{op}\)。

**例 5.3.4**：在 \(\mathbf{Set}\) 中，对象的余积（coproduct）是它们的不相交并集，通常记为 \(A \sqcup B\)。

### 5.4 极限的存在条件

**定理 5.4.1**（极限存在定理）：如果范畴 \(\mathcal{C}\) 有所有有限积和所有等化器，则它有所有有限极限。

**证明**：给定有限图 \(D: J \to \mathcal{C}\)，我们可以构造其极限如下：

1. 令 \(P = \prod_{j \in J} D(j)\) 为所有对象的积，配有投影 \(\pi_j: P \to D(j)\)。
2. 对于 \(J\) 中的每个态射 \(f: j \to k\)，考虑两个态射 \(D(f) \circ \pi_j, \pi_k: P \to D(k)\)。
3. 令 \(E\) 为所有这些态射对的等化器：\(E \xrightarrow{e} P\)，使得对于所有 \(f: j \to k\)，有 \(D(f) \circ \pi_j \circ e = \pi_k \circ e\)。
4. 可以证明 \((E, \{\pi_j \circ e\})\) 是 \(D\) 的极限。

**定理 5.4.2**（可完备性）：范畴 \(\mathcal{C}\) 是完备的（有所有小极限），当且仅当它有所有小积和所有小等化器。

**证明**：类似于有限情况，但需要处理小图而非有限图。

**定理 5.4.3**（余可完备性）：范畴 \(\mathcal{C}\) 是余完备的（有所有小余极限），当且仅当它有所有小余积和所有小余等化器。

## 6. 单子与余单子

### 6.1 单子的代数定义

**定义 6.1.1**：单子（monad）是一个三元组 \((T, \eta, \mu)\)，其中：

- \(T: \mathcal{C} \to \mathcal{C}\) 是自函子
- \(\eta: \text{Id}_{\mathcal{C}} \Rightarrow T\) 是单位自然变换
- \(\mu: T^2 \Rightarrow T\) 是乘法自然变换（其中 \(T^2 = T \circ T\)）

满足以下单子律：

- 结合律：\(\mu \circ T\mu = \mu \circ \mu T\)，即下图交换：
\[
\begin{CD}
T^3 @>{T\mu}>> T^2 \\
@V{\mu T}VV @VV{\mu}V \\
T^2 @>>{\mu}> T
\end{CD}
\]
- 单位律：\(\mu \circ \eta T = \mu \circ T\eta = \text{id}_T\)，即下图交换：
\[
\begin{CD}
T @>{\eta T}>> T^2 @<{T\eta}<< T \\
@V{\text{id}_T}VV @VV{\mu}V @VV{\text{id}_T}V \\
T @= T @= T
\end{CD}
\]

**定理 6.1.2**：单子可以看作是内部代数的抽象化，代表了计算的顺序组合。

**例 6.1.3**：标准的单子例子包括：

- 恒等单子：\((\text{Id}, \text{id}, \text{id})\)
- 幂集单子：\((\mathcal{P}, \{-\}, \bigcup)\) 在 \(\mathbf{Set}\) 上
- 列表单子：\((L, \text{singleton}, \text{concat})\) 在 \(\mathbf{Set}\) 上

### 6.2 克莱斯利范畴

**定义 6.2.1**：给定单子 \((T, \eta, \mu)\)，克莱斯利范畴（Kleisli category）\(\mathcal{C}_T\) 定义为：

- 对象与 \(\mathcal{C}\) 相同
- 态射 \(f: A \to_T B\) 对应于 \(\mathcal{C}\) 中的态射 \(\bar{f}: A \to T(B)\)
- 恒等态射 \(\text{id}_A: A \to_T A\) 对应于 \(\eta_A: A \to T(A)\)
- 态射组合 \(g \circ_T f\) 对应于 \(\mu_C \circ T(\bar{g}) \circ \bar{f}\)

**定理 6.2.2**：对于任何单子 \((T, \eta, \mu)\)，克莱斯利范畴 \(\mathcal{C}_T\) 构成合法范畴。

**证明**：需验证恒等律和结合律。对于恒等律，考虑 \(f: A \to_T B\)，有：
\[f \circ_T \text{id}_A = \mu_B \circ T(\bar{f}) \circ \eta_A\]
由单子的单位律，可证明这等于 \(f\)。类似地可证明 \(\text{id}_B \circ_T f = f\)。

对于结合律，考虑 \(f: A \to_T B\)，\(g: B \to_T C\)，\(h: C \to_T D\)，需证明 \((h \circ_T g) \circ_T f = h \circ_T (g \circ_T f)\)。通过单子的结合律可以验证。

**命题 6.2.3**：存在函子 \(F_T: \mathcal{C} \to \mathcal{C}_T\)，将对象保持不变，将态射 \(f: A \to B\) 映射到 \(\eta_B \circ f: A \to_T B\)。

### 6.3 单子代数与余代数

**定义 6.3.1**：给定单子 \((T, \eta, \mu)\)，\(T\)-代数是一个对 \((A, h)\)，其中 \(A\) 是 \(\mathcal{C}\) 中的对象，\(h: T(A) \to A\) 是态射，满足：

- \(h \circ \eta_A = \text{id}_A\)（单位律）
- \(h \circ \mu_A = h \circ T(h)\)（结合律）

**定义 6.3.2**：\(T\)-代数之间的态射 \(f: (A, h) \to (B, g)\) 是态射 \(f: A \to B\)，使得 \(f \circ h = g \circ T(f)\)。

**定理 6.3.3**：\(T\)-代数及其态射构成范畴 \(\mathcal{C}^T\)，称为艾伦伯格-摩尔范畴（Eilenberg-Moore category）。

**定义 6.3.4**：余单子（comonad）是一个三元组 \((D, \epsilon, \delta)\)，其中：

- \(D: \mathcal{C} \to \mathcal{C}\) 是自函子
- \(\epsilon: D \Rightarrow \text{Id}_{\mathcal{C}}\) 是余单位自然变换
- \(\delta: D \Rightarrow D^2\) 是余乘法自然变换

满足对偶的余单子律。

**定义 6.3.5**：\(D\)-余代数是一个对 \((A, k)\)，其中 \(A\) 是 \(\mathcal{C}\) 中的对象，\(k: A \to D(A)\) 是态射，满足对偶的单位律和结合律。

### 6.4 单子的组合定理

**定理 6.4.1**（单子组合）：给定单子 \((S, \eta^S, \mu^S)\) 和 \((T, \eta^T, \mu^T)\)，如果存在分配律自然变换 \(\lambda: ST \Rightarrow TS\)，满足某些一致性条件，则 \(TS\) 可以赋予单子结构。

**证明**：定义：

- 单位：\(\eta^{TS} = T\eta^S \circ \eta^T\)
- 乘法：\(\mu^{TS} = T\mu^S \circ \mu^T T S \circ T \lambda S\)

需验证单子律，通过分配律的一致性条件和两个单子的单子律可以证明。

**应用 6.4.2**：单子组合允许我们构建复杂的计算抽象，例如组合状态和异常处理。

## 7. 高级定理与推论

### 7.1 Yoneda引理及其证明

**定理 7.1.1**（Yoneda引理）：对于任何范畴 \(\mathcal{C}\)，对象 \(A \in \mathcal{C}\)，和函子 \(F: \mathcal{C}^{op} \to \mathbf{Set}\)，存在自然同构：
\[ \text{Nat}(\text{Hom}_{\mathcal{C}}(-, A), F) \cong F(A) \]
其中左边是自然变换集合，右边是集合 \(F(A)\)。

**证明**：定义映射 \(\Phi: \text{Nat}(\text{Hom}_{\mathcal{C}}(-, A), F) \to F(A)\)，对于每个自然变换 \(\alpha: \text{Hom}_{\mathcal{C}}(-, A) \Rightarrow F\)，令 \(\Phi(\alpha) = \alpha_A(\text{id}_A) \in F(A)\)。

定义逆映射 \(\Psi: F(A) \to \text{Nat}(\text{Hom}_{\mathcal{C}}(-, A), F)\)，对于 \(x \in F(A)\)，定义自然变换 \(\Psi(x)\)，其分量 \(\Psi(x)_B: \text{Hom}_{\mathcal{C}}(B, A) \to F(B)\) 定义为 \(\Psi(x)_B(f) = F(f)(x)\)。

可以验证 \(\Psi\) 是良定义的自然变换，且 \(\Phi\) 和 \(\Psi\) 互为逆映射。对于任意 \(\alpha\) 和 \(x = \alpha_A(\text{id}_A)\)，需要证明 \(\Psi(x) = \alpha\)，即对所有 \(B\) 和 \(f: B \to A\)，有 \(\Psi(x)_B(f) = \alpha_B(f)\)。由自然性条件，\(\alpha_B(f) = F(f)(\alpha_A(\text{id}_A)) = F(f)(x) = \Psi(x)_B(f)\)。

**推论 7.1.2**（Yoneda嵌入）：存在满忠实函子 \(Y: \mathcal{C} \to [\mathcal{C}^{op}, \mathbf{Set}]\)，定义为 \(Y(A) = \text{Hom}_{\mathcal{C}}(-, A)\)。

**证明**：由Yoneda引理，对于任意 \(A, B \in \mathcal{C}\)，有 \(\text{Nat}(\text{Hom}_{\mathcal{C}}(-, A), \text{Hom}_{\mathcal{C}}(-, B)) \cong \text{Hom}_{\mathcal{C}}(-, B)(A) = \text{Hom}_{\mathcal{C}}(A, B)\)。这表明 \(Y\) 是满忠实的。

### 7.2 可表函子定理

**定理 7.2.1**：函子 \(F: \mathcal{C} \to \mathbf{Set}\) 是可表示的，当且仅当存在对象 \(A \in \mathcal{C}\) 和自然同构 \(\alpha: \text{Hom}_{\mathcal{C}}(A, -) \Rightarrow F\)。

**证明**：直接应用可表示函子的定义。

**定理 7.2.2**（可表示函子的性质）：可表示函子保持极限。

**证明**：设 \(F \cong \text{Hom}_{\mathcal{C}}(A, -)\)，而 \(\text{Hom}_{\mathcal{C}}(A, -)\) 作为左完全函子保持极限。由自然同构，\(F\) 也保持极限。

### 7.3 伴随函数定理

**定理 7.3.1**（伴随函数定理）：对于函子 \(F: \mathcal{C} \to \mathcal{D}\)，以下条件等价：

1. \(F\) 有右伴随
2. 对于每个 \(D \in \mathcal{D}\)，函子 \(\text{Hom}_{\mathcal{D}}(F(-), D): \mathcal{C}^{op} \to \mathbf{Set}\) 是可表示的

**证明**：
(1 ⇒ 2) 假设 \(F \dashv G\)，则 \(\text{Hom}_{\mathcal{D}}(F(-), D) \cong \text{Hom}_{\mathcal{C}}(-, G(D))\)，因此 \(\text{Hom}_{\mathcal{D}}(F(-), D)\) 是由 \(G(D)\) 表示的。

(2 ⇒ 1) 假设对每个 \(D \in \mathcal{D}\)，存在 \(G(D) \in \mathcal{C}\) 和自然同构 \(\alpha_D: \text{Hom}_{\mathcal{D}}(F(-), D) \Rightarrow \text{Hom}_{\mathcal{C}}(-, G(D))\)。可以证明 \(G\) 可扩展为函子 \(G: \mathcal{D} \to \mathcal{C}\)，使得 \(F \dashv G\)。

### 7.4 巴尔加定理

**定理 7.4.1**（巴尔加定理，Barr-Beck定理）：函子 \(G: \mathcal{D} \to \mathcal{C}\) 是严格单子的（即存在某单子 \(T\) 使得 \(\mathcal{D} \simeq \mathcal{C}^T\)），当且仅当：

1. \(G\) 有左伴随 \(F\)
2. \(G\) 是忠实的
3. \(G\) 保持并反映 \(G\)-分裂余等化器

**证明概述**：巴尔加定理的证明相当复杂，涉及构造单子 \(T = G \circ F\)，并证明 \(\mathcal{D}\) 等价于 \(\mathcal{C}^T\)。

## 8. 笛卡尔闭范畴

### 8.1 笛卡尔积与终对象

**定义 8.1.1**：范畴 \(\mathcal{C}\) 具有有限积，如果对于任何两个对象 \(A, B \in \mathcal{C}\)，存在它们的积 \(A \times B\)，即存在对象 \(A \times B\) 和投影态射 \(\pi_A: A \times B \to A\)，\(\pi_B: A \times B \to B\)，使得对于任何对象 \(C\) 和态射 \(f: C \to A\)，\(g: C \to B\)，存在唯一态射 \(h: C \to A \times B\)，使得 \(\pi_A \circ h = f\) 且 \(\pi_B \circ h = g\)。

**定义 8.1.2**：范畴 \(\mathcal{C}\) 有终对象，如果存在对象 \(1 \in \mathcal{C}\)，使得对于每个对象 \(A \in \mathcal{C}\)，存在唯一态射 \(A \to 1\)。

**定义 8.1.3**：范畴 \(\mathcal{C}\) 是笛卡尔范畴（Cartesian category），如果它有所有有限积和终对象。

**定理 8.1.4**：在笛卡尔范畴中，积构造是可结合的，即存在自然同构 \((A \times B) \times C \cong A \times (B \times C)\)。

**证明**：通过积的普遍性质，构造适当的同构态射并验证其性质。

### 8.2 指数对象与内部Hom

**定义 8.2.1**：在有限积范畴 \(\mathcal{C}\) 中，对象 \(B\) 的对象 \(A\) 上的指数对象（exponential）是对象 \(B^A\)，配有求值态射 \(\text{eval}: B^A \times A \to B\)，使得对于任何对象 \(C\) 和态射 \(f: C \times A \to B\)，存在唯一态射 \(\lambda f: C \to B^A\)，使得 \(\text{eval} \circ (\lambda f \times \text{id}_A) = f\)。

**定义 8.2.2**：范畴 \(\mathcal{C}\) 是笛卡尔闭范畴（Cartesian closed category），如果它是笛卡尔范畴且对每对对象 \(A, B \in \mathcal{C}\)，存在指数对象 \(B^A\)。

**例 8.2.3**：\(\mathbf{Set}\) 是笛卡尔闭范畴，其中 \(B^A\) 是从 \(A\) 到 \(B\) 的所有函数集合。

### 8.3 闭性质与柯里化

**定理 8.3.1**（柯里化）：在笛卡尔闭范畴中，存在自然双射：
\[ \text{Hom}_{\mathcal{C}}(C \times A, B) \cong \text{Hom}_{\mathcal{C}}(C, B^A) \]

**证明**：这直接从指数对象的定义得出。给定 \(f: C \times A \to B\)，其柯里化是唯一的 \(\lambda f: C \to B^A\)。反之，给定 \(g: C \to B^A\)，可通过求值得到 \(\text{eval} \circ (g \times \text{id}_A): C \times A \to B\)。

**定理 8.3.2**：在笛卡尔闭范畴中，函子 \(- \times A: \mathcal{C} \to \mathcal{C}\) 有右伴随 \((-)^A: \mathcal{C} \to \mathcal{C}\)。

**证明**：由柯里化定理，\(\text{Hom}_{\mathcal{C}}(C \times A, B) \cong \text{Hom}_{\mathcal{C}}(C, B^A)\)，这正是伴随关系 \(- \times A \dashv (-)^A\) 的定义。

### 8.4 笛卡尔闭范畴的性质定理

**定理 8.4.1**：在笛卡尔闭范畴中，存在以下自然同构：

1. \(1^A \cong 1\)（单位法则）
2. \((B \times C)^A \cong B^A \times C^A\)（分配律）
3. \(B^{A \times C} \cong (B^C)^A\)（指数法则）

**证明**：这些可通过应用指数对象的普遍性质来证明。例如，对于指数法则，我们构造同构：
\[ \text{Hom}_{\mathcal{C}}(D, B^{A \times C}) \cong \text{Hom}_{\mathcal{C}}(D \times (A \times C), B) \cong \text{Hom}_{\mathcal{C}}((D \times A) \times C, B) \cong \text{Hom}_{\mathcal{C}}(D \times A, B^C) \cong \text{Hom}_{\mathcal{C}}(D, (B^C)^A) \]

**定理 8.4.2**：如果 \(\mathcal{C}\) 是笛卡尔闭范畴，则对于任何对象 \(A \in \mathcal{C}\)，可以定义内部函子范畴 \(\mathcal{C}^A\)，其中：

- 对象是指数对象 \(B^A\)
- 态射由适当的内部自然变换表示

**应用 8.4.3**：笛卡尔闭范畴为函数式编程提供了形式基础，其中：

- 终对象对应单元类型
- 积对应积类型（如元组或记录）
- 指数对象对应函数类型
- 柯里化对应高阶函数

范畴论通过这些抽象概念，为数学、计算机科学和其他领域提供了统一的语言和思考方式。
这些形式化定义和定理不仅揭示了不同结构之间的深层联系，也为创建新理论和解决复杂问题提供了强大工具。
