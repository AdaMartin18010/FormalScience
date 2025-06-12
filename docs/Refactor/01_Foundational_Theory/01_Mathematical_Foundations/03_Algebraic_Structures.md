# 代数结构 (Algebraic Structures)

## 目录

1. [基本概念](#1-基本概念)
2. [群论](#2-群论)
3. [环论](#3-环论)
4. [域论](#4-域论)
5. [模论](#5-模论)
6. [代数同态](#6-代数同态)
7. [代数结构在计算机科学中的应用](#7-代数结构在计算机科学中的应用)

## 1. 基本概念

### 1.1 运算与代数系统

**定义 1.1.1** (二元运算) 集合 $A$ 上的二元运算是函数 $f: A \times A \rightarrow A$。

**定义 1.1.2** (代数系统) 代数系统是二元组 $(A, \cdot)$，其中 $A$ 是非空集合，$\cdot$ 是 $A$ 上的二元运算。

**定义 1.1.3** (运算性质) 设 $\cdot$ 是集合 $A$ 上的二元运算：

1. 结合律：$\forall a, b, c \in A, (a \cdot b) \cdot c = a \cdot (b \cdot c)$
2. 交换律：$\forall a, b \in A, a \cdot b = b \cdot a$
3. 单位元：存在 $e \in A$ 使得 $\forall a \in A, e \cdot a = a \cdot e = a$
4. 逆元：对于 $a \in A$，存在 $a^{-1} \in A$ 使得 $a \cdot a^{-1} = a^{-1} \cdot a = e$

### 1.2 子代数与商代数

**定义 1.2.1** (子代数) 代数系统 $(A, \cdot)$ 的子代数是代数系统 $(B, \cdot_B)$，其中 $B \subseteq A$ 且 $\cdot_B$ 是 $\cdot$ 在 $B$ 上的限制。

**定义 1.2.2** (同余关系) 代数系统 $(A, \cdot)$ 上的同余关系是等价关系 $\sim$，满足：
$$\forall a, b, c, d \in A, a \sim b \land c \sim d \rightarrow a \cdot c \sim b \cdot d$$

**定义 1.2.3** (商代数) 设 $\sim$ 是代数系统 $(A, \cdot)$ 上的同余关系，商代数是 $(A/\sim, \cdot_{\sim})$，其中：

- $A/\sim = \{[a] : a \in A\}$ 是等价类集合
- $[a] \cdot_{\sim} [b] = [a \cdot b]$

## 2. 群论

### 2.1 群的定义

**定义 2.1.1** (群) 群是代数系统 $(G, \cdot)$，满足：

1. 结合律：$(a \cdot b) \cdot c = a \cdot (b \cdot c)$
2. 单位元：存在 $e \in G$ 使得 $\forall a \in G, e \cdot a = a \cdot e = a$
3. 逆元：$\forall a \in G, \exists a^{-1} \in G$ 使得 $a \cdot a^{-1} = a^{-1} \cdot a = e$

**定义 2.1.2** (阿贝尔群) 阿贝尔群是满足交换律的群。

**定理 2.1.1** (单位元唯一性) 群的单位元是唯一的。

**证明** 假设 $e$ 和 $e'$ 都是单位元，则 $e = e \cdot e' = e'$。

**定理 2.1.2** (逆元唯一性) 群中每个元素的逆元是唯一的。

**证明** 假设 $a^{-1}$ 和 $a'$ 都是 $a$ 的逆元，则 $a^{-1} = a^{-1} \cdot e = a^{-1} \cdot (a \cdot a') = (a^{-1} \cdot a) \cdot a' = e \cdot a' = a'$。

### 2.2 子群

**定义 2.2.1** (子群) 群 $(G, \cdot)$ 的子群是子集 $H \subseteq G$，使得 $(H, \cdot_H)$ 是群。

**定理 2.2.1** (子群判定) 群 $G$ 的非空子集 $H$ 是子群当且仅当：

1. $\forall a, b \in H, a \cdot b \in H$
2. $\forall a \in H, a^{-1} \in H$

**证明**

- 必要性：显然
- 充分性：结合律在 $H$ 上成立，单位元 $e = a \cdot a^{-1} \in H$，因此 $H$ 是子群

**定义 2.2.2** (生成子群) 群 $G$ 的子集 $S$ 生成的子群是包含 $S$ 的最小子群，记作 $\langle S \rangle$。

**定理 2.2.2** (拉格朗日定理) 有限群 $G$ 的子群 $H$ 的阶整除 $G$ 的阶。

**证明** 考虑 $H$ 在 $G$ 上的左陪集分解，每个陪集的大小等于 $|H|$，因此 $|G| = |H| \cdot [G : H]$。

### 2.3 群同态

**定义 2.3.1** (群同态) 群 $(G, \cdot)$ 到群 $(H, *)$ 的同态是函数 $f: G \rightarrow H$，满足：
$$\forall a, b \in G, f(a \cdot b) = f(a) * f(b)$$

**定义 2.3.2** (群同构) 群同态 $f: G \rightarrow H$ 是同构，如果 $f$ 是双射。

**定理 2.3.1** (同态基本定理) 设 $f: G \rightarrow H$ 是群同态，则：
$$G/\ker(f) \cong \text{im}(f)$$

**证明** 定义 $\phi: G/\ker(f) \rightarrow \text{im}(f)$ 为 $\phi(a\ker(f)) = f(a)$，可以证明 $\phi$ 是同构。

## 3. 环论

### 3.1 环的定义

**定义 3.1.1** (环) 环是三元组 $(R, +, \cdot)$，其中：

1. $(R, +)$ 是阿贝尔群
2. $(R, \cdot)$ 是半群（满足结合律）
3. 分配律：$\forall a, b, c \in R$，
   - $a \cdot (b + c) = a \cdot b + a \cdot c$
   - $(a + b) \cdot c = a \cdot c + b \cdot c$

**定义 3.1.2** (交换环) 交换环是满足乘法交换律的环。

**定义 3.1.3** (单位环) 单位环是具有乘法单位元的环。

**定义 3.1.4** (整环) 整环是交换单位环，且没有零因子。

### 3.2 理想

**定义 3.2.1** (左理想) 环 $R$ 的左理想是子集 $I \subseteq R$，满足：

1. $(I, +)$ 是 $(R, +)$ 的子群
2. $\forall r \in R, \forall a \in I, r \cdot a \in I$

**定义 3.2.2** (右理想) 环 $R$ 的右理想是子集 $I \subseteq R$，满足：

1. $(I, +)$ 是 $(R, +)$ 的子群
2. $\forall r \in R, \forall a \in I, a \cdot r \in I$

**定义 3.2.3** (理想) 环 $R$ 的理想是既是左理想又是右理想的子集。

**定理 3.2.1** (理想判定) 环 $R$ 的子集 $I$ 是理想当且仅当：

1. $\forall a, b \in I, a - b \in I$
2. $\forall r \in R, \forall a \in I, r \cdot a, a \cdot r \in I$

### 3.3 商环

**定义 3.3.1** (商环) 设 $I$ 是环 $R$ 的理想，商环是 $(R/I, +, \cdot)$，其中：

- $R/I = \{a + I : a \in R\}$
- $(a + I) + (b + I) = (a + b) + I$
- $(a + I) \cdot (b + I) = (a \cdot b) + I$

**定理 3.3.1** (环同态基本定理) 设 $f: R \rightarrow S$ 是环同态，则：
$$R/\ker(f) \cong \text{im}(f)$$

## 4. 域论

### 4.1 域的定义

**定义 4.1.1** (域) 域是三元组 $(F, +, \cdot)$，其中：

1. $(F, +)$ 是阿贝尔群
2. $(F \setminus \{0\}, \cdot)$ 是阿贝尔群
3. 分配律成立

**定义 4.1.2** (子域) 域 $F$ 的子域是子集 $K \subseteq F$，使得 $(K, +, \cdot)$ 是域。

**定理 4.1.1** (子域判定) 域 $F$ 的子集 $K$ 是子域当且仅当：

1. $0, 1 \in K$
2. $\forall a, b \in K, a - b \in K$
3. $\forall a, b \in K, b \neq 0 \rightarrow a \cdot b^{-1} \in K$

### 4.2 域扩张

**定义 4.2.1** (域扩张) 域扩张是域包含 $K \subseteq F$，记作 $F/K$。

**定义 4.2.2** (代数扩张) 域扩张 $F/K$ 是代数的，如果 $F$ 的每个元素都是 $K$ 上代数的。

**定义 4.2.3** (超越扩张) 域扩张 $F/K$ 是超越的，如果存在 $F$ 的元素不是 $K$ 上代数的。

**定理 4.2.1** (有限扩张的性质) 有限域扩张是代数的。

**证明** 设 $[F : K] = n$，对于任意 $a \in F$，集合 $\{1, a, a^2, \ldots, a^n\}$ 线性相关，因此 $a$ 满足 $K$ 上的多项式方程。

## 5. 模论

### 5.1 模的定义

**定义 5.1.1** (左模) 环 $R$ 上的左模是阿贝尔群 $(M, +)$ 和标量乘法 $R \times M \rightarrow M$，满足：

1. $\forall r \in R, \forall m, n \in M, r(m + n) = rm + rn$
2. $\forall r, s \in R, \forall m \in M, (r + s)m = rm + sm$
3. $\forall r, s \in R, \forall m \in M, (rs)m = r(sm)$
4. $\forall m \in M, 1m = m$

**定义 5.1.2** (右模) 环 $R$ 上的右模是阿贝尔群 $(M, +)$ 和标量乘法 $M \times R \rightarrow M$，满足相应的公理。

**定义 5.1.3** (双模) 环 $R$ 和 $S$ 上的双模是既是左 $R$-模又是右 $S$-模的阿贝尔群。

### 5.2 子模与商模

**定义 5.2.1** (子模) 左 $R$-模 $M$ 的子模是子集 $N \subseteq M$，使得 $(N, +)$ 是 $(M, +)$ 的子群，且 $\forall r \in R, \forall n \in N, rn \in N$。

**定义 5.2.2** (商模) 设 $N$ 是左 $R$-模 $M$ 的子模，商模是 $(M/N, +, \cdot)$，其中：

- $M/N = \{m + N : m \in M\}$
- $(m + N) + (n + N) = (m + n) + N$
- $r(m + N) = rm + N$

### 5.3 自由模

**定义 5.3.1** (自由模) 环 $R$ 上的自由模是形如 $R^{(I)}$ 的模，其中 $I$ 是索引集。

**定义 5.3.2** (基) 左 $R$-模 $M$ 的基是线性无关的生成集。

**定理 5.3.1** (自由模的性质) 自由模的基的基数（如果有限）是唯一的。

**证明** 使用线性代数的标准方法。

## 6. 代数同态

### 6.1 同态与同构

**定义 6.1.1** (环同态) 环 $(R, +, \cdot)$ 到环 $(S, \oplus, \odot)$ 的同态是函数 $f: R \rightarrow S$，满足：

1. $\forall a, b \in R, f(a + b) = f(a) \oplus f(b)$
2. $\forall a, b \in R, f(a \cdot b) = f(a) \odot f(b)$
3. $f(1_R) = 1_S$（如果环有单位元）

**定义 6.1.2** (模同态) 左 $R$-模 $M$ 到左 $R$-模 $N$ 的同态是函数 $f: M \rightarrow N$，满足：

1. $\forall m, n \in M, f(m + n) = f(m) + f(n)$
2. $\forall r \in R, \forall m \in M, f(rm) = rf(m)$

### 6.2 同态基本定理

**定理 6.2.1** (环同态基本定理) 设 $f: R \rightarrow S$ 是环同态，则：
$$R/\ker(f) \cong \text{im}(f)$$

**定理 6.2.2** (模同态基本定理) 设 $f: M \rightarrow N$ 是模同态，则：
$$M/\ker(f) \cong \text{im}(f)$$

## 7. 代数结构在计算机科学中的应用

### 7.1 密码学

**应用 7.1.1** (椭圆曲线密码学) 基于椭圆曲线群的点群运算。

**应用 7.1.2** (RSA算法) 基于模运算和欧拉定理。

**应用 7.1.3** (有限域) 在AES等对称加密算法中的应用。

### 7.2 编码理论

**应用 7.2.1** (线性码) 基于有限域上的向量空间。

**应用 7.2.2** (循环码) 基于多项式环的商环。

**应用 7.2.3** (Reed-Solomon码) 基于有限域上的多项式。

### 7.3 计算机代数

**应用 7.3.1** (多项式计算) 基于多项式环的运算。

**应用 7.3.2** (格约简) 基于格理论的算法。

**应用 7.3.3** (代数几何) 在计算机图形学中的应用。

### 7.4 类型理论

**应用 7.4.1** (范畴论) 为类型理论提供数学基础。

**应用 7.4.2** (代数数据类型) 基于初始代数和终结代数。

**应用 7.4.3** (函子) 在函数式编程中的应用。

---

**参考文献**

1. Dummit, D. S., & Foote, R. M. (2004). *Abstract Algebra*. John Wiley & Sons.
2. Lang, S. (2002). *Algebra*. Springer-Verlag.
3. Hungerford, T. W. (1974). *Algebra*. Springer-Verlag.
4. Artin, M. (1991). *Algebra*. Prentice Hall.
