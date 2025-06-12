# 集合论基础 (Set Theory Foundation)

## 目录

1. [基本概念](#1-基本概念)
2. [集合运算](#2-集合运算)
3. [关系与函数](#3-关系与函数)
4. [基数理论](#4-基数理论)
5. [序数理论](#5-序数理论)
6. [公理化集合论](#6-公理化集合论)
7. [应用与扩展](#7-应用与扩展)

## 1. 基本概念

### 1.1 集合的定义

**定义 1.1.1** (集合) 集合是满足某种性质的对象的总和。如果 $x$ 是集合 $A$ 的元素，记作 $x \in A$。

**公理 1.1.1** (外延公理) 两个集合相等当且仅当它们包含相同的元素：
$$\forall A \forall B [\forall x(x \in A \leftrightarrow x \in B) \rightarrow A = B]$$

**公理 1.1.2** (空集公理) 存在一个不包含任何元素的集合：
$$\exists \emptyset \forall x(x \notin \emptyset)$$

**定理 1.1.1** (空集唯一性) 空集是唯一的。

**证明** 假设存在两个空集 $\emptyset_1$ 和 $\emptyset_2$。根据空集公理，对于任意 $x$，都有 $x \notin \emptyset_1$ 和 $x \notin \emptyset_2$。因此，对于任意 $x$，$x \in \emptyset_1 \leftrightarrow x \in \emptyset_2$ 都成立。根据外延公理，$\emptyset_1 = \emptyset_2$。

### 1.2 子集与真子集

**定义 1.2.1** (子集) 集合 $A$ 是集合 $B$ 的子集，记作 $A \subseteq B$，如果 $A$ 的每个元素都是 $B$ 的元素：
$$A \subseteq B \leftrightarrow \forall x(x \in A \rightarrow x \in B)$$

**定义 1.2.2** (真子集) 集合 $A$ 是集合 $B$ 的真子集，记作 $A \subset B$，如果 $A \subseteq B$ 且 $A \neq B$：
$$A \subset B \leftrightarrow A \subseteq B \land A \neq B$$

**定理 1.2.1** (子集性质)
1. 对于任意集合 $A$，$\emptyset \subseteq A$
2. 对于任意集合 $A$，$A \subseteq A$
3. 如果 $A \subseteq B$ 且 $B \subseteq C$，则 $A \subseteq C$

**证明**
1. 对于任意 $x$，如果 $x \in \emptyset$，则 $x \in A$（因为 $x \in \emptyset$ 为假，所以整个蕴含为真）
2. 对于任意 $x$，如果 $x \in A$，则 $x \in A$（显然成立）
3. 对于任意 $x$，如果 $x \in A$，则 $x \in B$（因为 $A \subseteq B$），如果 $x \in B$，则 $x \in C$（因为 $B \subseteq C$），因此如果 $x \in A$，则 $x \in C$

### 1.3 幂集

**定义 1.3.1** (幂集) 集合 $A$ 的幂集是 $A$ 的所有子集组成的集合：
$$\mathcal{P}(A) = \{B : B \subseteq A\}$$

**定理 1.3.1** (幂集基数) 如果 $|A| = n$，则 $|\mathcal{P}(A)| = 2^n$。

**证明** 使用数学归纳法：
- 基础情况：$n = 0$，$A = \emptyset$，$\mathcal{P}(\emptyset) = \{\emptyset\}$，$|\mathcal{P}(\emptyset)| = 1 = 2^0$
- 归纳假设：假设对于 $|A| = k$，$|\mathcal{P}(A)| = 2^k$
- 归纳步骤：设 $|A| = k + 1$，取 $a \in A$，则 $\mathcal{P}(A) = \mathcal{P}(A \setminus \{a\}) \cup \{B \cup \{a\} : B \in \mathcal{P}(A \setminus \{a\})\}$，因此 $|\mathcal{P}(A)| = 2^k + 2^k = 2^{k+1}$

## 2. 集合运算

### 2.1 基本运算

**定义 2.1.1** (并集) 集合 $A$ 和 $B$ 的并集是包含 $A$ 和 $B$ 中所有元素的集合：
$$A \cup B = \{x : x \in A \lor x \in B\}$$

**定义 2.1.2** (交集) 集合 $A$ 和 $B$ 的交集是同时属于 $A$ 和 $B$ 的元素组成的集合：
$$A \cap B = \{x : x \in A \land x \in B\}$$

**定义 2.1.3** (差集) 集合 $A$ 和 $B$ 的差集是属于 $A$ 但不属于 $B$ 的元素组成的集合：
$$A \setminus B = \{x : x \in A \land x \notin B\}$$

**定义 2.1.4** (对称差) 集合 $A$ 和 $B$ 的对称差是只属于其中一个集合的元素组成的集合：
$$A \triangle B = (A \setminus B) \cup (B \setminus A)$$

### 2.2 运算性质

**定理 2.2.1** (并集性质)
1. 交换律：$A \cup B = B \cup A$
2. 结合律：$(A \cup B) \cup C = A \cup (B \cup C)$
3. 幂等律：$A \cup A = A$
4. 单位元：$A \cup \emptyset = A$

**证明**
1. 交换律：$\forall x(x \in A \cup B \leftrightarrow x \in A \lor x \in B \leftrightarrow x \in B \lor x \in A \leftrightarrow x \in B \cup A)$
2. 结合律：$\forall x(x \in (A \cup B) \cup C \leftrightarrow (x \in A \lor x \in B) \lor x \in C \leftrightarrow x \in A \lor (x \in B \lor x \in C) \leftrightarrow x \in A \cup (B \cup C))$
3. 幂等律：$\forall x(x \in A \cup A \leftrightarrow x \in A \lor x \in A \leftrightarrow x \in A)$
4. 单位元：$\forall x(x \in A \cup \emptyset \leftrightarrow x \in A \lor x \in \emptyset \leftrightarrow x \in A)$

**定理 2.2.2** (德摩根律) 对于任意集合 $A$、$B$ 和全集 $U$：
1. $(A \cup B)^c = A^c \cap B^c$
2. $(A \cap B)^c = A^c \cup B^c$

**证明**
1. $\forall x(x \in (A \cup B)^c \leftrightarrow x \notin A \cup B \leftrightarrow \neg(x \in A \lor x \in B) \leftrightarrow x \notin A \land x \notin B \leftrightarrow x \in A^c \land x \in B^c \leftrightarrow x \in A^c \cap B^c)$
2. $\forall x(x \in (A \cap B)^c \leftrightarrow x \notin A \cap B \leftrightarrow \neg(x \in A \land x \in B) \leftrightarrow x \notin A \lor x \notin B \leftrightarrow x \in A^c \lor x \in B^c \leftrightarrow x \in A^c \cup B^c)$

### 2.3 笛卡尔积

**定义 2.3.1** (有序对) 有序对 $(a, b)$ 定义为 $\{\{a\}, \{a, b\}\}$。

**定义 2.3.2** (笛卡尔积) 集合 $A$ 和 $B$ 的笛卡尔积是所有有序对 $(a, b)$ 组成的集合，其中 $a \in A$，$b \in B$：
$$A \times B = \{(a, b) : a \in A \land b \in B\}$$

**定理 2.3.1** (笛卡尔积基数) 如果 $|A| = m$，$|B| = n$，则 $|A \times B| = mn$。

**证明** 对于 $A$ 中的每个元素 $a$，都有 $n$ 个不同的有序对 $(a, b)$，其中 $b \in B$。因此总共有 $m \times n$ 个有序对。

## 3. 关系与函数

### 3.1 关系

**定义 3.1.1** (二元关系) 集合 $A$ 和 $B$ 之间的二元关系是 $A \times B$ 的子集。

**定义 3.1.2** (关系性质) 设 $R$ 是集合 $A$ 上的关系：
1. 自反性：$\forall x \in A(xRx)$
2. 对称性：$\forall x, y \in A(xRy \rightarrow yRx)$
3. 传递性：$\forall x, y, z \in A(xRy \land yRz \rightarrow xRz)$
4. 反对称性：$\forall x, y \in A(xRy \land yRx \rightarrow x = y)$

**定义 3.1.3** (等价关系) 满足自反性、对称性和传递性的关系称为等价关系。

**定义 3.1.4** (偏序关系) 满足自反性、反对称性和传递性的关系称为偏序关系。

### 3.2 函数

**定义 3.2.1** (函数) 函数 $f: A \rightarrow B$ 是满足以下条件的二元关系：
1. $\forall x \in A \exists y \in B((x, y) \in f)$（定义域覆盖）
2. $\forall x \in A \forall y_1, y_2 \in B((x, y_1) \in f \land (x, y_2) \in f \rightarrow y_1 = y_2)$（单值性）

**定义 3.2.2** (函数性质) 设 $f: A \rightarrow B$：
1. 单射：$\forall x_1, x_2 \in A(f(x_1) = f(x_2) \rightarrow x_1 = x_2)$
2. 满射：$\forall y \in B \exists x \in A(f(x) = y)$
3. 双射：既是单射又是满射

**定理 3.2.1** (函数基数) 如果 $f: A \rightarrow B$ 是双射，则 $|A| = |B|$。

**证明** 由于 $f$ 是双射，$A$ 中的每个元素都唯一对应 $B$ 中的一个元素，且 $B$ 中的每个元素都被对应到，因此 $A$ 和 $B$ 的元素个数相等。

## 4. 基数理论

### 4.1 基数定义

**定义 4.1.1** (基数) 集合 $A$ 的基数 $|A|$ 是 $A$ 中元素的个数。

**定义 4.1.2** (基数相等) 两个集合的基数相等，如果它们之间存在双射。

**定义 4.1.3** (基数比较) 集合 $A$ 的基数小于等于集合 $B$ 的基数，如果 $A$ 与 $B$ 的某个子集等势。

### 4.2 可数集

**定义 4.2.1** (可数集) 与自然数集 $\mathbb{N}$ 等势的集合称为可数集。

**定理 4.2.1** (可数集性质)
1. 可数集的子集是可数的或有限的
2. 可数集的并集是可数的
3. 可数集的笛卡尔积是可数的

**证明**
1. 设 $A$ 是可数集，$B \subseteq A$。如果 $B$ 是有限的，则结论成立。如果 $B$ 是无限的，则可以通过删除 $A$ 中不属于 $B$ 的元素得到 $B$ 与 $\mathbb{N}$ 的双射。
2. 设 $A_1, A_2, \ldots$ 是可数集。可以构造一个双射 $f: \mathbb{N} \rightarrow \bigcup_{i=1}^{\infty} A_i$。
3. 设 $A$ 和 $B$ 是可数集。可以构造一个双射 $f: \mathbb{N} \times \mathbb{N} \rightarrow A \times B$。

### 4.3 不可数集

**定理 4.3.1** (康托尔定理) 对于任意集合 $A$，$|A| < |\mathcal{P}(A)|$。

**证明** 假设存在双射 $f: A \rightarrow \mathcal{P}(A)$。定义 $B = \{x \in A : x \notin f(x)\}$。由于 $f$ 是满射，存在 $a \in A$ 使得 $f(a) = B$。如果 $a \in B$，则 $a \notin f(a) = B$，矛盾。如果 $a \notin B$，则 $a \in f(a) = B$，矛盾。因此不存在这样的双射。

**推论 4.3.1** 实数集 $\mathbb{R}$ 是不可数的。

**证明** 可以证明 $|\mathbb{R}| = |\mathcal{P}(\mathbb{N})|$，而 $|\mathbb{N}| < |\mathcal{P}(\mathbb{N})|$，因此 $\mathbb{R}$ 是不可数的。

## 5. 序数理论

### 5.1 良序集

**定义 5.1.1** (良序集) 集合 $A$ 上的全序关系 $<$ 是良序，如果 $A$ 的每个非空子集都有最小元素。

**定义 5.1.2** (序数) 序数是良序集的序型。

**定理 5.1.1** (序数性质) 每个序数都是传递集，且在其成员关系下是良序的。

### 5.2 超限归纳

**定理 5.2.1** (超限归纳原理) 设 $P$ 是序数的性质，如果：
1. $P(0)$ 成立
2. 对于任意序数 $\alpha$，如果对于所有 $\beta < \alpha$ 都有 $P(\beta)$，则 $P(\alpha)$ 成立

那么对于所有序数 $\alpha$，$P(\alpha)$ 都成立。

## 6. 公理化集合论

### 6.1 ZFC公理系统

**公理 6.1.1** (外延公理) $\forall A \forall B [\forall x(x \in A \leftrightarrow x \in B) \rightarrow A = B]$

**公理 6.1.2** (空集公理) $\exists \emptyset \forall x(x \notin \emptyset)$

**公理 6.1.3** (配对公理) $\forall x \forall y \exists z \forall w(w \in z \leftrightarrow w = x \lor w = y)$

**公理 6.1.4** (并集公理) $\forall F \exists A \forall x(x \in A \leftrightarrow \exists B(B \in F \land x \in B))$

**公理 6.1.5** (幂集公理) $\forall A \exists P \forall B(B \in P \leftrightarrow B \subseteq A)$

**公理 6.1.6** (无穷公理) $\exists A(\emptyset \in A \land \forall x(x \in A \rightarrow x \cup \{x\} \in A))$

**公理 6.1.7** (替换公理) 对于任意公式 $\phi(x, y)$，如果 $\forall x \forall y \forall z(\phi(x, y) \land \phi(x, z) \rightarrow y = z)$，则 $\forall A \exists B \forall y(y \in B \leftrightarrow \exists x \in A \phi(x, y))$

**公理 6.1.8** (正则公理) $\forall A(A \neq \emptyset \rightarrow \exists x \in A(x \cap A = \emptyset))$

**公理 6.1.9** (选择公理) 对于任意非空集合族，存在选择函数。

### 6.2 一致性

**定理 6.2.1** (哥德尔不完备性) 如果ZFC是一致的，则ZFC不能证明自身的一致性。

## 7. 应用与扩展

### 7.1 在数学中的应用

集合论为现代数学提供了基础：
- 实分析中的测度论
- 拓扑学中的开集概念
- 代数学中的群、环、域
- 数论中的数集结构

### 7.2 在计算机科学中的应用

集合论在计算机科学中有广泛应用：
- 数据库理论中的关系模型
- 形式语言理论中的语言定义
- 算法分析中的复杂度理论
- 软件工程中的类型系统

### 7.3 在逻辑学中的应用

集合论为逻辑学提供了语义基础：
- 模型论中的解释域
- 证明论中的构造
- 递归论中的可计算性
- 范畴论中的对象和态射

---

**参考文献**

1. Halmos, P. R. (1974). *Naive Set Theory*. Springer-Verlag.
2. Jech, T. (2003). *Set Theory*. Springer-Verlag.
3. Kunen, K. (1980). *Set Theory: An Introduction to Independence Proofs*. North-Holland.
4. Enderton, H. B. (1977). *Elements of Set Theory*. Academic Press. 