# 集合论基础 (Set Theory Foundation)

## 目录

1. [基本概念](#1-基本概念)
2. [集合运算](#2-集合运算)
3. [关系与函数](#3-关系与函数)
4. [基数理论](#4-基数理论)
5. [序数理论](#5-序数理论)
6. [公理化集合论](#6-公理化集合论)
7. [应用与扩展](#7-应用与扩展)
8. [参考文献](#8-参考文献)

## 1. 基本概念

### 1.1 集合的定义

**定义 1.1.1 (集合)**
集合是满足以下公理的对象的汇集：

- **外延公理**：两个集合相等当且仅当它们包含相同的元素
- **概括公理**：对于任意性质 $P(x)$，存在集合 $\{x \mid P(x)\}$

**定义 1.1.2 (元素关系)**
如果 $a$ 是集合 $A$ 的元素，记作 $a \in A$。

**定义 1.1.3 (子集)**
集合 $A$ 是集合 $B$ 的子集，记作 $A \subseteq B$，当且仅当：
$$\forall x (x \in A \Rightarrow x \in B)$$

**定义 1.1.4 (真子集)**
集合 $A$ 是集合 $B$ 的真子集，记作 $A \subset B$，当且仅当：
$$A \subseteq B \land A \neq B$$

**定理 1.1.1 (子集的性质)**
对于任意集合 $A, B, C$：

1. $A \subseteq A$ (自反性)
2. $A \subseteq B \land B \subseteq C \Rightarrow A \subseteq C$ (传递性)
3. $A \subseteq B \land B \subseteq A \Rightarrow A = B$ (反对称性)

**证明：**

1. 自反性：$\forall x (x \in A \Rightarrow x \in A)$ 显然成立
2. 传递性：假设 $A \subseteq B$ 且 $B \subseteq C$，则对于任意 $x \in A$，有 $x \in B$，进而 $x \in C$，因此 $A \subseteq C$
3. 反对称性：由外延公理直接得到

### 1.2 空集与单元素集

**定义 1.2.1 (空集)**
空集是唯一不包含任何元素的集合，记作 $\emptyset$。

**公理 1.2.1 (空集公理)**
存在集合 $\emptyset$ 使得：
$$\forall x (x \notin \emptyset)$$

**定理 1.2.1 (空集的性质)**

1. 空集是任意集合的子集：$\forall A (\emptyset \subseteq A)$
2. 空集是唯一的

**证明：**

1. 对于任意集合 $A$，$\forall x (x \in \emptyset \Rightarrow x \in A)$ 为真，因为 $x \in \emptyset$ 为假
2. 假设存在两个空集 $\emptyset_1$ 和 $\emptyset_2$，则 $\emptyset_1 \subseteq \emptyset_2$ 且 $\emptyset_2 \subseteq \emptyset_1$，因此 $\emptyset_1 = \emptyset_2$

**定义 1.2.2 (单元素集)**
对于任意对象 $a$，单元素集 $\{a\}$ 定义为：
$$\{a\} = \{x \mid x = a\}$$

### 1.3 幂集

**定义 1.3.1 (幂集)**
集合 $A$ 的幂集是 $A$ 的所有子集构成的集合，记作 $\mathcal{P}(A)$：
$$\mathcal{P}(A) = \{X \mid X \subseteq A\}$$

**定理 1.3.1 (幂集的性质)**
对于任意集合 $A$：

1. $\emptyset \in \mathcal{P}(A)$
2. $A \in \mathcal{P}(A)$
3. 如果 $A$ 有 $n$ 个元素，则 $\mathcal{P}(A)$ 有 $2^n$ 个元素

**证明：**

1. 空集是任意集合的子集
2. 集合是自身的子集
3. 对于每个元素，可以选择包含或不包含，因此总数为 $2^n$

## 2. 集合运算

### 2.1 基本运算

**定义 2.1.1 (并集)**
集合 $A$ 和 $B$ 的并集定义为：
$$A \cup B = \{x \mid x \in A \lor x \in B\}$$

**定义 2.1.2 (交集)**
集合 $A$ 和 $B$ 的交集定义为：
$$A \cap B = \{x \mid x \in A \land x \in B\}$$

**定义 2.1.3 (差集)**
集合 $A$ 和 $B$ 的差集定义为：
$$A \setminus B = \{x \mid x \in A \land x \notin B\}$$

**定义 2.1.4 (对称差)**
集合 $A$ 和 $B$ 的对称差定义为：
$$A \triangle B = (A \setminus B) \cup (B \setminus A)$$

**定理 2.1.1 (集合运算的基本性质)**
对于任意集合 $A, B, C$：

1. **交换律**：
   - $A \cup B = B \cup A$
   - $A \cap B = B \cap A$

2. **结合律**：
   - $(A \cup B) \cup C = A \cup (B \cup C)$
   - $(A \cap B) \cap C = A \cap (B \cap C)$

3. **分配律**：
   - $A \cup (B \cap C) = (A \cup B) \cap (A \cup C)$
   - $A \cap (B \cup C) = (A \cap B) \cup (A \cap C)$

4. **德摩根律**：
   - $(A \cup B)^c = A^c \cap B^c$
   - $(A \cap B)^c = A^c \cup B^c$

**证明：** 通过元素关系直接验证。

### 2.2 笛卡尔积

**定义 2.2.1 (有序对)**
对于任意对象 $a, b$，有序对 $(a, b)$ 定义为：
$$(a, b) = \{\{a\}, \{a, b\}\}$$

**定理 2.2.1 (有序对的性质)**
$(a, b) = (c, d)$ 当且仅当 $a = c$ 且 $b = d$

**证明：** 通过集合相等的定义直接验证。

**定义 2.2.2 (笛卡尔积)**
集合 $A$ 和 $B$ 的笛卡尔积定义为：
$$A \times B = \{(a, b) \mid a \in A \land b \in B\}$$

**定理 2.2.2 (笛卡尔积的性质)**
对于任意集合 $A, B, C$：

1. $A \times \emptyset = \emptyset \times A = \emptyset$
2. $A \times (B \cup C) = (A \times B) \cup (A \times C)$
3. $A \times (B \cap C) = (A \times B) \cap (A \times C)$

## 3. 关系与函数

### 3.1 二元关系

**定义 3.1.1 (二元关系)**
集合 $A$ 和 $B$ 之间的二元关系是 $A \times B$ 的子集。

**定义 3.1.2 (关系的性质)**
设 $R$ 是集合 $A$ 上的二元关系：

1. **自反性**：$\forall x \in A (x R x)$
2. **对称性**：$\forall x, y \in A (x R y \Rightarrow y R x)$
3. **反对称性**：$\forall x, y \in A (x R y \land y R x \Rightarrow x = y)$
4. **传递性**：$\forall x, y, z \in A (x R y \land y R z \Rightarrow x R z)$

**定义 3.1.3 (等价关系)**
满足自反性、对称性和传递性的关系称为等价关系。

**定义 3.1.4 (等价类)**
设 $R$ 是集合 $A$ 上的等价关系，对于 $a \in A$，$a$ 的等价类定义为：
$$[a]_R = \{x \in A \mid x R a\}$$

**定理 3.1.1 (等价类的性质)**
设 $R$ 是集合 $A$ 上的等价关系：

1. $\forall a \in A (a \in [a]_R)$
2. $\forall a, b \in A ([a]_R = [b]_R \lor [a]_R \cap [b]_R = \emptyset)$
3. $\bigcup_{a \in A} [a]_R = A$

### 3.2 函数

**定义 3.2.1 (函数)**
函数 $f: A \rightarrow B$ 是满足以下条件的二元关系：

1. $\forall x \in A \exists y \in B ((x, y) \in f)$ (定义域覆盖)
2. $\forall x \in A \forall y_1, y_2 \in B ((x, y_1) \in f \land (x, y_2) \in f \Rightarrow y_1 = y_2)$ (单值性)

**定义 3.2.2 (函数的性质)**
设 $f: A \rightarrow B$ 是函数：

1. **单射**：$\forall x_1, x_2 \in A (f(x_1) = f(x_2) \Rightarrow x_1 = x_2)$
2. **满射**：$\forall y \in B \exists x \in A (f(x) = y)$
3. **双射**：既是单射又是满射

**定理 3.2.1 (函数复合)**
设 $f: A \rightarrow B$ 和 $g: B \rightarrow C$ 是函数，则复合函数 $g \circ f: A \rightarrow C$ 定义为：
$$(g \circ f)(x) = g(f(x))$$

## 4. 基数理论

### 4.1 等势

**定义 4.1.1 (等势)**
集合 $A$ 和 $B$ 等势，记作 $A \sim B$，当且仅当存在双射 $f: A \rightarrow B$。

**定理 4.1.1 (等势的性质)**
等势关系是等价关系。

**定义 4.1.2 (基数)**
集合 $A$ 的基数是 $A$ 的等势类的代表，记作 $|A|$。

### 4.2 可数集

**定义 4.2.1 (可数集)**
集合 $A$ 是可数的，当且仅当 $A \sim \mathbb{N}$ 或 $A$ 是有限集。

**定理 4.2.1 (可数集的性质)**

1. $\mathbb{N}$ 是可数的
2. $\mathbb{Z}$ 是可数的
3. $\mathbb{Q}$ 是可数的

**证明：**

1. 显然
2. 构造双射 $f: \mathbb{N} \rightarrow \mathbb{Z}$：
   $$f(n) = \begin{cases}
   \frac{n}{2} & \text{if } n \text{ is even} \\
   -\frac{n+1}{2} & \text{if } n \text{ is odd}
   \end{cases}$$
3. 通过康托尔对角线法构造双射

### 4.3 不可数集

**定理 4.3.1 (康托尔定理)**
$\mathbb{R}$ 是不可数的。

**证明：** 通过康托尔对角线法：
假设 $\mathbb{R}$ 是可数的，则存在双射 $f: \mathbb{N} \rightarrow \mathbb{R}$。
构造实数 $r$，其第 $n$ 位小数与 $f(n)$ 的第 $n$ 位小数不同。
则 $r \notin \text{ran}(f)$，矛盾。

**定理 4.3.2 (幂集基数)**
对于任意集合 $A$，$|\mathcal{P}(A)| > |A|$。

**证明：** 通过康托尔对角线法，构造 $\mathcal{P}(A)$ 的子集，使其不属于任何 $A$ 到 $\mathcal{P}(A)$ 的函数的像。

## 5. 序数理论

### 5.1 良序集

**定义 5.1.1 (偏序集)**
偏序集是带有偏序关系的集合。

**定义 5.1.2 (全序集)**
全序集是偏序集，其中任意两个元素都可比较。

**定义 5.1.3 (良序集)**
良序集是全序集，其中每个非空子集都有最小元素。

**定理 5.1.1 (良序定理)**
任意集合都可以良序化。

### 5.2 序数

**定义 5.2.1 (序数)**
序数是传递的良序集。

**定理 5.2.1 (序数的性质)**

1. 每个序数的元素都是序数
2. 序数的序数也是序数
3. 序数类构成良序类

## 6. 公理化集合论

### 6.1 ZFC公理系统

**公理 6.1.1 (外延公理)**
$$\forall x \forall y (\forall z (z \in x \leftrightarrow z \in y) \rightarrow x = y)$$

**公理 6.1.2 (空集公理)**
$$\exists x \forall y (y \notin x)$$

**公理 6.1.3 (配对公理)**
$$\forall x \forall y \exists z \forall w (w \in z \leftrightarrow w = x \lor w = y)$$

**公理 6.1.4 (并集公理)**
$$\forall x \exists y \forall z (z \in y \leftrightarrow \exists w (w \in x \land z \in w))$$

**公理 6.1.5 (幂集公理)**
$$\forall x \exists y \forall z (z \in y \leftrightarrow z \subseteq x)$$

**公理 6.1.6 (无穷公理)**
$$\exists x (\emptyset \in x \land \forall y (y \in x \rightarrow y \cup \{y\} \in x))$$

**公理 6.1.7 (替换公理)**
$$\forall x \forall y \forall z (\phi(x, y) \land \phi(x, z) \rightarrow y = z) \rightarrow \forall u \exists v \forall y (y \in v \leftrightarrow \exists x (x \in u \land \phi(x, y)))$$

**公理 6.1.8 (正则公理)**
$$\forall x (x \neq \emptyset \rightarrow \exists y (y \in x \land y \cap x = \emptyset))$$

**公理 6.1.9 (选择公理)**
$$\forall x (\emptyset \notin x \rightarrow \exists f (f: x \rightarrow \bigcup x \land \forall y \in x (f(y) \in y)))$$

### 6.2 公理系统的性质

**定理 6.2.1 (ZFC的一致性)**
如果ZFC一致，则无法在ZFC内证明ZFC的一致性。

**定理 6.2.2 (ZFC的完备性)**
ZFC是不完备的，存在在ZFC内既不可证明也不可反驳的命题。

## 7. 应用与扩展

### 7.1 数学应用

集合论为现代数学提供了基础语言：

- 代数结构：群、环、域
- 拓扑空间：开集、闭集、连续映射
- 分析学：实数、函数、极限

### 7.2 计算机科学应用

集合论在计算机科学中有广泛应用：

- 数据结构：集合、映射、关系
- 数据库：关系代数、SQL查询
- 形式语言：字母表、语言、自动机

### 7.3 逻辑学应用

集合论为逻辑学提供语义基础：

- 模型论：结构、解释、真值
- 证明论：证明、推导、一致性
- 递归论：可计算性、算法

## 8. 参考文献

1. Halmos, P. R. (1974). Naive Set Theory. Springer-Verlag.
2. Jech, T. (2003). Set Theory. Springer-Verlag.
3. Kunen, K. (1980). Set Theory: An Introduction to Independence Proofs. North-Holland.
4. Enderton, H. B. (1977). Elements of Set Theory. Academic Press.
5. Suppes, P. (1972). Axiomatic Set Theory. Dover Publications.
