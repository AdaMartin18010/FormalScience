# 集合论基础 (Set Theory Foundation)

## 🎯 **概述**

集合论是现代数学的基础语言，为所有数学分支提供统一的表达框架。本文档构建了严格的公理化集合论体系，从朴素集合论到公理集合论，为整个数学体系提供坚实基础。

## 📚 **目录**

1. [基本概念](#1-基本概念)
2. [朴素集合论](#2-朴素集合论)
3. [公理集合论](#3-公理集合论)
4. [集合运算](#4-集合运算)
5. [关系与函数](#5-关系与函数)
6. [基数与序数](#6-基数与序数)
7. [选择公理](#7-选择公理)
8. [构造性集合论](#8-构造性集合论)

## 1. 基本概念

### 1.1 集合的定义

**定义 1.1 (集合)**
集合是数学的基本概念，表示某些对象的汇集。

**形式化定义：**
$$\text{Set}(A) \equiv \forall x (x \in A \lor x \notin A)$$

其中：
- $A$ 是集合
- $x \in A$ 表示"x属于A"
- $x \notin A$ 表示"x不属于A"

**定义 1.2 (元素)**
元素是集合的成员，满足属于关系。

**形式化定义：**
$$\text{Element}(x, A) \equiv x \in A$$

### 1.2 集合的基本关系

**定义 1.3 (集合关系)**
集合之间的基本关系包括：

1. **相等关系**：$A = B \equiv \forall x (x \in A \leftrightarrow x \in B)$
2. **包含关系**：$A \subseteq B \equiv \forall x (x \in A \rightarrow x \in B)$
3. **真包含关系**：$A \subset B \equiv A \subseteq B \land A \neq B$

**定理 1.1 (集合关系的基本性质)**
集合关系满足以下基本性质：

1. **自反性**：$\forall A (A = A)$
2. **对称性**：$\forall A \forall B (A = B \rightarrow B = A)$
3. **传递性**：$\forall A \forall B \forall C ((A = B \land B = C) \rightarrow A = C)$

**证明：**
1. **自反性证明**：
   - 根据定义，$A = A \equiv \forall x (x \in A \leftrightarrow x \in A)$
   - 这是逻辑重言式，因此 $\forall A (A = A)$

2. **对称性证明**：
   - 假设 $A = B$
   - 根据定义，$\forall x (x \in A \leftrightarrow x \in B)$
   - 等价于 $\forall x (x \in B \leftrightarrow x \in A)$
   - 因此 $B = A$

3. **传递性证明**：
   - 假设 $A = B \land B = C$
   - 根据定义，$\forall x (x \in A \leftrightarrow x \in B)$ 和 $\forall x (x \in B \leftrightarrow x \in C)$
   - 因此 $\forall x (x \in A \leftrightarrow x \in C)$
   - 所以 $A = C$

## 2. 朴素集合论

### 2.1 朴素集合论公理

**公理 2.1 (外延公理)**
两个集合相等当且仅当它们包含相同的元素。

**形式化表达：**
$$\forall A \forall B (A = B \leftrightarrow \forall x (x \in A \leftrightarrow x \in B))$$

**公理 2.2 (概括公理)**
对于任意性质P，存在集合包含所有满足P的对象。

**形式化表达：**
$$\exists A \forall x (x \in A \leftrightarrow P(x))$$

**定理 2.1 (罗素悖论)**
朴素集合论存在悖论。

**证明：**
- 考虑性质 $R(x) \equiv x \notin x$
- 根据概括公理，存在集合 $R = \{x : x \notin x\}$
- 问：$R \in R$ 吗？
- 如果 $R \in R$，则 $R \notin R$（矛盾）
- 如果 $R \notin R$，则 $R \in R$（矛盾）
- 因此朴素集合论不一致

### 2.2 朴素集合论的局限性

**定理 2.2 (朴素集合论的不一致性)**
朴素集合论是不一致的。

**证明：**
- 罗素悖论表明朴素集合论存在矛盾
- 任何包含矛盾的形式系统都是不一致的
- 因此朴素集合论不一致

## 3. 公理集合论

### 3.1 ZFC公理系统

**公理 3.1 (外延公理)**
$$\forall A \forall B (A = B \leftrightarrow \forall x (x \in A \leftrightarrow x \in B))$$

**公理 3.2 (空集公理)**
存在一个不包含任何元素的集合。

**形式化表达：**
$$\exists A \forall x (x \notin A)$$

**定义 3.1 (空集)**
空集是唯一的不包含任何元素的集合，记作 $\emptyset$。

**形式化定义：**
$$\emptyset = \{x : x \neq x\}$$

**公理 3.3 (配对公理)**
对于任意两个集合，存在包含它们的集合。

**形式化表达：**
$$\forall A \forall B \exists C \forall x (x \in C \leftrightarrow x = A \lor x = B)$$

**定义 3.2 (无序对)**
集合A和B的无序对记作 $\{A, B\}$。

**形式化定义：**
$$\{A, B\} = \{x : x = A \lor x = B\}$$

**公理 3.4 (并集公理)**
对于任意集合族，存在包含所有成员元素的集合。

**形式化表达：**
$$\forall F \exists A \forall x (x \in A \leftrightarrow \exists B (B \in F \land x \in B))$$

**定义 3.3 (并集)**
集合族F的并集记作 $\bigcup F$。

**形式化定义：**
$$\bigcup F = \{x : \exists B (B \in F \land x \in B)\}$$

**公理 3.5 (幂集公理)**
对于任意集合，存在包含其所有子集的集合。

**形式化表达：**
$$\forall A \exists B \forall x (x \in B \leftrightarrow x \subseteq A)$$

**定义 3.4 (幂集)**
集合A的幂集记作 $\mathcal{P}(A)$。

**形式化定义：**
$$\mathcal{P}(A) = \{x : x \subseteq A\}$$

### 3.2 分离公理模式

**公理 3.6 (分离公理模式)**
对于任意集合A和性质P，存在A的子集包含所有满足P的元素。

**形式化表达：**
$$\forall A \exists B \forall x (x \in B \leftrightarrow x \in A \land P(x))$$

**定义 3.5 (分离)**
从集合A中分离出满足性质P的元素，记作 $\{x \in A : P(x)\}$。

**形式化定义：**
$$\{x \in A : P(x)\} = \{x : x \in A \land P(x)\}$$

### 3.3 无穷公理

**公理 3.7 (无穷公理)**
存在一个归纳集。

**形式化表达：**
$$\exists A (\emptyset \in A \land \forall x (x \in A \rightarrow x \cup \{x\} \in A))$$

**定义 3.6 (归纳集)**
集合A是归纳集，如果：
1. $\emptyset \in A$
2. $\forall x (x \in A \rightarrow x \cup \{x\} \in A)$

**定理 3.1 (自然数的存在性)**
存在自然数集。

**证明：**
- 根据无穷公理，存在归纳集A
- 定义自然数集为所有归纳集的交集
- $\mathbb{N} = \bigcap \{A : A \text{ 是归纳集}\}$

## 4. 集合运算

### 4.1 基本运算

**定义 4.1 (并集)**
集合A和B的并集记作 $A \cup B$。

**形式化定义：**
$$A \cup B = \{x : x \in A \lor x \in B\}$$

**定义 4.2 (交集)**
集合A和B的交集记作 $A \cap B$。

**形式化定义：**
$$A \cap B = \{x : x \in A \land x \in B\}$$

**定义 4.3 (差集)**
集合A和B的差集记作 $A \setminus B$。

**形式化定义：**
$$A \setminus B = \{x : x \in A \land x \notin B\}$$

**定义 4.4 (对称差)**
集合A和B的对称差记作 $A \triangle B$。

**形式化定义：**
$$A \triangle B = (A \setminus B) \cup (B \setminus A)$$

### 4.2 运算性质

**定理 4.1 (并集的性质)**
并集运算满足以下性质：

1. **交换律**：$A \cup B = B \cup A$
2. **结合律**：$(A \cup B) \cup C = A \cup (B \cup C)$
3. **幂等律**：$A \cup A = A$
4. **单位元**：$A \cup \emptyset = A$

**证明：**
1. **交换律证明**：
   - $A \cup B = \{x : x \in A \lor x \in B\}$
   - $B \cup A = \{x : x \in B \lor x \in A\}$
   - 由于 $\lor$ 满足交换律，所以 $A \cup B = B \cup A$

2. **结合律证明**：
   - $(A \cup B) \cup C = \{x : (x \in A \lor x \in B) \lor x \in C\}$
   - $A \cup (B \cup C) = \{x : x \in A \lor (x \in B \lor x \in C)\}$
   - 由于 $\lor$ 满足结合律，所以 $(A \cup B) \cup C = A \cup (B \cup C)$

**定理 4.2 (交集的性质)**
交集运算满足以下性质：

1. **交换律**：$A \cap B = B \cap A$
2. **结合律**：$(A \cap B) \cap C = A \cap (B \cap C)$
3. **幂等律**：$A \cap A = A$
4. **单位元**：$A \cap U = A$（U是全集）

### 4.3 德摩根律

**定理 4.3 (德摩根律)**
对于任意集合A和B：

1. $(A \cup B)^c = A^c \cap B^c$
2. $(A \cap B)^c = A^c \cup B^c$

**证明：**
1. 第一个德摩根律：
   - $(A \cup B)^c = \{x : x \notin A \cup B\}$
   - $= \{x : \neg(x \in A \lor x \in B)\}$
   - $= \{x : x \notin A \land x \notin B\}$
   - $= A^c \cap B^c$

2. 第二个德摩根律：
   - $(A \cap B)^c = \{x : x \notin A \cap B\}$
   - $= \{x : \neg(x \in A \land x \in B)\}$
   - $= \{x : x \notin A \lor x \notin B\}$
   - $= A^c \cup B^c$

## 5. 关系与函数

### 5.1 有序对

**定义 5.1 (有序对)**
有序对(a,b)定义为 $\{\{a\}, \{a,b\}\}$。

**形式化定义：**
$$(a,b) = \{\{a\}, \{a,b\}\}$$

**定理 5.1 (有序对的性质)**
$(a,b) = (c,d)$ 当且仅当 $a = c$ 且 $b = d$。

**证明：**
- 充分性：如果 $a = c$ 且 $b = d$，则 $(a,b) = (c,d)$
- 必要性：假设 $(a,b) = (c,d)$
- 则 $\{\{a\}, \{a,b\}\} = \{\{c\}, \{c,d\}\}$
- 如果 $a = b$，则 $\{\{a\}\} = \{\{c\}, \{c,d\}\}$
- 因此 $\{c\} = \{a\}$ 且 $\{c,d\} = \{a\}$
- 所以 $c = a$ 且 $d = a = b$
- 如果 $a \neq b$，则 $\{a\} \neq \{a,b\}$
- 因此 $\{a\} = \{c\}$ 且 $\{a,b\} = \{c,d\}$
- 所以 $a = c$ 且 $b = d$

### 5.2 笛卡尔积

**定义 5.2 (笛卡尔积)**
集合A和B的笛卡尔积记作 $A \times B$。

**形式化定义：**
$$A \times B = \{(a,b) : a \in A \land b \in B\}$$

**定理 5.2 (笛卡尔积的性质)**
笛卡尔积满足以下性质：

1. $A \times \emptyset = \emptyset \times A = \emptyset$
2. $A \times (B \cup C) = (A \times B) \cup (A \times C)$
3. $A \times (B \cap C) = (A \times B) \cap (A \times C)$

### 5.3 关系

**定义 5.3 (关系)**
从集合A到集合B的关系是 $A \times B$ 的子集。

**形式化定义：**
$$R \subseteq A \times B$$

**定义 5.4 (关系的定义域和值域)**
关系R的定义域和值域分别为：

1. **定义域**：$\text{dom}(R) = \{a : \exists b ((a,b) \in R)\}$
2. **值域**：$\text{ran}(R) = \{b : \exists a ((a,b) \in R)\}$

### 5.4 函数

**定义 5.5 (函数)**
函数是从集合A到集合B的关系，满足单值性。

**形式化定义：**
$$\text{Function}(f, A, B) \equiv f \subseteq A \times B \land \forall a \in A \exists! b \in B ((a,b) \in f)$$

**定义 5.6 (函数的应用)**
函数f在a处的值记作 $f(a)$。

**形式化定义：**
$$f(a) = b \equiv (a,b) \in f$$

**定理 5.3 (函数的基本性质)**
函数满足以下基本性质：

1. **单值性**：$\forall a \forall b_1 \forall b_2 ((a,b_1) \in f \land (a,b_2) \in f \rightarrow b_1 = b_2)$
2. **定义域覆盖**：$\forall a \in \text{dom}(f) \exists b ((a,b) \in f)$

## 6. 基数与序数

### 6.1 等势

**定义 6.1 (等势)**
集合A和B等势，如果存在从A到B的双射。

**形式化定义：**
$$A \approx B \equiv \exists f (\text{Bijection}(f, A, B))$$

**定义 6.2 (双射)**
函数f是双射，如果它是单射且满射。

**形式化定义：**
$$\text{Bijection}(f, A, B) \equiv \text{Injection}(f, A, B) \land \text{Surjection}(f, A, B)$$

### 6.2 基数

**定义 6.3 (基数)**
集合A的基数是与A等势的所有集合的等价类。

**形式化定义：**
$$|A| = \{B : B \approx A\}$$

**定理 6.1 (基数比较)**
对于任意集合A和B，以下三种情况之一成立：

1. $|A| < |B|$
2. $|A| = |B|$
3. $|A| > |B|$

### 6.3 序数

**定义 6.4 (序数)**
序数是传递的良序集。

**形式化定义：**
$$\text{Ordinal}(\alpha) \equiv \text{Transitive}(\alpha) \land \text{WellOrdered}(\alpha, \in)$$

**定义 6.5 (传递集)**
集合A是传递的，如果其元素都是其子集。

**形式化定义：**
$$\text{Transitive}(A) \equiv \forall x \forall y (x \in y \land y \in A \rightarrow x \in A)$$

## 7. 选择公理

### 7.1 选择公理的表述

**公理 7.1 (选择公理)**
对于任意非空集合族，存在选择函数。

**形式化表达：**
$$\forall F (\emptyset \notin F \rightarrow \exists f (\text{Function}(f, F, \bigcup F) \land \forall A \in F (f(A) \in A)))$$

**定义 7.1 (选择函数)**
从集合族F到其并集的选择函数f满足：$\forall A \in F (f(A) \in A)$。

### 7.2 选择公理的等价形式

**定理 7.1 (佐恩引理)**
选择公理等价于佐恩引理。

**佐恩引理：** 每个偏序集都有极大链。

**定理 7.2 (良序定理)**
选择公理等价于良序定理。

**良序定理：** 每个集合都可以良序化。

## 8. 构造性集合论

### 8.1 直觉主义集合论

**公理 8.1 (直觉主义外延公理)**
$$\forall A \forall B (A = B \leftrightarrow \forall x (x \in A \leftrightarrow x \in B))$$

**公理 8.2 (直觉主义空集公理)**
$$\exists A \forall x \neg(x \in A)$$

### 8.2 构造性特征

**定义 8.1 (构造性存在)**
构造性存在要求明确构造对象。

**形式化定义：**
$$\exists x P(x) \equiv \text{可以构造} x \text{使得} P(x)$$

**定理 8.1 (构造性否定)**
在构造性数学中，$\neg \neg P$ 不等价于 $P$。

## 🔗 **相关链接**

- [逻辑基础](./../02_Logic/01_Logic_Foundation.md)
- [数系基础](./../03_Number_Systems/01_Number_Systems_Foundation.md)
- [函数基础](./../04_Functions/01_Functions_Foundation.md)
- [关系基础](./../05_Relations/01_Relations_Foundation.md)

## 📚 **参考文献**

1. Cantor, G. (1895). "Beiträge zur Begründung der transfiniten Mengenlehre". *Mathematische Annalen*.
2. Zermelo, E. (1908). "Untersuchungen über die Grundlagen der Mengenlehre I". *Mathematische Annalen*.
3. Fraenkel, A. (1922). "Zu den Grundlagen der Cantor-Zermeloschen Mengenlehre". *Mathematische Annalen*.
4. von Neumann, J. (1925). "Eine Axiomatisierung der Mengenlehre". *Journal für die reine und angewandte Mathematik*.
5. Gödel, K. (1940). *The Consistency of the Axiom of Choice and of the Generalized Continuum-Hypothesis with the Axioms of Set Theory*.

---

**注意**：本文档正在持续完善中，请关注更新。 