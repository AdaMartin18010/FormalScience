# 07. 范畴论基础 (Category Theory)

## 目录

1. [基本概念](#1-基本概念)
2. [函子](#2-函子)
3. [自然变换](#3-自然变换)
4. [极限与余极限](#4-极限与余极限)
5. [伴随函子](#5-伴随函子)
6. [幺半范畴](#6-幺半范畴)
7. [高阶范畴](#7-高阶范畴)
8. [范畴公理化](#8-范畴公理化)
9. [应用与算法](#9-应用与算法)

## 1. 基本概念

### 1.1 范畴定义

**定义 1.1.1** (范畴)
范畴 $\mathcal{C}$ 包含：

1. 对象类 $\text{Ob}(\mathcal{C})$
2. 态射集 $\text{Hom}(A, B)$ 对任意对象 $A, B$
3. 复合运算 $\circ: \text{Hom}(B, C) \times \text{Hom}(A, B) \to \text{Hom}(A, C)$
4. 单位态射 $1_A \in \text{Hom}(A, A)$

满足：

- 结合律：$(f \circ g) \circ h = f \circ (g \circ h)$
- 单位律：$f \circ 1_A = f = 1_B \circ f$

**定义 1.1.2** (小范畴与大范畴)

- 小范畴：对象和态射都是集合
- 大范畴：对象或态射可能是真类

### 1.2 基本例子

**例子 1.2.1** (集合范畴)
$\text{Set}$：对象是集合，态射是函数。

**例子 1.2.2** (群范畴)
$\text{Grp}$：对象是群，态射是群同态。

**例子 1.2.3** (拓扑空间范畴)
$\text{Top}$：对象是拓扑空间，态射是连续映射。

### 1.3 特殊态射

**定义 1.3.1** (同构)
态射 $f: A \to B$ 是同构当且仅当存在 $g: B \to A$ 使得 $f \circ g = 1_B$ 且 $g \circ f = 1_A$。

**定义 1.3.2** (单态射)
态射 $f: A \to B$ 是单态射当且仅当对任意 $g, h: X \to A$，$f \circ g = f \circ h$ 蕴含 $g = h$。

**定义 1.3.3** (满态射)
态射 $f: A \to B$ 是满态射当且仅当对任意 $g, h: B \to X$，$g \circ f = h \circ f$ 蕴含 $g = h$。

## 2. 函子

### 2.1 函子定义

**定义 2.1.1** (协变函子)
协变函子 $F: \mathcal{C} \to \mathcal{D}$ 包含：

1. 对象映射 $F: \text{Ob}(\mathcal{C}) \to \text{Ob}(\mathcal{D})$
2. 态射映射 $F: \text{Hom}(A, B) \to \text{Hom}(F(A), F(B))$

满足：

- $F(1_A) = 1_{F(A)}$
- $F(f \circ g) = F(f) \circ F(g)$

**定义 2.1.2** (反变函子)
反变函子 $F: \mathcal{C} \to \mathcal{D}$ 满足 $F(f \circ g) = F(g) \circ F(f)$。

### 2.2 重要函子

**例子 2.2.1** (遗忘函子)
$U: \text{Grp} \to \text{Set}$ 将群映射到其底集。

**例子 2.2.2** (自由函子)
$F: \text{Set} \to \text{Grp}$ 将集合映射到其自由群。

**例子 2.2.3** (Hom函子)
$\text{Hom}(A, -): \mathcal{C} \to \text{Set}$ 将对象 $B$ 映射到 $\text{Hom}(A, B)$。

## 3. 自然变换

### 3.1 自然变换定义

**定义 3.1.1** (自然变换)
自然变换 $\alpha: F \to G$ 是态射族 $\{\alpha_A: F(A) \to G(A)\}_{A \in \mathcal{C}}$，使得对任意 $f: A \to B$，有：
$$G(f) \circ \alpha_A = \alpha_B \circ F(f)$$

**定义 3.1.2** (自然同构)
自然变换 $\alpha$ 是自然同构当且仅当每个 $\alpha_A$ 都是同构。

### 3.2 自然变换的例子

**例子 3.2.1** (对偶空间)
$V \mapsto V^*$ 和 $V \mapsto V^{**}$ 之间的自然变换。

**定理 3.2.1** (米田引理)
对任意函子 $F: \mathcal{C} \to \text{Set}$ 和对象 $A$：
$$\text{Nat}(\text{Hom}(A, -), F) \cong F(A)$$

## 4. 极限与余极限

### 4.1 极限

**定义 4.1.1** (锥)
图 $D: \mathcal{J} \to \mathcal{C}$ 的锥是对象 $C$ 和态射族 $\{\pi_j: C \to D(j)\}_{j \in \mathcal{J}}$。

**定义 4.1.2** (极限)
图 $D$ 的极限是通用锥 $(L, \{\lambda_j\})$，即对任意锥 $(C, \{\pi_j\})$，存在唯一态射 $f: C \to L$ 使得 $\pi_j = \lambda_j \circ f$。

### 4.2 特殊极限

**例子 4.2.1** (积)
离散图的极限称为积。

**例子 4.2.2** (等化子)
平行态射的等化子是极限。

**例子 4.2.3** (拉回)
正方形图的极限称为拉回。

### 4.3 余极限

**定义 4.3.1** (余极限)
图 $D$ 的余极限是通用余锥 $(L, \{\lambda_j\})$。

**例子 4.3.1** (余积)
离散图的余极限称为余积。

**例子 4.3.2** (余等化子)
平行态射的余等化子是余极限。

## 5. 伴随函子

### 5.1 伴随定义

**定义 5.1.1** (伴随)
函子 $F: \mathcal{C} \to \mathcal{D}$ 和 $G: \mathcal{D} \to \mathcal{C}$ 是伴随的，记作 $F \dashv G$，当且仅当存在自然同构：
$$\text{Hom}_{\mathcal{D}}(F(A), B) \cong \text{Hom}_{\mathcal{C}}(A, G(B))$$

**定理 5.1.1** (伴随的等价定义)
$F \dashv G$ 当且仅当存在单位 $\eta: 1_{\mathcal{C}} \to G \circ F$ 和余单位 $\varepsilon: F \circ G \to 1_{\mathcal{D}}$ 满足三角恒等式。

### 5.2 伴随的例子

**例子 5.2.1** (自由-遗忘伴随)
自由群函子 $F$ 和遗忘函子 $U$ 满足 $F \dashv U$。

**例子 5.2.2** (张量-Hom伴随)
在向量空间范畴中，张量积和Hom函子形成伴随。

## 6. 幺半范畴

### 6.1 幺半范畴定义

**定义 6.1.1** (幺半范畴)
幺半范畴是带有张量积 $\otimes$ 和单位对象 $I$ 的范畴，满足结合律和单位律。

**定义 6.1.2** (幺半函子)
幺半函子是保持张量积和单位对象的函子。

### 6.2 对称幺半范畴

**定义 6.2.1** (对称幺半范畴)
对称幺半范畴是带有自然同构 $A \otimes B \cong B \otimes A$ 的幺半范畴。

**例子 6.2.1** (向量空间)
向量空间的张量积构成对称幺半范畴。

## 7. 高阶范畴

### 7.1 2-范畴

**定义 7.1.1** (2-范畴)
2-范畴是带有2-态射的范畴，2-态射可以在两个1-态射之间复合。

**定义 7.1.2** (2-函子)
2-函子是保持2-态射的函子。

### 7.2 无穷范畴

**定义 7.2.1** (无穷范畴)
无穷范畴是带有任意高阶态射的范畴。

## 8. 范畴公理化

### 8.1 公理系统

**定义 8.1.1** (范畴公理)
范畴满足的代数公理。

**定理 8.1.1** (公理的独立性)
某些公理不能由其他公理推出。

## 9. 应用与算法

### 9.1 函数式编程

**例子 9.1.1** (Haskell中的范畴)

```haskell
-- Functor类型类
class Functor f where
    fmap :: (a -> b) -> f a -> f b

-- Monad类型类
class Monad m where
    return :: a -> m a
    (>>=) :: m a -> (a -> m b) -> m b
```

### 9.2 数据库理论

**例子 9.2.1** (关系代数)
关系数据库的查询语言可以看作范畴。

### 9.3 量子计算

**例子 9.3.1** (量子门)
量子门可以看作幺半范畴中的态射。

## 参考文献

1. Mac Lane, S. (1998). *Categories for the Working Mathematician*. Springer.
2. Awodey, S. (2010). *Category Theory*. Oxford University Press.
3. Riehl, E. (2017). *Category Theory in Context*. Dover Publications.
4. Leinster, T. (2014). *Basic Category Theory*. Cambridge University Press.
5. Barr, M., & Wells, C. (2005). *Toposes, Triples and Theories*. Springer.

## 交叉引用

- [01_Philosophical_Foundations/01_Epistemological_Foundations.md](../01_Philosophical_Foundations/01_Epistemological_Foundations.md) - 数学知识的认识论基础
- [02_Mathematical_Foundations/01_Set_Theory.md](01_Set_Theory.md) - 集合论基础
- [02_Mathematical_Foundations/03_Algebra.md](03_Algebra.md) - 代数基础
- [03_Logic_Theory/01_Propositional_Logic.md](../03_Logic_Theory/01_Propositional_Logic.md) - 逻辑推理基础
- [05_Type_Theory/01_Type_Theory_Foundations.md](../05_Type_Theory/01_Type_Theory_Foundations.md) - 类型理论基础
