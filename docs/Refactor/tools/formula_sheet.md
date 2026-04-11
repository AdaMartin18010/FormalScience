# 公式速查表 📐

> 按学科分类的核心公式集合，所有公式均提供LaTeX源码

---

## 📑 目录

- [公式速查表 📐](#公式速查表-)
  - [📑 目录](#-目录)
  - [数学基础](#数学基础)
    - [集合论](#集合论)
    - [数论](#数论)
  - [数理逻辑](#数理逻辑)
    - [命题逻辑](#命题逻辑)
    - [谓词逻辑](#谓词逻辑)
    - [模态逻辑](#模态逻辑)
  - [离散数学](#离散数学)
    - [组合数学](#组合数学)
    - [图论](#图论)
  - [线性代数](#线性代数)
    - [矩阵运算](#矩阵运算)
    - [特征值与特征向量](#特征值与特征向量)
    - [向量空间](#向量空间)
  - [概率统计](#概率统计)
    - [概率基础](#概率基础)
    - [期望与方差](#期望与方差)
    - [常见分布](#常见分布)
  - [类型理论](#类型理论)
    - [简单类型](#简单类型)
    - [多态与依赖类型](#多态与依赖类型)
    - [类型判断](#类型判断)
  - [🔗 相关资源](#-相关资源)

---

## 数学基础

### 集合论

| 概念 | 公式 | LaTeX |
|-----|------|-------|
| 并集 | $A \cup B = \{x \mid x \in A \lor x \in B\}$ | `A \cup B = \{x \mid x \in A \lor x \in B\}` |
| 交集 | $A \cap B = \{x \mid x \in A \land x \in B\}$ | `A \cap B = \{x \mid x \in A \land x \in B\}` |
| 补集 | $A^c = \{x \mid x \notin A\}$ | `A^c = \{x \mid x \notin A\}` |
| 差集 | $A \setminus B = \{x \mid x \in A \land x \notin B\}$ | `A \setminus B = \{x \mid x \in A \land x \notin B\}` |
| 幂集 | $\mathcal{P}(A) = \{X \mid X \subseteq A\}$ | `\mathcal{P}(A) = \{X \mid X \subseteq A\}` |

**德摩根定律**

```latex
(A \cup B)^c = A^c \cap B^c
(A \cap B)^c = A^c \cup B^c
```

### 数论

| 概念 | 公式 | LaTeX |
|-----|------|-------|
| 整除 | $a \mid b \Leftrightarrow \exists k \in \mathbb{Z}, b = ka$ | `a \mid b \Leftrightarrow \exists k \in \mathbb{Z}, b = ka` |
| 同余 | $a \equiv b \pmod{m} \Leftrightarrow m \mid (a-b)$ | `a \equiv b \pmod{m} \Leftrightarrow m \mid (a-b)` |
| 欧拉函数 | $\varphi(n) = n \prod_{p|n} \left(1-\frac{1}{p}\right)$ | `\varphi(n) = n \prod_{p|n} \left(1-\frac{1}{p}\right)` |
| 欧几里得算法 | $\gcd(a,b) = \gcd(b, a \bmod b)$ | `\gcd(a,b) = \gcd(b, a \bmod b)` |

---

## 数理逻辑

### 命题逻辑

| 运算符 | 真值表定义 | LaTeX |
|-------|-----------|-------|
| 合取 | $p \land q$ | `p \land q` |
| 析取 | $p \lor q$ | `p \lor q` |
| 蕴含 | $p \rightarrow q \equiv \neg p \lor q$ | `p \rightarrow q` |
| 等价 | $p \leftrightarrow q \equiv (p \rightarrow q) \land (q \rightarrow p)$ | `p \leftrightarrow q` |
| 否定 | $\neg p$ | `\neg p` |

**蕴含恒等式**

```latex
p \rightarrow q \equiv \neg p \lor q
p \rightarrow q \equiv \neg q \rightarrow \neg p \quad \text{(逆否命题)}
```

### 谓词逻辑

| 量词 | 含义 | LaTeX |
|-----|------|-------|
| 全称量词 | $\forall x \in D, P(x)$ | `\forall x \in D, P(x)` |
| 存在量词 | $\exists x \in D, P(x)$ | `\exists x \in D, P(x)` |
| 唯一存在 | $\exists! x \in D, P(x)$ | `\exists! x \in D, P(x)` |

**量词否定**

```latex
\neg \forall x P(x) \equiv \exists x \neg P(x)
\neg \exists x P(x) \equiv \forall x \neg P(x)
```

### 模态逻辑

| 算子 | 含义 | LaTeX |
|-----|------|-------|
| 必然 | $\Box \varphi$ | `\Box \varphi` |
| 可能 | $\Diamond \varphi$ | `\Diamond \varphi` |
| 对偶性 | $\Diamond \varphi \equiv \neg\Box\neg\varphi$ | `\Diamond \varphi \equiv \neg\Box\neg\varphi` |

---

## 离散数学

### 组合数学

| 概念 | 公式 | LaTeX |
|-----|------|-------|
| 排列 | $P(n,r) = \frac{n!}{(n-r)!}$ | `P(n,r) = \frac{n!}{(n-r)!}` |
| 组合 | $\binom{n}{r} = C(n,r) = \frac{n!}{r!(n-r)!}$ | `\binom{n}{r} = \frac{n!}{r!(n-r)!}` |
| 二项式定理 | $(x+y)^n = \sum_{k=0}^{n} \binom{n}{k} x^k y^{n-k}$ | `(x+y)^n = \sum_{k=0}^{n} \binom{n}{k} x^k y^{n-k}` |
| 容斥原理 | $\left|\bigcup_{i=1}^{n} A_i\right| = \sum_{\emptyset \neq I \subseteq [n]} (-1)^{|I|+1} \left|\bigcap_{i \in I} A_i\right|$ | 见上 |

### 图论

| 概念 | 公式 | LaTeX |
|-----|------|-------|
| 握手定理 | $\sum_{v \in V} \deg(v) = 2|E|$ | `\sum_{v \in V} \deg(v) = 2|E|` |
| 欧拉公式(平面图) | $v - e + f = 2$ | `v - e + f = 2` |
| 完全图边数 | $|E(K_n)| = \binom{n}{2} = \frac{n(n-1)}{2}$ | `\binom{n}{2} = \frac{n(n-1)}{2}` |
| 树边数 | $|E| = |V| - 1$ | `|E| = |V| - 1` |

---

## 线性代数

### 矩阵运算

| 概念 | 公式 | LaTeX |
|-----|------|-------|
| 矩阵乘法 | $(AB)_{ij} = \sum_{k=1}^{n} a_{ik} b_{kj}$ | `(AB)_{ij} = \sum_{k=1}^{n} a_{ik} b_{kj}` |
| 转置 | $(A^T)_{ij} = A_{ji}$ | `(A^T)_{ij} = A_{ji}` |
| 逆矩阵 | $A^{-1} = \frac{1}{\det(A)} \text{adj}(A)$ | `A^{-1} = \frac{1}{\det(A)} \text{adj}(A)` |
| 行列式(2×2) | $\begin{vmatrix} a & b \\ c & d \end{vmatrix} = ad - bc$ | `\begin{vmatrix} a & b \\ c & d \end{vmatrix} = ad - bc` |

### 特征值与特征向量

```latex
A\mathbf{v} = \lambda\mathbf{v}
\det(A - \lambda I) = 0 \quad \text{(特征方程)}
```

**迹与行列式**

```latex
\text{tr}(A) = \sum_{i=1}^{n} \lambda_i
\det(A) = \prod_{i=1}^{n} \lambda_i
```

### 向量空间

| 概念 | 公式 | LaTeX |
|-----|------|-------|
| 内积 | $\langle \mathbf{u}, \mathbf{v} \rangle = \sum_{i=1}^{n} u_i v_i$ | `\langle \mathbf{u}, \mathbf{v} \rangle = \sum_{i=1}^{n} u_i v_i` |
| 范数 | $\|\mathbf{v}\| = \sqrt{\langle \mathbf{v}, \mathbf{v} \rangle}$ | `\|\mathbf{v}\| = \sqrt{\langle \mathbf{v}, \mathbf{v} \rangle}` |
| 柯西-施瓦茨 | $|\langle \mathbf{u}, \mathbf{v} \rangle| \leq \|\mathbf{u}\| \cdot \|\mathbf{v}\|$ | `|\langle \mathbf{u}, \mathbf{v} \rangle| \leq \|\mathbf{u}\| \cdot \|\mathbf{v}\|` |

---

## 概率统计

### 概率基础

| 概念 | 公式 | LaTeX |
|-----|------|-------|
| 条件概率 | $P(A|B) = \frac{P(A \cap B)}{P(B)}$ | `P(A|B) = \frac{P(A \cap B)}{P(B)}` |
| 贝叶斯定理 | $P(A|B) = \frac{P(B|A)P(A)}{P(B)}$ | `P(A|B) = \frac{P(B|A)P(A)}{P(B)}` |
| 全概率 | $P(A) = \sum_{i} P(A|B_i)P(B_i)$ | `P(A) = \sum_{i} P(A|B_i)P(B_i)` |
| 独立性 | $A \perp B \Leftrightarrow P(A \cap B) = P(A)P(B)$ | `P(A \cap B) = P(A)P(B)` |

### 期望与方差

```latex
\mathbb{E}[X] = \sum_{x} x \cdot P(X=x) \quad \text{(离散)}
\mathbb{E}[X] = \int_{-\infty}^{\infty} x \cdot f(x) dx \quad \text{(连续)}

\text{Var}(X) = \mathbb{E}[(X - \mathbb{E}[X])^2] = \mathbb{E}[X^2] - (\mathbb{E}[X])^2

\sigma = \sqrt{\text{Var}(X)}
```

### 常见分布

| 分布 | PMF/PDF | 期望 | 方差 |
|-----|---------|------|------|
| 伯努利 | $P(X=k) = p^k(1-p)^{1-k}$ | $p$ | $p(1-p)$ |
| 二项 | $P(X=k) = \binom{n}{k}p^k(1-p)^{n-k}$ | $np$ | $np(1-p)$ |
| 泊松 | $P(X=k) = \frac{\lambda^k e^{-\lambda}}{k!}$ | $\lambda$ | $\lambda$ |
| 正态 | $f(x) = \frac{1}{\sqrt{2\pi\sigma^2}}e^{-\frac{(x-\mu)^2}{2\sigma^2}}$ | $\mu$ | $\sigma^2$ |
| 均匀 | $f(x) = \frac{1}{b-a}$ | $\frac{a+b}{2}$ | $\frac{(b-a)^2}{12}$ |

---

## 类型理论

### 简单类型

| 概念 | 表示 | LaTeX |
|-----|------|-------|
| 函数类型 | $\sigma \rightarrow \tau$ | `\sigma \rightarrow \tau` |
| 积类型 | $\sigma \times \tau$ | `\sigma \times \tau` |
| 和类型 | $\sigma + \tau$ | `\sigma + \tau` |
| 单元类型 | $\mathbf{1}$ 或 $()$ | `\mathbf{1}` |
| 空类型 | $\mathbf{0}$ 或 $\bot$ | `\mathbf{0}` |

### 多态与依赖类型

```latex
\text{多态}: \forall \alpha. \alpha \rightarrow \alpha
\text{依赖函数}: \Pi_{x:A} B(x)
\text{依赖对}: \Sigma_{x:A} B(x)
```

### 类型判断

```latex
\frac{\Gamma \vdash t : A \quad \Gamma, x : A \vdash u : B}{\Gamma \vdash \text{let } x = t \text{ in } u : B}(\text{LET})

\frac{\Gamma, x : A \vdash t : B}{\Gamma \vdash \lambda x.t : A \rightarrow B}(\rightarrow_i)

\frac{\Gamma \vdash t : A \rightarrow B \quad \Gamma \vdash u : A}{\Gamma \vdash tu : B}(\rightarrow_e)
```

---

## 🔗 相关资源

- [Lean策略手册](./lean_tactics.md) - 形式化证明
- [术语查询工具](./glossary_tool.md) - 数学术语
- [对比表集合](./comparison_tables.md) - 类型系统对比

---

_最后更新: 2026-04-11_
