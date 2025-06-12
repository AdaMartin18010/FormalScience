# 简单类型λ演算 (Simply Typed Lambda Calculus)

## 目录

1. [语法定义](#1-语法定义)
2. [类型系统](#2-类型系统)
3. [类型推导](#3-类型推导)
4. [操作语义](#4-操作语义)
5. [类型安全性](#5-类型安全性)
6. [语义解释](#6-语义解释)
7. [扩展与变体](#7-扩展与变体)

## 1. 语法定义

### 1.1 类型语法

**定义 1.1.1** (类型) 类型按以下规则递归定义：

1. 基本类型：$o$ 是类型
2. 函数类型：如果 $\sigma$ 和 $\tau$ 是类型，则 $\sigma \rightarrow \tau$ 是类型

**定义 1.1.2** (类型上下文) 类型上下文 $\Gamma$ 是形如 $x_1 : \sigma_1, \ldots, x_n : \sigma_n$ 的有限序列，其中 $x_i$ 是变量，$\sigma_i$ 是类型。

**定义 1.1.3** (类型判断) 类型判断是形如 $\Gamma \vdash M : \sigma$ 的表达式，表示在上下文 $\Gamma$ 下，项 $M$ 具有类型 $\sigma$。

### 1.2 项语法

**定义 1.2.1** (项) 项按以下规则递归定义：

1. 变量：如果 $x$ 是变量，则 $x$ 是项
2. 抽象：如果 $M$ 是项，$x$ 是变量，$\sigma$ 是类型，则 $\lambda x : \sigma. M$ 是项
3. 应用：如果 $M$ 和 $N$ 是项，则 $MN$ 是项

**定义 1.2.2** (自由变量) 项 $M$ 的自由变量集 $FV(M)$ 按以下规则递归定义：

1. $FV(x) = \{x\}$
2. $FV(\lambda x : \sigma. M) = FV(M) \setminus \{x\}$
3. $FV(MN) = FV(M) \cup FV(N)$

**定义 1.2.3** (绑定变量) 在项 $\lambda x : \sigma. M$ 中，变量 $x$ 被绑定，$M$ 是绑定体。

## 2. 类型系统

### 2.1 类型推导规则

**定义 2.1.1** (类型推导系统) 简单类型λ演算的类型推导系统包含以下规则：

**变量规则**：
$$\frac{}{\Gamma, x : \sigma \vdash x : \sigma}$$

**抽象规则**：
$$\frac{\Gamma, x : \sigma \vdash M : \tau}{\Gamma \vdash \lambda x : \sigma. M : \sigma \rightarrow \tau}$$

**应用规则**：
$$\frac{\Gamma \vdash M : \sigma \rightarrow \tau \quad \Gamma \vdash N : \sigma}{\Gamma \vdash MN : \tau}$$

**弱化规则**：
$$\frac{\Gamma \vdash M : \sigma}{\Gamma, x : \tau \vdash M : \sigma}$$
其中 $x \notin \text{dom}(\Gamma)$

**交换规则**：
$$\frac{\Gamma, x : \sigma, y : \tau, \Delta \vdash M : \rho}{\Gamma, y : \tau, x : \sigma, \Delta \vdash M : \rho}$$

**收缩规则**：
$$\frac{\Gamma, x : \sigma, x : \sigma \vdash M : \tau}{\Gamma, x : \sigma \vdash M : \tau}$$

### 2.2 类型推导示例

**示例 2.2.1** 证明 $\vdash \lambda x : o. x : o \rightarrow o$

**证明**：

1. $x : o \vdash x : o$ (变量规则)
2. $\vdash \lambda x : o. x : o \rightarrow o$ (抽象规则，从1)

**示例 2.2.2** 证明 $\vdash (\lambda x : o. x)(\lambda y : o. y) : o \rightarrow o$

**证明**：

1. $x : o \vdash x : o$ (变量规则)
2. $\vdash \lambda x : o. x : o \rightarrow o$ (抽象规则，从1)
3. $y : o \vdash y : o$ (变量规则)
4. $\vdash \lambda y : o. y : o \rightarrow o$ (抽象规则，从3)
5. $\vdash (\lambda x : o. x)(\lambda y : o. y) : o \rightarrow o$ (应用规则，从2和4)

## 3. 类型推导

### 3.1 类型推导算法

**算法 3.1.1** (类型推导算法) 给定项 $M$ 和上下文 $\Gamma$，算法返回 $M$ 的类型（如果存在）。

**输入**：项 $M$，上下文 $\Gamma$
**输出**：类型 $\sigma$ 或失败

1. 如果 $M = x$，则：
   - 如果 $x : \sigma \in \Gamma$，返回 $\sigma$
   - 否则失败

2. 如果 $M = \lambda x : \sigma. N$，则：
   - 递归计算 $\Gamma, x : \sigma \vdash N : \tau$
   - 如果成功，返回 $\sigma \rightarrow \tau$
   - 否则失败

3. 如果 $M = NP$，则：
   - 递归计算 $\Gamma \vdash N : \rho$ 和 $\Gamma \vdash P : \sigma$
   - 如果 $\rho = \sigma \rightarrow \tau$，返回 $\tau$
   - 否则失败

**定理 3.1.1** (类型推导的确定性) 如果 $\Gamma \vdash M : \sigma$ 和 $\Gamma \vdash M : \tau$，则 $\sigma = \tau$。

**证明** 通过对项的结构归纳证明。

### 3.2 类型推导的复杂度

**定理 3.2.1** (类型推导的复杂度) 类型推导算法的时间复杂度是 $O(n^2)$，其中 $n$ 是项的大小。

**证明** 每个子项最多被访问一次，每次访问需要常数时间。

## 4. 操作语义

### 4.1 β归约

**定义 4.1.1** (β归约) β归约关系 $\rightarrow_\beta$ 是最小的满足以下条件的二元关系：

**β规则**：
$$(\lambda x : \sigma. M)N \rightarrow_\beta M[N/x]$$

**上下文规则**：

- 如果 $M \rightarrow_\beta M'$，则 $\lambda x : \sigma. M \rightarrow_\beta \lambda x : \sigma. M'$
- 如果 $M \rightarrow_\beta M'$，则 $MN \rightarrow_\beta M'N$
- 如果 $N \rightarrow_\beta N'$，则 $MN \rightarrow_\beta MN'$

**定义 4.1.2** (替换) 项 $M$ 中变量 $x$ 被项 $N$ 替换的结果 $M[N/x]$ 按以下规则递归定义：

1. $x[N/x] = N$
2. $y[N/x] = y$ 如果 $y \neq x$
3. $[\lambda y : \sigma. M](N/x) = \lambda y : \sigma. M[N/x]$ 如果 $y \neq x$ 且 $y \notin FV(N)$
4. $[M_1M_2](N/x) = M_1[N/x]M_2[N/x]$

**定义 4.1.3** (α等价) α等价关系 $\equiv_\alpha$ 是最小的满足以下条件的等价关系：

- $\lambda x : \sigma. M \equiv_\alpha \lambda y : \sigma. M[y/x]$ 如果 $y \notin FV(M)$

### 4.2 归约性质

**定理 4.2.1** (强正规化) 简单类型λ演算中的每个项都是强正规化的，即不存在无限归约序列。

**证明** 使用可约性方法：定义每个类型 $\sigma$ 上的可约性谓词 $R_\sigma$，然后证明每个类型正确的项都是可约的。

**定理 4.2.2** (丘奇-罗塞尔性质) 如果 $M \rightarrow_\beta^* N_1$ 和 $M \rightarrow_\beta^* N_2$，则存在 $N$ 使得 $N_1 \rightarrow_\beta^* N$ 和 $N_2 \rightarrow_\beta^* N$。

**证明** 通过证明β归约满足菱形性质。

## 5. 类型安全性

### 5.1 类型保持性

**定理 5.1.1** (类型保持性) 如果 $\Gamma \vdash M : \sigma$ 且 $M \rightarrow_\beta M'$，则 $\Gamma \vdash M' : \sigma$。

**证明** 通过对归约规则的结构归纳证明。

**引理 5.1.1** (替换引理) 如果 $\Gamma, x : \sigma \vdash M : \tau$ 且 $\Gamma \vdash N : \sigma$，则 $\Gamma \vdash M[N/x] : \tau$。

**证明** 通过对项 $M$ 的结构归纳证明。

### 5.2 进展性

**定理 5.2.1** (进展性) 如果 $\vdash M : \sigma$，则 $M$ 是值或者存在 $M'$ 使得 $M \rightarrow_\beta M'$。

**证明** 通过对类型推导的结构归纳证明。

**定义 5.2.1** (值) 值是形如 $\lambda x : \sigma. M$ 的项。

### 5.3 类型安全性总结

**定理 5.3.1** (类型安全性) 简单类型λ演算满足：

1. 类型保持性：归约保持类型
2. 进展性：类型正确的项要么是值，要么可以归约
3. 强正规化：不存在无限归约序列

## 6. 语义解释

### 6.1 集合论语义

**定义 6.1.1** (类型解释) 给定基本类型 $o$ 的解释 $D_o$，类型 $\sigma$ 的解释 $[\![\sigma]\!]$ 按以下规则递归定义：

1. $[\![o]\!] = D_o$
2. $[\![\sigma \rightarrow \tau]\!] = [\![\sigma]\!] \rightarrow [\![\tau]\!]$

**定义 6.1.2** (环境) 环境 $\rho$ 是从变量到域的映射。

**定义 6.1.3** (项解释) 项 $M$ 在环境 $\rho$ 下的解释 $[\![M]\!]_\rho$ 按以下规则递归定义：

1. $[\![x]\!]_\rho = \rho(x)$
2. $[\![\lambda x : \sigma. M]\!]_\rho = \lambda d \in [\![\sigma]\!]. [\![M]\!]_{\rho[x \mapsto d]}$
3. $[\![MN]\!]_\rho = [\![M]\!]_\rho([\![N]\!]_\rho)$

### 6.2 语义正确性

**定理 6.2.1** (语义正确性) 如果 $\Gamma \vdash M : \sigma$，则对于所有满足 $\Gamma$ 的环境 $\rho$，$[\![M]\!]_\rho \in [\![\sigma]\!]$。

**证明** 通过对类型推导的结构归纳证明。

## 7. 扩展与变体

### 7.1 产品类型

**定义 7.1.1** (产品类型) 如果 $\sigma$ 和 $\tau$ 是类型，则 $\sigma \times \tau$ 是类型。

**定义 7.1.2** (产品项) 产品项包括：

- 配对：如果 $M : \sigma$ 且 $N : \tau$，则 $\langle M, N \rangle : \sigma \times \tau$
- 投影：如果 $M : \sigma \times \tau$，则 $\pi_1(M) : \sigma$ 和 $\pi_2(M) : \tau$

### 7.2 和类型

**定义 7.2.1** (和类型) 如果 $\sigma$ 和 $\tau$ 是类型，则 $\sigma + \tau$ 是类型。

**定义 7.2.2** (和类型项) 和类型项包括：

- 注入：如果 $M : \sigma$，则 $\text{inl}(M) : \sigma + \tau$ 和 $\text{inr}(M) : \tau + \sigma$
- 情况分析：如果 $M : \sigma + \tau$，$N : \sigma \rightarrow \rho$，$P : \tau \rightarrow \rho$，则 $\text{case}(M, N, P) : \rho$

### 7.3 递归类型

**定义 7.3.1** (递归类型) 递归类型允许类型引用自身，如 $\mu \alpha. \sigma$。

**定义 7.3.2** (递归类型项) 递归类型项包括：

- 折叠：如果 $M : \sigma[\mu \alpha. \sigma/\alpha]$，则 $\text{fold}(M) : \mu \alpha. \sigma$
- 展开：如果 $M : \mu \alpha. \sigma$，则 $\text{unfold}(M) : \sigma[\mu \alpha. \sigma/\alpha]$

### 7.4 多态类型

**定义 7.4.1** (多态类型) 多态类型允许类型变量，如 $\forall \alpha. \sigma$。

**定义 7.4.2** (多态项) 多态项包括：

- 类型抽象：如果 $M : \sigma$ 且 $\alpha$ 不在 $M$ 中自由出现，则 $\Lambda \alpha. M : \forall \alpha. \sigma$
- 类型应用：如果 $M : \forall \alpha. \sigma$ 且 $\tau$ 是类型，则 $M[\tau] : \sigma[\tau/\alpha]$

---

**参考文献**

1. Barendregt, H. P. (1984). *The Lambda Calculus: Its Syntax and Semantics*. North-Holland.
2. Hindley, J. R., & Seldin, J. P. (2008). *Lambda-Calculus and Combinators: An Introduction*. Cambridge University Press.
3. Pierce, B. C. (2002). *Types and Programming Languages*. MIT Press.
4. Girard, J.-Y., Lafont, Y., & Taylor, P. (1989). *Proofs and Types*. Cambridge University Press.
