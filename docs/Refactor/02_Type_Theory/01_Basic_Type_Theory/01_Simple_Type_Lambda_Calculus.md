# 简单类型λ演算 (Simply Typed Lambda Calculus)

## 目录

1. [语法定义](#1-语法定义)
2. [类型系统](#2-类型系统)
3. [类型推导](#3-类型推导)
4. [操作语义](#4-操作语义)
5. [类型安全性](#5-类型安全性)
6. [语义解释](#6-语义解释)
7. [扩展与变体](#7-扩展与变体)
8. [参考文献](#8-参考文献)

## 1. 语法定义

### 1.1 类型语法

**定义 1.1.1 (类型)**
类型按以下规则递归定义：

1. 基本类型 $o$ 是类型
2. 如果 $\tau_1$ 和 $\tau_2$ 是类型，则 $\tau_1 \rightarrow \tau_2$ 是类型

**定义 1.1.2 (类型层次)**
类型层次结构：

- **0级类型**：基本类型 $o$
- **1级类型**：形如 $o \rightarrow o$ 的类型
- **2级类型**：形如 $(o \rightarrow o) \rightarrow o$ 的类型
- **n级类型**：包含n个箭头符号的类型

**定义 1.1.3 (类型复杂度)**
类型 $\tau$ 的复杂度 $|\tau|$ 递归定义：

1. $|o| = 0$
2. $|\tau_1 \rightarrow \tau_2| = \max(|\tau_1|, |\tau_2|) + 1$

### 1.2 项语法

**定义 1.2.1 (项)**
项按以下规则递归定义：

1. 变量 $x$ 是项
2. 如果 $M$ 和 $N$ 是项，则 $(M N)$ 是项（应用）
3. 如果 $M$ 是项，$x$ 是变量，$\tau$ 是类型，则 $(\lambda x : \tau. M)$ 是项（抽象）

**定义 1.2.2 (自由变量)**
项 $M$ 的自由变量集 $FV(M)$ 递归定义：

1. $FV(x) = \{x\}$
2. $FV(M N) = FV(M) \cup FV(N)$
3. $FV(\lambda x : \tau. M) = FV(M) \setminus \{x\}$

**定义 1.2.3 (绑定变量)**
项 $M$ 的绑定变量集 $BV(M)$ 递归定义：

1. $BV(x) = \emptyset$
2. $BV(M N) = BV(M) \cup BV(N)$
3. $BV(\lambda x : \tau. M) = \{x\} \cup BV(M)$

**定义 1.2.4 (闭项)**
项 $M$ 是闭项，当且仅当 $FV(M) = \emptyset$。

### 1.3 替换

**定义 1.3.1 (替换)**
项 $M[N/x]$ 表示将项 $M$ 中所有自由出现的变量 $x$ 替换为项 $N$，递归定义：

1. $x[N/x] = N$
2. $y[N/x] = y$ （如果 $y \neq x$）
3. $[M_1 M_2](N/x) = (M_1[N/x])(M_2[N/x])$
4. $[\lambda y : \tau. M](N/x) = \lambda y : \tau. (M[N/x])$ （如果 $y \neq x$ 且 $y \notin FV(N)$）

**定义 1.3.2 (α等价)**
项 $M$ 和 $N$ α等价，记作 $M \equiv_\alpha N$，当且仅当它们可以通过重命名绑定变量相互转换。

**定理 1.3.1 (α等价的性质)**
α等价是等价关系。

## 2. 类型系统

### 2.1 类型上下文

**定义 2.1.1 (类型上下文)**
类型上下文是变量到类型的有限映射，记作 $\Gamma$。

-**定义 2.1.2 (上下文操作)**

1. 空上下文：$\emptyset$
2. 上下文扩展：$\Gamma, x : \tau$
3. 上下文包含：$x : \tau \in \Gamma$

**定义 2.1.3 (上下文域)**
上下文 $\Gamma$ 的域 $dom(\Gamma)$ 是 $\Gamma$ 中所有变量的集合。

### 2.2 类型推导规则

**定义 2.2.1 (类型推导关系)**
类型推导关系 $\Gamma \vdash M : \tau$ 表示在上下文 $\Gamma$ 下，项 $M$ 具有类型 $\tau$。

**类型推导规则**：

**变量规则**：
$$\frac{x : \tau \in \Gamma}{\Gamma \vdash x : \tau}$$

**抽象规则**：
$$\frac{\Gamma, x : \tau_1 \vdash M : \tau_2}{\Gamma \vdash \lambda x : \tau_1. M : \tau_1 \rightarrow \tau_2}$$

**应用规则**：
$$\frac{\Gamma \vdash M : \tau_1 \rightarrow \tau_2 \quad \Gamma \vdash N : \tau_1}{\Gamma \vdash M N : \tau_2}$$

**定理 2.2.1 (类型推导的唯一性)**
如果 $\Gamma \vdash M : \tau_1$ 且 $\Gamma \vdash M : \tau_2$，则 $\tau_1 = \tau_2$。

**证明：** 通过对项 $M$ 的结构归纳。

### 2.3 类型推导算法

**算法 2.3.1 (类型推导算法)**
输入：项 $M$ 和上下文 $\Gamma$
输出：类型 $\tau$ 或失败

```haskell
typeInfer :: Context -> Term -> Maybe Type
typeInfer gamma (Var x) = lookup x gamma
typeInfer gamma (App M N) = do
  tau1_arrow_tau2 <- typeInfer gamma M
  case tau1_arrow_tau2 of
    Arrow tau1 tau2 -> do
      tau1' <- typeInfer gamma N
      if tau1 == tau1' then return tau2 else Nothing
    _ -> Nothing
typeInfer gamma (Lam x tau1 M) = do
  tau2 <- typeInfer (extend gamma x tau1) M
  return (Arrow tau1 tau2)
```

**定理 2.3.1 (类型推导算法的正确性)**
算法 `typeInfer` 是正确的：

1. 如果 `typeInfer Γ M = Just τ`，则 $\Gamma \vdash M : \tau$
2. 如果 $\Gamma \vdash M : \tau$，则 `typeInfer Γ M = Just τ`

## 3. 类型推导

### 3.1 类型推导示例

**示例 3.1.1 (恒等函数)**
推导 $\lambda x : o. x : o \rightarrow o$：

1. $x : o \vdash x : o$ （变量规则）
2. $\vdash \lambda x : o. x : o \rightarrow o$ （抽象规则）

**示例 3.1.2 (应用)**
推导 $(\lambda x : o. x) y : o$，其中 $y : o$：

1. $y : o \vdash y : o$ （变量规则）
2. $y : o \vdash \lambda x : o. x : o \rightarrow o$ （恒等函数）
3. $y : o \vdash (\lambda x : o. x) y : o$ （应用规则）

**示例 3.1.3 (高阶函数)**
推导 $\lambda f : o \rightarrow o. \lambda x : o. f x : (o \rightarrow o) \rightarrow o \rightarrow o$：

1. $f : o \rightarrow o, x : o \vdash f : o \rightarrow o$ （变量规则）
2. $f : o \rightarrow o, x : o \vdash x : o$ （变量规则）
3. $f : o \rightarrow o, x : o \vdash f x : o$ （应用规则）
4. $f : o \rightarrow o \vdash \lambda x : o. f x : o \rightarrow o$ （抽象规则）
5. $\vdash \lambda f : o \rightarrow o. \lambda x : o. f x : (o \rightarrow o) \rightarrow o \rightarrow o$ （抽象规则）

### 3.2 类型推导的复杂度

**定理 3.2.1 (类型推导的复杂度)**
类型推导算法的时间复杂度是 $O(n^2)$，其中 $n$ 是项的大小。

**证明：** 每个子项最多被访问一次，每次访问需要常数时间。

## 4. 操作语义

### 4.1 β归约

**定义 4.1.1 (β归约)**
β归约关系 $\rightarrow_\beta$ 定义为：
$$(\lambda x : \tau. M) N \rightarrow_\beta M[N/x]$$

**定义 4.1.2 (β归约的闭包)**
β归约的闭包 $\rightarrow_\beta^*$ 是 $\rightarrow_\beta$ 的自反传递闭包。

**定义 4.1.3 (β范式)**
项 $M$ 是β范式，当且仅当不存在项 $N$ 使得 $M \rightarrow_\beta N$。

### 4.2 归约策略

**定义 4.2.1 (最左最外归约)**
最左最外归约策略总是归约最左最外的β可归约式。

**定义 4.2.2 (最左最内归约)**
最左最内归约策略总是归约最左最内的β可归约式。

**定理 4.2.1 (归约策略的等价性)**
如果项 $M$ 通过某种归约策略归约到范式 $N_1$，通过另一种归约策略归约到范式 $N_2$，则 $N_1 \equiv_\alpha N_2$。

### 4.3 强正规化

**定理 4.3.1 (强正规化定理)**
简单类型λ演算中的每个项都是强正规化的，即不存在无限归约序列。

**证明：** 通过类型复杂度进行归纳。

**定义 4.3.1 (归约长度)**
项 $M$ 的归约长度是 $M$ 归约到范式所需的最少步数。

**定理 4.3.2 (归约长度的上界)**
项 $M$ 的归约长度不超过 $|\tau|^n$，其中 $\tau$ 是 $M$ 的类型，$n$ 是 $M$ 的大小。

## 5. 类型安全性

### 5.1 类型保持性

**定理 5.1.1 (类型保持性)**
如果 $\Gamma \vdash M : \tau$ 且 $M \rightarrow_\beta N$，则 $\Gamma \vdash N : \tau$。

**证明：** 通过对归约规则的结构归纳。

### 5.2 进展性

**定理 5.2.1 (进展性)**
如果 $\vdash M : \tau$ 且 $M$ 不是范式，则存在项 $N$ 使得 $M \rightarrow_\beta N$。

**证明：** 通过对项 $M$ 的结构归纳。

### 5.3 类型安全性

**定理 5.3.1 (类型安全性)**
简单类型λ演算是类型安全的：

1. **类型保持性**：归约保持类型
2. **进展性**：良类型项要么是范式，要么可以归约
3. **强正规化**：所有归约序列都终止

## 6. 语义解释

### 6.1 集合论语义

**定义 6.1.1 (类型解释)**
类型 $\tau$ 在集合论语义下的解释 $\llbracket \tau \rrbracket$ 递归定义：

1. $\llbracket o \rrbracket = D$ （某个固定集合）
2. $\llbracket \tau_1 \rightarrow \tau_2 \rrbracket = \llbracket \tau_1 \rrbracket \rightarrow \llbracket \tau_2 \rrbracket$

**定义 6.1.2 (环境)**
环境是变量到语义对象的映射 $\rho : \text{Var} \rightarrow \bigcup_{\tau} \llbracket \tau \rrbracket$。

**定义 6.1.3 (项解释)**
项 $M$ 在环境 $\rho$ 下的解释 $\llbracket M \rrbracket_\rho$ 递归定义：

1. $\llbracket x \rrbracket_\rho = \rho(x)$
2. $\llbracket M N \rrbracket_\rho = \llbracket M \rrbracket_\rho(\llbracket N \rrbracket_\rho)$
3. $\llbracket \lambda x : \tau. M \rrbracket_\rho = \lambda d \in \llbracket \tau \rrbracket. \llbracket M \rrbracket_{\rho[x \mapsto d]}$

**定理 6.1.1 (语义正确性)**
如果 $\Gamma \vdash M : \tau$，则对于所有满足 $\Gamma$ 的环境 $\rho$，$\llbracket M \rrbracket_\rho \in \llbracket \tau \rrbracket$。

### 6.2 范畴论语义

**定义 6.2.1 (笛卡尔闭范畴)**
笛卡尔闭范畴是具有有限积和指数对象的范畴。

**定义 6.2.2 (简单类型λ演算的范畴论语义)**
在笛卡尔闭范畴 $\mathcal{C}$ 中：

1. 基本类型 $o$ 解释为对象 $O \in \mathcal{C}$
2. 函数类型 $\tau_1 \rightarrow \tau_2$ 解释为指数对象 $[\llbracket \tau_1 \rrbracket, \llbracket \tau_2 \rrbracket]$
3. 项解释为态射

**定理 6.2.1 (语义等价性)**
集合论语义和范畴论语义在适当条件下是等价的。

## 7. 扩展与变体

### 7.1 产品类型

**定义 7.1.1 (产品类型)**
扩展类型语法：
$$\tau ::= o \mid \tau_1 \rightarrow \tau_2 \mid \tau_1 \times \tau_2$$

**定义 7.1.2 (产品类型的项)**
扩展项语法：
$$M ::= x \mid \lambda x : \tau. M \mid M N \mid \langle M, N \rangle \mid \pi_1 M \mid \pi_2 M$$

**类型推导规则**：
$$\frac{\Gamma \vdash M : \tau_1 \quad \Gamma \vdash N : \tau_2}{\Gamma \vdash \langle M, N \rangle : \tau_1 \times \tau_2}$$

$$\frac{\Gamma \vdash M : \tau_1 \times \tau_2}{\Gamma \vdash \pi_1 M : \tau_1} \quad \frac{\Gamma \vdash M : \tau_1 \times \tau_2}{\Gamma \vdash \pi_2 M : \tau_2}$$

### 7.2 和类型

**定义 7.2.1 (和类型)**
扩展类型语法：
$$\tau ::= o \mid \tau_1 \rightarrow \tau_2 \mid \tau_1 + \tau_2$$

**定义 7.2.2 (和类型的项)**
扩展项语法：
$$M ::= x \mid \lambda x : \tau. M \mid M N \mid \text{inl}_{\tau_2} M \mid \text{inr}_{\tau_1} M \mid \text{case } M \text{ of } \text{inl } x \Rightarrow N_1 \mid \text{inr } y \Rightarrow N_2$$

### 7.3 递归类型

**定义 7.3.1 (递归类型)**
递归类型允许类型包含自身：
$$\mu \alpha. \tau$$

**定义 7.3.2 (递归类型的项)**
递归类型引入折叠和展开操作：
$$M ::= x \mid \lambda x : \tau. M \mid M N \mid \text{fold}_{\mu \alpha. \tau} M \mid \text{unfold}_{\mu \alpha. \tau} M$$

### 7.4 多态类型

**定义 7.4.1 (多态类型)**
多态类型允许类型参数：
$$\tau ::= o \mid \alpha \mid \tau_1 \rightarrow \tau_2 \mid \forall \alpha. \tau$$

**定义 7.4.2 (多态类型的项)**
多态类型引入类型抽象和应用：
$$M ::= x \mid \lambda x : \tau. M \mid M N \mid \Lambda \alpha. M \mid M[\tau]$$

## 8. 参考文献

1. Hindley, J. R., & Seldin, J. P. (2008). Lambda-Calculus and Combinators: An Introduction. Cambridge University Press.
2. Pierce, B. C. (2002). Types and Programming Languages. MIT Press.
3. Barendregt, H. P. (1984). The Lambda Calculus: Its Syntax and Semantics. North-Holland.
4. Girard, J. Y., Lafont, Y., & Taylor, P. (1989). Proofs and Types. Cambridge University Press.
5. Mitchell, J. C. (1996). Foundations for Programming Languages. MIT Press.
