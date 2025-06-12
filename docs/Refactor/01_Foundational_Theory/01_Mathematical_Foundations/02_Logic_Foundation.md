# 逻辑学基础 (Logic Foundation)

## 目录

1. [命题逻辑](#1-命题逻辑)
2. [谓词逻辑](#2-谓词逻辑)
3. [模态逻辑](#3-模态逻辑)
4. [证明理论](#4-证明理论)
5. [模型论](#5-模型论)
6. [非经典逻辑](#6-非经典逻辑)
7. [逻辑哲学](#7-逻辑哲学)
8. [参考文献](#8-参考文献)

## 1. 命题逻辑

### 1.1 语法

**定义 1.1.1 (命题变量)**
命题变量是原子命题，通常用 $p, q, r, \ldots$ 表示。

**定义 1.1.2 (命题公式)**
命题公式按以下规则递归定义：

1. 命题变量是公式
2. 如果 $\phi$ 是公式，则 $\neg \phi$ 是公式
3. 如果 $\phi$ 和 $\psi$ 是公式，则 $(\phi \land \psi)$、$(\phi \lor \psi)$、$(\phi \rightarrow \psi)$、$(\phi \leftrightarrow \psi)$ 是公式

**定义 1.1.3 (子公式)**
公式 $\phi$ 的子公式递归定义：

1. $\phi$ 是 $\phi$ 的子公式
2. 如果 $\neg \psi$ 是 $\phi$ 的子公式，则 $\psi$ 是 $\phi$ 的子公式
3. 如果 $(\psi_1 \circ \psi_2)$ 是 $\phi$ 的子公式，则 $\psi_1$ 和 $\psi_2$ 是 $\phi$ 的子公式

### 1.2 语义

**定义 1.2.1 (真值赋值)**
真值赋值是函数 $v: \text{Prop} \rightarrow \{0, 1\}$，其中 $\text{Prop}$ 是命题变量集。

**定义 1.2.2 (真值函数)**
真值函数 $\llbracket \cdot \rrbracket_v$ 递归定义：

1. $\llbracket p \rrbracket_v = v(p)$
2. $\llbracket \neg \phi \rrbracket_v = 1 - \llbracket \phi \rrbracket_v$
3. $\llbracket \phi \land \psi \rrbracket_v = \min(\llbracket \phi \rrbracket_v, \llbracket \psi \rrbracket_v)$
4. $\llbracket \phi \lor \psi \rrbracket_v = \max(\llbracket \phi \rrbracket_v, \llbracket \psi \rrbracket_v)$
5. $\llbracket \phi \rightarrow \psi \rrbracket_v = \max(1 - \llbracket \phi \rrbracket_v, \llbracket \psi \rrbracket_v)$
6. $\llbracket \phi \leftrightarrow \psi \rrbracket_v = 1 - |\llbracket \phi \rrbracket_v - \llbracket \psi \rrbracket_v|$

**定义 1.2.3 (满足关系)**
公式 $\phi$ 在真值赋值 $v$ 下为真，记作 $v \models \phi$，当且仅当 $\llbracket \phi \rrbracket_v = 1$。

**定义 1.2.4 (重言式)**
公式 $\phi$ 是重言式，当且仅当对于所有真值赋值 $v$，$v \models \phi$。

**定义 1.2.5 (矛盾式)**
公式 $\phi$ 是矛盾式，当且仅当对于所有真值赋值 $v$，$v \not\models \phi$。

### 1.3 推理系统

**定义 1.3.1 (自然演绎系统)**
自然演绎系统包含以下推理规则：

**假设规则**：
$$\frac{}{\Gamma, \phi \vdash \phi}$$

**否定引入**：
$$\frac{\Gamma, \phi \vdash \bot}{\Gamma \vdash \neg \phi}$$

**否定消除**：
$$\frac{\Gamma \vdash \phi \quad \Gamma \vdash \neg \phi}{\Gamma \vdash \bot}$$

**合取引入**：
$$\frac{\Gamma \vdash \phi \quad \Gamma \vdash \psi}{\Gamma \vdash \phi \land \psi}$$

**合取消除**：
$$\frac{\Gamma \vdash \phi \land \psi}{\Gamma \vdash \phi} \quad \frac{\Gamma \vdash \phi \land \psi}{\Gamma \vdash \psi}$$

**析取引入**：
$$\frac{\Gamma \vdash \phi}{\Gamma \vdash \phi \lor \psi} \quad \frac{\Gamma \vdash \psi}{\Gamma \vdash \phi \lor \psi}$$

**析取消除**：
$$\frac{\Gamma \vdash \phi \lor \psi \quad \Gamma, \phi \vdash \chi \quad \Gamma, \psi \vdash \chi}{\Gamma \vdash \chi}$$

**蕴含引入**：
$$\frac{\Gamma, \phi \vdash \psi}{\Gamma \vdash \phi \rightarrow \psi}$$

**蕴含消除**：
$$\frac{\Gamma \vdash \phi \rightarrow \psi \quad \Gamma \vdash \phi}{\Gamma \vdash \psi}$$

**定理 1.3.1 (可靠性)**
如果 $\Gamma \vdash \phi$，则 $\Gamma \models \phi$。

**定理 1.3.2 (完备性)**
如果 $\Gamma \models \phi$，则 $\Gamma \vdash \phi$。

### 1.4 范式

**定义 1.4.1 (析取范式)**
公式 $\phi$ 是析取范式，当且仅当它是形如 $\bigvee_{i=1}^n \bigwedge_{j=1}^{m_i} l_{ij}$ 的公式，其中 $l_{ij}$ 是文字（命题变量或其否定）。

**定义 1.4.2 (合取范式)**
公式 $\phi$ 是合取范式，当且仅当它是形如 $\bigwedge_{i=1}^n \bigvee_{j=1}^{m_i} l_{ij}$ 的公式，其中 $l_{ij}$ 是文字。

**定理 1.4.1 (范式存在性)**
每个命题公式都等价于某个析取范式和某个合取范式。

**证明：** 通过德摩根律和分配律进行等价变换。

## 2. 谓词逻辑

### 2.1 语法

**定义 2.1.1 (一阶语言)**
一阶语言 $\mathcal{L}$ 包含：

1. 变量集 $V = \{x, y, z, \ldots\}$
2. 常量集 $C = \{c, d, \ldots\}$
3. 函数符号集 $F = \{f, g, \ldots\}$
4. 谓词符号集 $P = \{P, Q, R, \ldots\}$
5. 逻辑连接词 $\neg, \land, \lor, \rightarrow, \leftrightarrow$
6. 量词 $\forall, \exists$
7. 等号 $=$

**定义 2.1.2 (项)**
项递归定义：

1. 变量和常量是项
2. 如果 $f$ 是 $n$ 元函数符号，$t_1, \ldots, t_n$ 是项，则 $f(t_1, \ldots, t_n)$ 是项

**定义 2.1.3 (原子公式)**
原子公式是形如 $P(t_1, \ldots, t_n)$ 或 $t_1 = t_2$ 的表达式，其中 $P$ 是 $n$ 元谓词符号，$t_1, \ldots, t_n$ 是项。

**定义 2.1.4 (公式)**
公式递归定义：

1. 原子公式是公式
2. 如果 $\phi$ 是公式，则 $\neg \phi$ 是公式
3. 如果 $\phi$ 和 $\psi$ 是公式，则 $(\phi \land \psi)$、$(\phi \lor \psi)$、$(\phi \rightarrow \psi)$、$(\phi \leftrightarrow \psi)$ 是公式
4. 如果 $\phi$ 是公式，$x$ 是变量，则 $\forall x \phi$ 和 $\exists x \phi$ 是公式

### 2.2 语义

**定义 2.2.1 (结构)**
一阶语言 $\mathcal{L}$ 的结构 $\mathcal{M}$ 是四元组 $(M, I, J, K)$，其中：

1. $M$ 是非空集合（论域）
2. $I$ 是常量解释函数
3. $J$ 是函数解释函数
4. $K$ 是谓词解释函数

**定义 2.2.2 (赋值)**
赋值是函数 $s: V \rightarrow M$。

**定义 2.2.3 (项解释)**
项 $t$ 在结构 $\mathcal{M}$ 和赋值 $s$ 下的解释 $\llbracket t \rrbracket_{\mathcal{M}, s}$ 递归定义：

1. $\llbracket x \rrbracket_{\mathcal{M}, s} = s(x)$
2. $\llbracket c \rrbracket_{\mathcal{M}, s} = I(c)$
3. $\llbracket f(t_1, \ldots, t_n) \rrbracket_{\mathcal{M}, s} = J(f)(\llbracket t_1 \rrbracket_{\mathcal{M}, s}, \ldots, \llbracket t_n \rrbracket_{\mathcal{M}, s})$

**定义 2.2.4 (满足关系)**
满足关系 $\mathcal{M}, s \models \phi$ 递归定义：

1. $\mathcal{M}, s \models P(t_1, \ldots, t_n)$ 当且仅当 $(\llbracket t_1 \rrbracket_{\mathcal{M}, s}, \ldots, \llbracket t_n \rrbracket_{\mathcal{M}, s}) \in K(P)$
2. $\mathcal{M}, s \models t_1 = t_2$ 当且仅当 $\llbracket t_1 \rrbracket_{\mathcal{M}, s} = \llbracket t_2 \rrbracket_{\mathcal{M}, s}$
3. $\mathcal{M}, s \models \neg \phi$ 当且仅当 $\mathcal{M}, s \not\models \phi$
4. $\mathcal{M}, s \models \phi \land \psi$ 当且仅当 $\mathcal{M}, s \models \phi$ 且 $\mathcal{M}, s \models \psi$
5. $\mathcal{M}, s \models \phi \lor \psi$ 当且仅当 $\mathcal{M}, s \models \phi$ 或 $\mathcal{M}, s \models \psi$
6. $\mathcal{M}, s \models \phi \rightarrow \psi$ 当且仅当 $\mathcal{M}, s \not\models \phi$ 或 $\mathcal{M}, s \models \psi$
7. $\mathcal{M}, s \models \forall x \phi$ 当且仅当对于所有 $a \in M$，$\mathcal{M}, s[x \mapsto a] \models \phi$
8. $\mathcal{M}, s \models \exists x \phi$ 当且仅当存在 $a \in M$，$\mathcal{M}, s[x \mapsto a] \models \phi$

### 2.3 推理系统

**定义 2.3.1 (谓词逻辑推理规则)**
除命题逻辑规则外，还包含：

**全称引入**：
$$\frac{\Gamma \vdash \phi}{\Gamma \vdash \forall x \phi} \quad \text{if } x \text{ is not free in } \Gamma$$

**全称消除**：
$$\frac{\Gamma \vdash \forall x \phi}{\Gamma \vdash \phi[t/x]} \quad \text{if } t \text{ is free for } x \text{ in } \phi$$

**存在引入**：
$$\frac{\Gamma \vdash \phi[t/x]}{\Gamma \vdash \exists x \phi} \quad \text{if } t \text{ is free for } x \text{ in } \phi$$

**存在消除**：
$$\frac{\Gamma \vdash \exists x \phi \quad \Gamma, \phi \vdash \psi}{\Gamma \vdash \psi} \quad \text{if } x \text{ is not free in } \Gamma \text{ or } \psi$$

**定理 2.3.1 (哥德尔完备性定理)**
一阶谓词逻辑是可靠且完备的。

## 3. 模态逻辑

### 3.1 基本模态逻辑

**定义 3.1.1 (模态语言)**
模态语言包含：

1. 命题变量集 $P = \{p, q, r, \ldots\}$
2. 逻辑连接词 $\neg, \land, \lor, \rightarrow, \leftrightarrow$
3. 模态算子 $\Box$（必然）和 $\Diamond$（可能）

**定义 3.1.2 (模态公式)**
模态公式递归定义：

1. 命题变量是公式
2. 如果 $\phi$ 是公式，则 $\neg \phi$、$\Box \phi$、$\Diamond \phi$ 是公式
3. 如果 $\phi$ 和 $\psi$ 是公式，则 $(\phi \land \psi)$、$(\phi \lor \psi)$、$(\phi \rightarrow \psi)$、$(\phi \leftrightarrow \psi)$ 是公式

### 3.2 克里普克语义

**定义 3.2.1 (克里普克框架)**
克里普克框架是二元组 $\mathcal{F} = (W, R)$，其中：

1. $W$ 是非空集合（可能世界集）
2. $R \subseteq W \times W$ 是可达关系

**定义 3.2.2 (克里普克模型)**
克里普克模型是三元组 $\mathcal{M} = (W, R, V)$，其中：

1. $(W, R)$ 是克里普克框架
2. $V: P \rightarrow \mathcal{P}(W)$ 是赋值函数

**定义 3.2.3 (模态满足关系)**
满足关系 $\mathcal{M}, w \models \phi$ 递归定义：

1. $\mathcal{M}, w \models p$ 当且仅当 $w \in V(p)$
2. $\mathcal{M}, w \models \neg \phi$ 当且仅当 $\mathcal{M}, w \not\models \phi$
3. $\mathcal{M}, w \models \phi \land \psi$ 当且仅当 $\mathcal{M}, w \models \phi$ 且 $\mathcal{M}, w \models \psi$
4. $\mathcal{M}, w \models \phi \lor \psi$ 当且仅当 $\mathcal{M}, w \models \phi$ 或 $\mathcal{M}, w \models \psi$
5. $\mathcal{M}, w \models \phi \rightarrow \psi$ 当且仅当 $\mathcal{M}, w \not\models \phi$ 或 $\mathcal{M}, w \models \psi$
6. $\mathcal{M}, w \models \Box \phi$ 当且仅当对于所有 $v$ 使得 $w R v$，$\mathcal{M}, v \models \phi$
7. $\mathcal{M}, w \models \Diamond \phi$ 当且仅当存在 $v$ 使得 $w R v$ 且 $\mathcal{M}, v \models \phi$

### 3.3 模态系统

**定义 3.3.1 (K系统)**
K系统包含：

1. 所有重言式
2. 分配公理：$\Box(\phi \rightarrow \psi) \rightarrow (\Box \phi \rightarrow \Box \psi)$
3. 必然化规则：如果 $\vdash \phi$，则 $\vdash \Box \phi$

**定义 3.3.2 (T系统)**
T系统在K系统基础上添加：

- T公理：$\Box \phi \rightarrow \phi$

**定义 3.3.3 (S4系统)**
S4系统在T系统基础上添加：

- 4公理：$\Box \phi \rightarrow \Box \Box \phi$

**定义 3.3.4 (S5系统)**
S5系统在T系统基础上添加：

- 5公理：$\Diamond \phi \rightarrow \Box \Diamond \phi$

**定理 3.3.1 (对应定理)**
模态公理与框架性质对应：

- T公理 ↔ 自反性
- 4公理 ↔ 传递性
- 5公理 ↔ 欧几里得性
- B公理 ↔ 对称性

## 4. 证明理论

### 4.1 自然演绎

**定义 4.1.1 (证明)**
证明是有限序列 $\phi_1, \ldots, \phi_n$，其中每个 $\phi_i$ 要么是假设，要么是通过推理规则从前面的公式得到的。

**定义 4.1.2 (可证明性)**
$\Gamma \vdash \phi$ 表示存在从 $\Gamma$ 到 $\phi$ 的证明。

### 4.2 序列演算

**定义 4.2.1 (序列)**
序列是形如 $\Gamma \Rightarrow \Delta$ 的表达式，其中 $\Gamma$ 和 $\Delta$ 是公式的多重集。

**定义 4.2.2 (序列演算规则)**
序列演算包含以下规则：

**左规则**：
$$\frac{\Gamma, \phi \Rightarrow \Delta}{\Gamma, \phi \land \psi \Rightarrow \Delta} \quad \frac{\Gamma, \psi \Rightarrow \Delta}{\Gamma, \phi \land \psi \Rightarrow \Delta}$$

**右规则**：
$$\frac{\Gamma \Rightarrow \phi, \Delta \quad \Gamma \Rightarrow \psi, \Delta}{\Gamma \Rightarrow \phi \land \psi, \Delta}$$

**定理 4.2.1 (切割消除)**
序列演算中的切割规则是可消除的。

### 4.3 证明复杂度

**定义 4.3.1 (证明长度)**
证明的长度是证明中公式的数量。

**定义 4.3.2 (证明深度)**
证明的深度是证明树的最大高度。

**定理 4.3.1 (证明压缩)**
如果 $\phi$ 有长度为 $n$ 的证明，则 $\phi$ 有深度为 $O(\log n)$ 的证明。

## 5. 模型论

### 5.1 初等等价

**定义 5.1.1 (初等等价)**
结构 $\mathcal{M}$ 和 $\mathcal{N}$ 初等等价，记作 $\mathcal{M} \equiv \mathcal{N}$，当且仅当对于所有句子 $\phi$，$\mathcal{M} \models \phi$ 当且仅当 $\mathcal{N} \models \phi$。

**定理 5.1.1 (初等等价的刻画)**
$\mathcal{M} \equiv \mathcal{N}$ 当且仅当存在初等嵌入 $f: \mathcal{M} \rightarrow \mathcal{N}$ 和 $g: \mathcal{N} \rightarrow \mathcal{M}$。

### 5.2 紧致性定理

**定理 5.2.1 (紧致性定理)**
理论 $T$ 有模型当且仅当 $T$ 的每个有限子集都有模型。

**证明：** 通过超积构造或哥德尔完备性定理。

### 5.3 勒文海姆-斯科伦定理

**定理 5.3.1 (向下勒文海姆-斯科伦定理)**
如果理论 $T$ 有无限模型，则对于任意基数 $\kappa \geq |\mathcal{L}|$，$T$ 有基数为 $\kappa$ 的模型。

**定理 5.3.2 (向上勒文海姆-斯科伦定理)**
如果理论 $T$ 有无限模型，则对于任意基数 $\kappa \geq \max(|\mathcal{L}|, \aleph_0)$，$T$ 有基数为 $\kappa$ 的模型。

## 6. 非经典逻辑

### 6.1 直觉主义逻辑

**定义 6.1.1 (直觉主义语义)**
直觉主义逻辑的语义基于构造性解释：

- $\phi \lor \psi$ 为真当且仅当 $\phi$ 为真或 $\psi$ 为真
- $\exists x \phi(x)$ 为真当且仅当存在构造性证据证明 $\phi(a)$ 为真

**定理 6.1.1 (双重否定消除)**
在直觉主义逻辑中，$\neg \neg \phi \rightarrow \phi$ 不是定理。

### 6.2 多值逻辑

**定义 6.2.1 (三值逻辑)**
三值逻辑的真值集为 $\{0, \frac{1}{2}, 1\}$，其中 $\frac{1}{2}$ 表示"未定义"。

**定义 6.2.2 (模糊逻辑)**
模糊逻辑的真值集为 $[0, 1]$，真值函数定义为：

- $\llbracket \phi \land \psi \rrbracket = \min(\llbracket \phi \rrbracket, \llbracket \psi \rrbracket)$
- $\llbracket \phi \lor \psi \rrbracket = \max(\llbracket \phi \rrbracket, \llbracket \psi \rrbracket)$
- $\llbracket \neg \phi \rrbracket = 1 - \llbracket \phi \rrbracket$

### 6.3 非单调逻辑

**定义 6.3.1 (非单调推理)**
非单调推理允许在获得新信息时撤销之前的结论。

**定义 6.3.2 (默认逻辑)**
默认逻辑包含形如 $\frac{\alpha : \beta}{\gamma}$ 的默认规则，表示如果 $\alpha$ 为真且 $\beta$ 与当前知识一致，则推导 $\gamma$。

## 7. 逻辑哲学

### 7.1 逻辑的本质

**问题 7.1.1 (逻辑是发现的还是发明的？)**

- **发现论**：逻辑规律是客观存在的，人类只是发现它们
- **发明论**：逻辑是人类构造的工具，用于推理和论证

**问题 7.1.2 (逻辑的普遍性)**

- 逻辑规律是否适用于所有领域？
- 是否存在领域特定的逻辑？

### 7.2 逻辑多元主义

**定义 7.2.1 (逻辑多元主义)**
逻辑多元主义认为存在多种不同的逻辑系统，每种都有其适用领域。

**论证 7.2.1 (多元主义论证)**

1. 经典逻辑适用于经典数学
2. 直觉主义逻辑适用于构造性数学
3. 模态逻辑适用于可能性和必然性推理
4. 因此，不同逻辑适用于不同领域

### 7.3 逻辑与认知

**问题 7.3.1 (逻辑与思维的关系)**

- 逻辑是否反映了人类的思维规律？
- 逻辑是否应该符合人类的直觉？

**问题 7.3.2 (逻辑学习)**

- 逻辑能力是天生的还是后天习得的？
- 如何提高逻辑思维能力？

## 8. 参考文献

1. Enderton, H. B. (2001). A Mathematical Introduction to Logic. Academic Press.
2. van Dalen, D. (2013). Logic and Structure. Springer-Verlag.
3. Blackburn, P., de Rijke, M., & Venema, Y. (2001). Modal Logic. Cambridge University Press.
4. Troelstra, A. S., & Schwichtenberg, H. (2000). Basic Proof Theory. Cambridge University Press.
5. Chang, C. C., & Keisler, H. J. (2012). Model Theory. Dover Publications.
6. Priest, G. (2008). An Introduction to Non-Classical Logic. Cambridge University Press.
7. Haack, S. (1978). Philosophy of Logics. Cambridge University Press.
