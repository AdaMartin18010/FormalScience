# 逻辑学基础 (Logic Foundation)

## 目录

1. [命题逻辑](#1-命题逻辑)
2. [谓词逻辑](#2-谓词逻辑)
3. [模态逻辑](#3-模态逻辑)
4. [证明理论](#4-证明理论)
5. [模型论](#5-模型论)
6. [非经典逻辑](#6-非经典逻辑)
7. [逻辑哲学](#7-逻辑哲学)

## 1. 命题逻辑

### 1.1 语法

**定义 1.1.1** (命题变量) 命题变量是基本命题符号，通常用 $p, q, r, \ldots$ 表示。

**定义 1.1.2** (命题公式) 命题公式按以下规则递归定义：
1. 每个命题变量是命题公式
2. 如果 $\phi$ 是命题公式，则 $\neg \phi$ 是命题公式
3. 如果 $\phi$ 和 $\psi$ 是命题公式，则 $(\phi \land \psi)$、$(\phi \lor \psi)$、$(\phi \rightarrow \psi)$、$(\phi \leftrightarrow \psi)$ 是命题公式

**定义 1.1.3** (逻辑连接词) 逻辑连接词包括：
- $\neg$ (否定)
- $\land$ (合取)
- $\lor$ (析取)
- $\rightarrow$ (蕴含)
- $\leftrightarrow$ (等价)

### 1.2 语义

**定义 1.2.1** (真值赋值) 真值赋值是从命题变量到 $\{0, 1\}$ 的函数 $v$，其中 $0$ 表示假，$1$ 表示真。

**定义 1.2.2** (真值函数) 真值函数 $V_v$ 按以下规则递归定义：
1. $V_v(p) = v(p)$ 对于命题变量 $p$
2. $V_v(\neg \phi) = 1 - V_v(\phi)$
3. $V_v(\phi \land \psi) = \min(V_v(\phi), V_v(\psi))$
4. $V_v(\phi \lor \psi) = \max(V_v(\phi), V_v(\psi))$
5. $V_v(\phi \rightarrow \psi) = \max(1 - V_v(\phi), V_v(\psi))$
6. $V_v(\phi \leftrightarrow \psi) = 1$ 当且仅当 $V_v(\phi) = V_v(\psi)$

**定义 1.2.3** (重言式) 命题公式 $\phi$ 是重言式，如果对于所有真值赋值 $v$，都有 $V_v(\phi) = 1$。

**定义 1.2.4** (矛盾式) 命题公式 $\phi$ 是矛盾式，如果对于所有真值赋值 $v$，都有 $V_v(\phi) = 0$。

**定义 1.2.5** (可满足式) 命题公式 $\phi$ 是可满足式，如果存在真值赋值 $v$ 使得 $V_v(\phi) = 1$。

### 1.3 推理系统

**定义 1.3.1** (自然演绎系统) 自然演绎系统包含以下推理规则：

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

**定理 1.3.1** (可靠性) 如果 $\Gamma \vdash \phi$，则 $\Gamma \models \phi$。

**定理 1.3.2** (完备性) 如果 $\Gamma \models \phi$，则 $\Gamma \vdash \phi$。

### 1.4 范式

**定义 1.4.1** (析取范式) 命题公式是析取范式，如果它是形如 $\bigvee_{i=1}^n \bigwedge_{j=1}^{m_i} l_{ij}$ 的公式，其中每个 $l_{ij}$ 是文字（命题变量或其否定）。

**定义 1.4.2** (合取范式) 命题公式是合取范式，如果它是形如 $\bigwedge_{i=1}^n \bigvee_{j=1}^{m_i} l_{ij}$ 的公式，其中每个 $l_{ij}$ 是文字。

**定理 1.4.1** (范式存在性) 每个命题公式都等价于某个析取范式和某个合取范式。

**证明** 使用分配律和德摩根律可以将任意公式转换为范式。

## 2. 谓词逻辑

### 2.1 语法

**定义 2.1.1** (个体变量) 个体变量是表示个体的符号，通常用 $x, y, z, \ldots$ 表示。

**定义 2.1.2** (谓词符号) 谓词符号是表示关系的符号，通常用 $P, Q, R, \ldots$ 表示。

**定义 2.1.3** (函数符号) 函数符号是表示函数的符号，通常用 $f, g, h, \ldots$ 表示。

**定义 2.1.4** (项) 项按以下规则递归定义：
1. 每个个体变量是项
2. 每个个体常项是项
3. 如果 $f$ 是 $n$ 元函数符号，$t_1, \ldots, t_n$ 是项，则 $f(t_1, \ldots, t_n)$ 是项

**定义 2.1.5** (原子公式) 原子公式是形如 $P(t_1, \ldots, t_n)$ 的公式，其中 $P$ 是 $n$ 元谓词符号，$t_1, \ldots, t_n$ 是项。

**定义 2.1.6** (谓词公式) 谓词公式按以下规则递归定义：
1. 每个原子公式是谓词公式
2. 如果 $\phi$ 是谓词公式，则 $\neg \phi$ 是谓词公式
3. 如果 $\phi$ 和 $\psi$ 是谓词公式，则 $(\phi \land \psi)$、$(\phi \lor \psi)$、$(\phi \rightarrow \psi)$、$(\phi \leftrightarrow \psi)$ 是谓词公式
4. 如果 $\phi$ 是谓词公式，$x$ 是个体变量，则 $\forall x \phi$ 和 $\exists x \phi$ 是谓词公式

### 2.2 语义

**定义 2.2.1** (结构) 结构 $\mathcal{A} = (A, I)$ 由非空域 $A$ 和解释函数 $I$ 组成，其中 $I$ 为每个谓词符号和函数符号分配适当的解释。

**定义 2.2.2** (赋值) 赋值是从个体变量到域 $A$ 的函数 $s$。

**定义 2.2.3** (项解释) 项 $t$ 在结构 $\mathcal{A}$ 和赋值 $s$ 下的解释 $t^{\mathcal{A}, s}$ 按以下规则递归定义：
1. 如果 $t$ 是个体变量 $x$，则 $t^{\mathcal{A}, s} = s(x)$
2. 如果 $t$ 是个体常项 $c$，则 $t^{\mathcal{A}, s} = I(c)$
3. 如果 $t = f(t_1, \ldots, t_n)$，则 $t^{\mathcal{A}, s} = I(f)(t_1^{\mathcal{A}, s}, \ldots, t_n^{\mathcal{A}, s})$

**定义 2.2.4** (满足关系) 满足关系 $\models$ 按以下规则递归定义：
1. $\mathcal{A}, s \models P(t_1, \ldots, t_n)$ 当且仅当 $(t_1^{\mathcal{A}, s}, \ldots, t_n^{\mathcal{A}, s}) \in I(P)$
2. $\mathcal{A}, s \models \neg \phi$ 当且仅当 $\mathcal{A}, s \not\models \phi$
3. $\mathcal{A}, s \models \phi \land \psi$ 当且仅当 $\mathcal{A}, s \models \phi$ 且 $\mathcal{A}, s \models \psi$
4. $\mathcal{A}, s \models \phi \lor \psi$ 当且仅当 $\mathcal{A}, s \models \phi$ 或 $\mathcal{A}, s \models \psi$
5. $\mathcal{A}, s \models \phi \rightarrow \psi$ 当且仅当 $\mathcal{A}, s \not\models \phi$ 或 $\mathcal{A}, s \models \psi$
6. $\mathcal{A}, s \models \forall x \phi$ 当且仅当对于所有 $a \in A$，$\mathcal{A}, s[x \mapsto a] \models \phi$
7. $\mathcal{A}, s \models \exists x \phi$ 当且仅当存在 $a \in A$ 使得 $\mathcal{A}, s[x \mapsto a] \models \phi$

### 2.3 推理系统

**定义 2.3.1** (谓词逻辑推理规则) 在命题逻辑规则基础上，增加以下规则：

**全称引入**：
$$\frac{\Gamma \vdash \phi}{\Gamma \vdash \forall x \phi}$$
其中 $x$ 不在 $\Gamma$ 中自由出现。

**全称消除**：
$$\frac{\Gamma \vdash \forall x \phi}{\Gamma \vdash \phi[t/x]}$$
其中 $t$ 是项，$t$ 对 $x$ 在 $\phi$ 中可代入。

**存在引入**：
$$\frac{\Gamma \vdash \phi[t/x]}{\Gamma \vdash \exists x \phi}$$
其中 $t$ 是项，$t$ 对 $x$ 在 $\phi$ 中可代入。

**存在消除**：
$$\frac{\Gamma \vdash \exists x \phi \quad \Gamma, \phi \vdash \psi}{\Gamma \vdash \psi}$$
其中 $x$ 不在 $\Gamma$ 或 $\psi$ 中自由出现。

**定理 2.3.1** (哥德尔完备性) 谓词逻辑是可靠且完备的。

## 3. 模态逻辑

### 3.1 基本模态逻辑

**定义 3.1.1** (模态公式) 在命题逻辑基础上，增加模态算子 $\Box$ (必然) 和 $\Diamond$ (可能)：
- 如果 $\phi$ 是模态公式，则 $\Box \phi$ 和 $\Diamond \phi$ 是模态公式

**定义 3.1.2** (克里普克模型) 克里普克模型是三元组 $\mathcal{M} = (W, R, V)$，其中：
- $W$ 是可能世界集
- $R \subseteq W \times W$ 是可达关系
- $V: W \times \text{Prop} \rightarrow \{0, 1\}$ 是赋值函数

**定义 3.1.3** (模态语义) 满足关系按以下规则递归定义：
1. $\mathcal{M}, w \models p$ 当且仅当 $V(w, p) = 1$
2. $\mathcal{M}, w \models \Box \phi$ 当且仅当对于所有 $v$ 使得 $wRv$，$\mathcal{M}, v \models \phi$
3. $\mathcal{M}, w \models \Diamond \phi$ 当且仅当存在 $v$ 使得 $wRv$ 且 $\mathcal{M}, v \models \phi$

### 3.2 模态系统

**定义 3.2.1** (K系统) K系统包含以下公理和规则：
- 所有命题逻辑重言式
- K公理：$\Box(\phi \rightarrow \psi) \rightarrow (\Box \phi \rightarrow \Box \psi)$
- 必然化规则：如果 $\vdash \phi$，则 $\vdash \Box \phi$

**定义 3.2.2** (T系统) T系统在K系统基础上增加：
- T公理：$\Box \phi \rightarrow \phi$

**定义 3.2.3** (S4系统) S4系统在T系统基础上增加：
- 4公理：$\Box \phi \rightarrow \Box \Box \phi$

**定义 3.2.4** (S5系统) S5系统在T系统基础上增加：
- 5公理：$\Diamond \phi \rightarrow \Box \Diamond \phi$

**定理 3.2.1** (对应定理) 模态公式与框架性质之间存在对应关系：
- T公理对应自反性
- 4公理对应传递性
- 5公理对应欧几里得性

## 4. 证明理论

### 4.1 自然演绎

**定义 4.1.1** (证明) 证明是从假设到结论的有限步骤序列，每个步骤都遵循推理规则。

**定义 4.1.2** (可证明性) 如果存在从 $\Gamma$ 到 $\phi$ 的证明，则记作 $\Gamma \vdash \phi$。

**定理 4.1.1** (演绎定理) $\Gamma, \phi \vdash \psi$ 当且仅当 $\Gamma \vdash \phi \rightarrow \psi$。

### 4.2 序列演算

**定义 4.2.1** (序列) 序列是形如 $\Gamma \Rightarrow \Delta$ 的表达式，其中 $\Gamma$ 和 $\Delta$ 是公式的多重集。

**定义 4.2.2** (序列演算规则) 序列演算包含以下规则：

**左规则**：
$$\frac{\Gamma, \phi \Rightarrow \Delta}{\Gamma, \phi \land \psi \Rightarrow \Delta} \quad \frac{\Gamma, \psi \Rightarrow \Delta}{\Gamma, \phi \land \psi \Rightarrow \Delta}$$

**右规则**：
$$\frac{\Gamma \Rightarrow \phi, \Delta \quad \Gamma \Rightarrow \psi, \Delta}{\Gamma \Rightarrow \phi \land \psi, \Delta}$$

**定理 4.2.1** (切割消除) 序列演算中的切割规则是可消除的。

## 5. 模型论

### 5.1 基本概念

**定义 5.1.1** (初等等价) 两个结构 $\mathcal{A}$ 和 $\mathcal{B}$ 初等等价，如果它们满足相同的句子。

**定义 5.1.2** (初等子结构) 结构 $\mathcal{A}$ 是结构 $\mathcal{B}$ 的初等子结构，如果 $\mathcal{A} \subseteq \mathcal{B}$ 且对于所有公式 $\phi$ 和赋值 $s$，$\mathcal{A}, s \models \phi$ 当且仅当 $\mathcal{B}, s \models \phi$。

**定理 5.1.1** (勒文海姆-斯科伦定理) 如果可数语言的理论有无限模型，则它有任意基数的模型。

### 5.2 紧致性

**定理 5.2.1** (紧致性定理) 公式集 $\Gamma$ 可满足当且仅当 $\Gamma$ 的每个有限子集都可满足。

**推论 5.2.1** 如果理论 $T$ 的每个有限子理论都有模型，则 $T$ 有模型。

## 6. 非经典逻辑

### 6.1 直觉主义逻辑

**定义 6.1.1** (直觉主义语义) 直觉主义逻辑使用构造性解释，排中律 $\phi \lor \neg \phi$ 不是重言式。

**定义 6.1.2** (克里普克语义) 直觉主义逻辑的克里普克语义要求可达关系是偏序。

### 6.2 多值逻辑

**定义 6.2.1** (三值逻辑) 三值逻辑的真值集为 $\{0, \frac{1}{2}, 1\}$，其中 $\frac{1}{2}$ 表示不确定。

**定义 6.2.2** (模糊逻辑) 模糊逻辑的真值集为 $[0, 1]$，使用连续的真值函数。

### 6.3 非单调逻辑

**定义 6.3.1** (默认逻辑) 默认逻辑允许在缺乏相反证据时进行推理。

**定义 6.3.2** (自认知逻辑) 自认知逻辑包含关于知识和信念的推理。

## 7. 逻辑哲学

### 7.1 逻辑的本质

**问题 7.1.1** 逻辑是发现的还是发明的？

**观点 7.1.1** (柏拉图主义) 逻辑规律是客观存在的，我们只是发现它们。

**观点 7.1.2** (约定主义) 逻辑规律是人类约定的产物。

**观点 7.1.3** (工具主义) 逻辑是推理的工具，其有效性在于实用性。

### 7.2 逻辑多元主义

**定义 7.2.1** (逻辑多元主义) 存在多种不同的逻辑系统，它们都是有效的。

**论证 7.2.1** 不同的逻辑系统适用于不同的推理场景。

### 7.3 逻辑与数学

**关系 7.3.1** 逻辑为数学提供基础，数学为逻辑提供应用。

**问题 7.3.1** 数学是否可还原为逻辑？

---

**参考文献**

1. Enderton, H. B. (2001). *A Mathematical Introduction to Logic*. Academic Press.
2. van Dalen, D. (2013). *Logic and Structure*. Springer-Verlag.
3. Blackburn, P., de Rijke, M., & Venema, Y. (2001). *Modal Logic*. Cambridge University Press.
4. Priest, G. (2008). *An Introduction to Non-Classical Logic*. Cambridge University Press. 