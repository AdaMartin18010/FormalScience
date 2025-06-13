# 形式语言理论基础 - 形式化数学体系

## 目录

1. [基础概念与定义](#1-基础概念与定义)
2. [有限状态自动机](#2-有限状态自动机)
3. [上下文无关文法](#3-上下文无关文法)
4. [下推自动机](#4-下推自动机)
5. [图灵机理论](#5-图灵机理论)
6. [语法分析理论](#6-语法分析理论)
7. [语义理论](#7-语义理论)
8. [计算复杂性](#8-计算复杂性)

## 1. 基础概念与定义

### 1.1 字母表与字符串

-**定义 1.1.1 (字母表)**
字母表 $\Sigma$ 是有限符号集合：$\Sigma = \{a_1, a_2, \ldots, a_n\}$。

-**定义 1.1.2 (字符串)**
字符串是字母表中符号的有限序列：
$$w = a_1 a_2 \cdots a_n \text{ where } a_i \in \Sigma$$

-**定义 1.1.3 (空字符串)**
空字符串 $\epsilon$ 是长度为0的字符串。

-**定义 1.1.4 (字符串长度)**
字符串 $w = a_1 a_2 \cdots a_n$ 的长度：$|w| = n$。

-**定义 1.1.5 (字符串连接)**
字符串 $w_1 = a_1 \cdots a_m$ 和 $w_2 = b_1 \cdots b_n$ 的连接：
$$w_1 \cdot w_2 = a_1 \cdots a_m b_1 \cdots b_n$$

-**定义 1.1.6 (字符串幂运算)**
字符串 $w$ 的幂运算：
$$w^0 = \epsilon$$
$$w^{n+1} = w \cdot w^n$$

### 1.2 语言定义

-**定义 1.2.1 (克林闭包)**
字母表 $\Sigma$ 的克林闭包：
$$\Sigma^* = \bigcup_{n=0}^{\infty} \Sigma^n$$

其中 $\Sigma^n = \{w \mid |w| = n\}$。

-**定义 1.2.2 (语言)**
语言 $L$ 是字符串集合：$L \subseteq \Sigma^*$。

-**定义 1.2.3 (语言操作)**

- **并集**：$L_1 \cup L_2 = \{w \mid w \in L_1 \text{ or } w \in L_2\}$
- **连接**：$L_1 \cdot L_2 = \{w_1 w_2 \mid w_1 \in L_1, w_2 \in L_2\}$
- **克林闭包**：$L^* = \bigcup_{n=0}^{\infty} L^n$
- **正闭包**：$L^+ = \bigcup_{n=1}^{\infty} L^n$

**定理 1.2.1 (语言操作性质)**
对于任意语言 $L_1, L_2, L_3$：

1. **结合律**：$(L_1 \cdot L_2) \cdot L_3 = L_1 \cdot (L_2 \cdot L_3)$
2. **分配律**：$L_1 \cdot (L_2 \cup L_3) = L_1 \cdot L_2 \cup L_1 \cdot L_3$
3. **幂等律**：$(L^*)^* = L^*$

**证明：** 通过集合论和字符串操作的定义。

### 1.3 乔姆斯基层次结构

-**定义 1.3.1 (乔姆斯基层次)**
语言类别的层次结构：

1. **正则语言 (Regular Languages)**：有限状态自动机识别
2. **上下文无关语言 (Context-Free Languages)**：下推自动机识别
3. **上下文有关语言 (Context-Sensitive Languages)**：线性有界自动机识别
4. **递归可枚举语言 (Recursively Enumerable Languages)**：图灵机识别

**定理 1.3.1 (层次包含关系)**
$$\text{Regular} \subset \text{CFL} \subset \text{CSL} \subset \text{REL}$$

**证明：** 通过构造性证明：

1. **包含关系**：每个层次包含前一个层次
2. **严格包含**：存在语言属于更高层次但不属于较低层次
3. **泵引理**：通过泵引理证明严格包含

## 2. 有限状态自动机

### 2.1 确定性有限自动机

-**定义 2.1.1 (DFA)**
确定性有限自动机是五元组 $M = (Q, \Sigma, \delta, q_0, F)$，其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是输入字母表
- $\delta : Q \times \Sigma \rightarrow Q$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $F \subseteq Q$ 是接受状态集合

-**定义 2.1.2 (扩展转移函数)**
扩展转移函数 $\hat{\delta} : Q \times \Sigma^* \rightarrow Q$：
$$\hat{\delta}(q, \epsilon) = q$$
$$\hat{\delta}(q, wa) = \delta(\hat{\delta}(q, w), a)$$

-**定义 2.1.3 (DFA接受)**
DFA接受字符串 $w$，如果 $\hat{\delta}(q_0, w) \in F$。

-**定义 2.1.4 (DFA语言)**
DFA $M$ 接受的语言：
$$L(M) = \{w \in \Sigma^* \mid \hat{\delta}(q_0, w) \in F\}$$

-**算法 2.1.1 (DFA模拟)**

```haskell
simulateDFA :: DFA -> String -> Bool
simulateDFA dfa input = 
  let finalState = foldl (transition dfa) (initialState dfa) input
  in finalState `elem` (acceptingStates dfa)

transition :: DFA -> State -> Char -> State
transition dfa currentState symbol = 
  delta dfa currentState symbol

extendedTransition :: DFA -> State -> String -> State
extendedTransition dfa state [] = state
extendedTransition dfa state (c:cs) = 
  let nextState = transition dfa state c
  in extendedTransition dfa nextState cs
```

### 2.2 非确定性有限自动机

-**定义 2.2.1 (NFA)**
非确定性有限自动机是五元组 $M = (Q, \Sigma, \delta, q_0, F)$，其中：

- $\delta : Q \times \Sigma \rightarrow 2^Q$ 是转移函数

-**定义 2.2.2 (ε-NFA)**
ε-非确定性有限自动机是五元组 $M = (Q, \Sigma, \delta, q_0, F)$，其中：

- $\delta : Q \times (\Sigma \cup \{\epsilon\}) \rightarrow 2^Q$ 是转移函数

-**定义 2.2.3 (ε闭包)**
状态 $q$ 的ε闭包：
$$\text{CLOSURE}(q) = \{p \in Q \mid q \xrightarrow{\epsilon^*} p\}$$

**定理 2.2.1 (DFA与NFA等价性)**
对于每个NFA，存在等价的DFA。

**证明：** 通过子集构造：

1. **DFA状态**：DFA状态是NFA状态集合
2. **DFA转移**：DFA转移函数通过子集计算
3. **接受状态**：接受状态包含NFA接受状态

-**算法 2.2.1 (子集构造)**

```haskell
subsetConstruction :: NFA -> DFA
subsetConstruction nfa = 
  let initialState = epsilonClosure nfa [initialState nfa]
      allStates = generateAllStates nfa initialState
      transitions = buildTransitions nfa allStates
      acceptingStates = findAcceptingStates nfa allStates
  in DFA { states = allStates
         , alphabet = alphabet nfa
         , delta = transitions
         , initialState = initialState
         , acceptingStates = acceptingStates }

epsilonClosure :: NFA -> [State] -> [State]
epsilonClosure nfa states = 
  let directEpsilon = concat [delta nfa s Epsilon | s <- states]
      newStates = filter (`notElem` states) directEpsilon
  in if null newStates then states
     else epsilonClosure nfa (states ++ newStates)
```

### 2.3 正则表达式

-**定义 2.3.1 (正则表达式语法)**
正则表达式的语法：
$$R ::= \emptyset \mid \epsilon \mid a \mid R_1 + R_2 \mid R_1 \cdot R_2 \mid R^*$$

其中 $a \in \Sigma$。

-**定义 2.3.2 (正则表达式语义)**

- $L(\emptyset) = \emptyset$
- $L(\epsilon) = \{\epsilon\}$
- $L(a) = \{a\}$
- $L(R_1 + R_2) = L(R_1) \cup L(R_2)$
- $L(R_1 \cdot R_2) = L(R_1) \cdot L(R_2)$
- $L(R^*) = L(R)^*$

**定理 2.3.1 (正则表达式与DFA等价性)**
正则表达式和DFA识别相同的语言类。

**证明：** 双向构造：

1. **正则表达式到NFA**：通过递归构造
2. **NFA到DFA**：通过子集构造
3. **DFA到正则表达式**：通过状态消除

-**算法 2.3.1 (正则表达式到NFA)**

```haskell
regexToNFA :: Regex -> NFA
regexToNFA Empty = buildEmptyNFA
regexToNFA Epsilon = buildEpsilonNFA
regexToNFA (Symbol a) = buildSymbolNFA a
regexToNFA (Union r1 r2) = 
  let nfa1 = regexToNFA r1
      nfa2 = regexToNFA r2
  in unionNFA nfa1 nfa2
regexToNFA (Concat r1 r2) = 
  let nfa1 = regexToNFA r1
      nfa2 = regexToNFA r2
  in concatNFA nfa1 nfa2
regexToNFA (Star r) = 
  let nfa = regexToNFA r
  in starNFA nfa
```

### 2.4 泵引理

**定理 2.4.1 (正则语言泵引理)**
如果 $L$ 是正则语言，则存在常数 $n$ 使得对于任意 $w \in L$ 且 $|w| \geq n$，存在分解 $w = xyz$ 满足：

1. $|xy| \leq n$
2. $|y| > 0$
3. 对于任意 $k \geq 0$，$xy^k z \in L$

**证明：** 通过鸽巢原理：

1. 如果 $|w| \geq n$，则DFA计算中至少有一个状态重复
2. 重复状态之间的部分可以泵
3. 泵操作保持语言成员性

**应用 2.4.1 (非正则语言证明)**
语言 $L = \{a^n b^n \mid n \geq 0\}$ 不是正则语言。

**证明：** 使用泵引理：

1. 假设 $L$ 是正则语言
2. 选择 $w = a^n b^n$ 其中 $n$ 是泵引理常数
3. 分解 $w = xyz$ 满足泵引理条件
4. 由于 $|xy| \leq n$，$y$ 只包含 $a$
5. 泵 $y$ 得到 $xy^2 z = a^{n+|y|} b^n \notin L$
6. 矛盾，因此 $L$ 不是正则语言

## 3. 上下文无关文法

### 3.1 文法定义

-**定义 3.1.1 (CFG)**
上下文无关文法是四元组 $G = (V, T, P, S)$，其中：

- $V$ 是非终结符集合
- $T$ 是终结符集合
- $P$ 是产生式集合，形如 $A \rightarrow \alpha$
- $S \in V$ 是开始符号

-**定义 3.1.2 (推导)**
推导关系 $\Rightarrow$ 定义：

- 如果 $A \rightarrow \alpha \in P$，则 $\beta A \gamma \Rightarrow \beta \alpha \gamma$
- 如果 $\alpha \Rightarrow \beta$ 且 $\beta \Rightarrow \gamma$，则 $\alpha \Rightarrow \gamma$

-**定义 3.1.3 (语言生成)**
文法 $G$ 生成的语言：
$$L(G) = \{w \in T^* \mid S \Rightarrow^* w\}$$

-**定义 3.1.4 (语法树)**
语法树是推导的树形表示，其中：

- 根节点是开始符号
- 内部节点是非终结符
- 叶节点是终结符或ε

-**算法 3.1.1 (CFG解析)**

```haskell
parseCFG :: CFG -> String -> Bool
parseCFG cfg input = 
  let startSymbol = startSymbol cfg
      derivations = generateDerivations cfg startSymbol
      terminalStrings = filter isTerminal derivations
  in input `elem` terminalStrings

generateDerivations :: CFG -> Symbol -> [String]
generateDerivations cfg symbol = 
  case symbol of
    Terminal a -> [[a]]
    NonTerminal a -> 
      let productions = getProductions cfg a
          derivations = concatMap (generateDerivations cfg) productions
      in derivations
```

### 3.2 乔姆斯基范式

-**定义 3.2.1 (CNF)**
乔姆斯基范式文法满足：

- 所有产生式形如 $A \rightarrow BC$ 或 $A \rightarrow a$
- 其中 $A, B, C \in V$ 且 $a \in T$

**定理 3.2.1 (CNF转换)**
每个CFG都可以转换为等价的CNF。

**证明：** 通过构造性转换：

1. **消除ε产生式**：识别可推导ε的非终结符
2. **消除单位产生式**：通过传递闭包
3. **转换为CNF**：引入新的非终结符

-**算法 3.2.1 (CNF转换)**

```haskell
convertToCNF :: CFG -> CFG
convertToCNF cfg = 
  let cfg1 = eliminateEpsilon cfg
      cfg2 = eliminateUnit cfg1
      cfg3 = eliminateLong cfg2
  in cfg3

eliminateEpsilon :: CFG -> CFG
eliminateEpsilon cfg = 
  let nullable = findNullable cfg
      newProductions = removeEpsilonProductions cfg nullable
  in cfg { productions = newProductions }

eliminateUnit :: CFG -> CFG
eliminateUnit cfg = 
  let unitPairs = findUnitPairs cfg
      newProductions = removeUnitProductions cfg unitPairs
  in cfg { productions = newProductions }
```

### 3.3 格雷巴赫范式

-**定义 3.3.1 (GNF)**
格雷巴赫范式文法满足：

- 所有产生式形如 $A \rightarrow a\alpha$
- 其中 $a \in T$ 且 $\alpha \in V^*$

**定理 3.3.1 (GNF转换)**
每个CFG都可以转换为等价的GNF。

**证明：** 通过构造性转换：

1. 首先转换为CNF
2. 消除左递归
3. 转换为GNF形式

### 3.4 泵引理

**定理 3.4.1 (上下文无关语言泵引理)**
如果 $L$ 是上下文无关语言，则存在常数 $n$ 使得对于任意 $w \in L$ 且 $|w| \geq n$，存在分解 $w = uvxyz$ 满足：

1. $|vxy| \leq n$
2. $|vy| > 0$
3. 对于任意 $k \geq 0$，$uv^k xy^k z \in L$

**证明：** 通过语法树分析：

1. 如果 $|w| \geq n$，则语法树高度足够大
2. 存在路径上的非终结符重复
3. 重复部分可以泵

**应用 3.4.1 (非上下文无关语言证明)**
语言 $L = \{a^n b^n c^n \mid n \geq 0\}$ 不是上下文无关语言。

**证明：** 使用泵引理：

1. 假设 $L$ 是上下文无关语言
2. 选择 $w = a^n b^n c^n$ 其中 $n$ 是泵引理常数
3. 分解 $w = uvxyz$ 满足泵引理条件
4. 由于 $|vxy| \leq n$，$v$ 和 $y$ 不能同时包含所有三种符号
5. 泵 $v$ 和 $y$ 破坏符号平衡
6. 矛盾，因此 $L$ 不是上下文无关语言

## 4. 下推自动机

### 4.1 下推自动机定义

-**定义 4.1.1 (PDA)**
下推自动机是七元组 $M = (Q, \Sigma, \Gamma, \delta, q_0, Z_0, F)$，其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是输入字母表
- $\Gamma$ 是栈字母表
- $\delta : Q \times (\Sigma \cup \{\epsilon\}) \times \Gamma \rightarrow 2^{Q \times \Gamma^*}$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $Z_0 \in \Gamma$ 是初始栈符号
- $F \subseteq Q$ 是接受状态集合

-**定义 4.1.2 (PDA配置)**
PDA配置是三元组 $(q, w, \alpha)$，其中：

- $q \in Q$ 是当前状态
- $w \in \Sigma^*$ 是剩余输入
- $\alpha \in \Gamma^*$ 是栈内容

-**定义 4.1.3 (PDA转移)**
配置转移关系 $\vdash$：
$$(q, aw, Z\alpha) \vdash (p, w, \beta\alpha)$$

如果 $(p, \beta) \in \delta(q, a, Z)$。

-**定义 4.1.4 (PDA接受)**
PDA接受字符串 $w$，如果 $(q_0, w, Z_0) \vdash^* (q, \epsilon, \alpha)$ 且 $q \in F$。

-**算法 4.1.1 (PDA模拟)**

```haskell
simulatePDA :: PDA -> String -> Bool
simulatePDA pda input = 
  let initialConfig = (initialState pda, input, [initialStackSymbol pda])
      finalConfigs = reachableConfigs pda initialConfig
      acceptingConfigs = filter isAccepting finalConfigs
  in not (null acceptingConfigs)

reachableConfigs :: PDA -> Config -> [Config]
reachableConfigs pda config = 
  let nextConfigs = nextConfigurations pda config
      allConfigs = config : concatMap (reachableConfigs pda) nextConfigs
  in nub allConfigs
```

### 4.2 确定性下推自动机

-**定义 4.2.1 (DPDA)**
确定性下推自动机满足：

1. 对于任意 $(q, a, Z)$，$|\delta(q, a, Z)| \leq 1$
2. 对于任意 $(q, \epsilon, Z)$，$|\delta(q, \epsilon, Z)| \leq 1$
3. 如果 $\delta(q, a, Z) \neq \emptyset$，则 $\delta(q, \epsilon, Z) = \emptyset$

**定理 4.2.1 (DPDA语言类)**
DPDA识别的语言类是上下文无关语言的真子集。

**证明：** 通过构造性证明：

1. 每个DPDA都可以转换为等价的CFG
2. 存在CFL不能被DPDA识别
3. 例如：$L = \{ww^R \mid w \in \{a, b\}^*\}$

### 4.3 PDA与CFG等价性

**定理 4.3.1 (PDA与CFG等价性)**
下推自动机和上下文无关文法识别相同的语言类。

**证明：** 双向构造：

1. **CFG到PDA**：通过自顶向下或自底向上构造
2. **PDA到CFG**：通过配置转换构造

-**算法 4.3.1 (CFG到PDA)**

```haskell
cfgToPDA :: CFG -> PDA
cfgToPDA cfg = 
  let states = [q0, q1, q2]
      alphabet = terminals cfg
      stackAlphabet = terminals cfg ++ nonTerminals cfg ++ [Z0]
      delta = buildDelta cfg
  in PDA { states = states
         , alphabet = alphabet
         , stackAlphabet = stackAlphabet
         , delta = delta
         , initialState = q0
         , initialStackSymbol = Z0
         , acceptingStates = [q2] }

buildDelta :: CFG -> Delta
buildDelta cfg = 
  let productionRules = map productionToDelta (productions cfg)
      terminalRules = map terminalToDelta (terminals cfg)
  in productionRules ++ terminalRules
```

## 5. 图灵机理论

### 5.1 图灵机定义

-**定义 5.1.1 (图灵机)**
图灵机是七元组 $M = (Q, \Sigma, \Gamma, \delta, q_0, B, F)$，其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是输入字母表
- $\Gamma$ 是磁带字母表，$\Sigma \subseteq \Gamma$
- $\delta : Q \times \Gamma \rightarrow Q \times \Gamma \times \{L, R\}$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $B \in \Gamma \setminus \Sigma$ 是空白符号
- $F \subseteq Q$ 是接受状态集合

-**定义 5.1.2 (图灵机配置)**
图灵机配置是三元组 $(q, \alpha, i)$，其中：

- $q \in Q$ 是当前状态
- $\alpha \in \Gamma^*$ 是磁带内容
- $i \in \mathbb{N}$ 是读写头位置

-**定义 5.1.3 (图灵机转移)**
配置转移关系 $\vdash$：
$$(q, \alpha_1 \cdots \alpha_{i-1} a \alpha_{i+1} \cdots, i) \vdash (p, \alpha_1 \cdots \alpha_{i-1} b \alpha_{i+1} \cdots, j)$$

如果 $\delta(q, a) = (p, b, D)$ 且 $j = i + \text{offset}(D)$。

-**定义 5.1.4 (图灵机接受)**
图灵机接受字符串 $w$，如果 $(q_0, w, 0) \vdash^* (q, \alpha, i)$ 且 $q \in F$。

-**算法 5.1.1 (图灵机模拟)**

```haskell
simulateTuringMachine :: TuringMachine -> String -> Bool
simulateTuringMachine tm input = 
  let initialConfig = (initialState tm, input, 0)
      finalConfigs = reachableConfigs tm initialConfig
      acceptingConfigs = filter isAccepting finalConfigs
  in not (null acceptingConfigs)

reachableConfigs :: TuringMachine -> Config -> [Config]
reachableConfigs tm config = 
  let nextConfigs = nextConfigurations tm config
      allConfigs = config : concatMap (reachableConfigs tm) nextConfigs
  in nub allConfigs
```

### 5.2 图灵机变种

-**定义 5.2.1 (多带图灵机)**
多带图灵机有多个磁带，每个磁带有自己的读写头。

**定理 5.2.1 (多带图灵机等价性)**
多带图灵机和单带图灵机等价。

**证明：** 通过模拟构造：

1. 单带图灵机可以模拟多带图灵机
2. 通过交错存储和标记位置
3. 模拟每个转移步骤

-**定义 5.2.2 (非确定性图灵机)**
非确定性图灵机的转移函数：
$$\delta : Q \times \Gamma \rightarrow 2^{Q \times \Gamma \times \{L, R\}}$$

**定理 5.2.2 (非确定性图灵机等价性)**
非确定性图灵机和确定性图灵机等价。

**证明：** 通过模拟构造：

1. 确定性图灵机可以模拟非确定性图灵机
2. 通过广度优先搜索所有可能路径
3. 使用三带图灵机进行模拟

### 5.3 可计算性理论

-**定义 5.3.1 (可计算函数)**
函数 $f : \Sigma^* \rightarrow \Sigma^*$ 是可计算的，如果存在图灵机 $M$ 使得对于任意输入 $w$，$M$ 停机并输出 $f(w)$。

-**定义 5.3.2 (可判定语言)**
语言 $L$ 是可判定的，如果存在图灵机 $M$ 使得：

- 如果 $w \in L$，则 $M$ 接受 $w$
- 如果 $w \notin L$，则 $M$ 拒绝 $w$

-**定义 5.3.3 (可识别语言)**
语言 $L$ 是可识别的，如果存在图灵机 $M$ 使得：

- 如果 $w \in L$，则 $M$ 接受 $w$
- 如果 $w \notin L$，则 $M$ 要么拒绝 $w$ 要么永不停机

**定理 5.3.1 (停机问题不可判定性)**
停机问题是不可判定的。

**证明：** 通过对角化方法：

1. 假设存在图灵机 $H$ 判定停机问题
2. 构造图灵机 $D$ 使得 $D$ 在输入 $\langle D \rangle$ 上的行为与 $H$ 的预测相反
3. 矛盾，因此停机问题不可判定

## 6. 语法分析理论

### 6.1 自顶向下分析

-**定义 6.1.1 (递归下降分析)**
递归下降分析是自顶向下的语法分析方法，为每个非终结符编写一个递归函数。

-**算法 6.1.1 (递归下降分析器)**

```haskell
recursiveDescentParser :: CFG -> String -> ParseTree
recursiveDescentParser cfg input = 
  let tokens = tokenize input
      parseTree = parseStartSymbol cfg tokens
  in parseTree

parseStartSymbol :: CFG -> [Token] -> ParseTree
parseStartSymbol cfg tokens = 
  let startSymbol = startSymbol cfg
  in parseNonTerminal cfg startSymbol tokens

parseNonTerminal :: CFG -> NonTerminal -> [Token] -> ParseTree
parseNonTerminal cfg nt tokens = 
  let productions = getProductions cfg nt
      (production, remainingTokens) = selectProduction productions tokens
      children = parseProduction cfg production remainingTokens
  in Node nt children
```

-**定义 6.1.2 (LL(k)文法)**
LL(k)文法满足：对于任意两个不同的产生式 $A \rightarrow \alpha$ 和 $A \rightarrow \beta$，$FIRST_k(\alpha) \cap FIRST_k(\beta) = \emptyset$。

-**算法 6.1.2 (LL(1)分析器)**

```haskell
ll1Parser :: CFG -> String -> ParseTree
ll1Parser cfg input = 
  let tokens = tokenize input
      parseTable = buildLL1Table cfg
      parseTree = parseWithTable parseTable tokens
  in parseTree

buildLL1Table :: CFG -> ParseTable
buildLL1Table cfg = 
  let firstSets = computeFirstSets cfg
      followSets = computeFollowSets cfg firstSets
      table = buildTable cfg firstSets followSets
  in table
```

### 6.2 自底向上分析

-**定义 6.2.1 (LR分析)**
LR分析是自底向上的语法分析方法，使用状态机进行移进-归约操作。

-**定义 6.2.2 (LR(0)项)**
LR(0)项是形如 $A \rightarrow \alpha \cdot \beta$ 的产生式，其中 $\cdot$ 表示分析位置。

-**定义 6.2.3 (LR(0)自动机)**
LR(0)自动机的状态是LR(0)项的集合，转移通过移进和闭包操作定义。

-**算法 6.2.1 (LR分析器)**

```haskell
lrParser :: CFG -> String -> ParseTree
lrParser cfg input = 
  let tokens = tokenize input
      actionTable = buildActionTable cfg
      gotoTable = buildGotoTable cfg
      parseTree = parseWithTables actionTable gotoTable tokens
  in parseTree

parseWithTables :: ActionTable -> GotoTable -> [Token] -> ParseTree
parseWithTables actionTable gotoTable tokens = 
  let initialState = 0
      stack = [(initialState, [])]
      parseTree = parseStep actionTable gotoTable stack tokens
  in parseTree
```

### 6.3 语法分析算法

-**算法 6.3.1 (CYK算法)**
CYK算法是动态规划算法，用于判定字符串是否属于CFL。

```haskell
cykAlgorithm :: CFG -> String -> Bool
cykAlgorithm cfg input = 
  let n = length input
      table = array ((0,0), (n-1,n-1)) [((i,j), []) | i <- [0..n-1], j <- [0..n-1]]
      filledTable = fillTable cfg input table
      startSymbol = startSymbol cfg
  in startSymbol `elem` (filledTable ! (0, n-1))

fillTable :: CFG -> String -> Array (Int,Int) [NonTerminal] -> Array (Int,Int) [NonTerminal]
fillTable cfg input table = 
  let n = length input
      table1 = fillDiagonal cfg input table
      table2 = fillUpperTriangle cfg table1
  in table2
```

## 7. 语义理论

### 7.1 操作语义

-**定义 7.1.1 (小步语义)**
小步语义定义程序执行的基本步骤：
$$\frac{\text{premise}}{\text{conclusion}}$$

-**定义 7.1.2 (大步语义)**
大步语义定义程序的整体执行：
$$e \Downarrow v$$

-**定义 7.1.3 (自然语义)**
自然语义结合了小步和大步语义的特点。

### 7.2 指称语义

-**定义 7.2.1 (语义域)**
语义域是程序含义的数学表示。

-**定义 7.2.2 (语义函数)**
语义函数将语法结构映射到语义域：
$$\llbracket e \rrbracket : \text{Env} \rightarrow \text{Value}$$

### 7.3 公理语义

-**定义 7.3.1 (霍尔逻辑)**
霍尔逻辑用于程序正确性证明：
$$\{P\} \text{ } C \text{ } \{Q\}$$

-**定义 7.3.2 (最弱前置条件)**
最弱前置条件 $wp(C, Q)$ 是使得执行 $C$ 后满足 $Q$ 的最弱条件。

## 8. 计算复杂性

### 8.1 时间复杂性

-**定义 8.1.1 (时间复杂性)**
图灵机 $M$ 在输入 $w$ 上的时间复杂性是 $M$ 在 $w$ 上的步数。

-**定义 8.1.2 (时间复杂度类)**
时间复杂度类：

- $P$：多项式时间可判定语言
- $NP$：非确定性多项式时间可判定语言
- $EXP$：指数时间可判定语言

### 8.2 空间复杂性

-**定义 8.2.1 (空间复杂性)**
图灵机 $M$ 在输入 $w$ 上的空间复杂性是 $M$ 在 $w$ 上使用的磁带格子数。

-**定义 8.2.2 (空间复杂度类)**
空间复杂度类：

- $L$：对数空间可判定语言
- $PSPACE$：多项式空间可判定语言

### 8.3 复杂性理论

**定理 8.3.1 (时间层次定理)**
对于时间可构造函数 $t(n)$，如果 $t(n) = o(t'(n))$，则 $DTIME(t(n)) \subset DTIME(t'(n))$。

**定理 8.3.2 (空间层次定理)**
对于空间可构造函数 $s(n)$，如果 $s(n) = o(s'(n))$，则 $DSPACE(s(n)) \subset DSPACE(s'(n))$。

**定理 8.3.3 (萨维奇定理)**
$NSPACE(s(n)) \subseteq DSPACE(s^2(n))$。

## 结论

形式语言理论为计算机科学提供了完整的语言处理框架，从基础的自动机理论到高级的语法分析算法，涵盖了：

1. **语言分类**: 乔姆斯基层次结构
2. **自动机理论**: DFA、NFA、PDA、图灵机
3. **文法理论**: CFG、CNF、GNF
4. **语法分析**: 自顶向下、自底向上方法
5. **语义理论**: 操作语义、指称语义、公理语义
6. **计算复杂性**: 时间复杂性、空间复杂性

这些理论为编译器设计、自然语言处理、程序验证等领域提供了坚实的理论基础。

## 参考文献

1. Hopcroft, J. E., Motwani, R., & Ullman, J. D. (2006). *Introduction to automata theory, languages, and computation*. Pearson Education.
2. Sipser, M. (2012). *Introduction to the theory of computation*. Cengage Learning.
3. Aho, A. V., Lam, M. S., Sethi, R., & Ullman, J. D. (2006). *Compilers: principles, techniques, and tools*. Pearson Education.
4. Kozen, D. C. (2006). *Automata and computability*. Springer Science & Business Media.
5. Lewis, H. R., & Papadimitriou, C. H. (1998). *Elements of the theory of computation*. Prentice Hall.
6. Grune, D., & Jacobs, C. J. (2008). *Parsing techniques: a practical guide*. Springer Science & Business Media.
7. Winskel, G. (1993). *The formal semantics of programming languages: an introduction*. MIT press.

---

**最后更新**: 2024年12月19日  
**版本**: v1.0  
**状态**: 完成形式语言理论基础重构
