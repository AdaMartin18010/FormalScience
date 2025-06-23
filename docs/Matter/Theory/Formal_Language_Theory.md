# 形式语言理论 (Formal Language Theory)

## 1. 基础概念

### 1.1 字母表和语言

-**定义 1.1 (字母表)**
字母表 $\Sigma$ 是有限符号集合。

-**定义 1.2 (字符串)**
字符串是字母表中符号的有限序列：
$$w = a_1 a_2 \cdots a_n \text{ where } a_i \in \Sigma$$

-**定义 1.3 (字符串操作)**

- **连接**：$w_1 \cdot w_2 = w_1 w_2$
- **幂运算**：$w^0 = \epsilon$, $w^{n+1} = w \cdot w^n$
- **长度**：$|w| = n$ 对于 $w = a_1 a_2 \cdots a_n$

-**定义 1.4 (语言)**
语言 $L$ 是字符串集合：$L \subseteq \Sigma^*$

-**定义 1.5 (语言操作)**

- **并集**：$L_1 \cup L_2 = \{w \mid w \in L_1 \text{ or } w \in L_2\}$
- **连接**：$L_1 \cdot L_2 = \{w_1 w_2 \mid w_1 \in L_1, w_2 \in L_2\}$
- **克林闭包**：$L^* = \bigcup_{n=0}^{\infty} L^n$

### 1.2 乔姆斯基层次结构

-**定义 1.6 (乔姆斯基层次)**
语言类别的层次结构：

1. **正则语言**：有限状态自动机识别
2. **上下文无关语言**：下推自动机识别
3. **上下文有关语言**：线性有界自动机识别
4. **递归可枚举语言**：图灵机识别

**定理 1.1 (层次包含关系)**
$$\text{Regular} \subset \text{CFL} \subset \text{CSL} \subset \text{REL}$$

**证明：** 通过构造性证明：

1. 每个层次包含前一个层次
2. 存在语言属于更高层次但不属于较低层次
3. 通过泵引理证明严格包含

## 2. 有限状态自动机

### 2.1 确定性有限自动机

-**定义 2.1 (DFA)**
确定性有限自动机是五元组 $M = (Q, \Sigma, \delta, q_0, F)$，其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是输入字母表
- $\delta : Q \times \Sigma \rightarrow Q$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $F \subseteq Q$ 是接受状态集合

-**定义 2.2 (DFA计算)**
DFA在输入 $w = a_1 a_2 \cdots a_n$ 上的计算：
$$q_0 \xrightarrow{a_1} q_1 \xrightarrow{a_2} q_2 \cdots \xrightarrow{a_n} q_n$$

其中 $q_{i+1} = \delta(q_i, a_{i+1})$。

-**定义 2.3 (DFA接受)**
DFA接受字符串 $w$，如果计算结束于接受状态：$q_n \in F$。

-**算法 2.1 (DFA模拟)**

```haskell
simulateDFA :: DFA -> String -> Bool
simulateDFA dfa input = 
  let finalState = foldl (transition dfa) (initialState dfa) input
  in finalState `elem` (acceptingStates dfa)

transition :: DFA -> State -> Char -> State
transition dfa currentState symbol = 
  delta dfa currentState symbol
```

### 2.2 非确定性有限自动机

-**定义 2.4 (NFA)**
非确定性有限自动机是五元组 $M = (Q, \Sigma, \delta, q_0, F)$，其中：

- $\delta : Q \times \Sigma \rightarrow 2^Q$ 是转移函数

-**定义 2.5 (NFA计算)**
NFA在输入 $w$ 上的计算是一棵树，每个节点表示可能的状态。

**定理 2.1 (DFA与NFA等价性)**
对于每个NFA，存在等价的DFA。

**证明：** 通过子集构造：

1. DFA状态是NFA状态集合
2. DFA转移函数通过子集计算
3. 接受状态包含NFA接受状态

-**算法 2.2 (子集构造)**

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
```

### 2.3 正则表达式

-**定义 2.6 (正则表达式)**
正则表达式的语法：
$$R ::= \emptyset \mid \epsilon \mid a \mid R_1 + R_2 \mid R_1 \cdot R_2 \mid R^*$$

-**定义 2.7 (正则表达式语义)**

- $L(\emptyset) = \emptyset$
- $L(\epsilon) = \{\epsilon\}$
- $L(a) = \{a\}$
- $L(R_1 + R_2) = L(R_1) \cup L(R_2)$
- $L(R_1 \cdot R_2) = L(R_1) \cdot L(R_2)$
- $L(R^*) = L(R)^*$

**定理 2.2 (正则表达式与DFA等价性)**
正则表达式和DFA识别相同的语言类。

**证明：** 双向构造：

1. 正则表达式到NFA：通过递归构造
2. NFA到DFA：通过子集构造
3. DFA到正则表达式：通过状态消除

## 3. 上下文无关文法

### 3.1 文法定义

-**定义 3.1 (CFG)**
上下文无关文法是四元组 $G = (V, T, P, S)$，其中：

- $V$ 是非终结符集合
- $T$ 是终结符集合
- $P$ 是产生式集合
- $S \in V$ 是开始符号

-**定义 3.2 (推导)**
推导关系 $\Rightarrow$ 定义：

- 如果 $A \rightarrow \alpha \in P$，则 $\beta A \gamma \Rightarrow \beta \alpha \gamma$
- 如果 $\alpha \Rightarrow \beta$ 且 $\beta \Rightarrow \gamma$，则 $\alpha \Rightarrow \gamma$

-**定义 3.3 (语言生成)**
文法 $G$ 生成的语言：
$$L(G) = \{w \in T^* \mid S \Rightarrow^* w\}$$

-**算法 3.1 (CFG解析)**

```haskell
parseCFG :: CFG -> String -> Bool
parseCFG cfg input = 
  let startSymbol = startSymbol cfg
      derivations = generateDerivations cfg startSymbol
      terminalStrings = filter isTerminal derivations
  in input `elem` terminalStrings
```

### 3.2 乔姆斯基范式

-**定义 3.4 (CNF)**
乔姆斯基范式文法满足：

- 所有产生式形如 $A \rightarrow BC$ 或 $A \rightarrow a$
- 其中 $A, B, C \in V$ 且 $a \in T$

**定理 3.1 (CNF转换)**
每个CFG都可以转换为等价的CNF。

**证明：** 通过构造性转换：

1. 消除 $\epsilon$ 产生式
2. 消除单位产生式
3. 转换为CNF形式

-**算法 3.2 (CNF转换)**

```haskell
convertToCNF :: CFG -> CFG
convertToCNF cfg = 
  let cfg1 = eliminateEpsilon cfg
      cfg2 = eliminateUnit cfg1
      cfg3 = eliminateLong cfg2
  in cfg3
```

### 3.3 CYK算法

-**算法 3.3 (CYK算法)**

```haskell
cykParse :: CFG -> String -> Bool
cykParse cfg input = 
  let n = length input
      table = array ((0,0), (n-1,n-1)) []
      
      -- 初始化对角线
      table' = foldl (\t i -> t // [((i,i), findProductions cfg [input !! i])]) 
                     table [0..n-1]
      
      -- 填充表格
      finalTable = fillTable cfg table' n
      
      startSymbol = startSymbol cfg
  in startSymbol `elem` (finalTable ! (0, n-1))

fillTable :: CFG -> Array (Int,Int) [Symbol] -> Int -> Array (Int,Int) [Symbol]
fillTable cfg table n = 
  foldl (\t len -> 
    foldl (\t' i -> 
      let j = i + len - 1
          cells = [(i,k) | k <- [i..j-1]]
          symbols = concatMap (\k -> 
            let left = t' ! (i,k)
                right = t' ! (k+1,j)
            in findProductions cfg (left ++ right)) cells
      in t' // [((i,j), symbols)]) t [0..n-len]) table [2..n]
```

## 4. 下推自动机

### 4.1 PDA定义

-**定义 4.1 (PDA)**
下推自动机是七元组 $M = (Q, \Sigma, \Gamma, \delta, q_0, Z_0, F)$，其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是输入字母表
- $\Gamma$ 是栈字母表
- $\delta : Q \times (\Sigma \cup \{\epsilon\}) \times \Gamma \rightarrow 2^{Q \times \Gamma^*}$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $Z_0 \in \Gamma$ 是初始栈符号
- $F \subseteq Q$ 是接受状态集合

-**定义 4.2 (PDA配置)**
PDA配置是三元组 $(q, w, \gamma)$，其中：

- $q$ 是当前状态
- $w$ 是剩余输入
- $\gamma$ 是栈内容

-**定义 4.3 (PDA计算)**
PDA计算步骤：
$$(q, aw, A\gamma) \vdash (p, w, \beta\gamma)$$

如果 $(p, \beta) \in \delta(q, a, A)$。

-**算法 4.1 (PDA模拟)**

```haskell
simulatePDA :: PDA -> String -> Bool
simulatePDA pda input = 
  let initialConfig = (initialState pda, input, [initialStackSymbol pda])
      finalConfigs = computeAllConfigs pda initialConfig
      acceptingConfigs = filter isAccepting finalConfigs
  in not (null acceptingConfigs)
```

### 4.2 PDA与CFG等价性

**定理 4.1 (PDA与CFG等价性)**
下推自动机和上下文无关文法识别相同的语言类。

**证明：** 双向构造：

1. CFG到PDA：通过自顶向下或自底向上构造
2. PDA到CFG：通过配置转换构造

## 5. 图灵机

### 5.1 图灵机定义

-**定义 5.1 (图灵机)**
图灵机是七元组 $M = (Q, \Sigma, \Gamma, \delta, q_0, B, F)$，其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是输入字母表
- $\Gamma$ 是带字母表
- $\delta : Q \times \Gamma \rightarrow Q \times \Gamma \times \{L, R\}$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $B \in \Gamma$ 是空白符号
- $F \subseteq Q$ 是接受状态集合

-**定义 5.2 (图灵机配置)**
图灵机配置是三元组 $(q, \alpha, i)$，其中：

- $q$ 是当前状态
- $\alpha$ 是带内容
- $i$ 是读写头位置

-**定义 5.3 (图灵机计算)**
图灵机计算步骤：
$$(q, \alpha, i) \vdash (p, \alpha', j)$$

如果 $\delta(q, \alpha_i) = (p, b, D)$ 且：

- $\alpha'_i = b$
- $j = i + 1$ 如果 $D = R$
- $j = i - 1$ 如果 $D = L$

-**算法 5.1 (图灵机模拟)**

```haskell
simulateTuringMachine :: TuringMachine -> String -> Bool
simulateTuringMachine tm input = 
  let initialConfig = (initialState tm, input, 0)
      finalConfig = runComputation tm initialConfig
  in isAccepting tm finalConfig

runComputation :: TuringMachine -> Config -> Config
runComputation tm config = 
  if isHalted tm config
    then config
    else runComputation tm (step tm config)
```

### 5.2 图灵机变种

-**定义 5.4 (非确定性图灵机)**
非确定性图灵机的转移函数：
$$\delta : Q \times \Gamma \rightarrow 2^{Q \times \Gamma \times \{L, R\}}$$

-**定义 5.5 (多带图灵机)**
多带图灵机有多个读写头，可以同时操作多个带。

**定理 5.1 (图灵机等价性)**
确定性图灵机、非确定性图灵机和多带图灵机具有相同的计算能力。

**证明：** 通过模拟：

1. 非确定性图灵机可以模拟确定性图灵机
2. 确定性图灵机可以模拟非确定性图灵机
3. 多带图灵机可以相互模拟

## 6. 计算复杂性

### 6.1 时间复杂性

-**定义 6.1 (时间复杂性)**
图灵机 $M$ 的时间复杂性：
$$T_M(n) = \max\{t \mid M \text{ 在长度为 } n \text{ 的输入上运行 } t \text{ 步}\}$$

-**定义 6.2 (复杂性类)**

- **P**：多项式时间可解的问题
- **NP**：非确定性多项式时间可解的问题
- **PSPACE**：多项式空间可解的问题

**定理 6.1 (P与NP关系)**
$P \subseteq NP$，但 $P = NP$ 是否成立是未解决的问题。

### 6.2 空间复杂性

-**定义 6.3 (空间复杂性)**
图灵机 $M$ 的空间复杂性：
$$S_M(n) = \max\{s \mid M \text{ 在长度为 } n \text{ 的输入上使用 } s \text{ 个带单元}\}$$

**定理 6.2 (空间层次定理)**
对于任何空间可构造函数 $f$，存在语言 $L$ 在空间 $O(f(n))$ 中可解，但在空间 $o(f(n))$ 中不可解。

## 7. 实际应用

### 7.1 编译器设计

-**定义 7.1 (词法分析)**
词法分析器将输入字符串转换为词法单元序列：

```haskell
lexicalAnalysis :: String -> [Token]
lexicalAnalysis input = 
  let dfa = buildLexicalDFA
      tokens = tokenize dfa input
  in tokens
```

-**定义 7.2 (语法分析)**
语法分析器构建抽象语法树：

```haskell
syntaxAnalysis :: [Token] -> AST
syntaxAnalysis tokens = 
  let cfg = buildGrammar
      ast = parse cfg tokens
  in ast
```

### 7.2 自然语言处理

-**定义 7.3 (句法分析)**
句法分析识别句子结构：

```haskell
syntacticAnalysis :: String -> ParseTree
syntacticAnalysis sentence = 
  let grammar = buildNaturalLanguageGrammar
      parseTree = parse grammar sentence
  in parseTree
```

## 8. 结论

形式语言理论为计算机科学提供了强大的理论基础：

1. **语言分类**：通过乔姆斯基层次分类语言
2. **自动机理论**：提供语言识别的计算模型
3. **语法分析**：支持程序语言和自然语言处理
4. **计算复杂性**：分析算法的效率和可解性

形式语言理论在以下领域发挥着关键作用：

- 编译器设计和实现
- 自然语言处理
- 软件工程和程序验证
- 人工智能和机器学习

通过形式化的语言理论，我们可以：

- 设计高效的解析算法
- 验证程序的语法正确性
- 分析计算问题的复杂性
- 构建智能的语言处理系统
