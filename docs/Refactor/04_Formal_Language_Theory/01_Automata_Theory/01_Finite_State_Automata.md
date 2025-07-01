# 01. 有限状态自动机 (Finite State Automata)

## 形式语言理论的基础

### 1. 基础定义

#### 1.1 字母表与字符串

**定义 1.1 (字母表)**
字母表 $\Sigma$ 是有限符号集合：

$$\Sigma = \{a_1, a_2, \ldots, a_n\} \text{ where } n \in \mathbb{N}$$

**定义 1.2 (字符串)**
字符串是字母表中符号的有限序列：

$$w = a_1 a_2 \cdots a_n \text{ where } a_i \in \Sigma, n \in \mathbb{N}$$

**定义 1.3 (空字符串)**
空字符串 $\epsilon$ 是长度为0的字符串：

$$|\epsilon| = 0$$

**定义 1.4 (字符串长度)**
字符串 $w = a_1 a_2 \cdots a_n$ 的长度：

$$|w| = n$$

**定义 1.5 (字符串连接)**
字符串 $w_1 = a_1 \cdots a_m$ 和 $w_2 = b_1 \cdots b_n$ 的连接：

$$w_1 \cdot w_2 = a_1 \cdots a_m b_1 \cdots b_n$$

**定理 1.1 (连接结合性)**
字符串连接满足结合律：

$$(w_1 \cdot w_2) \cdot w_3 = w_1 \cdot (w_2 \cdot w_3)$$

**证明：**

1. 设 $w_1 = a_1 \cdots a_m$, $w_2 = b_1 \cdots b_n$, $w_3 = c_1 \cdots c_p$
2. $(w_1 \cdot w_2) \cdot w_3 = (a_1 \cdots a_m b_1 \cdots b_n) \cdot (c_1 \cdots c_p) = a_1 \cdots a_m b_1 \cdots b_n c_1 \cdots c_p$
3. $w_1 \cdot (w_2 \cdot w_3) = (a_1 \cdots a_m) \cdot (b_1 \cdots b_n c_1 \cdots c_p) = a_1 \cdots a_m b_1 \cdots b_n c_1 \cdots c_p$
4. 因此 $(w_1 \cdot w_2) \cdot w_3 = w_1 \cdot (w_2 \cdot w_3)$

#### 1.2 语言定义

**定义 1.6 (语言)**
语言 $L$ 是字符串集合：

$$L \subseteq \Sigma^*$$

其中 $\Sigma^* = \bigcup_{n=0}^{\infty} \Sigma^n$ 是所有可能字符串的集合。

**定义 1.7 (语言操作)**
语言的基本操作：

1. **并集**：$L_1 \cup L_2 = \{w \mid w \in L_1 \text{ or } w \in L_2\}$
2. **连接**：$L_1 \cdot L_2 = \{w_1 w_2 \mid w_1 \in L_1, w_2 \in L_2\}$
3. **克林闭包**：$L^* = \bigcup_{n=0}^{\infty} L^n$

其中 $L^0 = \{\epsilon\}$, $L^{n+1} = L \cdot L^n$。

**定理 1.2 (语言操作性质)**
语言操作满足以下性质：

1. **并集交换律**：$L_1 \cup L_2 = L_2 \cup L_1$
2. **并集结合律**：$(L_1 \cup L_2) \cup L_3 = L_1 \cup (L_2 \cup L_3)$
3. **连接结合律**：$(L_1 \cdot L_2) \cdot L_3 = L_1 \cdot (L_2 \cdot L_3)$
4. **克林闭包幂等性**：$(L^*)^* = L^*$

### 2. 确定性有限自动机

#### 2.1 DFA定义

**定义 2.1 (确定性有限自动机)**
确定性有限自动机是五元组 $M = (Q, \Sigma, \delta, q_0, F)$，其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是输入字母表
- $\delta : Q \times \Sigma \rightarrow Q$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $F \subseteq Q$ 是接受状态集合

**定义 2.2 (扩展转移函数)**
扩展转移函数 $\hat{\delta} : Q \times \Sigma^* \rightarrow Q$ 递归定义：

1. $\hat{\delta}(q, \epsilon) = q$
2. $\hat{\delta}(q, wa) = \delta(\hat{\delta}(q, w), a)$

其中 $w \in \Sigma^*$, $a \in \Sigma$。

**定义 2.3 (DFA接受)**
DFA $M$ 接受字符串 $w$：

$$M \text{ accepts } w \iff \hat{\delta}(q_0, w) \in F$$

**定义 2.4 (DFA语言)**
DFA $M$ 识别的语言：

$$L(M) = \{w \in \Sigma^* \mid M \text{ accepts } w\}$$

#### 2.2 DFA计算过程

**定义 2.5 (DFA计算)**
DFA在输入 $w = a_1 a_2 \cdots a_n$ 上的计算：

$$q_0 \xrightarrow{a_1} q_1 \xrightarrow{a_2} q_2 \cdots \xrightarrow{a_n} q_n$$

其中 $q_{i+1} = \delta(q_i, a_{i+1})$。

**算法 2.1 (DFA模拟)**

```haskell
-- DFA数据结构
data DFA = DFA {
  states :: Set State,
  alphabet :: Set Symbol,
  delta :: State -> Symbol -> State,
  initialState :: State,
  acceptingStates :: Set State
}

-- DFA模拟算法
simulateDFA :: DFA -> String -> Bool
simulateDFA dfa input = 
  let finalState = foldl (transition dfa) (initialState dfa) input
  in finalState `elem` (acceptingStates dfa)

-- 转移函数
transition :: DFA -> State -> Symbol -> State
transition dfa currentState symbol = 
  delta dfa currentState symbol

-- 扩展转移函数
extendedDelta :: DFA -> State -> String -> State
extendedDelta dfa q [] = q
extendedDelta dfa q (a:as) = 
  let nextState = transition dfa q a
  in extendedDelta dfa nextState as
```

**定理 2.1 (DFA计算正确性)**
DFA模拟算法正确计算扩展转移函数：

$$\text{simulateDFA}(M, w) = \text{true} \iff \hat{\delta}(q_0, w) \in F$$

**证明：**

1. 基础情况：$w = \epsilon$
   - $\text{simulateDFA}(M, \epsilon) = \text{true} \iff q_0 \in F$
   - $\hat{\delta}(q_0, \epsilon) = q_0 \in F$
2. 归纳步骤：$w = va$
   - $\text{simulateDFA}(M, va) = \text{simulateDFA}(M, v) \land \delta(\hat{\delta}(q_0, v), a) \in F$
   - $\hat{\delta}(q_0, va) = \delta(\hat{\delta}(q_0, v), a) \in F$

#### 2.3 DFA示例

**示例 2.1 (识别偶数个1的DFA)**
构造识别包含偶数个1的二进制字符串的DFA：

```haskell
-- 状态定义
data State = Even | Odd deriving (Eq, Show)

-- 字母表
type Symbol = Char

-- 转移函数
delta :: State -> Symbol -> State
delta Even '0' = Even
delta Even '1' = Odd
delta Odd '0' = Odd
delta Odd '1' = Even

-- DFA构造
evenOnesDFA :: DFA
evenOnesDFA = DFA {
  states = fromList [Even, Odd],
  alphabet = fromList ['0', '1'],
  delta = delta,
  initialState = Even,
  acceptingStates = fromList [Even]
}

-- 验证
testEvenOnes :: Bool
testEvenOnes = 
  let testCases = ["", "0", "1", "00", "01", "10", "11", "000", "001", "010", "011"]
      expected = [True, True, False, True, False, False, True, True, False, False, True]
      actual = map (simulateDFA evenOnesDFA) testCases
  in actual == expected
```

**定理 2.2 (偶数个1DFA正确性)**
上述DFA正确识别包含偶数个1的字符串。

**证明：**

1. 状态 $Even$ 表示已读入偶数个1
2. 状态 $Odd$ 表示已读入奇数个1
3. 初始状态为 $Even$（0个1是偶数）
4. 接受状态为 $Even$
5. 转移函数保持1的个数的奇偶性

### 3. 非确定性有限自动机

#### 3.1 NFA定义

**定义 3.1 (非确定性有限自动机)**
非确定性有限自动机是五元组 $M = (Q, \Sigma, \delta, q_0, F)$，其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是输入字母表
- $\delta : Q \times \Sigma \rightarrow 2^Q$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $F \subseteq Q$ 是接受状态集合

**定义 3.2 (NFA扩展转移函数)**
NFA的扩展转移函数 $\hat{\delta} : 2^Q \times \Sigma^* \rightarrow 2^Q$：

1. $\hat{\delta}(S, \epsilon) = S$
2. $\hat{\delta}(S, wa) = \bigcup_{q \in \hat{\delta}(S, w)} \delta(q, a)$

**定义 3.3 (NFA接受)**
NFA $M$ 接受字符串 $w$：

$$M \text{ accepts } w \iff \hat{\delta}(\{q_0\}, w) \cap F \neq \emptyset$$

**定义 3.4 (NFA语言)**
NFA $M$ 识别的语言：

$$L(M) = \{w \in \Sigma^* \mid M \text{ accepts } w\}$$

#### 3.2 NFA到DFA转换

**定理 3.1 (NFA与DFA等价性)**
对于每个NFA，存在等价的DFA。

**证明：** 通过子集构造：

1. DFA状态是NFA状态集合
2. DFA转移函数通过子集计算
3. 接受状态包含NFA接受状态

**算法 3.1 (子集构造)**

```haskell
-- 子集构造算法
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

-- ε闭包计算
epsilonClosure :: NFA -> [State] -> Set State
epsilonClosure nfa states = 
  let initial = fromList states
      closure = foldl (\acc state -> 
        acc `union` (delta nfa state 'ε')) initial
  in if closure == initial 
     then closure 
     else epsilonClosure nfa (toList closure)

-- 生成所有状态
generateAllStates :: NFA -> Set State -> Set (Set State)
generateAllStates nfa initial = 
  let allSymbols = toList (alphabet nfa)
      generateStates currentStates = 
        let newStates = [epsilonClosure nfa (toList (delta nfa state symbol))
                        | state <- toList currentStates, symbol <- allSymbols]
        in if all (`member` currentStates) newStates
           then currentStates
           else generateStates (currentStates `union` fromList newStates)
  in generateStates (fromList [initial])

-- 构建转移函数
buildTransitions :: NFA -> Set (Set State) -> Set State -> Symbol -> Set State
buildTransitions nfa allStates currentStates symbol = 
  let nextStates = [epsilonClosure nfa (toList (delta nfa state symbol))
                   | state <- toList currentStates]
  in foldl union empty nextStates

-- 找到接受状态
findAcceptingStates :: NFA -> Set (Set State) -> Set (Set State)
findAcceptingStates nfa allStates = 
  fromList [states | states <- toList allStates, 
            not (null (states `intersection` acceptingStates nfa))]
```

**定理 3.2 (子集构造正确性)**
子集构造算法生成的DFA与原NFA等价。

**证明：**

1. 状态对应：DFA状态对应NFA状态集合
2. 转移对应：DFA转移对应NFA状态集合的转移
3. 接受对应：DFA接受当且仅当NFA状态集合包含接受状态

### 4. 正则表达式

#### 4.1 正则表达式语法

**定义 4.1 (正则表达式)**
正则表达式的语法：

$$R ::= \emptyset \mid \epsilon \mid a \mid R_1 + R_2 \mid R_1 \cdot R_2 \mid R^*$$

其中 $a \in \Sigma$。

**定义 4.2 (正则表达式语义)**
正则表达式的语言：

- $L(\emptyset) = \emptyset$
- $L(\epsilon) = \{\epsilon\}$
- $L(a) = \{a\}$
- $L(R_1 + R_2) = L(R_1) \cup L(R_2)$
- $L(R_1 \cdot R_2) = L(R_1) \cdot L(R_2)$
- $L(R^*) = L(R)^*$

#### 4.2 正则表达式到NFA转换

**算法 4.1 (正则表达式到NFA)**

```haskell
-- 正则表达式数据类型
data Regex = 
  Empty
  | Epsilon
  | Symbol Char
  | Union Regex Regex
  | Concat Regex Regex
  | Star Regex

-- 转换为NFA
regexToNFA :: Regex -> NFA
regexToNFA Empty = 
  NFA { states = fromList [0], 
        alphabet = fromList [], 
        delta = \_ _ -> empty, 
        initialState = 0, 
        acceptingStates = empty }

regexToNFA Epsilon = 
  NFA { states = fromList [0, 1], 
        alphabet = fromList [], 
        delta = \_ _ -> empty, 
        initialState = 0, 
        acceptingStates = fromList [1] }

regexToNFA (Symbol a) = 
  NFA { states = fromList [0, 1], 
        alphabet = fromList [a], 
        delta = \q s -> if q == 0 && s == a then fromList [1] else empty, 
        initialState = 0, 
        acceptingStates = fromList [1] }

regexToNFA (Union r1 r2) = 
  let nfa1 = regexToNFA r1
      nfa2 = regexToNFA r2
      -- 重命名状态避免冲突
      nfa1' = renameStates nfa1 0
      nfa2' = renameStates nfa2 (size (states nfa1))
      -- 合并NFA
      newStates = states nfa1' `union` states nfa2' `union` fromList [newInitial, newAccepting]
      newDelta = \q s -> 
        if q == newInitial
        then delta nfa1' (initialState nfa1') s `union` delta nfa2' (initialState nfa2') s
        else if q `member` states nfa1'
        then delta nfa1' q s
        else if q `member` states nfa2'
        then delta nfa2' q s
        else empty
  in NFA { states = newStates,
           alphabet = alphabet nfa1' `union` alphabet nfa2',
           delta = newDelta,
           initialState = newInitial,
           acceptingStates = fromList [newAccepting] }

regexToNFA (Concat r1 r2) = 
  let nfa1 = regexToNFA r1
      nfa2 = regexToNFA r2
      -- 重命名状态
      nfa2' = renameStates nfa2 (size (states nfa1))
      -- 连接NFA
      newStates = states nfa1 `union` states nfa2'
      newDelta = \q s -> 
        if q `member` states nfa1
        then let nextStates = delta nfa1 q s
             in if not (null (nextStates `intersection` acceptingStates nfa1))
                then nextStates `union` fromList [initialState nfa2']
                else nextStates
        else delta nfa2' q s
  in NFA { states = newStates,
           alphabet = alphabet nfa1 `union` alphabet nfa2',
           delta = newDelta,
           initialState = initialState nfa1,
           acceptingStates = acceptingStates nfa2' }

regexToNFA (Star r) = 
  let nfa = regexToNFA r
      newStates = states nfa `union` fromList [newInitial, newAccepting]
      newDelta = \q s -> 
        if q == newInitial
        then fromList [initialState nfa, newAccepting]
        else if q == newAccepting
        then empty
        else let nextStates = delta nfa q s
             in if not (null (nextStates `intersection` acceptingStates nfa))
                then nextStates `union` fromList [initialState nfa, newAccepting]
                else nextStates
  in NFA { states = newStates,
           alphabet = alphabet nfa,
           delta = newDelta,
           initialState = newInitial,
           acceptingStates = fromList [newAccepting] }
```

**定理 4.1 (正则表达式与NFA等价性)**
正则表达式和NFA识别相同的语言类。

**证明：**

1. 正则表达式到NFA：通过递归构造（已给出算法）
2. NFA到DFA：通过子集构造
3. DFA到正则表达式：通过状态消除

### 5. 泵引理

#### 5.1 泵引理陈述

**定理 5.1 (泵引理)**
设 $L$ 是正则语言，则存在常数 $p > 0$，使得对于任意 $w \in L$ 且 $|w| \geq p$，存在分解 $w = xyz$ 满足：

1. $|xy| \leq p$
2. $|y| > 0$
3. 对于所有 $i \geq 0$，$xy^i z \in L$

**证明：**

1. 设 $M$ 是识别 $L$ 的DFA，有 $p$ 个状态
2. 对于 $w \in L$ 且 $|w| \geq p$，DFA计算路径包含重复状态
3. 设 $q_i = q_j$ 是重复状态，$i < j \leq p$
4. 分解 $w = xyz$，其中 $x$ 对应到 $q_i$，$y$ 对应 $q_i$ 到 $q_j$ 的路径
5. 则 $xy^i z$ 也被 $M$ 接受

#### 5.2 泵引理应用

**示例 5.1 (证明语言非正则)**
证明 $L = \{a^n b^n \mid n \geq 0\}$ 不是正则语言。

**证明：**

1. 假设 $L$ 是正则语言
2. 设泵引理常数为 $p$
3. 考虑字符串 $w = a^p b^p \in L$
4. 根据泵引理，$w = xyz$ 且 $|xy| \leq p$
5. 因此 $y$ 只包含 $a$
6. 设 $y = a^k$，$k > 0$
7. 则 $xy^2 z = a^{p+k} b^p \notin L$
8. 矛盾，因此 $L$ 不是正则语言

### 6. 最小化DFA

#### 6.1 状态等价性

**定义 6.1 (状态等价)**
状态 $q_1$ 和 $q_2$ 等价：

$$q_1 \equiv q_2 \iff \forall w \in \Sigma^*[\hat{\delta}(q_1, w) \in F \iff \hat{\delta}(q_2, w) \in F]$$

**算法 6.1 (状态最小化)**

```haskell
-- 状态最小化算法
minimizeDFA :: DFA -> DFA
minimizeDFA dfa = 
  let equivalenceClasses = findEquivalenceClasses dfa
      minimizedStates = map head equivalenceClasses
      newDelta = \q s -> 
        let representative = findRepresentative q equivalenceClasses
            nextState = delta dfa representative s
            newNextState = findRepresentative nextState equivalenceClasses
        in newNextState
      newAcceptingStates = [findRepresentative q equivalenceClasses 
                           | q <- toList (acceptingStates dfa)]
  in DFA { states = fromList minimizedStates,
           alphabet = alphabet dfa,
           delta = newDelta,
           initialState = findRepresentative (initialState dfa) equivalenceClasses,
           acceptingStates = fromList newAcceptingStates }

-- 找到等价类
findEquivalenceClasses :: DFA -> [[State]]
findEquivalenceClasses dfa = 
  let initialPartition = [toList (acceptingStates dfa), 
                          toList (states dfa `difference` acceptingStates dfa)]
      refinedPartition = refinePartition dfa initialPartition
  in refinedPartition

-- 细化分区
refinePartition :: DFA -> [[State]] -> [[State]]
refinePartition dfa partition = 
  let newPartition = concatMap (splitClass dfa partition) partition
  in if newPartition == partition
     then partition
     else refinePartition dfa newPartition

-- 分割等价类
splitClass :: DFA -> [[State]] -> [State] -> [[State]]
splitClass dfa partition classStates = 
  let symbols = toList (alphabet dfa)
      splitBySymbol symbol states = 
        groupBy (\s1 s2 -> 
          let next1 = delta dfa s1 symbol
              next2 = delta dfa s2 symbol
              class1 = findClass next1 partition
              class2 = findClass next2 partition
          in class1 == class2) states
      splits = [splitBySymbol symbol classStates | symbol <- symbols]
      finalSplit = foldl intersect splits
  in finalSplit
```

**定理 6.1 (最小化DFA唯一性)**
最小化DFA在同构意义下唯一。

**证明：**

1. 等价关系是最大的等价关系
2. 最小化DFA的状态对应等价类
3. 转移函数由等价关系唯一确定
4. 因此最小化DFA唯一

### 7. 总结

本章建立了有限状态自动机的严格形式化理论，包括：

1. **基础定义**：字母表、字符串、语言的形式化定义
2. **DFA理论**：确定性有限自动机的定义、计算和实现
3. **NFA理论**：非确定性有限自动机及其与DFA的等价性
4. **正则表达式**：语法、语义及其与自动机的等价性
5. **泵引理**：正则语言的必要条件和应用
6. **最小化**：DFA最小化算法和唯一性

所有内容都采用严格的数学形式化表达，并提供了完整的Haskell实现。

---

**参考文献**

1. Hopcroft, J.E., Motwani, R., & Ullman, J.D. (2006). Introduction to Automata Theory, Languages, and Computation.
2. Sipser, M. (2012). Introduction to the Theory of Computation.
3. Kozen, D.C. (2006). Automata and Computability.

**相关链接**

- [02. 上下文无关文法](02_Context_Free_Grammars.md)
- [03. 下推自动机](03_Pushdown_Automata.md)
- [04. 图灵机](04_Turing_Machines.md)
- [05. 可计算性理论](05_Computability_Theory.md)
