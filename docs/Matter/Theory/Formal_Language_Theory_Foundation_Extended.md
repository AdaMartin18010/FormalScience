# 形式语言理论基础扩展 (Formal Language Theory Foundation Extended)

## 🎯 **概述**

本文档构建了一个全面的形式语言理论基础体系，从基础的自动机理论到高级的语言理论，为编译器设计、自然语言处理和形式化验证提供坚实的理论基础。

## 1. 语言理论基础架构

### 1.1 语言层次结构深化

**定义 1.1 (扩展乔姆斯基层次)**
语言类别的完整层次结构：

1. **有限语言**：$\text{Finite} \subset \text{Regular}$
2. **正则语言**：$\text{Regular} \subset \text{CFL}$
3. **上下文无关语言**：$\text{CFL} \subset \text{CSL}$
4. **上下文有关语言**：$\text{CSL} \subset \text{REL}$
5. **递归可枚举语言**：$\text{REL} \subset \text{All}$

**定理 1.1 (层次严格性)**
每个包含关系都是严格的，即存在语言属于更高层次但不属于较低层次。

**证明：** 通过构造性证明：

1. **有限 vs 正则**：$L = \{a^n \mid n \text{ is prime}\}$ 是正则的但不是有限的
2. **正则 vs CFL**：$L = \{a^n b^n \mid n \geq 0\}$ 是CFL但不是正则的
3. **CFL vs CSL**：$L = \{a^n b^n c^n \mid n \geq 0\}$ 是CSL但不是CFL
4. **CSL vs REL**：$L = \{w \mid w \text{ encodes a halting computation}\}$ 是REL但不是CSL

### 1.2 语言操作代数

**定义 1.2 (语言代数)**
语言集合 $\mathcal{L}$ 上的代数结构：

- **并集**：$(L_1 \cup L_2)(w) = L_1(w) \lor L_2(w)$
- **交集**：$(L_1 \cap L_2)(w) = L_1(w) \land L_2(w)$
- **补集**：$\overline{L}(w) = \neg L(w)$
- **连接**：$(L_1 \cdot L_2)(w) = \exists w_1, w_2. w = w_1 w_2 \land L_1(w_1) \land L_2(w_2)$
- **克林闭包**：$L^*(w) = \exists n \geq 0. \exists w_1, \ldots, w_n. w = w_1 \cdots w_n \land \bigwedge_{i=1}^n L(w_i)$

**定理 1.2 (正则语言封闭性)**
正则语言在并集、交集、补集、连接和克林闭包下封闭。

**证明：** 通过构造性证明：

1. **并集**：通过NFA的并集构造
2. **交集**：通过DFA的乘积构造
3. **补集**：通过DFA的补集构造
4. **连接**：通过NFA的连接构造
5. **克林闭包**：通过NFA的克林闭包构造

## 2. 高级自动机理论

### 2.1 双向有限自动机

**定义 2.1 (双向DFA)**
双向确定性有限自动机是五元组 $M = (Q, \Sigma, \delta, q_0, F)$，其中：

- $\delta : Q \times \Sigma \rightarrow Q \times \{\text{left}, \text{right}\}$ 是转移函数
- 读头可以在输入带上左右移动

**定理 2.1 (双向DFA等价性)**
双向DFA与单向DFA识别相同的语言类。

**证明：** 通过模拟构造：

1. 双向DFA的配置可以用状态和位置表示
2. 单向DFA可以通过状态编码位置信息
3. 状态空间大小最多增加 $O(n)$ 倍

**算法 2.1 (双向DFA模拟)**

```haskell
data TwoWayDFA = TwoWayDFA {
  states :: Set State,
  alphabet :: Set Char,
  delta :: State -> Char -> (State, Direction),
  initialState :: State,
  acceptingStates :: Set State
}

data Direction = Left | Right

simulateTwoWayDFA :: TwoWayDFA -> String -> Bool
simulateTwoWayDFA dfa input = 
  let initialConfig = Config (initialState dfa) 0 input
      finalConfigs = iterateStep dfa initialConfig
  in any isAccepting finalConfigs

data Config = Config {
  state :: State,
  position :: Int,
  tape :: String
}

iterateStep :: TwoWayDFA -> Config -> [Config]
iterateStep dfa config = 
  if position config < 0 || position config >= length (tape config)
  then [config]  -- 停止条件
  else let currentChar = tape config !! position config
           (newState, direction) = delta dfa (state config) currentChar
           newPosition = case direction of
                          Left -> position config - 1
                          Right -> position config + 1
           newConfig = Config newState newPosition (tape config)
       in newConfig : iterateStep dfa newConfig
```

### 2.2 交替有限自动机

**定义 2.2 (交替DFA)**
交替确定性有限自动机是五元组 $M = (Q, \Sigma, \delta, q_0, F)$，其中：

- $\delta : Q \times \Sigma \rightarrow \mathcal{P}(\mathcal{P}(Q))$ 是转移函数
- 每个转移返回状态集合的集合，表示"存在性"和"全称性"选择

**定义 2.3 (交替DFA接受)**
交替DFA接受字符串 $w$，如果存在接受计算树。

**定理 2.2 (交替DFA表达能力)**
交替DFA可以识别所有正则语言，且某些情况下状态数更少。

**算法 2.2 (交替DFA模拟)**

```haskell
data AlternatingDFA = AlternatingDFA {
  states :: Set State,
  alphabet :: Set Char,
  delta :: State -> Char -> Set (Set State),
  initialState :: State,
  acceptingStates :: Set State
}

simulateAlternatingDFA :: AlternatingDFA -> String -> Bool
simulateAlternatingDFA dfa input = 
  let initialConfig = (initialState dfa, input)
  in acceptsConfig dfa initialConfig

acceptsConfig :: AlternatingDFA -> (State, String) -> Bool
acceptsConfig dfa (state, []) = 
  state `elem` acceptingStates dfa

acceptsConfig dfa (state, c:cs) = 
  let transitions = delta dfa state c
      -- 存在性选择：至少有一个转移集合使得所有状态都接受
      validTransitions = filter (\stateSet -> 
        all (\s -> acceptsConfig dfa (s, cs)) stateSet) transitions
  in not (null validTransitions)
```

### 2.3 概率有限自动机

**定义 2.3 (概率DFA)**
概率确定性有限自动机是五元组 $M = (Q, \Sigma, \delta, q_0, F)$，其中：

- $\delta : Q \times \Sigma \times Q \rightarrow [0,1]$ 是转移概率函数
- 满足 $\sum_{q' \in Q} \delta(q, a, q') = 1$ 对于所有 $q \in Q, a \in \Sigma$

**定义 2.4 (概率DFA接受概率)**
概率DFA接受字符串 $w$ 的概率：
$$P_M(w) = \sum_{q \in F} P_M(w, q)$$

其中 $P_M(w, q)$ 是读入 $w$ 后到达状态 $q$ 的概率。

**算法 2.3 (概率DFA模拟)**

```haskell
data ProbabilisticDFA = ProbabilisticDFA {
  states :: Set State,
  alphabet :: Set Char,
  delta :: State -> Char -> State -> Double,
  initialState :: State,
  acceptingStates :: Set State
}

acceptanceProbability :: ProbabilisticDFA -> String -> Double
acceptanceProbability dfa input = 
  let initialProb = Map.singleton (initialState dfa) 1.0
      finalProbs = foldl (stepProbabilistic dfa) initialProb input
  in sum [finalProbs Map.! q | q <- acceptingStates dfa]

stepProbabilistic :: ProbabilisticDFA -> Map State Double -> Char -> Map State Double
stepProbabilistic dfa currentProbs char = 
  let newProbs = Map.empty
      updates = [(q', prob * delta dfa q char q') | 
                 (q, prob) <- Map.toList currentProbs,
                 q' <- states dfa]
  in foldl (\m (q, p) -> Map.insertWith (+) q p m) newProbs updates
```

## 3. 高级文法理论

### 3.1 属性文法

**定义 3.1 (属性文法)**
属性文法是四元组 $G = (V, T, P, A)$，其中：

- $V$ 是非终结符集合
- $T$ 是终结符集合
- $P$ 是产生式集合
- $A$ 是属性计算规则集合

**定义 3.2 (综合属性和继承属性)**

- **综合属性**：从子节点向上传播
- **继承属性**：从父节点向下传播

**算法 3.1 (属性文法求值)**

```haskell
data AttributeGrammar = AttributeGrammar {
  nonTerminals :: Set NonTerminal,
  terminals :: Set Terminal,
  productions :: [Production],
  attributeRules :: Map Production [AttributeRule]
}

data AttributeRule = AttributeRule {
  target :: Attribute,
  expression :: AttributeExpression
}

evaluateAttributes :: AttributeGrammar -> ParseTree -> AttributeEnvironment
evaluateAttributes grammar tree = 
  let initialEnv = Map.empty
      -- 首先计算所有综合属性
      env1 = evaluateSynthesized grammar tree initialEnv
      -- 然后计算所有继承属性
      env2 = evaluateInherited grammar tree env1
  in env2

evaluateSynthesized :: AttributeGrammar -> ParseTree -> AttributeEnvironment -> AttributeEnvironment
evaluateSynthesized grammar (Leaf symbol) env = env
evaluateSynthesized grammar (Node production children) env = 
  let -- 递归计算子节点的综合属性
      env1 = foldl (\e child -> evaluateSynthesized grammar child e) env children
      -- 计算当前节点的综合属性
      rules = attributeRules grammar Map.! production
      synthesizedRules = filter isSynthesized rules
      env2 = foldl (\e rule -> evaluateRule grammar rule e) env1 synthesizedRules
  in env2
```

### 3.2 树邻接文法

**定义 3.3 (树邻接文法)**
树邻接文法是四元组 $G = (V, T, I, A)$，其中：

- $V$ 是非终结符集合
- $T$ 是终结符集合
- $I$ 是初始树集合
- $A$ 是辅助树集合

**定义 3.4 (替换和邻接操作)**

- **替换**：在非终结符节点处插入树
- **邻接**：在非终结符节点处邻接辅助树

**算法 3.2 (树邻接文法解析)**

```haskell
data TreeAdjoiningGrammar = TreeAdjoiningGrammar {
  nonTerminals :: Set NonTerminal,
  terminals :: Set Terminal,
  initialTrees :: [Tree],
  auxiliaryTrees :: [Tree]
}

data Tree = Tree {
  root :: NonTerminal,
  children :: [Tree],
  isFoot :: Bool  -- 标记是否为辅助树的脚节点
}

parseTAG :: TreeAdjoiningGrammar -> String -> Bool
parseTAG grammar input = 
  let initialDerivations = initialTrees grammar
      allDerivations = generateAllDerivations grammar initialDerivations
      terminalTrees = filter isTerminalTree allDerivations
      yields = map yield terminalTrees
  in input `elem` yields

generateAllDerivations :: TreeAdjoiningGrammar -> [Tree] -> [Tree]
generateAllDerivations grammar trees = 
  let newTrees = concatMap (\tree -> 
    concatMap (\op -> applyOperation op tree) [Substitution, Adjunction]) trees
  in if newTrees == trees
     then trees  -- 固定点
     else generateAllDerivations grammar (trees ++ newTrees)
```

### 3.3 依赖文法

**定义 3.5 (依赖文法)**
依赖文法是三元组 $G = (V, T, D)$，其中：

- $V$ 是词汇集合
- $T$ 是依存关系类型集合
- $D$ 是依存关系规则集合

**定义 3.6 (依存关系)**
依存关系是二元组 $(w_1, w_2, t)$，表示词 $w_1$ 通过关系 $t$ 依存于词 $w_2$。

**算法 3.3 (依赖文法解析)**

```haskell
data DependencyGrammar = DependencyGrammar {
  vocabulary :: Set Word,
  relationTypes :: Set RelationType,
  dependencyRules :: [DependencyRule]
}

data DependencyRule = DependencyRule {
  head :: Word,
  dependent :: Word,
  relation :: RelationType,
  constraints :: [Constraint]
}

parseDependency :: DependencyGrammar -> [Word] -> [Dependency]
parseDependency grammar words = 
  let initialDeps = []
      allDeps = generateDependencies grammar words initialDeps
      validDeps = filter (isValidDependencyTree grammar) allDeps
  in head validDeps  -- 返回第一个有效解析

generateDependencies :: DependencyGrammar -> [Word] -> [Dependency] -> [Dependency]
generateDependencies grammar words currentDeps = 
  let possibleDeps = [(w1, w2, t) | 
                      w1 <- words, w2 <- words, w1 /= w2,
                      t <- relationTypes grammar,
                      isValidRule grammar w1 w2 t]
      newDeps = filter (\dep -> not (createsCycle currentDeps dep)) possibleDeps
  in currentDeps ++ newDeps
```

## 4. 语言理论算法

### 4.1 最小化算法

**算法 4.1 (DFA最小化)**

```haskell
minimizeDFA :: DFA -> DFA
minimizeDFA dfa = 
  let -- 移除不可达状态
      reachableStates = findReachableStates dfa
      dfa1 = removeUnreachableStates dfa reachableStates
      -- 移除不可区分状态
      equivalentStates = findEquivalentStates dfa1
      minimizedStates = mergeEquivalentStates dfa1 equivalentStates
  in minimizedStates

findEquivalentStates :: DFA -> Set (Set State)
findEquivalentStates dfa = 
  let initialPartition = [acceptingStates dfa, states dfa \\ acceptingStates dfa]
      refinedPartition = refinePartition dfa initialPartition
  in refinedPartition

refinePartition :: DFA -> [Set State] -> [Set State]
refinePartition dfa partition = 
  let newPartition = concatMap (\block -> 
    let subBlocks = splitBlock dfa block partition
    in subBlocks) partition
  in if newPartition == partition
     then partition  -- 固定点
     else refinePartition dfa newPartition

splitBlock :: DFA -> Set State -> [Set State] -> [Set State]
splitBlock dfa block partition = 
  let -- 根据转移函数将块分割
      splits = groupBy (\s1 s2 -> 
        all (\a -> 
          let next1 = delta dfa s1 a
              next2 = delta dfa s2 a
          in findBlock next1 partition == findBlock next2 partition) 
        (alphabet dfa)) (Set.toList block)
  in map Set.fromList splits
```

### 4.2 语言等价性检查

**算法 4.2 (语言等价性)**

```haskell
areLanguagesEquivalent :: DFA -> DFA -> Bool
areLanguagesEquivalent dfa1 dfa2 = 
  let -- 构造乘积自动机
      productDFA = constructProductDFA dfa1 dfa2
      -- 检查是否存在接受状态差异
      acceptingDifference = findAcceptingDifference productDFA
  in null acceptingDifference

constructProductDFA :: DFA -> DFA -> DFA
constructProductDFA dfa1 dfa2 = 
  let productStates = [(q1, q2) | q1 <- states dfa1, q2 <- states dfa2]
      productDelta (q1, q2) a = (delta dfa1 q1 a, delta dfa2 q2 a)
      productAccepting = [(q1, q2) | 
                         q1 <- acceptingStates dfa1, 
                         q2 <- acceptingStates dfa2]
  in DFA {
    states = Set.fromList productStates,
    alphabet = alphabet dfa1,
    delta = productDelta,
    initialState = (initialState dfa1, initialState dfa2),
    acceptingStates = Set.fromList productAccepting
  }
```

### 4.3 语言包含性检查

**算法 4.3 (语言包含性)**

```haskell
isLanguageContained :: DFA -> DFA -> Bool
isLanguageContained dfa1 dfa2 = 
  let -- 构造补集自动机
      complementDFA2 = complementDFA dfa2
      -- 检查交集是否为空
      intersection = intersectDFA dfa1 complementDFA2
  in isEmptyLanguage intersection

isEmptyLanguage :: DFA -> Bool
isEmptyLanguage dfa = 
  let reachableStates = findReachableStates dfa
      reachableAccepting = Set.intersection reachableStates (acceptingStates dfa)
  in Set.null reachableAccepting
```

## 5. 高级语言特性

### 5.1 上下文敏感语言

**定义 5.1 (线性有界自动机)**
线性有界自动机是五元组 $M = (Q, \Sigma, \Gamma, \delta, q_0)$，其中：

- $\Gamma$ 是工作字母表
- $\delta : Q \times \Gamma \rightarrow Q \times \Gamma \times \{\text{left}, \text{right}\}$
- 工作带长度与输入长度成正比

**定理 5.1 (LBA与CSL等价性)**
线性有界自动机识别的语言类与上下文敏感语言等价。

**算法 5.1 (LBA模拟)**

```haskell
data LinearBoundedAutomaton = LinearBoundedAutomaton {
  states :: Set State,
  inputAlphabet :: Set Char,
  workAlphabet :: Set Char,
  delta :: State -> Char -> (State, Char, Direction),
  initialState :: State
}

simulateLBA :: LinearBoundedAutomaton -> String -> Bool
simulateLBA lba input = 
  let initialConfig = LBAConfig (initialState lba) 0 (markInput input)
      finalConfigs = iterateLBAStep lba initialConfig
  in any isAccepting finalConfigs

data LBAConfig = LBAConfig {
  state :: State,
  headPosition :: Int,
  workTape :: String
}

markInput :: String -> String
markInput input = ">" ++ input ++ "<"  -- 添加边界标记

iterateLBAStep :: LinearBoundedAutomaton -> LBAConfig -> [LBAConfig]
iterateLBAStep lba config = 
  let currentChar = workTape config !! headPosition config
      (newState, newChar, direction) = delta lba (state config) currentChar
      newTape = updateTape (workTape config) (headPosition config) newChar
      newPosition = case direction of
                     Left -> headPosition config - 1
                     Right -> headPosition config + 1
      newConfig = LBAConfig newState newPosition newTape
  in if newPosition < 0 || newPosition >= length newTape
     then [config]  -- 停止条件
     else newConfig : iterateLBAStep lba newConfig
```

### 5.2 递归可枚举语言

**定义 5.2 (图灵机)**
图灵机是七元组 $M = (Q, \Sigma, \Gamma, \delta, q_0, B, F)$，其中：

- $\Gamma$ 是带字母表
- $B \in \Gamma$ 是空白符号
- $\delta : Q \times \Gamma \rightarrow Q \times \Gamma \times \{\text{left}, \text{right}\}$

**算法 5.2 (图灵机模拟)**

```haskell
data TuringMachine = TuringMachine {
  states :: Set State,
  inputAlphabet :: Set Char,
  tapeAlphabet :: Set Char,
  delta :: State -> Char -> (State, Char, Direction),
  initialState :: State,
  blankSymbol :: Char,
  acceptingStates :: Set State
}

simulateTuringMachine :: TuringMachine -> String -> Bool
simulateTuringMachine tm input = 
  let initialConfig = TMConfig (initialState tm) 0 (input ++ repeat (blankSymbol tm))
      finalConfigs = iterateTMStep tm initialConfig
  in any isAccepting finalConfigs

data TMConfig = TMConfig {
  state :: State,
  headPosition :: Int,
  tape :: String
}

iterateTMStep :: TuringMachine -> TMConfig -> [TMConfig]
iterateTMStep tm config = 
  let currentChar = tape config !! headPosition config
      (newState, newChar, direction) = delta tm (state config) currentChar
      newTape = updateTape (tape config) (headPosition config) newChar
      newPosition = case direction of
                     Left -> headPosition config - 1
                     Right -> headPosition config + 1
      newConfig = TMConfig newState newPosition newTape
  in newConfig : iterateTMStep tm newConfig
```

## 6. 语言理论应用

### 6.1 编译器设计

**算法 6.1 (词法分析器生成)**

```haskell
generateLexer :: [RegularExpression] -> Lexer
generateLexer regexps = 
  let -- 为每个正则表达式构造NFA
      nfas = map regexToNFA regexps
      -- 合并所有NFA
      combinedNFA = combineNFAs nfas
      -- 转换为DFA
      dfa = nfaToDFA combinedNFA
      -- 最小化DFA
      minimizedDFA = minimizeDFA dfa
  in Lexer minimizedDFA

data Lexer = Lexer {
  dfa :: DFA,
  tokenTypes :: Map State TokenType
}

tokenize :: Lexer -> String -> [Token]
tokenize lexer input = 
  let tokens = []
      (finalTokens, _) = foldl (\acc char -> 
        let (tokens, currentState) = acc
            newState = delta (dfa lexer) currentState char
        in if newState `elem` acceptingStates (dfa lexer)
           then (tokens ++ [createToken lexer newState], newState)
           else (tokens, newState)) (tokens, initialState (dfa lexer)) input
  in finalTokens
```

### 6.2 自然语言处理

**算法 6.2 (句法分析器)**

```haskell
data Parser = Parser {
  grammar :: ContextFreeGrammar,
  parsingTable :: Map (NonTerminal, Terminal) [Production]
}

parseSentence :: Parser -> [Token] -> ParseTree
parseSentence parser tokens = 
  let initialStack = [startSymbol (grammar parser)]
      initialInput = tokens
      parseTree = shiftReduce parser initialStack initialInput
  in parseTree

shiftReduce :: Parser -> [Symbol] -> [Token] -> ParseTree
shiftReduce parser stack input = 
  case (stack, input) of
    ([start], []) -> createParseTree start
    (s:ss, t:ts) -> 
      let action = getAction parser (head s) t
      in case action of
           Shift -> shiftReduce parser (t:s:ss) ts
           Reduce prod -> 
             let newStack = reduceStack parser s ss prod
             in shiftReduce parser newStack input
           Accept -> createParseTree (head s)
```

## 7. 前沿研究方向

### 7.1 量子自动机

**定义 7.1 (量子有限自动机)**
量子有限自动机是五元组 $M = (Q, \Sigma, \delta, q_0, F)$，其中：

- $\delta : Q \times \Sigma \times Q \rightarrow \mathbb{C}$ 是转移振幅函数
- 满足 $\sum_{q' \in Q} |\delta(q, a, q')|^2 = 1$ 对于所有 $q \in Q, a \in \Sigma$

**算法 7.1 (量子自动机模拟)**

```haskell
data QuantumDFA = QuantumDFA {
  states :: Set State,
  alphabet :: Set Char,
  delta :: State -> Char -> State -> Complex Double,
  initialState :: State,
  acceptingStates :: Set State
}

acceptanceProbability :: QuantumDFA -> String -> Double
acceptanceProbability qdfa input = 
  let initialState = Map.singleton (initialState qdfa) 1.0
      finalState = foldl (stepQuantum qdfa) initialState input
  in sum [magnitude (finalState Map.! q) | q <- acceptingStates qdfa]

stepQuantum :: QuantumDFA -> Map State (Complex Double) -> Char -> Map State (Complex Double)
stepQuantum qdfa currentState char = 
  let newState = Map.empty
      updates = [(q', amplitude * delta qdfa q char q') | 
                 (q, amplitude) <- Map.toList currentState,
                 q' <- states qdfa]
  in foldl (\m (q, amp) -> Map.insertWith (+) q amp m) newState updates
```

### 7.2 概率上下文无关文法

**定义 7.2 (PCFG)**
概率上下文无关文法是五元组 $G = (V, T, P, S, \pi)$，其中：

- $\pi : P \rightarrow [0,1]$ 是产生式概率函数
- 满足 $\sum_{A \rightarrow \alpha} \pi(A \rightarrow \alpha) = 1$ 对于所有 $A \in V$

**算法 7.2 (PCFG解析)**

```haskell
data ProbabilisticCFG = ProbabilisticCFG {
  nonTerminals :: Set NonTerminal,
  terminals :: Set Terminal,
  productions :: [Production],
  probabilities :: Map Production Double,
  startSymbol :: NonTerminal
}

parsePCFG :: ProbabilisticCFG -> String -> (ParseTree, Double)
parsePCFG pcfg input = 
  let -- 使用CYK算法计算所有解析的概率
      parseTable = buildParseTable pcfg input
      -- 选择概率最高的解析
      bestParse = findBestParse pcfg parseTable input
  in bestParse

buildParseTable :: ProbabilisticCFG -> String -> Array (Int,Int) (Map NonTerminal Double)
buildParseTable pcfg input = 
  let n = length input
      table = array ((0,0), (n-1,n-1)) (repeat Map.empty)
      
      -- 初始化对角线
      table' = foldl (\t i -> 
        let char = input !! i
            probs = [(A, prob) | (A, alpha) <- productions pcfg,
                               alpha == [char],
                               let prob = probabilities pcfg Map.! (A, alpha)]
        in t // [((i,i), Map.fromList probs)]) table [0..n-1]
      
      -- 填充表格
      finalTable = fillParseTable pcfg table' n
  in finalTable
```

## 8. 结论

形式语言理论基础扩展为现代计算机科学提供了强大的理论工具。从基础的自动机理论到高级的语言理论，这些概念和方法在编译器设计、自然语言处理、形式化验证等领域发挥着重要作用。随着量子计算和概率计算的发展，形式语言理论也在不断扩展和深化。

## 参考文献

1. Hopcroft, J. E., Motwani, R., & Ullman, J. D. (2006). Introduction to automata theory, languages, and computation.
2. Sipser, M. (2012). Introduction to the theory of computation. Cengage Learning.
3. Aho, A. V., Lam, M. S., Sethi, R., & Ullman, J. D. (2006). Compilers: principles, techniques, and tools.
4. Joshi, A. K., & Schabes, Y. (1997). Tree-adjoining grammars. In Handbook of formal languages (pp. 69-123).
5. Manning, C. D., & Schütze, H. (1999). Foundations of statistical natural language processing.
6. Kondacs, A., & Watrous, J. (1997). On the power of quantum finite state automata. In Proceedings 38th Annual Symposium on Foundations of Computer Science (pp. 66-75).
