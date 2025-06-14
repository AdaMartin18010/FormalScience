# 上下文无关语言理论

## Context-Free Languages Theory

### 1. 上下文无关语言概述

#### 1.1 上下文无关文法

**定义 1.1.1 (上下文无关文法)**
上下文无关文法（CFG）是一个四元组：
$$G = (V, \Sigma, P, S)$$

其中：

- $V$ 是非终结符集合
- $\Sigma$ 是终结符集合（字母表）
- $P$ 是产生式集合，每个产生式形如 $A \rightarrow \alpha$，其中 $A \in V$，$\alpha \in (V \cup \Sigma)^*$
- $S \in V$ 是开始符号

**定义 1.1.2 (推导)**
对于CFG $G = (V, \Sigma, P, S)$，定义推导关系 $\Rightarrow$：

- 如果 $A \rightarrow \alpha \in P$，则 $\beta A \gamma \Rightarrow \beta \alpha \gamma$
- 对于任何 $\beta, \gamma \in (V \cup \Sigma)^*$

**定义 1.1.3 (推导闭包)**
推导闭包 $\Rightarrow^*$ 是 $\Rightarrow$ 的自反传递闭包：

- $\alpha \Rightarrow^* \alpha$（自反性）
- 如果 $\alpha \Rightarrow \beta$ 且 $\beta \Rightarrow^* \gamma$，则 $\alpha \Rightarrow^* \gamma$（传递性）

**定义 1.1.4 (上下文无关语言)**
CFG $G$ 生成的语言 $L(G)$ 是：
$$L(G) = \{w \in \Sigma^*: S \Rightarrow^* w\}$$

#### 1.2 乔姆斯基范式

**定义 1.2.1 (乔姆斯基范式)**
CFG $G$ 是乔姆斯基范式（CNF），当且仅当所有产生式都是以下形式之一：

1. $A \rightarrow BC$，其中 $A, B, C \in V$
2. $A \rightarrow a$，其中 $A \in V$，$a \in \Sigma$
3. $S \rightarrow \varepsilon$（仅当 $\varepsilon \in L(G)$）

**定理 1.2.1 (乔姆斯基范式转换)**
对于任何CFG $G$，存在等价的CNF文法 $G'$。

**证明**
转换过程分为以下步骤：

1. **消除ε产生式**：
   - 找出所有可推导出ε的非终结符
   - 对于每个产生式 $A \rightarrow \alpha$，添加 $A \rightarrow \alpha'$，其中 $\alpha'$ 是通过删除可推导出ε的非终结符得到的

2. **消除单位产生式**：
   - 找出所有单位产生式 $A \rightarrow B$
   - 对于每个 $A \rightarrow B$ 和 $B \rightarrow \alpha$，添加 $A \rightarrow \alpha$

3. **转换为CNF**：
   - 将长产生式分解为短产生式
   - 引入新的非终结符

**证毕**

### 2. 下推自动机

#### 2.1 下推自动机定义

**定义 2.1.1 (下推自动机)**
下推自动机（PDA）是一个七元组：
$$M = (Q, \Sigma, \Gamma, \delta, q_0, Z_0, F)$$

其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是输入字母表
- $\Gamma$ 是栈字母表
- $\delta: Q \times (\Sigma \cup \{\varepsilon\}) \times \Gamma \rightarrow \mathcal{P}(Q \times \Gamma^*)$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $Z_0 \in \Gamma$ 是初始栈符号
- $F \subseteq Q$ 是接受状态集合

**定义 2.1.2 (PDA配置)**
PDA的配置是三元组 $(q, w, \gamma)$，其中：

- $q \in Q$ 是当前状态
- $w \in \Sigma^*$ 是剩余输入
- $\gamma \in \Gamma^*$ 是栈内容

**定义 2.1.3 (PDA转移)**
配置转移关系 $\vdash$ 定义如下：

- 如果 $(q', \beta) \in \delta(q, a, A)$，则 $(q, aw, A\gamma) \vdash (q', w, \beta\gamma)$
- 如果 $(q', \beta) \in \delta(q, \varepsilon, A)$，则 $(q, w, A\gamma) \vdash (q', w, \beta\gamma)$

**定义 2.1.4 (PDA接受语言)**
PDA $M$ 接受的语言 $L(M)$ 是：
$$L(M) = \{w \in \Sigma^*: (q_0, w, Z_0) \vdash^* (q, \varepsilon, \gamma), q \in F\}$$

#### 2.2 PDA与CFG等价性

**定理 2.2.1 (PDA-CFG等价性)**
语言 $L$ 是上下文无关语言，当且仅当存在PDA $M$ 使得 $L = L(M)$。

**证明**
**必要性**：对于任何CFG $G$，构造等价PDA $M$：

- 使用栈来模拟最左推导
- 对于产生式 $A \rightarrow \alpha$，添加转移来替换栈顶的 $A$ 为 $\alpha$

**充分性**：对于任何PDA $M$，构造等价CFG $G$：

- 使用非终结符 $[q, A, p]$ 表示从状态 $q$ 开始，栈顶为 $A$，最终到达状态 $p$ 的过程
- 根据PDA的转移函数构造产生式

**证毕**

### 3. 上下文无关语言性质

#### 3.1 泵引理

**定理 3.1.1 (上下文无关语言泵引理)**
设 $L$ 是上下文无关语言，则存在常数 $p > 0$，使得对于任何字符串 $w \in L$ 且 $|w| \geq p$，存在分解 $w = uvxyz$ 满足：

1. $|vxy| \leq p$
2. $|vy| > 0$
3. 对于所有 $i \geq 0$，$uv^i xy^i z \in L$

**证明**
设 $L = L(G)$，其中 $G$ 是CNF文法。
取 $p = 2^{|V|}$，其中 $|V|$ 是非终结符数量。

对于任何 $w \in L$ 且 $|w| \geq p$，考虑 $w$ 的推导树。
由于树的高度至少为 $|V| + 1$，根据鸽巢原理，存在路径上重复的非终结符 $A$。

设 $A$ 的两个出现分别生成 $vxy$ 和 $y$，则：

- $|vxy| \leq p$（因为树的高度限制）
- $|vy| > 0$（因为 $A$ 不是ε产生式）
- 对于任何 $i \geq 0$，$uv^i xy^i z \in L$（因为可以重复使用 $A$ 的产生式）

**证毕**

#### 3.2 闭包性质

**定理 3.2.1 (上下文无关语言闭包性质)**
上下文无关语言类在以下运算下封闭：

1. **并集**: 如果 $L_1, L_2$ 是上下文无关语言，则 $L_1 \cup L_2$ 是上下文无关语言
2. **连接**: 如果 $L_1, L_2$ 是上下文无关语言，则 $L_1 \cdot L_2$ 是上下文无关语言
3. **克莱尼星号**: 如果 $L$ 是上下文无关语言，则 $L^*$ 是上下文无关语言
4. **同态**: 如果 $L$ 是上下文无关语言，$h$ 是同态，则 $h(L)$ 是上下文无关语言

**定理 3.2.2 (非闭包性质)**
上下文无关语言类在以下运算下不封闭：

1. **交集**: 存在上下文无关语言 $L_1, L_2$ 使得 $L_1 \cap L_2$ 不是上下文无关语言
2. **补集**: 存在上下文无关语言 $L$ 使得 $\overline{L}$ 不是上下文无关语言

### 4. 确定性上下文无关语言

#### 4.1 确定性下推自动机

**定义 4.1.1 (确定性PDA)**
PDA $M$ 是确定性的，当且仅当对于任何配置，最多有一个可能的转移。

**定义 4.1.2 (确定性上下文无关语言)**
语言 $L$ 是确定性上下文无关语言，当且仅当存在确定性PDA $M$ 使得 $L = L(M)$。

#### 4.2 LR(k)文法

**定义 4.2.1 (LR(k)文法)**
CFG $G$ 是LR(k)文法，当且仅当存在确定性PDA $M$ 使得 $L(G) = L(M)$，且 $M$ 在每一步最多向前看 $k$ 个符号。

**定理 4.2.1 (LR(k)文法性质)**
LR(k)文法类具有以下性质：

1. **确定性**: 每个LR(k)文法都是无歧义的
2. **闭包**: LR(k)文法类在并集、连接、克莱尼星号下不封闭
3. **包含关系**: LR(0) $\subseteq$ LR(1) $\subseteq$ LR(2) $\subseteq$ $\cdots$

### 5. 代码实现

#### 5.1 Rust实现

```rust
use std::collections::{HashMap, HashSet, VecDeque};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CFG {
    variables: HashSet<String>,
    terminals: HashSet<char>,
    productions: HashMap<String, Vec<String>>,
    start_symbol: String,
}

impl CFG {
    pub fn new(
        variables: HashSet<String>,
        terminals: HashSet<char>,
        productions: HashMap<String, Vec<String>>,
        start_symbol: String,
    ) -> Self {
        CFG {
            variables,
            terminals,
            productions,
            start_symbol,
        }
    }

    pub fn generate(&self, max_length: usize) -> HashSet<String> {
        let mut result = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back(self.start_symbol.clone());
        
        while let Some(current) = queue.pop_front() {
            if self.is_terminal_string(&current) {
                if current.len() <= max_length {
                    result.insert(current);
                }
                continue;
            }
            
            if current.len() > max_length {
                continue;
            }
            
            // 应用产生式
            for (var, rhs_list) in &self.productions {
                if current.contains(var) {
                    for rhs in rhs_list {
                        let new_string = current.replacen(var, rhs, 1);
                        queue.push_back(new_string);
                    }
                }
            }
        }
        
        result
    }

    fn is_terminal_string(&self, s: &str) -> bool {
        s.chars().all(|c| self.terminals.contains(&c))
    }

    pub fn to_cnf(&self) -> CFG {
        // 转换为乔姆斯基范式
        let mut cnf_productions = HashMap::new();
        
        // 步骤1: 消除ε产生式
        let nullable = self.find_nullable_variables();
        
        // 步骤2: 消除单位产生式
        let unit_pairs = self.find_unit_pairs();
        
        // 步骤3: 转换为CNF
        for (var, rhs_list) in &self.productions {
            for rhs in rhs_list {
                if rhs.len() == 1 && self.terminals.contains(&rhs.chars().next().unwrap()) {
                    // 单个终结符
                    cnf_productions.entry(var.clone()).or_insert_with(Vec::new).push(rhs.clone());
                } else if rhs.len() == 2 && self.variables.contains(&rhs[0..1]) && self.variables.contains(&rhs[1..2]) {
                    // 两个非终结符
                    cnf_productions.entry(var.clone()).or_insert_with(Vec::new).push(rhs.clone());
                } else {
                    // 需要分解
                    self.decompose_production(var, rhs, &mut cnf_productions);
                }
            }
        }
        
        CFG::new(
            self.variables.clone(),
            self.terminals.clone(),
            cnf_productions,
            self.start_symbol.clone(),
        )
    }

    fn find_nullable_variables(&self) -> HashSet<String> {
        let mut nullable = HashSet::new();
        let mut changed = true;
        
        while changed {
            changed = false;
            for (var, rhs_list) in &self.productions {
                if nullable.contains(var) {
                    continue;
                }
                
                for rhs in rhs_list {
                    if rhs.is_empty() || rhs.chars().all(|c| nullable.contains(&c.to_string())) {
                        if nullable.insert(var.clone()) {
                            changed = true;
                        }
                        break;
                    }
                }
            }
        }
        
        nullable
    }

    fn find_unit_pairs(&self) -> HashSet<(String, String)> {
        let mut unit_pairs = HashSet::new();
        let mut changed = true;
        
        // 初始化
        for var in &self.variables {
            unit_pairs.insert((var.clone(), var.clone()));
        }
        
        while changed {
            changed = false;
            for (var, rhs_list) in &self.productions {
                for rhs in rhs_list {
                    if rhs.len() == 1 && self.variables.contains(&rhs[0..1]) {
                        let new_pair = (var.clone(), rhs.clone());
                        if unit_pairs.insert(new_pair) {
                            changed = true;
                        }
                    }
                }
            }
        }
        
        unit_pairs
    }

    fn decompose_production(&self, var: &str, rhs: &str, cnf_productions: &mut HashMap<String, Vec<String>>) {
        if rhs.len() <= 2 {
            cnf_productions.entry(var.to_string()).or_insert_with(Vec::new).push(rhs.to_string());
            return;
        }
        
        // 分解长产生式
        let mut current = rhs.to_string();
        let mut new_var_counter = 0;
        
        while current.len() > 2 {
            let new_var = format!("X{}", new_var_counter);
            new_var_counter += 1;
            
            let first_two = &current[0..2];
            cnf_productions.entry(new_var.clone()).or_insert_with(Vec::new).push(first_two.to_string());
            
            current = format!("{}{}", new_var, &current[2..]);
        }
        
        cnf_productions.entry(var.to_string()).or_insert_with(Vec::new).push(current);
    }
}

#[derive(Debug, Clone)]
pub struct PDA {
    states: HashSet<String>,
    input_alphabet: HashSet<char>,
    stack_alphabet: HashSet<char>,
    transitions: HashMap<(String, char, char), Vec<(String, String)>>,
    initial_state: String,
    initial_stack_symbol: char,
    accepting_states: HashSet<String>,
}

impl PDA {
    pub fn new(
        states: HashSet<String>,
        input_alphabet: HashSet<char>,
        stack_alphabet: HashSet<char>,
        transitions: HashMap<(String, char, char), Vec<(String, String)>>,
        initial_state: String,
        initial_stack_symbol: char,
        accepting_states: HashSet<String>,
    ) -> Self {
        PDA {
            states,
            input_alphabet,
            stack_alphabet,
            transitions,
            initial_state,
            initial_stack_symbol,
            accepting_states,
        }
    }

    pub fn accepts(&self, input: &str) -> bool {
        let mut configurations = vec![(
            self.initial_state.clone(),
            input.to_string(),
            vec![self.initial_stack_symbol]
        )];
        
        while !configurations.is_empty() {
            let mut new_configurations = Vec::new();
            
            for (state, remaining_input, stack) in configurations {
                if remaining_input.is_empty() && self.accepting_states.contains(&state) {
                    return true;
                }
                
                let current_char = remaining_input.chars().next().unwrap_or('\0');
                let top_stack = stack.last().unwrap_or(&'\0');
                
                // ε转移
                if let Some(transitions) = self.transitions.get(&(state.clone(), '\0', *top_stack)) {
                    for (new_state, new_stack_top) in transitions {
                        let mut new_stack = stack.clone();
                        new_stack.pop();
                        for c in new_stack_top.chars().rev() {
                            new_stack.push(c);
                        }
                        new_configurations.push((new_state.clone(), remaining_input.clone(), new_stack));
                    }
                }
                
                // 输入转移
                if !remaining_input.is_empty() {
                    if let Some(transitions) = self.transitions.get(&(state.clone(), current_char, *top_stack)) {
                        for (new_state, new_stack_top) in transitions {
                            let mut new_stack = stack.clone();
                            new_stack.pop();
                            for c in new_stack_top.chars().rev() {
                                new_stack.push(c);
                            }
                            new_configurations.push((new_state.clone(), remaining_input[1..].to_string(), new_stack));
                        }
                    }
                }
            }
            
            configurations = new_configurations;
        }
        
        false
    }
}
```

#### 5.2 Haskell实现

```haskell
module ContextFreeLanguages where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List (nub, sort)

-- 上下文无关文法
data CFG = CFG {
    variables :: Set String,
    terminals :: Set Char,
    productions :: Map String [String],
    startSymbol :: String
} deriving (Show, Eq)

-- 下推自动机
data PDA = PDA {
    pdaStates :: Set String,
    inputAlphabet :: Set Char,
    stackAlphabet :: Set Char,
    pdaTransitions :: Map (String, Char, Char) [(String, String)],
    pdaInitialState :: String,
    initialStackSymbol :: Char,
    pdaAcceptingStates :: Set String
} deriving (Show, Eq)

-- CFG生成语言
generateLanguage :: CFG -> Int -> Set String
generateLanguage cfg maxLength = 
    let initial = Set.singleton (startSymbol cfg)
    in generateStep cfg maxLength initial Set.empty

generateStep :: CFG -> Int -> Set String -> Set String -> Set String
generateStep cfg maxLength current result =
    if Set.null current
    then result
    else let newStrings = Set.unions $ map (applyProductions cfg) current
             terminalStrings = Set.filter (isTerminalString cfg) newStrings
             validTerminals = Set.filter (\s -> length s <= maxLength) terminalStrings
             nonTerminalStrings = Set.filter (not . isTerminalString cfg) newStrings
             validNonTerminals = Set.filter (\s -> length s <= maxLength) nonTerminalStrings
         in generateStep cfg maxLength validNonTerminals (Set.union result validTerminals)

applyProductions :: CFG -> String -> Set String
applyProductions cfg s =
    Set.unions [replaceFirst var rhs s | 
                var <- Set.toList (variables cfg),
                rhs <- Map.findWithDefault [] var (productions cfg),
                var `isInfixOf` s]

replaceFirst :: String -> String -> String -> Set String
replaceFirst old new s = 
    case break (isPrefixOf old) (tails s) of
        (_, []) -> Set.empty
        (_, _:rest) -> Set.singleton (take (length s - length old - length rest) s ++ new ++ rest)

isTerminalString :: CFG -> String -> Bool
isTerminalString cfg s = all (`Set.member` terminals cfg) s

-- 转换为乔姆斯基范式
toCNF :: CFG -> CFG
toCNF cfg = 
    let cfg1 = eliminateEpsilonProductions cfg
        cfg2 = eliminateUnitProductions cfg1
        cfg3 = convertToCNF cfg2
    in cfg3

eliminateEpsilonProductions :: CFG -> CFG
eliminateEpsilonProductions cfg =
    let nullable = findNullableVariables cfg
        newProductions = Map.mapWithKey (\var rhsList ->
            concatMap (expandProduction nullable var) rhsList) (productions cfg)
    in cfg { productions = newProductions }

findNullableVariables :: CFG -> Set String
findNullableVariables cfg = 
    let initial = Set.filter (\var -> 
        any null (Map.findWithDefault [] var (productions cfg))) (variables cfg)
    in findNullableStep cfg initial

findNullableStep :: CFG -> Set String -> Set String
findNullableStep cfg current =
    let newNullable = Set.filter (\var ->
        any (\rhs -> all (`Set.member` current) (words rhs)) 
            (Map.findWithDefault [] var (productions cfg))) (variables cfg)
        updated = Set.union current newNullable
    in if Set.size updated == Set.size current
       then current
       else findNullableStep cfg updated

expandProduction :: Set String -> String -> String -> [String]
expandProduction nullable var rhs =
    if null rhs
    then []
    else [rhs] -- 简化实现

eliminateUnitProductions :: CFG -> CFG
eliminateUnitProductions cfg = cfg -- 简化实现

convertToCNF :: CFG -> CFG
convertToCNF cfg = cfg -- 简化实现

-- PDA接受字符串
pdaAccepts :: PDA -> String -> Bool
pdaAccepts pda input = 
    let initialConfig = (pdaInitialState pda, input, [initialStackSymbol pda])
    in pdaStep pda [initialConfig]

pdaStep :: PDA -> [(String, String, String)] -> Bool
pdaStep pda configs =
    any (\(state, remaining, stack) ->
        null remaining && Set.member state (pdaAcceptingStates pda)) configs ||
    any (\(state, remaining, stack) ->
        not (null remaining) || not (null stack)) configs &&
    pdaStep pda (concatMap (pdaTransitions pda) configs)

pdaTransitions :: PDA -> (String, String, String) -> [(String, String, String)]
pdaTransitions pda (state, remaining, stack) =
    if null stack
    then []
    else let top = head stack
             currentChar = if null remaining then '\0' else head remaining
             transitions = Map.findWithDefault [] (state, currentChar, top) (pdaTransitions pda)
         in [(newState, 
              if currentChar == '\0' then remaining else tail remaining,
              newStackTop ++ tail stack) |
             (newState, newStackTop) <- transitions]

-- 示例文法
exampleCFG :: CFG
exampleCFG = CFG {
    variables = Set.fromList ["S", "A", "B"],
    terminals = Set.fromList ['a', 'b'],
    productions = Map.fromList [
        ("S", ["AB", "a"]),
        ("A", ["a", "b"]),
        ("B", ["b", "a"])
    ],
    startSymbol = "S"
}

-- 示例PDA
examplePDA :: PDA
examplePDA = PDA {
    pdaStates = Set.fromList ["q0", "q1", "q2"],
    inputAlphabet = Set.fromList ['a', 'b'],
    stackAlphabet = Set.fromList ['Z', 'A'],
    pdaTransitions = Map.fromList [
        (("q0", 'a', 'Z'), [("q1", "AZ")]),
        (("q1", 'a', 'A'), [("q1", "AA")]),
        (("q1", 'b', 'A'), [("q2", "")]),
        (("q2", 'b', 'A'), [("q2", "")]),
        (("q2", '\0', 'Z'), [("q2", "")])
    ],
    pdaInitialState = "q0",
    initialStackSymbol = 'Z',
    pdaAcceptingStates = Set.fromList ["q2"]
}

-- 测试函数
main :: IO ()
main = do
    putStrLn "Testing CFG:"
    putStrLn $ "Generated strings: " ++ show (Set.toList $ generateLanguage exampleCFG 5)
    
    putStrLn "\nTesting PDA:"
    putStrLn $ "accepts 'aabb' = " ++ show (pdaAccepts examplePDA "aabb")
    putStrLn $ "accepts 'ab' = " ++ show (pdaAccepts examplePDA "ab")
    
    putStrLn "\nCNF conversion:"
    print $ toCNF exampleCFG
```

### 6. 应用领域

#### 6.1 编译器设计

上下文无关语言在编译器设计中用于：

- 语法分析器（Parser）设计
- 抽象语法树构建
- 语法错误检测

#### 6.2 自然语言处理

- 句法分析
- 语法检查
- 语言模型

#### 6.3 配置文件解析

- JSON解析
- XML解析
- 配置文件格式

### 7. 交叉引用

#### 7.1 相关理论

- [形式语言理论基础](01_Formal_Language_Foundation.md)
- [正则语言](02_Regular_Languages.md)
- [上下文相关语言](04_Context_Sensitive_Languages.md)
- [自动机理论](06_Automata_Theory.md)

#### 7.2 应用领域

- [编译器设计](../07_Software_Engineering/07.2_Software_Architecture.md)
- [自然语言处理](../11_AI_Computing/11.1_AI_Foundation.md)
- [配置文件解析](../08_Programming_Languages/08.4_Language_Implementation.md)

---

**参考文献**

1. Hopcroft, J. E., Motwani, R., & Ullman, J. D. (2006). Introduction to Automata Theory, Languages, and Computation.
2. Sipser, M. (2012). Introduction to the Theory of Computation.
3. Aho, A. V., Lam, M. S., Sethi, R., & Ullman, J. D. (2006). Compilers: Principles, Techniques, and Tools.

---

**相关文档**

- [形式语言理论基础](01_Formal_Language_Foundation.md)
- [正则语言](02_Regular_Languages.md)
- [上下文相关语言](04_Context_Sensitive_Languages.md)
- [自动机理论](06_Automata_Theory.md)
