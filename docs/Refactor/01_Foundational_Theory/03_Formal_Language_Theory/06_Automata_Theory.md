# 自动机理论

## Automata Theory

### 1. 自动机概述

#### 1.1 自动机定义

**定义 1.1.1 (自动机)**
自动机是一个抽象的计算模型，用于识别或生成形式语言。自动机由以下部分组成：

1. **状态集合**: 有限或无限的状态集合
2. **输入字母表**: 输入符号的集合
3. **转移函数**: 定义状态转换的规则
4. **初始状态**: 计算的起始状态
5. **接受状态**: 标识计算成功的状态

#### 1.2 自动机分类

**分类 1.2.1 (按计算能力分类)**

1. **有限自动机**: 识别正则语言
2. **下推自动机**: 识别上下文无关语言
3. **图灵机**: 识别递归可枚举语言
4. **线性有界自动机**: 识别上下文相关语言

**分类 1.2.2 (按确定性分类)**

1. **确定性自动机**: 每个配置最多有一个后继
2. **非确定性自动机**: 每个配置可能有多个后继

### 2. 有限自动机

#### 2.1 确定性有限自动机

**定义 2.1.1 (DFA)**
确定性有限自动机是一个五元组：
$$M = (Q, \Sigma, \delta, q_0, F)$$

其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是输入字母表
- $\delta: Q \times \Sigma \rightarrow Q$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $F \subseteq Q$ 是接受状态集合

**定义 2.1.2 (DFA配置)**
DFA的配置是二元组 $(q, w)$，其中：

- $q \in Q$ 是当前状态
- $w \in \Sigma^*$ 是剩余输入

**定义 2.1.3 (DFA转移)**
配置转移关系 $\vdash$ 定义如下：
$$(q, aw) \vdash (q', w) \text{ 当且仅当 } \delta(q, a) = q'$$

**定义 2.1.4 (DFA接受语言)**
DFA $M$ 接受的语言 $L(M)$ 是：
$$L(M) = \{w \in \Sigma^*: (q_0, w) \vdash^* (q, \varepsilon), q \in F\}$$

#### 2.2 非确定性有限自动机

**定义 2.2.1 (NFA)**
非确定性有限自动机是一个五元组：
$$M = (Q, \Sigma, \delta, q_0, F)$$

其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是输入字母表
- $\delta: Q \times (\Sigma \cup \{\varepsilon\}) \rightarrow \mathcal{P}(Q)$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $F \subseteq Q$ 是接受状态集合

**定义 2.2.2 (NFA配置)**
NFA的配置是二元组 $(q, w)$，其中：

- $q \in Q$ 是当前状态
- $w \in \Sigma^*$ 是剩余输入

**定义 2.2.3 (NFA转移)**
配置转移关系 $\vdash$ 定义如下：

1. $(q, aw) \vdash (q', w)$ 当且仅当 $q' \in \delta(q, a)$
2. $(q, w) \vdash (q', w)$ 当且仅当 $q' \in \delta(q, \varepsilon)$

**定义 2.2.4 (NFA接受语言)**
NFA $M$ 接受的语言 $L(M)$ 是：
$$L(M) = \{w \in \Sigma^*: (q_0, w) \vdash^* (q, \varepsilon), q \in F\}$$

#### 2.3 DFA与NFA等价性

**定理 2.3.1 (DFA-NFA等价性)**
对于任何NFA $M$，存在等价的DFA $M'$。

**证明**
使用子集构造法：

1. **状态集合**: $Q' = \mathcal{P}(Q)$
2. **初始状态**: $q_0' = \varepsilon\text{-closure}(\{q_0\})$
3. **转移函数**: $\delta'(S, a) = \varepsilon\text{-closure}(\text{move}(S, a))$
4. **接受状态**: $F' = \{S \subseteq Q: S \cap F \neq \emptyset\}$

其中：

- $\varepsilon\text{-closure}(S)$ 是从 $S$ 中的状态通过ε转移可达的所有状态
- $\text{move}(S, a)$ 是从 $S$ 中的状态通过输入 $a$ 可达的所有状态

**证毕**

### 3. 下推自动机

#### 3.1 下推自动机定义

**定义 3.1.1 (PDA)**
下推自动机是一个七元组：
$$M = (Q, \Sigma, \Gamma, \delta, q_0, Z_0, F)$$

其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是输入字母表
- $\Gamma$ 是栈字母表
- $\delta: Q \times (\Sigma \cup \{\varepsilon\}) \times \Gamma \rightarrow \mathcal{P}(Q \times \Gamma^*)$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $Z_0 \in \Gamma$ 是初始栈符号
- $F \subseteq Q$ 是接受状态集合

**定义 3.1.2 (PDA配置)**
PDA的配置是三元组 $(q, w, \gamma)$，其中：

- $q \in Q$ 是当前状态
- $w \in \Sigma^*$ 是剩余输入
- $\gamma \in \Gamma^*$ 是栈内容

**定义 3.1.3 (PDA转移)**
配置转移关系 $\vdash$ 定义如下：

1. $(q, aw, A\gamma) \vdash (q', w, \beta\gamma)$ 当且仅当 $(q', \beta) \in \delta(q, a, A)$
2. $(q, w, A\gamma) \vdash (q', w, \beta\gamma)$ 当且仅当 $(q', \beta) \in \delta(q, \varepsilon, A)$

**定义 3.1.4 (PDA接受语言)**
PDA $M$ 接受的语言 $L(M)$ 是：
$$L(M) = \{w \in \Sigma^*: (q_0, w, Z_0) \vdash^* (q, \varepsilon, \gamma), q \in F\}$$

#### 3.2 确定性下推自动机

**定义 3.2.1 (确定性PDA)**
PDA $M$ 是确定性的，当且仅当对于任何配置，最多有一个可能的转移。

**定义 3.2.2 (确定性上下文无关语言)**
语言 $L$ 是确定性上下文无关语言，当且仅当存在确定性PDA $M$ 使得 $L = L(M)$。

### 4. 图灵机

#### 4.1 图灵机定义

**定义 4.1.1 (图灵机)**
图灵机是一个七元组：
$$M = (Q, \Sigma, \Gamma, \delta, q_0, B, F)$$

其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是输入字母表
- $\Gamma$ 是带字母表，$\Sigma \subseteq \Gamma$
- $\delta: Q \times \Gamma \rightarrow Q \times \Gamma \times \{L, R\}$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $B \in \Gamma \setminus \Sigma$ 是空白符号
- $F \subseteq Q$ 是接受状态集合

**定义 4.1.2 (图灵机配置)**
图灵机的配置是三元组 $(q, \alpha, i)$，其中：

- $q \in Q$ 是当前状态
- $\alpha \in \Gamma^*$ 是带内容
- $i \in \mathbb{N}$ 是读写头位置

**定义 4.1.3 (图灵机转移)**
配置转移关系 $\vdash$ 定义如下：
$$(q, \alpha, i) \vdash (q', \alpha', i')$$

当且仅当：

- $\delta(q, \alpha_i) = (q', b, D)$
- $\alpha' = \alpha_0 \cdots \alpha_{i-1} b \alpha_{i+1} \cdots$
- $i' = \begin{cases} i-1 & \text{if } D = L \\ i+1 & \text{if } D = R \end{cases}$

**定义 4.1.4 (图灵机接受语言)**
图灵机 $M$ 接受的语言 $L(M)$ 是：
$$L(M) = \{w \in \Sigma^*: (q_0, w, 0) \vdash^* (q, \alpha, i), q \in F\}$$

#### 4.2 图灵机变种

**定义 4.2.1 (多带图灵机)**
多带图灵机有多个带，每个带都有自己的读写头。

**定义 4.2.2 (非确定性图灵机)**
非确定性图灵机的转移函数返回可能转移的集合。

**定理 4.2.1 (图灵机等价性)**
多带图灵机、非确定性图灵机与标准图灵机在计算能力上等价。

### 5. 线性有界自动机

#### 5.1 线性有界自动机定义

**定义 5.1.1 (LBA)**
线性有界自动机是一个七元组：
$$M = (Q, \Sigma, \Gamma, \delta, q_0, B, F)$$

其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是输入字母表
- $\Gamma$ 是带字母表，$\Sigma \subseteq \Gamma$
- $\delta: Q \times \Gamma \rightarrow Q \times \Gamma \times \{L, R\}$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $B \in \Gamma \setminus \Sigma$ 是空白符号
- $F \subseteq Q$ 是接受状态集合

**限制**: LBA的读写头不能超出输入字符串的边界。

**定义 5.1.2 (LBA接受语言)**
LBA $M$ 接受的语言 $L(M)$ 是：
$$L(M) = \{w \in \Sigma^*: (q_0, w, 0) \vdash^* (q, \alpha, i), q \in F\}$$

### 6. 自动机与语言类的关系

#### 6.1 乔姆斯基层次结构

**定理 6.1.1 (乔姆斯基层次结构)**
自动机与语言类的关系如下：

1. **类型3 (正则语言)**: 被有限自动机识别
2. **类型2 (上下文无关语言)**: 被下推自动机识别
3. **类型1 (上下文相关语言)**: 被线性有界自动机识别
4. **类型0 (递归可枚举语言)**: 被图灵机识别

#### 6.2 包含关系

**定理 6.2.1 (语言类包含关系)**
$$\text{正则语言} \subset \text{确定性上下文无关语言} \subset \text{上下文无关语言} \subset \text{上下文相关语言} \subset \text{递归可枚举语言}$$

### 7. 代码实现

#### 7.1 Rust实现

```rust
use std::collections::{HashMap, HashSet};

// 有限自动机
#[derive(Debug, Clone)]
pub struct FiniteAutomaton {
    states: HashSet<String>,
    alphabet: HashSet<char>,
    transitions: HashMap<(String, char), String>,
    initial_state: String,
    accepting_states: HashSet<String>,
}

impl FiniteAutomaton {
    pub fn accepts(&self, input: &str) -> bool {
        let mut current_state = self.initial_state.clone();
        
        for c in input.chars() {
            if let Some(next_state) = self.transitions.get(&(current_state.clone(), c)) {
                current_state = next_state.clone();
            } else {
                return false;
            }
        }
        
        self.accepting_states.contains(&current_state)
    }
}

// 下推自动机
#[derive(Debug, Clone)]
pub struct PushdownAutomaton {
    states: HashSet<String>,
    input_alphabet: HashSet<char>,
    stack_alphabet: HashSet<char>,
    transitions: HashMap<(String, char, char), Vec<(String, String)>>,
    initial_state: String,
    initial_stack_symbol: char,
    accepting_states: HashSet<String>,
}

impl PushdownAutomaton {
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

// 图灵机
#[derive(Debug, Clone)]
pub struct TuringMachine {
    states: HashSet<String>,
    input_alphabet: HashSet<char>,
    tape_alphabet: HashSet<char>,
    transitions: HashMap<(String, char), (String, char, Direction)>,
    initial_state: String,
    blank_symbol: char,
    accepting_states: HashSet<String>,
}

#[derive(Debug, Clone, Copy)]
pub enum Direction {
    Left,
    Right,
}

impl TuringMachine {
    pub fn accepts(&self, input: &str) -> bool {
        let mut tape: Vec<char> = input.chars().collect();
        let mut head_position = 0;
        let mut current_state = self.initial_state.clone();
        
        // 扩展磁带
        while head_position >= tape.len() {
            tape.push(self.blank_symbol);
        }
        
        loop {
            if self.accepting_states.contains(&current_state) {
                return true;
            }
            
            let current_symbol = tape[head_position];
            if let Some((new_state, new_symbol, direction)) = self.transitions.get(&(current_state.clone(), current_symbol)) {
                tape[head_position] = *new_symbol;
                current_state = new_state.clone();
                
                match direction {
                    Direction::Left => {
                        if head_position == 0 {
                            tape.insert(0, self.blank_symbol);
                        } else {
                            head_position -= 1;
                        }
                    }
                    Direction::Right => {
                        head_position += 1;
                        if head_position >= tape.len() {
                            tape.push(self.blank_symbol);
                        }
                    }
                }
            } else {
                return false;
            }
        }
    }
}
```

#### 7.2 Haskell实现

```haskell
module AutomataTheory where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

-- 有限自动机
data FiniteAutomaton = FiniteAutomaton {
    faStates :: Set String,
    faAlphabet :: Set Char,
    faTransitions :: Map (String, Char) String,
    faInitialState :: String,
    faAcceptingStates :: Set String
} deriving (Show, Eq)

-- 下推自动机
data PushdownAutomaton = PushdownAutomaton {
    pdaStates :: Set String,
    pdaInputAlphabet :: Set Char,
    pdaStackAlphabet :: Set Char,
    pdaTransitions :: Map (String, Char, Char) [(String, String)],
    pdaInitialState :: String,
    pdaInitialStackSymbol :: Char,
    pdaAcceptingStates :: Set String
} deriving (Show, Eq)

-- 图灵机
data TuringMachine = TuringMachine {
    tmStates :: Set String,
    tmInputAlphabet :: Set Char,
    tmTapeAlphabet :: Set Char,
    tmTransitions :: Map (String, Char) (String, Char, Direction),
    tmInitialState :: String,
    tmBlankSymbol :: Char,
    tmAcceptingStates :: Set String
} deriving (Show, Eq)

data Direction = Left | Right deriving (Show, Eq)

-- 有限自动机接受字符串
faAccepts :: FiniteAutomaton -> String -> Bool
faAccepts fa input = 
    let finalState = foldl (faStep fa) (faInitialState fa) input
    in Set.member finalState (faAcceptingStates fa)

faStep :: FiniteAutomaton -> String -> Char -> String
faStep fa state char = 
    case Map.lookup (state, char) (faTransitions fa) of
        Just nextState -> nextState
        Nothing -> error "Invalid transition"

-- 下推自动机接受字符串
pdaAccepts :: PushdownAutomaton -> String -> Bool
pdaAccepts pda input = 
    let initialConfig = (pdaInitialState pda, input, [pdaInitialStackSymbol pda])
    in pdaStep pda [initialConfig]

pdaStep :: PushdownAutomaton -> [(String, String, String)] -> Bool
pdaStep pda configs =
    any (\(state, remaining, stack) ->
        null remaining && Set.member state (pdaAcceptingStates pda)) configs ||
    any (\(state, remaining, stack) ->
        not (null remaining) || not (null stack)) configs &&
    pdaStep pda (concatMap (pdaTransitions pda) configs)

pdaTransitions :: PushdownAutomaton -> (String, String, String) -> [(String, String, String)]
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

-- 图灵机接受字符串
tmAccepts :: TuringMachine -> String -> Bool
tmAccepts tm input = 
    let initialTape = input ++ replicate 100 (tmBlankSymbol tm)
        initialConfig = (tmInitialState tm, initialTape, 0)
    in tmStep tm initialConfig

tmStep :: TuringMachine -> (String, String, Int) -> Bool
tmStep tm (state, tape, headPos) =
    if Set.member state (tmAcceptingStates tm)
    then True
    else if headPos < 0 || headPos >= length tape
         then False
         else let currentSymbol = tape !! headPos
                  transition = Map.lookup (state, currentSymbol) (tmTransitions tm)
              in case transition of
                   Just (newState, newSymbol, direction) ->
                       let newTape = take headPos tape ++ [newSymbol] ++ drop (headPos + 1) tape
                           newHeadPos = case direction of
                                          Left -> headPos - 1
                                          Right -> headPos + 1
                       in tmStep tm (newState, newTape, newHeadPos)
                   Nothing -> False

-- 示例自动机
exampleFA :: FiniteAutomaton
exampleFA = FiniteAutomaton {
    faStates = Set.fromList ["q0", "q1", "q2"],
    faAlphabet = Set.fromList ['a', 'b'],
    faTransitions = Map.fromList [
        (("q0", 'a'), "q1"),
        (("q1", 'b'), "q2"),
        (("q2", 'a'), "q1")
    ],
    faInitialState = "q0",
    faAcceptingStates = Set.fromList ["q2"]
}

examplePDA :: PushdownAutomaton
examplePDA = PushdownAutomaton {
    pdaStates = Set.fromList ["q0", "q1", "q2"],
    pdaInputAlphabet = Set.fromList ['a', 'b'],
    pdaStackAlphabet = Set.fromList ['Z', 'A'],
    pdaTransitions = Map.fromList [
        (("q0", 'a', 'Z'), [("q1", "AZ")]),
        (("q1", 'a', 'A'), [("q1", "AA")]),
        (("q1", 'b', 'A'), [("q2", "")]),
        (("q2", 'b', 'A'), [("q2", "")]),
        (("q2", '\0', 'Z'), [("q2", "")])
    ],
    pdaInitialState = "q0",
    pdaInitialStackSymbol = 'Z',
    pdaAcceptingStates = Set.fromList ["q2"]
}

exampleTM :: TuringMachine
exampleTM = TuringMachine {
    tmStates = Set.fromList ["q0", "q1", "q2", "q3"],
    tmInputAlphabet = Set.fromList ['a', 'b'],
    tmTapeAlphabet = Set.fromList ['a', 'b', 'B'],
    tmTransitions = Map.fromList [
        (("q0", 'a'), ("q1", 'B', Right)),
        (("q1", 'a'), ("q1", 'a', Right)),
        (("q1", 'b'), ("q2", 'b', Right)),
        (("q2", 'b'), ("q2", 'b', Right)),
        (("q2", 'B'), ("q3", 'B', Left))
    ],
    tmInitialState = "q0",
    tmBlankSymbol = 'B',
    tmAcceptingStates = Set.fromList ["q3"]
}

-- 测试函数
main :: IO ()
main = do
    putStrLn "Testing Finite Automaton:"
    putStrLn $ "accepts 'ab' = " ++ show (faAccepts exampleFA "ab")
    putStrLn $ "accepts 'aba' = " ++ show (faAccepts exampleFA "aba")
    
    putStrLn "\nTesting Pushdown Automaton:"
    putStrLn $ "accepts 'aabb' = " ++ show (pdaAccepts examplePDA "aabb")
    putStrLn $ "accepts 'ab' = " ++ show (pdaAccepts examplePDA "ab")
    
    putStrLn "\nTesting Turing Machine:"
    putStrLn $ "accepts 'ab' = " ++ show (tmAccepts exampleTM "ab")
    putStrLn $ "accepts 'aabb' = " ++ show (tmAccepts exampleTM "aabb")
```

### 8. 应用领域

#### 8.1 编译器设计

自动机在编译器设计中用于：

- 词法分析（有限自动机）
- 语法分析（下推自动机）
- 代码优化

#### 8.2 自然语言处理

- 句法分析
- 模式匹配
- 语言识别

#### 8.3 硬件设计

- 数字电路设计
- 状态机实现
- 协议验证

### 9. 交叉引用

#### 9.1 相关理论

- [形式语言理论基础](01_Formal_Language_Foundation.md)
- [正则语言](02_Regular_Languages.md)
- [上下文无关语言](03_Context_Free_Languages.md)
- [可计算性理论](07_Computability_Theory.md)

#### 9.2 应用领域

- [编译器设计](../07_Software_Engineering/07.2_Software_Architecture.md)
- [自然语言处理](../11_AI_Computing/11.1_AI_Foundation.md)
- [硬件设计](../04_Distributed_Systems/04.1_Distributed_Systems_Foundation.md)

---

**参考文献**

1. Hopcroft, J. E., Motwani, R., & Ullman, J. D. (2006). Introduction to Automata Theory, Languages, and Computation.
2. Sipser, M. (2012). Introduction to the Theory of Computation.
3. Kozen, D. C. (2006). Automata and Computability.

---

**相关文档**

- [形式语言理论基础](01_Formal_Language_Foundation.md)
- [正则语言](02_Regular_Languages.md)
- [上下文无关语言](03_Context_Free_Languages.md)
- [可计算性理论](07_Computability_Theory.md)
