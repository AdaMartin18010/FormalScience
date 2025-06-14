# 可计算性理论

## Computability Theory

### 1. 可计算性概述

#### 1.1 可计算性定义

**定义 1.1.1 (可计算函数)**
函数 $f: \mathbb{N}^k \rightarrow \mathbb{N}$ 是可计算的，当且仅当存在图灵机 $M$ 使得对于任何输入 $(n_1, n_2, \ldots, n_k)$，$M$ 在有限步内停机并输出 $f(n_1, n_2, \ldots, n_k)$。

**定义 1.1.2 (可计算语言)**
语言 $L \subseteq \Sigma^*$ 是可计算的，当且仅当存在图灵机 $M$ 使得：

- 对于任何 $w \in L$，$M$ 在输入 $w$ 上停机并接受
- 对于任何 $w \notin L$，$M$ 在输入 $w$ 上停机并拒绝

**定义 1.1.3 (递归可枚举语言)**
语言 $L \subseteq \Sigma^*$ 是递归可枚举的，当且仅当存在图灵机 $M$ 使得：

- 对于任何 $w \in L$，$M$ 在输入 $w$ 上停机并接受
- 对于任何 $w \notin L$，$M$ 在输入 $w$ 上可能停机并拒绝，也可能永不停机

#### 1.2 丘奇-图灵论题

**论题 1.2.1 (丘奇-图灵论题)**
任何可计算的函数都可以由图灵机计算。

**等价形式**：

1. **λ演算形式**: 任何可计算的函数都可以用λ演算表示
2. **递归函数形式**: 任何可计算的函数都是递归函数
3. **寄存器机形式**: 任何可计算的函数都可以用寄存器机计算

### 2. 图灵机理论

#### 2.1 标准图灵机

**定义 2.1.1 (标准图灵机)**
标准图灵机是一个七元组：
$$M = (Q, \Sigma, \Gamma, \delta, q_0, B, F)$$

其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是输入字母表
- $\Gamma$ 是带字母表，$\Sigma \subseteq \Gamma$
- $\delta: Q \times \Gamma \rightarrow Q \times \Gamma \times \{L, R\}$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $B \in \Gamma \setminus \Sigma$ 是空白符号
- $F \subseteq Q$ 是接受状态集合

**定义 2.1.2 (图灵机配置)**
图灵机的配置是三元组 $(q, \alpha, i)$，其中：

- $q \in Q$ 是当前状态
- $\alpha \in \Gamma^*$ 是带内容
- $i \in \mathbb{N}$ 是读写头位置

**定义 2.1.3 (图灵机转移)**
配置转移关系 $\vdash$ 定义如下：
$$(q, \alpha, i) \vdash (q', \alpha', i')$$

当且仅当：

- $\delta(q, \alpha_i) = (q', b, D)$
- $\alpha' = \alpha_0 \cdots \alpha_{i-1} b \alpha_{i+1} \cdots$
- $i' = \begin{cases} i-1 & \text{if } D = L \\ i+1 & \text{if } D = R \end{cases}$

#### 2.2 图灵机变种

**定义 2.2.1 (多带图灵机)**
多带图灵机有 $k$ 个带，每个带都有自己的读写头。转移函数为：
$$\delta: Q \times \Gamma^k \rightarrow Q \times \Gamma^k \times \{L, R\}^k$$

**定理 2.2.1 (多带图灵机等价性)**
多带图灵机与标准图灵机在计算能力上等价。

**定义 2.2.2 (非确定性图灵机)**
非确定性图灵机的转移函数返回可能转移的集合：
$$\delta: Q \times \Gamma \rightarrow \mathcal{P}(Q \times \Gamma \times \{L, R\})$$

**定理 2.2.2 (非确定性图灵机等价性)**
非确定性图灵机与确定性图灵机在计算能力上等价。

### 3. 递归函数理论

#### 3.1 原始递归函数

**定义 3.1.1 (基本函数)**

1. **零函数**: $Z(n) = 0$
2. **后继函数**: $S(n) = n + 1$
3. **投影函数**: $P_i^k(n_1, n_2, \ldots, n_k) = n_i$

**定义 3.1.2 (复合)**
如果 $f: \mathbb{N}^k \rightarrow \mathbb{N}$ 和 $g_1, g_2, \ldots, g_k: \mathbb{N}^m \rightarrow \mathbb{N}$ 是原始递归函数，则复合函数 $h: \mathbb{N}^m \rightarrow \mathbb{N}$ 定义为：
$$h(x_1, x_2, \ldots, x_m) = f(g_1(x_1, x_2, \ldots, x_m), g_2(x_1, x_2, \ldots, x_m), \ldots, g_k(x_1, x_2, \ldots, x_m))$$

**定义 3.1.3 (原始递归)**
如果 $g: \mathbb{N}^k \rightarrow \mathbb{N}$ 和 $h: \mathbb{N}^{k+2} \rightarrow \mathbb{N}$ 是原始递归函数，则原始递归函数 $f: \mathbb{N}^{k+1} \rightarrow \mathbb{N}$ 定义为：
$$f(0, x_1, x_2, \ldots, x_k) = g(x_1, x_2, \ldots, x_k)$$
$$f(n+1, x_1, x_2, \ldots, x_k) = h(n, f(n, x_1, x_2, \ldots, x_k), x_1, x_2, \ldots, x_k)$$

**定义 3.1.4 (原始递归函数类)**
原始递归函数类是最小的函数类，包含基本函数且在复合和原始递归下封闭。

#### 3.2 一般递归函数

**定义 3.2.1 (μ算子)**
如果 $g: \mathbb{N}^{k+1} \rightarrow \mathbb{N}$ 是递归函数，则μ算子定义的函数 $f: \mathbb{N}^k \rightarrow \mathbb{N}$ 为：
$$f(x_1, x_2, \ldots, x_k) = \mu y[g(x_1, x_2, \ldots, x_k, y) = 0]$$

其中 $\mu y[P(y)]$ 表示满足条件 $P(y)$ 的最小自然数 $y$，如果不存在这样的 $y$，则 $f$ 在该输入上无定义。

**定义 3.2.2 (一般递归函数)**
一般递归函数类是最小的函数类，包含基本函数且在复合、原始递归和μ算子下封闭。

**定理 3.2.1 (递归函数与图灵机等价性)**
一般递归函数类与图灵可计算函数类等价。

### 4. 不可计算性

#### 4.1 停机问题

**定义 4.1.1 (停机问题)**
停机问题是判断给定图灵机 $M$ 在给定输入 $w$ 上是否会停机的问题。

**定理 4.1.1 (停机问题不可判定性)**
停机问题是不可判定的。

**证明**
假设停机问题是可判定的，则存在图灵机 $H$ 判定停机问题。

构造图灵机 $D$：

1. 输入：图灵机 $M$ 的编码 $\langle M \rangle$
2. 运行 $H$ 判断 $M$ 在输入 $\langle M \rangle$ 上是否停机
3. 如果 $H$ 输出"停机"，则 $D$ 进入无限循环
4. 如果 $H$ 输出"不停机"，则 $D$ 停机并接受

考虑 $D$ 在输入 $\langle D \rangle$ 上的行为：

- 如果 $D$ 停机，则 $H$ 输出"停机"，$D$ 进入无限循环，矛盾
- 如果 $D$ 不停机，则 $H$ 输出"不停机"，$D$ 停机，矛盾

因此停机问题是不可判定的。
**证毕**

#### 4.2 其他不可判定问题

**定理 4.2.1 (空性问题不可判定性)**
判断给定图灵机是否接受空语言是不可判定的。

**定理 4.2.2 (等价性问题不可判定性)**
判断两个图灵机是否等价是不可判定的。

**定理 4.2.3 (接受性问题不可判定性)**
判断给定图灵机是否接受给定字符串是不可判定的。

### 5. 归约理论

#### 5.1 多一归约

**定义 5.1.1 (多一归约)**
语言 $A$ 多一归约到语言 $B$，记作 $A \leq_m B$，当且仅当存在可计算函数 $f$ 使得：
$$x \in A \iff f(x) \in B$$

**定理 5.1.1 (多一归约性质)**

1. **自反性**: $A \leq_m A$
2. **传递性**: 如果 $A \leq_m B$ 且 $B \leq_m C$，则 $A \leq_m C$
3. **封闭性**: 如果 $A \leq_m B$ 且 $B$ 是可判定的，则 $A$ 是可判定的

#### 5.2 图灵归约

**定义 5.2.1 (图灵归约)**
语言 $A$ 图灵归约到语言 $B$，记作 $A \leq_T B$，当且仅当存在带有 $B$ 作为神谕的图灵机 $M^B$ 判定 $A$。

**定理 5.2.1 (图灵归约性质)**

1. **自反性**: $A \leq_T A$
2. **传递性**: 如果 $A \leq_T B$ 且 $B \leq_T C$，则 $A \leq_T C$
3. **封闭性**: 如果 $A \leq_T B$ 且 $B$ 是可判定的，则 $A$ 是可判定的

### 6. 代码实现

#### 6.1 Rust实现

```rust
use std::collections::{HashMap, HashSet};

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
    pub fn accepts(&self, input: &str) -> Option<bool> {
        let mut tape: Vec<char> = input.chars().collect();
        let mut head_position = 0;
        let mut current_state = self.initial_state.clone();
        let mut step_count = 0;
        let max_steps = 10000; // 防止无限循环
        
        // 扩展磁带
        while head_position >= tape.len() {
            tape.push(self.blank_symbol);
        }
        
        loop {
            if step_count > max_steps {
                return None; // 可能无限循环
            }
            
            if self.accepting_states.contains(&current_state) {
                return Some(true);
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
                return Some(false);
            }
            
            step_count += 1;
        }
    }

    pub fn halts(&self, input: &str) -> bool {
        self.accepts(input).is_some()
    }
}

// 递归函数
pub trait RecursiveFunction {
    fn compute(&self, args: &[u32]) -> Option<u32>;
}

// 基本函数
pub struct ZeroFunction;

impl RecursiveFunction for ZeroFunction {
    fn compute(&self, _args: &[u32]) -> Option<u32> {
        Some(0)
    }
}

pub struct SuccessorFunction;

impl RecursiveFunction for SuccessorFunction {
    fn compute(&self, args: &[u32]) -> Option<u32> {
        if args.len() == 1 {
            Some(args[0] + 1)
        } else {
            None
        }
    }
}

pub struct ProjectionFunction {
    index: usize,
    arity: usize,
}

impl ProjectionFunction {
    pub fn new(index: usize, arity: usize) -> Self {
        ProjectionFunction { index, arity }
    }
}

impl RecursiveFunction for ProjectionFunction {
    fn compute(&self, args: &[u32]) -> Option<u32> {
        if args.len() == self.arity && self.index < self.arity {
            Some(args[self.index])
        } else {
            None
        }
    }
}

// 复合函数
pub struct CompositionFunction {
    outer_function: Box<dyn RecursiveFunction>,
    inner_functions: Vec<Box<dyn RecursiveFunction>>,
}

impl CompositionFunction {
    pub fn new(
        outer_function: Box<dyn RecursiveFunction>,
        inner_functions: Vec<Box<dyn RecursiveFunction>>,
    ) -> Self {
        CompositionFunction {
            outer_function,
            inner_functions,
        }
    }
}

impl RecursiveFunction for CompositionFunction {
    fn compute(&self, args: &[u32]) -> Option<u32> {
        let mut inner_results = Vec::new();
        
        for inner_func in &self.inner_functions {
            if let Some(result) = inner_func.compute(args) {
                inner_results.push(result);
            } else {
                return None;
            }
        }
        
        self.outer_function.compute(&inner_results)
    }
}

// 原始递归函数
pub struct PrimitiveRecursionFunction {
    base_function: Box<dyn RecursiveFunction>,
    step_function: Box<dyn RecursiveFunction>,
}

impl PrimitiveRecursionFunction {
    pub fn new(
        base_function: Box<dyn RecursiveFunction>,
        step_function: Box<dyn RecursiveFunction>,
    ) -> Self {
        PrimitiveRecursionFunction {
            base_function,
            step_function,
        }
    }
}

impl RecursiveFunction for PrimitiveRecursionFunction {
    fn compute(&self, args: &[u32]) -> Option<u32> {
        if args.is_empty() {
            return None;
        }
        
        let n = args[0];
        let rest_args = &args[1..];
        
        if n == 0 {
            self.base_function.compute(rest_args)
        } else {
            let prev_result = self.compute(&[&[n - 1], rest_args].concat())?;
            let step_args = [&[n - 1, prev_result], rest_args].concat();
            self.step_function.compute(&step_args)
        }
    }
}

// 停机问题
pub fn halting_problem(tm: &TuringMachine, input: &str) -> bool {
    // 这是不可判定的，这里只是一个简化的实现
    tm.halts(input)
}

// 归约
pub fn many_one_reduction<F>(a: &str, b: &str, f: F) -> bool
where
    F: Fn(&str) -> String,
{
    // 简化实现：假设f是可计算的
    let f_a = f(a);
    f_a == b
}
```

#### 6.2 Haskell实现

```haskell
module ComputabilityTheory where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)

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

-- 图灵机配置
data TMConfig = TMConfig {
    configState :: String,
    configTape :: String,
    configHead :: Int
} deriving (Show, Eq)

-- 图灵机执行
tmAccepts :: TuringMachine -> String -> Maybe Bool
tmAccepts tm input = 
    let initialConfig = TMConfig (tmInitialState tm) input 0
        maxSteps = 10000
    in tmStep tm initialConfig maxSteps

tmStep :: TuringMachine -> TMConfig -> Int -> Maybe Bool
tmStep tm config steps
    | steps <= 0 = Nothing -- 可能无限循环
    | Set.member (configState config) (tmAcceptingStates tm) = Just True
    | otherwise = 
        let currentSymbol = getTapeSymbol (configTape config) (configHead config) (tmBlankSymbol tm)
            transition = Map.lookup (configState config, currentSymbol) (tmTransitions tm)
        in case transition of
             Just (newState, newSymbol, direction) ->
                 let newTape = setTapeSymbol (configTape config) (configHead config) newSymbol
                     newHead = case direction of
                                 Left -> max 0 (configHead config - 1)
                                 Right -> configHead config + 1
                     newConfig = TMConfig newState newTape newHead
                 in tmStep tm newConfig (steps - 1)
             Nothing -> Just False

getTapeSymbol :: String -> Int -> Char -> Char
getTapeSymbol tape pos blank
    | pos < 0 || pos >= length tape = blank
    | otherwise = tape !! pos

setTapeSymbol :: String -> Int -> Char -> String
setTapeSymbol tape pos symbol
    | pos < 0 = symbol : tape
    | pos >= length tape = tape ++ replicate (pos - length tape + 1) 'B' ++ [symbol]
    | otherwise = take pos tape ++ [symbol] ++ drop (pos + 1) tape

-- 停机问题
haltingProblem :: TuringMachine -> String -> Bool
haltingProblem tm input = 
    case tmAccepts tm input of
        Just _ -> True
        Nothing -> False

-- 递归函数
class RecursiveFunction f where
    compute :: f -> [Integer] -> Maybe Integer

-- 基本函数
data ZeroFunction = ZeroFunction deriving Show

instance RecursiveFunction ZeroFunction where
    compute _ _ = Just 0

data SuccessorFunction = SuccessorFunction deriving Show

instance RecursiveFunction SuccessorFunction where
    compute _ [x] = Just (x + 1)
    compute _ _ = Nothing

data ProjectionFunction = ProjectionFunction {
    projIndex :: Int,
    projArity :: Int
} deriving Show

instance RecursiveFunction ProjectionFunction where
    compute (ProjectionFunction i n) args
        | length args == n && i < n = Just (args !! i)
        | otherwise = Nothing

-- 复合函数
data CompositionFunction = CompositionFunction {
    compOuter :: BoxedRecursiveFunction,
    compInner :: [BoxedRecursiveFunction]
} deriving Show

data BoxedRecursiveFunction = BoxedRecursiveFunction {
    unbox :: [Integer] -> Maybe Integer
}

instance RecursiveFunction CompositionFunction where
    compute (CompositionFunction outer inner) args = do
        innerResults <- mapM (\f -> unbox f args) inner
        unbox outer innerResults

-- 原始递归函数
data PrimitiveRecursionFunction = PrimitiveRecursionFunction {
    prBase :: BoxedRecursiveFunction,
    prStep :: BoxedRecursiveFunction
} deriving Show

instance RecursiveFunction PrimitiveRecursionFunction where
    compute (PrimitiveRecursionFunction base step) args
        | null args = Nothing
        | head args == 0 = unbox base (tail args)
        | otherwise = do
            let n = head args
            let restArgs = tail args
            prevResult <- compute (PrimitiveRecursionFunction base step) ((n-1):restArgs)
            unbox step (n-1:prevResult:restArgs)

-- 归约
manyOneReduction :: (String -> String) -> String -> String -> Bool
manyOneReduction f a b = f a == b

-- 递归可枚举集
isRecursivelyEnumerable :: (String -> Maybe Bool) -> String -> Bool
isRecursivelyEnumerable f x = 
    case f x of
        Just True -> True
        _ -> False

-- 递归集
isRecursive :: (String -> Maybe Bool) -> String -> Bool
isRecursive f x = 
    case f x of
        Just result -> result
        Nothing -> False

-- 示例图灵机
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

-- 示例递归函数
addFunction :: PrimitiveRecursionFunction
addFunction = PrimitiveRecursionFunction {
    prBase = BoxedRecursiveFunction (\args -> Just (head args)),
    prStep = BoxedRecursiveFunction (\args -> Just (args !! 1 + 1))
}

-- 测试函数
main :: IO ()
main = do
    putStrLn "Testing Turing Machine:"
    putStrLn $ "accepts 'ab' = " ++ show (tmAccepts exampleTM "ab")
    putStrLn $ "accepts 'aabb' = " ++ show (tmAccepts exampleTM "aabb")
    
    putStrLn "\nTesting Halting Problem:"
    putStrLn $ "halts on 'ab' = " ++ show (haltingProblem exampleTM "ab")
    
    putStrLn "\nTesting Recursive Functions:"
    putStrLn $ "add(2,3) = " ++ show (compute addFunction [2,3])
    
    putStrLn "\nTesting Reductions:"
    let f x = x ++ "test"
    putStrLn $ "many-one reduction: " ++ show (manyOneReduction f "hello" "hellotest")
```

### 7. 应用领域

#### 7.1 计算机科学基础

可计算性理论在计算机科学中用于：

- 算法设计
- 程序验证
- 编译器设计

#### 7.2 人工智能

- 机器学习理论
- 自动推理
- 知识表示

#### 7.3 数学基础

- 数论
- 集合论
- 逻辑学

### 8. 交叉引用

#### 8.1 相关理论

- [形式语言理论基础](01_Formal_Language_Foundation.md)
- [自动机理论](06_Automata_Theory.md)
- [复杂性理论](08_Complexity_Theory.md)
- [类型理论](../01_Foundational_Theory/01.1_Type_Theory_Foundation.md)

#### 8.2 应用领域

- [算法设计](../07_Software_Engineering/07.3_Software_Design.md)
- [人工智能](../11_AI_Computing/11.1_AI_Foundation.md)
- [数学基础](../02_Mathematical_Foundation/02.1_Mathematical_Foundation.md)

---

**参考文献**

1. Sipser, M. (2012). Introduction to the Theory of Computation.
2. Hopcroft, J. E., Motwani, R., & Ullman, J. D. (2006). Introduction to Automata Theory, Languages, and Computation.
3. Rogers, H. (1987). Theory of Recursive Functions and Effective Computability.

---

**相关文档**

- [形式语言理论基础](01_Formal_Language_Foundation.md)
- [自动机理论](06_Automata_Theory.md)
- [复杂性理论](08_Complexity_Theory.md)
- [类型理论](../01_Foundational_Theory/01.1_Type_Theory_Foundation.md)
