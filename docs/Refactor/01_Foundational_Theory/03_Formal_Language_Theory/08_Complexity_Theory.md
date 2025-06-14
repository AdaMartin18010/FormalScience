# 复杂性理论

## Complexity Theory

### 1. 复杂性理论概述

#### 1.1 计算复杂性定义

**定义 1.1.1 (时间复杂度)**
算法的时间复杂度是算法执行所需的基本操作数量，通常表示为输入大小的函数。

**定义 1.1.2 (空间复杂度)**
算法的空间复杂度是算法执行所需的内存空间，通常表示为输入大小的函数。

**定义 1.1.3 (渐进复杂度)**
对于函数 $f(n)$ 和 $g(n)$：

- $f(n) = O(g(n))$ 表示存在常数 $c > 0$ 和 $n_0$ 使得对于所有 $n \geq n_0$，$f(n) \leq c \cdot g(n)$
- $f(n) = \Omega(g(n))$ 表示存在常数 $c > 0$ 和 $n_0$ 使得对于所有 $n \geq n_0$，$f(n) \geq c \cdot g(n)$
- $f(n) = \Theta(g(n))$ 表示 $f(n) = O(g(n))$ 且 $f(n) = \Omega(g(n))$

#### 1.2 复杂性类

**定义 1.2.1 (P类)**
P类是可以在多项式时间内被确定性图灵机判定的所有语言类：
$$\text{P} = \bigcup_{k \geq 0} \text{TIME}(n^k)$$

**定义 1.2.2 (NP类)**
NP类是可以在多项式时间内被非确定性图灵机判定的所有语言类：
$$\text{NP} = \bigcup_{k \geq 0} \text{NTIME}(n^k)$$

**定义 1.2.3 (PSPACE类)**
PSPACE类是可以在多项式空间内被确定性图灵机判定的所有语言类：
$$\text{PSPACE} = \bigcup_{k \geq 0} \text{SPACE}(n^k)$$

### 2. P与NP问题

#### 2.1 P类性质

**定理 2.1.1 (P类封闭性)**
P类在以下运算下封闭：

1. **并集**: 如果 $L_1, L_2 \in \text{P}$，则 $L_1 \cup L_2 \in \text{P}$
2. **交集**: 如果 $L_1, L_2 \in \text{P}$，则 $L_1 \cap L_2 \in \text{P}$
3. **补集**: 如果 $L \in \text{P}$，则 $\overline{L} \in \text{P}$
4. **连接**: 如果 $L_1, L_2 \in \text{P}$，则 $L_1 \cdot L_2 \in \text{P}$
5. **克莱尼星号**: 如果 $L \in \text{P}$，则 $L^* \in \text{P}$

**证明 (并集封闭性)**
设 $M_1$ 和 $M_2$ 分别是判定 $L_1$ 和 $L_2$ 的多项式时间图灵机。
构造图灵机 $M$：

1. 在输入 $w$ 上并行运行 $M_1$ 和 $M_2$
2. 如果 $M_1$ 或 $M_2$ 接受，则 $M$ 接受
3. 否则 $M$ 拒绝

由于 $M_1$ 和 $M_2$ 都在多项式时间内运行，$M$ 也在多项式时间内运行。
**证毕**

#### 2.2 NP类性质

**定理 2.2.1 (NP类封闭性)**
NP类在以下运算下封闭：

1. **并集**: 如果 $L_1, L_2 \in \text{NP}$，则 $L_1 \cup L_2 \in \text{NP}$
2. **交集**: 如果 $L_1, L_2 \in \text{NP}$，则 $L_1 \cap L_2 \in \text{NP}$
3. **连接**: 如果 $L_1, L_2 \in \text{NP}$，则 $L_1 \cdot L_2 \in \text{NP}$
4. **克莱尼星号**: 如果 $L \in \text{NP}$，则 $L^* \in \text{NP}$

**注意**: NP类在补集下不一定封闭。

#### 2.3 P与NP关系

**定理 2.3.1 (P包含于NP)**
$$\text{P} \subseteq \text{NP}$$

**证明**
任何确定性图灵机都是非确定性图灵机的特例。
**证毕**

**开放问题 2.3.1 (P与NP问题)**
$$\text{P} = \text{NP}?$$

这是计算机科学中最重要的开放问题之一。

### 3. NP完全性

#### 3.1 NP完全性定义

**定义 3.1.1 (NP困难)**
语言 $L$ 是NP困难的，当且仅当对于任何 $A \in \text{NP}$，$A \leq_p L$。

**定义 3.1.2 (NP完全)**
语言 $L$ 是NP完全的，当且仅当 $L \in \text{NP}$ 且 $L$ 是NP困难的。

**定理 3.1.1 (NP完全性特征)**
如果 $L$ 是NP完全的，则：

1. $L \in \text{NP}$
2. 对于任何 $A \in \text{NP}$，$A \leq_p L$
3. 如果 $L \in \text{P}$，则 $\text{P} = \text{NP}$

#### 3.2 第一个NP完全问题

**定理 3.2.1 (库克-列文定理)**
SAT问题是NP完全的。

**证明**

1. **SAT ∈ NP**: 非确定性图灵机可以猜测赋值并在多项式时间内验证。

2. **NP困难性**: 对于任何 $L \in \text{NP}$，存在非确定性图灵机 $M$ 在多项式时间 $p(n)$ 内判定 $L$。

   构造从 $L$ 到SAT的多项式时间归约：
   - 对于输入 $w$，构造布尔公式 $\phi_w$ 使得 $\phi_w$ 可满足当且仅当 $M$ 接受 $w$
   - $\phi_w$ 描述 $M$ 在输入 $w$ 上的计算过程
   - 变量表示图灵机的配置
   - 子句确保计算的正确性

   由于 $M$ 在多项式时间内运行，$\phi_w$ 的大小也是多项式的。
**证毕**

#### 3.3 其他NP完全问题

**定理 3.3.1 (3-SAT的NP完全性)**
3-SAT问题是NP完全的。

**证明**
通过从SAT归约到3-SAT：

1. 将每个子句转换为等价的3-CNF公式
2. 使用额外的变量来保持等价性
3. 归约是多项式时间的
**证毕**

**定理 3.3.2 (团问题的NP完全性)**
团问题是NP完全的。

**证明**
通过从3-SAT归约到团问题：

1. 对于3-SAT公式 $\phi$，构造图 $G$
2. 每个子句对应图中的一个三角形
3. 不同子句中的顶点之间根据变量赋值建立边
4. $\phi$ 可满足当且仅当 $G$ 有大小为子句数量的团
**证毕**

### 4. 空间复杂性

#### 4.1 空间复杂性类

**定义 4.1.1 (L类)**
L类是可以在对数空间内被确定性图灵机判定的所有语言类：
$$\text{L} = \text{SPACE}(\log n)$$

**定义 4.1.2 (NL类)**
NL类是可以在对数空间内被非确定性图灵机判定的所有语言类：
$$\text{NL} = \text{NSPACE}(\log n)$$

**定义 4.1.3 (PSPACE类)**
PSPACE类是可以在多项式空间内被确定性图灵机判定的所有语言类：
$$\text{PSPACE} = \bigcup_{k \geq 0} \text{SPACE}(n^k)$$

#### 4.2 空间复杂性关系

**定理 4.2.1 (空间层次定理)**
对于任何空间可构造函数 $f$ 和 $g$，如果 $f(n) = o(g(n))$，则：
$$\text{SPACE}(f(n)) \subsetneq \text{SPACE}(g(n))$$

**定理 4.2.2 (萨维奇定理)**
对于任何空间可构造函数 $f(n) \geq \log n$：
$$\text{NSPACE}(f(n)) \subseteq \text{SPACE}(f^2(n))$$

**推论 4.2.1**
$$\text{NL} \subseteq \text{L}^2$$

### 5. 代码实现

#### 5.1 Rust实现

```rust
use std::collections::{HashMap, HashSet};
use std::time::{Duration, Instant};

// 复杂度分析工具
pub struct ComplexityAnalyzer {
    measurements: Vec<(usize, Duration)>,
}

impl ComplexityAnalyzer {
    pub fn new() -> Self {
        ComplexityAnalyzer {
            measurements: Vec::new(),
        }
    }

    pub fn measure<F>(&mut self, input_size: usize, algorithm: F) -> Duration
    where
        F: FnOnce() -> (),
    {
        let start = Instant::now();
        algorithm();
        let duration = start.elapsed();
        self.measurements.push((input_size, duration));
        duration
    }

    pub fn analyze_complexity(&self) -> String {
        if self.measurements.len() < 2 {
            return "需要更多数据点".to_string();
        }

        let mut ratios = Vec::new();
        for i in 1..self.measurements.len() {
            let (size1, time1) = self.measurements[i - 1];
            let (size2, time2) = self.measurements[i];
            
            let size_ratio = size2 as f64 / size1 as f64;
            let time_ratio = time2.as_nanos() as f64 / time1.as_nanos() as f64;
            
            ratios.push((size_ratio, time_ratio));
        }

        // 分析复杂度模式
        let avg_ratio = ratios.iter().map(|(_, r)| r).sum::<f64>() / ratios.len() as f64;
        
        if avg_ratio < 1.5 {
            "O(1) - 常数时间".to_string()
        } else if avg_ratio < 3.0 {
            "O(log n) - 对数时间".to_string()
        } else if avg_ratio < 10.0 {
            "O(n) - 线性时间".to_string()
        } else if avg_ratio < 100.0 {
            "O(n log n) - 线性对数时间".to_string()
        } else if avg_ratio < 1000.0 {
            "O(n²) - 平方时间".to_string()
        } else {
            "O(n^k) - 多项式时间".to_string()
        }
    }
}

// NP完全问题示例：子集和问题
pub fn subset_sum(numbers: &[i32], target: i32) -> bool {
    subset_sum_recursive(numbers, target, 0, 0)
}

fn subset_sum_recursive(numbers: &[i32], target: i32, current_sum: i32, index: usize) -> bool {
    if current_sum == target {
        return true;
    }
    
    if index >= numbers.len() || current_sum > target {
        return false;
    }
    
    // 包含当前数字
    if subset_sum_recursive(numbers, target, current_sum + numbers[index], index + 1) {
        return true;
    }
    
    // 不包含当前数字
    subset_sum_recursive(numbers, target, current_sum, index + 1)
}

// 动态规划解法（伪多项式时间）
pub fn subset_sum_dp(numbers: &[i32], target: i32) -> bool {
    let n = numbers.len();
    let mut dp = vec![vec![false; (target + 1) as usize]; n + 1];
    
    // 空子集的和为0
    for i in 0..=n {
        dp[i][0] = true;
    }
    
    for i in 1..=n {
        for j in 1..=target {
            if j >= numbers[i - 1] {
                dp[i][j as usize] = dp[i - 1][j as usize] || dp[i - 1][(j - numbers[i - 1]) as usize];
            } else {
                dp[i][j as usize] = dp[i - 1][j as usize];
            }
        }
    }
    
    dp[n][target as usize]
}

// 3-SAT问题
pub struct Clause {
    literals: Vec<(usize, bool)>, // (变量索引, 是否取反)
}

pub struct ThreeSAT {
    clauses: Vec<Clause>,
    num_variables: usize,
}

impl ThreeSAT {
    pub fn new(num_variables: usize) -> Self {
        ThreeSAT {
            clauses: Vec::new(),
            num_variables,
        }
    }

    pub fn add_clause(&mut self, literals: Vec<(usize, bool)>) {
        if literals.len() <= 3 {
            self.clauses.push(Clause { literals });
        } else {
            // 将长子句分解为3-CNF
            self.decompose_clause(&literals);
        }
    }

    fn decompose_clause(&mut self, literals: &[(usize, bool)]) {
        // 简化的分解方法
        for chunk in literals.chunks(3) {
            let mut clause_literals = chunk.to_vec();
            while clause_literals.len() < 3 {
                clause_literals.push((0, false)); // 添加虚拟变量
            }
            self.clauses.push(Clause { literals: clause_literals });
        }
    }

    pub fn is_satisfiable(&self) -> bool {
        // 暴力搜索所有可能的赋值
        for assignment in 0..(1 << self.num_variables) {
            if self.evaluate_assignment(assignment) {
                return true;
            }
        }
        false
    }

    fn evaluate_assignment(&self, assignment: usize) -> bool {
        for clause in &self.clauses {
            let mut clause_satisfied = false;
            for (var_index, negated) in &clause.literals {
                let var_value = (assignment >> var_index) & 1 == 1;
                let literal_value = if *negated { !var_value } else { var_value };
                if literal_value {
                    clause_satisfied = true;
                    break;
                }
            }
            if !clause_satisfied {
                return false;
            }
        }
        true
    }
}

// 团问题
pub struct Graph {
    vertices: usize,
    edges: Vec<(usize, usize)>,
}

impl Graph {
    pub fn new(vertices: usize) -> Self {
        Graph {
            vertices,
            edges: Vec::new(),
        }
    }

    pub fn add_edge(&mut self, u: usize, v: usize) {
        if u < self.vertices && v < self.vertices {
            self.edges.push((u, v));
        }
    }

    pub fn has_clique_of_size(&self, k: usize) -> bool {
        if k > self.vertices {
            return false;
        }

        // 生成所有大小为k的顶点子集
        let mut combination = (0..k).collect::<Vec<usize>>();
        
        loop {
            if self.is_clique(&combination) {
                return true;
            }
            
            if !self.next_combination(&mut combination, self.vertices) {
                break;
            }
        }
        
        false
    }

    fn is_clique(&self, vertices: &[usize]) -> bool {
        for i in 0..vertices.len() {
            for j in (i + 1)..vertices.len() {
                if !self.has_edge(vertices[i], vertices[j]) {
                    return false;
                }
            }
        }
        true
    }

    fn has_edge(&self, u: usize, v: usize) -> bool {
        self.edges.contains(&(u, v)) || self.edges.contains(&(v, u))
    }

    fn next_combination(&self, combination: &mut [usize], n: usize) -> bool {
        let k = combination.len();
        let mut i = k - 1;
        
        while i >= 0 && combination[i] == n - k + i {
            i -= 1;
        }
        
        if i < 0 {
            return false;
        }
        
        combination[i] += 1;
        for j in (i + 1)..k {
            combination[j] = combination[j - 1] + 1;
        }
        
        true
    }
}
```

#### 5.2 Haskell实现

```haskell
module ComplexityTheory where

import Data.List (permutations, subsequences)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Time.Clock (diffUTCTime, getCurrentTime)
import System.IO.Unsafe (unsafePerformIO)

-- 复杂度分析
data ComplexityResult = ComplexityResult {
    inputSize :: Int,
    executionTime :: Double,
    complexity :: String
} deriving (Show)

measureComplexity :: (a -> b) -> [a] -> [ComplexityResult]
measureComplexity f inputs = 
    map (\input -> 
        let start = unsafePerformIO getCurrentTime
            result = f input
            end = unsafePerformIO getCurrentTime
            time = realToFrac $ diffUTCTime end start
        in ComplexityResult (size input) time "") inputs
    where size = length . show

analyzeComplexity :: [ComplexityResult] -> String
analyzeComplexity results
    | length results < 2 = "需要更多数据点"
    | otherwise = 
        let ratios = zipWith (\r1 r2 -> 
                let sizeRatio = fromIntegral (inputSize r2) / fromIntegral (inputSize r1)
                    timeRatio = executionTime r2 / executionTime r1
                in (sizeRatio, timeRatio)) results (tail results)
            avgRatio = sum (map snd ratios) / fromIntegral (length ratios)
        in if avgRatio < 1.5
           then "O(1) - 常数时间"
           else if avgRatio < 3.0
           then "O(log n) - 对数时间"
           else if avgRatio < 10.0
           then "O(n) - 线性时间"
           else if avgRatio < 100.0
           then "O(n log n) - 线性对数时间"
           else if avgRatio < 1000.0
           then "O(n²) - 平方时间"
           else "O(n^k) - 多项式时间"

-- 子集和问题
subsetSum :: [Int] -> Int -> Bool
subsetSum numbers target = 
    any (\subset -> sum subset == target) (subsequences numbers)

subsetSumDP :: [Int] -> Int -> Bool
subsetSumDP numbers target = 
    let n = length numbers
        dp = [[i == 0 | j <- [0..target]] | i <- [0..n]]
        dp' = foldl (\dp i -> 
            foldl (\dp' j -> 
                if j >= numbers !! (i-1)
                then dp' ++ [dp !! (i-1) !! j || dp !! (i-1) !! (j - numbers !! (i-1))]
                else dp' ++ [dp !! (i-1) !! j]
            ) [] [0..target]
        ) dp [1..n]
    in dp' !! n !! target

-- 3-SAT问题
data Literal = Literal {
    varIndex :: Int,
    negated :: Bool
} deriving (Show, Eq)

data Clause = Clause {
    literals :: [Literal]
} deriving (Show)

data ThreeSAT = ThreeSAT {
    clauses :: [Clause],
    numVariables :: Int
} deriving (Show)

isSatisfiable :: ThreeSAT -> Bool
isSatisfiable sat = 
    any (\assignment -> all (evaluateClause assignment) (clauses sat)) 
        [0..(2^(numVariables sat) - 1)]

evaluateClause :: Int -> Clause -> Bool
evaluateClause assignment clause = 
    any (\literal -> 
        let varValue = (assignment `div` (2 ^ varIndex literal)) `mod` 2 == 1
        in if negated literal then not varValue else varValue
    ) (literals clause)

-- 团问题
data Graph = Graph {
    vertices :: Int,
    edges :: [(Int, Int)]
} deriving (Show)

hasCliqueOfSize :: Graph -> Int -> Bool
hasCliqueOfSize graph k = 
    any (\subset -> 
        length subset == k && isClique graph subset
    ) (subsequences [0..vertices graph - 1])

isClique :: Graph -> [Int] -> Bool
isClique graph vertices = 
    all (\(v1, v2) -> 
        v1 < v2 && hasEdge graph v1 v2
    ) [(v1, v2) | v1 <- vertices, v2 <- vertices]

hasEdge :: Graph -> Int -> Int -> Bool
hasEdge graph u v = 
    (u, v) `elem` edges graph || (v, u) `elem` edges graph

-- 示例使用
exampleSubsetSum :: [Int]
exampleSubsetSum = [3, 34, 4, 12, 5, 2]

exampleGraph :: Graph
exampleGraph = Graph {
    vertices = 4,
    edges = [(0,1), (1,2), (2,3), (0,3), (1,3)]
}

exampleThreeSAT :: ThreeSAT
exampleThreeSAT = ThreeSAT {
    clauses = [
        Clause [Literal 0 False, Literal 1 True, Literal 2 False],
        Clause [Literal 0 True, Literal 1 False, Literal 2 True]
    ],
    numVariables = 3
}

-- 测试函数
main :: IO ()
main = do
    putStrLn "Testing Subset Sum Problem:"
    putStrLn $ "subsetSum [3,34,4,12,5,2] 9 = " ++ show (subsetSum exampleSubsetSum 9)
    putStrLn $ "subsetSumDP [3,34,4,12,5,2] 9 = " ++ show (subsetSumDP exampleSubsetSum 9)
    
    putStrLn "\nTesting Clique Problem:"
    putStrLn $ "hasCliqueOfSize exampleGraph 3 = " ++ show (hasCliqueOfSize exampleGraph 3)
    putStrLn $ "hasCliqueOfSize exampleGraph 4 = " ++ show (hasCliqueOfSize exampleGraph 4)
    
    putStrLn "\nTesting 3-SAT Problem:"
    putStrLn $ "isSatisfiable exampleThreeSAT = " ++ show (isSatisfiable exampleThreeSAT)
    
    putStrLn "\nComplexity Analysis:"
    let results = measureComplexity length ["a", "ab", "abc", "abcd", "abcde"]
    putStrLn $ "Complexity: " ++ analyzeComplexity results
```

### 6. 应用领域

#### 6.1 算法设计

复杂性理论在算法设计中用于：

- 算法效率分析
- 最优算法设计
- 近似算法设计

#### 6.2 密码学

- 公钥密码系统
- 数字签名
- 零知识证明

#### 6.3 人工智能

- 机器学习算法
- 优化问题
- 搜索算法

### 7. 交叉引用

#### 7.1 相关理论

- [形式语言理论基础](01_Formal_Language_Foundation.md)
- [可计算性理论](07_Computability_Theory.md)
- [自动机理论](06_Automata_Theory.md)
- [算法设计](../07_Software_Engineering/07.3_Software_Design.md)

#### 7.2 应用领域

- [密码学](../04_Distributed_Systems/04.8_Distributed_Security.md)
- [人工智能](../11_AI_Computing/11.1_AI_Foundation.md)
- [优化理论](../03_Control_Theory/03.4_Optimal_Control_Theory.md)

---

**参考文献**

1. Sipser, M. (2012). Introduction to the Theory of Computation.
2. Arora, S., & Barak, B. (2009). Computational Complexity: A Modern Approach.
3. Papadimitriou, C. H. (1994). Computational Complexity.

---

**相关文档**

- [形式语言理论基础](01_Formal_Language_Foundation.md)
- [可计算性理论](07_Computability_Theory.md)
- [自动机理论](06_Automata_Theory.md)
- [算法设计](../07_Software_Engineering/07.3_Software_Design.md)
