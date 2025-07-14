# 确定性有限自动机理论 (Deterministic Finite Automaton Theory)

## 📋 概述

确定性有限自动机（DFA）是形式语言理论的基础，是计算理论的核心概念。本文档建立了严格的DFA形式化体系，包括基本概念、形式化定义、算法实现和应用实例。

## 📚 目录

- [确定性有限自动机理论 (Deterministic Finite Automaton Theory)](#确定性有限自动机理论-deterministic-finite-automaton-theory)
  - [📋 概述](#-概述)
  - [📚 目录](#-目录)
  - [交叉引用](#交叉引用)
  - [1. 基本概念](#1-基本概念)
    - [1.1 DFA的定义](#11-dfa的定义)
    - [1.2 DFA的基本性质](#12-dfa的基本性质)
  - [2. 形式化定义](#2-形式化定义)
    - [2.1 语言接受](#21-语言接受)
    - [2.2 扩展转移函数](#22-扩展转移函数)
  - [3. DFA的性质](#3-dfa的性质)
    - [3.1 正则性](#31-正则性)
    - [3.2 封闭性](#32-封闭性)
    - [3.3 可判定性](#33-可判定性)
  - [4. DFA的运算](#4-dfa的运算)
    - [4.1 乘积构造](#41-乘积构造)
    - [4.2 补集构造](#42-补集构造)
  - [5. DFA的等价性](#5-dfa的等价性)
    - [5.1 等价性定义](#51-等价性定义)
    - [5.2 等价性判定](#52-等价性判定)
  - [6. DFA的最小化](#6-dfa的最小化)
    - [6.1 最小化定义](#61-最小化定义)
    - [6.2 最小化算法](#62-最小化算法)
  - [7. DFA定理](#7-dfa定理)
    - [7.1 基本定理](#71-基本定理)
    - [7.2 高级定理](#72-高级定理)
  - [8. DFA算法](#8-dfa算法)
    - [8.1 DFA实现](#81-dfa实现)
    - [8.2 DFA运算算法](#82-dfa运算算法)
  - [9. 应用实例](#9-应用实例)
    - [9.1 字符串匹配](#91-字符串匹配)
    - [9.2 语言运算](#92-语言运算)
    - [9.3 编译器应用](#93-编译器应用)
  - [10. 参考文献](#10-参考文献)
  - [批判性分析](#批判性分析)

## 交叉引用

- [Mealy机](02_Mealy_Machine.md)
- [Moore机](03_Moore_Machine.md)
- [有限自动机基础](01_Finite_Automata_Basics.md)
- [自动机理论总览](../README.md)
- [正则语言](../../02_Regular_Languages.md)
- [形式文法](../../03.2_Formal_Grammars.md)
- [计算理论](../README.md)
- [上下文系统](../README.md)

## 1. 基本概念

### 1.1 DFA的定义

**定义 1.1 (确定性有限自动机)**
确定性有限自动机（DFA）是一个五元组 $M = (Q, \Sigma, \delta, q_0, F)$，其中：

- $Q$ 是有限状态集
- $\Sigma$ 是有限输入字母表
- $\delta: Q \times \Sigma \rightarrow Q$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $F \subseteq Q$ 是接受状态集

**定义 1.2 (配置)**
DFA的配置是一个二元组 $(q, w)$，其中：

- $q \in Q$ 是当前状态
- $w \in \Sigma^*$ 是剩余输入串

**定义 1.3 (转移关系)**
转移关系 $\vdash_M$ 定义为：
$$(q, aw) \vdash_M (q', w) \text{ 当且仅当 } \delta(q, a) = q'$$

**定义 1.4 (多步转移)**
多步转移 $\vdash_M^*$ 是 $\vdash_M$ 的自反传递闭包。

### 1.2 DFA的基本性质

**公理 1.1 (确定性)**
对于任意状态 $q$ 和输入符号 $a$，转移函数 $\delta$ 是确定的：
$$\forall q \in Q \forall a \in \Sigma \exists! q' \in Q(\delta(q, a) = q')$$

**公理 1.2 (有限性)**
状态集和字母表都是有限的：
$$|Q| < \infty \land |\Sigma| < \infty$$

**公理 1.3 (完整性)**
转移函数对所有状态和输入符号都有定义：
$$\forall q \in Q \forall a \in \Sigma(\delta(q, a) \text{ 有定义})$$

## 2. 形式化定义

### 2.1 语言接受

**定义 2.1 (语言接受)**
DFA $M$ 接受字符串 $w$，当且仅当：
$$(q_0, w) \vdash_M^* (q, \varepsilon) \text{ 且 } q \in F$$

**定义 2.2 (接受的语言)**
DFA $M$ 接受的语言定义为：
$$L(M) = \{w \in \Sigma^* \mid M \text{ 接受 } w\}$$

**定义 2.3 (状态可达性)**
状态 $q$ 从状态 $p$ 可达，当且仅当存在字符串 $w$ 使得：
$$(p, w) \vdash_M^* (q, \varepsilon)$$

### 2.2 扩展转移函数

**定义 2.4 (扩展转移函数)**
扩展转移函数 $\delta^*: Q \times \Sigma^* \rightarrow Q$ 递归定义为：

1. $\delta^*(q, \varepsilon) = q$
2. $\delta^*(q, wa) = \delta(\delta^*(q, w), a)$

**定理 2.1 (扩展转移函数的正确性)**
对于任意字符串 $w$ 和状态 $q$：
$$(q, w) \vdash_M^* (\delta^*(q, w), \varepsilon)$$

**证明**：

1. 基础情况：$w = \varepsilon$
   - $\delta^*(q, \varepsilon) = q$
   - $(q, \varepsilon) \vdash_M^* (q, \varepsilon)$

2. 归纳步骤：$w = va$，其中 $v \in \Sigma^*$，$a \in \Sigma$
   - 根据归纳假设：$(q, v) \vdash_M^* (\delta^*(q, v), \varepsilon)$
   - 根据转移关系：$(\delta^*(q, v), a) \vdash_M (\delta(\delta^*(q, v), a), \varepsilon)$
   - 因此：$(q, va) \vdash_M^* (\delta(\delta^*(q, v), a), \varepsilon)$
   - 根据定义：$\delta^*(q, va) = \delta(\delta^*(q, v), a)$

## 3. DFA的性质

### 3.1 正则性

**定义 3.1 (正则语言)**
语言 $L$ 是正则的，当且仅当存在DFA $M$ 使得 $L = L(M)$。

**定理 3.1 (DFA接受的语言是正则的)**
如果 $L = L(M)$ 对于某个DFA $M$，那么 $L$ 是正则的。

**证明**：

1. 根据定义，$L(M)$ 是DFA接受的语言
2. 根据正则语言的定义，$L(M)$ 是正则的
3. 因此 $L$ 是正则的

### 3.2 封闭性

**定理 3.2 (正则语言的封闭性)**
正则语言在以下运算下是封闭的：

1. 并集
2. 交集
3. 补集
4. 连接
5. 克林星号

**证明**：

1. **并集封闭性**：
   - 设 $L_1 = L(M_1)$，$L_2 = L(M_2)$
   - 构造DFA $M$ 接受 $L_1 \cup L_2$
   - 使用乘积构造法

2. **交集封闭性**：
   - 设 $L_1 = L(M_1)$，$L_2 = L(M_2)$
   - 构造DFA $M$ 接受 $L_1 \cap L_2$
   - 使用乘积构造法

3. **补集封闭性**：
   - 设 $L = L(M)$
   - 构造DFA $M'$ 接受 $\Sigma^* \setminus L$
   - 交换接受状态和非接受状态

### 3.3 可判定性

**定理 3.3 (DFA问题的可判定性)**
以下问题对于DFA是可判定的：

1. 成员问题：给定DFA $M$ 和字符串 $w$，判断 $w \in L(M)$
2. 空性问题：给定DFA $M$，判断 $L(M) = \emptyset$
3. 有限性问题：给定DFA $M$，判断 $L(M)$ 是否有限
4. 等价性问题：给定两个DFA $M_1$ 和 $M_2$，判断 $L(M_1) = L(M_2)$

**证明**：

1. **成员问题**：
   - 模拟DFA在输入 $w$ 上的运行
   - 时间复杂度：$O(|w|)$

2. **空性问题**：
   - 检查是否存在从初始状态到接受状态的路径
   - 使用可达性算法

3. **有限性问题**：
   - 检查DFA是否包含循环
   - 使用深度优先搜索

4. **等价性问题**：
   - 构造接受对称差集的DFA
   - 检查该DFA是否为空

## 4. DFA的运算

### 4.1 乘积构造

**定义 4.1 (乘积DFA)**
给定两个DFA $M_1 = (Q_1, \Sigma, \delta_1, q_{01}, F_1)$ 和 $M_2 = (Q_2, \Sigma, \delta_2, q_{02}, F_2)$，它们的乘积DFA定义为：
$$M_1 \times M_2 = (Q_1 \times Q_2, \Sigma, \delta, (q_{01}, q_{02}), F)$$
其中：

- $\delta((q_1, q_2), a) = (\delta_1(q_1, a), \delta_2(q_2, a))$
- $F$ 根据运算类型确定

**定理 4.1 (乘积构造的正确性)**:

1. 对于并集：$F = (F_1 \times Q_2) \cup (Q_1 \times F_2)$
2. 对于交集：$F = F_1 \times F_2$
3. 对于差集：$F = F_1 \times (Q_2 \setminus F_2)$

### 4.2 补集构造

**定义 4.2 (补集DFA)**
给定DFA $M = (Q, \Sigma, \delta, q_0, F)$，它的补集DFA定义为：
$$M^c = (Q, \Sigma, \delta, q_0, Q \setminus F)$$

**定理 4.2 (补集构造的正确性)**
$$L(M^c) = \Sigma^* \setminus L(M)$$

**证明**：

1. 对于任意字符串 $w$：
   - $w \in L(M^c)$ 当且仅当 $\delta^*(q_0, w) \in Q \setminus F$
   - $w \in L(M^c)$ 当且仅当 $\delta^*(q_0, w) \notin F$
   - $w \in L(M^c)$ 当且仅当 $w \notin L(M)$
   - 因此 $L(M^c) = \Sigma^* \setminus L(M)$

## 5. DFA的等价性

### 5.1 等价性定义

**定义 5.1 (DFA等价性)**
两个DFA $M_1$ 和 $M_2$ 等价，当且仅当 $L(M_1) = L(M_2)$。

**定义 5.2 (状态等价性)**
两个状态 $q_1$ 和 $q_2$ 等价，当且仅当对于任意字符串 $w$：
$$\delta^*(q_1, w) \in F \leftrightarrow \delta^*(q_2, w) \in F$$

### 5.2 等价性判定

**算法 5.1 (等价性判定算法)**:

```rust
/// 等价性判定算法
pub fn are_equivalent(dfa1: &DFA, dfa2: &DFA) -> bool {
    // 构造接受对称差集的DFA
    let symmetric_difference = dfa1.symmetric_difference(dfa2);
    
    // 检查对称差集是否为空
    symmetric_difference.is_empty()
}
```

**定理 5.1 (等价性判定的正确性)**
两个DFA等价当且仅当它们的对称差集为空。

**证明**：

1. 如果 $L(M_1) = L(M_2)$，那么 $L(M_1) \triangle L(M_2) = \emptyset$
2. 如果 $L(M_1) \triangle L(M_2) = \emptyset$，那么 $L(M_1) = L(M_2)$
3. 因此等价性判定算法是正确的

## 6. DFA的最小化

### 6.1 最小化定义

**定义 6.1 (最小DFA)**
DFA $M$ 是最小的，当且仅当不存在等价的状态数更少的DFA。

**定义 6.2 (不可区分状态)**
两个状态 $q_1$ 和 $q_2$ 不可区分，当且仅当它们等价。

### 6.2 最小化算法

**算法 6.1 (Hopcroft最小化算法)**:

```rust
/// Hopcroft最小化算法
pub fn minimize_dfa(dfa: &DFA) -> DFA {
    let mut partitions = vec![
        dfa.accepting_states().clone(),
        dfa.non_accepting_states().clone()
    ];
    
    loop {
        let mut new_partitions = Vec::new();
        
        for partition in &partitions {
            if partition.len() <= 1 {
                new_partitions.push(partition.clone());
                continue;
            }
            
            // 根据转移函数分割分区
            let sub_partitions = split_partition(partition, &dfa, &partitions);
            new_partitions.extend(sub_partitions);
        }
        
        if new_partitions.len() == partitions.len() {
            break;
        }
        
        partitions = new_partitions;
    }
    
    // 构造最小DFA
    construct_minimal_dfa(dfa, &partitions)
}
```

**定理 6.1 (最小化算法的正确性)**
Hopcroft算法产生等价的最小DFA。

**证明**：

1. 算法保持语言等价性
2. 算法产生不可分割的分区
3. 最小DFA的状态数等于等价类的数量
4. 因此算法产生最小DFA

## 7. DFA定理

### 7.1 基本定理

**定理 7.1 (DFA状态数下界)**
如果DFA $M$ 接受语言 $L$，那么 $M$ 的状态数至少为 $L$ 的Myhill-Nerode等价类的数量。

**证明**：

1. 设 $L$ 的Myhill-Nerode等价类为 $[w_1], [w_2], \ldots, [w_n]$
2. 对于每个等价类 $[w_i]$，存在状态 $q_i$ 使得 $\delta^*(q_0, w_i) = q_i$
3. 如果 $[w_i] \neq [w_j]$，那么 $q_i \neq q_j$
4. 因此DFA至少需要 $n$ 个状态

**定理 7.2 (DFA唯一性)**
对于每个正则语言 $L$，存在唯一的最小DFA（在同构意义下）。

**证明**：

1. 最小DFA的状态对应于Myhill-Nerode等价类
2. Myhill-Nerode等价类是唯一的
3. 因此最小DFA在同构意义下是唯一的

### 7.2 高级定理

**定理 7.3 (泵引理)**
对于正则语言 $L$，存在常数 $n$ 使得对于任意字符串 $w \in L$ 且 $|w| \geq n$，存在分解 $w = xyz$ 满足：

1. $|xy| \leq n$
2. $|y| > 0$
3. 对于任意 $i \geq 0$，$xy^i z \in L$

**证明**：

1. 设DFA $M$ 接受 $L$，状态数为 $n$
2. 对于字符串 $w$ 且 $|w| \geq n$，在运行过程中至少有一个状态被访问两次
3. 设 $q$ 是第一个重复访问的状态
4. 设 $x$ 是从初始状态到第一次访问 $q$ 的输入
5. 设 $y$ 是从第一次访问 $q$ 到第二次访问 $q$ 的输入
6. 设 $z$ 是从第二次访问 $q$ 到接受状态的输入
7. 因此 $w = xyz$ 满足泵引理条件

## 8. DFA算法

### 8.1 DFA实现

```rust
/// 确定性有限自动机
pub struct DFA {
    states: Vec<State>,
    alphabet: Vec<Symbol>,
    transitions: HashMap<(State, Symbol), State>,
    initial_state: State,
    accepting_states: HashSet<State>,
}

/// 状态类型
pub type State = usize;

/// 符号类型
pub type Symbol = char;

impl DFA {
    /// 构造新的DFA
    pub fn new(
        states: Vec<State>,
        alphabet: Vec<Symbol>,
        transitions: HashMap<(State, Symbol), State>,
        initial_state: State,
        accepting_states: HashSet<State>,
    ) -> Self {
        Self {
            states,
            alphabet,
            transitions,
            initial_state,
            accepting_states,
        }
    }
    
    /// 检查字符串是否被接受
    pub fn accepts(&self, input: &str) -> bool {
        let mut current_state = self.initial_state;
        
        for symbol in input.chars() {
            if let Some(&next_state) = self.transitions.get(&(current_state, symbol)) {
                current_state = next_state;
            } else {
                return false; // 转移函数未定义
            }
        }
        
        self.accepting_states.contains(&current_state)
    }
    
    /// 计算扩展转移函数
    pub fn extended_delta(&self, state: State, input: &str) -> Option<State> {
        let mut current_state = state;
        
        for symbol in input.chars() {
            if let Some(&next_state) = self.transitions.get(&(current_state, symbol)) {
                current_state = next_state;
            } else {
                return None;
            }
        }
        
        Some(current_state)
    }
    
    /// 获取接受的语言
    pub fn accepted_language(&self) -> Vec<String> {
        // 使用BFS生成所有接受的字符串
        let mut accepted = Vec::new();
        let mut queue = VecDeque::new();
        queue.push_back((self.initial_state, String::new()));
        
        while let Some((state, string)) = queue.pop_front() {
            if self.accepting_states.contains(&state) {
                accepted.push(string.clone());
            }
            
            // 限制字符串长度以避免无限循环
            if string.len() < 10 {
                for &symbol in &self.alphabet {
                    if let Some(&next_state) = self.transitions.get(&(state, symbol)) {
                        let mut new_string = string.clone();
                        new_string.push(symbol);
                        queue.push_back((next_state, new_string));
                    }
                }
            }
        }
        
        accepted
    }
    
    /// 检查DFA是否为空
    pub fn is_empty(&self) -> bool {
        // 检查是否存在从初始状态到接受状态的路径
        let mut visited = HashSet::new();
        let mut stack = vec![self.initial_state];
        
        while let Some(state) = stack.pop() {
            if self.accepting_states.contains(&state) {
                return false;
            }
            
            if visited.insert(state) {
                for &symbol in &self.alphabet {
                    if let Some(&next_state) = self.transitions.get(&(state, symbol)) {
                        stack.push(next_state);
                    }
                }
            }
        }
        
        true
    }
    
    /// 检查DFA是否接受有限语言
    pub fn is_finite(&self) -> bool {
        // 检查是否存在循环
        let mut visited = HashSet::new();
        let mut rec_stack = HashSet::new();
        
        fn has_cycle(
            dfa: &DFA,
            state: State,
            visited: &mut HashSet<State>,
            rec_stack: &mut HashSet<State>,
        ) -> bool {
            visited.insert(state);
            rec_stack.insert(state);
            
            for &symbol in &dfa.alphabet {
                if let Some(&next_state) = dfa.transitions.get(&(state, symbol)) {
                    if !visited.contains(&next_state) {
                        if has_cycle(dfa, next_state, visited, rec_stack) {
                            return true;
                        }
                    } else if rec_stack.contains(&next_state) {
                        return true;
                    }
                }
            }
            
            rec_stack.remove(&state);
            false
        }
        
        !has_cycle(self, self.initial_state, &mut visited, &mut rec_stack)
    }
}
```

### 8.2 DFA运算算法

```rust
impl DFA {
    /// 构造补集DFA
    pub fn complement(&self) -> DFA {
        let new_accepting_states: HashSet<State> = self
            .states
            .iter()
            .filter(|&&state| !self.accepting_states.contains(&state))
            .cloned()
            .collect();
        
        DFA::new(
            self.states.clone(),
            self.alphabet.clone(),
            self.transitions.clone(),
            self.initial_state,
            new_accepting_states,
        )
    }
    
    /// 构造乘积DFA（用于交集）
    pub fn intersection(&self, other: &DFA) -> DFA {
        let mut new_transitions = HashMap::new();
        let mut new_states = Vec::new();
        let mut new_accepting_states = HashSet::new();
        
        // 构造乘积状态
        for &state1 in &self.states {
            for &state2 in &other.states {
                let product_state = (state1, state2);
                new_states.push(product_state);
                
                // 构造转移函数
                for &symbol in &self.alphabet {
                    if let (Some(&next1), Some(&next2)) = (
                        self.transitions.get(&(state1, symbol)),
                        other.transitions.get(&(state2, symbol)),
                    ) {
                        new_transitions.insert((product_state, symbol), (next1, next2));
                    }
                }
                
                // 确定接受状态
                if self.accepting_states.contains(&state1) && other.accepting_states.contains(&state2) {
                    new_accepting_states.insert(product_state);
                }
            }
        }
        
        DFA::new(
            new_states,
            self.alphabet.clone(),
            new_transitions,
            (self.initial_state, other.initial_state),
            new_accepting_states,
        )
    }
    
    /// 构造并集DFA
    pub fn union(&self, other: &DFA) -> DFA {
        let mut new_transitions = HashMap::new();
        let mut new_states = Vec::new();
        let mut new_accepting_states = HashSet::new();
        
        // 构造乘积状态
        for &state1 in &self.states {
            for &state2 in &other.states {
                let product_state = (state1, state2);
                new_states.push(product_state);
                
                // 构造转移函数
                for &symbol in &self.alphabet {
                    if let (Some(&next1), Some(&next2)) = (
                        self.transitions.get(&(state1, symbol)),
                        other.transitions.get(&(state2, symbol)),
                    ) {
                        new_transitions.insert((product_state, symbol), (next1, next2));
                    }
                }
                
                // 确定接受状态
                if self.accepting_states.contains(&state1) || other.accepting_states.contains(&state2) {
                    new_accepting_states.insert(product_state);
                }
            }
        }
        
        DFA::new(
            new_states,
            self.alphabet.clone(),
            new_transitions,
            (self.initial_state, other.initial_state),
            new_accepting_states,
        )
    }
    
    /// 最小化DFA
    pub fn minimize(&self) -> DFA {
        // 实现Hopcroft最小化算法
        let mut partitions = vec![
            self.accepting_states.clone(),
            self.states
                .iter()
                .filter(|&&s| !self.accepting_states.contains(&s))
                .cloned()
                .collect::<HashSet<_>>(),
        ];
        
        loop {
            let mut new_partitions = Vec::new();
            
            for partition in &partitions {
                if partition.len() <= 1 {
                    new_partitions.push(partition.clone());
                    continue;
                }
                
                // 分割分区
                let sub_partitions = self.split_partition(partition, &partitions);
                new_partitions.extend(sub_partitions);
            }
            
            if new_partitions.len() == partitions.len() {
                break;
            }
            
            partitions = new_partitions;
        }
        
        // 构造最小DFA
        self.construct_minimal_dfa(&partitions)
    }
    
    /// 分割分区
    fn split_partition(&self, partition: &HashSet<State>, partitions: &[HashSet<State>]) -> Vec<HashSet<State>> {
        let mut sub_partitions = Vec::new();
        let mut current_partition = partition.clone();
        
        for &symbol in &self.alphabet {
            let mut groups = HashMap::new();
            
            for &state in &current_partition {
                if let Some(&next_state) = self.transitions.get(&(state, symbol)) {
                    let partition_index = partitions
                        .iter()
                        .position(|p| p.contains(&next_state))
                        .unwrap_or(0);
                    
                    groups.entry(partition_index).or_insert_with(HashSet::new).insert(state);
                }
            }
            
            if groups.len() > 1 {
                // 分割分区
                for group in groups.values() {
                    if !group.is_empty() {
                        sub_partitions.push(group.clone());
                    }
                }
                return sub_partitions;
            }
        }
        
        vec![current_partition]
    }
    
    /// 构造最小DFA
    fn construct_minimal_dfa(&self, partitions: &[HashSet<State>]) -> DFA {
        let mut new_states = Vec::new();
        let mut new_transitions = HashMap::new();
        let mut new_accepting_states = HashSet::new();
        let mut state_mapping = HashMap::new();
        
        // 构造新状态
        for (i, partition) in partitions.iter().enumerate() {
            new_states.push(i);
            
            for &state in partition {
                state_mapping.insert(state, i);
            }
            
            // 确定接受状态
            if partition.iter().any(|&s| self.accepting_states.contains(&s)) {
                new_accepting_states.insert(i);
            }
        }
        
        // 构造转移函数
        for (i, partition) in partitions.iter().enumerate() {
            for &state in partition {
                for &symbol in &self.alphabet {
                    if let Some(&next_state) = self.transitions.get(&(state, symbol)) {
                        if let Some(&new_next_state) = state_mapping.get(&next_state) {
                            new_transitions.insert((i, symbol), new_next_state);
                        }
                    }
                }
            }
        }
        
        // 确定初始状态
        let new_initial_state = state_mapping[&self.initial_state];
        
        DFA::new(
            new_states,
            self.alphabet.clone(),
            new_transitions,
            new_initial_state,
            new_accepting_states,
        )
    }
}
```

## 9. 应用实例

### 9.1 字符串匹配

**实例 9.1 (模式匹配)**
构造DFA识别包含子串"ab"的字符串：

```rust
// 构造DFA
let dfa = DFA::new(
    vec![0, 1, 2],  // 状态：0=初始，1=看到'a'，2=接受
    vec!['a', 'b'],
    HashMap::from([
        ((0, 'a'), 1),
        ((0, 'b'), 0),
        ((1, 'a'), 1),
        ((1, 'b'), 2),
        ((2, 'a'), 2),
        ((2, 'b'), 2),
    ]),
    0,  // 初始状态
    HashSet::from([2]),  // 接受状态
);

// 测试
assert!(dfa.accepts("ab"));
assert!(dfa.accepts("cab"));
assert!(dfa.accepts("abab"));
assert!(!dfa.accepts("ac"));
assert!(!dfa.accepts("ba"));
```

**实例 9.2 (数字识别)**
构造DFA识别偶数个0的二进制串：

```rust
// 构造DFA
let dfa = DFA::new(
    vec![0, 1],  // 状态：0=偶数个0，1=奇数个0
    vec!['0', '1'],
    HashMap::from([
        ((0, '0'), 1),
        ((0, '1'), 0),
        ((1, '0'), 0),
        ((1, '1'), 1),
    ]),
    0,  // 初始状态
    HashSet::from([0]),  // 接受状态
);

// 测试
assert!(dfa.accepts(""));
assert!(dfa.accepts("1"));
assert!(dfa.accepts("00"));
assert!(dfa.accepts("101"));
assert!(!dfa.accepts("0"));
assert!(!dfa.accepts("01"));
```

### 9.2 语言运算

**实例 9.3 (语言运算)**:

```rust
// 构造两个DFA
let dfa1 = construct_dfa_for_pattern("ab");
let dfa2 = construct_dfa_for_pattern("bc");

// 计算交集
let intersection = dfa1.intersection(&dfa2);
assert!(intersection.accepts("abc"));

// 计算并集
let union = dfa1.union(&dfa2);
assert!(union.accepts("ab"));
assert!(union.accepts("bc"));

// 计算补集
let complement = dfa1.complement();
assert!(!complement.accepts("ab"));
assert!(complement.accepts("ac"));
```

### 9.3 编译器应用

**实例 9.4 (词法分析器)**:

```rust
// 构造标识符DFA
let identifier_dfa = DFA::new(
    vec![0, 1, 2],  // 状态：0=初始，1=字母，2=字母或数字
    vec!['a', 'b', '0', '1', '_'],
    HashMap::from([
        ((0, 'a'), 1), ((0, 'b'), 1), ((0, '_'), 1),
        ((1, 'a'), 2), ((1, 'b'), 2), ((1, '0'), 2), ((1, '1'), 2), ((1, '_'), 2),
        ((2, 'a'), 2), ((2, 'b'), 2), ((2, '0'), 2), ((2, '1'), 2), ((2, '_'), 2),
    ]),
    0,
    HashSet::from([1, 2]),
);

// 词法分析
fn tokenize(input: &str) -> Vec<Token> {
    let mut tokens = Vec::new();
    let mut current = String::new();
    
    for ch in input.chars() {
        if identifier_dfa.accepts(&format!("{}{}", current, ch)) {
            current.push(ch);
        } else {
            if !current.is_empty() {
                tokens.push(Token::Identifier(current.clone()));
                current.clear();
            }
            // 处理其他字符...
        }
    }
    
    if !current.is_empty() {
        tokens.push(Token::Identifier(current));
    }
    
    tokens
}
```

## 10. 参考文献

1. Hopcroft, J.E., Motwani, R., & Ullman, J.D. *Introduction to Automata Theory, Languages, and Computation*. Addison-Wesley, 2006.
2. Sipser, M. *Introduction to the Theory of Computation*. Cengage Learning, 2012.
3. Kozen, D.C. *Automata and Computability*. Springer, 1997.
4. Lewis, H.R., & Papadimitriou, C.H. *Elements of the Theory of Computation*. Prentice Hall, 1998.
5. Hopcroft, J.E., & Ullman, J.D. *Introduction to Automata Theory, Languages, and Computation*. Addison-Wesley, 1979.
6. Aho, A.V., Lam, M.S., Sethi, R., & Ullman, J.D. *Compilers: Principles, Techniques, and Tools*. Addison-Wesley, 2006.
7. Grune, D., & Jacobs, C.J.H. *Parsing Techniques: A Practical Guide*. Springer, 2008.
8. Brzozowski, J.A. *Canonical Regular Expressions and Minimal State Graphs for Definite Events*. Mathematical Theory of Automata, 1962.

---

**最后更新时间**: 2024年12月20日  
**版本**: v1.0  
**维护者**: 形式语言理论团队

## 批判性分析

- 本节内容待补充：请从多元理论视角、局限性、争议点、应用前景等方面进行批判性分析。
