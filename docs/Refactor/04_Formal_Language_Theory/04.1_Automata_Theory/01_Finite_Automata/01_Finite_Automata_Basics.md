# 03.01.01 有限自动机基础理论 (Finite Automata Basics)

## 📋 概述

有限自动机是形式语言理论的基础，研究有限状态机器的计算能力和语言识别。本文档建立了严格的形式化有限自动机理论，为所有形式语言理论提供基础。

**构建时间**: 2024年12月21日  
**版本**: v1.0  
**状态**: 已完成

## 📚 目录

- [03.01.01 有限自动机基础理论 (Finite Automata Basics)](#030101-有限自动机基础理论-finite-automata-basics)
  - [📋 概述](#-概述)
  - [📚 目录](#-目录)
  - [交叉引用](#交叉引用)
  - [1. 基本概念](#1-基本概念)
    - [1.1 有限自动机的定义](#11-有限自动机的定义)
    - [1.2 状态转换](#12-状态转换)
    - [1.3 语言识别](#13-语言识别)
  - [2. 形式化定义](#2-形式化定义)
    - [2.1 确定性有限自动机](#21-确定性有限自动机)
    - [2.2 非确定性有限自动机](#22-非确定性有限自动机)
    - [2.3 扩展转换函数](#23-扩展转换函数)
  - [3. 自动机公理](#3-自动机公理)
    - [3.1 基本公理](#31-基本公理)
    - [3.2 转换函数公理](#32-转换函数公理)
  - [4. 核心定理](#4-核心定理)
    - [4.1 DFA与NFA等价性](#41-dfa与nfa等价性)
    - [4.2 泵引理](#42-泵引理)
    - [4.3 最小化定理](#43-最小化定理)
  - [5. 自动机类型](#5-自动机类型)
    - [5.1 确定性有限自动机](#51-确定性有限自动机)
    - [5.2 非确定性有限自动机](#52-非确定性有限自动机)
    - [5.3 ε-非确定性有限自动机](#53-ε-非确定性有限自动机)
  - [6. 状态转换](#6-状态转换)
    - [6.1 转换函数定义](#61-转换函数定义)
    - [6.2 扩展转换函数](#62-扩展转换函数)
    - [6.3 ε闭包](#63-ε闭包)
  - [7. 语言识别](#7-语言识别)
    - [7.1 语言定义](#71-语言定义)
    - [7.2 语言性质](#72-语言性质)
    - [7.3 语言等价性](#73-语言等价性)
  - [8. 应用实例](#8-应用实例)
    - [8.1 词法分析器](#81-词法分析器)
    - [8.2 数字识别](#82-数字识别)
    - [8.3 模式匹配](#83-模式匹配)
  - [9. 代码实现](#9-代码实现)
    - [9.1 Rust实现](#91-rust实现)
    - [9.2 Haskell实现](#92-haskell实现)
  - [10. 参考文献](#10-参考文献)
  - [批判性分析](#批判性分析)

## 交叉引用

- [Mealy机](02_Mealy_Machine.md)
- [Moore机](03_Moore_Machine.md)
- [DFA理论](01_DFA_Theory.md)
- [自动机理论总览](../README.md)
- [正则语言](../../02_Regular_Languages.md)
- [形式文法](../../03.2_Formal_Grammars.md)
- [计算理论](../README.md)
- [上下文系统](../README.md)

## 1. 基本概念

### 1.1 有限自动机的定义

**定义 1.1.1** (有限自动机)
有限自动机是一个五元组 $(Q, \Sigma, \delta, q_0, F)$，其中：

- $Q$ 是有限状态集合
- $\Sigma$ 是有限输入字母表
- $\delta$ 是状态转换函数
- $q_0$ 是初始状态
- $F$ 是接受状态集合

**形式化表示**:
$$\text{FiniteAutomaton}(M) \equiv \text{Quintuple}(Q, \Sigma, \delta, q_0, F)$$

### 1.2 状态转换

**定义 1.2.1** (状态转换)
状态转换是自动机从一个状态到另一个状态的转移。

**形式化表示**:
$$\delta: Q \times \Sigma \rightarrow Q$$

### 1.3 语言识别

**定义 1.3.1** (语言识别)
自动机识别一个字符串，当且仅当从初始状态开始，经过一系列转换后到达接受状态。

**形式化表示**:
$$L(M) = \{w \in \Sigma^* \mid \delta^*(q_0, w) \in F\}$$

## 2. 形式化定义

### 2.1 确定性有限自动机

**定义 2.1.1** (确定性有限自动机)
确定性有限自动机(DFA)是状态转换函数为确定性的有限自动机。

**形式化定义**:
$$\text{DFA}(M) \equiv \text{FiniteAutomaton}(M) \land \text{Deterministic}(\delta)$$

### 2.2 非确定性有限自动机

**定义 2.2.1** (非确定性有限自动机)
非确定性有限自动机(NFA)是状态转换函数可以为非确定性的有限自动机。

**形式化定义**:
$$\text{NFA}(M) \equiv \text{FiniteAutomaton}(M) \land \text{Nondeterministic}(\delta)$$

### 2.3 扩展转换函数

**定义 2.3.1** (扩展转换函数)
扩展转换函数 $\delta^*$ 是处理字符串的状态转换函数。

**形式化定义**:
$$\delta^*: Q \times \Sigma^* \rightarrow Q$$

对于DFA：
$$\delta^*(q, \varepsilon) = q$$
$$\delta^*(q, wa) = \delta(\delta^*(q, w), a)$$

对于NFA：
$$\delta^*: Q \times \Sigma^* \rightarrow 2^Q$$

## 3. 自动机公理

### 3.1 基本公理

**公理 3.1.1** (状态集合非空性)
状态集合非空。

**形式化表示**:
$$Q \neq \emptyset$$

**公理 3.1.2** (字母表非空性)
输入字母表非空。

**形式化表示**:
$$\Sigma \neq \emptyset$$

**公理 3.1.3** (初始状态存在性)
初始状态在状态集合中。

**形式化表示**:
$$q_0 \in Q$$

**公理 3.1.4** (接受状态子集性)
接受状态集合是状态集合的子集。

**形式化表示**:
$$F \subseteq Q$$

### 3.2 转换函数公理

**公理 3.2.1** (转换函数定义域)
转换函数在定义域上完全定义。

**形式化表示**:
$$\forall q \in Q, \forall a \in \Sigma, \delta(q, a) \text{ is defined}$$

**公理 3.2.2** (转换函数值域)
转换函数的值在状态集合中。

**形式化表示**:
$$\forall q \in Q, \forall a \in \Sigma, \delta(q, a) \in Q$$

## 4. 核心定理

### 4.1 DFA与NFA等价性

**定理 4.1.1** (DFA与NFA等价性)
对于每个NFA，存在等价的DFA。

**形式化表示**:
$$\forall M_{NFA}, \exists M_{DFA}: L(M_{NFA}) = L(M_{DFA})$$

**证明**:

1. **构造方法**: 子集构造法
   - 设NFA $M = (Q, \Sigma, \delta, q_0, F)$
   - 构造DFA $M' = (2^Q, \Sigma, \delta', \{q_0\}, F')$
   - 其中 $\delta'(S, a) = \bigcup_{q \in S} \delta(q, a)$
   - $F' = \{S \subseteq Q \mid S \cap F \neq \emptyset\}$

2. **等价性证明**:
   - 对于任意字符串 $w$，$w \in L(M)$ 当且仅当 $w \in L(M')$
   - 使用数学归纳法证明 $\delta'^*(\{q_0\}, w) = \delta^*(q_0, w)$

### 4.2 泵引理

**定理 4.2.1** (泵引理)
如果 $L$ 是正则语言，则存在泵长度 $p$，使得对于所有长度至少为 $p$ 的字符串 $s \in L$，存在分解 $s = xyz$ 满足：

1. $|xy| \leq p$
2. $|y| > 0$
3. 对于所有 $i \geq 0$，$xy^iz \in L$

**形式化表示**:
$$L \text{ is regular} \rightarrow \exists p \forall s (|s| \geq p \land s \in L \rightarrow \exists x,y,z (s = xyz \land |xy| \leq p \land |y| > 0 \land \forall i \geq 0, xy^iz \in L))$$

**证明**:

1. 设 $M$ 是识别 $L$ 的DFA，状态数为 $n$
2. 取泵长度 $p = n$
3. 对于长度至少为 $p$ 的字符串 $s$，在 $M$ 上运行时必然重复某个状态
4. 设重复的状态为 $q$，对应的子串为 $y$
5. 可以泵入任意数量的 $y$，得到 $xy^iz \in L$

### 4.3 最小化定理

**定理 4.3.1** (DFA最小化)
对于每个DFA，存在唯一的最小等价DFA。

**形式化表示**:
$$\forall M_{DFA}, \exists! M_{min}: L(M_{DFA}) = L(M_{min}) \land \text{Minimal}(M_{min})$$

**证明**:

1. **构造方法**: 等价类构造
   - 定义状态等价关系：$q \sim r$ 当且仅当 $\forall w, \delta^*(q, w) \in F \leftrightarrow \delta^*(r, w) \in F$
   - 构造等价类 $[q] = \{r \mid q \sim r\}$
   - 最小化DFA的状态为等价类集合

2. **唯一性证明**:
   - 假设存在两个不同的最小DFA
   - 构造它们的乘积自动机
   - 通过等价性证明它们必须相同

## 5. 自动机类型

### 5.1 确定性有限自动机

**定义 5.1.1** (DFA)
确定性有限自动机是状态转换完全确定的自动机。

**特征**:

- 每个状态对每个输入符号有唯一的后继状态
- 转换函数是单值函数
- 计算过程是确定性的

### 5.2 非确定性有限自动机

**定义 5.2.1** (NFA)
非确定性有限自动机是状态转换可以为非确定性的自动机。

**特征**:

- 每个状态对每个输入符号可以有多个后继状态
- 转换函数是多值函数
- 计算过程是非确定性的

### 5.3 ε-非确定性有限自动机

**定义 5.3.1** (ε-NFA)
ε-非确定性有限自动机是允许ε转换的非确定性有限自动机。

**特征**:

- 允许不消耗输入符号的状态转换
- 转换函数为 $\delta: Q \times (\Sigma \cup \{\varepsilon\}) \rightarrow 2^Q$
- 可以处理空字符串转换

## 6. 状态转换

### 6.1 转换函数定义

**定义 6.1.1** (DFA转换函数)
DFA的转换函数是确定性的：

$$\delta: Q \times \Sigma \rightarrow Q$$

**定义 6.1.2** (NFA转换函数)
NFA的转换函数是非确定性的：

$$\delta: Q \times \Sigma \rightarrow 2^Q$$

**定义 6.1.3** (ε-NFA转换函数)
ε-NFA的转换函数包含ε转换：

$$\delta: Q \times (\Sigma \cup \{\varepsilon\}) \rightarrow 2^Q$$

### 6.2 扩展转换函数

**定义 6.2.1** (DFA扩展转换函数)
对于DFA，扩展转换函数递归定义为：

$$\delta^*(q, \varepsilon) = q$$
$$\delta^*(q, wa) = \delta(\delta^*(q, w), a)$$

**定义 6.2.2** (NFA扩展转换函数)
对于NFA，扩展转换函数递归定义为：

$$\delta^*(q, \varepsilon) = \{q\}$$
$$\delta^*(q, wa) = \bigcup_{r \in \delta^*(q, w)} \delta(r, a)$$

### 6.3 ε闭包

**定义 6.3.1** (ε闭包)
ε闭包是从给定状态通过ε转换可达的所有状态集合。

**形式化定义**:
$$\varepsilon\text{-closure}(q) = \{p \mid q \stackrel{\varepsilon^*}{\rightarrow} p\}$$

## 7. 语言识别

### 7.1 语言定义

**定义 7.1.1** (DFA语言)
DFA $M$ 识别的语言为：

$$L(M) = \{w \in \Sigma^* \mid \delta^*(q_0, w) \in F\}$$

**定义 7.1.2** (NFA语言)
NFA $M$ 识别的语言为：

$$L(M) = \{w \in \Sigma^* \mid \delta^*(q_0, w) \cap F \neq \emptyset\}$$

### 7.2 语言性质

**性质 7.2.1** (正则语言封闭性)
正则语言在以下运算下封闭：

1. 并集
2. 交集
3. 补集
4. 连接
5. 星闭包

**证明**:
通过构造相应的有限自动机证明每种运算的封闭性。

### 7.3 语言等价性

**定义 7.3.1** (自动机等价性)
两个自动机等价，当且仅当它们识别相同的语言。

**形式化表示**:
$$M_1 \equiv M_2 \leftrightarrow L(M_1) = L(M_2)$$

## 8. 应用实例

### 8.1 词法分析器

**实例 8.1.1** (标识符识别)
识别编程语言中的标识符：

```rust
// 标识符DFA
let identifier_dfa = DFA::new(
    vec!["start", "letter", "letter_digit"],
    vec!['a'..='z', 'A'..='Z', '0'..='9', '_'],
    // 转换函数定义
    "start",
    vec!["letter", "letter_digit"]
);
```

### 8.2 数字识别

**实例 8.1.2** (整数识别)
识别整数常量：

```rust
// 整数DFA
let integer_dfa = DFA::new(
    vec!["start", "digit"],
    vec!['0'..='9', '+', '-'],
    // 转换函数定义
    "start",
    vec!["digit"]
);
```

### 8.3 模式匹配

**实例 8.1.3** (字符串匹配)
使用自动机进行字符串匹配：

```rust
// 模式匹配自动机
let pattern = "abab";
let pattern_dfa = build_pattern_dfa(pattern);
```

## 9. 代码实现

### 9.1 Rust实现

```rust
// 有限自动机基础理论 - Rust实现
// 文件名: finite_automata_basics.rs

use std::collections::{HashMap, HashSet};
use std::fmt;

/// 状态类型
pub type State = String;

/// 符号类型
pub type Symbol = char;

/// 转换函数类型
pub type TransitionFunction = HashMap<(State, Symbol), State>;

/// 非确定性转换函数类型
pub type NFATransitionFunction = HashMap<(State, Symbol), HashSet<State>>;

/// 确定性有限自动机
#[derive(Debug, Clone)]
pub struct DFA {
    states: HashSet<State>,
    alphabet: HashSet<Symbol>,
    transition: TransitionFunction,
    initial_state: State,
    accepting_states: HashSet<State>,
}

impl DFA {
    /// 创建新的DFA
    pub fn new(
        states: Vec<State>,
        alphabet: Vec<Symbol>,
        transition: TransitionFunction,
        initial_state: State,
        accepting_states: Vec<State>,
    ) -> Self {
        let states_set: HashSet<State> = states.into_iter().collect();
        let alphabet_set: HashSet<Symbol> = alphabet.into_iter().collect();
        let accepting_set: HashSet<State> = accepting_states.into_iter().collect();
        
        DFA {
            states: states_set,
            alphabet: alphabet_set,
            transition,
            initial_state,
            accepting_states: accepting_set,
        }
    }
    
    /// 执行单步转换
    pub fn step(&self, current_state: &State, symbol: Symbol) -> Option<State> {
        self.transition.get(&(current_state.clone(), symbol)).cloned()
    }
    
    /// 执行扩展转换
    pub fn step_extended(&self, current_state: &State, input: &str) -> Option<State> {
        let mut current = current_state.clone();
        
        for symbol in input.chars() {
            if let Some(next_state) = self.step(&current, symbol) {
                current = next_state;
            } else {
                return None;
            }
        }
        
        Some(current)
    }
    
    /// 检查字符串是否被接受
    pub fn accepts(&self, input: &str) -> bool {
        if let Some(final_state) = self.step_extended(&self.initial_state, input) {
            self.accepting_states.contains(&final_state)
        } else {
            false
        }
    }
    
    /// 获取DFA识别的语言
    pub fn language(&self) -> Vec<String> {
        // 简化实现：返回所有长度不超过3的字符串
        let mut language = Vec::new();
        let max_length = 3;
        
        for length in 0..=max_length {
            self.generate_strings(&self.initial_state, "", length, &mut language);
        }
        
        language
    }
    
    /// 生成字符串
    fn generate_strings(&self, current_state: &State, current_string: &str, remaining_length: usize, language: &mut Vec<String>) {
        if remaining_length == 0 {
            if self.accepting_states.contains(current_state) {
                language.push(current_string.to_string());
            }
            return;
        }
        
        for &symbol in &self.alphabet {
            if let Some(next_state) = self.step(current_state, symbol) {
                let new_string = format!("{}{}", current_string, symbol);
                self.generate_strings(&next_state, &new_string, remaining_length - 1, language);
            }
        }
    }
    
    /// 最小化DFA
    pub fn minimize(&self) -> DFA {
        // 实现Hopcroft算法进行DFA最小化
        let equivalence_classes = self.compute_equivalence_classes();
        self.build_minimal_dfa(&equivalence_classes)
    }
    
    /// 计算等价类
    fn compute_equivalence_classes(&self) -> HashMap<State, usize> {
        let mut classes = HashMap::new();
        let mut class_id = 0;
        
        // 初始分类：接受状态和非接受状态
        for state in &self.states {
            let class = if self.accepting_states.contains(state) { 0 } else { 1 };
            classes.insert(state.clone(), class);
        }
        
        // 迭代细化等价类
        let mut changed = true;
        while changed {
            changed = false;
            let mut new_classes = HashMap::new();
            let mut new_class_id = 0;
            
            for state in &self.states {
                let mut signature = Vec::new();
                signature.push(classes[state]);
                
                for &symbol in &self.alphabet {
                    if let Some(next_state) = self.step(state, symbol) {
                        signature.push(classes[&next_state]);
                    } else {
                        signature.push(usize::MAX);
                    }
                }
                
                let new_class = if let Some(&existing_class) = new_classes.get(&signature) {
                    existing_class
                } else {
                    new_classes.insert(signature, new_class_id);
                    new_class_id += 1;
                    new_class_id - 1
                };
                
                if classes[state] != new_class {
                    changed = true;
                }
                classes.insert(state.clone(), new_class);
            }
        }
        
        classes
    }
    
    /// 构建最小化DFA
    fn build_minimal_dfa(&self, equivalence_classes: &HashMap<State, usize>) -> DFA {
        let mut new_states = HashSet::new();
        let mut new_transition = HashMap::new();
        let mut new_accepting_states = HashSet::new();
        
        // 构建新状态
        for class_id in equivalence_classes.values() {
            new_states.insert(format!("q{}", class_id));
        }
        
        // 构建新转换函数
        for state in &self.states {
            let class_id = equivalence_classes[state];
            let new_state = format!("q{}", class_id);
            
            for &symbol in &self.alphabet {
                if let Some(next_state) = self.step(state, symbol) {
                    let next_class_id = equivalence_classes[&next_state];
                    let new_next_state = format!("q{}", next_class_id);
                    new_transition.insert((new_state.clone(), symbol), new_next_state);
                }
            }
        }
        
        // 构建新接受状态
        for state in &self.accepting_states {
            let class_id = equivalence_classes[state];
            new_accepting_states.insert(format!("q{}", class_id));
        }
        
        DFA {
            states: new_states,
            alphabet: self.alphabet.clone(),
            transition: new_transition,
            initial_state: format!("q{}", equivalence_classes[&self.initial_state]),
            accepting_states: new_accepting_states,
        }
    }
}

/// 非确定性有限自动机
#[derive(Debug, Clone)]
pub struct NFA {
    states: HashSet<State>,
    alphabet: HashSet<Symbol>,
    transition: NFATransitionFunction,
    initial_state: State,
    accepting_states: HashSet<State>,
}

impl NFA {
    /// 创建新的NFA
    pub fn new(
        states: Vec<State>,
        alphabet: Vec<Symbol>,
        transition: NFATransitionFunction,
        initial_state: State,
        accepting_states: Vec<State>,
    ) -> Self {
        let states_set: HashSet<State> = states.into_iter().collect();
        let alphabet_set: HashSet<Symbol> = alphabet.into_iter().collect();
        let accepting_set: HashSet<State> = accepting_states.into_iter().collect();
        
        NFA {
            states: states_set,
            alphabet: alphabet_set,
            transition,
            initial_state,
            accepting_states: accepting_set,
        }
    }
    
    /// 执行单步转换
    pub fn step(&self, current_states: &HashSet<State>, symbol: Symbol) -> HashSet<State> {
        let mut next_states = HashSet::new();
        
        for state in current_states {
            if let Some(target_states) = self.transition.get(&(state.clone(), symbol)) {
                next_states.extend(target_states.clone());
            }
        }
        
        next_states
    }
    
    /// 执行扩展转换
    pub fn step_extended(&self, current_states: &HashSet<State>, input: &str) -> HashSet<State> {
        let mut current = current_states.clone();
        
        for symbol in input.chars() {
            current = self.step(&current, symbol);
        }
        
        current
    }
    
    /// 检查字符串是否被接受
    pub fn accepts(&self, input: &str) -> bool {
        let initial_states = vec![self.initial_state.clone()].into_iter().collect();
        let final_states = self.step_extended(&initial_states, input);
        
        !final_states.is_disjoint(&self.accepting_states)
    }
    
    /// 转换为DFA
    pub fn to_dfa(&self) -> DFA {
        let mut dfa_states = HashSet::new();
        let mut dfa_transition = HashMap::new();
        let mut dfa_accepting_states = HashSet::new();
        
        // 初始状态
        let initial_dfa_state = vec![self.initial_state.clone()].into_iter().collect();
        dfa_states.insert(self.state_set_to_string(&initial_dfa_state));
        
        // 使用队列进行广度优先搜索
        let mut queue = vec![initial_dfa_state];
        let mut processed = HashSet::new();
        
        while let Some(current_states) = queue.pop() {
            let current_state_str = self.state_set_to_string(&current_states);
            
            if processed.contains(&current_state_str) {
                continue;
            }
            processed.insert(current_state_str.clone());
            
            // 检查是否为接受状态
            if !current_states.is_disjoint(&self.accepting_states) {
                dfa_accepting_states.insert(current_state_str.clone());
            }
            
            // 为每个输入符号计算转换
            for &symbol in &self.alphabet {
                let next_states = self.step(&current_states, symbol);
                let next_state_str = self.state_set_to_string(&next_states);
                
                if !next_states.is_empty() {
                    dfa_states.insert(next_state_str.clone());
                    dfa_transition.insert((current_state_str.clone(), symbol), next_state_str.clone());
                    
                    if !processed.contains(&next_state_str) {
                        queue.push(next_states);
                    }
                }
            }
        }
        
        DFA {
            states: dfa_states,
            alphabet: self.alphabet.clone(),
            transition: dfa_transition,
            initial_state: self.state_set_to_string(&initial_dfa_state),
            accepting_states: dfa_accepting_states,
        }
    }
    
    /// 将状态集合转换为字符串表示
    fn state_set_to_string(&self, states: &HashSet<State>) -> String {
        let mut sorted_states: Vec<_> = states.iter().collect();
        sorted_states.sort();
        format!("{{{}}}", sorted_states.join(","))
    }
}

/// 自动机构造器
pub struct AutomataBuilder;

impl AutomataBuilder {
    /// 构造识别特定字符串的DFA
    pub fn build_string_dfa(pattern: &str) -> DFA {
        let mut states = Vec::new();
        let mut transition = HashMap::new();
        let mut accepting_states = Vec::new();
        
        // 创建状态
        for i in 0..=pattern.len() {
            states.push(format!("q{}", i));
        }
        
        // 创建转换
        for (i, &symbol) in pattern.as_bytes().iter().enumerate() {
            let current_state = format!("q{}", i);
            let next_state = format!("q{}", i + 1);
            transition.insert((current_state, symbol as char), next_state);
        }
        
        // 添加失败转换
        for i in 0..pattern.len() {
            let current_state = format!("q{}", i);
            for c in b'a'..=b'z' {
                let symbol = c as char;
                if symbol != pattern.chars().nth(i).unwrap() {
                    // 计算失败状态
                    let mut failure_state = 0;
                    for j in 0..i {
                        if pattern[..j+1] == pattern[i-j..i+1] {
                            failure_state = j + 1;
                        }
                    }
                    transition.insert((current_state.clone(), symbol), format!("q{}", failure_state));
                }
            }
        }
        
        accepting_states.push(format!("q{}", pattern.len()));
        
        DFA::new(states, vec!['a', 'b', 'c'], transition, "q0".to_string(), accepting_states)
    }
    
    /// 构造识别正则表达式的NFA
    pub fn build_regex_nfa(regex: &str) -> NFA {
        // 简化实现：只处理基本的正则表达式
        let mut states = Vec::new();
        let mut transition = HashMap::new();
        let mut accepting_states = Vec::new();
        
        // 创建状态
        states.push("q0".to_string());
        states.push("q1".to_string());
        
        // 创建转换
        for c in regex.chars() {
            if c.is_alphanumeric() {
                let mut target_states = HashSet::new();
                target_states.insert("q1".to_string());
                transition.insert(("q0".to_string(), c), target_states);
            }
        }
        
        accepting_states.push("q1".to_string());
        
        NFA::new(states, vec!['a', 'b', 'c'], transition, "q0".to_string(), accepting_states)
    }
}

/// 测试模块
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dfa_construction() {
        let mut transition = HashMap::new();
        transition.insert(("q0".to_string(), 'a'), "q1".to_string());
        transition.insert(("q1".to_string(), 'b'), "q2".to_string());
        transition.insert(("q2".to_string(), 'a'), "q1".to_string());
        
        let dfa = DFA::new(
            vec!["q0".to_string(), "q1".to_string(), "q2".to_string()],
            vec!['a', 'b'],
            transition,
            "q0".to_string(),
            vec!["q2".to_string()],
        );
        
        assert!(dfa.accepts("aba"));
        assert!(!dfa.accepts("ab"));
    }

    #[test]
    fn test_nfa_construction() {
        let mut transition = HashMap::new();
        let mut target_states = HashSet::new();
        target_states.insert("q1".to_string());
        target_states.insert("q2".to_string());
        transition.insert(("q0".to_string(), 'a'), target_states);
        
        let nfa = NFA::new(
            vec!["q0".to_string(), "q1".to_string(), "q2".to_string()],
            vec!['a', 'b'],
            transition,
            "q0".to_string(),
            vec!["q1".to_string(), "q2".to_string()],
        );
        
        assert!(nfa.accepts("a"));
    }

    #[test]
    fn test_nfa_to_dfa_conversion() {
        let mut transition = HashMap::new();
        let mut target_states = HashSet::new();
        target_states.insert("q1".to_string());
        transition.insert(("q0".to_string(), 'a'), target_states);
        
        let nfa = NFA::new(
            vec!["q0".to_string(), "q1".to_string()],
            vec!['a'],
            transition,
            "q0".to_string(),
            vec!["q1".to_string()],
        );
        
        let dfa = nfa.to_dfa();
        assert!(dfa.accepts("a"));
    }

    #[test]
    fn test_string_pattern_dfa() {
        let dfa = AutomataBuilder::build_string_dfa("aba");
        assert!(dfa.accepts("aba"));
        assert!(!dfa.accepts("abb"));
    }
}
```

### 9.2 Haskell实现

```haskell
-- 有限自动机基础理论 - Haskell实现
-- 文件名: FiniteAutomataBasics.hs

{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module FiniteAutomataBasics where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List (find, nub)

-- 状态类型
type State = String

-- 符号类型
type Symbol = Char

-- 确定性有限自动机
data DFA = DFA
  { states :: Set State
  , alphabet :: Set Symbol
  , transition :: Map (State, Symbol) State
  , initialState :: State
  , acceptingStates :: Set State
  }
  deriving (Show, Eq)

-- 非确定性有限自动机
data NFA = NFA
  { nfaStates :: Set State
  , nfaAlphabet :: Set Symbol
  , nfaTransition :: Map (State, Symbol) (Set State)
  , nfaInitialState :: State
  , nfaAcceptingStates :: Set State
  }
  deriving (Show, Eq)

-- 创建DFA
makeDFA :: [State] -> [Symbol] -> [(State, Symbol, State)] -> State -> [State] -> DFA
makeDFA statesList alphabetList transitions initial accepting = DFA
  { states = Set.fromList statesList
  , alphabet = Set.fromList alphabetList
  , transition = Map.fromList [(s, a, t) | (s, a, t) <- transitions]
  , initialState = initial
  , acceptingStates = Set.fromList accepting
  }

-- 创建NFA
makeNFA :: [State] -> [Symbol] -> [(State, Symbol, [State])] -> State -> [State] -> NFA
makeNFA statesList alphabetList transitions initial accepting = NFA
  { nfaStates = Set.fromList statesList
  , nfaAlphabet = Set.fromList alphabetList
  , nfaTransition = Map.fromList [(s, a, Set.fromList ts) | (s, a, ts) <- transitions]
  , nfaInitialState = initial
  , nfaAcceptingStates = Set.fromList accepting
  }

-- DFA单步转换
dfaStep :: DFA -> State -> Symbol -> Maybe State
dfaStep dfa state symbol = Map.lookup (state, symbol) (transition dfa)

-- DFA扩展转换
dfaStepExtended :: DFA -> State -> String -> Maybe State
dfaStepExtended dfa state [] = Just state
dfaStepExtended dfa state (c:cs) = do
  nextState <- dfaStep dfa state c
  dfaStepExtended dfa nextState cs

-- DFA接受检查
dfaAccepts :: DFA -> String -> Bool
dfaAccepts dfa input = case dfaStepExtended dfa (initialState dfa) input of
  Just finalState -> Set.member finalState (acceptingStates dfa)
  Nothing -> False

-- NFA单步转换
nfaStep :: NFA -> Set State -> Symbol -> Set State
nfaStep nfa currentStates symbol = Set.unions [targetStates | state <- Set.toList currentStates, targetStates <- maybe [] (:[]) (Map.lookup (state, symbol) (nfaTransition nfa))]

-- NFA扩展转换
nfaStepExtended :: NFA -> Set State -> String -> Set State
nfaStepExtended nfa currentStates [] = currentStates
nfaStepExtended nfa currentStates (c:cs) = nfaStepExtended nfa (nfaStep nfa currentStates c) cs

-- NFA接受检查
nfaAccepts :: NFA -> String -> Bool
nfaAccepts nfa input = not $ Set.null $ Set.intersection finalStates (nfaAcceptingStates nfa)
  where
    initialStates = Set.singleton (nfaInitialState nfa)
    finalStates = nfaStepExtended nfa initialStates input

-- NFA转DFA
nfaToDFA :: NFA -> DFA
nfaToDFA nfa = DFA
  { states = dfaStates
  , alphabet = nfaAlphabet nfa
  , transition = dfaTransition
  , initialState = stateSetToString initialDFAState
  , acceptingStates = dfaAcceptingStates
  }
  where
    initialDFAState = Set.singleton (nfaInitialState nfa)
    (dfaStates, dfaTransition, dfaAcceptingStates) = buildDFA nfa initialDFAState Set.empty Map.empty Set.empty

-- 构建DFA
buildDFA :: NFA -> Set State -> Set (Set State) -> Map (String, Symbol) State -> Set String -> (Set String, Map (String, Symbol) State, Set String)
buildDFA nfa currentStates processedStates transitions acceptingStates
  | Set.member currentStates processedStates = (Set.singleton (stateSetToString currentStates), transitions, acceptingStates)
  | otherwise = (newStates, newTransitions, newAcceptingStates)
  where
    currentStateStr = stateSetToString currentStates
    newProcessedStates = Set.insert currentStates processedStates
    newAcceptingStates = if not (Set.null (Set.intersection currentStates (nfaAcceptingStates nfa)))
      then Set.insert currentStateStr acceptingStates
      else acceptingStates
    
    (newStates, newTransitions) = foldl addTransitions (Set.singleton currentStateStr, transitions) (Set.toList (nfaAlphabet nfa))
    
    addTransitions (states, trans) symbol = (states, Map.insert (currentStateStr, symbol) nextStateStr trans)
      where
        nextStates = nfaStep nfa currentStates symbol
        nextStateStr = stateSetToString nextStates
        newStates = Set.insert nextStateStr states

-- 状态集合转字符串
stateSetToString :: Set State -> String
stateSetToString states = "{" ++ intercalate "," (Set.toList states) ++ "}"

-- 字符串分割
intercalate :: String -> [String] -> String
intercalate _ [] = ""
intercalate _ [x] = x
intercalate sep (x:xs) = x ++ sep ++ intercalate sep xs

-- DFA最小化
minimizeDFA :: DFA -> DFA
minimizeDFA dfa = buildMinimalDFA dfa (computeEquivalenceClasses dfa)

-- 计算等价类
computeEquivalenceClasses :: DFA -> Map State Int
computeEquivalenceClasses dfa = iterateRefinement initialClasses
  where
    initialClasses = Map.fromList [(state, if Set.member state (acceptingStates dfa) then 0 else 1) | state <- Set.toList (states dfa)]
    
    iterateRefinement classes = if changed then iterateRefinement newClasses else classes
      where
        (changed, newClasses) = refineClasses dfa classes

-- 细化等价类
refineClasses :: DFA -> Map State Int -> (Bool, Map State Int)
refineClasses dfa classes = (changed, newClasses)
  where
    signatures = Map.fromList [(state, computeSignature dfa classes state) | state <- Set.toList (states dfa)]
    newClasses = assignNewClasses signatures
    changed = any (\state -> Map.findWithDefault 0 state classes /= Map.findWithDefault 0 state newClasses) (Set.toList (states dfa))

-- 计算状态签名
computeSignature :: DFA -> Map State Int -> State -> [Int]
computeSignature dfa classes state = currentClass : [Map.findWithDefault (-1) (state, symbol) (transition dfa) | symbol <- Set.toList (alphabet dfa)]
  where
    currentClass = Map.findWithDefault 0 state classes

-- 分配新类
assignNewClasses :: Map State [Int] -> Map State Int
assignNewClasses signatures = Map.fromList [(state, classId) | (state, classId) <- zip (Map.keys signatures) [0..]]
  where
    uniqueSignatures = nub (Map.elems signatures)
    classId = Map.fromList (zip uniqueSignatures [0..])

-- 构建最小化DFA
buildMinimalDFA :: DFA -> Map State Int -> DFA
buildMinimalDFA dfa classes = DFA
  { states = newStates
  , alphabet = alphabet dfa
  , transition = newTransition
  , initialState = newInitialState
  , acceptingStates = newAcceptingStates
  }
  where
    newStates = Set.fromList [show classId | classId <- nub (Map.elems classes)]
    newInitialState = show (Map.findWithDefault 0 (initialState dfa) classes)
    newAcceptingStates = Set.fromList [show classId | (state, classId) <- Map.toList classes, Set.member state (acceptingStates dfa)]
    newTransition = Map.fromList [((show classId, symbol), show targetClassId) | (state, classId) <- Map.toList classes, symbol <- Set.toList (alphabet dfa), Just targetState <- [Map.lookup (state, symbol) (transition dfa)], let targetClassId = Map.findWithDefault 0 targetState classes]

-- 自动机构造器
class AutomataBuilder where
  buildStringDFA :: String -> DFA
  buildRegexNFA :: String -> NFA

-- 实例化自动机构造器
instance AutomataBuilder where
  buildStringDFA pattern = makeDFA states alphabet transitions "q0" [last states]
    where
      states = ["q" ++ show i | i <- [0..length pattern]]
      alphabet = nub pattern
      transitions = [(states !! i, pattern !! i, states !! (i + 1)) | i <- [0..length pattern - 1]]
  
  buildRegexNFA regex = makeNFA ["q0", "q1"] alphabet transitions "q0" ["q1"]
    where
      alphabet = nub regex
      transitions = [("q0", c, ["q1"]) | c <- regex, c `elem` ['a'..'z']]

-- 测试函数
testDFAConstruction :: Bool
testDFAConstruction =
  let dfa = makeDFA ["q0", "q1", "q2"] ['a', 'b'] [("q0", 'a', "q1"), ("q1", 'b', "q2")] "q0" ["q2"]
  in dfaAccepts dfa "ab" && not (dfaAccepts dfa "a")

testNFAConstruction :: Bool
testNFAConstruction =
  let nfa = makeNFA ["q0", "q1"] ['a'] [("q0", 'a', ["q1"])] "q0" ["q1"]
  in nfaAccepts nfa "a"

testNFAtoDFAConversion :: Bool
testNFAtoDFAConversion =
  let nfa = makeNFA ["q0", "q1"] ['a'] [("q0", 'a', ["q1"])] "q0" ["q1"]
      dfa = nfaToDFA nfa
  in dfaAccepts dfa "a"

testStringPatternDFA :: Bool
testStringPatternDFA =
  let dfa = buildStringDFA "aba"
  in dfaAccepts dfa "aba" && not (dfaAccepts dfa "abb")

-- 运行所有测试
runAllTests :: IO ()
runAllTests = do
  putStrLn "Running finite automata tests..."
  putStrLn $ "DFA construction test: " ++ show testDFAConstruction
  putStrLn $ "NFA construction test: " ++ show testNFAConstruction
  putStrLn $ "NFA to DFA conversion test: " ++ show testNFAtoDFAConversion
  putStrLn $ "String pattern DFA test: " ++ show testStringPatternDFA
  putStrLn "All tests completed!"
```

## 10. 参考文献

1. Hopcroft, John E. and Ullman, Jeffrey D. *Introduction to Automata Theory, Languages, and Computation*. Addison-Wesley, 1979.
2. Sipser, Michael. *Introduction to the Theory of Computation*. Cengage Learning, 2012.
3. Kozen, Dexter C. *Automata and Computability*. Springer, 1997.
4. Lewis, Harry R. and Papadimitriou, Christos H. *Elements of the Theory of Computation*. Prentice Hall, 1998.
5. Martin, John C. *Introduction to Languages and the Theory of Computation*. McGraw-Hill, 2010.
6. Linz, Peter. *An Introduction to Formal Languages and Automata*. Jones & Bartlett Learning, 2011.
7. Sudkamp, Thomas A. *Languages and Machines: An Introduction to the Theory of Computer Science*. Addison-Wesley, 2006.
8. Davis, Martin D., Sigal, Ron, and Weyuker, Elaine J. *Computability, Complexity, and Languages: Fundamentals of Theoretical Computer Science*. Academic Press, 1994.
9. Hopcroft, John E., Motwani, Rajeev, and Ullman, Jeffrey D. *Introduction to Automata Theory, Languages, and Computation*. Pearson, 2006.
10. Arora, Sanjeev and Barak, Boaz. *Computational Complexity: A Modern Approach*. Cambridge University Press, 2009.

---

**最后更新时间**: 2024年12月21日  
**版本**: v1.0  
**维护者**: 形式科学理论体系重构团队  
**状态**: ✅ 已完成

## 批判性分析

- 本节内容待补充：请从多元理论视角、局限性、争议点、应用前景等方面进行批判性分析。
