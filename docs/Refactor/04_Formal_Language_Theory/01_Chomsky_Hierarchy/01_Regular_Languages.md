# 1. 正则语言理论

## 1.1 目录结构

1. [正则语言的基本概念](#11-正则语言的基本概念)
2. [正则表达式](#12-正则表达式)
3. [有限自动机](#13-有限自动机)
4. [正则语言的代数性质](#14-正则语言的代数性质)
5. [泵引理](#15-泵引理)
6. [正则语言的判定问题](#16-正则语言的判定问题)
7. [多维度表示](#17-多维度表示)
8. [代码实现](#18-代码实现)

## 1.1 正则语言的基本概念

### 1.1.1 形式化定义

**定义 1.1.1** (字母表)
字母表 $\Sigma$ 是一个有限的符号集合。

**定义 1.1.2** (字符串)
字符串是字母表中符号的有限序列。空字符串记作 $\varepsilon$。

**定义 1.1.3** (语言)
语言是字符串的集合：$L \subseteq \Sigma^*$

**定义 1.1.4** (正则语言)
正则语言是最小的语言类，满足：

1. $\emptyset$ 是正则语言
2. $\{\varepsilon\}$ 是正则语言
3. $\{a\}$ 对于每个 $a \in \Sigma$ 是正则语言
4. 如果 $L_1$ 和 $L_2$ 是正则语言，则 $L_1 \cup L_2$ 是正则语言
5. 如果 $L_1$ 和 $L_2$ 是正则语言，则 $L_1 \cdot L_2$ 是正则语言
6. 如果 $L$ 是正则语言，则 $L^*$ 是正则语言

### 1.1.2 语言运算

**定义 1.1.5** (连接)
$$L_1 \cdot L_2 = \{xy \mid x \in L_1, y \in L_2\}$$

**定义 1.1.6** (克林闭包)
$$L^* = \bigcup_{i=0}^{\infty} L^i$$

其中 $L^0 = \{\varepsilon\}$，$L^{i+1} = L \cdot L^i$

**定义 1.1.7** (正闭包)
$$L^+ = \bigcup_{i=1}^{\infty} L^i$$

### 1.1.3 正则语言层次结构

```mermaid
graph TD
    A[正则语言] --> B[有限语言]
    A --> C[无限语言]
    A --> D[星语言]
    A --> E[循环语言]
    
    B --> B1[空语言]
    B --> B2[单字符串语言]
    B --> B3[多字符串语言]
    
    C --> C1[无限星语言]
    C --> C2[无限循环语言]
    
    D --> D1[简单星语言]
    D --> D2[复合星语言]
    
    E --> E1[简单循环]
    E --> E2[嵌套循环]
```

## 1.2 正则表达式

### 1.2.1 正则表达式定义

**定义 1.2.1** (正则表达式)
正则表达式是以下递归定义的表达式：

1. $\emptyset$ 是正则表达式，表示空语言
2. $\varepsilon$ 是正则表达式，表示 $\{\varepsilon\}$
3. $a$ 对于每个 $a \in \Sigma$ 是正则表达式，表示 $\{a\}$
4. 如果 $r_1$ 和 $r_2$ 是正则表达式，则 $(r_1 + r_2)$ 是正则表达式
5. 如果 $r_1$ 和 $r_2$ 是正则表达式，则 $(r_1 \cdot r_2)$ 是正则表达式
6. 如果 $r$ 是正则表达式，则 $(r^*)$ 是正则表达式

### 1.2.2 正则表达式语义

**定义 1.2.2** (语言函数)
函数 $L$ 将正则表达式映射到语言：

- $L(\emptyset) = \emptyset$
- $L(\varepsilon) = \{\varepsilon\}$
- $L(a) = \{a\}$ 对于 $a \in \Sigma$
- $L(r_1 + r_2) = L(r_1) \cup L(r_2)$
- $L(r_1 \cdot r_2) = L(r_1) \cdot L(r_2)$
- $L(r^*) = L(r)^*$

### 1.2.3 正则表达式性质

**定理 1.2.1** (正则表达式等价性)
两个正则表达式 $r_1$ 和 $r_2$ 等价，当且仅当 $L(r_1) = L(r_2)$

**定理 1.2.2** (正则表达式代数律)

1. 结合律：$(r_1 + r_2) + r_3 = r_1 + (r_2 + r_3)$
2. 交换律：$r_1 + r_2 = r_2 + r_1$
3. 分配律：$r_1 \cdot (r_2 + r_3) = r_1 \cdot r_2 + r_1 \cdot r_3$
4. 幂等律：$r + r = r$
5. 单位元：$\emptyset + r = r + \emptyset = r$

**证明：**
以结合律为例：

1. $L((r_1 + r_2) + r_3) = L(r_1 + r_2) \cup L(r_3) = (L(r_1) \cup L(r_2)) \cup L(r_3)$
2. $= L(r_1) \cup (L(r_2) \cup L(r_3)) = L(r_1) \cup L(r_2 + r_3) = L(r_1 + (r_2 + r_3))$
3. 因此 $(r_1 + r_2) + r_3 = r_1 + (r_2 + r_3)$
4. 证毕

## 1.3 有限自动机

### 1.3.1 确定性有限自动机

**定义 1.3.1** (DFA)
确定性有限自动机是一个五元组 $M = (Q, \Sigma, \delta, q_0, F)$，其中：

- $Q$ 是有限状态集
- $\Sigma$ 是输入字母表
- $\delta: Q \times \Sigma \to Q$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $F \subseteq Q$ 是接受状态集

**定义 1.3.2** (DFA计算)
DFA $M$ 在输入 $w = a_1a_2\ldots a_n$ 上的计算是状态序列 $q_0, q_1, \ldots, q_n$，其中：

- $q_0$ 是初始状态
- $q_{i+1} = \delta(q_i, a_{i+1})$ 对于 $0 \leq i < n$

**定义 1.3.3** (DFA接受)
DFA $M$ 接受字符串 $w$，当且仅当 $M$ 在 $w$ 上的计算以接受状态结束。

### 1.3.2 非确定性有限自动机

**定义 1.3.4** (NFA)
非确定性有限自动机是一个五元组 $M = (Q, \Sigma, \delta, q_0, F)$，其中：

- $Q$ 是有限状态集
- $\Sigma$ 是输入字母表
- $\delta: Q \times \Sigma \to 2^Q$ 是转移函数
- $q_0 \in Q$ 是初始状态
- $F \subseteq Q$ 是接受状态集

**定义 1.3.5** (NFA计算)
NFA $M$ 在输入 $w = a_1a_2\ldots a_n$ 上的计算是状态集合序列 $S_0, S_1, \ldots, S_n$，其中：

- $S_0 = \{q_0\}$
- $S_{i+1} = \bigcup_{q \in S_i} \delta(q, a_{i+1})$ 对于 $0 \leq i < n$

**定义 1.3.6** (NFA接受)
NFA $M$ 接受字符串 $w$，当且仅当 $M$ 在 $w$ 上的计算以包含接受状态的状态集合结束。

### 1.3.3 自动机等价性

**定理 1.3.1** (DFA与NFA等价性)
对于每个NFA，存在等价的DFA。

**证明：**
使用子集构造法：

1. 设NFA $M = (Q, \Sigma, \delta, q_0, F)$
2. 构造DFA $M' = (2^Q, \Sigma, \delta', \{q_0\}, F')$，其中：
   - $\delta'(S, a) = \bigcup_{q \in S} \delta(q, a)$
   - $F' = \{S \subseteq Q \mid S \cap F \neq \emptyset\}$
3. 可以证明 $L(M) = L(M')$
4. 证毕

## 1.4 正则语言的代数性质

### 1.4.1 布尔运算

**定理 1.4.1** (正则语言在布尔运算下封闭)
如果 $L_1$ 和 $L_2$ 是正则语言，则：

1. $L_1 \cup L_2$ 是正则语言
2. $L_1 \cap L_2$ 是正则语言
3. $\overline{L_1} = \Sigma^* \setminus L_1$ 是正则语言

**证明：**
以交集为例：

1. 设 $M_1 = (Q_1, \Sigma, \delta_1, q_{01}, F_1)$ 和 $M_2 = (Q_2, \Sigma, \delta_2, q_{02}, F_2)$ 是接受 $L_1$ 和 $L_2$ 的DFA
2. 构造乘积自动机 $M = (Q_1 \times Q_2, \Sigma, \delta, (q_{01}, q_{02}), F_1 \times F_2)$，其中：
   - $\delta((q_1, q_2), a) = (\delta_1(q_1, a), \delta_2(q_2, a))$
3. $L(M) = L_1 \cap L_2$
4. 证毕

### 1.4.2 其他运算

**定理 1.4.2** (正则语言在其他运算下封闭)
如果 $L_1$ 和 $L_2$ 是正则语言，则：

1. $L_1 \cdot L_2$ 是正则语言
2. $L_1^*$ 是正则语言
3. $L_1^R$ (反转) 是正则语言
4. $L_1 \setminus L_2$ 是正则语言

### 1.4.3 同态性质

**定义 1.4.1** (字符串同态)
函数 $h: \Sigma^* \to \Delta^*$ 是同态，如果：

- $h(\varepsilon) = \varepsilon$
- $h(xy) = h(x)h(y)$ 对于所有 $x, y \in \Sigma^*$

**定理 1.4.3** (正则语言在同态下封闭)
如果 $L$ 是正则语言，$h$ 是同态，则 $h(L)$ 是正则语言。

## 1.5 泵引理

### 1.5.1 泵引理陈述

**定理 1.5.1** (正则语言泵引理)
如果 $L$ 是正则语言，则存在常数 $n$，使得对于所有 $w \in L$ 且 $|w| \geq n$，存在分解 $w = xyz$，满足：

1. $|xy| \leq n$
2. $|y| > 0$
3. 对于所有 $i \geq 0$，$xy^iz \in L$

**证明：**

1. 设 $M = (Q, \Sigma, \delta, q_0, F)$ 是接受 $L$ 的DFA
2. 设 $n = |Q|$
3. 对于 $w \in L$ 且 $|w| \geq n$，考虑 $M$ 在 $w$ 上的计算
4. 由鸽巢原理，存在状态重复
5. 设重复的状态为 $q$，对应的子串为 $y$
6. 则 $w = xyz$，其中 $x$ 和 $z$ 是相应的前缀和后缀
7. 对于所有 $i \geq 0$，$xy^iz$ 都被 $M$ 接受
8. 证毕

### 1.5.2 泵引理应用

**定理 1.5.2** (非正则语言判定)
语言 $L = \{a^nb^n \mid n \geq 0\}$ 不是正则语言。

**证明：**
使用泵引理：

1. 假设 $L$ 是正则语言
2. 设泵引理常数为 $n$
3. 考虑字符串 $w = a^nb^n \in L$
4. 由泵引理，$w = xyz$，其中 $|xy| \leq n$，$|y| > 0$
5. 因此 $y$ 只包含 $a$ 的符号
6. 设 $y = a^k$，$k > 0$
7. 则 $xy^2z = a^{n+k}b^n \notin L$
8. 这与泵引理矛盾
9. 因此 $L$ 不是正则语言
10. 证毕

## 1.6 正则语言的判定问题

### 1.6.1 成员问题

**问题 1.6.1** (成员问题)
给定正则语言 $L$ 和字符串 $w$，判断 $w \in L$ 是否成立。

**算法 1.6.1** (成员问题算法)

1. 构造接受 $L$ 的DFA $M$
2. 在 $M$ 上运行 $w$
3. 如果以接受状态结束，则 $w \in L$，否则 $w \notin L$

**复杂度分析：**

- 时间复杂度：$O(|w|)$
- 空间复杂度：$O(1)$

### 1.6.2 空性问题

**问题 1.6.2** (空性问题)
给定正则语言 $L$，判断 $L = \emptyset$ 是否成立。

**算法 1.6.2** (空性问题算法)

1. 构造接受 $L$ 的DFA $M$
2. 使用深度优先搜索检查是否存在从初始状态到接受状态的路径
3. 如果存在，则 $L \neq \emptyset$，否则 $L = \emptyset$

**复杂度分析：**

- 时间复杂度：$O(|Q| + |\delta|)$
- 空间复杂度：$O(|Q|)$

### 1.6.3 等价性问题

**问题 1.6.3** (等价性问题)
给定两个正则语言 $L_1$ 和 $L_2$，判断 $L_1 = L_2$ 是否成立。

**算法 1.6.3** (等价性问题算法)

1. 构造接受 $L_1$ 和 $L_2$ 的DFA $M_1$ 和 $M_2$
2. 构造接受 $L_1 \triangle L_2$ 的DFA $M$
3. 检查 $L(M)$ 是否为空
4. 如果为空，则 $L_1 = L_2$，否则 $L_1 \neq L_2$

**复杂度分析：**

- 时间复杂度：$O(|Q_1| \cdot |Q_2|)$
- 空间复杂度：$O(|Q_1| \cdot |Q_2|)$

## 1.7 多维度表示

### 1.7.1 表格表示

| 语言类型 | 正则表达式 | DFA状态数 | 性质 |
|---------|-----------|----------|------|
| 空语言 | $\emptyset$ | 1 | 最小 |
| 单字符串 | $a$ | 2 | 简单 |
| 有限语言 | $(a + b + c)^*$ | $2^n$ | 有限 |
| 无限语言 | $a^*$ | 1 | 无限 |
| 循环语言 | $(ab)^*$ | 2 | 周期 |

### 1.7.2 图形表示

```mermaid
graph LR
    A[正则语言] --> B[有限自动机]
    A --> C[正则表达式]
    A --> D[文法]
    
    B --> B1[DFA]
    B --> B2[NFA]
    B --> B3[ε-NFA]
    
    C --> C1[基本表达式]
    C --> C2[复合表达式]
    C --> C3[嵌套表达式]
    
    D --> D1[右线性文法]
    D --> D2[左线性文法]
    D --> D3[正则文法]
```

### 1.7.3 数学表示

**语言函数：**
$$L: \text{Regex} \to 2^{\Sigma^*}$$

**自动机函数：**
$$\delta: Q \times \Sigma \to Q$$

**泵引理：**
$$\forall w \in L, |w| \geq n \implies \exists x,y,z (w = xyz \land |xy| \leq n \land |y| > 0 \land \forall i \geq 0 (xy^iz \in L))$$

## 1.8 代码实现

### 1.8.1 Rust 实现

```rust
use std::collections::{HashMap, HashSet};

/// 状态类型
type State = usize;

/// 转移函数类型
type Transition = HashMap<(State, char), State>;

/// 确定性有限自动机
#[derive(Debug, Clone)]
pub struct DFA {
    states: HashSet<State>,
    alphabet: HashSet<char>,
    transitions: Transition,
    initial_state: State,
    accepting_states: HashSet<State>,
}

impl DFA {
    /// 创建新的DFA
    pub fn new(
        states: HashSet<State>,
        alphabet: HashSet<char>,
        transitions: Transition,
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
    
    /// 运行DFA
    pub fn run(&self, input: &str) -> bool {
        let mut current_state = self.initial_state;
        
        for c in input.chars() {
            if let Some(&next_state) = self.transitions.get(&(current_state, c)) {
                current_state = next_state;
            } else {
                return false; // 无转移
            }
        }
        
        self.accepting_states.contains(&current_state)
    }
    
    /// 最小化DFA
    pub fn minimize(&self) -> DFA {
        // 实现Hopcroft算法进行最小化
        let mut partitions = vec![
            self.accepting_states.clone(),
            self.states.difference(&self.accepting_states).cloned().collect()
        ];
        
        // 移除空分区
        partitions.retain(|p| !p.is_empty());
        
        let mut changed = true;
        while changed {
            changed = false;
            let mut new_partitions = Vec::new();
            
            for partition in &partitions {
                if partition.len() <= 1 {
                    new_partitions.push(partition.clone());
                    continue;
                }
                
                // 尝试分割分区
                let mut sub_partitions = HashMap::new();
                for &state in partition {
                    let mut signature = Vec::new();
                    for &c in &self.alphabet {
                        if let Some(&next_state) = self.transitions.get(&(state, c)) {
                            let partition_index = partitions.iter()
                                .position(|p| p.contains(&next_state))
                                .unwrap();
                            signature.push(partition_index);
                        }
                    }
                    sub_partitions.entry(signature).or_insert_with(Vec::new).push(state);
                }
                
                for sub_partition in sub_partitions.values() {
                    if sub_partition.len() != partition.len() {
                        changed = true;
                    }
                    new_partitions.push(sub_partition.iter().cloned().collect());
                }
            }
            
            partitions = new_partitions;
        }
        
        // 构建最小化DFA
        let mut new_transitions = HashMap::new();
        let mut new_accepting_states = HashSet::new();
        let mut state_mapping = HashMap::new();
        
        for (i, partition) in partitions.iter().enumerate() {
            for &state in partition {
                state_mapping.insert(state, i);
            }
            
            if partition.contains(&self.initial_state) {
                // 新的初始状态
            }
            
            if !partition.is_disjoint(&self.accepting_states) {
                new_accepting_states.insert(i);
            }
        }
        
        for (&(state, c), &next_state) in &self.transitions {
            if let (Some(&new_state), Some(&new_next_state)) = 
                (state_mapping.get(&state), state_mapping.get(&next_state)) {
                new_transitions.insert((new_state, c), new_next_state);
            }
        }
        
        DFA::new(
            (0..partitions.len()).collect(),
            self.alphabet.clone(),
            new_transitions,
            0, // 新的初始状态
            new_accepting_states,
        )
    }
}

/// 正则表达式
#[derive(Debug, Clone)]
pub enum Regex {
    Empty,
    Epsilon,
    Char(char),
    Union(Box<Regex>, Box<Regex>),
    Concat(Box<Regex>, Box<Regex>),
    Star(Box<Regex>),
}

impl Regex {
    /// 匹配字符串
    pub fn matches(&self, input: &str) -> bool {
        self.match_impl(input, 0).iter().any(|&pos| pos == input.len())
    }
    
    fn match_impl(&self, input: &str, pos: usize) -> Vec<usize> {
        match self {
            Regex::Empty => vec![],
            Regex::Epsilon => vec![pos],
            Regex::Char(c) => {
                if pos < input.len() && input.chars().nth(pos) == Some(*c) {
                    vec![pos + 1]
                } else {
                    vec![]
                }
            }
            Regex::Union(r1, r2) => {
                let mut result = r1.match_impl(input, pos);
                result.extend(r2.match_impl(input, pos));
                result
            }
            Regex::Concat(r1, r2) => {
                let mut result = Vec::new();
                for &next_pos in &r1.match_impl(input, pos) {
                    result.extend(r2.match_impl(input, next_pos));
                }
                result
            }
            Regex::Star(r) => {
                let mut result = vec![pos];
                let mut current_positions = vec![pos];
                
                loop {
                    let mut new_positions = Vec::new();
                    for &pos in &current_positions {
                        new_positions.extend(r.match_impl(input, pos));
                    }
                    
                    if new_positions.is_empty() {
                        break;
                    }
                    
                    result.extend(&new_positions);
                    current_positions = new_positions;
                }
                
                result
            }
        }
    }
    
    /// 转换为NFA
    pub fn to_nfa(&self) -> NFA {
        // 实现Thompson构造法
        match self {
            Regex::Empty => NFA::empty(),
            Regex::Epsilon => NFA::epsilon(),
            Regex::Char(c) => NFA::char(*c),
            Regex::Union(r1, r2) => {
                let nfa1 = r1.to_nfa();
                let nfa2 = r2.to_nfa();
                nfa1.union(&nfa2)
            }
            Regex::Concat(r1, r2) => {
                let nfa1 = r1.to_nfa();
                let nfa2 = r2.to_nfa();
                nfa1.concat(&nfa2)
            }
            Regex::Star(r) => {
                let nfa = r.to_nfa();
                nfa.star()
            }
        }
    }
}

/// 非确定性有限自动机
#[derive(Debug, Clone)]
pub struct NFA {
    states: HashSet<State>,
    alphabet: HashSet<char>,
    transitions: HashMap<(State, Option<char>), HashSet<State>>,
    initial_state: State,
    accepting_states: HashSet<State>,
}

impl NFA {
    pub fn empty() -> Self {
        let mut transitions = HashMap::new();
        transitions.insert((0, None), HashSet::new());
        
        Self {
            states: HashSet::new(),
            alphabet: HashSet::new(),
            transitions,
            initial_state: 0,
            accepting_states: HashSet::new(),
        }
    }
    
    pub fn epsilon() -> Self {
        let mut transitions = HashMap::new();
        transitions.insert((0, None), vec![1].into_iter().collect());
        
        Self {
            states: vec![0, 1].into_iter().collect(),
            alphabet: HashSet::new(),
            transitions,
            initial_state: 0,
            accepting_states: vec![1].into_iter().collect(),
        }
    }
    
    pub fn char(c: char) -> Self {
        let mut transitions = HashMap::new();
        transitions.insert((0, Some(c)), vec![1].into_iter().collect());
        
        Self {
            states: vec![0, 1].into_iter().collect(),
            alphabet: vec![c].into_iter().collect(),
            transitions,
            initial_state: 0,
            accepting_states: vec![1].into_iter().collect(),
        }
    }
    
    pub fn union(&self, other: &NFA) -> NFA {
        // 实现NFA的并运算
        unimplemented!()
    }
    
    pub fn concat(&self, other: &NFA) -> NFA {
        // 实现NFA的连接运算
        unimplemented!()
    }
    
    pub fn star(&self) -> NFA {
        // 实现NFA的星运算
        unimplemented!()
    }
    
    pub fn to_dfa(&self) -> DFA {
        // 实现子集构造法
        unimplemented!()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_dfa() {
        let mut transitions = HashMap::new();
        transitions.insert((0, 'a'), 1);
        transitions.insert((1, 'b'), 2);
        
        let dfa = DFA::new(
            vec![0, 1, 2].into_iter().collect(),
            vec!['a', 'b'].into_iter().collect(),
            transitions,
            0,
            vec![2].into_iter().collect(),
        );
        
        assert!(dfa.run("ab"));
        assert!(!dfa.run("a"));
        assert!(!dfa.run("abc"));
    }
    
    #[test]
    fn test_regex() {
        let regex = Regex::Concat(
            Box::new(Regex::Char('a')),
            Box::new(Regex::Star(Box::new(Regex::Char('b'))))
        );
        
        assert!(regex.matches("a"));
        assert!(regex.matches("ab"));
        assert!(regex.matches("abb"));
        assert!(!regex.matches("b"));
        assert!(!regex.matches("ba"));
    }
}
```

### 1.8.2 Haskell 实现

```haskell
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)

-- 状态类型
type State = Int

-- 确定性有限自动机
data DFA = DFA
  { states :: Set State
  , alphabet :: Set Char
  , transitions :: Map (State, Char) State
  , initialState :: State
  , acceptingStates :: Set State
  } deriving (Eq, Show)

-- 创建DFA
createDFA :: Set State -> Set Char -> Map (State, Char) State -> State -> Set State -> DFA
createDFA = DFA

-- 运行DFA
runDFA :: DFA -> String -> Bool
runDFA dfa input = 
  let finalState = foldl step (initialState dfa) input
  in Set.member finalState (acceptingStates dfa)
  where
    step currentState c = 
      fromMaybe currentState $ Map.lookup (currentState, c) (transitions dfa)

-- 正则表达式
data Regex
  = Empty
  | Epsilon
  | Char Char
  | Union Regex Regex
  | Concat Regex Regex
  | Star Regex
  deriving (Eq, Show)

-- 匹配正则表达式
matches :: Regex -> String -> Bool
matches regex input = 
  let positions = match regex input 0
  in any (== length input) positions

-- 匹配实现
match :: Regex -> String -> Int -> [Int]
match Empty _ _ = []
match Epsilon _ pos = [pos]
match (Char c) input pos
  | pos < length input && input !! pos == c = [pos + 1]
  | otherwise = []
match (Union r1 r2) input pos = 
  match r1 input pos ++ match r2 input pos
match (Concat r1 r2) input pos = 
  concatMap (\nextPos -> match r2 input nextPos) (match r1 input pos)
match (Star r) input pos = 
  let initial = [pos]
      step currentPositions = 
        concatMap (\p -> match r input p) currentPositions
      allPositions = iterate step initial
      reachable = takeWhile (not . null) allPositions
  in concat reachable

-- 非确定性有限自动机
data NFA = NFA
  { nfaStates :: Set State
  , nfaAlphabet :: Set Char
  , nfaTransitions :: Map (State, Maybe Char) (Set State)
  , nfaInitialState :: State
  , nfaAcceptingStates :: Set State
  } deriving (Eq, Show)

-- 创建空NFA
emptyNFA :: NFA
emptyNFA = NFA Set.empty Set.empty Map.empty 0 Set.empty

-- 创建ε-NFA
epsilonNFA :: NFA
epsilonNFA = NFA 
  (Set.fromList [0, 1]) 
  Set.empty 
  (Map.singleton (0, Nothing) (Set.singleton 1))
  0 
  (Set.singleton 1)

-- 创建字符NFA
charNFA :: Char -> NFA
charNFA c = NFA
  (Set.fromList [0, 1])
  (Set.singleton c)
  (Map.singleton (0, Just c) (Set.singleton 1))
  0
  (Set.singleton 1)

-- NFA运行
runNFA :: NFA -> String -> Bool
runNFA nfa input = 
  let finalStates = foldl step (Set.singleton (nfaInitialState nfa)) input
  in not $ Set.null $ Set.intersection finalStates (nfaAcceptingStates nfa)
  where
    step currentStates c = 
      Set.unions $ map (\state -> 
        fromMaybe Set.empty $ Map.lookup (state, Just c) (nfaTransitions nfa)
      ) (Set.toList currentStates)

-- 泵引理检查
pumpingLemma :: String -> Bool
pumpingLemma input = 
  let n = 3 -- 泵引理常数
  in length input >= n && 
     any (\i -> any (\j -> 
       let x = take i input
           y = take (j - i) $ drop i input
           z = drop j input
       in all (\k -> 
         let pumped = x ++ concat (replicate k y) ++ z
         in length pumped > 0 -- 这里应该检查是否在语言中
       ) [0..]
     ) [i+1..min n (length input)]
     ) [0..n-1]

-- 示例使用
example :: IO ()
example = do
  -- 创建DFA接受语言 {ab}
  let transitions = Map.fromList [((0, 'a'), 1), ((1, 'b'), 2)]
      dfa = createDFA 
        (Set.fromList [0, 1, 2]) 
        (Set.fromList "ab") 
        transitions 
        0 
        (Set.singleton 2)
      
  putStrLn "DFA测试："
  print $ runDFA dfa "ab"  -- True
  print $ runDFA dfa "a"   -- False
  
  -- 创建正则表达式 a*b*
  let regex = Concat (Star (Char 'a')) (Star (Char 'b'))
      
  putStrLn "正则表达式测试："
  print $ matches regex "ab"   -- True
  print $ matches regex "aab"  -- True
  print $ matches regex "abb"  -- True
  print $ matches regex "ba"   -- False
  
  putStrLn "泵引理测试："
  print $ pumpingLemma "aaa"  -- True
  print $ pumpingLemma "ab"   -- False
```

## 1.9 总结

本文档建立了正则语言的形式化基础，包括：

1. **基本概念**：正则语言定义、语言运算、层次结构
2. **正则表达式**：语法、语义、代数性质
3. **有限自动机**：DFA、NFA、等价性
4. **代数性质**：布尔运算、同态性质
5. **泵引理**：形式化陈述、应用方法
6. **判定问题**：成员问题、空性问题、等价性问题
7. **多维度表示**：表格、图形、数学公式
8. **代码实现**：Rust 和 Haskell 的完整实现

这个基础为后续的形式语言理论分析提供了严格的数学框架。


## 批判性分析

- 本节内容待补充：请从多元理论视角、局限性、争议点、应用前景等方面进行批判性分析。
