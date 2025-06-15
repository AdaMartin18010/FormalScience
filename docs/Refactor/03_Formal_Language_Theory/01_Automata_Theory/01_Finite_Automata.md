# 01. 有限自动机 (Finite Automata)

## 目录

1. [基本概念](#基本概念)
2. [确定性有限自动机](#确定性有限自动机)
3. [非确定性有限自动机](#非确定性有限自动机)
4. [正则语言](#正则语言)
5. [形式化表示](#形式化表示)
6. [证明系统](#证明系统)
7. [与其他学科的关联](#与其他学科的关联)

## 基本概念

### 1.1 有限自动机的定义

**定义 1.1.1 (有限自动机)**
有限自动机是一个五元组 M = (Q, Σ, δ, q₀, F)，其中：

- Q 是有限状态集合
- Σ 是有限输入字母表
- δ: Q × Σ → Q 是转移函数
- q₀ ∈ Q 是初始状态
- F ⊆ Q 是接受状态集合

### 1.2 状态转移

**定义 1.1.2 (状态转移)**
对于状态 q ∈ Q 和输入符号 a ∈ Σ，δ(q, a) 表示从状态 q 读入符号 a 后转移到的状态。

**扩展转移函数：**

```latex
δ̂: Q × Σ* → Q
```

递归定义：

1. δ̂(q, ε) = q
2. δ̂(q, wa) = δ(δ̂(q, w), a)

### 1.3 语言接受

**定义 1.1.3 (语言接受)**
自动机 M 接受的语言定义为：

```latex
L(M) = {w ∈ Σ* | δ̂(q₀, w) ∈ F}
```

## 确定性有限自动机

### 2.1 DFA的定义

**定义 2.1.1 (DFA)**
确定性有限自动机是满足以下条件的有限自动机：

- 转移函数 δ: Q × Σ → Q 是确定的
- 对于每个状态和输入符号，有且仅有一个后继状态

### 2.2 DFA的性质

**定理 2.1.1 (DFA的确定性)**:

```latex
∀q ∈ Q ∀a ∈ Σ ∃!q' ∈ Q (δ(q, a) = q')
```

**证明：**

1. 根据DFA定义，δ 是函数
2. 函数满足单值性
3. 因此对于任意 q 和 a，存在唯一的 q' 使得 δ(q, a) = q'

### 2.3 DFA示例

**示例 2.1.1 (识别偶数个1的DFA)**:

```latex
M = ({q₀, q₁}, {0, 1}, δ, q₀, {q₀})

转移函数：
δ(q₀, 0) = q₀
δ(q₀, 1) = q₁
δ(q₁, 0) = q₁
δ(q₁, 1) = q₀
```

## 非确定性有限自动机

### 3.1 NFA的定义

**定义 3.1.1 (NFA)**
非确定性有限自动机是一个五元组 M = (Q, Σ, δ, q₀, F)，其中：

- Q 是有限状态集合
- Σ 是有限输入字母表
- δ: Q × Σ → P(Q) 是转移函数
- q₀ ∈ Q 是初始状态
- F ⊆ Q 是接受状态集合

### 3.2 NFA的状态转移

**扩展转移函数：**

```latex
δ̂: P(Q) × Σ* → P(Q)
```

递归定义：

1. δ̂(S, ε) = S
2. δ̂(S, wa) = ⋃_{q ∈ δ̂(S, w)} δ(q, a)

### 3.3 NFA的语言接受

**定义 3.1.2 (NFA语言接受)**:

```latex
L(M) = {w ∈ Σ* | δ̂({q₀}, w) ∩ F ≠ ∅}
```

## 正则语言

### 4.1 正则语言的定义

**定义 4.1.1 (正则语言)**
语言 L 是正则的，当且仅当存在有限自动机 M 使得 L = L(M)。

### 4.2 正则语言的性质

**定理 4.1.1 (正则语言的封闭性)**
正则语言在以下运算下封闭：

1. 并集
2. 交集
3. 补集
4. 连接
5. 星闭包

**证明 (并集封闭性)：**

1. 设 L₁ = L(M₁), L₂ = L(M₂)
2. 构造 NFA M 接受 L₁ ∪ L₂
3. 使用ε转移连接两个自动机
4. 因此 L₁ ∪ L₂ 是正则的

### 4.3 泵引理

**定理 4.1.2 (泵引理)**
设 L 是正则语言，则存在常数 n 使得对于任意 w ∈ L 且 |w| ≥ n，存在分解 w = xyz 满足：

1. |xy| ≤ n
2. |y| > 0
3. ∀k ≥ 0 (xyᵏz ∈ L)

**证明：**

1. 设 M 是接受 L 的 DFA，有 n 个状态
2. 对于 |w| ≥ n，在 M 上运行 w 时至少经过一个状态两次
3. 设第一次和第二次经过状态 q 时的输入分别为 x 和 xy
4. 则 y 是循环部分，可以重复任意次数

## 形式化表示

### 5.1 一阶逻辑表示

**语言 L：**

- 个体变元：q, q', q₀, q₁, ..., a, b, ..., w, x, y, z, ...
- 谓词符号：∈ (属于), = (等于), δ (转移)
- 函数符号：δ̂ (扩展转移)
- 逻辑连接词：¬, ∧, ∨, →, ↔
- 量词：∀, ∃

**公理系统：**

```latex
A1: ∀q∀a∃q'(δ(q, a) = q')  // 转移函数定义
A2: δ̂(q, ε) = q  // 空串转移
A3: δ̂(q, wa) = δ(δ̂(q, w), a)  // 扩展转移递归
A4: w ∈ L(M) ↔ δ̂(q₀, w) ∈ F  // 语言接受定义
```

### 5.2 类型论表示

**类型定义：**

```rust
// 状态类型
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct State(String);

// 输入符号类型
#[derive(Debug, Clone, PartialEq, Eq)]
struct Symbol(char);

// 转移函数类型
type TransitionFunction = Fn(State, Symbol) -> State;

// 有限自动机类型
struct FiniteAutomaton {
    states: HashSet<State>,
    alphabet: HashSet<Symbol>,
    transition: Box<dyn TransitionFunction>,
    initial_state: State,
    accepting_states: HashSet<State>,
}

impl FiniteAutomaton {
    // 扩展转移函数
    fn extended_transition(&self, state: &State, input: &str) -> State {
        let mut current_state = state.clone();
        
        for ch in input.chars() {
            let symbol = Symbol(ch);
            current_state = (self.transition)(current_state, symbol);
        }
        
        current_state
    }
    
    // 语言接受
    fn accepts(&self, input: &str) -> bool {
        let final_state = self.extended_transition(&self.initial_state, input);
        self.accepting_states.contains(&final_state)
    }
}

// 非确定性有限自动机
struct NondeterministicFiniteAutomaton {
    states: HashSet<State>,
    alphabet: HashSet<Symbol>,
    transition: HashMap<(State, Symbol), HashSet<State>>,
    initial_state: State,
    accepting_states: HashSet<State>,
}

impl NondeterministicFiniteAutomaton {
    // 扩展转移函数
    fn extended_transition(&self, states: &HashSet<State>, input: &str) -> HashSet<State> {
        let mut current_states = states.clone();
        
        for ch in input.chars() {
            let symbol = Symbol(ch);
            let mut next_states = HashSet::new();
            
            for state in &current_states {
                if let Some(transitions) = self.transition.get(&(state.clone(), symbol.clone())) {
                    next_states.extend(transitions);
                }
            }
            
            current_states = next_states;
        }
        
        current_states
    }
    
    // 语言接受
    fn accepts(&self, input: &str) -> bool {
        let initial_states = HashSet::from([self.initial_state.clone()]);
        let final_states = self.extended_transition(&initial_states, input);
        !final_states.is_disjoint(&self.accepting_states)
    }
}
```

## 证明系统

### 6.1 自动机等价性证明

**定理 6.1.1 (DFA与NFA等价)**
对于任意NFA，存在等价的DFA。

**证明：**

1. 设 N = (Q, Σ, δ, q₀, F) 是NFA
2. 构造DFA D = (P(Q), Σ, δ', {q₀}, F')
3. 其中 δ'(S, a) = ⋃_{q ∈ S} δ(q, a)
4. F' = {S ⊆ Q | S ∩ F ≠ ∅}
5. 证明 L(D) = L(N)

### 6.2 最小化算法

**定理 6.1.2 (DFA最小化)**
对于任意DFA，存在唯一的最小等价DFA。

**算法：**

1. 移除不可达状态
2. 合并等价状态
3. 使用等价关系：q₁ ≡ q₂ ↔ ∀w(δ̂(q₁, w) ∈ F ↔ δ̂(q₂, w) ∈ F)

## 与其他学科的关联

### 7.1 与哲学的关联

**认识论：**

- 状态表示与知识表示
- 转移与推理过程
- 接受与判断标准

**本体论：**

- 状态与实体
- 转移与变化
- 语言与实在

### 7.2 与数学的关联

**集合论：**

- 状态集合
- 语言集合
- 转移关系

**代数：**

- 状态转移的代数结构
- 语言的代数性质
- 自动机的代数表示

### 7.3 与计算机科学的关联

**编译器：**

- 词法分析器
- 语法分析器
- 代码生成

**形式验证：**

- 模型检查
- 状态空间搜索
- 性质验证

## 应用示例

### 8.1 词法分析器

```rust
// 使用有限自动机实现词法分析器
#[derive(Debug, Clone, PartialEq)]
enum TokenType {
    Identifier,
    Number,
    Operator,
    Keyword,
}

#[derive(Debug, Clone)]
struct Token {
    token_type: TokenType,
    value: String,
    position: usize,
}

struct Lexer {
    automaton: FiniteAutomaton,
    keywords: HashSet<String>,
}

impl Lexer {
    fn new() -> Self {
        // 构造识别标识符、数字、运算符的自动机
        let automaton = Self::build_lexical_automaton();
        let keywords = HashSet::from([
            "if".to_string(),
            "else".to_string(),
            "while".to_string(),
            "for".to_string(),
        ]);
        
        Lexer { automaton, keywords }
    }
    
    fn tokenize(&self, input: &str) -> Vec<Token> {
        let mut tokens = Vec::new();
        let mut current_pos = 0;
        
        while current_pos < input.len() {
            let (token, next_pos) = self.scan_token(&input[current_pos..], current_pos);
            tokens.push(token);
            current_pos = next_pos;
        }
        
        tokens
    }
    
    fn scan_token(&self, input: &str, start_pos: usize) -> (Token, usize) {
        // 使用自动机扫描单个词法单元
        unimplemented!()
    }
    
    fn build_lexical_automaton() -> FiniteAutomaton {
        // 构造词法分析自动机
        unimplemented!()
    }
}
```

### 8.2 形式化验证

```rust
// 使用有限自动机进行形式化验证
#[derive(Debug, Clone)]
struct Property {
    name: String,
    automaton: FiniteAutomaton,
}

struct ModelChecker {
    system: FiniteAutomaton,
    properties: Vec<Property>,
}

impl ModelChecker {
    fn new(system: FiniteAutomaton) -> Self {
        ModelChecker {
            system,
            properties: Vec::new(),
        }
    }
    
    fn add_property(&mut self, property: Property) {
        self.properties.push(property);
    }
    
    fn verify_property(&self, property: &Property) -> bool {
        // 检查系统是否满足性质
        // 使用自动机交集和补集操作
        let complement = self.complement_automaton(&property.automaton);
        let intersection = self.intersect_automata(&self.system, &complement);
        
        // 检查交集是否为空
        self.is_empty_automaton(&intersection)
    }
    
    fn complement_automaton(&self, automaton: &FiniteAutomaton) -> FiniteAutomaton {
        // 构造补自动机
        unimplemented!()
    }
    
    fn intersect_automata(&self, a: &FiniteAutomaton, b: &FiniteAutomaton) -> FiniteAutomaton {
        // 构造交集自动机
        unimplemented!()
    }
    
    fn is_empty_automaton(&self, automaton: &FiniteAutomaton) -> bool {
        // 检查自动机是否接受空语言
        unimplemented!()
    }
}
```

## 总结

有限自动机是形式语言理论的基础，通过形式化表示和严格的证明系统，我们可以：

1. 建立自动机的基本理论
2. 定义语言接受机制
3. 证明自动机的等价性
4. 应用到实际系统中

这些理论为后续的编译器、形式验证、自然语言处理等提供了重要的理论基础。
