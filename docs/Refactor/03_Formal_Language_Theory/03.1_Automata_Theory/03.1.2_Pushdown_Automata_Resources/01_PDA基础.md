# 02. 下推自动机 (Pushdown Automata)

## 目录

1. [基本概念](#基本概念)
2. [确定性下推自动机](#确定性下推自动机)
3. [非确定性下推自动机](#非确定性下推自动机)
4. [上下文无关语言](#上下文无关语言)
5. [形式化表示](#形式化表示)
6. [证明系统](#证明系统)
7. [与其他学科的关联](#与其他学科的关联)

## 基本概念

### 1.1 下推自动机的定义

**定义 1.1.1 (下推自动机)**
下推自动机是一个七元组 M = (Q, Σ, Γ, δ, q₀, Z₀, F)，其中：

- Q 是有限状态集合
- Σ 是有限输入字母表
- Γ 是有限栈字母表
- δ: Q × (Σ ∪ {ε}) × Γ → P(Q × Γ*) 是转移函数
- q₀ ∈ Q 是初始状态
- Z₀ ∈ Γ 是初始栈符号
- F ⊆ Q 是接受状态集合

### 1.2 瞬时描述

**定义 1.1.2 (瞬时描述)**
瞬时描述是一个三元组 (q, w, α)，其中：

- q ∈ Q 是当前状态
- w ∈ Σ* 是剩余输入
- α ∈ Γ* 是栈内容

**转移关系：**

```
(q, aw, Zα) ⊢ (p, w, βα)  // 如果 (p, β) ∈ δ(q, a, Z)
(q, w, Zα) ⊢ (p, w, βα)   // 如果 (p, β) ∈ δ(q, ε, Z)
```

### 1.3 语言接受

**定义 1.1.3 (语言接受)**
自动机 M 接受的语言定义为：

```
L(M) = {w ∈ Σ* | (q₀, w, Z₀) ⊢* (q, ε, α) 且 q ∈ F}
```

## 确定性下推自动机

### 2.1 DPDA的定义

**定义 2.1.1 (DPDA)**
确定性下推自动机是满足以下条件的下推自动机：

- 对于任意 q ∈ Q, a ∈ Σ ∪ {ε}, Z ∈ Γ，|δ(q, a, Z)| ≤ 1
- 如果 δ(q, ε, Z) ≠ ∅，则对于任意 a ∈ Σ，δ(q, a, Z) = ∅

### 2.2 DPDA的性质

**定理 2.1.1 (DPDA的确定性)**

```
∀q ∈ Q ∀a ∈ Σ ∪ {ε} ∀Z ∈ Γ (|δ(q, a, Z)| ≤ 1)
```

**证明：**

1. 根据DPDA定义，转移函数满足确定性条件
2. 因此对于任意状态、输入和栈符号，最多有一个转移

### 2.3 DPDA示例

**示例 2.1.1 (识别 {aⁿbⁿ | n ≥ 1} 的DPDA)**

```
M = ({q₀, q₁, q₂}, {a, b}, {Z₀, A}, δ, q₀, Z₀, {q₂})

转移函数：
δ(q₀, a, Z₀) = {(q₁, AZ₀)}
δ(q₁, a, A) = {(q₁, AA)}
δ(q₁, b, A) = {(q₂, ε)}
δ(q₂, b, A) = {(q₂, ε)}
δ(q₂, ε, Z₀) = {(q₂, ε)}
```

## 非确定性下推自动机

### 3.1 NPDA的定义

**定义 3.1.1 (NPDA)**
非确定性下推自动机是允许多个转移的下推自动机。

### 3.2 NPDA的状态转移

**扩展转移关系：**

```
(q, w, α) ⊢* (q, w, α)  // 零步转移
(q, w, α) ⊢* (r, v, β)  // 如果存在 p 使得 (q, w, α) ⊢ (p, u, γ) 且 (p, u, γ) ⊢* (r, v, β)
```

### 3.3 NPDA的语言接受

**定义 3.1.2 (NPDA语言接受)**

```
L(M) = {w ∈ Σ* | (q₀, w, Z₀) ⊢* (q, ε, α) 且 q ∈ F}
```

## 上下文无关语言

### 4.1 上下文无关语言的定义

**定义 4.1.1 (上下文无关语言)**
语言 L 是上下文无关的，当且仅当存在下推自动机 M 使得 L = L(M)。

### 4.2 上下文无关语言的性质

**定理 4.1.1 (上下文无关语言的封闭性)**
上下文无关语言在以下运算下封闭：

1. 并集
2. 连接
3. 星闭包
4. 同态

**证明 (并集封闭性)：**

1. 设 L₁ = L(M₁), L₂ = L(M₂)
2. 构造NPDA M 接受 L₁ ∪ L₂
3. 使用ε转移连接两个自动机
4. 因此 L₁ ∪ L₂ 是上下文无关的

### 4.3 泵引理

**定理 4.1.2 (上下文无关语言的泵引理)**
设 L 是上下文无关语言，则存在常数 n 使得对于任意 w ∈ L 且 |w| ≥ n，存在分解 w = uvxyz 满足：

1. |vxy| ≤ n
2. |vy| > 0
3. ∀k ≥ 0 (uvᵏxyᵏz ∈ L)

**证明：**

1. 设 M 是接受 L 的NPDA，有 m 个状态
2. 对于 |w| ≥ n = 2^m，在 M 上运行 w 时栈高度会重复
3. 设重复的栈配置对应的输入分别为 u 和 uv
4. 则 v 和 y 是循环部分，可以重复任意次数

## 形式化表示

### 5.1 一阶逻辑表示

**语言 L：**

- 个体变元：q, q', q₀, q₁, ..., a, b, ..., w, x, y, z, ..., α, β, γ, ...
- 谓词符号：∈ (属于), = (等于), δ (转移), ⊢ (转移关系)
- 函数符号：δ̂ (扩展转移)
- 逻辑连接词：¬, ∧, ∨, →, ↔
- 量词：∀, ∃

**公理系统：**

```
A1: ∀q∀a∀Z∃S(δ(q, a, Z) = S)  // 转移函数定义
A2: (q, aw, Zα) ⊢ (p, w, βα) ↔ (p, β) ∈ δ(q, a, Z)  // 转移关系
A3: (q, w, α) ⊢* (q, w, α)  // 零步转移
A4: (q, w, α) ⊢* (r, v, β) ↔ ∃p((q, w, α) ⊢ (p, u, γ) ∧ (p, u, γ) ⊢* (r, v, β))  // 多步转移
A5: w ∈ L(M) ↔ (q₀, w, Z₀) ⊢* (q, ε, α) ∧ q ∈ F  // 语言接受定义
```

### 5.2 类型论表示

**类型定义：**

```rust
// 状态类型
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct State(String);

// 输入符号类型
#[derive(Debug, Clone, PartialEq, Eq)]
struct InputSymbol(char);

// 栈符号类型
#[derive(Debug, Clone, PartialEq, Eq)]
struct StackSymbol(char);

// 转移类型
#[derive(Debug, Clone)]
struct Transition {
    from_state: State,
    input_symbol: Option<InputSymbol>,
    stack_symbol: StackSymbol,
    to_state: State,
    stack_push: Vec<StackSymbol>,
}

// 下推自动机类型
struct PushdownAutomaton {
    states: HashSet<State>,
    input_alphabet: HashSet<InputSymbol>,
    stack_alphabet: HashSet<StackSymbol>,
    transitions: Vec<Transition>,
    initial_state: State,
    initial_stack_symbol: StackSymbol,
    accepting_states: HashSet<State>,
}

impl PushdownAutomaton {
    fn new(
        states: HashSet<State>,
        input_alphabet: HashSet<InputSymbol>,
        stack_alphabet: HashSet<StackSymbol>,
        initial_state: State,
        initial_stack_symbol: StackSymbol,
        accepting_states: HashSet<State>,
    ) -> Self {
        PushdownAutomaton {
            states,
            input_alphabet,
            stack_alphabet,
            transitions: Vec::new(),
            initial_state,
            initial_stack_symbol,
            accepting_states,
        }
    }
    
    fn add_transition(&mut self, transition: Transition) {
        self.transitions.push(transition);
    }
    
    fn accepts(&self, input: &str) -> bool {
        let mut configurations = vec![Configuration {
            state: self.initial_state.clone(),
            remaining_input: input.to_string(),
            stack: vec![self.initial_stack_symbol.clone()],
        }];
        
        while !configurations.is_empty() {
            let mut next_configurations = Vec::new();
            
            for config in configurations {
                // 尝试所有可能的转移
                for transition in &self.transitions {
                    if self.can_apply_transition(&config, transition) {
                        let new_config = self.apply_transition(&config, transition);
                        next_configurations.push(new_config);
                    }
                }
            }
            
            // 检查是否有接受配置
            for config in &next_configurations {
                if config.remaining_input.is_empty() 
                    && self.accepting_states.contains(&config.state) {
                    return true;
                }
            }
            
            configurations = next_configurations;
        }
        
        false
    }
    
    fn can_apply_transition(&self, config: &Configuration, transition: &Transition) -> bool {
        // 检查状态是否匹配
        if config.state != transition.from_state {
            return false;
        }
        
        // 检查栈顶符号是否匹配
        if config.stack.is_empty() || config.stack.last().unwrap() != &transition.stack_symbol {
            return false;
        }
        
        // 检查输入符号是否匹配
        match &transition.input_symbol {
            Some(symbol) => {
                if config.remaining_input.is_empty() {
                    return false;
                }
                let first_char = config.remaining_input.chars().next().unwrap();
                InputSymbol(first_char) == *symbol
            }
            None => true, // ε转移
        }
    }
    
    fn apply_transition(&self, config: &Configuration, transition: &Transition) -> Configuration {
        let mut new_stack = config.stack.clone();
        
        // 弹出栈顶符号
        new_stack.pop();
        
        // 压入新符号序列
        for symbol in transition.stack_push.iter().rev() {
            new_stack.push(symbol.clone());
        }
        
        let new_remaining_input = match &transition.input_symbol {
            Some(_) => {
                if !config.remaining_input.is_empty() {
                    config.remaining_input[1..].to_string()
                } else {
                    config.remaining_input.clone()
                }
            }
            None => config.remaining_input.clone(),
        };
        
        Configuration {
            state: transition.to_state.clone(),
            remaining_input: new_remaining_input,
            stack: new_stack,
        }
    }
}

#[derive(Debug, Clone)]
struct Configuration {
    state: State,
    remaining_input: String,
    stack: Vec<StackSymbol>,
}

// 确定性下推自动机
struct DeterministicPushdownAutomaton {
    pda: PushdownAutomaton,
}

impl DeterministicPushdownAutomaton {
    fn new(pda: PushdownAutomaton) -> Self {
        DeterministicPushdownAutomaton { pda }
    }
    
    fn is_deterministic(&self) -> bool {
        // 检查是否满足确定性条件
        for state in &self.pda.states {
            for symbol in &self.pda.stack_alphabet {
                let epsilon_transitions = self.pda.transitions.iter()
                    .filter(|t| t.from_state == *state 
                        && t.input_symbol.is_none() 
                        && t.stack_symbol == *symbol)
                    .count();
                
                let input_transitions = self.pda.transitions.iter()
                    .filter(|t| t.from_state == *state 
                        && t.input_symbol.is_some() 
                        && t.stack_symbol == *symbol)
                    .count();
                
                // 确定性条件：每个配置最多一个转移
                if epsilon_transitions + input_transitions > 1 {
                    return false;
                }
                
                // 如果有ε转移，则不能有输入转移
                if epsilon_transitions > 0 && input_transitions > 0 {
                    return false;
                }
            }
        }
        
        true
    }
    
    fn accepts(&self, input: &str) -> bool {
        if !self.is_deterministic() {
            return false;
        }
        
        self.pda.accepts(input)
    }
}
```

## 证明系统

### 6.1 自动机等价性证明

**定理 6.1.1 (NPDA与CFG等价)**
对于任意上下文无关文法，存在等价的下推自动机。

**证明：**

1. 设 G = (V, Σ, P, S) 是上下文无关文法
2. 构造NPDA M = (Q, Σ, Γ, δ, q₀, Z₀, F)
3. 其中 Q = {q₀, q₁, q₂}, Γ = V ∪ Σ ∪ {Z₀}
4. 转移函数包含：
   - δ(q₀, ε, Z₀) = {(q₁, SZ₀)}
   - δ(q₁, ε, A) = {(q₁, α) | A → α ∈ P}
   - δ(q₁, a, a) = {(q₁, ε)} for a ∈ Σ
   - δ(q₁, ε, Z₀) = {(q₂, ε)}
5. F = {q₂}
6. 证明 L(M) = L(G)

### 6.2 最小化算法

**定理 6.1.2 (DPDA最小化)**
对于任意DPDA，存在唯一的最小等价DPDA。

**算法：**

1. 移除不可达状态
2. 合并等价状态
3. 使用等价关系：q₁ ≡ q₂ ↔ ∀w∀α((q₁, w, α) ⊢*(p₁, ε, β₁) ↔ (q₂, w, α) ⊢* (p₂, ε, β₂))

## 与其他学科的关联

### 7.1 与哲学的关联

**认识论：**

- 状态表示与知识表示
- 栈操作与记忆过程
- 接受与判断标准

**本体论：**

- 状态与实体
- 栈与结构
- 语言与实在

### 7.2 与数学的关联

**集合论：**

- 状态集合
- 语言集合
- 转移关系

**代数：**

- 栈操作的代数结构
- 语言的代数性质
- 自动机的代数表示

### 7.3 与计算机科学的关联

**编译器：**

- 语法分析器
- 表达式求值
- 代码生成

**形式验证：**

- 模型检查
- 状态空间搜索
- 性质验证

## 应用示例

### 8.1 语法分析器

```rust
// 使用下推自动机实现语法分析器
#[derive(Debug, Clone)]
enum Token {
    Identifier(String),
    Number(i32),
    Operator(String),
    Keyword(String),
    LeftParen,
    RightParen,
}

struct Parser {
    automaton: PushdownAutomaton,
    grammar: ContextFreeGrammar,
}

impl Parser {
    fn new(grammar: ContextFreeGrammar) -> Self {
        let automaton = Self::build_parser_automaton(&grammar);
        Parser { automaton, grammar }
    }
    
    fn parse(&self, tokens: &[Token]) -> Option<ParseTree> {
        // 使用下推自动机进行语法分析
        let input = self.tokens_to_string(tokens);
        if self.automaton.accepts(&input) {
            Some(self.build_parse_tree(tokens))
        } else {
            None
        }
    }
    
    fn tokens_to_string(&self, tokens: &[Token]) -> String {
        tokens.iter()
            .map(|token| match token {
                Token::Identifier(name) => name.clone(),
                Token::Number(n) => n.to_string(),
                Token::Operator(op) => op.clone(),
                Token::Keyword(keyword) => keyword.clone(),
                Token::LeftParen => "(".to_string(),
                Token::RightParen => ")".to_string(),
            })
            .collect::<Vec<_>>()
            .join("")
    }
    
    fn build_parser_automaton(grammar: &ContextFreeGrammar) -> PushdownAutomaton {
        // 构造语法分析自动机
        let mut automaton = PushdownAutomaton::new(
            HashSet::from([State("q0".to_string()), State("q1".to_string()), State("q2".to_string())]),
            HashSet::new(), // 输入字母表为空，使用ε转移
            HashSet::from([StackSymbol("S".to_string()), StackSymbol("E".to_string()), StackSymbol("T".to_string())]),
            State("q0".to_string()),
            StackSymbol("Z0".to_string()),
            HashSet::from([State("q2".to_string())]),
        );
        
        // 添加转移规则
        automaton.add_transition(Transition {
            from_state: State("q0".to_string()),
            input_symbol: None,
            stack_symbol: StackSymbol("Z0".to_string()),
            to_state: State("q1".to_string()),
            stack_push: vec![StackSymbol("S".to_string())],
        });
        
        // 添加语法规则对应的转移
        for rule in &grammar.rules {
            automaton.add_transition(Transition {
                from_state: State("q1".to_string()),
                input_symbol: None,
                stack_symbol: StackSymbol(rule.left.clone()),
                to_state: State("q1".to_string()),
                stack_push: rule.right.iter().map(|s| StackSymbol(s.clone())).collect(),
            });
        }
        
        automaton
    }
    
    fn build_parse_tree(&self, tokens: &[Token]) -> ParseTree {
        // 构建语法分析树
        unimplemented!()
    }
}

#[derive(Debug, Clone)]
struct ContextFreeGrammar {
    variables: HashSet<String>,
    terminals: HashSet<String>,
    rules: Vec<ProductionRule>,
    start_symbol: String,
}

#[derive(Debug, Clone)]
struct ProductionRule {
    left: String,
    right: Vec<String>,
}

#[derive(Debug, Clone)]
struct ParseTree {
    node: String,
    children: Vec<ParseTree>,
}
```

### 8.2 形式化验证

```rust
// 使用下推自动机进行形式化验证
#[derive(Debug, Clone)]
struct Property {
    name: String,
    automaton: PushdownAutomaton,
}

struct ModelChecker {
    system: PushdownAutomaton,
    properties: Vec<Property>,
}

impl ModelChecker {
    fn new(system: PushdownAutomaton) -> Self {
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
    
    fn complement_automaton(&self, automaton: &PushdownAutomaton) -> PushdownAutomaton {
        // 构造补自动机（对于确定性自动机）
        let mut complement = automaton.clone();
        let mut new_accepting_states = HashSet::new();
        
        for state in &automaton.states {
            if !automaton.accepting_states.contains(state) {
                new_accepting_states.insert(state.clone());
            }
        }
        
        complement.accepting_states = new_accepting_states;
        complement
    }
    
    fn intersect_automata(&self, a: &PushdownAutomaton, b: &PushdownAutomaton) -> PushdownAutomaton {
        // 构造交集自动机
        let mut intersection = PushdownAutomaton::new(
            HashSet::new(),
            a.input_alphabet.intersection(&b.input_alphabet).cloned().collect(),
            a.stack_alphabet.union(&b.stack_alphabet).cloned().collect(),
            State(format!("({},{})", a.initial_state.0, b.initial_state.0)),
            StackSymbol("Z0".to_string()),
            HashSet::new(),
        );
        
        // 构造状态和转移
        // 这里需要实现复杂的交集构造算法
        
        intersection
    }
    
    fn is_empty_automaton(&self, automaton: &PushdownAutomaton) -> bool {
        // 检查自动机是否接受空语言
        // 使用可达性分析
        let mut reachable_states = HashSet::new();
        reachable_states.insert(automaton.initial_state.clone());
        
        let mut changed = true;
        while changed {
            changed = false;
            for transition in &automaton.transitions {
                if reachable_states.contains(&transition.from_state) {
                    if reachable_states.insert(transition.to_state.clone()) {
                        changed = true;
                    }
                }
            }
        }
        
        // 检查是否有接受状态可达
        reachable_states.intersection(&automaton.accepting_states).next().is_none()
    }
}
```

## 总结

下推自动机是形式语言理论的重要模型，通过形式化表示和严格的证明系统，我们可以：

1. 建立下推自动机的基本理论
2. 定义上下文无关语言的接受机制
3. 证明下推自动机与上下文无关文法的等价性
4. 应用到语法分析和形式验证中

这些理论为后续的编译器、形式验证、自然语言处理等提供了重要的理论基础。
