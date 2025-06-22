# 2. 自动机理论 (Automata Theory)

## 2.1 概述

自动机理论是形式语言理论的核心分支，研究抽象计算模型及其计算能力。它为计算机科学、编译原理、人工智能等领域提供了理论基础。

## 2.2 有限自动机

### 2.2.1 确定性有限自动机 (DFA)

**定义 2.1** (确定性有限自动机)
确定性有限自动机是一个五元组 $M = (Q, \Sigma, \delta, q_0, F)$，其中：

1. $Q$ 是有限状态集
2. $\Sigma$ 是有限输入字母表
3. $\delta: Q \times \Sigma \to Q$ 是转移函数
4. $q_0 \in Q$ 是初始状态
5. $F \subseteq Q$ 是接受状态集

**定义 2.2** (DFA的扩展转移函数)
扩展转移函数 $\hat{\delta}: Q \times \Sigma^* \to Q$ 定义为：

1. $\hat{\delta}(q, \varepsilon) = q$
2. $\hat{\delta}(q, wa) = \delta(\hat{\delta}(q, w), a)$

**定义 2.3** (DFA接受的语言)
DFA $M$ 接受的语言定义为：
$$L(M) = \{w \in \Sigma^* \mid \hat{\delta}(q_0, w) \in F\}$$

### 2.2.2 非确定性有限自动机 (NFA)

**定义 2.4** (非确定性有限自动机)
非确定性有限自动机是一个五元组 $M = (Q, \Sigma, \delta, q_0, F)$，其中：

1. $Q$ 是有限状态集
2. $\Sigma$ 是有限输入字母表
3. $\delta: Q \times \Sigma \to 2^Q$ 是转移函数
4. $q_0 \in Q$ 是初始状态
5. $F \subseteq Q$ 是接受状态集

**定义 2.5** (NFA的扩展转移函数)
扩展转移函数 $\hat{\delta}: Q \times \Sigma^* \to 2^Q$ 定义为：

1. $\hat{\delta}(q, \varepsilon) = \{q\}$
2. $\hat{\delta}(q, wa) = \bigcup_{p \in \hat{\delta}(q, w)} \delta(p, a)$

**定义 2.6** (NFA接受的语言)
NFA $M$ 接受的语言定义为：
$$L(M) = \{w \in \Sigma^* \mid \hat{\delta}(q_0, w) \cap F \neq \emptyset\}$$

### 2.2.3 DFA与NFA的等价性

**定理 2.1** (DFA与NFA等价性)
对于每个NFA，存在等价的DFA。

**证明**:
构造DFA $M' = (Q', \Sigma, \delta', q_0', F')$，其中：

- $Q' = 2^Q$
- $q_0' = \{q_0\}$
- $F' = \{S \subseteq Q \mid S \cap F \neq \emptyset\}$
- $\delta'(S, a) = \bigcup_{q \in S} \delta(q, a)$

### 2.2.4 有限自动机的性质

**定理 2.2** (有限自动机的封闭性)
正则语言在以下运算下封闭：

1. 并集
2. 交集
3. 补集
4. 连接
5. 克林闭包

## 2.3 下推自动机

### 2.3.1 确定性下推自动机 (DPDA)

**定义 2.7** (确定性下推自动机)
确定性下推自动机是一个七元组 $M = (Q, \Sigma, \Gamma, \delta, q_0, Z_0, F)$，其中：

1. $Q$ 是有限状态集
2. $\Sigma$ 是输入字母表
3. $\Gamma$ 是栈字母表
4. $\delta: Q \times \Sigma \times \Gamma \to Q \times \Gamma^*$ 是转移函数
5. $q_0 \in Q$ 是初始状态
6. $Z_0 \in \Gamma$ 是初始栈符号
7. $F \subseteq Q$ 是接受状态集

### 2.3.2 非确定性下推自动机 (NPDA)

**定义 2.8** (非确定性下推自动机)
非确定性下推自动机是一个七元组 $M = (Q, \Sigma, \Gamma, \delta, q_0, Z_0, F)$，其中：

1. $Q$ 是有限状态集
2. $\Sigma$ 是输入字母表
3. $\Gamma$ 是栈字母表
4. $\delta: Q \times (\Sigma \cup \{\varepsilon\}) \times \Gamma \to 2^{Q \times \Gamma^*}$ 是转移函数
5. $q_0 \in Q$ 是初始状态
6. $Z_0 \in \Gamma$ 是初始栈符号
7. $F \subseteq Q$ 是接受状态集

### 2.3.3 下推自动机的配置

**定义 2.9** (配置)
下推自动机的配置是一个三元组 $(q, w, \gamma)$，其中：

- $q \in Q$ 是当前状态
- $w \in \Sigma^*$ 是剩余输入串
- $\gamma \in \Gamma^*$ 是栈内容

**定义 2.10** (转移关系)
配置转移关系 $\vdash$ 定义为：
$(q, aw, Z\gamma) \vdash (p, w, \alpha\gamma)$ 当且仅当 $(p, \alpha) \in \delta(q, a, Z)$

### 2.3.4 下推自动机接受的语言

**定义 2.11** (终态接受)
下推自动机 $M$ 终态接受的语言定义为：
$$L(M) = \{w \in \Sigma^* \mid (q_0, w, Z_0) \vdash^* (q, \varepsilon, \gamma), q \in F\}$$

**定义 2.12** (空栈接受)
下推自动机 $M$ 空栈接受的语言定义为：
$$N(M) = \{w \in \Sigma^* \mid (q_0, w, Z_0) \vdash^* (q, \varepsilon, \varepsilon)\}$$

## 2.4 图灵机

### 2.4.1 基本图灵机

**定义 2.13** (图灵机)
图灵机是一个七元组 $M = (Q, \Sigma, \Gamma, \delta, q_0, B, F)$，其中：

1. $Q$ 是有限状态集
2. $\Sigma$ 是输入字母表
3. $\Gamma$ 是带字母表，$\Sigma \subseteq \Gamma$
4. $\delta: Q \times \Gamma \to Q \times \Gamma \times \{L, R\}$ 是转移函数
5. $q_0 \in Q$ 是初始状态
6. $B \in \Gamma - \Sigma$ 是空白符号
7. $F \subseteq Q$ 是接受状态集

### 2.4.2 图灵机的配置

**定义 2.14** (图灵机配置)
图灵机的配置是一个三元组 $(q, \alpha, i)$，其中：

- $q \in Q$ 是当前状态
- $\alpha \in \Gamma^*$ 是带内容
- $i \in \mathbb{N}$ 是读写头位置

**定义 2.15** (图灵机转移)
配置转移关系 $\vdash$ 定义为：
$(q, \alpha, i) \vdash (p, \beta, j)$ 当且仅当：

- $\delta(q, \alpha_i) = (p, b, D)$
- $\beta = \alpha[0:i] b \alpha[i+1:]$
- $j = i + 1$ (如果 $D = R$) 或 $j = i - 1$ (如果 $D = L$)

### 2.4.3 图灵机接受的语言

**定义 2.16** (图灵机接受的语言)
图灵机 $M$ 接受的语言定义为：
$$L(M) = \{w \in \Sigma^* \mid (q_0, w, 0) \vdash^* (q, \alpha, i), q \in F\}$$

### 2.4.4 图灵机的变种

**定义 2.17** (多带图灵机)
多带图灵机有多个带，每个带都有自己的读写头。

**定义 2.18** (非确定性图灵机)
非确定性图灵机的转移函数为：
$$\delta: Q \times \Gamma \to 2^{Q \times \Gamma \times \{L, R\}}$$

**定理 2.3** (图灵机变种的等价性)
所有图灵机变种在计算能力上等价。

## 2.5 自动机在计算机科学中的应用

### 2.5.1 词法分析

有限自动机在编译器中用于词法分析：

```rust
// 词法分析器
struct Lexer {
    dfa: DFA,
    source: String,
    position: usize,
}

struct DFA {
    states: Vec<State>,
    transitions: HashMap<(StateId, char), StateId>,
    initial_state: StateId,
    accepting_states: HashSet<StateId>,
}

impl Lexer {
    fn new(dfa: DFA, source: String) -> Self {
        Lexer {
            dfa,
            source,
            position: 0,
        }
    }
    
    fn next_token(&mut self) -> Option<Token> {
        let start_pos = self.position;
        let mut current_state = self.dfa.initial_state;
        let mut last_accepting_pos = None;
        let mut last_accepting_state = None;
        
        while self.position < self.source.len() {
            let current_char = self.source.chars().nth(self.position).unwrap();
            
            if let Some(&next_state) = self.dfa.transitions.get(&(current_state, current_char)) {
                current_state = next_state;
                
                if self.dfa.accepting_states.contains(&current_state) {
                    last_accepting_pos = Some(self.position);
                    last_accepting_state = Some(current_state);
                }
                
                self.position += 1;
            } else {
                break;
            }
        }
        
        if let (Some(pos), Some(state)) = (last_accepting_pos, last_accepting_state) {
            let lexeme = &self.source[start_pos..=pos];
            let token_type = self.get_token_type(state);
            Some(Token::new(token_type, lexeme.to_string(), start_pos))
        } else {
            None
        }
    }
    
    fn get_token_type(&self, state: StateId) -> TokenType {
        // 根据状态确定token类型
        match state {
            1 => TokenType::Identifier,
            2 => TokenType::Number,
            3 => TokenType::String,
            _ => TokenType::Unknown,
        }
    }
}

// 构建DFA的示例
fn build_identifier_dfa() -> DFA {
    let mut transitions = HashMap::new();
    
    // 状态0到状态1的转移（字母或下划线）
    for c in 'a'..='z' {
        transitions.insert((0, c), 1);
    }
    for c in 'A'..='Z' {
        transitions.insert((0, c), 1);
    }
    transitions.insert((0, '_'), 1);
    
    // 状态1的自环（字母、数字或下划线）
    for c in 'a'..='z' {
        transitions.insert((1, c), 1);
    }
    for c in 'A'..='Z' {
        transitions.insert((1, c), 1);
    }
    for c in '0'..='9' {
        transitions.insert((1, c), 1);
    }
    transitions.insert((1, '_'), 1);
    
    DFA {
        states: vec![0, 1],
        transitions,
        initial_state: 0,
        accepting_states: HashSet::from([1]),
    }
}
```

### 2.5.2 语法分析

下推自动机用于语法分析：

```rust
// 语法分析器
struct Parser {
    pda: PushDownAutomaton,
    tokens: Vec<Token>,
    position: usize,
}

struct PushDownAutomaton {
    states: Vec<State>,
    stack: Vec<StackSymbol>,
    transitions: HashMap<(StateId, Option<TokenType>, StackSymbol), Vec<(StateId, Vec<StackSymbol>)>>,
    initial_state: StateId,
    accepting_states: HashSet<StateId>,
}

impl Parser {
    fn new(pda: PushDownAutomaton, tokens: Vec<Token>) -> Self {
        Parser {
            pda,
            tokens,
            position: 0,
        }
    }
    
    fn parse(&mut self) -> Result<ParseTree, ParseError> {
        let mut current_state = self.pda.initial_state;
        let mut stack = vec![self.pda.initial_stack_symbol.clone()];
        
        while self.position < self.tokens.len() || !stack.is_empty() {
            let current_token = self.tokens.get(self.position);
            let top_stack = stack.last().unwrap();
            
            let key = (current_state, current_token.map(|t| t.token_type.clone()), top_stack.clone());
            
            if let Some(transitions) = self.pda.transitions.get(&key) {
                // 选择第一个转移（简化实现）
                let (next_state, stack_push) = &transitions[0];
                current_state = *next_state;
                
                // 更新栈
                stack.pop();
                for symbol in stack_push.iter().rev() {
                    stack.push(symbol.clone());
                }
                
                if current_token.is_some() {
                    self.position += 1;
                }
            } else {
                return Err(ParseError::UnexpectedToken);
            }
        }
        
        if self.pda.accepting_states.contains(&current_state) {
            Ok(ParseTree::new())
        } else {
            Err(ParseError::InvalidInput)
        }
    }
}

// 构建PDA的示例
fn build_expression_pda() -> PushDownAutomaton {
    let mut transitions = HashMap::new();
    
    // 处理左括号
    transitions.insert(
        (0, Some(TokenType::LeftParen), StackSymbol::Initial),
        vec![(0, vec![StackSymbol::Initial, StackSymbol::LeftParen])]
    );
    
    // 处理右括号
    transitions.insert(
        (0, Some(TokenType::RightParen), StackSymbol::LeftParen),
        vec![(0, vec![])]
    );
    
    PushDownAutomaton {
        states: vec![0],
        stack: vec![StackSymbol::Initial],
        transitions,
        initial_state: 0,
        accepting_states: HashSet::from([0]),
    }
}
```

### 2.5.3 形式化验证

图灵机用于形式化验证：

```rust
// 图灵机模拟器
struct TuringMachine {
    states: Vec<State>,
    tape: Vec<char>,
    head_position: usize,
    current_state: StateId,
    transitions: HashMap<(StateId, char), (StateId, char, Direction)>,
    accepting_states: HashSet<StateId>,
}

enum Direction {
    Left,
    Right,
}

impl TuringMachine {
    fn new(transitions: HashMap<(StateId, char), (StateId, char, Direction)>, 
           accepting_states: HashSet<StateId>) -> Self {
        TuringMachine {
            states: vec![],
            tape: vec!['B'], // 空白符号
            head_position: 0,
            current_state: 0,
            transitions,
            accepting_states,
        }
    }
    
    fn run(&mut self, input: &str) -> bool {
        // 初始化带
        self.tape = input.chars().collect();
        self.tape.push('B'); // 添加空白符号
        self.head_position = 0;
        self.current_state = 0;
        
        loop {
            let current_symbol = self.tape[self.head_position];
            
            if let Some(&(next_state, write_symbol, direction)) = 
                self.transitions.get(&(self.current_state, current_symbol)) {
                
                // 写入符号
                self.tape[self.head_position] = write_symbol;
                
                // 移动读写头
                match direction {
                    Direction::Left => {
                        if self.head_position > 0 {
                            self.head_position -= 1;
                        } else {
                            self.tape.insert(0, 'B');
                        }
                    },
                    Direction::Right => {
                        self.head_position += 1;
                        if self.head_position >= self.tape.len() {
                            self.tape.push('B');
                        }
                    }
                }
                
                self.current_state = next_state;
            } else {
                // 没有转移，停机
                break;
            }
        }
        
        self.accepting_states.contains(&self.current_state)
    }
}

// 构建图灵机的示例
fn build_palindrome_tm() -> TuringMachine {
    let mut transitions = HashMap::new();
    
    // 检查回文串的图灵机
    // 状态0：向右移动到第一个符号
    transitions.insert((0, '0'), (1, '0', Direction::Right));
    transitions.insert((0, '1'), (1, '1', Direction::Right));
    
    // 状态1：向右移动到最后一个符号
    transitions.insert((1, '0'), (1, '0', Direction::Right));
    transitions.insert((1, '1'), (1, '1', Direction::Right));
    transitions.insert((1, 'B'), (2, 'B', Direction::Left));
    
    // 状态2：比较并向左移动
    transitions.insert((2, '0'), (3, 'B', Direction::Left));
    transitions.insert((2, '1'), (4, 'B', Direction::Left));
    
    // 状态3：向左移动到对应的0
    transitions.insert((3, '0'), (5, 'B', Direction::Left));
    transitions.insert((3, '1'), (6, 'B', Direction::Left)); // 拒绝
    
    // 状态4：向左移动到对应的1
    transitions.insert((4, '0'), (6, 'B', Direction::Left)); // 拒绝
    transitions.insert((4, '1'), (5, 'B', Direction::Left));
    
    // 状态5：继续向左移动
    transitions.insert((5, '0'), (5, '0', Direction::Left));
    transitions.insert((5, '1'), (5, '1', Direction::Left));
    transitions.insert((5, 'B'), (0, 'B', Direction::Right));
    
    // 状态6：拒绝状态（无转移）
    
    TuringMachine::new(transitions, HashSet::from([0]))
}
```

### 2.5.4 形式化证明

在定理证明系统中，自动机理论为形式化证明提供了基础：

```lean
-- Lean 中的自动机理论
import data.finset
import data.list

-- 有限自动机
structure finite_automaton (α : Type*) :=
  (states : finset α)
  (alphabet : finset char)
  (transitions : α → char → α)
  (initial_state : α)
  (accepting_states : finset α)

-- 配置
structure configuration (α : Type*) :=
  (state : α)
  (input : list char)
  (position : ℕ)

-- 转移关系
def step {α : Type*} (M : finite_automaton α) (c : configuration α) : configuration α :=
  if c.position < c.input.length then
    let current_char := c.input.nth_le c.position (by linarith)
    let next_state := M.transitions c.state current_char
    { state := next_state,
      input := c.input,
      position := c.position + 1 }
  else
    c

-- 多步转移
def steps {α : Type*} (M : finite_automaton α) (c : configuration α) (n : ℕ) : configuration α :=
  nat.rec_on n c (λ _ c', step M c')

-- 接受的语言
def accepts {α : Type*} (M : finite_automaton α) (w : list char) : Prop :=
  let final_config := steps M { state := M.initial_state, input := w, position := 0 } w.length
  M.accepting_states.contains final_config.state

-- 确定性有限自动机的性质
theorem dfa_deterministic {α : Type*} (M : finite_automaton α) (c : configuration α) :
  ∃! c', step M c = c' :=
begin
  -- 证明确定性
  existsi step M c,
  split,
  { refl },
  { intros c' h,
    rw ← h,
    refl }
end

-- 正则语言的封闭性
theorem regular_union {α β : Type*} (M1 : finite_automaton α) (M2 : finite_automaton β) :
  ∃ M : finite_automaton (α ⊕ β), 
  ∀ w : list char, accepts M w ↔ accepts M1 w ∨ accepts M2 w :=
begin
  -- 构造并集自动机
  let M := {
    states := finset.union (finset.map sum.inl M1.states) (finset.map sum.inr M2.states),
    alphabet := finset.union M1.alphabet M2.alphabet,
    transitions := λ s c, match s with
      | sum.inl s1 := sum.inl (M1.transitions s1 c)
      | sum.inr s2 := sum.inr (M2.transitions s2 c)
      end,
    initial_state := sum.inl M1.initial_state,
    accepting_states := finset.union 
      (finset.map sum.inl M1.accepting_states)
      (finset.map sum.inr M2.accepting_states)
  },
  existsi M,
  -- 证明等价性
  sorry
end
```

## 2.6 总结

自动机理论为形式科学提供了强大的计算模型：

1. **有限自动机** 为正则语言提供了识别模型
2. **下推自动机** 为上下文无关语言提供了识别模型
3. **图灵机** 为可计算性理论提供了基础模型
4. **应用领域** 涵盖了编译原理、形式化验证、人工智能等多个领域
5. **形式化方法** 为计算理论提供了严格的数学基础

这些理论不仅在理论计算机科学中具有重要地位，也为实际应用提供了基础。

## 参考文献

1. Hopcroft, J. E., Motwani, R., & Ullman, J. D. (2006). *Introduction to automata theory, languages, and computation*. Pearson Education.
2. Sipser, M. (2012). *Introduction to the theory of computation*. Cengage Learning.
3. Kozen, D. C. (2006). *Theory of computation*. Springer.
4. Lewis, H. R., & Papadimitriou, C. H. (1997). *Elements of the theory of computation*. Prentice Hall.

---

**更新时间**: 2024-12-21  
**版本**: 1.0  
**作者**: FormalScience Team
