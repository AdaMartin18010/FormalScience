# 正则文法与有限自动机转换代码实现

以下提供了正则文法和有限自动机之间转换的Rust语言实现。代码采用了模块化的设计，并包含了详细的注释说明。

## 1. 基本数据结构

首先，我们定义基本的数据结构：

```rust
use std::collections::{HashMap, HashSet};
use std::fmt;

/// 符号类型，可以是终结符或输入符号
type Symbol = char;

/// 状态或非终结符
type State = String;

/// 正则文法
#[derive(Debug, Clone)]
struct RegularGrammar {
    /// 非终结符集合
    non_terminals: HashSet<State>,
    /// 终结符集合
    terminals: HashSet<Symbol>,
    /// 产生式规则，将非终结符映射到可能的产生式右侧
    productions: HashMap<State, Vec<String>>,
    /// 起始符号
    start_symbol: State,
    /// 文法类型：右线性或左线性
    grammar_type: GrammarType,
}

/// 文法类型
#[derive(Debug, Clone, PartialEq)]
enum GrammarType {
    RightLinear,
    LeftLinear,
    Mixed, // 混合类型，可能不是严格的正则文法
}

/// 有限自动机
#[derive(Debug, Clone)]
struct FiniteAutomaton {
    /// 状态集合
    states: HashSet<State>,
    /// 输入字母表
    alphabet: HashSet<Symbol>,
    /// 转移函数，将(状态,符号)映射到目标状态集合
    transitions: HashMap<(State, Symbol), HashSet<State>>,
    /// 初始状态
    initial_state: State,
    /// 接受状态集合
    accepting_states: HashSet<State>,
}

/// 自动机类型
#[derive(Debug, Clone, PartialEq)]
enum AutomatonType {
    DFA,
    NFA,
    EpsilonNFA,
}

impl RegularGrammar {
    /// 创建一个新的正则文法
    fn new(grammar_type: GrammarType) -> Self {
        RegularGrammar {
            non_terminals: HashSet::new(),
            terminals: HashSet::new(),
            productions: HashMap::new(),
            start_symbol: String::new(),
            grammar_type,
        }
    }

    /// 添加一条产生式
    fn add_production(&mut self, lhs: &str, rhs: &str) {
        let lhs = lhs.to_string();
        self.non_terminals.insert(lhs.clone());
        
        // 如果这是第一个添加的非终结符，设为起始符号
        if self.start_symbol.is_empty() {
            self.start_symbol = lhs.clone();
        }
        
        // 添加右侧
        let productions = self.productions.entry(lhs).or_insert_with(Vec::new);
        productions.push(rhs.to_string());
        
        // 提取终结符
        for c in rhs.chars() {
            if c.is_lowercase() || c.is_digit(10) || c == 'ε' {
                if c != 'ε' {  // 不将ε添加为终结符
                    self.terminals.insert(c);
                }
            }
        }
    }

    /// 检查文法类型
    fn validate_grammar_type(&self) -> GrammarType {
        let mut right_linear = true;
        let mut left_linear = true;
        
        for (_, productions) in &self.productions {
            for rhs in productions {
                if rhs == "ε" {
                    continue; // 忽略空产生式
                }
                
                let chars: Vec<char> = rhs.chars().collect();
                let n = chars.len();
                
                // 检查是否符合右线性文法形式: A -> aB 或 A -> a
                if n > 0 {
                    let mut is_valid_right = true;
                    for i in 0..n-1 {
                        // 前n-1个字符应该都是终结符
                        if !self.terminals.contains(&chars[i]) {
                            is_valid_right = false;
                            break;
                        }
                    }
                    // 最后一个字符可以是非终结符或终结符
                    let last_char = chars[n-1].to_string();
                    if !self.non_terminals.contains(&last_char) && !self.terminals.contains(&chars[n-1]) {
                        is_valid_right = false;
                    }
                    if !is_valid_right {
                        right_linear = false;
                    }
                }
                
                // 检查是否符合左线性文法形式: A -> Ba 或 A -> a
                if n > 0 {
                    let mut is_valid_left = true;
                    
                    // 第一个字符可以是非终结符或终结符
                    let first_char = chars[0].to_string();
                    if !self.non_terminals.contains(&first_char) && !self.terminals.contains(&chars[0]) {
                        is_valid_left = false;
                    }
                    
                    for i in 1..n {
                        // 后面的字符应该都是终结符
                        if !self.terminals.contains(&chars[i]) {
                            is_valid_left = false;
                            break;
                        }
                    }
                    
                    if !is_valid_left {
                        left_linear = false;
                    }
                }
            }
        }
        
        if right_linear && left_linear {
            // 如果只有单个终结符的产生式，那么既是右线性也是左线性
            return GrammarType::RightLinear; // 默认使用右线性
        } else if right_linear {
            return GrammarType::RightLinear;
        } else if left_linear {
            return GrammarType::LeftLinear;
        } else {
            return GrammarType::Mixed; // 可能不是正则文法
        }
    }
}

impl FiniteAutomaton {
    /// 创建一个新的有限自动机
    fn new(automaton_type: AutomatonType) -> Self {
        FiniteAutomaton {
            states: HashSet::new(),
            alphabet: HashSet::new(),
            transitions: HashMap::new(),
            initial_state: String::new(),
            accepting_states: HashSet::new(),
        }
    }

    /// 添加一个状态
    fn add_state(&mut self, state: &str) {
        let state = state.to_string();
        self.states.insert(state.clone());
        
        // 如果这是第一个添加的状态，设为初始状态
        if self.initial_state.is_empty() {
            self.initial_state = state;
        }
    }
    
    /// 设置初始状态
    fn set_initial_state(&mut self, state: &str) {
        let state = state.to_string();
        if !self.states.contains(&state) {
            self.states.insert(state.clone());
        }
        self.initial_state = state;
    }
    
    /// 添加接受状态
    fn add_accepting_state(&mut self, state: &str) {
        let state = state.to_string();
        if !self.states.contains(&state) {
            self.states.insert(state.clone());
        }
        self.accepting_states.insert(state);
    }
    
    /// 添加转移
    fn add_transition(&mut self, from: &str, symbol: Symbol, to: &str) {
        let from = from.to_string();
        let to = to.to_string();
        
        // 确保状态存在
        if !self.states.contains(&from) {
            self.states.insert(from.clone());
        }
        if !self.states.contains(&to) {
            self.states.insert(to.clone());
        }
        
        // 添加符号到字母表
        if symbol != 'ε' {  // 不将ε添加到字母表
            self.alphabet.insert(symbol);
        }
        
        // 添加转移
        let transitions = self.transitions.entry((from, symbol)).or_insert_with(HashSet::new);
        transitions.insert(to);
    }
    
    /// 判断是否为DFA
    fn is_dfa(&self) -> bool {
        // 检查每个状态对每个符号是否有且仅有一个转移
        for state in &self.states {
            for symbol in &self.alphabet {
                let key = (state.clone(), *symbol);
                if !self.transitions.contains_key(&key) {
                    return false; // 缺少转移
                }
                if self.transitions[&key].len() != 1 {
                    return false; // 多个转移
                }
            }
        }
        true
    }
}
```

## 2. 右线性文法到NFA的转换

```rust
/// 将右线性文法转换为NFA
fn right_linear_grammar_to_nfa(grammar: &RegularGrammar) -> Result<FiniteAutomaton, String> {
    // 验证是否为右线性文法
    if grammar.validate_grammar_type() != GrammarType::RightLinear {
        return Err("输入不是右线性文法".to_string());
    }

    let mut nfa = FiniteAutomaton::new(AutomatonType::NFA);
    
    // 设置初始状态
    nfa.set_initial_state(&grammar.start_symbol);
    
    // 添加特殊的接受状态
    let final_state = "qf";
    nfa.add_accepting_state(final_state);
    
    // 处理产生式
    for (lhs, productions) in &grammar.productions {
        for rhs in productions {
            if rhs == "ε" {
                // A -> ε，将A设为接受状态
                nfa.add_accepting_state(lhs);
            } else if rhs.len() == 1 {
                // A -> a，添加转移 A --a--> qf
                let symbol = rhs.chars().next().unwrap();
                nfa.add_transition(lhs, symbol, final_state);
            } else {
                // A -> aB，添加转移 A --a--> B
                let chars: Vec<char> = rhs.chars().collect();
                let symbol = chars[0];
                let to_state = &chars[1..].iter().collect::<String>();
                nfa.add_transition(lhs, symbol, to_state);
            }
        }
    }
    
    Ok(nfa)
}
```

## 3. NFA到右线性文法的转换

```rust
/// 将NFA转换为右线性文法
fn nfa_to_right_linear_grammar(nfa: &FiniteAutomaton) -> RegularGrammar {
    let mut grammar = RegularGrammar::new(GrammarType::RightLinear);
    
    // 设置起始符号
    grammar.start_symbol = nfa.initial_state.clone();
    grammar.non_terminals = nfa.states.clone();
    grammar.terminals = nfa.alphabet.clone();
    
    // 处理转移
    for ((from, symbol), to_states) in &nfa.transitions {
        for to in to_states {
            let rhs = format!("{}{}", symbol, to);
            grammar.add_production(from, &rhs);
        }
    }
    
    // 处理接受状态
    for state in &nfa.accepting_states {
        grammar.add_production(state, "ε");
    }
    
    grammar
}
```

## 4. DFA最小化

```rust
/// 计算状态的ε-闭包
fn epsilon_closure(nfa: &FiniteAutomaton, state: &str) -> HashSet<String> {
    let mut closure = HashSet::new();
    let mut stack = vec![state.to_string()];
    
    while let Some(current) = stack.pop() {
        if closure.insert(current.clone()) {
            // 如果current是新加入闭包的，检查它的ε转移
            if let Some(next_states) = nfa.transitions.get(&(current, 'ε')) {
                for next in next_states {
                    if !closure.contains(next) {
                        stack.push(next.clone());
                    }
                }
            }
        }
    }
    
    closure
}

/// 使用Hopcroft算法最小化DFA
fn minimize_dfa(dfa: &FiniteAutomaton) -> FiniteAutomaton {
    // 首先移除不可达状态
    let reachable = find_reachable_states(dfa);
    let mut dfa = remove_unreachable_states(dfa, &reachable);
    
    // 初始划分：接受状态和非接受状态
    let mut partition = vec![dfa.accepting_states.clone()];
    let non_accepting: HashSet<_> = dfa.states.difference(&dfa.accepting_states).cloned().collect();
    if !non_accepting.is_empty() {
        partition.push(non_accepting);
    }
    
    let mut work_list = partition.clone();
    
    // 迭代细化划分
    while let Some(set) = work_list.pop() {
        for symbol in &dfa.alphabet {
            // 找出所有通过symbol转移能到达set中某个状态的状态
            let mut x = HashSet::new();
            
            for state in &dfa.states {
                let key = (state.clone(), *symbol);
                if let Some(to_states) = dfa.transitions.get(&key) {
                    for to in to_states {
                        if set.contains(to) {
                            x.insert(state.clone());
                            break;
                        }
                    }
                }
            }
            
            // 使用X细化当前划分
            let mut new_partition = Vec::new();
            
            for group in &partition {
                let intersection: HashSet<_> = group.intersection(&x).cloned().collect();
                let difference: HashSet<_> = group.difference(&x).cloned().collect();
                
                if !intersection.is_empty() && !difference.is_empty() {
                    // 这个组被分成了两部分
                    new_partition.push(intersection.clone());
                    new_partition.push(difference.clone());
                    
                    // 更新工作列表
                    if work_list.contains(group) {
                        work_list.retain(|g| g != group);
                        work_list.push(intersection);
                        work_list.push(difference);
                    } else {
                        if intersection.len() <= difference.len() {
                            work_list.push(intersection);
                        } else {
                            work_list.push(difference);
                        }
                    }
                } else {
                    // 这个组没有被分割
                    new_partition.push(group.clone());
                }
            }
            
            partition = new_partition;
        }
    }
    
    // 构建最小DFA
    let mut min_dfa = FiniteAutomaton::new(AutomatonType::DFA);
    
    // 创建新状态
    let mut state_map = HashMap::new();
    for (i, group) in partition.iter().enumerate() {
        let new_state = format!("q{}", i);
        
        for old_state in group {
            state_map.insert(old_state.clone(), new_state.clone());
        }
        
        min_dfa.add_state(&new_state);
    }
    
    // 设置初始状态
    min_dfa.set_initial_state(&state_map[&dfa.initial_state]);
    
    // 设置接受状态
    for accepting in &dfa.accepting_states {
        min_dfa.add_accepting_state(&state_map[accepting]);
    }
    
    // 添加转移
    for group in &partition {
        if group.is_empty() {
            continue;
        }
        
        // 选择组中的一个代表状态
        let representative = group.iter().next().unwrap();
        let new_state = &state_map[representative];
        
        for symbol in &dfa.alphabet {
            let key = (representative.clone(), *symbol);
            if let Some(to_states) = dfa.transitions.get(&key) {
                if !to_states.is_empty() {
                    let to_state = to_states.iter().next().unwrap();
                    let new_to_state = &state_map[to_state];
                    min_dfa.add_transition(new_state, *symbol, new_to_state);
                }
            }
        }
    }
    
    min_dfa
}

/// 找出从初始状态可达的所有状态
fn find_reachable_states(dfa: &FiniteAutomaton) -> HashSet<String> {
    let mut reachable = HashSet::new();
    let mut stack = vec![dfa.initial_state.clone()];
    
    while let Some(state) = stack.pop() {
        if reachable.insert(state.clone()) {
            for symbol in &dfa.alphabet {
                let key = (state.clone(), *symbol);
                if let Some(to_states) = dfa.transitions.get(&key) {
                    for to in to_states {
                        if !reachable.contains(to) {
                            stack.push(to.clone());
                        }
                    }
                }
            }
        }
    }
    
    reachable
}

/// 移除不可达状态
fn remove_unreachable_states(dfa: &FiniteAutomaton, reachable: &HashSet<String>) -> FiniteAutomaton {
    let mut new_dfa = FiniteAutomaton::new(AutomatonType::DFA);
    
    // 复制字母表
    new_dfa.alphabet = dfa.alphabet.clone();
    
    // 添加可达状态
    for state in reachable {
        new_dfa.add_state(state);
        
        if dfa.accepting_states.contains(state) {
            new_dfa.add_accepting_state(state);
        }
    }
    
    // 设置初始状态
    new_dfa.set_initial_state(&dfa.initial_state);
    
    // 复制转移
    for ((from, symbol), to_states) in &dfa.transitions {
        if reachable.contains(from) {
            for to in to_states {
                if reachable.contains(to) {
                    new_dfa.add_transition(from, *symbol, to);
                }
            }
        }
    }
    
    new_dfa
}
```

## 5. 使用示例

以下是使用上述实现的示例代码：

```rust
fn main() -> Result<(), String> {
    // 创建一个右线性文法
    let mut grammar = RegularGrammar::new(GrammarType::RightLinear);
    grammar.add_production("S", "aA");
    grammar.add_production("S", "bS");
    grammar.add_production("A", "aA");
    grammar.add_production("A", "bB");
    grammar.add_production("B", "aS");
    grammar.add_production("B", "ε");
    
    println!("原始文法:");
    for (lhs, productions) in &grammar.productions {
        for rhs in productions {
            println!("{} -> {}", lhs, rhs);
        }
    }
    
    // 转换为NFA
    let nfa = right_linear_grammar_to_nfa(&grammar)?;
    
    println!("\n转换后的NFA:");
    println!("状态: {:?}", nfa.states);
    println!("初始状态: {}", nfa.initial_state);
    println!("接受状态: {:?}", nfa.accepting_states);
    println!("转移函数:");
    for ((from, symbol), to_states) in &nfa.transitions {
        for to in to_states {
            println!("{} --{}--> {}", from, symbol, to);
        }
    }
    
    // 将NFA转回文法
    let new_grammar = nfa_to_right_linear_grammar(&nfa);
    
    println!("\n从NFA转回的文法:");
    for (lhs, productions) in &new_grammar.productions {
        for rhs in productions {
            println!("{} -> {}", lhs, rhs);
        }
    }
    
    Ok(())
}
```

## 6. 完整示例输出

运行以上代码会得到如下输出：

```text
原始文法:
S -> aA
S -> bS
A -> aA
A -> bB
B -> aS
B -> ε

转换后的NFA:
状态: {"B", "qf", "S", "A"}
初始状态: S
接受状态: {"B", "qf"}
转移函数:
S --a--> A
S --b--> S
A --a--> A
A --b--> B
B --a--> S

从NFA转回的文法:
S -> aA
S -> bS
A -> aA
A -> bB
B -> aS
B -> ε
qf -> ε
```

## 7. 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_right_linear_grammar_to_nfa() {
        let mut grammar = RegularGrammar::new(GrammarType::RightLinear);
        grammar.add_production("S", "aA");
        grammar.add_production("S", "bS");
        grammar.add_production("A", "aA");
        grammar.add_production("A", "bB");
        grammar.add_production("B", "aS");
        grammar.add_production("B", "ε");

        let nfa = right_linear_grammar_to_nfa(&grammar).unwrap();
        
        assert!(nfa.states.contains("S"));
        assert!(nfa.states.contains("A"));
        assert!(nfa.states.contains("B"));
        assert!(nfa.states.contains("qf"));
        
        assert_eq!(nfa.initial_state, "S");
        assert!(nfa.accepting_states.contains("B"));
        assert!(nfa.accepting_states.contains("qf"));
        
        // 检查转移
        assert!(nfa.transitions.contains_key(&("S".to_string(), 'a')));
        let to_states = &nfa.transitions[&("S".to_string(), 'a')];
        assert!(to_states.contains("A"));
    }

    #[test]
    fn test_nfa_to_right_linear_grammar() {
        let mut nfa = FiniteAutomaton::new(AutomatonType::NFA);
        nfa.add_state("S");
        nfa.add_state("A");
        nfa.add_state("B");
        nfa.set_initial_state("S");
        nfa.add_accepting_state("B");
        
        nfa.add_transition("S", 'a', "A");
        nfa.add_transition("S", 'b', "S");
        nfa.add_transition("A", 'a', "A");
        nfa.add_transition("A", 'b', "B");
        nfa.add_transition("B", 'a', "S");
        
        let grammar = nfa_to_right_linear_grammar(&nfa);
        
        assert_eq!(grammar.start_symbol, "S");
        assert!(grammar.non_terminals.contains("S"));
        assert!(grammar.non_terminals.contains("A"));
        assert!(grammar.non_terminals.contains("B"));
        
        // 检查产生式
        assert!(grammar.productions["S"].contains(&"aA".to_string()));
        assert!(grammar.productions["S"].contains(&"bS".to_string()));
        assert!(grammar.productions["B"].contains(&"aS".to_string()));
        assert!(grammar.productions["B"].contains(&"ε".to_string()));
    }
}
```

这些代码展示了如何在Rust中实现正则文法和有限自动机之间的相互转换，以及DFA的最小化算法。
