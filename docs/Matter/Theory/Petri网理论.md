# Petri网理论 (Petri Net Theory)

## 概述

Petri网是一种用于描述和分析并发系统的数学建模工具，由Carl Adam Petri在1962年提出。Petri网特别适用于描述具有并发、同步、冲突和资源共享特性的系统。

## 基础概念

### 1. 基本Petri网

**定义**：
基本Petri网是一个三元组 N = (P, T, F)，其中：

- P 是库所（places）的有限集合
- T 是变迁（transitions）的有限集合
- F ⊆ (P × T) ∪ (T × P) 是流关系（flow relation）

**形式化表达**：

```rust
#[derive(Clone, Debug)]
struct PetriNet {
    places: HashSet<String>,
    transitions: HashSet<String>,
    flow_relation: HashSet<(String, String)>,
    initial_marking: HashMap<String, u32>
}

impl PetriNet {
    fn new() -> Self {
        PetriNet {
            places: HashSet::new(),
            transitions: HashSet::new(),
            flow_relation: HashSet::new(),
            initial_marking: HashMap::new()
        }
    }
    
    fn add_place(&mut self, place: String) {
        self.places.insert(place);
    }
    
    fn add_transition(&mut self, transition: String) {
        self.transitions.insert(transition);
    }
    
    fn add_flow(&mut self, from: String, to: String) {
        self.flow_relation.insert((from, to));
    }
    
    fn set_initial_marking(&mut self, place: String, tokens: u32) {
        self.initial_marking.insert(place, tokens);
    }
}
```

### 2. 标记和变迁规则

**定义**：

- 标记（Marking）是库所到非负整数的映射
- 变迁的使能条件：所有输入库所都有足够的令牌
- 变迁的激发：从输入库所移除令牌，向输出库所添加令牌

**形式化表达**：

```rust
#[derive(Clone, Debug)]
struct Marking {
    tokens: HashMap<String, u32>
}

impl Marking {
    fn new() -> Self {
        Marking {
            tokens: HashMap::new()
        }
    }
    
    fn get_tokens(&self, place: &str) -> u32 {
        *self.tokens.get(place).unwrap_or(&0)
    }
    
    fn set_tokens(&mut self, place: String, count: u32) {
        self.tokens.insert(place, count);
    }
    
    fn add_tokens(&mut self, place: &str, count: u32) {
        let current = self.get_tokens(place);
        self.tokens.insert(place.to_string(), current + count);
    }
    
    fn remove_tokens(&mut self, place: &str, count: u32) -> bool {
        let current = self.get_tokens(place);
        if current >= count {
            self.tokens.insert(place.to_string(), current - count);
            true
        } else {
            false
        }
    }
}

impl PetriNet {
    fn is_enabled(&self, transition: &str, marking: &Marking) -> bool {
        for (place, _) in self.get_input_places(transition) {
            if marking.get_tokens(place) == 0 {
                return false;
            }
        }
        true
    }
    
    fn fire(&self, transition: &str, marking: &mut Marking) -> bool {
        if !self.is_enabled(transition, marking) {
            return false;
        }
        
        // 移除输入令牌
        for (place, _) in self.get_input_places(transition) {
            marking.remove_tokens(place, 1);
        }
        
        // 添加输出令牌
        for (place, _) in self.get_output_places(transition) {
            marking.add_tokens(place, 1);
        }
        
        true
    }
    
    fn get_input_places(&self, transition: &str) -> Vec<(&String, &String)> {
        self.flow_relation.iter()
            .filter(|(from, to)| to == transition)
            .collect()
    }
    
    fn get_output_places(&self, transition: &str) -> Vec<(&String, &String)> {
        self.flow_relation.iter()
            .filter(|(from, to)| from == transition)
            .collect()
    }
}
```

## 高级Petri网

### 1. 有色Petri网 (Colored Petri Nets)

**定义**：
有色Petri网扩展了基本Petri网，允许令牌携带数据值，使模型更加紧凑和表达能力强。

**形式化表达**：

```rust
#[derive(Clone, Debug)]
struct ColoredToken {
    color: String,
    value: Value
}

#[derive(Clone, Debug)]
enum Value {
    Integer(i32),
    String(String),
    Boolean(bool),
    Tuple(Vec<Value>)
}

#[derive(Clone, Debug)]
struct ColoredPetriNet {
    places: HashSet<String>,
    transitions: HashSet<String>,
    flow_relation: HashMap<(String, String), ArcExpression>,
    initial_marking: HashMap<String, Vec<ColoredToken>>
}

#[derive(Clone, Debug)]
enum ArcExpression {
    Variable(String),
    Constant(Value),
    Tuple(Vec<ArcExpression>),
    Function(String, Vec<ArcExpression>)
}

impl ColoredPetriNet {
    fn is_enabled(&self, transition: &str, marking: &HashMap<String, Vec<ColoredToken>>) -> Vec<Binding> {
        let mut bindings = Vec::new();
        let input_arcs = self.get_input_arcs(transition);
        
        // 计算所有可能的绑定
        for arc in input_arcs {
            let place = &arc.0;
            let expression = &arc.1;
            let tokens = marking.get(place).unwrap_or(&Vec::new());
            
            for token in tokens {
                if let Some(binding) = self.evaluate_expression(expression, token) {
                    bindings.push(binding);
                }
            }
        }
        
        bindings
    }
    
    fn fire(&self, transition: &str, binding: &Binding, marking: &mut HashMap<String, Vec<ColoredToken>>) {
        // 移除输入令牌
        for (place, expression) in self.get_input_arcs(transition) {
            let tokens = marking.get_mut(place).unwrap();
            let token_to_remove = self.evaluate_expression(expression, binding);
            if let Some(token) = token_to_remove {
                tokens.retain(|t| t != &token);
            }
        }
        
        // 添加输出令牌
        for (place, expression) in self.get_output_arcs(transition) {
            let tokens = marking.entry(place.clone()).or_insert_with(Vec::new);
            let new_token = self.evaluate_expression(expression, binding);
            if let Some(token) = new_token {
                tokens.push(token);
            }
        }
    }
}
```

### 2. 时间Petri网 (Timed Petri Nets)

**定义**：
时间Petri网为变迁添加了时间约束，用于建模实时系统。

**形式化表达**：

```rust
#[derive(Clone, Debug)]
struct TimedPetriNet {
    places: HashSet<String>,
    transitions: HashSet<String>,
    flow_relation: HashSet<(String, String)>,
    timing_constraints: HashMap<String, TimeInterval>,
    initial_marking: HashMap<String, u32>
}

#[derive(Clone, Debug)]
struct TimeInterval {
    min_delay: f64,
    max_delay: f64
}

#[derive(Clone, Debug)]
struct TimedMarking {
    tokens: HashMap<String, u32>,
    transition_clocks: HashMap<String, f64>
}

impl TimedPetriNet {
    fn is_enabled(&self, transition: &str, marking: &TimedMarking) -> bool {
        // 检查基本使能条件
        if !self.basic_enabled(transition, marking) {
            return false;
        }
        
        // 检查时间约束
        if let Some(interval) = self.timing_constraints.get(transition) {
            if let Some(clock) = marking.transition_clocks.get(transition) {
                return *clock >= interval.min_delay && *clock <= interval.max_delay;
            }
        }
        
        true
    }
    
    fn fire(&self, transition: &str, marking: &mut TimedMarking) -> bool {
        if !self.is_enabled(transition, marking) {
            return false;
        }
        
        // 执行基本激发
        self.basic_fire(transition, marking);
        
        // 重置相关时钟
        self.reset_clocks(transition, marking);
        
        true
    }
    
    fn advance_time(&self, delta: f64, marking: &mut TimedMarking) {
        for (transition, clock) in &mut marking.transition_clocks {
            *clock += delta;
        }
    }
}
```

### 3. 随机Petri网 (Stochastic Petri Nets)

**定义**：
随机Petri网为变迁添加了随机延迟，用于性能分析和可靠性建模。

**形式化表达**：

```rust
#[derive(Clone, Debug)]
struct StochasticPetriNet {
    places: HashSet<String>,
    transitions: HashSet<String>,
    flow_relation: HashSet<(String, String)>,
    firing_rates: HashMap<String, f64>,
    initial_marking: HashMap<String, u32>
}

#[derive(Clone, Debug)]
struct StochasticMarking {
    tokens: HashMap<String, u32>,
    transition_timers: HashMap<String, f64>
}

impl StochasticPetriNet {
    fn next_event_time(&self, marking: &StochasticMarking) -> (String, f64) {
        let mut min_time = f64::INFINITY;
        let mut next_transition = String::new();
        
        for transition in &self.transitions {
            if self.is_enabled(transition, marking) {
                if let Some(rate) = self.firing_rates.get(transition) {
                    let delay = self.exponential_random(*rate);
                    if delay < min_time {
                        min_time = delay;
                        next_transition = transition.clone();
                    }
                }
            }
        }
        
        (next_transition, min_time)
    }
    
    fn exponential_random(&self, rate: f64) -> f64 {
        // 生成指数分布的随机数
        -(-1.0_f64.ln()) / rate
    }
    
    fn simulate(&self, duration: f64) -> Vec<Marking> {
        let mut marking = self.initial_marking.clone();
        let mut history = Vec::new();
        let mut current_time = 0.0;
        
        while current_time < duration {
            history.push(marking.clone());
            
            let (transition, delay) = self.next_event_time(&marking);
            current_time += delay;
            
            if current_time < duration {
                self.fire(&transition, &mut marking);
            }
        }
        
        history
    }
}
```

## 分析技术

### 1. 可达性分析

**定义**：
可达性分析确定从初始标记可以到达的所有标记。

**形式化表达**：

```rust
impl PetriNet {
    fn reachability_analysis(&self) -> HashSet<Marking> {
        let mut reachable = HashSet::new();
        let mut to_explore = Vec::new();
        
        let initial = Marking::from(&self.initial_marking);
        reachable.insert(initial.clone());
        to_explore.push(initial);
        
        while let Some(current_marking) = to_explore.pop() {
            for transition in &self.transitions {
                if self.is_enabled(transition, &current_marking) {
                    let mut new_marking = current_marking.clone();
                    self.fire(transition, &mut new_marking);
                    
                    if reachable.insert(new_marking.clone()) {
                        to_explore.push(new_marking);
                    }
                }
            }
        }
        
        reachable
    }
}
```

### 2. 不变性分析

**定义**：
不变性分析寻找在系统执行过程中保持不变的属性。

**形式化表达**：

```rust
#[derive(Clone, Debug)]
struct Invariant {
    places: Vec<String>,
    coefficients: Vec<i32>,
    constant: i32
}

impl PetriNet {
    fn find_p_invariants(&self) -> Vec<Invariant> {
        // 使用线性代数方法寻找P-不变性
        let incidence_matrix = self.build_incidence_matrix();
        let null_space = self.compute_null_space(&incidence_matrix);
        
        null_space.into_iter()
            .map(|vector| self.vector_to_invariant(vector))
            .collect()
    }
    
    fn find_t_invariants(&self) -> Vec<Invariant> {
        // 使用线性代数方法寻找T-不变性
        let incidence_matrix = self.build_incidence_matrix();
        let transposed = self.transpose_matrix(&incidence_matrix);
        let null_space = self.compute_null_space(&transposed);
        
        null_space.into_iter()
            .map(|vector| self.vector_to_invariant(vector))
            .collect()
    }
}
```

### 3. 死锁检测

**定义**：
死锁检测识别系统中可能导致死锁的状态。

**形式化表达**：

```rust
impl PetriNet {
    fn detect_deadlocks(&self) -> Vec<Marking> {
        let reachable = self.reachability_analysis();
        let mut deadlocks = Vec::new();
        
        for marking in reachable {
            if self.is_deadlock(&marking) {
                deadlocks.push(marking);
            }
        }
        
        deadlocks
    }
    
    fn is_deadlock(&self, marking: &Marking) -> bool {
        for transition in &self.transitions {
            if self.is_enabled(transition, marking) {
                return false;
            }
        }
        true
    }
}
```

## 应用领域

### 1. 并发系统建模

```rust
// 生产者-消费者系统
fn producer_consumer_system() -> PetriNet {
    let mut net = PetriNet::new();
    
    // 添加库所
    net.add_place("buffer_empty".to_string());
    net.add_place("buffer_full".to_string());
    net.add_place("producer_ready".to_string());
    net.add_place("consumer_ready".to_string());
    
    // 添加变迁
    net.add_transition("produce".to_string());
    net.add_transition("consume".to_string());
    
    // 添加流关系
    net.add_flow("buffer_empty".to_string(), "produce".to_string());
    net.add_flow("produce".to_string(), "buffer_full".to_string());
    net.add_flow("buffer_full".to_string(), "consume".to_string());
    net.add_flow("consume".to_string(), "buffer_empty".to_string());
    
    // 设置初始标记
    net.set_initial_marking("buffer_empty".to_string(), 1);
    net.set_initial_marking("producer_ready".to_string(), 1);
    net.set_initial_marking("consumer_ready".to_string(), 1);
    
    net
}
```

### 2. 工作流建模

```rust
// 简单工作流系统
fn workflow_system() -> PetriNet {
    let mut net = PetriNet::new();
    
    // 工作流状态
    net.add_place("start".to_string());
    net.add_place("task1_running".to_string());
    net.add_place("task1_completed".to_string());
    net.add_place("task2_running".to_string());
    net.add_place("task2_completed".to_string());
    net.add_place("end".to_string());
    
    // 工作流活动
    net.add_transition("start_task1".to_string());
    net.add_transition("complete_task1".to_string());
    net.add_transition("start_task2".to_string());
    net.add_transition("complete_task2".to_string());
    
    // 流关系
    net.add_flow("start".to_string(), "start_task1".to_string());
    net.add_flow("start_task1".to_string(), "task1_running".to_string());
    net.add_flow("task1_running".to_string(), "complete_task1".to_string());
    net.add_flow("complete_task1".to_string(), "task1_completed".to_string());
    net.add_flow("task1_completed".to_string(), "start_task2".to_string());
    net.add_flow("start_task2".to_string(), "task2_running".to_string());
    net.add_flow("task2_running".to_string(), "complete_task2".to_string());
    net.add_flow("complete_task2".to_string(), "task2_completed".to_string());
    net.add_flow("task2_completed".to_string(), "end".to_string());
    
    // 初始标记
    net.set_initial_marking("start".to_string(), 1);
    
    net
}
```

## 总结

Petri网理论为并发系统建模和分析提供了强大的工具：

1. **基础理论**：基本Petri网、标记、变迁规则
2. **高级扩展**：有色Petri网、时间Petri网、随机Petri网
3. **分析技术**：可达性分析、不变性分析、死锁检测
4. **应用领域**：并发系统、工作流、实时系统、性能分析

Petri网特别适合建模具有并发、同步和资源共享特性的系统，为系统设计和验证提供了形式化的方法。
