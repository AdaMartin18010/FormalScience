# 分布式工作流系统的理论基础与实践：形式化验证、组合模型与演化路径

```text
<think>
我需要重新生成一个更为深入的分析，关注以下几个方面：

1. 形式化验证 - 如何使用类型论和其他形式化方法验证分布式系统的正确性
2. 模型间的等价关系 - 不同系统模型间的映射和转换
3. 组合关系和演化路径 - 系统组件如何组合和随时间演化
4. 运行时策略调整 - 动态自适应执行机制
5. 一致性实现机制 - 从强一致性到最终一致性的实现和选择
6. 边缘云组合 - 如何结合边缘计算和云计算模式
7. 分布式监测 - 系统监控、可观测性和预测性维护

我会从这些视角重新组织内容，更多地关注理论模型和底层机制，提供更深入的代码示例，
特别是在形式化验证、一致性和边缘计算方面。
</think>
```

## 目录

- [分布式工作流系统的理论基础与实践：形式化验证、组合模型与演化路径](#分布式工作流系统的理论基础与实践形式化验证组合模型与演化路径)
  - [目录](#目录)
  - [引言](#引言)
  - [形式化基础与验证](#形式化基础与验证)
    - [类型理论基础](#类型理论基础)
    - [模型等价性](#模型等价性)
    - [时序逻辑验证](#时序逻辑验证)
    - [不变性与后置条件](#不变性与后置条件)
  - [系统模型与组合规则](#系统模型与组合规则)
    - [代数效应模型](#代数效应模型)
    - [组合规则形式化](#组合规则形式化)
    - [组合安全性证明](#组合安全性证明)
    - [对偶性与反模式](#对偶性与反模式)
  - [一致性模型谱系](#一致性模型谱系)
    - [线性一致性机制](#线性一致性机制)
    - [因果一致性模型](#因果一致性模型)
    - [混合一致性实现](#混合一致性实现)
    - [一致性升降级策略](#一致性升降级策略)
  - [边缘云组合架构](#边缘云组合架构)
    - [连续体计算模型](#连续体计算模型)
    - [边缘自主决策机制](#边缘自主决策机制)
    - [混合执行模式](#混合执行模式)
    - [容错与分区处理](#容错与分区处理)
  - [动态自适应运行时](#动态自适应运行时)
    - [自适应调度策略](#自适应调度策略)
    - [资源感知执行](#资源感知执行)
    - [负载均衡与迁移](#负载均衡与迁移)
    - [策略优化框架](#策略优化框架)
  - [系统演化框架](#系统演化框架)
    - [演化代数](#演化代数)
    - [渐进式类型演化](#渐进式类型演化)
    - [共变分离原则](#共变分离原则)
    - [无停机演化路径](#无停机演化路径)
  - [结论与未来方向](#结论与未来方向)
    - [系统演化与版本兼容性](#系统演化与版本兼容性)
    - [应用场景与未来研究方向](#应用场景与未来研究方向)
    - [系统架构图](#系统架构图)

## 引言

分布式工作流系统作为复杂分布式应用的核心组件，
不仅需要面对并发、分布式和容错等基本挑战，
更需要对形式化正确性、系统组合性、演化稳定性等理论和实践问题进行深入探讨。

本文从形式化验证、模型等价性、组合关系、一致性机制和边缘云协同等新视角，
重新审视分布式工作流系统的理论基础与实现策略，并基于Rust语言提供具体实现方案。

特别地，本文聚焦于如何通过形式验证技术保障系统正确性，
如何构建支持灵活组合且保持语义一致的子系统，
如何设计允许系统安全演化的路径，
以及如何在边缘-云混合环境中实现高效可靠的工作流执行。
通过这些探讨，我们旨在提供一个理论完备、实用高效的分布式工作流系统框架。

## 形式化基础与验证

### 类型理论基础

分布式系统的形式化验证可以建立在类型理论和程序逻辑的基础上。
通过依赖类型系统和线性类型，我们可以在编译时验证系统的关键安全属性。

```rust
// 依赖类型的模拟实现：工作流状态依赖
// 使用类型状态模式(typestate pattern)实现依赖类型的效果
pub struct Workflow<S: WorkflowState> {
    id: WorkflowId,
    definition: WorkflowDefinition,
    state: S,
    phantom: PhantomData<S>,
}

// 工作流状态特征
pub trait WorkflowState: private::Sealed {}

// 具体状态类型
pub struct Created;
pub struct Running;
pub struct Completed;
pub struct Failed;

impl WorkflowState for Created {}
impl WorkflowState for Running {}
impl WorkflowState for Completed {}
impl WorkflowState for Failed {}

// 私有模块防止外部实现特征
mod private {
    pub trait Sealed {}
    impl Sealed for super::Created {}
    impl Sealed for super::Running {}
    impl Sealed for super::Completed {}
    impl Sealed for super::Failed {}
}

// 状态转换仅在类型系统允许的路径上进行
impl Workflow<Created> {
    pub fn new(id: WorkflowId, definition: WorkflowDefinition) -> Self {
        Self {
            id,
            definition,
            state: Created,
            phantom: PhantomData,
        }
    }
    
    // 只有Created状态可以转换为Running
    pub fn start(self, input: Value) -> Result<Workflow<Running>, WorkflowError> {
        // 执行启动逻辑
        let running_state = Running;
        
        Ok(Workflow {
            id: self.id,
            definition: self.definition,
            state: running_state,
            phantom: PhantomData,
        })
    }
}

impl Workflow<Running> {
    // 只有Running状态可以转换为Completed或Failed
    pub fn complete(self, output: Value) -> Workflow<Completed> {
        Workflow {
            id: self.id,
            definition: self.definition,
            state: Completed,
            phantom: PhantomData,
        }
    }
    
    pub fn fail(self, error: WorkflowError) -> Workflow<Failed> {
        Workflow {
            id: self.id,
            definition: self.definition,
            state: Failed,
            phantom: PhantomData,
        }
    }
}
```

通过这种类型状态模式，我们确保了工作流状态转换的正确性和安全性。
例如，只有处于`Running`状态的工作流才能被完成或失败，直接通过类型系统阻止了无效状态转换。

### 模型等价性

在分布式系统中，不同抽象层次的模型之间存在等价关系。
通过建立这些等价关系，我们可以在不同层次验证系统属性。

```rust
// 不同抽象级别的工作流模型及其等价映射

// 高级模型：面向用户的工作流DSL
struct WorkflowDSL {
    tasks: Vec<TaskDefinition>,
    dependencies: Vec<(TaskId, TaskId)>,
    conditions: HashMap<TaskId, Condition>,
}

// 中级模型：基于事件的执行模型
struct EventBasedWorkflow {
    initial_events: Vec<Event>,
    event_handlers: HashMap<EventType, Vec<EventHandler>>,
    completion_conditions: Vec<CompletionCondition>,
}

// 低级模型：状态机表示
struct StateMachineWorkflow {
    states: Vec<State>,
    transitions: Vec<Transition>,
    initial_state: StateId,
    final_states: Vec<StateId>,
}

// 模型映射和等价性证明
trait ModelMapping<Source, Target> {
    fn map(source: &Source) -> Target;
    fn is_equivalent(source: &Source, target: &Target) -> bool;
}

struct DSLToEventMapping;

impl ModelMapping<WorkflowDSL, EventBasedWorkflow> for DSLToEventMapping {
    fn map(dsl: &WorkflowDSL) -> EventBasedWorkflow {
        // 将DSL模型映射到事件模型
        let mut workflow = EventBasedWorkflow {
            initial_events: Vec::new(),
            event_handlers: HashMap::new(),
            completion_conditions: Vec::new(),
        };
        
        // 创建初始事件
        for task in dsl.tasks.iter().filter(|t| !has_dependencies(t.id, &dsl.dependencies)) {
            workflow.initial_events.push(Event::TaskReady(task.id));
        }
        
        // 创建事件处理器
        for task in &dsl.tasks {
            let mut handler = EventHandler::new(task.id);
            
            // 添加完成后触发的后续任务
            for (from, to) in dsl.dependencies.iter().filter(|(f, _)| *f == task.id) {
                handler.add_effect(Effect::TriggerEvent(Event::TaskReady(*to)));
            }
            
            workflow.event_handlers.insert(
                EventType::TaskCompleted(task.id),
                vec![handler]
            );
        }
        
        // 添加完成条件
        let final_tasks: Vec<_> = dsl.tasks.iter()
            .filter(|t| !dsl.dependencies.iter().any(|(_, to)| *to == t.id))
            .map(|t| t.id)
            .collect();
            
        workflow.completion_conditions.push(
            CompletionCondition::AllTasksCompleted(final_tasks)
        );
        
        workflow
    }
    
    fn is_equivalent(dsl: &WorkflowDSL, event_based: &EventBasedWorkflow) -> bool {
        // 验证两个模型是否等价(简化版)
        
        // 1. 检查所有无依赖的任务都成为初始事件
        let initial_tasks: HashSet<_> = dsl.tasks.iter()
            .filter(|t| !has_dependencies(t.id, &dsl.dependencies))
            .map(|t| t.id)
            .collect();
            
        let initial_events: HashSet<_> = event_based.initial_events.iter()
            .filter_map(|e| if let Event::TaskReady(id) = e { Some(*id) } else { None })
            .collect();
            
        if initial_tasks != initial_events {
            return false;
        }
        
        // 2. 检查每个任务完成后的触发关系是否保持
        for (from, to) in &dsl.dependencies {
            let triggers_to = if let Some(handlers) = event_based.event_handlers.get(&EventType::TaskCompleted(*from)) {
                handlers.iter().any(|h| h.effects.iter().any(|e| 
                    matches!(e, Effect::TriggerEvent(Event::TaskReady(id)) if *id == *to)
                ))
            } else {
                false
            };
            
            if !triggers_to {
                return false;
            }
        }
        
        // 3. 检查完成条件
        let final_tasks: HashSet<_> = dsl.tasks.iter()
            .filter(|t| !dsl.dependencies.iter().any(|(_, to)| *to == t.id))
            .map(|t| t.id)
            .collect();
            
        let has_proper_completion = event_based.completion_conditions.iter().any(|c| {
            matches!(c, CompletionCondition::AllTasksCompleted(tasks) if tasks.iter().cloned().collect::<HashSet<_>>() == final_tasks)
        });
        
        if !has_proper_completion {
            return false;
        }
        
        true
    }
}

fn has_dependencies(task_id: TaskId, dependencies: &Vec<(TaskId, TaskId)>) -> bool {
    dependencies.iter().any(|(_, to)| *to == task_id)
}
```

此代码定义了不同抽象级别的工作流模型（DSL、事件模型、状态机）及其映射关系，
并提供了验证模型等价性的方法。
这种形式化的映射关系使我们能够确保模型转换的正确性，并在不同抽象级别上推理系统行为。

### 时序逻辑验证

时序逻辑是形式化验证分布式系统的强大工具，可以表达系统随时间演化的属性。

```rust
// 时序逻辑属性验证框架
pub enum TemporalFormula<State> {
    // 原子命题
    Atom(Box<dyn Fn(&State) -> bool>),
    
    // 逻辑运算符
    Not(Box<TemporalFormula<State>>),
    And(Box<TemporalFormula<State>>, Box<TemporalFormula<State>>),
    Or(Box<TemporalFormula<State>>, Box<TemporalFormula<State>>),
    Implies(Box<TemporalFormula<State>>, Box<TemporalFormula<State>>),
    
    // 时序运算符
    Always(Box<TemporalFormula<State>>),          // □φ (全局)
    Eventually(Box<TemporalFormula<State>>),      // ◇φ (最终)
    Next(Box<TemporalFormula<State>>),            // ○φ (下一步)
    Until(Box<TemporalFormula<State>>, Box<TemporalFormula<State>>), // φ U ψ (直到)
}

impl<State: Clone> TemporalFormula<State> {
    // 创建原子命题
    pub fn atom<F>(predicate: F) -> Self 
    where 
        F: Fn(&State) -> bool + 'static 
    {
        TemporalFormula::Atom(Box::new(predicate))
    }
    
    // 逻辑否定
    pub fn not(self) -> Self {
        TemporalFormula::Not(Box::new(self))
    }
    
    // 逻辑与
    pub fn and(self, other: Self) -> Self {
        TemporalFormula::And(Box::new(self), Box::new(other))
    }
    
    // 逻辑或
    pub fn or(self, other: Self) -> Self {
        TemporalFormula::Or(Box::new(self), Box::new(other))
    }
    
    // 逻辑蕴含
    pub fn implies(self, other: Self) -> Self {
        TemporalFormula::Implies(Box::new(self), Box::new(other))
    }
    
    // 全局性质
    pub fn always(self) -> Self {
        TemporalFormula::Always(Box::new(self))
    }
    
    // 最终性质
    pub fn eventually(self) -> Self {
        TemporalFormula::Eventually(Box::new(self))
    }
    
    // 下一步性质
    pub fn next(self) -> Self {
        TemporalFormula::Next(Box::new(self))
    }
    
    // 直到性质
    pub fn until(self, other: Self) -> Self {
        TemporalFormula::Until(Box::new(self), Box::new(other))
    }
    
    // 评估公式在给定状态序列上的真值
    pub fn evaluate(&self, trace: &[State]) -> bool {
        match self {
            TemporalFormula::Atom(pred) => {
                if trace.is_empty() {
                    false
                } else {
                    pred(&trace[0])
                }
            },
            TemporalFormula::Not(f) => !f.evaluate(trace),
            TemporalFormula::And(f1, f2) => f1.evaluate(trace) && f2.evaluate(trace),
            TemporalFormula::Or(f1, f2) => f1.evaluate(trace) || f2.evaluate(trace),
            TemporalFormula::Implies(f1, f2) => !f1.evaluate(trace) || f2.evaluate(trace),
            TemporalFormula::Always(f) => {
                // □φ: 对所有future states，φ都成立
                (0..trace.len()).all(|i| f.evaluate(&trace[i..]))
            },
            TemporalFormula::Eventually(f) => {
                // ◇φ: 存在future state，φ成立
                (0..trace.len()).any(|i| f.evaluate(&trace[i..]))
            },
            TemporalFormula::Next(f) => {
                // ○φ: 下一个状态φ成立
                trace.len() > 1 && f.evaluate(&trace[1..])
            },
            TemporalFormula::Until(f1, f2) => {
                // φ U ψ: φ成立直到ψ成立
                (0..trace.len()).any(|j| {
                    f2.evaluate(&trace[j..]) && 
                    (0..j).all(|i| f1.evaluate(&trace[i..]))
                })
            },
        }
    }
}

// 工作流安全性属性示例
fn verify_workflow_safety<S: Clone>(workflow: &Workflow<S>, trace_generator: &TraceGenerator<S>) -> bool {
    // 定义工作流必须满足的LTL属性
    
    // 属性1: 任何启动的工作流最终会完成或失败
    let prop1 = TemporalFormula::atom(|state: &WorkflowState| 
        state.status == WorkflowStatus::Running
    ).implies(
        TemporalFormula::atom(|state: &WorkflowState| 
            state.status == WorkflowStatus::Completed || 
            state.status == WorkflowStatus::Failed
        ).eventually()
    );
    
    // 属性2: 工作流完成后状态不再变化
    let prop2 = TemporalFormula::atom(|state: &WorkflowState| 
        state.status == WorkflowStatus::Completed
    ).implies(
        TemporalFormula::atom(|state: &WorkflowState| 
            state.status == WorkflowStatus::Completed
        ).always()
    );
    
    // 属性3: 任务只能在其所有依赖完成后执行
    let prop3 = TemporalFormula::atom(|state: &WorkflowState| {
        for task in &state.running_tasks {
            for dep_id in workflow.get_task_dependencies(task.id) {
                if !state.completed_tasks.contains(&dep_id) {
                    return false;
                }
            }
        }
        true
    }).always();
    
    // 生成执行轨迹并验证属性
    let traces = trace_generator.generate_traces(workflow);
    
    for trace in traces {
        if !prop1.evaluate(&trace) || !prop2.evaluate(&trace) || !prop3.evaluate(&trace) {
            return false;
        }
    }
    
    true
}
```

这段代码定义了一个时序逻辑公式框架，能够表达和验证工作流系统的时态属性，如"任何启动的工作流最终会完成或失败"和"工作流完成后状态不再变化"等。这种形式化验证方法可以捕捉到传统测试难以发现的微妙时序问题。

### 不变性与后置条件

通过不变性和后置条件，我们可以形式化地验证系统状态的正确性。

```rust
// 不变性与后置条件验证
pub trait Invariant<S> {
    fn check(&self, state: &S) -> bool;
    fn description(&self) -> &str;
}

pub trait Postcondition<S, A, R> {
    fn check(&self, pre_state: &S, action: &A, post_state: &S, result: &R) -> bool;
    fn description(&self) -> &str;
}

// 工作流系统不变性检查器
pub struct WorkflowInvariantChecker<S> {
    invariants: Vec<Box<dyn Invariant<S>>>,
}

impl<S> WorkflowInvariantChecker<S> {
    pub fn new() -> Self {
        Self { invariants: Vec::new() }
    }
    
    pub fn add_invariant<I: Invariant<S> + 'static>(&mut self, invariant: I) {
        self.invariants.push(Box::new(invariant));
    }
    
    pub fn check_all(&self, state: &S) -> Vec<&str> {
        self.invariants.iter()
            .filter(|inv| !inv.check(state))
            .map(|inv| inv.description())
            .collect()
    }
}

// 系统状态转换验证器
pub struct StateTransitionVerifier<S, A, R> {
    postconditions: HashMap<TypeId, Vec<Box<dyn Postcondition<S, A, R>>>>,
}

impl<S, A: 'static, R> StateTransitionVerifier<S, A, R> {
    pub fn new() -> Self {
        Self { postconditions: HashMap::new() }
    }
    
    pub fn add_postcondition<T: 'static, P: Postcondition<S, A, R> + 'static>(&mut self, postcondition: P) {
        let type_id = TypeId::of::<T>();
        self.postconditions.entry(type_id)
            .or_insert_with(Vec::new)
            .push(Box::new(postcondition));
    }
    
    pub fn verify_transition<T: 'static>(&self, pre_state: &S, action: &A, post_state: &S, result: &R) -> Vec<&str> {
        let type_id = TypeId::of::<T>();
        
        if let Some(conditions) = self.postconditions.get(&type_id) {
            conditions.iter()
                .filter(|post| !post.check(pre_state, action, post_state, result))
                .map(|post| post.description())
                .collect()
        } else {
            Vec::new()
        }
    }
}

// 工作流不变性示例
struct NoCircularDependency;

impl Invariant<WorkflowDefinition> for NoCircularDependency {
    fn check(&self, workflow: &WorkflowDefinition) -> bool {
        // 使用深度优先搜索检测依赖图中的环
        let mut visited = HashSet::new();
        let mut path = HashSet::new();
        
        for task_id in workflow.tasks.keys() {
            if !visited.contains(task_id) {
                if has_cycle(task_id, workflow, &mut visited, &mut path) {
                    return false;
                }
            }
        }
        
        true
    }
    
    fn description(&self) -> &str {
        "工作流不能包含循环依赖"
    }
}

fn has_cycle(
    task_id: &TaskId, 
    workflow: &WorkflowDefinition,
    visited: &mut HashSet<TaskId>,
    path: &mut HashSet<TaskId>
) -> bool {
    visited.insert(task_id.clone());
    path.insert(task_id.clone());
    
    if let Some(deps) = workflow.dependencies.get(task_id) {
        for dep in deps {
            if !visited.contains(dep) {
                if has_cycle(dep, workflow, visited, path) {
                    return true;
                }
            } else if path.contains(dep) {
                return true;
            }
        }
    }
    
    path.remove(task_id);
    false
}

// 工作流后置条件示例
struct TaskCompletionPostcondition;

impl Postcondition<WorkflowState, CompleteTaskAction, TaskResult> for TaskCompletionPostcondition {
    fn check(&self, pre_state: &WorkflowState, action: &CompleteTaskAction, post_state: &WorkflowState, result: &TaskResult) -> bool {
        // 验证任务完成后的状态一致性
        
        // 1. 任务应该从运行中任务列表移到已完成列表
        let task_moved = !post_state.running_tasks.contains(&action.task_id) && 
                        post_state.completed_tasks.contains(&action.task_id);
                        
        // 2. 任务的所有依赖任务应该被激活（如果它们的所有依赖都完成了）
        let dependent_tasks_activated = workflow_definition.get_dependent_tasks(&action.task_id)
            .into_iter()
            .all(|dep_task_id| {
                // 如果dep_task的所有依赖都已完成，它应该在运行中任务列表
                let all_deps_completed = workflow_definition.get_task_dependencies(&dep_task_id)
                    .into_iter()
                    .all(|dep| post_state.completed_tasks.contains(&dep));
                    
                !all_deps_completed || post_state.running_tasks.contains(&dep_task_id)
            });
            
        task_moved && dependent_tasks_activated
    }
    
    fn description(&self) -> &str {
        "任务完成后应从运行中列表移至已完成列表，且所有依赖已满足的下游任务应被激活"
    }
}
```

这段代码展示了如何使用不变性和后置条件来验证工作流系统的关键属性，如依赖无环和状态转换的正确性。通过这些形式化验证技术，我们可以在系统设计和实现阶段捕获潜在的逻辑错误。

## 系统模型与组合规则

### 代数效应模型

代数效应提供了一种将纯函数式编程与副作用分离的方法，特别适合建模工作流中的异步操作和错误处理。

```rust
// 代数效应模型实现
pub trait Effect {
    type Output;
}

// 异步执行效应
pub struct Async<F> {
    future: F,
}

// 错误处理效应
pub struct Catch<E> {
    _marker: PhantomData<E>,
}

// 状态读写效应
pub struct State<S> {
    _marker: PhantomData<S>,
}

// 工作流引擎的代数效应处理器
pub struct EffectHandler {
    async_runtime: AsyncRuntime,
    state_store: Box<dyn StateStore>,
    error_handlers: HashMap<TypeId, Box<dyn ErrorHandler>>,
}

impl EffectHandler {
    pub fn handle<E: Effect>(&self, effect: E) -> Result<E::Output, HandlerError> {
        // 根据效应类型分发到不同的处理器
        self.dispatch_effect(effect)
    }
    
    fn dispatch_effect<E: Effect>(&self, effect: E) -> Result<E::Output, HandlerError> {
        let type_id = TypeId::of::<E>();
        
        if type_id == TypeId::of::<Async<BoxFuture<'static, Result<(), WorkflowError>>>>() {
            // 处理异步效应
            self.handle_async(effect)
        } else if type_id == TypeId::of::<State<WorkflowData>>() {
            // 处理状态效应
            self.handle_state(effect)
        } else if type_id == TypeId::of::<Catch<WorkflowError>>() {
            // 处理错误处理效应
            self.handle_error(effect)
        } else {
            Err(HandlerError::UnsupportedEffect)
        }
    }
    
    // 处理异步效应
    fn handle_async<F>(&self, effect: Async<F>) -> Result<F::Output, HandlerError>
    where
        F: Future<Output = Result<(), WorkflowError>> + 'static,
    {
        // 将Future提交到异步运行时
        self.async_runtime.spawn(effect.future)
    }
    
    // 处理状态效应
    fn handle_state<S>(&self, effect: State<S>) -> Result<S::Output, HandlerError>
    where
        S: StateEffect,
    {
        match effect {
            State::Get => {
                let state = self.state_store.get(&effect.key)?;
                Ok(state)
            },
            State::Put { key, value } => {
                self.state_store.put(&key, &value)?;
                Ok(())
            },
        }
    }
    
    // 处理错误效应
    fn handle_error<E>(&self, effect: Catch<E>) -> Result<E::Output, HandlerError>
    where
        E: Error + 'static,
    {
        // 查找合适的错误处理器
        let type_id = TypeId::of::<E>();
        
        if let Some(handler) = self.error_handlers.get(&type_id) {
            handler.handle_error(&*effect.error as &dyn Error)
        } else {
            Err(HandlerError::NoErrorHandler)
        }
    }
}

// 表示含有效应的工作流操作
pub struct WorkflowOperation<T, E> {
    perform: Box<dyn FnOnce(&mut EffectHandler) -> Result<T, E>>,
}

impl<T, E> WorkflowOperation<T, E> {
    pub fn new<F>(f: F) -> Self
    where
        F: FnOnce(&mut EffectHandler) -> Result<T, E> + 'static,
    {
        Self {
            perform: Box::new(f),
        }
    }
    
    pub fn map<U, F>(self, f: F) -> WorkflowOperation<U, E>
    where
        F: FnOnce(T) -> U + 'static,
    {
        WorkflowOperation::new(move |handler| {
            let result = (self.perform)(handler)?;
            Ok(f(result))
        })
    }
    
    pub fn and_then<U, F>(self, f: F) -> WorkflowOperation<U, E>
    where
        F: FnOnce(T) -> WorkflowOperation<U, E> + 'static,
    {
        WorkflowOperation::new(move |handler| {
            let result = (self.perform)(handler)?;
            let next_op = f(result);
            (next_op.perform)(handler)
        })
    }
    
    pub fn execute(self, handler: &mut EffectHandler) -> Result<T, E> {
        (self.perform)(handler)
    }
}

// 异步任务操作示例
fn async_task<F, T>(future: F) -> WorkflowOperation<T, WorkflowError>
where
    F: Future<Output = Result<T, WorkflowError>> + 'static,
{
    WorkflowOperation::new(move |handler| {
        let effect = Async { future: Box::pin(future) };
        handler.handle(effect).map_err(|e| WorkflowError::HandlerError(e.to_string()))
    })
}

// 状态操作示例
fn get_state<T: DeserializeOwned>(key: String) -> WorkflowOperation<Option<T>, WorkflowError> {
    WorkflowOperation::new(move |handler| {
        let effect = State::Get { key };
        handler.handle(effect)
            .map_err(|e| WorkflowError::HandlerError(e.to_string()))
    })
}

fn put_state<T: Serialize>(key: String, value: T) -> WorkflowOperation<(), WorkflowError> {
    WorkflowOperation::new(move |handler| {
        let serialized = serde_json::to_vec(&value)
            .map_err(|e| WorkflowError::SerializationError(e.to_string()))?;
            
        let effect = State::Put { key, value: serialized };
        handler.handle(effect)
            .map_err(|e| WorkflowError::HandlerError(e.to_string()))
    })
}

// 组合工作流操作示例
fn process_order(order_id: String) -> WorkflowOperation<OrderResult, WorkflowError> {
    // 1. 获取订单数据
    get_state::<Order>(format!("order:{}", order_id))
        .and_then(move |maybe_order| {
            let order = maybe_order.ok_or(WorkflowError::NotFound(format!("Order {}", order_id)))?;
            
            // 2. 处理支付
            process_payment(order.payment_details)
                .and_then(move |payment_result| {
                    // 3. 更新订单状态
                    let updated_order = Order {
                        id: order.id,
                        status: if payment_result.success { "paid" } else { "payment_failed" },
                        ..order
                    };
                    
                    put_state(format!("order:{}", order_id), updated_order)
                        .map(move |_| OrderResult {
                            order_id: order_id,
                            status: updated_order.status.to_string(),
                            payment_id: payment_result.transaction_id,
                        })
                })
        })
}
```

这段代码展示了如何使用代数效应模型设计工作流系统，将副作用（异步、状态管理、错误处理）与纯逻辑分离。这种设计模式使工作流操作更易于组合和测试，同时保持了良好的抽象和分离关注点。

### 组合规则形式化

工作流组件的组合规则可以形式化为一组代数定律，确保组合的正确性和一致性。

```rust
// 工作流组合规则形式化

// 任务抽象
trait Task<In, Out> {
    fn execute(&self, input: In) -> WorkflowResult<Out>;
    fn name(&self) -> &str;
}

// 工作流组合子
enum WorkflowCombinator<A, B, C, D> {
    // 顺序组合: A -> B
    Sequence(A, B),
    
    // 并行组合: (A, B) -> (C, D)
    Parallel(A, B),
    
    // 选择组合: either A or B
    Choice(A, B),
    
    // 循环组合: repeat A until condition
    Loop(A, Box<dyn Fn(&C) -> bool>),
}

// 组合规则验证器
struct CompositionVerifier;

impl CompositionVerifier {
    // 验证顺序组合的结合律: (A >>> B) >>> C = A >>> (B >>> C)
    fn verify_sequence_associativity<A, B, C, In, Mid1, Mid2, Out>(
        a: &A, b: &B, c: &C
    ) -> bool
    where
        A: Task<In, Mid1>,
        B: Task<Mid1, Mid2>,
        C: Task<Mid2, Out>,
    {
        true  // 在实际实现中，这里会通过形式化证明验证该属性
    }
    
    // 验证并行组合的交换律: A ||| B = B ||| A
    fn verify_parallel_commutativity<A, B, InA, InB, OutA, OutB>(
        a: &A, b: &B
    ) -> bool
    where
        A: Task<InA, OutA>,
        B: Task<InB, OutB>,
    {
        true  // 在实际实现中，这里会通过形式化证明验证该属性
    }
    
    // 验证选择组合的分配律: (A + B) >>> C = (A >>> C) + (B >>> C)
    fn verify_choice_distributivity<A, B, C, InA, InB, MidA, MidB, Out>(
        a: &A, b: &B, c: &C
    ) -> bool
    where
        A: Task<InA, MidA>,
        B: Task<InB, MidB>,
        C: Task<MidA, Out>, // 假设MidA和MidB是相同类型
    {
        true  // 在实际实现中，这里会通过形式化证明验证该属性
    }
}

// 工作流组合器
struct WorkflowComposer;

impl WorkflowComposer {
    // 顺序组合
    fn sequence<A, B, In, Mid, Out>(a: A, b: B) -> impl Task<In, Out>
    where
        A: Task<In, Mid>,
        B: Task<Mid, Out>,
    {
        struct SequenceTask<A, B, In, Mid, Out> {
            first: A,
            second: B,
            _phantom: PhantomData<(In, Mid, Out)>,
        }
        
        impl<A, B, In, Mid, Out> Task<In, Out> for SequenceTask<A, B, In, Mid, Out>
        where
            A: Task<In, Mid>,
            B: Task<Mid, Out>,
        {
            fn execute(&self, input: In) -> WorkflowResult<Out> {
                let mid_result = self.first.execute(input)?;
                self.second.execute(mid_result)
            }
            
            fn name(&self) -> &str {
                "sequence"
            }
        }
        
        SequenceTask {
            first: a,
            second: b,
            _phantom: PhantomData,
        }
    }
    
    // 并行组合
    fn parallel<A, B, InA, InB, OutA, OutB>(a: A, b: B) -> impl Task<(InA, InB), (OutA, OutB)>
    where
        A: Task<InA, OutA> + Send + 'static,
        B: Task<InB, OutB> + Send + 'static,
        InA: Send + 'static,
        InB: Send + 'static,
        OutA: Send + 'static,
        OutB: Send + 'static,
    {
        struct ParallelTask<A, B, InA, InB, OutA, OutB> {
            left: A,
            right: B,
            _phantom: PhantomData<(InA, InB, OutA, OutB)>,
        }
        
        impl<A, B, InA, InB, OutA, OutB> Task<(InA, InB), (OutA, OutB)> 
            for ParallelTask<A, B, InA, InB, OutA, OutB>
        where
            A: Task<InA, OutA> + Send + 'static,
            B: Task<InB, OutB> + Send + 'static,
            InA: Send + 'static,
            InB: Send + 'static,
            OutA: Send + 'static,
            OutB: Send + 'static,
        {
            fn execute(&self, input: (InA, InB)) -> WorkflowResult<(OutA, OutB)> {
                let (in_a, in_b) = input;
                let a = self.left.clone();
                let b = self.right.clone();
                
                // 并行执行两个任务
                let handle_a = std::thread::spawn(move || a.execute(in_a));
                let handle_b = std::thread::spawn(move || b.execute(in_b));
                
                // 等待两个任务完成
                let result_a = handle_a.join().unwrap()?;
                let result_b = handle_b.join().unwrap()?;
                
                Ok((result_a, result_b))
            }
            
            fn name(&self) -> &str {
                "parallel"
            }
        }
        
        ParallelTask {
            left: a,
            right: b,
            _phantom: PhantomData,
        }
    }
    
    // 选择组合
    fn choice<A, B, In, Out>(a: A, b: B, predicate: impl Fn(&In) -> bool + 'static) -> impl Task<In, Out>
    where
        A: Task<In, Out>,
        B: Task<In, Out>,
    {
        struct ChoiceTask<A, B, In, Out, P> {
            left: A,
            right: B,
            predicate: P,
            _phantom: PhantomData<(In, Out)>,
        }
        
        impl<A, B, In, Out, P> Task<In, Out> for ChoiceTask<A, B, In, Out, P>
        where
            A: Task<In, Out>,
            B: Task<In, Out>,
            P: Fn(&In) -> bool,
        {
            fn execute(&self, input: In) -> WorkflowResult<Out> {
                if (self.predicate)(&input) {
                    self.left.execute(input)
                } else {
                    self.right.execute(input)
                }
            }
            
            fn name(&self) -> &str {
                "choice"
            }
        }
        
        ChoiceTask {
            left: a,
            right: b,
            predicate,
            _phantom: PhantomData,
        }
    }
    
    // 循环组合
    fn loop_until<A, In, Out>(a: A, condition: impl Fn(&Out) -> bool + 'static) -> impl Task<In, Out>
    where
        A: Task<In, Out> + Clone,
        In: Clone + From<Out>,
    {
        struct LoopTask<A, In, Out, C> {
            task: A,
            condition: C,
            _phantom: PhantomData<(In, Out)>,
        }
        
        impl<A, In, Out, C> Task<In, Out> for LoopTask<A, In, Out, C>
        where
            A: Task<In, Out> + Clone,
            In: Clone + From<Out>,
            C: Fn(&Out) -> bool,
        {
            fn execute(&self, input: In) -> WorkflowResult<Out> {
                let mut current_input = input;
                loop {
                    let result = self.task.execute(current_input.clone())?;
                    if (self.condition)(&result) {
                        return Ok(result);
                    }
                    current_input = In::from(result);
                }
            }
            
            fn name(&self) -> &str {
                "loop"
            }
        }
        
        LoopTask {
            task: a,
            condition,
            _phantom: PhantomData,
        }
    }
}

// 组合律可证明性验证
fn verify_composition_laws() -> bool {
    // 此函数实际上会构建形式化证明，验证各种组合规则的代数律
    
    // 验证结合律: (A >>> B) >>> C = A >>> (B >>> C)
    let task_a = /* 任务A */;
    let task_b = /* 任务B */;
    let task_c = /* 任务C */;
    
    let associativity_holds = CompositionVerifier::verify_sequence_associativity(&task_a, &task_b, &task_c);
    
    // 验证交换律: A ||| B = B ||| A
    let commutativity_holds = CompositionVerifier::verify_parallel_commutativity(&task_a, &task_b);
    
    // 验证分配律: (A + B) >>> C = (A >>> C) + (B >>> C)
    let distributivity_holds = CompositionVerifier::verify_choice_distributivity(&task_a, &task_b, &task_c);
    
    associativity_holds && commutativity_holds && distributivity_holds
}
```

### 组合安全性证明

基于类型系统的组合安全性证明可以确保工作流组合在语法上和语义上都是正确的。

```rust
// 组合安全性证明
// 通过依赖类型系统和线性类型确保工作流组合的安全性

// 资源类型（使用线性类型模拟）
pub struct Resource<T>(T);

impl<T> Resource<T> {
    // 创建新资源
    pub fn new(value: T) -> Self {
        Resource(value)
    }
    
    // 消费资源并返回内部值
    pub fn consume(self) -> T {
        self.0
    }
}

// 工作流安全性证明框架
pub trait SafetyProof {
    type PreCondition;
    type PostCondition;
    
    fn prove(&self) -> bool;
    fn pre_condition(&self) -> Self::PreCondition;
    fn post_condition(&self) -> Self::PostCondition;
}

// 组合工作流的安全性证明
pub struct SequentialCompositionProof<P1, P2>
where
    P1: SafetyProof,
    P2: SafetyProof,
{
    proof1: P1,
    proof2: P2,
    // 证明P1的后置条件蕴含P2的前置条件
    implication: Box<dyn Fn(P1::PostCondition) -> Option<P2::PreCondition>>,
}

impl<P1, P2> SafetyProof for SequentialCompositionProof<P1, P2>
where
    P1: SafetyProof,
    P2: SafetyProof,
{
    type PreCondition = P1::PreCondition;
    type PostCondition = P2::PostCondition;
    
    fn prove(&self) -> bool {
        // 两个子证明都成立
        if !self.proof1.prove() || !self.proof2.prove() {
            return false;
        }
        
        // P1的后置条件必须能够推导出P2的前置条件
        (self.implication)(self.proof1.post_condition()).is_some()
    }
    
    fn pre_condition(&self) -> Self::PreCondition {
        self.proof1.pre_condition()
    }
    
    fn post_condition(&self) -> Self::PostCondition {
        self.proof2.post_condition()
    }
}

// 并行组合工作流的安全性证明
pub struct ParallelCompositionProof<P1, P2>
where
    P1: SafetyProof,
    P2: SafetyProof,
{
    proof1: P1,
    proof2: P2,
    // 证明两个工作流可以安全并行执行（没有资源冲突）
    no_conflict: Box<dyn Fn(&P1::PreCondition, &P2::PreCondition) -> bool>,
}

impl<P1, P2> SafetyProof for ParallelCompositionProof<P1, P2>
where
    P1: SafetyProof,
    P2: SafetyProof,
{
    type PreCondition = (P1::PreCondition, P2::PreCondition);
    type PostCondition = (P1::PostCondition, P2::PostCondition);
    
    fn prove(&self) -> bool {
        // 两个子证明都成立
        if !self.proof1.prove() || !self.proof2.prove() {
            return false;
        }
        
        // 必须没有资源冲突
        (self.no_conflict)(&self.proof1.pre_condition(), &self.proof2.pre_condition())
    }
    
    fn pre_condition(&self) -> Self::PreCondition {
        (self.proof1.pre_condition(), self.proof2.pre_condition())
    }
    
    fn post_condition(&self) -> Self::PostCondition {
        (self.proof1.post_condition(), self.proof2.post_condition())
    }
}

// 安全工作流示例
pub struct SafeWorkflow<P: SafetyProof, I, O> {
    workflow: Box<dyn Fn(Resource<I>) -> Resource<O>>,
    safety_proof: P,
}

impl<P: SafetyProof, I, O> SafeWorkflow<P, I, O> {
    pub fn new<F>(workflow: F, proof: P) -> Self
    where
        F: Fn(Resource<I>) -> Resource<O> + 'static,
    {
        SafeWorkflow {
            workflow: Box::new(workflow),
            safety_proof: proof,
        }
    }
    
    pub fn execute(&self, input: Resource<I>) -> Resource<O> {
        // 执行前验证安全性证明
        assert!(self.safety_proof.prove(), "安全性证明失败");
        (self.workflow)(input)
    }
    
    // 顺序组合安全工作流
    pub fn then<P2, O2>(self, next: SafeWorkflow<P2, O, O2>) -> SafeWorkflow<SequentialCompositionProof<P, P2>, I, O2>
    where
        P2: SafetyProof,
    {
        let proof = SequentialCompositionProof {
            proof1: self.safety_proof,
            proof2: next.safety_proof,
            implication: Box::new(|_| Some(())), // 简化的蕴含证明
        };
        
        SafeWorkflow::new(
            move |input| {
                let mid_result = (self.workflow)(input);
                (next.workflow)(mid_result)
            },
            proof,
        )
    }
    
    // 并行组合安全工作流
    pub fn par<P2, I2, O2>(self, other: SafeWorkflow<P2, I2, O2>) 
        -> SafeWorkflow<ParallelCompositionProof<P, P2>, (I, I2), (O, O2)>
    where
        P2: SafetyProof,
    {
        let proof = ParallelCompositionProof {
            proof1: self.safety_proof,
            proof2: other.safety_proof,
            no_conflict: Box::new(|_, _| true), // 简化的无冲突证明
        };
        
        SafeWorkflow::new(
            move |input: Resource<(I, I2)>| {
                let (input1, input2) = input.consume();
                let result1 = (self.workflow)(Resource::new(input1));
                let result2 = (other.workflow)(Resource::new(input2));
                Resource::new((result1.consume(), result2.consume()))
            },
            proof,
        )
    }
}

// 使用安全工作流组合构建复杂工作流
fn build_safe_payment_workflow() -> SafeWorkflow<impl SafetyProof, PaymentRequest, PaymentResult> {
    // 验证请求工作流
    let validate = SafeWorkflow::new(
        |input: Resource<PaymentRequest>| {
            let request = input.consume();
            // 执行验证逻辑
            Resource::new(ValidatedRequest { request, timestamp: Utc::now() })
        },
        SimpleProof::new(/* 验证的前置和后置条件 */)
    );
    
    // 处理付款工作流
    let process = SafeWorkflow::new(
        |input: Resource<ValidatedRequest>| {
            let validated = input.consume();
            // 执行支付处理逻辑
            Resource::new(PaymentResult { 
                id: Uuid::new_v4(),
                status: "completed",
                timestamp: Utc::now(),
            })
        },
        SimpleProof::new(/* 处理的前置和后置条件 */)
    );
    
    // 安全组合
    validate.then(process)
}
```

### 对偶性与反模式

系统设计中的对偶性可以指导我们找到优雅的解决方案，而识别反模式则可以帮助我们避免常见的陷阱。

```rust
// 工作流系统中的对偶性与反模式

// 对偶性: 生产者-消费者对偶
trait Producer<T> {
    fn produce(&self) -> T;
}

trait Consumer<T> {
    fn consume(&self, item: T);
}

// 对偶转换: 生产者 -> 消费者
struct ProducerAsConsumer<P, F, T, U> {
    producer: P,
    transform: F,
    _phantom: PhantomData<(T, U)>,
}

impl<P, F, T, U> Consumer<T> for ProducerAsConsumer<P, F, T, U>
where
    P: Producer<U>,
    F: Fn(T, U),
{
    fn consume(&self, item: T) {
        let produced = self.producer.produce();
        (self.transform)(item, produced);
    }
}

// 对偶性: 推送-拉取对偶
trait PushBased<T> {
    fn push(&self, item: T);
}

trait PullBased<T> {
    fn pull(&self) -> Option<T>;
}

// 对偶转换: 推送 -> 拉取
struct PushToPull<P, T> {
    source: P,
    buffer: Mutex<VecDeque<T>>,
}

impl<P, T> PushToPull<P, T>
where
    P: PushBased<T>,
    T: Clone,
{
    fn new(source: P) -> Self {
        let this = Self {
            source,
            buffer: Mutex::new(VecDeque::new()),
        };
        
        // 为了简化示例，实际可能需要更复杂的订阅机制
        // source.subscribe(|item| {
        //     let mut buffer = this.buffer.lock().unwrap();
        //     buffer.push_back(item);
        // });
        
        this
    }
}

impl<P, T> PullBased<T> for PushToPull<P, T>
where
    P: PushBased<T>,
    T: Clone,
{
    fn pull(&self) -> Option<T> {
        let mut buffer = self.buffer.lock().unwrap();
        buffer.pop_front()
    }
}

// 反模式：共享可变状态
// 解决方案：使用消息传递或不可变数据结构
struct AntiPatternSharedMutable {
    state: Mutex<HashMap<String, String>>,
}

struct ImprovedImmutablePattern {
    state: Arc<HashMap<String, String>>,
    updates: mpsc::Sender<StateUpdate>,
}

enum StateUpdate {
    Insert(String, String),
    Remove(String),
    Clear,
}

impl ImprovedImmutablePattern {
    fn new() -> Self {
        let (tx, rx) = mpsc::channel();
        let state = Arc::new(HashMap::new());
        let state_clone = Arc::clone(&state);
        
        // 在单独线程中处理状态更新
        std::thread::spawn(move || {
            let mut current_state = (*state_clone).clone();
            
            for update in rx {
                let new_state = match update {
                    StateUpdate::Insert(k, v) => {
                        let mut map = current_state.clone();
                        map.insert(k, v);
                        map
                    },
                    StateUpdate::Remove(k) => {
                        let mut map = current_state.clone();
                        map.remove(&k);
                        map
                    },
                    StateUpdate::Clear => HashMap::new(),
                };
                
                current_state = new_state;
                // 更新共享状态
                // 在实际实现中，可能需要Arc::make_mut或其他方法
                // *state_clone = Arc::new(current_state.clone());
            }
        });
        
        Self {
            state,
            updates: tx,
        }
    }
    
    fn get(&self, key: &str) -> Option<String> {
        self.state.get(key).cloned()
    }
    
    fn insert(&self, key: String, value: String) {
        let _ = self.updates.send(StateUpdate::Insert(key, value));
    }
    
    fn remove(&self, key: String) {
        let _ = self.updates.send(StateUpdate::Remove(key));
    }
    
    fn clear(&self) {
        let _ = self.updates.send(StateUpdate::Clear);
    }
}

// 反模式：全局状态
// 改进：依赖注入
struct AntiPatternGlobalState;

impl AntiPatternGlobalState {
    fn get_config() -> &'static Config {
        GLOBAL_CONFIG.get().expect("配置未初始化")
    }
}

struct ImprovedDependencyInjection<C> {
    config: C,
}

impl<C: Config> ImprovedDependencyInjection<C> {
    fn new(config: C) -> Self {
        Self { config }
    }
    
    fn get_config(&self) -> &C {
        &self.config
    }
}

// 反模式：阻塞工作流
// 改进：响应式工作流
struct AntiPatternBlockingWorkflow;

impl AntiPatternBlockingWorkflow {
    fn process(&self) {
        // 直接阻塞调用
        let data = fetch_data_blocking();
        let processed = process_data_blocking(data);
        save_data_blocking(processed);
    }
}

struct ImprovedReactiveWorkflow;

impl ImprovedReactiveWorkflow {
    fn process(&self) -> impl Future<Output = Result<(), Error>> {
        async {
            let data = fetch_data().await?;
            let processed = process_data(data).await?;
            save_data(processed).await
        }
    }
}

// 对偶模式: 命令-查询分离 (CQS)
trait Command {
    type Error;
    fn execute(&self) -> Result<(), Self::Error>;
}

trait Query<T> {
    type Error;
    fn execute(&self) -> Result<T, Self::Error>;
}

// 对偶模式: 事件源与事件溯源
trait EventSourced<E> {
    fn apply(&mut self, event: E);
    fn events(&self) -> Vec<E>;
}

trait EventSourcing<E, S> {
    fn replay(events: &[E]) -> S;
}
```

## 一致性模型谱系

### 线性一致性机制

线性一致性（线性化）是分布式系统中最强的一致性模型，它保证所有操作看起来是以某种全局顺序执行的。

```rust
// 线性一致性机制实现
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::collections::HashMap;
use std::time::{Duration, Instant};
use uuid::Uuid;

// 线性一致性的分布式寄存器
pub struct LinearizableRegister<T: Clone> {
    data: Arc<Mutex<HashMap<String, (T, u64)>>>,
    version_counter: AtomicU64,
}

impl<T: Clone> LinearizableRegister<T> {
    pub fn new() -> Self {
        Self {
            data: Arc::new(Mutex::new(HashMap::new())),
            version_counter: AtomicU64::new(0),
        }
    }
    
    // 写入操作，返回操作的版本号
    pub fn write(&self, key: &str, value: T) -> u64 {
        // 获取新版本号
        let version = self.version_counter.fetch_add(1, Ordering::SeqCst) + 1;
        
        // 写入数据
        let mut data = self.data.lock().unwrap();
        data.insert(key.to_string(), (value, version));
        
        version
    }
    
    // 读取操作，返回值和版本号
    pub fn read(&self, key: &str) -> Option<(T, u64)> {
        let data = self.data.lock().unwrap();
        data.get(key).map(|(value, version)| (value.clone(), *version))
    }
    
    // 比较并交换操作，实现线性一致性
    pub fn compare_and_swap(&self, key: &str, expected_version: u64, new_value: T) -> Result<u64, u64> {
        let mut data = self.data.lock().unwrap();
        
        match data.get(key) {
            Some((_, current_version)) if *current_version == expected_version => {
                // 版本匹配，执行更新
                let new_version = self.version_counter.fetch_add(1, Ordering::SeqCst) + 1;
                data.insert(key.to_string(), (new_value, new_version));
                Ok(new_version)
            },
            Some((_, current_version)) => {
                // 版本不匹配，返回当前版本
                Err(*current_version)
            },
            None if expected_version == 0 => {
                // 键不存在，且期望版本为0，执行插入
                let new_version = self.version_counter.fetch_add(1, Ordering::SeqCst) + 1;
                data.insert(key.to_string(), (new_value, new_version));
                Ok(new_version)
            },
            None => {
                // 键不存在，但期望版本不为0，返回错误
                Err(0)
            }
        }
    }
}

// 分布式线性一致性共识实现（基于Raft算法简化版）
pub struct RaftConsensus<T: Clone + Send + 'static> {
    node_id: String,
    peers: Vec<String>,
    state: Arc<Mutex<RaftState<T>>>,
    log: Arc<Mutex<Vec<LogEntry<T>>>>,
    commit_index: AtomicU64,
    last_applied: AtomicU64,
}

struct RaftState<T> {
    current_term: u64,
    voted_for: Option<String>,
    role: RaftRole,
    leader_id: Option<String>,
    data: HashMap<String, T>,
}

enum RaftRole {
    Follower,
    Candidate,
    Leader,
}

struct LogEntry<T> {
    term: u64,
    index: u64,
    command: Command<T>,
}

enum Command<T> {
    Put { key: String, value: T },
    Delete { key: String },
}

impl<T: Clone + Send + 'static> RaftConsensus<T> {
    pub fn new(node_id: String, peers: Vec<String>) -> Self {
        let consensus = Self {
            node_id,
            peers,
            state: Arc::new(Mutex::new(RaftState {
                current_term: 0,
                voted_for: None,
                role: RaftRole::Follower,
                leader_id: None,
                data: HashMap::new(),
            })),
            log: Arc::new(Mutex::new(Vec::new())),
            commit_index: AtomicU64::new(0),
            last_applied: AtomicU64::new(0),
        };
        
        // 启动Raft循环
        consensus.start_raft_loop();
        
        consensus
    }
    
    // 客户端写请求
    pub fn put(&self, key: String, value: T) -> Result<(), ConsensusError> {
        // 检查当前节点是否是Leader
        let state = self.state.lock().unwrap();
        match state.role {
            RaftRole::Leader => {
                drop(state);
                
                // 创建日志条目
                let mut log = self.log.lock().unwrap();
                let new_index = log.len() as u64;
                let current_term = self.state.lock().unwrap().current_term;
                
                log.push(LogEntry {
                    term: current_term,
                    index: new_index,
                    command: Command::Put { key, value },
                });
                
                // 在实际实现中，这里应该请求其他节点复制日志
                // 这里简化为直接提交
                self.commit_log_entries(new_index);
                
                Ok(())
            },
            _ => {
                // 如果不是Leader，则将请求重定向到Leader
                if let Some(leader_id) = &state.leader_id {
                    Err(ConsensusError::NotLeader(leader_id.clone()))
                } else {
                    Err(ConsensusError::NoLeader)
                }
            }
        }
    }
    
    // 客户端读请求
    pub fn get(&self, key: &str) -> Result<Option<T>, ConsensusError> {
        // 在线性一致性模型中，读请求也需要通过共识确认
        // 实现方式有两种：
        // 1. ReadIndex: Leader确认自己仍然是Leader（检查大多数节点响应）
        // 2. Lease-based: Leader使用租约机制避免每次读操作都需要网络通信
        
        // 这里使用简化的方式：仅当节点是Leader时才能读取最新数据
        let state = self.state.lock().unwrap();
        
        match state.role {
            RaftRole::Leader => {
                // 应用所有已提交的日志条目
                self.apply_committed_logs();
                
                // 返回当前状态
                Ok(state.data.get(key).cloned())
            },
            _ => {
                // 如果不是Leader，则将请求重定向到Leader
                if let Some(leader_id) = &state.leader_id {
                    Err(ConsensusError::NotLeader(leader_id.clone()))
                } else {
                    Err(ConsensusError::NoLeader)
                }
            }
        }
    }
    
    // 启动Raft主循环
    fn start_raft_loop(&self) {
        let state_clone = Arc::clone(&self.state);
        let node_id = self.node_id.clone();
        let peers = self.peers.clone();
        
        std::thread::spawn(move || {
            let mut election_timeout = Self::random_election_timeout();
            let mut last_activity = Instant::now();
            
            loop {
                let elapsed = last_activity.elapsed();
                
                // 检查角色并执行相应操作
                let mut state = state_clone.lock().unwrap();
                
                match state.role {
                    RaftRole::Follower => {
                        // 如果超过选举超时，变成Candidate并开始选举
                        if elapsed >= election_timeout {
                            state.role = RaftRole::Candidate;
                            state.current_term += 1;
                            state.voted_for = Some(node_id.clone());
                            
                            // 实际实现中，这里应该启动选举过程
                            // self.request_votes();
                            
                            last_activity = Instant::now();
                            election_timeout = Self::random_election_timeout();
                        }
                    },
                    RaftRole::Candidate => {
                        // 如果超过选举超时，开始新的选举
                        if elapsed >= election_timeout {
                            state.current_term += 1;
                            
                            // 实际实现中，这里应该重新启动选举过程
                            // self.request_votes();
                            
                            last_activity = Instant::now();
                            election_timeout = Self::random_election_timeout();
                        }
                    },
                    RaftRole::Leader => {
                        // 定期发送心跳（AppendEntries）
                        if elapsed >= Duration::from_millis(100) {
                            // 实际实现中，这里应该向所有Follower发送心跳
                            // self.send_heartbeats();
                            
                            last_activity = Instant::now();
                        }
                    }
                }
                
                drop(state);
                std::thread::sleep(Duration::from_millis(10));
            }
        });
    }
    
    // 提交日志条目
    fn commit_log_entries(&self, up_to_index: u64) {
        // 在实际实现中，这里需要确保大多数节点已经复制了日志
        // 简化实现：直接更新commit_index
        self.commit_index.store(up_to_index, Ordering::SeqCst);
        
        // 应用已提交的日志
        self.apply_committed_logs();
    }
    
    // 应用已提交但尚未应用的日志条目
    fn apply_committed_logs(&self) {
        let commit_index = self.commit_index.load(Ordering::SeqCst);
        let mut last_applied = self.last_applied.load(Ordering::SeqCst);
        
        if commit_index > last_applied {
            let log = self.log.lock().unwrap();
            let mut state = self.state.lock().unwrap();
            
            while last_applied < commit_index {
                last_applied += 1;
                
                if let Some(entry) = log.get(last_applied as usize) {
                    match &entry.command {
                        Command::Put { key, value } => {
                            state.data.insert(key.clone(), value.clone());
                        },
                        Command::Delete { key } => {
                            state.data.remove(key);
                        }
                    }
                }
            }
            
            self.last_applied.store(last_applied, Ordering::SeqCst);
        }
    }
    
    // 生成随机选举超时时间（150ms到300ms之间）
    fn random_election_timeout() -> Duration {
        use rand::Rng;
        let mut rng = rand::thread_rng();
        Duration::from_millis(rng.gen_range(150..300))
    }
}

// 共识错误
enum ConsensusError {
    NotLeader(String), // 包含Leader ID
    NoLeader,
    Timeout,
    NetworkError,
}
```

### 因果一致性模型

因果一致性是比线性一致性弱但实用的一致性模型，它保证因果相关的操作按照一致的顺序被观察到。

```rust
// 因果一致性模型实现
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};

// 向量时钟
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct VectorClock {
    // 节点ID -> 逻辑时间戳
    clocks: HashMap<String, u64>,
}

impl VectorClock {
    pub fn new() -> Self {
        Self {
            clocks: HashMap::new(),
        }
    }
    
    // 为指定节点的时钟递增
    pub fn increment(&mut self, node_id: &str) {
        let count = self.clocks.entry(node_id.to_string()).or_insert(0);
        *count += 1;
    }
    
    // 合并两个向量时钟，取每个节点的最大值
    pub fn merge(&mut self, other: &VectorClock) {
        for (node, &time) in &other.clocks {
            let entry = self.clocks.entry(node.clone()).or_insert(0);
            *entry = std::cmp::max(*entry, time);
        }
    }
    
    // 检查this是否发生在other之前（因果关系）
    pub fn happens_before(&self, other: &VectorClock) -> bool {
        // 检查是否存在至少一个节点，this[node] < other[node]
        let mut less_exists = false;
        
        // 检查所有节点，确保不存在this[node] > other[node]
        for (node, &this_time) in &self.clocks {
            let other_time = other.clocks.get(node).cloned().unwrap_or(0);
            
            if this_time > other_time {
                return false;
            }
            
            if this_time < other_time {
                less_exists = true;
            }
        }
        
        // 检查other中存在但this中不存在的节点（视为其在this中为0）
        for (node, &other_time) in &other.clocks {
            if !self.clocks.contains_key(node) && other_time > 0 {
                less_exists = true;
            }
        }
        
        less_exists
    }
    
    // 检查两个向量时钟是否并发（无因果关系）
    pub fn concurrent_with(&self, other: &VectorClock) -> bool {
        !self.happens_before(other) && !other.happens_before(self)
    }
}

// 因果一致性数据存储
pub struct CausalStore<T: Clone> {
    node_id: String,
    data: Arc<Mutex<HashMap<String, Vec<VersionedValue<T>>>>>,
    vector_clock: Arc<Mutex<VectorClock>>,
}

// 带版本的值
#[derive(Clone)]
struct VersionedValue<T> {
    value: T,
    version: VectorClock,
}

impl<T: Clone> CausalStore<T> {
    pub fn new(node_id: String) -> Self {
        let mut clock = VectorClock::new();
        clock.increment(&node_id);
        
        Self {
            node_id,
            data: Arc::new(Mutex::new(HashMap::new())),
            vector_clock: Arc::new(Mutex::new(clock)),
        }
    }
    
    // 写入值，确保因果一致性
    pub fn put(&self, key: &str, value: T, context: Option<VectorClock>) -> VectorClock {
        let mut local_clock = self.vector_clock.lock().unwrap();
        
        // 如果提供了上下文，合并向量时钟
        if let Some(ctx) = context {
            local_clock.merge(&ctx);
        }
        
        // 增加本地节点的时钟
        local_clock.increment(&self.node_id);
        
        // 创建新版本
        let new_version = VersionedValue {
            value,
            version: local_clock.clone(),
        };
        
        // 存储新版本
        let mut data = self.data.lock().unwrap();
        let versions = data.entry(key.to_string()).or_insert_with(Vec::new);
        
        // 删除被新版本因果覆盖的旧版本
        versions.retain(|v| !v.version.happens_before(&new_version.version));
        
        // 添加新版本
        versions.push(new_version);
        
        // 返回操作的向量时钟，作为因果上下文
        local_clock.clone()
    }
    
    // 读取值，保证因果一致性
    pub fn get(&self, key: &str, context: Option<VectorClock>) -> (Option<T>, VectorClock) {
        let mut local_clock = self.vector_clock.lock().unwrap();
        
        // 如果提供了上下文，合并向量时钟
        if let Some(ctx) = context {
            local_clock.merge(&ctx);
        }
        
        let data = self.data.lock().unwrap();
        
        if let Some(versions) = data.get(key) {
            // 过滤出与当前上下文因果一致的版本
            let compatible_versions: Vec<_> = if let Some(ref ctx) = context {
                versions.iter()
                    .filter(|v| !v.version.happens_before(ctx))
                    .collect()
            } else {
                versions.iter().collect()
            };
            
            if compatible_versions.is_empty() {
                // 没有找到因果兼容的版本
                return (None, local_clock.clone());
            }
            
            // 在有多个并发更新的情况下，我们需要解决冲突
            // 这里采用简单策略：选择向量时钟"最大"的版本
            // 实际系统可能会使用更复杂的冲突解决策略
            let mut latest = &compatible_versions[0];
            
            for version in &compatible_versions[1..] {
                if version.version.happens_before(&latest.version) {
                    // 当前版本发生在latest之前，忽略
                    continue;
                }
                
                if latest.version.happens_before(&version.version) {
                    // latest发生在当前版本之前，更新latest
                    latest = version;
                    continue;
                }
                
                // 并发版本，使用某种冲突解决策略
                // 这里简单地选择节点ID字典序较大的版本
                if version.version.clocks.keys().max() > latest.version.clocks.keys().max() {
                    latest = version;
                }
            }
            
            // 更新本地向量时钟
            local_clock.merge(&latest.version);
            
            (Some(latest.value.clone()), local_clock.clone())
        } else {
            (None, local_clock.clone())
        }
    }
    
    // 获取当前向量时钟作为因果上下文
    pub fn get_context(&self) -> VectorClock {
        self.vector_clock.lock().unwrap().clone()
    }
}

// 分布式因果一致性系统
pub struct CausalSystem<T: Clone + Send + 'static> {
    stores: HashMap<String, Arc<CausalStore<T>>>,
}

impl<T: Clone + Send + 'static> CausalSystem<T> {
    pub fn new() -> Self {
        Self {
            stores: HashMap::new(),
        }
    }
    
    // 添加节点
    pub fn add_node(&mut self, node_id: String) -> Arc<CausalStore<T>> {
        let store = Arc::new(CausalStore::new(node_id.clone()));
        self.stores.insert(node_id, Arc::clone(&store));
        store
    }
    
    // 模拟消息传递：从源节点发送操作到目标节点
    pub fn send_operation(&self, from_id: &str, to_id: &str, key: &str) -> Result<(), String> {
        let from_store = self.stores.get(from_id)
            .ok_or_else(|| format!("源节点 {} 不存在", from_id))?;
            
        let to_store = self.stores.get(to_id)
            .ok_or_else(|| format!("目标节点 {} 不存在", to_id))?;
            
        // 从源节点读取数据和上下文
        let (value, context) = from_store.get(key, None);
        
        if let Some(value) = value {
            // 将操作复制到目标节点，保留因果上下文
            to_store.put(key, value, Some(context));
            Ok(())
        } else {
            Err(format!("键 {} 在源节点 {} 不存在", key, from_id))
        }
    }
}
```

### 混合一致性实现

在实际系统中，常常需要针对不同操作和数据采用不同的一致性模型，以平衡性能和正确性。

```rust
// 混合一致性模型实现
use std::collections::HashMap;
use std::sync::{Arc, Mutex, RwLock};
use std::time::{Duration, Instant};

// 一致性级别枚举
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ConsistencyLevel {
    Linearizable,   // 线性一致性
    Sequential,     // 顺序一致性
    Causal,         // 因果一致性
    Eventual,       // 最终一致性
}

// 一致性策略特征，决定使用哪种一致性级别
pub trait ConsistencyStrategy {
    fn get_level_for_read(&self, key: &str) -> ConsistencyLevel;
    fn get_level_for_write(&self, key: &str) -> ConsistencyLevel;
}

// 混合一致性存储
pub struct HybridConsistencyStore<T: Clone + Send + Sync + 'static, S: ConsistencyStrategy> {
    // 内部存储
    linearizable_store: Arc<LinearizableStore<T>>,
    sequential_store: Arc<SequentialStore<T>>,
    causal_store: Arc<CausalStore<T>>,
    eventual_store: Arc<EventualStore<T>>,
    
    // 一致性策略
    strategy: S,
    
    // 节点ID
    node_id: String,
}

impl<T: Clone + Send + Sync + 'static, S: ConsistencyStrategy> HybridConsistencyStore<T, S> {
    pub fn new(node_id: String, strategy: S) -> Self {
        Self {
            linearizable_store: Arc::new(LinearizableStore::new()),
            sequential_store: Arc::new(SequentialStore::new()),
            causal_store: Arc::new(CausalStore::new(node_id.clone())),
            eventual_store: Arc::new(EventualStore::new()),
            strategy,
            node_id,
        }
    }
    
    // 读取操作，根据策略选择一致性级别
    pub fn get(&self, key: &str) -> Option<T> {
        let level = self.strategy.get_level_for_read(key);
        
        match level {
            ConsistencyLevel::Linearizable => self.linearizable_store.get(key),
            ConsistencyLevel::Sequential => self.sequential_store.get(key),
            ConsistencyLevel::Causal => self.causal_store.get(key, None).0,
            ConsistencyLevel::Eventual => self.eventual_store.get(key),
        }
    }
    
    // 写入操作，根据策略选择一致性级别
    pub fn put(&self, key: &str, value: T) -> Result<(), StoreError> {
        let level = self.strategy.get_level_for_write(key);
        
        match level {
            ConsistencyLevel::Linearizable => {
                self.linearizable_store.put(key, value.clone())?;
                // 同步复制到其他存储以保持一致性
                self.sequential_store.put(key, value.clone())?;
                self.causal_store.put(key, value.clone(), None);
                self.eventual_store.put(key, value);
            },
            ConsistencyLevel::Sequential => {
                self.sequential_store.put(key, value.clone())?;
                // 复制到因果和最终一致性存储
                self.causal_store.put(key, value.clone(), None);
                self.eventual_store.put(key, value);
            },
            ConsistencyLevel::Causal => {
                let ctx = self.causal_store.put(key, value.clone(), None);
                // 复制到最终一致性存储
                self.eventual_store.put(key, value);
            },
            ConsistencyLevel::Eventual => {
                self.eventual_store.put(key, value);
            },
        }
        
        Ok(())
    }
    
    // 获取指定一致性级别的存储
    pub fn get_store(&self, level: ConsistencyLevel) -> Arc<dyn Store<T>> {
        match level {
            ConsistencyLevel::Linearizable => self.linearizable_store.clone() as Arc<dyn Store<T>>,
            ConsistencyLevel::Sequential => self.sequential_store.clone() as Arc<dyn Store<T>>,
            ConsistencyLevel::Causal => self.causal_store.clone() as Arc<dyn Store<T>>,
            ConsistencyLevel::Eventual => self.eventual_store.clone() as Arc<dyn Store<T>>,
        }
    }
}

// 通用存储接口
pub trait Store<T> {
    fn get(&self, key: &str) -> Option<T>;
}

// 线性一致性存储实现示意
struct LinearizableStore<T: Clone + Send + Sync + 'static> {
    data: RwLock<HashMap<String, T>>,
    // 在实际系统中，可能需要使用分布式共识算法（如Raft）
}

impl<T: Clone + Send + Sync + 'static> LinearizableStore<T> {
    fn new() -> Self {
        Self {
            data: RwLock::new(HashMap::new()),
        }
    }
    
    fn put(&self, key: &str, value: T) -> Result<(), StoreError> {
        let mut data = self.data.write().unwrap();
        data.insert(key.to_string(), value);
        Ok(())
    }
}

impl<T: Clone + Send + Sync + 'static> Store<T> for LinearizableStore<T> {
    fn get(&self, key: &str) -> Option<T> {
        let data = self.data.read().unwrap();
        data.get(key).cloned()
    }
}

// 顺序一致性存储实现示意
struct SequentialStore<T: Clone + Send + Sync + 'static> {
    data: Mutex<HashMap<String, T>>,
}

impl<T: Clone + Send + Sync + 'static> SequentialStore<T> {
    fn new() -> Self {
        Self {
            data: Mutex::new(HashMap::new()),
        }
    }
    
    fn put(&self, key: &str, value: T) -> Result<(), StoreError> {
        let mut data = self.data.lock().unwrap();
        data.insert(key.to_string(), value);
        Ok(())
    }
}

impl<T: Clone + Send + Sync + 'static> Store<T> for SequentialStore<T> {
    fn get(&self, key: &str) -> Option<T> {
        let data = self.data.lock().unwrap();
        data.get(key).cloned()
    }
}

// 最终一致性存储
struct EventualStore<T: Clone + Send + Sync + 'static> {
    data: RwLock<HashMap<String, T>>,
    // 在实际系统中，这里可能有复制队列和后台同步线程
}

impl<T: Clone + Send + Sync + 'static> EventualStore<T> {
    fn new() -> Self {
        Self {
            data: RwLock::new(HashMap::new()),
        }
    }
    
    fn put(&self, key: &str, value: T) -> Result<(), StoreError> {
        let mut data = self.data.write().unwrap();
        data.insert(key.to_string(), value);
        
        // 在实际系统中，这里会将更新加入异步复制队列
        
        Ok(())
    }
}

impl<T: Clone + Send + Sync + 'static> Store<T> for EventualStore<T> {
    fn get(&self, key: &str) -> Option<T> {
        let data = self.data.read().unwrap();
        data.get(key).cloned()
    }
}

impl<T: Clone + Send + Sync + 'static> Store<T> for CausalStore<T> {
    fn get(&self, key: &str) -> Option<T> {
        self.get(key, None).0
    }
}

// 存储错误
pub enum StoreError {
    Timeout,
    NetworkError,
    ConsensusError,
    ConcurrencyError,
}

// 基于数据类型的一致性策略示例
pub struct DataTypeDrivenStrategy {
    // 不同类型数据使用不同一致性级别
    config: HashMap<String, ConsistencyLevel>,
    default_level: ConsistencyLevel,
}

impl DataTypeDrivenStrategy {
    pub fn new(default_level: ConsistencyLevel) -> Self {
        Self {
            config: HashMap::new(),
            default_level,
        }
    }
    
    pub fn set_level_for_type(&mut self, data_type: &str, level: ConsistencyLevel) {
        self.config.insert(data_type.to_string(), level);
    }
    
    // 从键名推断数据类型
    fn get_data_type(&self, key: &str) -> String {
        // 假设键格式为"type:id"，例如"user:123"
        if let Some(pos) = key.find(':') {
            key[0..pos].to_string()
        } else {
            "default".to_string()
        }
    }
}

impl ConsistencyStrategy for DataTypeDrivenStrategy {
    fn get_level_for_read(&self, key: &str) -> ConsistencyLevel {
        let data_type = self.get_data_type(key);
        *self.config.get(&data_type).unwrap_or(&self.default_level)
    }
    
    fn get_level_for_write(&self, key: &str) -> ConsistencyLevel {
        let data_type = self.get_data_type(key);
        *self.config.get(&data_type).unwrap_or(&self.default_level)
    }
}

// 显式一致性策略示例：由客户端显式指定一致性级别
pub struct ExplicitConsistencyContext {
    read_level: ConsistencyLevel,
    write_level: ConsistencyLevel,
}

impl ExplicitConsistencyContext {
    pub fn new(read_level: ConsistencyLevel, write_level: ConsistencyLevel) -> Self {
        Self {
            read_level,
            write_level,
        }
    }
    
    pub fn set_read_level(&mut self, level: ConsistencyLevel) {
        self.read_level = level;
    }
    
    pub fn set_write_level(&mut self, level: ConsistencyLevel) {
        self.write_level = level;
    }
}

// 使用线程本地存储实现显式一致性上下文
thread_local! {
    static CONSISTENCY_CONTEXT: RefCell<ExplicitConsistencyContext> = RefCell::new(
        ExplicitConsistencyContext::new(
            ConsistencyLevel::Eventual,  // 默认读一致性
            ConsistencyLevel::Causal,    // 默认写一致性
        )
    );
}

// 上下文管理函数
pub fn with_consistency<F, R>(level: ConsistencyLevel, f: F) -> R
where
    F: FnOnce() -> R,
{
    CONSISTENCY_CONTEXT.with(|ctx| {
        let old_read = ctx.borrow().read_level;
        ctx.borrow_mut().set_read_level(level);
        let result = f();
        ctx.borrow_mut().set_read_level(old_read);
        result
    })
}

// 带显式一致性上下文的存储接口
struct ContextAwareStore<T: Clone + Send + Sync + 'static> {
    hybrid_store: HybridConsistencyStore<T, DataTypeDrivenStrategy>,
}

impl<T: Clone + Send + Sync + 'static> ContextAwareStore<T> {
    fn get(&self, key: &str) -> Option<T> {
        CONSISTENCY_CONTEXT.with(|ctx| {
            let level = ctx.borrow().read_level;
            match level {
                ConsistencyLevel::Linearizable => self.hybrid_store.linearizable_store.get(key),
                ConsistencyLevel::Sequential => self.hybrid_store.sequential_store.get(key),
                ConsistencyLevel::Causal => self.hybrid_store.causal_store.get(key, None).0,
                ConsistencyLevel::Eventual => self.hybrid_store.eventual_store.get(key),
            }
        })
    }
    
    fn put(&self, key: &str, value: T) -> Result<(), StoreError> {
        CONSISTENCY_CONTEXT.with(|ctx| {
            let level = ctx.borrow().write_level;
            match level {
                ConsistencyLevel::Linearizable => {
                    self.hybrid_store.linearizable_store.put(key, value.clone())?;
                    self.hybrid_store.sequential_store.put(key, value.clone())?;
                    self.hybrid_store.causal_store.put(key, value.clone(), None);
                    self.hybrid_store.eventual_store.put(key, value);
                },
                ConsistencyLevel::Sequential => {
                    self.hybrid_store.sequential_store.put(key, value.clone())?;
                    self.hybrid_store.causal_store.put(key, value.clone(), None);
                    self.hybrid_store.eventual_store.put(key, value);
                },
                ConsistencyLevel::Causal => {
                    self.hybrid_store.causal_store.put(key, value.clone(), None);
                    self.hybrid_store.eventual_store.put(key, value);
                },
                ConsistencyLevel::Eventual => {
                    self.hybrid_store.eventual_store.put(key, value);
                },
            }
            Ok(())
        })
    }
}
```

### 一致性升降级策略

在面对系统负载变化、网络故障或部分节点不可用时，动态调整一致性级别是一种有效的策略。

```rust
// 一致性升降级策略
use std::collections::HashMap;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, RwLock};
use std::time::{Duration, Instant};

// 系统健康状态
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SystemHealth {
    Healthy,          // 系统正常运行，所有节点可用
    Degraded,         // 系统部分降级，部分节点不可用
    Critical,         // 系统处于临界状态，大部分节点不可用
    Emergency,        // 紧急状态，仅有少数节点可用
}

// 自适应一致性策略，根据系统健康状态自动调整
pub struct AdaptiveConsistencyStrategy {
    // 健康状态到一致性级别的映射
    read_policy: HashMap<SystemHealth, ConsistencyLevel>,
    write_policy: HashMap<SystemHealth, ConsistencyLevel>,
    
    // 当前系统健康状态
    health_state: Arc<RwLock<SystemHealth>>,
    
    // 监控指标
    metrics: Arc<SystemMetrics>,
}

impl AdaptiveConsistencyStrategy {
    pub fn new(metrics: Arc<SystemMetrics>) -> Self {
        let mut read_policy = HashMap::new();
        read_policy.insert(SystemHealth::Healthy, ConsistencyLevel::Linearizable);
        read_policy.insert(SystemHealth::Degraded, ConsistencyLevel::Sequential);
        read_policy.insert(SystemHealth::Critical, ConsistencyLevel::Causal);
        read_policy.insert(SystemHealth::Emergency, ConsistencyLevel::Eventual);
        
        let mut write_policy = HashMap::new();
        write_policy.insert(SystemHealth::Healthy, ConsistencyLevel::Linearizable);
        write_policy.insert(SystemHealth::Degraded, ConsistencyLevel::Sequential);
        write_policy.insert(SystemHealth::Critical, ConsistencyLevel::Causal);
        write_policy.insert(SystemHealth::Emergency, ConsistencyLevel::Eventual);
        
        let strategy = Self {
            read_policy,
            write_policy,
            health_state: Arc::new(RwLock::new(SystemHealth::Healthy)),
            metrics,
        };
        
        // 启动健康状态检查线程
        strategy.start_health_monitor();
        
        strategy
    }
    
    // 启动健康状态监控线程
    fn start_health_monitor(&self) {
        let metrics = Arc::clone(&self.metrics);
        let health_state = Arc::clone(&self.health_state);
        
        std::thread::spawn(move || {
            loop {
                // 收集系统指标
                let available_nodes = metrics.get_available_nodes();
                let total_nodes = metrics.get_total_nodes();
                let p99_latency = metrics.get_p99_latency();
                
                // 计算健康比率
                let health_ratio = available_nodes as f64 / total_nodes as f64;
                
                // 根据指标判断系统健康状态
                let new_health = if health_ratio >= 0.9 && p99_latency < 100.0 {
                    SystemHealth::Healthy
                } else if health_ratio >= 0.7 && p99_latency < 200.0 {
                    SystemHealth::Degraded
                } else if health_ratio >= 0.5 && p99_latency < 500.0 {
                    SystemHealth::Critical
                } else {
                    SystemHealth::Emergency
                };
                
                // 更新健康状态
                {
                    let mut state = health_state.write().unwrap();
                    if *state != new_health {
                        println!("System health changed from {:?} to {:?}", *state, new_health);
                        *state = new_health;
                    }
                }
                
                // 每10秒检查一次
                std::thread::sleep(Duration::from_secs(10));
            }
        });
    }
}

impl ConsistencyStrategy for AdaptiveConsistencyStrategy {
    fn get_level_for_read(&self, _key: &str) -> ConsistencyLevel {
        let health = *self.health_state.read().unwrap();
        *self.read_policy.get(&health).unwrap_or(&ConsistencyLevel::Eventual)
    }
    
    fn get_level_for_write(&self, _key: &str) -> ConsistencyLevel {
        let health = *self.health_state.read().unwrap();
        *self.write_policy.get(&health).unwrap_or(&ConsistencyLevel::Eventual)
    }
}

// 系统指标收集器
pub struct SystemMetrics {
    available_nodes: AtomicUsize,
    total_nodes: AtomicUsize,
    latencies: Mutex<Vec<f64>>,
}

impl SystemMetrics {
    pub fn new(total_nodes: usize) -> Self {
        Self {
            available_nodes: AtomicUsize::new(total_nodes),
            total_nodes: AtomicUsize::new(total_nodes),
            latencies: Mutex::new(Vec::new()),
        }
    }
    
    pub fn report_node_available(&self, available: bool) {
        if available {
            self.available_nodes.fetch_add(1, Ordering::Relaxed);
        } else {
            self.available_nodes.fetch_sub(1, Ordering::Relaxed);
        }
    }
    
    pub fn report_latency(&self, latency_ms: f64) {
        let mut latencies = self.latencies.lock().unwrap();
        latencies.push(latency_ms);
        
        // 保持最近1000个样本
        if latencies.len() > 1000 {
            *latencies = latencies.iter().skip(latencies.len() - 1000).cloned().collect();
        }
    }
    
    pub fn get_available_nodes(&self) -> usize {
        self.available_nodes.load(Ordering::Relaxed)
    }
    
    pub fn get_total_nodes(&self) -> usize {
        self.total_nodes.load(Ordering::Relaxed)
    }
    
    pub fn get_p99_latency(&self) -> f64 {
        let latencies = self.latencies.lock().unwrap();
        if latencies.is_empty() {
            return 0.0;
        }
        
        let mut sorted = latencies.clone();
        sorted.sort_by(|a, b| a.partial_cmp(b).unwrap());
        
        let p99_index = ((sorted.len() as f64) * 0.99) as usize;
        sorted[p99_index]
    }
}

// 客户端一致性适配器
pub struct ConsistencyAdapter<T: Clone + Send + Sync + 'static> {
    store: Arc<HybridConsistencyStore<T, AdaptiveConsistencyStrategy>>,
    metrics: Arc<SystemMetrics>,
    timeout_policy: TimeoutPolicy,
}

// 超时策略
pub struct TimeoutPolicy {
    timeouts: HashMap<ConsistencyLevel, Duration>,
    fallback_levels: HashMap<ConsistencyLevel, ConsistencyLevel>,
}

impl TimeoutPolicy {
    pub fn new() -> Self {
        let mut timeouts = HashMap::new();
        timeouts.insert(ConsistencyLevel::Linearizable, Duration::from_millis(500));
        timeouts.insert(ConsistencyLevel::Sequential, Duration::from_millis(300));
        timeouts.insert(ConsistencyLevel::Causal, Duration::from_millis(200));
        timeouts.insert(ConsistencyLevel::Eventual, Duration::from_millis(100));
        
        let mut fallback_levels = HashMap::new();
        fallback_levels.insert(ConsistencyLevel::Linearizable, ConsistencyLevel::Sequential);
        fallback_levels.insert(ConsistencyLevel::Sequential, ConsistencyLevel::Causal);
        fallback_levels.insert(ConsistencyLevel::Causal, ConsistencyLevel::Eventual);
        fallback_levels.insert(ConsistencyLevel::Eventual, ConsistencyLevel::Eventual); // 不再降级
        
        Self {
            timeouts,
            fallback_levels,
        }
    }
    
    pub fn get_timeout(&self, level: ConsistencyLevel) -> Duration {
        *self.timeouts.get(&level).unwrap_or(&Duration::from_millis(100))
    }
    
    pub fn get_fallback(&self, level: ConsistencyLevel) -> ConsistencyLevel {
        *self.fallback_levels.get(&level).unwrap_or(&ConsistencyLevel::Eventual)
    }
}

impl<T: Clone + Send + Sync + 'static> ConsistencyAdapter<T> {
    pub fn new(
        store: Arc<HybridConsistencyStore<T, AdaptiveConsistencyStrategy>>,
        metrics: Arc<SystemMetrics>,
    ) -> Self {
        Self {
            store,
            metrics,
            timeout_policy: TimeoutPolicy::new(),
        }
    }
    
    // 带超时和自动降级的读操作
    pub fn get_with_timeout(&self, key: &str, initial_level: ConsistencyLevel) -> Option<T> {
        let mut current_level = initial_level;
        
        // 尝试不同一致性级别，直到成功或达到最低级别
        loop {
            let timeout = self.timeout_policy.get_timeout(current_level);
            let start = Instant::now();
            
            // 创建读取任务
            let store_clone = Arc::clone(&self.store);
            let key_clone = key.to_string();
            let read_task = std::thread::spawn(move || {
                let store = store_clone.get_store(current_level);
                store.get(&key_clone)
            });
            
            // 使用超时等待结果
            match read_task.join() {
                Ok(result) => {
                    // 记录延迟
                    let latency = start.elapsed().as_millis() as f64;
                    self.metrics.report_latency(latency);
                    
                    if latency <= timeout.as_millis() as f64 {
                        return result;
                    }
                },
                Err(_) => {
                    // 线程错误，记录为最大延迟
                    self.metrics.report_latency(timeout.as_millis() as f64 * 1.5);
                }
            }
            
            // 获取降级的一致性级别
            let fallback = self.timeout_policy.get_fallback(current_level);
            
            if fallback == current_level {
                // 已经到达最低级别，返回空结果
                return None;
            }
            
            // 降级一致性并重试
            println!("Downgrading consistency from {:?} to {:?} for key {}", current_level, fallback, key);
            current_level = fallback;
        }
    }
}
```

## 边缘云组合架构

### 连续体计算模型

边缘计算和云计算形成一个计算连续体，工作流系统可以跨越这个连续体灵活地部署和执行任务。

```rust
// 连续体计算模型实现
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex, RwLock};
use std::time::{Duration, Instant};

// 计算位置枚举
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum ComputeLocation {
    Cloud,               // 中心云
    RegionalCloud,       // 区域云
    EdgeCloud,           // 边缘云
    EdgeDevice,          // 边缘设备
    LocalDevice,         // 本地设备
}

// 资源约束
#[derive(Clone, Debug)]
pub struct ResourceConstraints {
    cpu_cores: f32,
    memory_mb: u32,
    storage_gb: u32,
    network_mbps: u32,
    max_latency_ms: u32,
}

// 位置要求
#[derive(Clone, Debug)]
pub enum LocationRequirement {
    Specific(ComputeLocation),         // 必须在特定位置执行
    PreferredOrder(Vec<ComputeLocation>), // 按偏好顺序执行
    AnyOf(Vec<ComputeLocation>),       // 任选一个位置执行
    All,                               // 任何位置都可以执行
}

// 连续体可执行单元
#[derive(Clone)]
pub struct ContinuumExecutableUnit<T> {
    id: String,
    function: Arc<dyn Fn(T) -> T + Send + Sync>,
    resource_constraints: ResourceConstraints,
    location_requirement: LocationRequirement,
    data_locality_preference: bool,  // 是否偏好数据本地性
    state_requirements: HashSet<String>, // 需要访问的状态键
}

impl<T: Clone + Send + 'static> ContinuumExecutableUnit<T> {
    pub fn new(
        id: String,
        function: impl Fn(T) -> T + Send + Sync + 'static,
        resource_constraints: ResourceConstraints,
        location_requirement: LocationRequirement,
    ) -> Self {
        Self {
            id,
            function: Arc::new(function),
            resource_constraints,
            location_requirement,
            data_locality_preference: false,
            state_requirements: HashSet::new(),
        }
    }
    
    pub fn with_data_locality(mut self, prefer_locality: bool) -> Self {
        self.data_locality_preference = prefer_locality;
        self
    }
    
    pub fn add_state_requirement(mut self, key: &str) -> Self {
        self.state_requirements.insert(key.to_string());
        self
    }
    
    pub fn execute(&self, input: T) -> T {
        (self.function)(input)
    }
}

// 计算节点管理器
pub struct ComputeNodeManager {
    nodes: RwLock<HashMap<String, ComputeNode>>,
}

impl ComputeNodeManager {
    pub fn new() -> Self {
        Self {
            nodes: RwLock::new(HashMap::new()),
        }
    }
    
    pub fn register_node(&self, node: ComputeNode) {
        let mut nodes = self.nodes.write().unwrap();
        nodes.insert(node.id.clone(), node);
    }
    
    pub fn unregister_node(&self, node_id: &str) {
        let mut nodes = self.nodes.write().unwrap();
        nodes.remove(node_id);
    }
    
    pub fn get_node(&self, node_id: &str) -> Option<ComputeNode> {
        let nodes = self.nodes.read().unwrap();
        nodes.get(node_id).cloned()
    }
    
    pub fn find_suitable_nodes(
        &self,
        constraints: &ResourceConstraints,
        location_req: &LocationRequirement,
        state_keys: &HashSet<String>,
    ) -> Vec<String> {
        let nodes = self.nodes.read().unwrap();
        
        nodes.values()
            .filter(|node| {
                // 检查资源约束
                node.available_resources.cpu_cores >= constraints.cpu_cores &&
                node.available_resources.memory_mb >= constraints.memory_mb &&
                node.available_resources.storage_gb >= constraints.storage_gb &&
                node.available_resources.network_mbps >= constraints.network_mbps &&
                node.latency_ms <= constraints.max_latency_ms &&
                
                // 检查位置要求
                match location_req {
                    LocationRequirement::Specific(loc) => node.location == *loc,
                    LocationRequirement::PreferredOrder(locs) => locs.contains(&node.location),
                    LocationRequirement::AnyOf(locs) => locs.contains(&node.location),
                    LocationRequirement::All => true,
                } &&
                
                // 检查状态要求
                state_keys.iter().all(|key| node.available_state_keys.contains(key))
            })
            .map(|node| node.id.clone())
            .collect()
    }
}

// 计算节点
#[derive(Clone)]
pub struct ComputeNode {
    id: String,
    location: ComputeLocation,
    available_resources: ResourceConstraints,
    latency_ms: u32,  // 与中心云的估计延迟
    available_state_keys: HashSet<String>,  // 节点可访问的状态键
}

impl ComputeNode {
    pub fn new(
        id: String,
        location: ComputeLocation,
        available_resources: ResourceConstraints,
        latency_ms: u32,
    ) -> Self {
        Self {
            id,
            location,
            available_resources,
            latency_ms,
            available_state_keys: HashSet::new(),
        }
    }
    
    pub fn add_state_key(&mut self, key: &str) {
        self.available_state_keys.insert(key.to_string());
    }
    
    pub fn remove_state_key(&mut self, key: &str) {
        self.available_state_keys.remove(key);
    }
}

// 连续体工作流执行器
pub struct ContinuumWorkflowExecutor<T: Clone + Send + 'static> {
    node_manager: Arc<ComputeNodeManager>,
    units: HashMap<String, ContinuumExecutableUnit<T>>,
    dependencies: HashMap<String, Vec<String>>,
    state_manager: Arc<ContinuumStateManager>,
}

impl<T: Clone + Send + 'static> ContinuumWorkflowExecutor<T> {
    pub fn new(node_manager: Arc<ComputeNodeManager>, state_manager: Arc<ContinuumStateManager>) -> Self {
        Self {
            node_manager,
            units: HashMap::new(),
            dependencies: HashMap::new(),
            state_manager,
        }
    }
    
    pub fn add_executable_unit(&mut self, unit: ContinuumExecutableUnit<T>) {
        self.units.insert(unit.id.clone(), unit);
        self.dependencies.entry(unit.id.clone()).or_insert_with(Vec::new);
    }
    
    pub fn add_dependency(&mut self, from_id: &str, to_id: &str) {
        if self.units.contains_key(from_id) && self.units.contains_key(to_id) {
            self.dependencies.entry(to_id.to_string())
                .or_insert_with(Vec::new)
                .push(from_id.to_string());
        }
    }
    
    pub fn execute_workflow(&self, initial_input: T) -> Result<T, WorkflowError> {
        // 找出没有依赖的单元作为起点
        let mut ready_units: Vec<String> = self.dependencies.iter()
            .filter(|(_, deps)| deps.is_empty())
            .map(|(id, _)| id.clone())
            .collect();
            
        let mut completed_units = HashSet::new();
        let mut unit_results: HashMap<String, T> = HashMap::new();
        
        // 存储初始输入
        unit_results.insert("__initial__".to_string(), initial_input);
        
        // 执行工作流，直到所有单元都已执行
        while !ready_units.is_empty() {
            let unit_id = ready_units.remove(0);
            let unit = self.units.get(&unit_id).ok_or(WorkflowError::UnitNotFound)?;
            
            // 为执行单元找到合适的计算节点
            let suitable_nodes = self.node_manager.find_suitable_nodes(
                &unit.resource_constraints,
                &unit.location_requirement,
                &unit.state_requirements,
            );
            
            if suitable_nodes.is_empty() {
                return Err(WorkflowError::NoSuitableNode);
            }
            
            // 选择最合适的节点（简化版：选择第一个）
            let target_node_id = &suitable_nodes[0];
            
            // 获取输入（从依赖单元的结果或初始输入）
            let input = if let Some(deps) = self.dependencies.get(&unit_id) {
                if deps.is_empty() {
                    // 无依赖，使用初始输入
                    unit_results.get("__initial__").cloned().unwrap()
                } else {
                    // 有依赖，使用最后一个依赖的输出（简化处理）
                    // 实际系统可能需要汇总多个依赖的结果
                    unit_results.get(&deps[deps.len() - 1]).cloned().unwrap()
                }
            } else {
                // 默认使用初始输入
                unit_results.get("__initial__").cloned().unwrap()
            };
            
            // 执行单元（在实际系统中，这会涉及到跨节点分发执行请求）
            println!("Executing unit {} on node {}", unit_id, target_node_id);
            let result = unit.execute(input);
            
            // 存储结果
            unit_results.insert(unit_id.clone(), result);
            completed_units.insert(unit_id.clone());
            
            // 检查哪些单元可以执行了
            for (next_id, deps) in &self.dependencies {
                if !completed_units.contains(next_id) && 
                   deps.iter().all(|dep| completed_units.contains(dep)) {
                    ready_units.push(next_id.clone());
                }
            }
        }
        
        // 找出没有后继单元的单元作为终点
        let terminal_units: Vec<String> = self.dependencies.keys()
            .filter(|id| !self.dependencies.values().any(|deps| deps.contains(id)))
            .cloned()
            .collect();
            
        if terminal_units.is_empty() {
            return Err(WorkflowError::NoTerminalUnit);
        }
        
        // 返回最后一个终点单元的结果
        unit_results.get(&terminal_units[terminal_units.len() - 1])
            .cloned()
            .ok_or(WorkflowError::ResultNotFound)
    }
}

// 工作流错误
pub enum WorkflowError {
    UnitNotFound,
    NoSuitableNode,
    NoTerminalUnit,
    ResultNotFound,
    StateError(String),
}

// 连续体状态管理器
pub struct ContinuumStateManager {
    state_locations: RwLock<HashMap<String, HashSet<String>>>, // 状态键到节点ID的映射
    replication_policy: ReplicationPolicy,
}

// 复制策略
pub enum ReplicationPolicy {
    None,               // 不复制
    FullReplication,    // 完全复制到所有节点
    RegionalReplication, // 按区域复制
    Custom(Box<dyn Fn(&str) -> Vec<ComputeLocation> + Send + Sync>), // 自定义复制规则
}

impl ContinuumStateManager {
    pub fn new(replication_policy: ReplicationPolicy) -> Self {
        Self {
            state_locations: RwLock::new(HashMap::new()),
            replication_policy,
        }
    }
    
    // 注册状态位置
    pub fn register_state(&self, key: &str, node_id: &str) {
        let mut state_locs = self.state_locations.write().unwrap();
        state_locs.entry(key.to_string())
            .or_insert_with(HashSet::new)
            .insert(node_id.to_string());
    }
    
    // 获取状态所在的节点
    pub fn get_state_locations(&self, key: &str) -> HashSet<String> {
        let state_locs = self.state_locations.read().unwrap();
        state_locs.get(key).cloned().unwrap_or_else(HashSet::new)
    }
    
    // 复制状态到目标节点
    pub fn replicate_state(&self, key: &str, from_node: &str, to_node: &str) -> Result<(), StateError> {
        // 实际系统中，这里会涉及到实际的数据传输
        // 简化实现：只更新状态位置信息
        let mut state_locs = self.state_locations.write().unwrap();
        
        if let Some(locations) = state_locs.get_mut(key) {
            if locations.contains(from_node) {
                locations.insert(to_node.to_string());
                Ok(())
            } else {
                Err(StateError::SourceNotAvailable)
            }
        } else {
            Err(StateError::KeyNotFound)
        }
    }
}

// 状态错误
pub enum StateError {
    KeyNotFound,
    SourceNotAvailable,
    TargetUnavailable,
    NetworkError,
}
```

### 边缘自主决策机制

边缘节点常常需要在有限的网络连接或高延迟环境下工作，因此需要具备一定的自主决策能力。

```rust
// 边缘自主决策机制实现
use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::{Arc, Mutex, RwLock};
use std::time::{Duration, Instant};

// 边缘节点决策级别
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum EdgeAutonomyLevel {
    FullyDependent,      // 完全依赖云端决策
    SemiAutonomous,      // 半自主决策
    HighlyAutonomous,    // 高度自主决策
    FullyAutonomous,     // 完全自主决策
}

// 自主决策规则类型
pub enum DecisionRuleType {
    Threshold,           // 基于阈值的规则
    Pattern,             // 基于模式的规则
    Prediction,          // 基于预测的规则
    CompositeCond,       // 复合条件规则
}

// 决策规则
pub trait DecisionRule {
    fn evaluate(&self, context: &DecisionContext) -> bool;
    fn rule_type(&self) -> DecisionRuleType;
    fn description(&self) -> String;
}

// 决策上下文
pub struct DecisionContext {
    metrics: HashMap<String, f64>,            // 度量指标
    events: VecDeque<EdgeEvent>,              // 最近的事件
    state: HashMap<String, Vec<u8>>,          // 本地状态
    connectivity: ConnectivityStatus,         // 连接状态
    timestamp: u64,                           // 时间戳
}

// 连接状态
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ConnectivityStatus {
    Connected,           // 连接正常
    Degraded,            // 连接降级
    Intermittent,        // 间歇性连接
    Disconnected,        // 完全断开
}

// 边缘事件
pub struct EdgeEvent {
    event_type: String,
    timestamp: u64,
    payload: HashMap<String, String>,
}

// 边缘自主决策引擎
pub struct EdgeAutonomyEngine {
    node_id: String,
    autonomy_level: EdgeAutonomyLevel,
    decision_rules: Vec<Box<dyn DecisionRule + Send + Sync>>,
    fallback_handlers: HashMap<String, Box<dyn FallbackHandler + Send + Sync>>,
    context: RwLock<DecisionContext>,
    connectivity_monitor: Arc<ConnectivityMonitor>,
}

// 回退处理器特征
pub trait FallbackHandler {
    fn handle_fallback(&self, context: &DecisionContext) -> FallbackAction;
    fn description(&self) -> String;
}

// 回退动作
pub enum FallbackAction {
    Retry,               // 重试原始操作
    UseCache,            // 使用缓存数据
    ExecuteLocal,        // 本地执行
    Defer,               // 延迟处理
    Reject,              // 拒绝请求
    UseApproximation,    // 使用近似结果
}

impl EdgeAutonomyEngine {
    pub fn new(
        node_id: String,
        initial_autonomy_level: EdgeAutonomyLevel,
        connectivity_monitor: Arc<ConnectivityMonitor>,
    ) -> Self {
        let context = DecisionContext {
            metrics: HashMap::new(),
            events: VecDeque::with_capacity(100),
            state: HashMap::new(),
            connectivity: ConnectivityStatus::Connected,
            timestamp: 0,
        };
        
        Self {
            node_id,
            autonomy_level: initial_autonomy_level,
            decision_rules: Vec::new(),
            fallback_handlers: HashMap::new(),
            context: RwLock::new(context),
            connectivity_monitor,
        }
    }
    
    // 添加决策规则
    pub fn add_rule(&mut self, rule: Box<dyn DecisionRule + Send + Sync>) {
        self.decision_rules.push(rule);
    }
    
    // 添加回退处理器
    pub fn add_fallback_handler(
        &mut self,
        operation_type: &str,
        handler: Box<dyn FallbackHandler + Send + Sync>
    ) {
        self.fallback_handlers.insert(operation_type.to_string(), handler);
    }
    
    // 更新决策上下文
    pub fn update_context(&self, update_fn: impl FnOnce(&mut DecisionContext)) {
        let mut context = self.context.write().unwrap();
        update_fn(&mut context);
    }
    
    // 添加事件
    pub fn add_event(&self, event: EdgeEvent) {
        let mut context = self.context.write().unwrap();
        context.events.push_back(event);
        
        // 保持事件队列大小限制
        while context.events.len() > 100 {
            context.events.pop_front();
        }
    }
    
    // 决策函数：判断是否可以本地决策
    pub fn can_decide_locally(&self, operation_type: &str) -> bool {
        // 1. 检查自主级别
        match self.autonomy_level {
            EdgeAutonomyLevel::FullyDependent => false,
            EdgeAutonomyLevel::FullyAutonomous => true,
            _ => {
                // 2. 检查连接状态
                let connectivity = self.connectivity_monitor.get_status();
                if connectivity == ConnectivityStatus::Disconnected {
                    return true; // 断开连接时强制本地决策
                }
                
                // 3. 评估决策规则
                let context = self.context.read().unwrap();
                self.decision_rules.iter().any(|rule| rule.evaluate(&context))
            }
        }
    }
    
    // 获取回退动作
    pub fn get_fallback_action(&self, operation_type: &str) -> Option<FallbackAction> {
        if let Some(handler) = self.fallback_handlers.get(operation_type) {
            let context = self.context.read().unwrap();
            Some(handler.handle_fallback(&context))
        } else {
            None
        }
    }
    
    // 动态调整自主级别
    pub fn adjust_autonomy_level(&mut self) {
        let context = self.context.read().unwrap();
        let connectivity = self.connectivity_monitor.get_status();
        
        // 基于连接状态调整自主级别
        self.autonomy_level = match connectivity {
            ConnectivityStatus::Connected => {
                // 连接良好，根据历史决策准确性降低自主级别
                let decision_accuracy = self.calculate_decision_accuracy(&context);
                if decision_accuracy > 0.9 {
                    EdgeAutonomyLevel::SemiAutonomous
                } else {
                    EdgeAutonomyLevel::FullyDependent
                }
            },
            ConnectivityStatus::Degraded => {
                // 连接降级，保持一定自主级别
                EdgeAutonomyLevel::SemiAutonomous
            },
            ConnectivityStatus::Intermittent => {
                // 间歇性连接，提高自主级别
                EdgeAutonomyLevel::HighlyAutonomous
            },
            ConnectivityStatus::Disconnected => {
                // 完全断开，最高自主级别
                EdgeAutonomyLevel::FullyAutonomous
            },
        };
    }
    
    // 计算历史决策准确性
    fn calculate_decision_accuracy(&self, context: &DecisionContext) -> f64 {
        // 实际系统中，这里会基于历史决策与云端结果的比较
        // 简化实现：使用固定值
        0.85
    }
}

// 连接监视器
pub struct ConnectivityMonitor {
    status: RwLock<ConnectivityStatus>,
    last_heartbeat: RwLock<Instant>,
    heartbeat_timeout: Duration,
}

impl ConnectivityMonitor {
    pub fn new(heartbeat_timeout: Duration) -> Self {
        Self {
            status: RwLock::new(ConnectivityStatus::Connected),
            last_heartbeat: RwLock::new(Instant::now()),
            heartbeat_timeout,
        }
    }
    
    pub fn update_status(&self, new_status: ConnectivityStatus) {
        let mut status = self.status.write().unwrap();
        *status = new_status;
        
        if new_status == ConnectivityStatus::Connected {
            let mut last_heartbeat = self.last_heartbeat.write().unwrap();
            *last_heartbeat = Instant::now();
        }
    }
    
    pub fn record_heartbeat(&self) {
        let mut last_heartbeat = self.last_heartbeat.write().unwrap();
        *last_heartbeat = Instant::now();
        
        let mut status = self.status.write().unwrap();
        if *status != ConnectivityStatus::Connected {
            *status = ConnectivityStatus::Connected;
        }
    }
    
    pub fn get_status(&self) -> ConnectivityStatus {
        // 检查心跳超时
        let last_heartbeat = self.last_heartbeat.read().unwrap();
        let elapsed = last_heartbeat.elapsed();
        
        if elapsed > self.heartbeat_timeout {
            // 心跳超时，标记为断开连接
            let mut status = self.status.write().unwrap();
            *status = ConnectivityStatus::Disconnected;
        }
        
        *self.status.read().unwrap()
    }
    
    pub fn start_monitoring(&self) {
        let monitor = Arc::new(self.clone());
        
        std::thread::spawn(move || {
            loop {
                // 周期性检查连接状态并更新
                let current_status = monitor.get_status();
                
                // 根据心跳间隔计算连接质量
                let last_heartbeat = monitor.last_heartbeat.read().unwrap();
                let elapsed = last_heartbeat.elapsed();
                
                let new_status = if elapsed < monitor.heartbeat_timeout / 4 {
                    ConnectivityStatus::Connected
                } else if elapsed < monitor.heartbeat_timeout / 2 {
                    ConnectivityStatus::Degraded
                } else if elapsed < monitor.heartbeat_timeout {
                    ConnectivityStatus::Intermittent
                } else {
                    ConnectivityStatus::Disconnected
                };
                
                if current_status != new_status {
                    monitor.update_status(new_status);
                }
                
                std::thread::sleep(Duration::from_secs(1));
            }
        });
    }
}

impl Clone for ConnectivityMonitor {
    fn clone(&self) -> Self {
        Self {
            status: RwLock::new(*self.status.read().unwrap()),
            last_heartbeat: RwLock::new(*self.last_heartbeat.read().unwrap()),
            heartbeat_timeout: self.heartbeat_timeout,
        }
    }
}

// 阈值决策规则
pub struct ThresholdRule {
    metric_name: String,
    threshold: f64,
    comparison: ThresholdComparison,
    description: String,
}

// 阈值比较类型
pub enum ThresholdComparison {
    GreaterThan,
    LessThan,
    Equal,
    NotEqual,
}

impl ThresholdRule {
    pub fn new(
        metric_name: String,
        threshold: f64,
        comparison: ThresholdComparison,
        description: String,
    ) -> Self {
        Self {
            metric_name,
            threshold,
            comparison,
            description,
        }
    }
}

impl DecisionRule for ThresholdRule {
    fn evaluate(&self, context: &DecisionContext) -> bool {
        if let Some(&metric_value) = context.metrics.get(&self.metric_name) {
            match self.comparison {
                ThresholdComparison::GreaterThan => metric_value > self.threshold,
                ThresholdComparison::LessThan => metric_value < self.threshold,
                ThresholdComparison::Equal => (metric_value - self.threshold).abs() < std::f64::EPSILON,
                ThresholdComparison::NotEqual => (metric_value - self.threshold).abs() >= std::f64::EPSILON,
            }
        } else {
            false
        }
    }
    
    fn rule_type(&self) -> DecisionRuleType {
        DecisionRuleType::Threshold
    }
    
    fn description(&self) -> String {
        self.description.clone()
    }
}

// 模式决策规则
pub struct PatternRule {
    event_pattern: Vec<String>,
    time_window_seconds: u64,
    description: String,
}

impl PatternRule {
    pub fn new(
        event_pattern: Vec<String>,
        time_window_seconds: u64,
        description: String,
    ) -> Self {
        Self {
            event_pattern,
            time_window_seconds,
            description,
        }
    }
}

impl DecisionRule for PatternRule {
    fn evaluate(&self, context: &DecisionContext) -> bool {
        // 检查近期事件是否匹配指定模式
        let now = context.timestamp;
        let window_start = now.saturating_sub(self.time_window_seconds);
        
        // 过滤时间窗口内的事件
        let recent_events: Vec<_> = context.events.iter()
            .filter(|e| e.timestamp >= window_start)
            .collect();
            
        // 检查是否包含所有模式事件
        self.event_pattern.iter().all(|pattern| {
            recent_events.iter().any(|e| e.event_type == *pattern)
        })
    }
    
    fn rule_type(&self) -> DecisionRuleType {
        DecisionRuleType::Pattern
    }
    
    fn description(&self) -> String {
        self.description.clone()
    }
}

// 缓存使用回退处理器
pub struct CacheFallbackHandler {
    max_cache_age_seconds: u64,
    description: String,
}

impl CacheFallbackHandler {
    pub fn new(max_cache_age_seconds: u64, description: String) -> Self {
        Self {
            max_cache_age_seconds,
            description,
        }
    }
}

impl FallbackHandler for CacheFallbackHandler {
    fn handle_fallback(&self, context: &DecisionContext) -> FallbackAction {
        // 检查是否有足够新的缓存数据
        let has_recent_cache = context.state.keys().any(|key| {
            key.starts_with("cache_") && {
                if let Some(cache_time_str) = key.strip_prefix("cache_") {
                    if let Ok(cache_time) = cache_time_str.parse::<u64>() {
                        // 检查缓存是否足够新
                        context.timestamp.saturating_sub(cache_time) <= self.max_cache_age_seconds
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
        });
        
        if has_recent_cache {
            FallbackAction::UseCache
        } else if context.connectivity == ConnectivityStatus::Intermittent {
            FallbackAction::Retry
        } else {
            FallbackAction::ExecuteLocal
        }
    }
    
    fn description(&self) -> String {
        self.description.clone()
    }
}
```

### 混合执行模式

混合执行模式允许工作流系统根据实际情况在边缘和云之间动态分配任务执行位置。

```rust
// 混合执行模式实现
use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::{Arc, Mutex, RwLock};
use std::time::{Duration, Instant};

// 执行模式
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ExecutionMode {
    CloudOnly,          // 仅在云端执行
    EdgeOnly,           // 仅在边缘执行
    HybridStatic,       // 静态混合模式（预定义的执行位置）
    HybridDynamic,      // 动态混合模式（运行时决策执行位置）
    AdaptiveFlow,       // 自适应流动执行（任务可迁移）
}

// 执行位置决策参数
pub struct ExecutionPlacementParams {
    data_size_bytes: u64,              // 数据大小
    computation_complexity: f64,       // 计算复杂度
    latency_sensitivity_ms: u32,       // 延迟敏感度
    energy_constraints: bool,          // 能源约束
    bandwidth_available_mbps: u32,     // 可用带宽
    location_requirements: Option<LocationRequirement>, // 位置要求
}

// 混合执行调度器
pub struct HybridExecutionScheduler {
    mode: ExecutionMode,
    node_manager: Arc<ComputeNodeManager>,
    placement_strategy: Box<dyn PlacementStrategy + Send + Sync>,
    task_locations: RwLock<HashMap<String, String>>, // 任务ID到节点ID的映射
    task_stats: RwLock<HashMap<String, TaskExecutionStats>>, // 任务执行统计
}

// 任务执行统计
pub struct TaskExecutionStats {
    execution_times: VecDeque<(ComputeLocation, Duration)>, // 执行位置和耗时
    data_transfer_sizes: VecDeque<u64>,                     // 数据传输大小
    failure_rates: HashMap<ComputeLocation, f64>,           // 各位置失败率
    last_execution: Instant,                                // 上次执行时间
}

// 任务分配策略
pub trait PlacementStrategy {
    fn decide_placement(
        &self,
        task_id: &str,
        params: &ExecutionPlacementParams,
        available_nodes: &[ComputeNode],
        stats: Option<&TaskExecutionStats>,
    ) -> Option<String>; // 返回选中的节点ID
    
    fn name(&self) -> &str;
}

impl HybridExecutionScheduler {
    pub fn new(
        mode: ExecutionMode,
        node_manager: Arc<ComputeNodeManager>,
        placement_strategy: Box<dyn PlacementStrategy + Send + Sync>,
    ) -> Self {
        Self {
            mode,
            node_manager,
            placement_strategy,
            task_locations: RwLock::new(HashMap::new()),
            task_stats: RwLock::new(HashMap::new()),
        }
    }
    
    // 设置执行模式
    pub fn set_mode(&mut self, mode: ExecutionMode) {
        self.mode = mode;
    }
    
    // 为任务选择执行位置
    pub fn schedule_task(
        &self,
        task_id: &str,
        params: ExecutionPlacementParams,
    ) -> Result<String, SchedulingError> {
        // 根据当前模式选择节点
        match self.mode {
            ExecutionMode::CloudOnly => {
                // 仅选择云节点
                let cloud_nodes = self.get_nodes_by_location(ComputeLocation::Cloud);
                if cloud_nodes.is_empty() {
                    return Err(SchedulingError::NoSuitableNode);
                }
                
                // 简单策略：选择第一个云节点
                Ok(cloud_nodes[0].id.clone())
            },
            ExecutionMode::EdgeOnly => {
                // 仅选择边缘节点
                let edge_nodes = self.get_nodes_by_location(ComputeLocation::EdgeDevice);
                if edge_nodes.is_empty() {
                    return Err(SchedulingError::NoSuitableNode);
                }
                
                // 简单策略：选择第一个边缘节点
                Ok(edge_nodes[0].id.clone())
            },
            ExecutionMode::HybridStatic => {
                // 根据任务位置要求静态分配
                if let Some(LocationRequirement::Specific(location)) = &params.location_requirements {
                    let nodes = self.get_nodes_by_location(*location);
                    if nodes.is_empty() {
                        return Err(SchedulingError::NoSuitableNode);
                    }
                    
                    // 简单策略：选择第一个符合位置的节点
                    Ok(nodes[0].id.clone())
                } else {
                    // 没有明确位置要求，默认使用云节点
                    let cloud_nodes = self.get_nodes_by_location(ComputeLocation::Cloud);
                    if cloud_nodes.is_empty() {
                        return Err(SchedulingError::NoSuitableNode);
                    }
                    
                    Ok(cloud_nodes[0].id.clone())
                }
            },
            ExecutionMode::HybridDynamic | ExecutionMode::AdaptiveFlow => {
                // 使用动态分配策略
                let mut available_nodes = Vec::new();
                
                // 根据任务位置要求过滤节点
                if let Some(req) = &params.location_requirements {
                    match req {
                        LocationRequirement::Specific(location) => {
                            available_nodes.extend(self.get_nodes_by_location(*location));
                        },
                        LocationRequirement::PreferredOrder(locations) => {
                            for loc in locations {
                                available_nodes.extend(self.get_nodes_by_location(*loc));
                            }
                        },
                        LocationRequirement::AnyOf(locations) => {
                            for loc in locations {
                                available_nodes.extend(self.get_nodes_by_location(*loc));
                            }
                        },
                        LocationRequirement::All => {
                            // 所有节点都是候选
                            available_nodes = self.get_all_nodes();
                        },
                    }
                } else {
                    // 没有明确位置要求，使用所有节点
                    available_nodes = self.get_all_nodes();
                }
                
                if available_nodes.is_empty() {
                    return Err(SchedulingError::NoSuitableNode);
                }
                
                // 获取任务统计信息
                let stats = {
                    let task_stats = self.task_stats.read().unwrap();
                    task_stats.get(task_id).cloned()
                };
                
                // 使用放置策略决定执行位置
                if let Some(node_id) = self.placement_strategy.decide_placement(
                    task_id,
                    &params,
                    &available_nodes,
                    stats.as_ref(),
                ) {
                    // 记录任务位置
                    let mut task_locations = self.task_locations.write().unwrap();
                    task_locations.insert(task_id.to_string(), node_id.clone());
                    
                    Ok(node_id)
                } else {
                    Err(SchedulingError::StrategyFailed)
                }
            },
        }
    }
    
    // 记录任务执行统计
    pub fn record_execution(
        &self,
        task_id: &str,
        node_id: &str,
        duration: Duration,
        data_size: u64,
        success: bool,
    ) {
        let node = self.node_manager.get_node(node_id);
        
        if let Some(node) = node {
            let mut task_stats = self.task_stats.write().unwrap();
            let stats = task_stats.entry(task_id.to_string()).or_insert_with(|| {
                TaskExecutionStats {
                    execution_times: VecDeque::with_capacity(10),
                    data_transfer_sizes: VecDeque::with_capacity(10),
                    failure_rates: HashMap::new(),
                    last_execution: Instant::now(),
                }
            });
            
            // 更新执行时间
            stats.execution_times.push_back((node.location, duration));
            if stats.execution_times.len() > 10 {
                stats.execution_times.pop_front();
            }
            
            // 更新数据传输大小
            stats.data_transfer_sizes.push_back(data_size);
            if stats.data_transfer_sizes.len() > 10 {
                stats.data_transfer_sizes.pop_front();
            }
            
            // 更新失败率
            let failure_rate = stats.failure_rates.entry(node.location).or_insert(0.0);
            *failure_rate = *failure_rate * 0.9 + (if success { 0.0 } else { 0.1 });
            
            // 更新上次执行时间
            stats.last_execution = Instant::now();
        }
    }
    
    // 检查任务迁移条件
    pub fn should_migrate_task(&self, task_id: &str) -> bool {
        // 仅在自适应流动模式下考虑迁移
        if self.mode != ExecutionMode::AdaptiveFlow {
            return false;
        }
        
        let task_stats = self.task_stats.read().unwrap();
        let stats = if let Some(stats) = task_stats.get(task_id) {
            stats
        } else {
            return false;
        };
        
        // 检查是否有性能下降迹象
        if stats.execution_times.len() >= 3 {
            // 计算最近三次执行的平均时间
            let recent_avg = stats.execution_times.iter().rev().take(3)
                .fold(Duration::from_secs(0), |acc, (_, time)| acc + *time)
                .div_f32(3.0);
                
            // 计算前面执行的平均时间
            if stats.execution_times.len() > 5 {
                let previous_avg = stats.execution_times.iter().rev().skip(3).take(stats.execution_times.len() - 3)
                    .fold(Duration::from_secs(0), |acc, (_, time)| acc + *time)
                    .div_f32((stats.execution_times.len() - 3) as f32);
                    
                // 如果最近的执行比之前慢20%以上，考虑迁移
                if recent_avg > previous_avg.mul_f32(1.2) {
                    return true;
                }
            }
        }
        
        // 检查失败率
        if let Some(task_location) = self.task_locations.read().unwrap().get(task_id) {
            if let Some(node) = self.node_manager.get_node(task_location) {
                if let Some(failure_rate) = stats.failure_rates.get(&node.location) {
                    // 如果失败率超过10%，考虑迁移
                    if *failure_rate > 0.1 {
                        return true;
                    }
                }
            }
        }
        
        false
    }
    
    // 执行任务迁移
    pub fn migrate_task(
        &self,
        task_id: &str,
        params: ExecutionPlacementParams,
    ) -> Result<String, SchedulingError> {
        // 获取当前节点
        let current_node_id = {
            let task_locations = self.task_locations.read().unwrap();
            if let Some(node_id) = task_locations.get(task_id) {
                Some(node_id.clone())
            } else {
                None
            }
        };
        
        // 重新调度，但排除当前节点
        let mut available_nodes = Vec::new();
        
        // 根据任务位置要求过滤节点
        if let Some(req) = &params.location_requirements {
            match req {
                LocationRequirement::Specific(location) => {
                    available_nodes.extend(self.get_nodes_by_location(*location));
                },
                LocationRequirement::PreferredOrder(locations) => {
                    for loc in locations {
                        available_nodes.extend(self.get_nodes_by_location(*loc));
                    }
                },
                LocationRequirement::AnyOf(locations) => {
                    for loc in locations {
                        available_nodes.extend(self.get_nodes_by_location(*loc));
                    }
                },
                LocationRequirement::All => {
                    // 所有节点都是候选
                    available_nodes = self.get_all_nodes();
                },
            }
        } else {
            // 没有明确位置要求，使用所有节点
            available_nodes = self.get_all_nodes();
        }
        
        // 排除当前节点
        if let Some(current_id) = &current_node_id {
            available_nodes.retain(|node| node.id != *current_id);
        }
        
        if available_nodes.is_empty() {
            return Err(SchedulingError::NoSuitableNode);
        }
        
        // 获取任务统计信息
        let stats = {
            let task_stats = self.task_stats.read().unwrap();
            task_stats.get(task_id).cloned()
        };
        
        // 使用放置策略决定新的执行位置
        if let Some(node_id) = self.placement_strategy.decide_placement(
            task_id,
            &params,
            &available_nodes,
            stats.as_ref(),
        ) {
            // 更新任务位置
            let mut task_locations = self.task_locations.write().unwrap();
            task_locations.insert(task_id.to_string(), node_id.clone());
            
            println!("Migrating task {} from {:?} to {}", task_id, current_node_id, node_id);
            
            Ok(node_id)
        } else {
            Err(SchedulingError::StrategyFailed)
        }
    }
    
    // 获取指定位置的所有节点
    fn get_nodes_by_location(&self, location: ComputeLocation) -> Vec<ComputeNode> {
        let nodes = self.node_manager.nodes.read().unwrap();
        nodes.values()
            .filter(|node| node.location == location)
            .cloned()
            .collect()
    }
    
    // 获取所有可用节点
    fn get_all_nodes(&self) -> Vec<ComputeNode> {
        let nodes = self.node_manager.nodes.read().unwrap();
        nodes.values().cloned().collect()
    }
}

// 调度错误
pub enum SchedulingError {
    NoSuitableNode,
    StrategyFailed,
    TaskNotFound,
    NodeUnavailable,
}

// 数据感知放置策略
pub struct DataAwarePlacementStrategy {
    data_locality_weight: f64,  // 数据局部性权重
    compute_power_weight: f64,  // 计算能力权重
    latency_weight: f64,        // 延迟权重
    energy_weight: f64,         // 能耗权重
}

impl DataAwarePlacementStrategy {
    pub fn new(
        data_locality_weight: f64,
        compute_power_weight: f64,
        latency_weight: f64,
        energy_weight: f64,
    ) -> Self {
        Self {
            data_locality_weight,
            compute_power_weight,
            latency_weight,
            energy_weight,
        }
    }
}

impl PlacementStrategy for DataAwarePlacementStrategy {
    fn decide_placement(
        &self,
        task_id: &str,
        params: &ExecutionPlacementParams,
        available_nodes: &[ComputeNode],
        stats: Option<&TaskExecutionStats>,
    ) -> Option<String> {
        if available_nodes.is_empty() {
            return None;
        }
        
        // 计算每个节点的得分
        let mut node_scores: Vec<(String, f64)> = Vec::with_capacity(available_nodes.len());
        
        for node in available_nodes {
            let mut score = 0.0;
            
            // 数据局部性得分：数据大小越大，在数据所在位置执行越有利
            if let Some(location_req) = &params.location_requirements {
                if let LocationRequirement::Specific(preferred_location) = location_req {
                    if node.location == *preferred_location {
                        score += self.data_locality_weight * (params.data_size_bytes as f64 / 1024.0 / 1024.0);
                    }
                }
            }
            
            // 计算能力得分：计算密集型任务更适合高性能节点
            let compute_score = match node.location {
                ComputeLocation::Cloud => 1.0,
                ComputeLocation::RegionalCloud => 0.8,
                ComputeLocation::EdgeCloud => 0.6,
                ComputeLocation::EdgeDevice => 0.3,
                ComputeLocation::LocalDevice => 0.1,
            } * params.computation_complexity;
            
            score += self.compute_power_weight * compute_score;
            
            // 延迟敏感度得分：延迟敏感的任务更适合边缘执行
            let latency_score = match node.location {
                ComputeLocation::Cloud => 0.2,
                ComputeLocation::RegionalCloud => 0.4,
                ComputeLocation::EdgeCloud => 0.6,
                ComputeLocation::EdgeDevice => 0.8,
                ComputeLocation::LocalDevice => 1.0,
            } * (params.latency_sensitivity_ms as f64 / 100.0);
            
            score += self.latency_weight * latency_score;
            
            // 能耗得分：如果有能源约束，优先考虑能耗低的位置
            if params.energy_constraints {
                let energy_score = match node.location {
                    ComputeLocation::Cloud => 0.3,        // 能耗高但效率高
                    ComputeLocation::RegionalCloud => 0.4,
                    ComputeLocation::EdgeCloud => 0.6,
                    ComputeLocation::EdgeDevice => 0.7,
                    ComputeLocation::LocalDevice => 1.0,  // 能耗最低
                };
                
                score += self.energy_weight * energy_score;
            }
            
            // 历史执行情况调整
            if let Some(stats) = stats {
                // 如果该位置有历史失败率，降低得分
                if let Some(failure_rate) = stats.failure_rates.get(&node.location) {
                    score *= (1.0 - failure_rate);
                }
                
                // 查找历史执行时间
                let avg_execution_time = stats.execution_times.iter()
                    .filter(|(loc, _)| *loc == node.location)
                    .map(|(_, time)| time.as_millis() as f64)
                    .fold((0.0, 0), |(sum, count), time| (sum + time, count + 1));
                    
                if avg_execution_time.1 > 0 {
                    // 执行时间越短，得分越高
                    let time_score = 1000.0 / (avg_execution_time.0 / avg_execution_time.1 as f64);
                    score += time_score * 0.2; // 加入历史执行时间的权重
                }
            }
            
            node_scores.push((node.id.clone(), score));
        }
        
        // 选择得分最高的节点
        node_scores.sort_by(|(_, a), (_, b)| b.partial_cmp(a).unwrap_or(std::cmp::Ordering::Equal));
        
        node_scores.first().map(|(id, _)| id.clone())
    }
    
    fn name(&self) -> &str {
        "DataAwarePlacementStrategy"
    }
}
```

### 容错与分区处理

在边缘-云混合环境中，网络分区和节点故障是常见的挑战，需要特殊的容错机制。

```rust
// 容错与分区处理实现
use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::{Arc, Mutex, RwLock};
use std::time::{Duration, Instant};

// 节点状态
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum NodeState {
    Healthy,           // 健康状态
    Degraded,          // 性能降级
    Partitioned,       // 网络分区
    Failed,            // 完全故障
}

// 分区处理策略
pub enum PartitionHandlingStrategy {
    ReadOnly,          // 分区期间只允许读操作
    WriteLocal,        // 分区期间写入本地，稍后合并
    RejectWrites,      // 分区期间拒绝写入操作
    LeaderOnly,        // 仅Leader分区接受写入
}

// 容错模式
pub enum FaultToleranceMode {
    ActivePassive,     // 主备模式
    ActiveActive,      // 双活模式
    Quorum,            // 仲裁模式
    MultiMaster,       // 多主模式
}

// 恢复操作
pub enum RecoveryAction {
    Restart,           // 重启节点
    Failover,          // 故障转移
    Reconcile,         // 数据协调
    StateTransfer,     // 状态传输
}

// 容错管理器
pub struct FaultToleranceManager {
    node_states: RwLock<HashMap<String, NodeHealthInfo>>,
    partition_strategy: PartitionHandlingStrategy,
    ft_mode: FaultToleranceMode,
    recovery_handlers: HashMap<NodeState, Box<dyn RecoveryHandler + Send + Sync>>,
    conflict_resolver: Box<dyn ConflictResolver + Send + Sync>,
}

// 节点健康信息
pub struct NodeHealthInfo {
    state: NodeState,
    last_heartbeat: Instant,
    consecutive_failures: u32,
    metadata: HashMap<String, String>,
}

// 恢复处理器特征
pub trait RecoveryHandler {
    fn handle_recovery(&self, node_id: &str, state: NodeState) -> Vec<RecoveryAction>;
    fn description(&self) -> &str;
}

// 冲突解析器特征
pub trait ConflictResolver {
    fn resolve_conflicts(&self, conflicting_versions: &[VersionedData]) -> VersionedData;
    fn description(&self) -> &str;
}

// 版本化数据
pub struct VersionedData {
    key: String,
    value: Vec<u8>,
    version: u64,
    timestamp: u64,
    node_id: String,
    vector_clock: HashMap<String, u64>,
}

impl FaultToleranceManager {
    pub fn new(
        partition_strategy: PartitionHandlingStrategy,
        ft_mode: FaultToleranceMode,
        conflict_resolver: Box<dyn ConflictResolver + Send + Sync>,
    ) -> Self {
        Self {
            node_states: RwLock::new(HashMap::new()),
            partition_strategy,
            ft_mode,
            recovery_handlers: HashMap::new(),
            conflict_resolver,
        }
    }
    
    // 添加恢复处理器
    pub fn add_recovery_handler(
        &mut self,
        state: NodeState,
        handler: Box<dyn RecoveryHandler + Send + Sync>,
    ) {
        self.recovery_handlers.insert(state, handler);
    }
    
    // 注册节点健康信息
    pub fn register_node(&self, node_id: &str) {
        let mut node_states = self.node_states.write().unwrap();
        
        node_states.insert(node_id.to_string(), NodeHealthInfo {
            state: NodeState::Healthy,
            last_heartbeat: Instant::now(),
            consecutive_failures: 0,
            metadata: HashMap::new(),
        });
    }
    
    // 接收心跳
    pub fn receive_heartbeat(&self, node_id: &str) -> Result<(), FaultToleranceError> {
        let mut node_states = self.node_states.write().unwrap();
        
        if let Some(info) = node_states.get_mut(node_id) {
            info.last_heartbeat = Instant::now();
            
            // 如果节点之前是分区或故障状态，现在恢复了
            if info.state == NodeState::Partitioned || info.state == NodeState::Failed {
                info.state = NodeState::Healthy;
                info.consecutive_failures = 0;
                
                // 在实际系统中，这里可能需要触发恢复逻辑
                drop(node_states); // 释放锁后再处理恢复
                self.handle_node_recovery(node_id);
            }
            
            Ok(())
        } else {
            Err(FaultToleranceError::NodeNotFound)
        }
    }
    
    // 检测节点故障
    pub fn detect_failures(&self, heartbeat_timeout: Duration) -> Vec<String> {
        let mut node_states = self.node_states.write().unwrap();
        let now = Instant::now();
        
        let mut failed_nodes = Vec::new();
        
        for (node_id, info) in node_states.iter_mut() {
            if info.state != NodeState::Failed && now.duration_since(info.last_heartbeat) > heartbeat_timeout {
                info.consecutive_failures += 1;
                
                // 更新节点状态
                if info.consecutive_failures >= 3 {
                    let old_state = info.state;
                    info.state = NodeState::Failed;
                    
                    if old_state != NodeState::Failed {
                        failed_nodes.push(node_id.clone());
                    }
                } else if info.consecutive_failures >= 1 {
                    info.state = NodeState::Partitioned;
                }
            }
        }
        
        failed_nodes
    }
    
    // 处理节点恢复
    fn handle_node_recovery(&self, node_id: &str) -> Vec<RecoveryAction> {
        let node_state = {
            let node_states = self.node_states.read().unwrap();
            if let Some(info) = node_states.get(node_id) {
                info.state
            } else {
                return Vec::new(); // 节点不存在，无需恢复
            }
        };
        
        // 找到对应的恢复处理器
        if let Some(handler) = self.recovery_handlers.get(&node_state) {
            handler.handle_recovery(node_id, node_state)
        } else {
            // 默认恢复动作
            match node_state {
                NodeState::Partitioned => vec![RecoveryAction::Reconcile],
                NodeState::Failed => vec![RecoveryAction::Restart, RecoveryAction::StateTransfer],
                _ => Vec::new(),
            }
        }
    }
    
    // 检查是否可以写入（基于分区策略）
    pub fn can_write(&self, node_id: &str) -> bool {
        let node_states = self.node_states.read().unwrap();
        
        if let Some(info) = node_states.get(node_id) {
            match info.state {
                NodeState::Healthy => true, // 健康节点总是可写
                NodeState::Degraded => true, // 降级节点仍可写
                NodeState::Partitioned => {
                    // 根据分区策略决定
                    match self.partition_strategy {
                        PartitionHandlingStrategy::ReadOnly => false,
                        PartitionHandlingStrategy::WriteLocal => true,
                        PartitionHandlingStrategy::RejectWrites => false,
                        PartitionHandlingStrategy::LeaderOnly => {
                            // 检查是否是Leader分区
                            self.is_in_leader_partition(node_id)
                        }
                    }
                },
                NodeState::Failed => false, // 故障节点不可写
            }
        } else {
            false // 未知节点不可写
        }
    }
    
    // 检查是否可以读取
    pub fn can_read(&self, node_id: &str) -> bool {
        let node_states = self.node_states.read().unwrap();
        
        if let Some(info) = node_states.get(node_id) {
            match info.state {
                NodeState::Healthy | NodeState::Degraded => true, // 健康和降级节点可读
                NodeState::Partitioned => true, // 分区节点通常仍然可读
                NodeState::Failed => false, // 故障节点不可读
            }
        } else {
            false // 未知节点不可读
        }
    }
    
    // 检查节点是否在Leader分区
    fn is_in_leader_partition(&self, node_id: &str) -> bool {
        // 在实际系统中，这里需要检查节点是否在包含多数派节点的分区中
        // 简化实现：假设ID最小的活跃节点所在的分区是Leader分区
        
        let node_states = self.node_states.read().unwrap();
        
        // 收集所有非故障节点
        let active_nodes: Vec<&String> = node_states.iter()
            .filter(|(_, info)| info.state != NodeState::Failed)
            .map(|(id, _)| id)
            .collect();
            
        if active_nodes.is_empty() {
            return false;
        }
        
        // 找出ID最小的活跃节点
        let leader_partition_node = active_nodes.iter().min().unwrap();
        
        // 检查目标节点和ID最小的活跃节点是否在同一个分区
        // 简化处理：只判断节点状态
        if let (Some(node_info), Some(min_node_info)) = (
            node_states.get(node_id),
            node_states.get(*leader_partition_node)
        ) {
            // 如果两个节点都是健康或都是分区状态，认为它们在同一分区
            (node_info.state == NodeState::Healthy && min_node_info.state == NodeState::Healthy) ||
            (node_info.state == NodeState::Partitioned && min_node_info.state == NodeState::Partitioned)
        } else {
            false
        }
    }
    
    // 合并分区后的数据冲突
    pub fn merge_after_partition(&self, conflicting_versions: Vec<VersionedData>) -> VersionedData {
        self.conflict_resolver.resolve_conflicts(&conflicting_versions)
    }
}

// 容错错误类型
pub enum FaultToleranceError {
    NodeNotFound,
    StateTransferFailed,
    ReconciliationFailed,
    FailoverFailed,
}

// 向量时钟冲突解析器
pub struct VectorClockResolver;

impl ConflictResolver for VectorClockResolver {
    fn resolve_conflicts(&self, conflicting_versions: &[VersionedData]) -> VersionedData {
        if conflicting_versions.is_empty() {
            panic!("Cannot resolve conflicts with empty versions");
        }
        
        if conflicting_versions.len() == 1 {
            return conflicting_versions[0].clone();
        }
        
        // 尝试使用向量时钟确定因果顺序
        let mut causally_latest = Vec::new();
        
        for (i, version_a) in conflicting_versions.iter().enumerate() {
            let mut is_latest = true;
            
            for (j, version_b) in conflicting_versions.iter().enumerate() {
                if i == j {
                    continue;
                }
                
                // 检查B的向量时钟是否优于A
                let mut b_dominates_a = false;
                let mut a_dominates_b = false;
                
                for (node, &count_b) in &version_b.vector_clock {
                    let count_a = version_a.vector_clock.get(node).cloned().unwrap_or(0);
                    
                    if count_b > count_a {
                        b_dominates_a = true;
                    } else if count_a > count_b {
                        a_dominates_b = true;
                    }
                }
                
                // A的向量时钟中有，但B没有的节点
                for (node, &count_a) in &version_a.vector_clock {
                    if !version_b.vector_clock.contains_key(node) && count_a > 0 {
                        a_dominates_b = true;
                    }
                }
                
                // 如果B的向量时钟严格优于A的，那么A不是最新的
                if b_dominates_a && !a_dominates_b {
                    is_latest = false;
                    break;
                }
            }
            
            if is_latest {
                causally_latest.push(conflicting_versions[i].clone());
            }
        }
        
        // 如果有唯一的因果最新版本，返回它
        if causally_latest.len() == 1 {
            return causally_latest[0].clone();
        }
        
        // 存在多个并发修改，需要进一步解决冲突
        // 选择时间戳最新的版本
        causally_latest.sort_by_key(|v| std::cmp::Reverse(v.timestamp));
        
        // 返回时间戳最新的版本
        causally_latest[0].clone()
    }
    
    fn description(&self) -> &str {
        "Vector Clock Based Conflict Resolver"
    }
}

impl Clone for VersionedData {
    fn clone(&self) -> Self {
        Self {
            key: self.key.clone(),
            value: self.value.clone(),
            version: self.version,
            timestamp: self.timestamp,
            node_id: self.node_id.clone(),
            vector_clock: self.vector_clock.clone(),
        }
    }
}

// 基于租约的故障恢复处理器
pub struct LeaseBasedRecoveryHandler {
    lease_duration_ms: u64,
    lease_manager: Arc<LeaseManager>,
    description: String,
}

impl LeaseBasedRecoveryHandler {
    pub fn new(lease_duration_ms: u64, lease_manager: Arc<LeaseManager>, description: String) -> Self {
        Self {
            lease_duration_ms,
            lease_manager,
            description,
        }
    }
}

impl RecoveryHandler for LeaseBasedRecoveryHandler {
    fn handle_recovery(&self, node_id: &str, state: NodeState) -> Vec<RecoveryAction> {
        match state {
            NodeState::Failed => {
                // 对于完全故障的节点，检查是否持有租约
                if self.lease_manager.has_active_lease(node_id) {
                    // 等待租约过期或强制撤销租约
                    if self.lease_manager.revoke_lease(node_id).is_ok() {
                        // 故障转移和状态传输
                        vec![RecoveryAction::Failover, RecoveryAction::StateTransfer]
                    } else {
                        // 无法撤销租约，需要等待过期
                        vec![RecoveryAction::Restart]
                    }
                } else {
                    // 无租约，直接重启
                    vec![RecoveryAction::Restart]
                }
            },
            NodeState::Partitioned => {
                // 对于网络分区，尝试协调状态
                if self.lease_manager.has_active_lease(node_id) {
                    // 有租约，等待租约过期
                    vec![RecoveryAction::Reconcile]
                } else {
                    // 无租约，可以立即协调
                    vec![RecoveryAction::Reconcile]
                }
            },
            _ => Vec::new(), // 其他状态无需恢复
        }
    }
    
    fn description(&self) -> &str {
        &self.description
    }
}

// 租约管理器
pub struct LeaseManager {
    leases: RwLock<HashMap<String, Lease>>,
}

// 租约信息
struct Lease {
    holder: String,
    expires_at: Instant,
    resources: HashSet<String>,
}

impl LeaseManager {
    pub fn new() -> Self {
        Self {
            leases: RwLock::new(HashMap::new()),
        }
    }
    
    // 请求租约
    pub fn acquire_lease(
        &self,
        holder: &str,
        duration: Duration,
        resources: HashSet<String>,
    ) -> Result<(), LeaseError> {
        let mut leases = self.leases.write().unwrap();
        
        // 检查资源是否已被占用
        for resource in &resources {
            for lease in leases.values() {
                if lease.resources.contains(resource) && lease.expires_at > Instant::now() {
                    return Err(LeaseError::ResourceBusy);
                }
            }
        }
        
        // 创建新租约
        leases.insert(holder.to_string(), Lease {
            holder: holder.to_string(),
            expires_at: Instant::now() + duration,
            resources,
        });
        
        Ok(())
    }
    
    // 续租
    pub fn renew_lease(&self, holder: &str, duration: Duration) -> Result<(), LeaseError> {
        let mut leases = self.leases.write().unwrap();
        
        if let Some(lease) = leases.get_mut(holder) {
            lease.expires_at = Instant::now() + duration;
            Ok(())
        } else {
            Err(LeaseError::LeaseNotFound)
        }
    }
    
    // 释放租约
    pub fn release_lease(&self, holder: &str) -> Result<(), LeaseError> {
        let mut leases = self.leases.write().unwrap();
        
        if leases.remove(holder).is_some() {
            Ok(())
        } else {
            Err(LeaseError::LeaseNotFound)
        }
    }
    
    // 撤销租约（强制）
    pub fn revoke_lease(&self, holder: &str) -> Result<(), LeaseError> {
        let mut leases = self.leases.write().unwrap();
        
        if leases.remove(holder).is_some() {
            Ok(())
        } else {
            Err(LeaseError::LeaseNotFound)
        }
    }
    
    // 检查是否有活跃租约
    pub fn has_active_lease(&self, holder: &str) -> bool {
        let leases = self.leases.read().unwrap();
        
        if let Some(lease) = leases.get(holder) {
            lease.expires_at > Instant::now()
        } else {
            false
        }
    }
    
    // 清理过期租约
    pub fn cleanup_expired_leases(&self) {
        let mut leases = self.leases.write().unwrap();
        let now = Instant::now();
        
        leases.retain(|_, lease| lease.expires_at > now);
    }
}

// 租约错误
pub enum LeaseError {
    ResourceBusy,
    LeaseNotFound,
}
```

## 动态自适应运行时

### 自适应调度策略

自适应调度策略可以根据系统负载、资源利用率和任务特性动态调整任务执行计划。

```rust
// 自适应调度策略实现
use std::collections::{HashMap, HashSet, VecDeque, BinaryHeap};
use std::sync::{Arc, Mutex, RwLock};
use std::time::{Duration, Instant};
use std::cmp::Ordering;

// 资源类型
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum ResourceType {
    CPU,
    Memory,
    Disk,
    Network,
    GPU,
}

// 任务优先级
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum TaskPriority {
    Critical,
    High,
    Normal,
    Low,
    Background,
}

// 调度策略
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SchedulingPolicy {
    FIFO,               // 先入先出
    Priority,           // 优先级
    FairShare,          // 公平共享
    WeightedFair,       // 加权公平
    Deadline,           // 截止时间
    ResourceAware,      // 资源感知
    Hybrid,             // 混合策略
}

// 任务分配指标
#[derive(Clone)]
pub struct AllocationMetrics {
    waiting_time: Duration,        // 等待时间
    processing_time: Duration,     // 处理时间
    deadline: Option<Instant>,     // 截止时间
    priority: TaskPriority,        // 优先级
    resource_usage: HashMap<ResourceType, f64>, // 资源使用率
    locality_preference: Option<String>, // 局部性偏好
}

// 可调度任务
pub struct SchedulableTask<T> {
    id: String,
    task: T,
    metrics: AllocationMetrics,
    dependencies: HashSet<String>,
    submission_time: Instant,
}

// 为优先级队列实现比较
impl<T> Ord for SchedulableTask<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        // 首先按优先级排序
        match self.metrics.priority.cmp(&other.metrics.priority) {
            Ordering::Equal => {
                // 优先级相同时，比较截止时间
                if let (Some(self_deadline), Some(other_deadline)) = 
                    (self.metrics.deadline, other.metrics.deadline) {
                    self_deadline.cmp(&other_deadline)
                } else if self.metrics.deadline.is_some() {
                    Ordering::Less // 有截止时间的任务优先
                } else if other.metrics.deadline.is_some() {
                    Ordering::Greater
                } else {
                    // 无截止时间，比较等待时间
                    other.metrics.waiting_time.cmp(&self.metrics.waiting_time)
                }
            },
            other_ord => other_ord,
        }
    }
}

impl<T> PartialOrd for SchedulableTask<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> PartialEq for SchedulableTask<T> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl<T> Eq for SchedulableTask<T> {}

// 自适应调度器
pub struct AdaptiveScheduler<T> {
    current_policy: SchedulingPolicy,
    task_queue: Mutex<BinaryHeap<SchedulableTask<T>>>,
    completed_tasks: RwLock<HashMap<String, TaskExecutionResult>>,
    running_tasks: RwLock<HashMap<String, (String, Instant)>>, // 任务ID -> (执行节点, 开始时间)
    
    executors: HashMap<String, TaskExecutor<T>>,
    executor_metrics: RwLock<HashMap<String, ExecutorMetrics>>,
    
    policy_evaluator: Box<dyn PolicyEvaluator + Send + Sync>,
    scheduling_history: RwLock<VecDeque<SchedulingEvent>>,
}

// 任务执行结果
pub struct TaskExecutionResult {
    task_id: String,
    executor_id: String,
    start_time: Instant,
    completion_time: Instant,
    status: TaskStatus,
    metrics: ExecutionMetrics,
}

// 任务状态
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TaskStatus {
    Succeeded,
    Failed,
    Canceled,
    Timeout,
}

// 执行指标
#[derive(Clone)]
pub struct ExecutionMetrics {
    cpu_usage: f64,           // CPU使用率 (0-1)
    memory_usage: f64,        // 内存使用率 (0-1)
    disk_io: u64,             // 磁盘IO (bytes)
    network_io: u64,          // 网络IO (bytes)
    processing_time: Duration, // 处理时间
}

// 执行器指标
#[derive(Clone)]
pub struct ExecutorMetrics {
    total_tasks_processed: u64,
    success_rate: f64,
    avg_processing_time: Duration,
    current_load: HashMap<ResourceType, f64>,
    available_resources: HashMap<ResourceType, f64>,
    last_updated: Instant,
}

// 任务执行器
pub struct TaskExecutor<T> {
    id: String,
    executor: Box<dyn Fn(T) -> Result<T, TaskExecutionError> + Send + Sync>,
    capacity: HashMap<ResourceType, f64>,
}

// 执行错误
pub enum TaskExecutionError {
    ResourceExhausted,
    Timeout,
    ExecutionFailed(String),
    Interrupted,
}

// 调度事件
pub struct SchedulingEvent {
    timestamp: Instant,
    task_id: String,
    event_type: SchedulingEventType,
    executor_id: Option<String>,
}

// 调度事件类型
pub enum SchedulingEventType {
    Submitted,
    Scheduled,
    Started,
    Completed,
    Failed,
    Canceled,
}

// 策略评估器特征
pub trait PolicyEvaluator {
    fn evaluate_policies(
        &self,
        task_history: &[SchedulingEvent],
        executor_metrics: &HashMap<String, ExecutorMetrics>,
        system_load: f64,
    ) -> SchedulingPolicy;
    
    fn description(&self) -> &str;
}

impl<T: Clone + Send + 'static> AdaptiveScheduler<T> {
    pub fn new(
        initial_policy: SchedulingPolicy,
        executors: HashMap<String, TaskExecutor<T>>,
        policy_evaluator: Box<dyn PolicyEvaluator + Send + Sync>,
    ) -> Self {
        // 初始化执行器指标
        let mut executor_metrics = HashMap::new();
        for (id, executor) in &executors {
            executor_metrics.insert(id.clone(), ExecutorMetrics {
                total_tasks_processed: 0,
                success_rate: 1.0,
                avg_processing_time: Duration::from_secs(0),
                current_load: HashMap::new(),
                available_resources: executor.capacity.clone(),
                last_updated: Instant::now(),
            });
        }
        
        Self {
            current_policy: initial_policy,
            task_queue: Mutex::new(BinaryHeap::new()),
            completed_tasks: RwLock::new(HashMap::new()),
            running_tasks: RwLock::new(HashMap::new()),
            executors,
            executor_metrics: RwLock::new(executor_metrics),
            policy_evaluator,
            scheduling_history: RwLock::new(VecDeque::with_capacity(1000)),
        }
    }
    
    // 提交任务
    pub fn submit_task(
        &self,
        id: String,
        task: T,
        metrics: AllocationMetrics,
        dependencies: HashSet<String>,
    ) -> Result<(), SchedulingError> {
        let submission_time = Instant::now();
        
        // 创建可调度任务
        let schedulable_task = SchedulableTask {
            id: id.clone(),
            task,
            metrics,
            dependencies,
            submission_time,
        };
        
        // 添加到任务队列
        let mut task_queue = self.task_queue.lock().unwrap();
        task_queue.push(schedulable_task);
        
        // 记录调度事件
        let event = SchedulingEvent {
            timestamp: submission_time,
            task_id: id.clone(),
            event_type: SchedulingEventType::Submitted,
            executor_id: None,
        };
        
        self.record_scheduling_event(event);
        
        Ok(())
    }
    
    // 记录调度事件
    fn record_scheduling_event(&self, event: SchedulingEvent) {
        let mut history = self.scheduling_history.write().unwrap();
        history.push_back(event);
        
        // 保持历史记录大小限制
        if history.len() > 1000 {
            history.pop_front();
        }
    }
    
    // 调度任务
    pub fn schedule_tasks(&self) -> Vec<Result<String, SchedulingError>> {
        // 周期性重新评估调度策略
        self.reevaluate_policy();
        
        let mut results = Vec::new();
        
        // 获取就绪任务
        let ready_tasks = self.get_ready_tasks();
        
        // 根据当前策略对任务排序
        let sorted_tasks = self.sort_tasks_by_policy(ready_tasks);
        
        // 尝试为每个任务分配执行器
        for task in sorted_tasks {
            // 为任务选择最佳执行器
            match self.select_executor(&task) {
                Some(executor_id) => {
                    // 分配任务到执行器
                    match self.allocate_task(task, &executor_id) {
                        Ok(task_id) => {
                            results.push(Ok(task_id));
                            
                            // 记录调度事件
                            let event = SchedulingEvent {
                                timestamp: Instant::now(),
                                task_id: task_id.clone(),
                                event_type: SchedulingEventType::Scheduled,
                                executor_id: Some(executor_id.clone()),
                            };
                            
                            self.record_scheduling_event(event);
                        },
                        Err(err) => {
                            results.push(Err(err));
                        }
                    }
                },
                None => {
                    // 无法找到合适的执行器
                    results.push(Err(SchedulingError::NoSuitableExecutor));
                }
            }
        }
        
        results
    }
    
    // 获取就绪的任务（所有依赖已完成）
    fn get_ready_tasks(&self) -> Vec<SchedulableTask<T>> {
        let mut task_queue = self.task_queue.lock().unwrap();
        let completed_tasks = self.completed_tasks.read().unwrap();
        
        // 筛选出所有依赖已完成的任务
        let ready_tasks: Vec<_> = task_queue.iter()
            .filter(|task| {
                task.dependencies.iter().all(|dep_id| completed_tasks.contains_key(dep_id))
            })
            .cloned()
            .collect();
            
        // 从队列中移除就绪任务
        for ready_task in &ready_tasks {
            task_queue.iter()
                .position(|t| t.id == ready_task.id)
                .map(|i| task_queue.remove(i));
        }
        
        ready_tasks
    }
    
    // 根据当前策略对任务排序
    fn sort_tasks_by_policy(&self, mut tasks: Vec<SchedulableTask<T>>) -> Vec<SchedulableTask<T>> {
        match self.current_policy {
            SchedulingPolicy::FIFO => {
                // 按提交时间排序
                tasks.sort_by_key(|task| task.submission_time);
            },
            SchedulingPolicy::Priority => {
                // 按优先级排序
                tasks.sort_by(|a, b| a.metrics.priority.cmp(&b.metrics.priority));
            },
            SchedulingPolicy::Deadline => {
                // 按截止时间排序
                tasks.sort_by(|a, b| {
                    match (a.metrics.deadline, b.metrics.deadline) {
                        (Some(a_deadline), Some(b_deadline)) => a_deadline.cmp(&b_deadline),
                        (Some(_), None) => Ordering::Less,
                        (None, Some(_)) => Ordering::Greater,
                        (None, None) => a.submission_time.cmp(&b.submission_time),
                    }
                });
            },
            SchedulingPolicy::FairShare | SchedulingPolicy::WeightedFair => {
                // 按等待时间排序（公平共享）
                tasks.sort_by_key(|task| {
                    let waiting_time = Instant::now().duration_since(task.submission_time);
                    
                    if self.current_policy == SchedulingPolicy::WeightedFair {
                        // 加入优先级权重
                        let priority_weight = match task.metrics.priority {
                            TaskPriority::Critical => 4,
                            TaskPriority::High => 3,
                            TaskPriority::Normal => 2,
                            TaskPriority::Low => 1,
                            TaskPriority::Background => 0,
                        };
                        
                        // 等待时间乘以优先级权重
                        waiting_time.mul_f32(1.0 + (priority_weight as f32 * 0.25))
                    } else {
                        waiting_time
                    }
                });
            },
            SchedulingPolicy::ResourceAware => {
                // 根据资源利用率排序
                let executor_metrics = self.executor_metrics.read().unwrap();
                
                tasks.sort_by(|a, b| {
                    // 计算每个任务的资源匹配度
                    let a_score = self.calculate_resource_fit(a, &executor_metrics);
                    let b_score = self.calculate_resource_fit(b, &executor_metrics);
                    
                    // 资源匹配度越高越优先
                    b_score.partial_cmp(&a_score).unwrap_or(Ordering::Equal)
                });
            },
            SchedulingPolicy::Hybrid => {
                // 混合策略：综合考虑优先级、等待时间、截止时间和资源利用率
                let executor_metrics = self.executor_metrics.read().unwrap();
                
                tasks.sort_by(|a, b| {
                    // 计算混合得分
                    let a_score = self.calculate_hybrid_score(a, &executor_metrics);
                    let b_score = self.calculate_hybrid_score(b, &executor_metrics);
                    
                    // 得分越高越优先
                    b_score.partial_cmp(&a_score).unwrap_or(Ordering::Equal)
                });
            },
        }
        
        tasks
    }
    
    // 计算任务的资源匹配度
    fn calculate_resource_fit(
        &self,
        task: &SchedulableTask<T>,
        executor_metrics: &HashMap<String, ExecutorMetrics>,
    ) -> f64 {
        let mut best_fit = 0.0;
        
        for (_, executor_metric) in executor_metrics {
            let mut fit_score = 0.0;
            let mut resource_count = 0;
            
            for (resource_type, usage) in &task.metrics.resource_usage {
                if let Some(available) = executor_metric.available_resources.get(resource_type) {
                    // 资源充足度：1.0表示完全充足，0.0表示不足
                    let resource_fit = if *available >= *usage {
                        1.0
                    } else {
                        *available / *usage
                    };
                    
                    fit_score += resource_fit;
                    resource_count += 1;
                }
            }
            
            if resource_count > 0 {
                let avg_fit = fit_score / resource_count as f64;
                best_fit = best_fit.max(avg_fit);
            }
        }
        
        best_fit
    }
    
    // 计算任务的混合策略得分
    fn calculate_hybrid_score(
        &self,
        task: &SchedulableTask<T>,
        executor_metrics: &HashMap<String, ExecutorMetrics>,
    ) -> f64 {
        // 资源匹配度 (0.0-1.0)
        let resource_fit = self.calculate_resource_fit(task, executor_metrics);
        
        // 优先级分数 (0.0-1.0)
        let priority_score = match task.metrics.priority {
            TaskPriority::Critical => 1.0,
            TaskPriority::High => 0.8,
            TaskPriority::Normal => 0.6,
            TaskPriority::Low => 0.4,
            TaskPriority::Background => 0.2,
        };
        
        // 等待时间分数 (0.0-1.0)
        let wait_time = Instant::now().duration_since(task.submission_time);
        let wait_score = (wait_time.as_secs_f64() / 3600.0).min(1.0); // 归一化，最大1小时
        
        // 截止时间紧迫度 (0.0-1.0)
        let deadline_score = if let Some(deadline) = task.metrics.deadline {
            let time_left = deadline.duration_since(Instant::now());
            let urgency = 1.0 - (time_left.as_secs_f64() / 3600.0).min(1.0);
            urgency.max(0.0)
        } else {
            0.5 // 默认中等紧迫度
        };
        
        // 混合得分：加权组合各因素
        resource_fit * 0.3 + priority_score * 0.3 + wait_score * 0.2 + deadline_score * 0.2
    }
    
    // 为任务选择最佳执行器
    fn select_executor(&self, task: &SchedulableTask<T>) -> Option<String> {
        let executor_metrics = self.executor_metrics.read().unwrap();
        
        let mut best_executor_id = None;
        let mut best_score = 0.0;
        
        for (executor_id, metrics) in &*executor_metrics {
            // 检查是否有足够的资源
            let has_sufficient_resources = task.metrics.resource_usage.iter().all(|(res_type, usage)| {
                if let Some(available) = metrics.available_resources.get(res_type) {
                    *available >= *usage
                } else {
                    true // 如果执行器没有报告该资源类型，假设资源充足
                }
            });
            
            if !has_sufficient_resources {
                continue;
            }
            
            // 计算执行器得分
            let mut score = 0.0;
            
            // 1. 资源匹配度
            let mut resource_fit = 0.0;
            let mut resource_count = 0;
            
            for (res_type, usage) in &task.metrics.resource_usage {
                if let Some(available) = metrics.available_resources.get(res_type) {
                    // 资源余量比例（越接近使用量越好，但不能小于使用量）
                    let fit = if *available >= *usage {
                        let excess = (*available - *usage) / *usage;
                        1.0 / (1.0 + excess) // 归一化为0-1，越接近1越好
                    } else {
                        0.0 // 资源不足
                    };
                    
                    resource_fit += fit;
                    resource_count += 1;
                }
            }
            
            if resource_count > 0 {
                score += resource_fit / resource_count as f64 * 0.4; // 资源匹配度权重0.4
            }
            
            // 2. 历史成功率
            score += metrics.success_rate * 0.2; // 成功率权重0.2
            
            // 3. 当前负载
            let avg_load = metrics.current_load.values().sum::<f64>() / 
                           metrics.current_load.len().max(1) as f64;
            score += (1.0 - avg_load) * 0.2; // 负载权重0.2
            
            // 4. 局部性偏好
            if let Some(preferred_executor) = &task.metrics.locality_preference {
                if preferred_executor == executor_id {
                    score += 0.2; // 局部性匹配加分0.2
                }
            }
            
            // 更新最佳执行器
            if score > best_score {
                best_score = score;
                best_executor_id = Some(executor_id.clone());
            }
        }
        
        best_executor_id
    }
    
    // 分配任务到执行器
    fn allocate_task(&self, task: SchedulableTask<T>, executor_id: &str) -> Result<String, SchedulingError> {
        // 获取执行器
        let executor = self.executors.get(executor_id)
            .ok_or(SchedulingError::ExecutorNotFound)?;
            
        // 更新执行器指标
        {
            let mut metrics = self.executor_metrics.write().unwrap();
            if let Some(executor_metrics) = metrics.get_mut(executor_id) {
                // 更新资源使用情况
                for (res_type, usage) in &task.metrics.resource_usage {
                    let current = executor_metrics.current_load.entry(*res_type).or_insert(0.0);
                    *current += *usage;
                    
                    let available = executor_metrics.available_resources.entry(*res_type).or_insert(0.0);
                    *available -= *usage;
                }
                
                executor_metrics.last_updated = Instant::now();
            }
        }
        
        // 记录运行任务
        {
            let mut running_tasks = self.running_tasks.write().unwrap();
            running_tasks.insert(task.id.clone(), (executor_id.to_string(), Instant::now()));
        }
        
        // 在新线程中执行任务
        let task_id = task.id.clone();
        let executor_fn = executor.executor.clone();
        let task_data = task.task;
        let scheduler = Arc::new(self.clone());
        
        std::thread::spawn(move || {
            // 记录开始执行事件
            let start_time = Instant::now();
            scheduler.record_scheduling_event(SchedulingEvent {
                timestamp: start_time,
                task_id: task_id.clone(),
                event_type: SchedulingEventType::Started,
                executor_id: Some(executor_id.to_string()),
            });
            
            // 执行任务
            let result = executor_fn(task_data);
            let completion_time = Instant::now();
            
            // 处理执行结果
            match result {
                Ok(_) => {
                    // 任务成功完成
                    scheduler.task_completed(
                        &task_id, 
                        executor_id,
                        start_time,
                        completion_time,
                        TaskStatus::Succeeded,
                    );
                },
                Err(err) => {
                    // 任务执行失败
                    let status = match err {
                        TaskExecutionError::Timeout => TaskStatus::Timeout,
                        TaskExecutionError::Interrupted => TaskStatus::Canceled,
                        _ => TaskStatus::Failed,
                    };
                    
                    scheduler.task_completed(
                        &task_id,
                        executor_id,
                        start_time,
                        completion_time,
                        status,
                    );
                }
            }
        });
        
        Ok(task.id)
    }
    
    // 任务完成处理
    fn task_completed(
        &self,
        task_id: &str,
        executor_id: &str,
        start_time: Instant,
        completion_time: Instant,
        status: TaskStatus,
    ) {
        // 更新运行任务列表
        let mut running_tasks = self.running_tasks.write().unwrap();
        running_tasks.remove(task_id);
        
        // 创建执行指标
        let processing_time = completion_time.duration_since(start_time);
        let metrics = ExecutionMetrics {
            cpu_usage: 0.5,  // 简化：使用固定值
            memory_usage: 0.3, // 简化：使用固定值
            disk_io: 1024,   // 简化：使用固定值
            network_io: 512, // 简化：使用固定值
            processing_time,
        };
        
        // 更新已完成任务
        let mut completed_tasks = self.completed_tasks.write().unwrap();
        completed_tasks.insert(task_id.to_string(), TaskExecutionResult {
            task_id: task_id.to_string(),
            executor_id: executor_id.to_string(),
            start_time,
            completion_time,
            status,
            metrics: metrics.clone(),
        });
        
        // 更新执行器指标
        {
            let mut executor_metrics = self.executor_metrics.write().unwrap();
            if let Some(metrics_data) = executor_metrics.get_mut(executor_id) {
                // 更新任务计数
                metrics_data.total_tasks_processed += 1;
                
                // 更新成功率
                let success_factor = if status == TaskStatus::Succeeded { 1.0 } else { 0.0 };
                metrics_data.success_rate = metrics_data.success_rate * 0.9 + success_factor * 0.1;
                
                // 更新平均处理时间（使用滑动平均）
                let old_avg = metrics_data.avg_processing_time;
                metrics_data.avg_processing_time = old_avg.mul_f32(0.9) + processing_time.mul_f32(0.1);
                
                // 恢复资源
                // 这里简化处理，实际系统需要获取真实资源使用情况
                if let Some(task_metrics) = self.get_task_metrics(task_id) {
                    for (res_type, usage) in &task_metrics.resource_usage {
                        let current = metrics_data.current_load.entry(*res_type).or_insert(0.0);
                        *current = (*current - *usage).max(0.0);
                        
                        let available = metrics_data.available_resources.entry(*res_type).or_insert(0.0);
                        *available += *usage;
                    }
                }
                
                metrics_data.last_updated = Instant::now();
            }
        }
        
        // 记录完成事件
        let event_type = if status == TaskStatus::Succeeded {
            SchedulingEventType::Completed
        } else {
            SchedulingEventType::Failed
        };
        
        self.record_scheduling_event(SchedulingEvent {
            timestamp: completion_time,
            task_id: task_id.to_string(),
            event_type,
            executor_id: Some(executor_id.to_string()),
        });
    }
    
    // 获取任务指标（已完成任务的队列中）
    fn get_task_metrics(&self, task_id: &str) -> Option<AllocationMetrics> {
        // 在实际系统中，应该从任务存储中查询任务信息
        // 这里简化返回默认指标
        Some(AllocationMetrics {
            waiting_time: Duration::from_secs(0),
            processing_time: Duration::from_secs(0),
            deadline: None,
            priority: TaskPriority::Normal,
            resource_usage: {
                let mut usage = HashMap::new();
                usage.insert(ResourceType::CPU, 0.1);
                usage.insert(ResourceType::Memory, 128.0);
                usage
            },
            locality_preference: None,
        })
    }
    
    // 重新评估调度策略
    fn reevaluate_policy(&self) {
        // 获取系统负载
        let system_load = self.calculate_system_load();
        
        // 获取调度历史
        let history = self.scheduling_history.read().unwrap();
        let recent_events: Vec<_> = history.iter().cloned().collect();
        
        // 获取执行器指标
        let executor_metrics = self.executor_metrics.read().unwrap();
        let metrics_snapshot = executor_metrics.clone();
        
        // 使用策略评估器评估最佳策略
        let best_policy = self.policy_evaluator.evaluate_policies(
            &recent_events,
            &metrics_snapshot,
            system_load,
        );
        
        // 更新当前策略
        if best_policy != self.current_policy {
            println!("Switching scheduling policy from {:?} to {:?}", 
                     self.current_policy, best_policy);
            self.current_policy = best_policy;
        }
    }
    
    // 计算系统总负载
    fn calculate_system_load(&self) -> f64 {
        let executor_metrics = self.executor_metrics.read().unwrap();
        let mut total_load = 0.0;
        let mut executor_count = 0;
        
        for metrics in executor_metrics.values() {
            let cpu_load = metrics.current_load.get(&ResourceType::CPU).cloned().unwrap_or(0.0);
            total_load += cpu_load;
            executor_count += 1;
        }
        
        if executor_count > 0 {
            total_load / executor_count as f64
        } else {
            0.0
        }
    }
}

// 调度错误
pub enum SchedulingError {
    TaskAlreadyExists,
    TaskNotFound,
    ExecutorNotFound,
    ResourceExhausted,
    NoSuitableExecutor,
}

// 实现Clone以支持线程间共享
impl<T: Clone> Clone for AdaptiveScheduler<T> {
    fn clone(&self) -> Self {
        Self {
            current_policy: self.current_policy,
            task_queue: Mutex::new(self.task_queue.lock().unwrap().clone()),
            completed_tasks: RwLock::new(self.completed_tasks.read().unwrap().clone()),
            running_tasks: RwLock::new(self.running_tasks.read().unwrap().clone()),
            executors: self.executors.clone(),
            executor_metrics: RwLock::new(self.executor_metrics.read().unwrap().clone()),
            policy_evaluator: self.policy_evaluator.clone_box(),
            scheduling_history: RwLock::new(self.scheduling_history.read().unwrap().clone()),
        }
    }
}

// 支持策略评估器的Clone
pub trait CloneBox {
    fn clone_box(&self) -> Box<dyn PolicyEvaluator + Send + Sync>;
}

impl<T> CloneBox for T 
where
    T: 'static + PolicyEvaluator + Clone + Send + Sync
{
    fn clone_box(&self) -> Box<dyn PolicyEvaluator + Send + Sync> {
        Box::new(self.clone())
    }
}

impl Clone for Box<dyn PolicyEvaluator + Send + Sync> {
    fn clone(&self) -> Self {
        self.clone_box()
    }
}

// 负载感知策略评估器
#[derive(Clone)]
pub struct LoadAwarePolicyEvaluator {
    low_load_policy: SchedulingPolicy,
    medium_load_policy: SchedulingPolicy,
    high_load_policy: SchedulingPolicy,
    description: String,
}

impl LoadAwarePolicyEvaluator {
    pub fn new(
        low_load_policy: SchedulingPolicy,
        medium_load_policy: SchedulingPolicy,
        high_load_policy: SchedulingPolicy,
        description: String,
    ) -> Self {
        Self {
            low_load_policy,
            medium_load_policy,
            high_load_policy,
            description,
        }
    }
}

impl PolicyEvaluator for LoadAwarePolicyEvaluator {
    fn evaluate_policies(
        &self,
        _task_history: &[SchedulingEvent],
        _executor_metrics: &HashMap<String, ExecutorMetrics>,
        system_load: f64,
    ) -> SchedulingPolicy {
        // 根据系统负载选择策略
        if system_load < 0.3 {
            self.low_load_policy
        } else if system_load < 0.7 {
            self.medium_load_policy
        } else {
            self.high_load_policy
        }
    }
    
    fn description(&self) -> &str {
        &self.description
    }
}
```

### 资源感知执行

资源感知执行可以根据任务特性和资源可用性动态调整任务执行策略，提高资源利用率。

```rust
// 资源感知执行实现
use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::{Arc, Mutex, RwLock};
use std::time::{Duration, Instant};

// 资源种类
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum ResourceKind {
    CPU,
    Memory,
    Disk,
    Network,
    GPU,
    FPGA,
    TPU,
    Bandwidth,
    ConnectionCount,
}

// 资源要求
#[derive(Clone)]
pub struct ResourceRequirements {
    min_resources: HashMap<ResourceKind, f64>,  // 最小资源需求
    recommended: HashMap<ResourceKind, f64>,    // 推荐资源配置
    elastic: bool,                              // 是否弹性资源需求
    scalability_factor: f64,                    // 可伸缩性因子(0-1)
}

// 资源可用性
#[derive(Clone)]
pub struct ResourceAvailability {
    total: HashMap<ResourceKind, f64>,          // 总资源量
    available: HashMap<ResourceKind, f64>,      // 可用资源量
    reserved: HashMap<ResourceKind, f64>,       // 预留资源量
    last_updated: Instant,                      // 最后更新时间
}

// 资源利用率历史
#[derive(Clone)]
pub struct ResourceUtilizationHistory {
    samples: VecDeque<(ResourceKind, f64, Instant)>, // 资源类型、使用率、时间戳
    max_samples: usize,                             // 最大样本数
}

impl ResourceUtilizationHistory {
    pub fn new(max_samples: usize) -> Self {
        Self {
            samples: VecDeque::with_capacity(max_samples),
            max_samples,
        }
    }
    
    pub fn add_sample(&mut self, kind: ResourceKind, utilization: f64) {
        self.samples.push_back((kind, utilization, Instant::now()));
        
        while self.samples.len() > self.max_samples {
            self.samples.pop_front();
        }
    }
    
    pub fn get_average_utilization(&self, kind: ResourceKind, window: Duration) -> Option<f64> {
        let now = Instant::now();
        let window_start = now.checked_sub(window)?;
        
        let relevant_samples: Vec<_> = self.samples.iter()
            .filter(|(k, _, timestamp)| *k == kind && *timestamp >= window_start)
            .collect();
            
        if relevant_samples.is_empty() {
            return None;
        }
        
        let sum: f64 = relevant_samples.iter().map(|(_, util, _)| *util).sum();
        Some(sum / relevant_samples.len() as f64)
    }
}

// 资源感知执行器
pub struct ResourceAwareExecutor<T> {
    id: String,
    resource_availability: RwLock<ResourceAvailability>,
    utilization_history: RwLock<ResourceUtilizationHistory>,
    running_tasks: RwLock<HashMap<String, (T, ResourceAllocation)>>,
    resource_monitors: Vec<Box<dyn ResourceMonitor + Send + Sync>>,
    scaling_strategies: HashMap<ResourceKind, Box<dyn ResourceScalingStrategy + Send + Sync>>,
}

// 资源分配
#[derive(Clone)]
pub struct ResourceAllocation {
    allocated: HashMap<ResourceKind, f64>,  // 分配的资源量
    allocation_time: Instant,               // 分配时间
    adjustable: bool,                       // 是否可调整
}

// 资源监控器特征
pub trait ResourceMonitor {
    fn get_resource_utilization(&self, kind: ResourceKind) -> Option<f64>;
    fn get_total_resources(&self, kind: ResourceKind) -> Option<f64>;
    fn get_available_resources(&self, kind: ResourceKind) -> Option<f64>;
    fn resource_kinds(&self) -> HashSet<ResourceKind>;
}

// 资源伸缩策略特征
pub trait ResourceScalingStrategy {
    fn should_scale_up(&self, utilization: f64, history: &ResourceUtilizationHistory) -> bool;
    fn should_scale_down(&self, utilization: f64, history: &ResourceUtilizationHistory) -> bool;
    fn get_scale_factor(&self, utilization: f64) -> f64;
    fn resource_kind(&self) -> ResourceKind;
}

impl<T: Clone + Send + Sync + 'static> ResourceAwareExecutor<T> {
    pub fn new(
        id: String,
        initial_resources: HashMap<ResourceKind, f64>,
        max_history_samples: usize,
    ) -> Self {
        let resource_availability = ResourceAvailability {
            total: initial_resources.clone(),
            available: initial_resources.clone(),
            reserved: HashMap::new(),
            last_updated: Instant::now(),
        };
        
        Self {
            id,
            resource_availability: RwLock::new(resource_availability),
            utilization_history: RwLock::new(ResourceUtilizationHistory::new(max_history_samples)),
            running_tasks: RwLock::new(HashMap::new()),
            resource_monitors: Vec::new(),
            scaling_strategies: HashMap::new(),
        }
    }
    
    // 添加资源监控器
    pub fn add_resource_monitor(&mut self, monitor: Box<dyn ResourceMonitor + Send + Sync>) {
        self.resource_monitors.push(monitor);
    }
    
    // 添加资源伸缩策略
    pub fn add_scaling_strategy(
        &mut self,
        kind: ResourceKind,
        strategy: Box<dyn ResourceScalingStrategy + Send + Sync>,
    ) {
        self.scaling_strategies.insert(kind, strategy);
    }
    
    // 检查资源是否足够
    pub fn has_sufficient_resources(&self, requirements: &ResourceRequirements) -> bool {
        let availability = self.resource_availability.read().unwrap();
        
        for (kind, required) in &requirements.min_resources {
            if let Some(available) = availability.available.get(kind) {
                if available < required {
                    return false;
                }
            } else {
                return false; // 没有该类型的资源
            }
        }
        
        true
    }
    
    // 分配资源
    pub fn allocate_resources(
        &self,
        task_id: &str,
        task: T,
        requirements: &ResourceRequirements,
    ) -> Result<ResourceAllocation, ResourceError> {
        // 检查资源是否足够
        if !self.has_sufficient_resources(requirements) {
            return Err(ResourceError::InsufficientResources);
        }
        
        let mut allocation = ResourceAllocation {
            allocated: HashMap::new(),
            allocation_time: Instant::now(),
            adjustable: requirements.elastic,
        };
        
        // 分配资源
        {
            let mut availability = self.resource_availability.write().unwrap();
            
            // 优先尝试分配推荐资源量
            for (kind, recommended) in &requirements.recommended {
                let available = availability.available.get_mut(kind)
                    .ok_or(ResourceError::ResourceNotAvailable)?;
                    
                let min_required = requirements.min_resources.get(kind)
                    .ok_or(ResourceError::InvalidResourceRequest)?;
                
                // 分配资源（在最小需求和推荐量之间）
                let allocate_amount = (*available).min(*recommended).max(*min_required);
                *available -= allocate_amount;
                
                allocation.allocated.insert(*kind, allocate_amount);
            }
            
            // 处理推荐中没有但最小需求中有的资源
            for (kind, min_required) in &requirements.min_resources {
                if !allocation.allocated.contains_key(kind) {
                    let available = availability.available.get_mut(kind)
                        .ok_or(ResourceError::ResourceNotAvailable)?;
                        
                    if *available < *min_required {
                        // 回滚已分配的资源
                        for (k, amount) in &allocation.allocated {
                            if let Some(avail) = availability.available.get_mut(k) {
                                *avail += *amount;
                            }
                        }
                        
                        return Err(ResourceError::InsufficientResources);
                    }
                    
                    *available -= *min_required;
                    allocation.allocated.insert(*kind, *min_required);
                }
            }
        }
        
        // 记录分配
        let mut running_tasks = self.running_tasks.write().unwrap();
        running_tasks.insert(task_id.to_string(), (task, allocation.clone()));
        
        Ok(allocation)
    }
    
    // 释放资源
    pub fn release_resources(&self, task_id: &str) -> Result<(), ResourceError> {
        let mut running_tasks = self.running_tasks.write().unwrap();
        
        if let Some((_, allocation)) = running_tasks.remove(task_id) {
            let mut availability = self.resource_availability.write().unwrap();
            
            // 归还资源
            for (kind, amount) in &allocation.allocated {
                if let Some(available) = availability.available.get_mut(kind) {
                    *available += *amount;
                }
            }
            
            Ok(())
        } else {
            Err(ResourceError::TaskNotFound)
        }
    }
    
    // 动态调整任务资源
    pub fn adjust_task_resources(
        &self,
        task_id: &str,
        adjustment: &HashMap<ResourceKind, f64>,
    ) -> Result<ResourceAllocation, ResourceError> {
        let mut running_tasks = self.running_tasks.write().unwrap();
        
        if let Some((task, mut allocation)) = running_tasks.remove(task_id) {
            if !allocation.adjustable {
                running_tasks.insert(task_id.to_string(), (task, allocation.clone()));
                return Err(ResourceError::ResourceNotAdjustable);
            }
            
            let mut availability = self.resource_availability.write().unwrap();
            let mut new_allocation = allocation.clone();
            
            // 处理增加资源
            for (kind, delta) in adjustment {
                if *delta > 0.0 {
                    // 检查是否有足够的资源增加
                    let available = availability.available.get_mut(kind)
                        .ok_or(ResourceError::ResourceNotAvailable)?;
                        
                    if *available < *delta {
                        // 资源不足，无法增加
                        running_tasks.insert(task_id.to_string(), (task, allocation));
                        return Err(ResourceError::InsufficientResources);
                    }
                    
                    // 增加资源
                    *available -= *delta;
                    let current = new_allocation.allocated.entry(*kind).or_insert(0.0);
                    *current += *delta;
                }
            }
            
            // 处理减少资源
            for (kind, delta) in adjustment {
                if *delta < 0.0 {
                    let allocated = new_allocation.allocated.get_mut(kind)
                        .ok_or(ResourceError::ResourceNotAllocated)?;
                        
                    // 确保不减少到负值
                    let reduce_amount = (*allocated + *delta).max(0.0) - *allocated;
                    
                    // 更新分配和可用资源
                    *allocated += reduce_amount; // reduce_amount是负值
                    
                    if let Some(available) = availability.available.get_mut(kind) {
                        *available -= reduce_amount; // 增加可用资源（减去负值）
                    }
                }
            }
            
            // 更新任务记录
            running_tasks.insert(task_id.to_string(), (task, new_allocation.clone()));
            
            Ok(new_allocation)
        } else {
            Err(ResourceError::TaskNotFound)
        }
    }
    
    // 更新资源利用率
    pub fn update_resource_utilization(&self) {
        // 收集各监控器报告的资源利用率
        let mut utilization_data: HashMap<ResourceKind, Vec<f64>> = HashMap::new();
        
        for monitor in &self.resource_monitors {
            for kind in monitor.resource_kinds() {
                if let Some(utilization) = monitor.get_resource_utilization(kind) {
                    utilization_data.entry(kind).or_insert_with(Vec::new).push(utilization);
                }
            }
        }
        
        // 计算每种资源的平均利用率
        let average_utilization: HashMap<ResourceKind, f64> = utilization_data.iter()
            .map(|(kind, values)| {
                let avg = values.iter().sum::<f64>() / values.len() as f64;
                (*kind, avg)
            })
            .collect();
            
        // 更新利用率历史
        let mut history = self.utilization_history.write().unwrap();
        for (kind, utilization) in &average_utilization {
            history.add_sample(*kind, *utilization);
        }
        
        // 更新资源可用性
        {
            let mut availability = self.resource_availability.write().unwrap();
            availability.last_updated = Instant::now();
            
            // 更新总资源量（可能随时间变化）
            for monitor in &self.resource_monitors {
                for kind in monitor.resource_kinds() {
                    if let Some(total) = monitor.get_total_resources(kind) {
                        availability.total.insert(kind, total);
                    }
                    
                    if let Some(available) = monitor.get_available_resources(kind) {
                        // 这里可能需要小心处理，因为我们正在追踪分配的资源
                        // 可能需要保证 available + allocated = total
                        availability.available.insert(kind, available);
                    }
                }
            }
        }
        
        // 检查是否需要根据利用率调整资源
        self.check_resource_scaling(&average_utilization);
    }
    
    // 检查是否需要根据利用率调整资源
    fn check_resource_scaling(&self, utilization: &HashMap<ResourceKind, f64>) {
        let history = self.utilization_history.read().unwrap();
        
        for (kind, strategy) in &self.scaling_strategies {
            if let Some(&current_utilization) = utilization.get(kind) {
                // 检查是否需要扩容
                if strategy.should_scale_up(current_utilization, &history) {
                    let scale_factor = strategy.get_scale_factor(current_utilization);
                    self.scale_up_resource(*kind, scale_factor);
                }
                
                // 检查是否需要缩容
                if strategy.should_scale_down(current_utilization, &history) {
                    let scale_factor = strategy.get_scale_factor(current_utilization);
                    self.scale_down_resource(*kind, scale_factor);
                }
            }
        }
    }
    
    // 扩容资源
    fn scale_up_resource(&self, kind: ResourceKind, factor: f64) {
        println!("Scaling up resource {:?} by factor {}", kind, factor);
        
        // 在实际系统中，这里可能涉及到与基础设施交互来获取更多资源
        // 简化实现：仅记录扩容意图
        
        // 在云环境中可能是请求更多的VM或容器
        // 在边缘设备可能是动态调整优先级或请求临时超额配置
    }
    
    // 缩容资源
    fn scale_down_resource(&self, kind: ResourceKind, factor: f64) {
        println!("Scaling down resource {:?} by factor {}", kind, factor);
        
        // 在实际系统中，这里可能涉及到释放或停用部分资源
        // 简化实现：仅记录缩容意图
        
        // 首先需要检查是否有任务正在使用这些资源
        let running_tasks = self.running_tasks.read().unwrap();
        let total_allocated: f64 = running_tasks.values()
            .filter_map(|(_, allocation)| allocation.allocated.get(&kind))
            .sum();
            
        let mut availability = self.resource_availability.write().unwrap();
        
        if let (Some(total), Some(available)) = (availability.total.get_mut(&kind), availability.available.get(&kind)) {
            // 计算当前未使用的资源量
            let unused = *available;
            
            // 计算可以安全释放的资源量
            let safe_to_release = unused * factor;
            
            if safe_to_release > 0.0 {
                // 减少总资源量
                *total -= safe_to_release;
                
                // 确保 available 不变（因为我们只释放未使用的资源）
                // 如果需要释放正在使用的资源，需要迁移或终止任务
            }
        }
    }
    
    // 获取任务运行状态
    pub fn get_task_status(&self, task_id: &str) -> Option<TaskResourceStatus> {
        let running_tasks = self.running_tasks.read().unwrap();
        
        running_tasks.get(task_id).map(|(_, allocation)| {
            let now = Instant::now();
            let running_time = now.duration_since(allocation.allocation_time);
            
            TaskResourceStatus {
                allocated_resources: allocation.allocated.clone(),
                running_time,
                adjustable: allocation.adjustable,
            }
        })
    }
    
    // 提供任务资源使用建议
    pub fn suggest_resource_adjustment(&self, task_id: &str) -> Option<HashMap<ResourceKind, f64>> {
        let running_tasks = self.running_tasks.read().unwrap();
        
        if let Some((_, allocation)) = running_tasks.get(task_id) {
            if !allocation.adjustable {
                return None; // 不可调整的任务
            }
            
            let mut suggestions = HashMap::new();
            let history = self.utilization_history.read().unwrap();
            
            // 检查每种资源的历史利用率
            for (kind, allocated) in &allocation.allocated {
                if let Some(avg_util) = history.get_average_utilization(*kind, Duration::from_secs(60)) {
                    // 资源利用率过低，建议减少
                    if avg_util < 0.3 {
                        let reduction = allocated * 0.2; // 减少20%
                        suggestions.insert(*kind, -reduction);
                    }
                    // 资源利用率过高，建议增加
                    else if avg_util > 0.8 {
                        let increase = allocated * 0.3; // 增加30%
                        suggestions.insert(*kind, increase);
                    }
                }
            }
            
            if !suggestions.is_empty() {
                Some(suggestions)
            } else {
                None
            }
        } else {
            None
        }
    }
    
    // 获取资源利用率报告
    pub fn get_utilization_report(&self) -> ResourceUtilizationReport {
        let history = self.utilization_history.read().unwrap();
        let availability = self.resource_availability.read().unwrap();
        
        let mut current_utilization = HashMap::new();
        let mut avg_utilization_1min = HashMap::new();
        let mut avg_utilization_5min = HashMap::new();
        let mut avg_utilization_15min = HashMap::new();
        
        // 计算当前和历史平均利用率
        for kind in ResourceKind::all() {
            // 从监控器获取当前利用率
            let current = self.resource_monitors.iter()
                .filter_map(|m| m.get_resource_utilization(kind))
                .next();
                
            if let Some(util) = current {
                current_utilization.insert(kind, util);
            }
            
            // 计算不同时间窗口的平均利用率
            if let Some(avg_1min) = history.get_average_utilization(kind, Duration::from_secs(60)) {
                avg_utilization_1min.insert(kind, avg_1min);
            }
            
            if let Some(avg_5min) = history.get_average_utilization(kind, Duration::from_secs(300)) {
                avg_utilization_5min.insert(kind, avg_5min);
            }
            
            if let Some(avg_15min) = history.get_average_utilization(kind, Duration::from_secs(900)) {
                avg_utilization_15min.insert(kind, avg_15min);
            }
        }
        
        ResourceUtilizationReport {
            timestamp: Instant::now(),
            current_utilization,
            avg_utilization_1min,
            avg_utilization_5min,
            avg_utilization_15min,
            total_resources: availability.total.clone(),
            available_resources: availability.available.clone(),
        }
    }
}

// 资源错误
pub enum ResourceError {
    InsufficientResources,
    ResourceNotAvailable,
    InvalidResourceRequest,
    TaskNotFound,
    ResourceNotAllocated,
    ResourceNotAdjustable,
}

// 任务资源状态
pub struct TaskResourceStatus {
    allocated_resources: HashMap<ResourceKind, f64>,
    running_time: Duration,
    adjustable: bool,
}

// 资源利用率报告
pub struct ResourceUtilizationReport {
    timestamp: Instant,
    current_utilization: HashMap<ResourceKind, f64>,
    avg_utilization_1min: HashMap<ResourceKind, f64>,
    avg_utilization_5min: HashMap<ResourceKind, f64>,
    avg_utilization_15min: HashMap<ResourceKind, f64>,
    total_resources: HashMap<ResourceKind, f64>,
    available_resources: HashMap<ResourceKind, f64>,
}

// 为ResourceKind添加便利方法
impl ResourceKind {
    pub fn all() -> Vec<ResourceKind> {
        vec![
            ResourceKind::CPU,
            ResourceKind::Memory,
            ResourceKind::Disk,
            ResourceKind::Network,
            ResourceKind::GPU,
            ResourceKind::FPGA,
            ResourceKind::TPU,
            ResourceKind::Bandwidth,
            ResourceKind::ConnectionCount,
        ]
    }
}

// 系统资源监控器实现
pub struct SystemResourceMonitor {
    refresh_interval: Duration,
    last_refresh: Instant,
    current_utilization: HashMap<ResourceKind, f64>,
    total_resources: HashMap<ResourceKind, f64>,
}

impl SystemResourceMonitor {
    pub fn new(refresh_interval: Duration) -> Self {
        let mut total_resources = HashMap::new();
        
        // 初始化系统资源信息（简化实现）
        total_resources.insert(ResourceKind::CPU, num_cpus::get() as f64);
        total_resources.insert(ResourceKind::Memory, 16.0 * 1024.0); // 16GB
        
        Self {
            refresh_interval,
            last_refresh: Instant::now(),
            current_utilization: HashMap::new(),
            total_resources,
        }
    }
    
    // 刷新资源利用率数据
    fn refresh(&mut self) {
        let now = Instant::now();
        
        if now.duration_since(self.last_refresh) < self.refresh_interval {
            return; // 尚未到达刷新间隔
        }
        
        self.last_refresh = now;
        
        // 在实际系统中，这里会使用系统API获取资源利用率
        // 简化实现：使用随机值模拟
        
        // CPU利用率 (0-1)
        self.current_utilization.insert(
            ResourceKind::CPU,
            rand::random::<f64>() * 0.6 + 0.2, // 20%-80%
        );
        
        // 内存利用率 (0-1)
        self.current_utilization.insert(
            ResourceKind::Memory,
            rand::random::<f64>() * 0.5 + 0.3, // 30%-80%
        );
        
        // 磁盘利用率 (0-1)
        self.current_utilization.insert(
            ResourceKind::Disk,
            rand::random::<f64>() * 0.4 + 0.1, // 10%-50%
        );
        
        // 网络利用率 (0-1)
        self.current_utilization.insert(
            ResourceKind::Network,
            rand::random::<f64>() * 0.7 + 0.1, // 10%-80%
        );
    }
}

impl ResourceMonitor for SystemResourceMonitor {
    fn get_resource_utilization(&self, kind: ResourceKind) -> Option<f64> {
        // 确保数据是最新的
        let mut this = self.clone();
        this.refresh();
        
        this.current_utilization.get(&kind).cloned()
    }
    
    fn get_total_resources(&self, kind: ResourceKind) -> Option<f64> {
        self.total_resources.get(&kind).cloned()
    }
    
    fn get_available_resources(&self, kind: ResourceKind) -> Option<f64> {
        if let (Some(total), Some(utilization)) = (
            self.total_resources.get(&kind),
            self.current_utilization.get(&kind)
        ) {
            Some(total * (1.0 - utilization))
        } else {
            None
        }
    }
    
    fn resource_kinds(&self) -> HashSet<ResourceKind> {
        self.total_resources.keys().cloned().collect()
    }
}

impl Clone for SystemResourceMonitor {
    fn clone(&self) -> Self {
        Self {
            refresh_interval: self.refresh_interval,
            last_refresh: self.last_refresh,
            current_utilization: self.current_utilization.clone(),
            total_resources: self.total_resources.clone(),
        }
    }
}

// 阈值伸缩策略
pub struct ThresholdScalingStrategy {
    resource_kind: ResourceKind,
    scale_up_threshold: f64,     // 超过此利用率则扩容
    scale_down_threshold: f64,   // 低于此利用率则缩容
    scale_up_factor: f64,        // 扩容比例
    scale_down_factor: f64,      // 缩容比例
    cooldown_period: Duration,   // 冷却期
    last_scaling: Option<Instant>, // 上次伸缩时间
}

impl ThresholdScalingStrategy {
    pub fn new(
        resource_kind: ResourceKind,
        scale_up_threshold: f64,
        scale_down_threshold: f64,
        scale_up_factor: f64,
        scale_down_factor: f64,
        cooldown_period: Duration,
    ) -> Self {
        Self {
            resource_kind,
            scale_up_threshold,
            scale_down_threshold,
            scale_up_factor,
            scale_down_factor,
            cooldown_period,
            last_scaling: None,
        }
    }
    
    // 检查是否处于冷却期
    fn in_cooldown(&self) -> bool {
        if let Some(last) = self.last_scaling {
            Instant::now().duration_since(last) < self.cooldown_period
        } else {
            false
        }
    }
}

impl ResourceScalingStrategy for ThresholdScalingStrategy {
    fn should_scale_up(&self, utilization: f64, history: &ResourceUtilizationHistory) -> bool {
        if self.in_cooldown() {
            return false;
        }
        
        // 检查当前利用率是否超过阈值
        if utilization > self.scale_up_threshold {
            // 检查最近5分钟平均利用率是否也较高，避免短暂峰值触发伸缩
            if let Some(avg_5min) = history.get_average_utilization(
                self.resource_kind,
                Duration::from_secs(300)
            ) {
                return avg_5min > self.scale_up_threshold * 0.9;
            }
        }
        
        false
    }
    
    fn should_scale_down(&self, utilization: f64, history: &ResourceUtilizationHistory) -> bool {
        if self.in_cooldown() {
            return false;
        }
        
        // 检查当前利用率是否低于阈值
        if utilization < self.scale_down_threshold {
            // 检查最近15分钟平均利用率是否也较低，确保是持续低负载
            if let Some(avg_15min) = history.get_average_utilization(
                self.resource_kind,
                Duration::from_secs(900)
            ) {
                return avg_15min < self.scale_down_threshold * 1.1;
            }
        }
        
        false
    }
    
    fn get_scale_factor(&self, utilization: f64) -> f64 {
        if utilization > self.scale_up_threshold {
            self.scale_up_factor
        } else if utilization < self.scale_down_threshold {
            self.scale_down_factor
        } else {
            1.0 // 不伸缩
        }
    }
    
    fn resource_kind(&self) -> ResourceKind {
        self.resource_kind
    }
}

// 预测伸缩策略
pub struct PredictiveScalingStrategy {
    resource_kind: ResourceKind,
    history_window: Duration,    // 用于预测的历史窗口
    prediction_window: Duration, // 预测窗口
    scale_up_threshold: f64,     // 预测利用率超过此值则扩容
    scale_down_threshold: f64,   // 预测利用率低于此值则缩容
    scale_up_factor: f64,        // 扩容比例
    scale_down_factor: f64,      // 缩容比例
    last_scaling: Option<Instant>, // 上次伸缩时间
    cooldown_period: Duration,   // 冷却期
}

impl PredictiveScalingStrategy {
    pub fn new(
        resource_kind: ResourceKind,
        history_window: Duration,
        prediction_window: Duration,
        scale_up_threshold: f64,
        scale_down_threshold: f64,
        scale_up_factor: f64,
        scale_down_factor: f64,
        cooldown_period: Duration,
    ) -> Self {
        Self {
            resource_kind,
            history_window,
            prediction_window,
            scale_up_threshold,
            scale_down_threshold,
            scale_up_factor,
            scale_down_factor,
            last_scaling: None,
            cooldown_period,
        }
    }
    
    // 预测未来利用率
    fn predict_future_utilization(&self, history: &ResourceUtilizationHistory) -> Option<f64> {
        // 获取历史窗口内的样本
        let now = Instant::now();
        let window_start = now.checked_sub(self.history_window)?;
        
        // 筛选出相关样本
        let samples: Vec<_> = history.samples.iter()
            .filter(|(kind, _, timestamp)| 
                *kind == self.resource_kind && *timestamp >= window_start
            )
            .collect();
            
        if samples.len() < 3 {
            return None; // 样本太少，无法预测
        }
        
        // 简单线性回归预测
        let n = samples.len() as f64;
        
        // 计算样本时间（相对于现在的秒数）和利用率
        let mut x_values: Vec<f64> = Vec::with_capacity(samples.len());
        let mut y_values: Vec<f64> = Vec::with_capacity(samples.len());
        
        for (_, utilization, timestamp) in &samples {
            let seconds_ago = now.duration_since(*timestamp).as_secs_f64();
            x_values.push(-seconds_ago); // 负值表示过去
            y_values.push(*utilization);
        }
        
        // 计算x和y的平均值
        let mean_x: f64 = x_values.iter().sum::<f64>() / n;
        let mean_y: f64 = y_values.iter().sum::<f64>() / n;
        
        // 计算斜率和截距
        let mut numerator = 0.0;
        let mut denominator = 0.0;
        
        for i in 0..samples.len() {
            let x_diff = x_values[i] - mean_x;
            let y_diff = y_values[i] - mean_y;
            numerator += x_diff * y_diff;
            denominator += x_diff * x_diff;
        }
        
        if denominator.abs() < std::f64::EPSILON {
            return Some(mean_y); // 斜率为0，使用平均值
        }
        
        let slope = numerator / denominator;
        let intercept = mean_y - slope * mean_x;
        
        // 预测未来利用率
        let prediction_time = self.prediction_window.as_secs_f64();
        let predicted_utilization = slope * prediction_time + intercept;
        
        // 确保预测值在有效范围内
        Some(predicted_utilization.max(0.0).min(1.0))
    }
    
    // 检查是否处于冷却期
    fn in_cooldown(&self) -> bool {
        if let Some(last) = self.last_scaling {
            Instant::now().duration_since(last) < self.cooldown_period
        } else {
            false
        }
    }
}

impl ResourceScalingStrategy for PredictiveScalingStrategy {
    fn should_scale_up(&self, _: f64, history: &ResourceUtilizationHistory) -> bool {
        if self.in_cooldown() {
            return false;
        }
        
        // 预测未来利用率
        if let Some(predicted) = self.predict_future_utilization(history) {
            return predicted > self.scale_up_threshold;
        }
        
        false
    }
    
    fn should_scale_down(&self, _: f64, history: &ResourceUtilizationHistory) -> bool {
        if self.in_cooldown() {
            return false;
        }
        
        // 预测未来利用率
        if let Some(predicted) = self.predict_future_utilization(history) {
            return predicted < self.scale_down_threshold;
        }
        
        false
    }
    
    fn get_scale_factor(&self, _: f64) -> f64 {
        // 实际实现可能会根据预测的差距调整伸缩因子
        1.2 // 默认扩容20%
    }
    
    fn resource_kind(&self) -> ResourceKind {
        self.resource_kind
    }
}
```

### 负载均衡与迁移

负载均衡与任务迁移机制可以在系统资源分布不均或负载变化时，动态调整任务分布以优化资源利用率。

```rust
// 负载均衡与迁移实现
use std::collections::{HashMap, HashSet, BinaryHeap};
use std::sync::{Arc, Mutex, RwLock};
use std::time::{Duration, Instant};
use std::cmp::Ordering;

// 负载均衡策略
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum LoadBalancingStrategy {
    RoundRobin,             // 轮询
    LeastConnections,       // 最少连接
    WeightedRoundRobin,     // 加权轮询
    ConsistentHashing,      // 一致性哈希
    ResourceBased,          // 基于资源
    ResponseTime,           // 响应时间
    AdaptiveLoadAware,      // 自适应负载感知
}

// 迁移触发条件
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum MigrationTrigger {
    LoadImbalance,          // 负载不均衡
    ResourceConstraint,     // 资源约束
    PerformanceDegradation, // 性能下降
    AvailabilityRisk,       // 可用性风险
    EnergyOptimization,     // 能源优化
    UserRequest,            // 用户请求
}

// 负载状态
#[derive(Clone, PartialEq, Debug)]
pub struct LoadState {
    cpu_usage: f64,         // CPU使用率 (0-1)
    memory_usage: f64,      // 内存使用率 (0-1)
    io_load: f64,           // IO负载 (0-1)
    network_load: f64,      // 网络负载 (0-1)
    task_count: usize,      // 任务数量
    connection_count: usize, // 连接数量
    last_updated: Instant,  // 最后更新时间
}

// 迁移代价
#[derive(Clone, Debug)]
pub struct MigrationCost {
    time_cost: Duration,    // 时间代价
    resource_cost: HashMap<ResourceKind, f64>, // 资源代价
    service_disruption: f64, // 服务中断影响 (0-1)
    data_transfer: u64,      // 数据传输量 (bytes)
}

// 负载均衡器
pub struct LoadBalancer<T: Clone + Send + 'static> {
    strategy: LoadBalancingStrategy,
    nodes: RwLock<HashMap<String, NodeInfo>>,
    task_assignments: RwLock<HashMap<String, String>>, // 任务ID -> 节点ID
    session_affinity: bool,
    session_map: RwLock<HashMap<String, String>>, // 会话ID -> 节点ID
    sticky_session_timeout: Duration,
    consistent_hash_ring: Option<ConsistentHashRing>,
    round_robin_counter: AtomicUsize,
    health_check_interval: Duration,
    last_rebalance: Mutex<Instant>,
    rebalance_interval: Duration,
    // 任务迁移管理器
    migration_manager: Arc<MigrationManager<T>>,
}

// 节点信息
#[derive(Clone)]
pub struct NodeInfo {
    id: String,
    weight: u32,
    load_state: LoadState,
    capacity: HashMap<ResourceKind, f64>,
    health_status: HealthStatus,
    location: Option<String>,
    tags: HashSet<String>,
}

// 健康状态
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum HealthStatus {
    Healthy,
    Degraded,
    Unhealthy,
    Maintenance,
}

// 一致性哈希环
pub struct ConsistentHashRing {
    ring: RwLock<BTreeMap<u64, String>>,
    replicas: usize,
}

impl ConsistentHashRing {
    pub fn new(replicas: usize) -> Self {
        Self {
            ring: RwLock::new(BTreeMap::new()),
            replicas,
        }
    }
    
    pub fn add_node(&self, node_id: &str) {
        let mut ring = self.ring.write().unwrap();
        
        for i in 0..self.replicas {
            let key = self.hash(&format!("{}:{}", node_id, i));
            ring.insert(key, node_id.to_string());
        }
    }
    
    pub fn remove_node(&self, node_id: &str) {
        let mut ring = self.ring.write().unwrap();
        
        for i in 0..self.replicas {
            let key = self.hash(&format!("{}:{}", node_id, i));
            ring.remove(&key);
        }
    }
    
    pub fn get_node(&self, key: &str) -> Option<String> {
        let ring = self.ring.read().unwrap();
        
        if ring.is_empty() {
            return None;
        }
        
        let hash = self.hash(key);
        
        // 找到哈希环上大于等于hash的第一个节点
        match ring.range(hash..).next() {
            Some((_, node)) => Some(node.clone()),
            None => {
                // 如果没有找到，则取环上的第一个节点
                ring.values().next().cloned()
            }
        }
    }
    
    // 简单的哈希函数（使用FNV-1a算法）
    fn hash(&self, key: &str) -> u64 {
        let mut hash: u64 = 14695981039346656037; // FNV偏移基数
        for byte in key.bytes() {
            hash ^= byte as u64;
            hash = hash.wrapping_mul(1099511628211); // FNV质数
        }
        hash
    }
}

// 任务迁移管理器
pub struct MigrationManager<T: Clone + Send + 'static> {
    migrations_in_progress: RwLock<HashMap<String, MigrationStatus<T>>>,
    migration_history: RwLock<VecDeque<MigrationRecord>>,
    max_concurrent_migrations: usize,
    migration_handlers: HashMap<String, Box<dyn MigrationHandler<T> + Send + Sync>>,
    cost_calculator: Box<dyn MigrationCostCalculator + Send + Sync>,
}

// 迁移状态
#[derive(Clone)]
pub struct MigrationStatus<T> {
    task_id: String,
    task: T,
    source_node: String,
    target_node: String,
    start_time: Instant,
    estimated_completion: Instant,
    progress: f64, // 0-1
    state: MigrationState,
    trigger: MigrationTrigger,
}

// 迁移状态枚举
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum MigrationState {
    Preparing,     // 准备阶段
    Transferring,  // 传输阶段
    Activating,    // 激活阶段
    Completed,     // 已完成
    Failed,        // 失败
    Canceled,      // 已取消
}

// 迁移记录
pub struct MigrationRecord {
    task_id: String,
    source_node: String,
    target_node: String,
    start_time: Instant,
    end_time: Instant,
    success: bool,
    duration: Duration,
    data_transferred: u64,
    trigger: MigrationTrigger,
}

// 迁移处理器特征
pub trait MigrationHandler<T> {
    fn prepare_migration(&self, task: &T, source: &str, target: &str) -> Result<(), MigrationError>;
    fn transfer_state(&self, task_id: &str, progress_callback: Box<dyn Fn(f64) + Send>) -> Result<(), MigrationError>;
    fn activate_on_target(&self, task_id: &str) -> Result<(), MigrationError>;
    fn cleanup_source(&self, task_id: &str) -> Result<(), MigrationError>;
    fn cancel_migration(&self, task_id: &str) -> Result<(), MigrationError>;
    fn get_task_size(&self, task: &T) -> u64;
}

// 迁移代价计算器特征
pub trait MigrationCostCalculator {
    fn calculate_cost(
        &self,
        task_id: &str,
        source_node: &str,
        target_node: &str,
        task_size: u64,
        load_states: &HashMap<String, LoadState>,
    ) -> MigrationCost;
}

// 迁移错误
pub enum MigrationError {
    TaskNotFound,
    NodeNotFound,
    PreparationFailed,
    TransferFailed,
    ActivationFailed,
    CleanupFailed,
    MigrationLimitExceeded,
    AlreadyInProgress,
    IncompatibleTarget,
}

impl<T: Clone + Send + 'static> MigrationManager<T> {
    pub fn new(
        max_concurrent_migrations: usize,
        cost_calculator: Box<dyn MigrationCostCalculator + Send + Sync>,
    ) -> Self {
        Self {
            migrations_in_progress: RwLock::new(HashMap::new()),
            migration_history: RwLock::new(VecDeque::with_capacity(1000)),
            max_concurrent_migrations,
            migration_handlers: HashMap::new(),
            cost_calculator,
        }
    }
    
    // 添加迁移处理器
    pub fn add_migration_handler(
        &mut self,
        task_type: &str,
        handler: Box<dyn MigrationHandler<T> + Send + Sync>,
    ) {
        self.migration_handlers.insert(task_type.to_string(), handler);
    }
    
    // 开始任务迁移
    pub fn start_migration(
        &self,
        task_id: &str,
        task: T,
        source_node: &str,
        target_node: &str,
        task_type: &str,
        trigger: MigrationTrigger,
    ) -> Result<(), MigrationError> {
        let mut migrations = self.migrations_in_progress.write().unwrap();
        
        // 检查是否超过最大并发迁移数
        if migrations.len() >= self.max_concurrent_migrations {
            return Err(MigrationError::MigrationLimitExceeded);
        }
        
        // 检查任务是否已在迁移中
        if migrations.contains_key(task_id) {
            return Err(MigrationError::AlreadyInProgress);
        }
        
        // 获取对应的迁移处理器
        let handler = self.migration_handlers.get(task_type)
            .ok_or(MigrationError::TaskNotFound)?;
            
        // 准备迁移
        handler.prepare_migration(&task, source_node, target_node)?;
        
        // 计算任务大小
        let task_size = handler.get_task_size(&task);
        
        // 估计完成时间（简化计算）
        let now = Instant::now();
        let estimated_completion = now + Duration::from_secs((task_size / (1024 * 1024) + 1) as u64);
        
        // 创建迁移状态
        let status = MigrationStatus {
            task_id: task_id.to_string(),
            task: task.clone(),
            source_node: source_node.to_string(),
            target_node: target_node.to_string(),
            start_time: now,
            estimated_completion,
            progress: 0.0,
            state: MigrationState::Preparing,
            trigger,
        };
        
        // 记录迁移
        migrations.insert(task_id.to_string(), status);
        
        // 在后台线程中执行迁移
        let task_id = task_id.to_string();
        let task_type = task_type.to_string();
        let manager = Arc::new(self.clone());
        
        std::thread::spawn(move || {
            manager.execute_migration(&task_id, &task_type);
        });
        
        Ok(())
    }
    
    // 执行迁移过程
    fn execute_migration(&self, task_id: &str, task_type: &str) {
        let handler = if let Some(h) = self.migration_handlers.get(task_type) {
            h
        } else {
            return;
        };
        
        // 更新状态为传输中
        self.update_migration_state(task_id, MigrationState::Transferring, 0.0);
        
        // 创建进度回调
        let manager = Arc::new(self.clone());
        let task_id_clone = task_id.to_string();
        let progress_callback = Box::new(move |progress: f64| {
            manager.update_migration_progress(&task_id_clone, progress);
        });
        
        // 传输状态
        let transfer_result = handler.transfer_state(task_id, progress_callback);
        
       if transfer_result.is_err() {
            // 传输失败
            self.update_migration_state(task_id, MigrationState::Failed, 0.0);
            self.record_migration_completion(task_id, false);
            return;
        }
        
        // 更新状态为激活中
        self.update_migration_state(task_id, MigrationState::Activating, 0.95);
        
        // 在目标节点激活任务
        let activation_result = handler.activate_on_target(task_id);
        
        if activation_result.is_err() {
            // 激活失败
            self.update_migration_state(task_id, MigrationState::Failed, 0.0);
            self.record_migration_completion(task_id, false);
            return;
        }
        
        // 清理源节点的任务状态
        let cleanup_result = handler.cleanup_source(task_id);
        
        // 不管清理是否成功，都标记迁移完成
        self.update_migration_state(task_id, MigrationState::Completed, 1.0);
        self.record_migration_completion(task_id, true);
    }
    
    // 更新迁移状态
    fn update_migration_state(&self, task_id: &str, state: MigrationState, progress: f64) {
        let mut migrations = self.migrations_in_progress.write().unwrap();
        
        if let Some(status) = migrations.get_mut(task_id) {
            status.state = state;
            status.progress = progress;
        }
    }
    
    // 更新迁移进度
    fn update_migration_progress(&self, task_id: &str, progress: f64) {
        let mut migrations = self.migrations_in_progress.write().unwrap();
        
        if let Some(status) = migrations.get_mut(task_id) {
            status.progress = progress;
        }
    }
    
    // 记录迁移完成
    fn record_migration_completion(&self, task_id: &str, success: bool) {
        let mut migrations = self.migrations_in_progress.write().unwrap();
        
        if let Some(status) = migrations.remove(task_id) {
            let end_time = Instant::now();
            let duration = end_time.duration_since(status.start_time);
            
            // 估算传输的数据量（简化）
            let data_transferred = if success {
                // 根据任务处理器获取实际大小
                if let Some(handler) = self.migration_handlers.values().next() {
                    handler.get_task_size(&status.task)
                } else {
                    0
                }
            } else {
                // 失败时，按进度比例估算
                let handler = self.migration_handlers.values().next().unwrap();
                let total_size = handler.get_task_size(&status.task);
                (total_size as f64 * status.progress) as u64
            };
            
            // 创建迁移记录
            let record = MigrationRecord {
                task_id: task_id.to_string(),
                source_node: status.source_node,
                target_node: status.target_node,
                start_time: status.start_time,
                end_time,
                success,
                duration,
                data_transferred,
                trigger: status.trigger,
            };
            
            // 添加到历史记录
            let mut history = self.migration_history.write().unwrap();
            history.push_back(record);
            
            // 保持历史记录大小限制
            while history.len() > 1000 {
                history.pop_front();
            }
        }
    }
    
    // 取消迁移
    pub fn cancel_migration(&self, task_id: &str) -> Result<(), MigrationError> {
        let migrations = self.migrations_in_progress.read().unwrap();
        
        if let Some(status) = migrations.get(task_id) {
            // 获取任务类型对应的处理器
            // 简化：使用第一个可用的处理器
            if let Some(handler) = self.migration_handlers.values().next() {
                // 在处理器中执行取消操作
                handler.cancel_migration(task_id)?;
                
                // 更新状态
                drop(migrations); // 释放读锁
                self.update_migration_state(task_id, MigrationState::Canceled, status.progress);
                self.record_migration_completion(task_id, false);
                
                return Ok(());
            } else {
                return Err(MigrationError::TaskNotFound);
            }
        } else {
            return Err(MigrationError::TaskNotFound);
        }
    }
    
    // 获取迁移状态
    pub fn get_migration_status(&self, task_id: &str) -> Option<MigrationState> {
        let migrations = self.migrations_in_progress.read().unwrap();
        migrations.get(task_id).map(|status| status.state)
    }
    
    // 获取所有进行中的迁移
    pub fn get_active_migrations(&self) -> Vec<(String, MigrationState, f64)> {
        let migrations = self.migrations_in_progress.read().unwrap();
        
        migrations.iter()
            .map(|(id, status)| (id.clone(), status.state, status.progress))
            .collect()
    }
    
    // 计算迁移任务的成本
    pub fn calculate_migration_cost(
        &self,
        task_id: &str,
        task: &T,
        source_node: &str,
        target_node: &str,
        load_states: &HashMap<String, LoadState>,
    ) -> MigrationCost {
        // 获取任务大小
        let task_size = if let Some(handler) = self.migration_handlers.values().next() {
            handler.get_task_size(task)
        } else {
            0
        };
        
        // 使用成本计算器计算迁移成本
        self.cost_calculator.calculate_cost(
            task_id,
            source_node,
            target_node,
            task_size,
            load_states,
        )
    }
    
    // 获取迁移历史统计
    pub fn get_migration_stats(&self) -> MigrationStatistics {
        let history = self.migration_history.read().unwrap();
        
        let total_migrations = history.len();
        let successful_migrations = history.iter().filter(|r| r.success).count();
        let failed_migrations = total_migrations - successful_migrations;
        
        let mut total_duration = Duration::from_secs(0);
        let mut total_data = 0;
        
        for record in history.iter() {
            total_duration += record.duration;
            total_data += record.data_transferred;
        }
        
        let avg_duration = if total_migrations > 0 {
            total_duration / total_migrations as u32
        } else {
            Duration::from_secs(0)
        };
        
        let avg_data_size = if total_migrations > 0 {
            total_data / total_migrations as u64
        } else {
            0
        };
        
        // 按触发器类型统计
        let mut by_trigger = HashMap::new();
        for record in history.iter() {
            *by_trigger.entry(record.trigger).or_insert(0) += 1;
        }
        
        MigrationStatistics {
            total_migrations,
            successful_migrations,
            failed_migrations,
            avg_duration,
            avg_data_size,
            by_trigger,
        }
    }
}

// 实现Clone以支持线程间共享
impl<T: Clone + Send + 'static> Clone for MigrationManager<T> {
    fn clone(&self) -> Self {
        Self {
            migrations_in_progress: RwLock::new(self.migrations_in_progress.read().unwrap().clone()),
            migration_history: RwLock::new(self.migration_history.read().unwrap().clone()),
            max_concurrent_migrations: self.max_concurrent_migrations,
            migration_handlers: self.migration_handlers.clone(),
            cost_calculator: self.cost_calculator.clone_box(),
        }
    }
}

// 迁移统计信息
pub struct MigrationStatistics {
    total_migrations: usize,
    successful_migrations: usize,
    failed_migrations: usize,
    avg_duration: Duration,
    avg_data_size: u64,
    by_trigger: HashMap<MigrationTrigger, usize>,
}

// 网络带宽感知的迁移成本计算器
pub struct BandwidthAwareCostCalculator {
    network_topology: HashMap<(String, String), f64>, // (源节点,目标节点) -> 带宽(Mbps)
    default_bandwidth: f64, // 默认带宽(Mbps)
    overhead_factor: f64,   // 额外开销因子
}

impl BandwidthAwareCostCalculator {
    pub fn new(default_bandwidth: f64, overhead_factor: f64) -> Self {
        Self {
            network_topology: HashMap::new(),
            default_bandwidth,
            overhead_factor,
        }
    }
    
    // 添加节点间带宽信息
    pub fn add_bandwidth_info(&mut self, source: &str, target: &str, bandwidth_mbps: f64) {
        self.network_topology.insert(
            (source.to_string(), target.to_string()),
            bandwidth_mbps,
        );
    }
    
    // 获取节点间带宽
    fn get_bandwidth(&self, source: &str, target: &str) -> f64 {
        self.network_topology
            .get(&(source.to_string(), target.to_string()))
            .cloned()
            .unwrap_or(self.default_bandwidth)
    }
}

impl MigrationCostCalculator for BandwidthAwareCostCalculator {
    fn calculate_cost(
        &self,
        task_id: &str,
        source_node: &str,
        target_node: &str,
        task_size: u64,
        load_states: &HashMap<String, LoadState>,
    ) -> MigrationCost {
        // 获取节点间带宽
        let bandwidth_mbps = self.get_bandwidth(source_node, target_node);
        
        // 计算传输时间（考虑带宽和当前负载）
        let source_load = load_states.get(source_node).cloned().unwrap_or_else(|| {
            LoadState {
                cpu_usage: 0.5,
                memory_usage: 0.5,
                io_load: 0.5,
                network_load: 0.5,
                task_count: 1,
                connection_count: 1,
                last_updated: Instant::now(),
            }
        });
        
        let target_load = load_states.get(target_node).cloned().unwrap_or_else(|| {
            LoadState {
                cpu_usage: 0.5,
                memory_usage: 0.5,
                io_load: 0.5,
                network_load: 0.5,
                task_count: 1,
                connection_count: 1,
                last_updated: Instant::now(),
            }
        });
        
        // 考虑网络负载对带宽的影响
        let effective_bandwidth = bandwidth_mbps * (1.0 - source_load.network_load.max(target_load.network_load));
        
        // 转换为bytes/s
        let bytes_per_second = (effective_bandwidth * 1024.0 * 1024.0 / 8.0) as u64;
        
        // 计算传输时间（秒）
        let transfer_seconds = (task_size as f64 / bytes_per_second as f64) * self.overhead_factor;
        
        // 创建时间代价
        let time_cost = Duration::from_secs_f64(transfer_seconds);
        
        // 创建资源代价
        let mut resource_cost = HashMap::new();
        resource_cost.insert(ResourceKind::CPU, 0.1 + source_load.cpu_usage * 0.1); // CPU占用增加
        resource_cost.insert(ResourceKind::Network, source_load.network_load + 0.2); // 网络占用增加
        
        // 估算服务中断影响
        let service_disruption = match task_size {
            size if size < 1024 * 1024 => 0.1, // <1MB，影响小
            size if size < 10 * 1024 * 1024 => 0.3, // <10MB，中等影响
            size if size < 100 * 1024 * 1024 => 0.5, // <100MB，较大影响
            _ => 0.8, // 大文件，影响大
        };
        
        MigrationCost {
            time_cost,
            resource_cost,
            service_disruption,
            data_transfer: task_size,
        }
    }
}

impl Clone for Box<dyn MigrationCostCalculator + Send + Sync> {
    fn clone(&self) -> Self {
        self.clone_box()
    }
}

// 支持MigrationCostCalculator的Clone
pub trait MigrationCostCalculatorClone {
    fn clone_box(&self) -> Box<dyn MigrationCostCalculator + Send + Sync>;
}

impl<T> MigrationCostCalculatorClone for T
where
    T: 'static + MigrationCostCalculator + Clone + Send + Sync
{
    fn clone_box(&self) -> Box<dyn MigrationCostCalculator + Send + Sync> {
        Box::new(self.clone())
    }
}

impl Clone for BandwidthAwareCostCalculator {
    fn clone(&self) -> Self {
        Self {
            network_topology: self.network_topology.clone(),
            default_bandwidth: self.default_bandwidth,
            overhead_factor: self.overhead_factor,
        }
    }
}

// 实现负载均衡器
impl<T: Clone + Send + 'static> LoadBalancer<T> {
    pub fn new(
        strategy: LoadBalancingStrategy,
        session_affinity: bool,
        sticky_session_timeout: Duration,
        health_check_interval: Duration,
        rebalance_interval: Duration,
        migration_manager: Arc<MigrationManager<T>>,
    ) -> Self {
        let consistent_hash_ring = if strategy == LoadBalancingStrategy::ConsistentHashing {
            Some(ConsistentHashRing::new(10)) // 10个虚拟节点
        } else {
            None
        };
        
        Self {
            strategy,
            nodes: RwLock::new(HashMap::new()),
            task_assignments: RwLock::new(HashMap::new()),
            session_affinity,
            session_map: RwLock::new(HashMap::new()),
            sticky_session_timeout,
            consistent_hash_ring,
            round_robin_counter: AtomicUsize::new(0),
            health_check_interval,
            last_rebalance: Mutex::new(Instant::now()),
            rebalance_interval,
            migration_manager,
        }
    }
    
    // 注册节点
    pub fn register_node(&self, node: NodeInfo) {
        let mut nodes = self.nodes.write().unwrap();
        
        // 添加到节点列表
        nodes.insert(node.id.clone(), node.clone());
        
        // 如果使用一致性哈希，也添加到哈希环
        if let Some(ref hash_ring) = self.consistent_hash_ring {
            hash_ring.add_node(&node.id);
        }
    }
    
    // 注销节点
    pub fn unregister_node(&self, node_id: &str) -> Result<(), LoadBalancerError> {
        let mut nodes = self.nodes.write().unwrap();
        
        if nodes.remove(node_id).is_some() {
            // 如果使用一致性哈希，也从哈希环移除
            if let Some(ref hash_ring) = self.consistent_hash_ring {
                hash_ring.remove_node(node_id);
            }
            
            // 更新任务分配
            let mut task_assignments = self.task_assignments.write().unwrap();
            let affected_tasks: Vec<_> = task_assignments.iter()
                .filter(|(_, assigned_node)| *assigned_node == node_id)
                .map(|(task_id, _)| task_id.clone())
                .collect();
                
            // 重新分配受影响的任务
            for task_id in affected_tasks {
                task_assignments.remove(&task_id);
                // 实际实现中，这里可能需要触发任务重新调度
            }
            
            // 清理会话映射
            if self.session_affinity {
                let mut session_map = self.session_map.write().unwrap();
                session_map.retain(|_, node| *node != node_id);
            }
            
            Ok(())
        } else {
            Err(LoadBalancerError::NodeNotFound)
        }
    }
    
    // 更新节点负载状态
    pub fn update_node_load(&self, node_id: &str, load_state: LoadState) -> Result<(), LoadBalancerError> {
        let mut nodes = self.nodes.write().unwrap();
        
        if let Some(node) = nodes.get_mut(node_id) {
            node.load_state = load_state;
            Ok(())
        } else {
            Err(LoadBalancerError::NodeNotFound)
        }
    }
    
    // 更新节点健康状态
    pub fn update_node_health(&self, node_id: &str, status: HealthStatus) -> Result<(), LoadBalancerError> {
        let mut nodes = self.nodes.write().unwrap();
        
        if let Some(node) = nodes.get_mut(node_id) {
            let old_status = node.health_status;
            node.health_status = status;
            
            // 如果节点状态从健康变为不健康，需要重新分配任务
            if old_status == HealthStatus::Healthy && status != HealthStatus::Healthy {
                drop(nodes); // 释放写锁，避免死锁
                self.handle_node_unhealthy(node_id);
            }
            
            Ok(())
        } else {
            Err(LoadBalancerError::NodeNotFound)
        }
    }
    
    // 处理节点不健康的情况
    fn handle_node_unhealthy(&self, node_id: &str) {
        let task_assignments = self.task_assignments.read().unwrap();
        
        // 找出分配到不健康节点的任务
        let affected_tasks: Vec<_> = task_assignments.iter()
            .filter(|(_, assigned_node)| *assigned_node == node_id)
            .map(|(task_id, _)| task_id.clone())
            .collect();
            
        drop(task_assignments); // 释放读锁
        
        // 重新分配这些任务
        for task_id in affected_tasks {
            // 这里应该有任务重新分配的逻辑
            // 从不健康节点迁移到健康节点
            self.reassign_task(&task_id, node_id);
        }
    }
    
    // 重新分配任务
    fn reassign_task(&self, task_id: &str, current_node: &str) {
        // 选择一个新节点
        if let Some(new_node) = self.select_node(task_id, None) {
            if new_node != current_node {
                // 更新任务分配
                let mut task_assignments = self.task_assignments.write().unwrap();
                task_assignments.insert(task_id.to_string(), new_node.clone());
                
                // 实际系统中，这里会触发任务迁移
                // 简化：只打印日志
                println!("Task {} reassigned from {} to {}", task_id, current_node, new_node);
            }
        }
    }
    
    // 获取任务分配的节点
    pub fn get_assigned_node(&self, task_id: &str) -> Option<String> {
        let task_assignments = self.task_assignments.read().unwrap();
        task_assignments.get(task_id).cloned()
    }
    
    // 为任务选择节点
    pub fn select_node(&self, task_id: &str, session_id: Option<&str>) -> Option<String> {
        // 如果启用了会话亲和性，且提供了会话ID，检查会话映射
        if self.session_affinity && session_id.is_some() {
            let session_id = session_id.unwrap();
            let session_map = self.session_map.read().unwrap();
            
            if let Some(node_id) = session_map.get(session_id) {
                // 验证节点健康状态
                let nodes = self.nodes.read().unwrap();
                if let Some(node) = nodes.get(node_id) {
                    if node.health_status == HealthStatus::Healthy {
                        return Some(node_id.clone());
                    }
                }
            }
        }
        
        // 根据策略选择节点
        let selected_node = match self.strategy {
            LoadBalancingStrategy::RoundRobin => self.select_round_robin(),
            LoadBalancingStrategy::LeastConnections => self.select_least_connections(),
            LoadBalancingStrategy::WeightedRoundRobin => self.select_weighted_round_robin(),
            LoadBalancingStrategy::ConsistentHashing => self.select_consistent_hashing(task_id),
            LoadBalancingStrategy::ResourceBased => self.select_resource_based(),
            LoadBalancingStrategy::ResponseTime => self.select_response_time(),
            LoadBalancingStrategy::AdaptiveLoadAware => self.select_adaptive_load_aware(),
        };
        
        // 如果找到节点，更新任务分配和会话映射
        if let Some(node_id) = &selected_node {
            // 更新任务分配
            let mut task_assignments = self.task_assignments.write().unwrap();
            task_assignments.insert(task_id.to_string(), node_id.clone());
            
            // 如果启用了会话亲和性且提供了会话ID，更新会话映射
            if self.session_affinity && session_id.is_some() {
                let mut session_map = self.session_map.write().unwrap();
                session_map.insert(session_id.unwrap().to_string(), node_id.clone());
            }
        }
        
        selected_node
    }
    
    // 轮询选择
    fn select_round_robin(&self) -> Option<String> {
        let nodes = self.nodes.read().unwrap();
        
        // 过滤出健康节点
        let healthy_nodes: Vec<_> = nodes.values()
            .filter(|node| node.health_status == HealthStatus::Healthy)
            .collect();
            
        if healthy_nodes.is_empty() {
            return None;
        }
        
        // 增加计数器并取模
        let counter = self.round_robin_counter.fetch_add(1, Ordering::SeqCst);
        let index = counter % healthy_nodes.len();
        
        Some(healthy_nodes[index].id.clone())
    }
    
    // 最少连接选择
    fn select_least_connections(&self) -> Option<String> {
        let nodes = self.nodes.read().unwrap();
        
        // 过滤出健康节点
        let healthy_nodes: Vec<_> = nodes.values()
            .filter(|node| node.health_status == HealthStatus::Healthy)
            .collect();
            
        if healthy_nodes.is_empty() {
            return None;
        }
        
        // 找出连接数最少的节点
        healthy_nodes.iter()
            .min_by_key(|node| node.load_state.connection_count)
            .map(|node| node.id.clone())
    }
    
    // 加权轮询选择
    fn select_weighted_round_robin(&self) -> Option<String> {
        let nodes = self.nodes.read().unwrap();
        
        // 过滤出健康节点
        let healthy_nodes: Vec<_> = nodes.values()
            .filter(|node| node.health_status == HealthStatus::Healthy)
            .collect();
            
        if healthy_nodes.is_empty() {
            return None;
        }
        
        // 计算权重总和
        let total_weight: u32 = healthy_nodes.iter().map(|node| node.weight).sum();
        
        if total_weight == 0 {
            // 如果总权重为0，退化为普通轮询
            return self.select_round_robin();
        }
        
        // 生成一个0到总权重的随机数
        let rand_weight = rand::random::<u32>() % total_weight;
        
        // 根据权重选择节点
        let mut current_weight = 0;
        for node in healthy_nodes {
            current_weight += node.weight;
            if rand_weight < current_weight {
                return Some(node.id.clone());
            }
        }
        
        // 兜底：选择第一个节点
        Some(healthy_nodes[0].id.clone())
    }
    
    // 一致性哈希选择
    fn select_consistent_hashing(&self, key: &str) -> Option<String> {
        if let Some(ref hash_ring) = self.consistent_hash_ring {
            // 从哈希环获取节点
            if let Some(node_id) = hash_ring.get_node(key) {
                // 验证节点健康状态
                let nodes = self.nodes.read().unwrap();
                if let Some(node) = nodes.get(&node_id) {
                    if node.health_status == HealthStatus::Healthy {
                        return Some(node_id);
                    }
                }
            }
        }
        
        // 如果找不到或节点不健康，退化为轮询
        self.select_round_robin()
    }
    
    // 基于资源选择
    fn select_resource_based(&self) -> Option<String> {
        let nodes = self.nodes.read().unwrap();
        
        // 过滤出健康节点
        let healthy_nodes: Vec<_> = nodes.values()
            .filter(|node| node.health_status == HealthStatus::Healthy)
            .collect();
            
        if healthy_nodes.is_empty() {
            return None;
        }
        
        // 根据综合资源评分选择节点
        healthy_nodes.iter()
            .max_by(|a, b| {
                let a_score = 1.0 - (a.load_state.cpu_usage + a.load_state.memory_usage) / 2.0;
                let b_score = 1.0 - (b.load_state.cpu_usage + b.load_state.memory_usage) / 2.0;
                a_score.partial_cmp(&b_score).unwrap_or(Ordering::Equal)
            })
            .map(|node| node.id.clone())
    }
    
    // 基于响应时间选择
    fn select_response_time(&self) -> Option<String> {
        // 实际实现中，这里应该使用历史响应时间数据
        // 简化：使用CPU负载作为响应时间的代理
        let nodes = self.nodes.read().unwrap();
        
        // 过滤出健康节点
        let healthy_nodes: Vec<_> = nodes.values()
            .filter(|node| node.health_status == HealthStatus::Healthy)
            .collect();
            
        if healthy_nodes.is_empty() {
            return None;
        }
        
        // 选择CPU负载最低的节点
        healthy_nodes.iter()
            .min_by(|a, b| {
                a.load_state.cpu_usage.partial_cmp(&b.load_state.cpu_usage)
                    .unwrap_or(Ordering::Equal)
            })
            .map(|node| node.id.clone())
    }
    
    // 自适应负载感知选择
    fn select_adaptive_load_aware(&self) -> Option<String> {
        let nodes = self.nodes.read().unwrap();
        
        // 过滤出健康节点
        let healthy_nodes: Vec<_> = nodes.values()
            .filter(|node| node.health_status == HealthStatus::Healthy)
            .collect();
            
        if healthy_nodes.is_empty() {
            return None;
        }
        
        // 计算每个节点的综合评分
        healthy_nodes.iter()
            .max_by(|a, b| {
                // 计算综合评分（考虑多种资源）
                let a_cpu_score = 1.0 - a.load_state.cpu_usage;
                let a_mem_score = 1.0 - a.load_state.memory_usage;
                let a_io_score = 1.0 - a.load_state.io_load;
                let a_net_score = 1.0 - a.load_state.network_load;
                
                let b_cpu_score = 1.0 - b.load_state.cpu_usage;
                let b_mem_score = 1.0 - b.load_state.memory_usage;
                let b_io_score = 1.0 - b.load_state.io_load;
                let b_net_score = 1.0 - b.load_state.network_load;
                
                // 计算加权平均分
                let a_score = a_cpu_score * 0.4 + a_mem_score * 0.3 + a_io_score * 0.15 + a_net_score * 0.15;
                let b_score = b_cpu_score * 0.4 + b_mem_score * 0.3 + b_io_score * 0.15 + b_net_score * 0.15;
                
                a_score.partial_cmp(&b_score).unwrap_or(Ordering::Equal)
            })
            .map(|node| node.id.clone())
    }
    
    // 定期执行负载均衡
    pub fn rebalance(&self) -> Result<Vec<String>, LoadBalancerError> {
        let mut last_rebalance = self.last_rebalance.lock().unwrap();
        let now = Instant::now();
        
        // 检查是否到达重新平衡间隔
        if now.duration_since(*last_rebalance) < self.rebalance_interval {
            return Ok(Vec::new()); // 尚未到达重新平衡时间
        }
        
        *last_rebalance = now;
        
        // 获取当前节点和任务分配状态
        let nodes = self.nodes.read().unwrap();
        let task_assignments = self.task_assignments.read().unwrap();
        
        // 检查负载是否不平衡
        if !self.is_load_imbalanced(&nodes) {
            return Ok(Vec::new()); // 负载已经平衡，无需重新平衡
        }
        
        // 计算每个节点的当前任务数
        let mut node_task_counts: HashMap<String, usize> = HashMap::new();
        for node_id in task_assignments.values() {
            *node_task_counts.entry(node_id.clone()).or_insert(0) += 1;
        }
        
        // 计算平均任务数
        let healthy_nodes: Vec<_> = nodes.values()
            .filter(|node| node.health_status == HealthStatus::Healthy)
            .collect();
            
        if healthy_nodes.is_empty() {
            return Err(LoadBalancerError::NoHealthyNodes);
        }
        
        let total_tasks = task_assignments.len();
        let avg_tasks_per_node = total_tasks as f64 / healthy_nodes.len() as f64;
        
        // 找出负载过高和过低的节点
        let mut overloaded_nodes: Vec<_> = healthy_nodes.iter()
            .filter(|node| {
                let task_count = node_task_counts.get(&node.id).cloned().unwrap_or(0);
                task_count as f64 > avg_tasks_per_node * 1.2 // 负载超过平均值20%
            })
            .collect();
            
        let mut underloaded_nodes: Vec<_> = healthy_nodes.iter()
            .filter(|node| {
                let task_count = node_task_counts.get(&node.id).cloned().unwrap_or(0);
                task_count as f64 < avg_tasks_per_node * 0.8 // 负载低于平均值20%
            })
            .collect();
            
        // 对过载节点按负载从高到低排序
        overloaded_nodes.sort_by(|a, b| {
            let a_count = node_task_counts.get(&a.id).cloned().unwrap_or(0);
            let b_count = node_task_counts.get(&b.id).cloned().unwrap_or(0);
            b_count.cmp(&a_count)
        });
        
        // 对低负载节点按负载从低到高排序
        underloaded_nodes.sort_by(|a, b| {
            let a_count = node_task_counts.get(&a.id).cloned().unwrap_or(0);
            let b_count = node_task_counts.get(&b.id).cloned().unwrap_or(0);
            a_count.cmp(&b_count)
        });
        
        // 找出需要迁移的任务
        let mut migrations = Vec::new();
        
        for overloaded_node in &overloaded_nodes {
            let current_count = node_task_counts.get(&overloaded_node.id).cloned().unwrap_or(0);
            let target_count = (avg_tasks_per_node * 1.1) as usize; // 目标是接近平均值
            
            if current_count <= target_count {
                continue; // 已经接近平均值，不需要迁移
            }
            
            let tasks_to_migrate = current_count - target_count;
            
            // 找出分配给该节点的任务
            let node_tasks: Vec<_> = task_assignments.iter()
                .filter(|(_, node_id)| **node_id == overloaded_node.id)
                .map(|(task_id, _)| task_id.clone())
                .collect();
                
            // 选择要迁移的任务（简化：选择前N个）
            let tasks_selected = node_tasks.into_iter().take(tasks_to_migrate);
            
            // 为每个任务找一个低负载节点
            for task_id in tasks_selected {
                if underloaded_nodes.is_empty() {
                    break; // 没有低负载节点了
                }
                
                let target_node = &underloaded_nodes[0];
                
                // 记录迁移操作
                migrations.push(task_id.clone());
                
                // 更新目标节点的任务计数
                let target_count = node_task_counts.entry(target_node.id.clone()).or_insert(0);
                *target_count += 1;
                
                // 如果目标节点不再是低负载，将其从列表中移除
                if *target_count as f64 >= avg_tasks_per_node * 0.9 {
                    underloaded_nodes.remove(0);
                }
            }
        }
        
        // 执行任务迁移（实际实现中应该异步进行）
        // 简化：只打印日志
        println!("Rebalancing: {} tasks to be migrated", migrations.len());
        
        Ok(migrations)
    }
    
    // 检查负载是否不平衡
    fn is_load_imbalanced(&self, nodes: &HashMap<String, NodeInfo>) -> bool {
        // 计算各项资源的最大和最小负载
        let mut min_cpu = f64::MAX;
        let mut max_cpu = f64::MIN;
        let mut min_memory = f64::MAX;
        let mut max_memory = f64::MIN;
        
        for node in nodes.values() {
            if node.health_status != HealthStatus::Healthy {
                continue;
            }
            
            min_cpu = min_cpu.min(node.load_state.cpu_usage);
            max_cpu = max_cpu.max(node.load_state.cpu_usage);
            min_memory = min_memory.min(node.load_state.memory_usage);
            max_memory = max_memory.max(node.load_state.memory_usage);
        }
        
        // 计算差异比例
        let cpu_diff_ratio = if min_cpu > 0.0 { (max_cpu - min_cpu) / min_cpu } else { 0.0 };
        let memory_diff_ratio = if min_memory > 0.0 { (max_memory - min_memory) / min_memory } else { 0.0 };
        
        // 如果任一资源差异超过30%，认为负载不平衡
        cpu_diff_ratio > 0.3 || memory_diff_ratio > 0.3
    }
    
    // 执行健康检查
    pub fn perform_health_checks(&self) {
        let nodes = self.nodes.read().unwrap();
        
        for (node_id, node) in nodes.iter() {
            // 实际实现中，这里应该使用HTTP探针或其他机制检查节点健康状态
            // 简化：假设所有节点都健康
            
            // 如果节点状态变化，更新状态
            // self.update_node_health(node_id, HealthStatus::Healthy);
        }
    }
    
    // 清理过期的会话映射
    pub fn cleanup_expired_sessions(&self) {
        if !self.session_affinity {
            return;
        }
        
        let now = Instant::now();
        let mut session_map = self.session_map.write().unwrap();
        
        // 简化：假设所有会话都有相同的创建时间
        // 实际实现中，应该维护每个会话的创建/更新时间
        
        // 这里我们只是打印日志
        println!("Cleaning up expired sessions: {} active sessions", session_map.len());
    }
}

// 负载均衡器错误
pub enum LoadBalancerError {
    NodeNotFound,
    TaskNotFound,
    NoHealthyNodes,
    InvalidStrategy,
}

// 使用std::cmp::Ordering
use std::cmp::Ordering;
// 使用std::collections::BTreeMap
use std::collections::BTreeMap;
// 使用std::sync::atomic::AtomicUsize
use std::sync::atomic::{AtomicUsize, Ordering as AtomicOrdering};
```

### 策略优化框架

策略优化框架通过历史数据分析、性能反馈和优化目标自动调整系统策略，实现自优化。

```rust
// 策略优化框架实现
use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::{Arc, Mutex, RwLock};
use std::time::{Duration, Instant};

// 优化目标
#[derive(Clone, Copy, PartialEq, Debug)]
pub enum OptimizationObjective {
    Throughput,            // 吞吐量最大化
    Latency,               // 延迟最小化
    ResourceUtilization,   // 资源利用率优化
    CostEfficiency,        // 成本效率优化
    EnergyEfficiency,      // 能源效率优化
    Resilience,            // 系统弹性增强
    Balanced,              // 多目标平衡
}

// 策略参数类型
#[derive(Clone, PartialEq, Debug)]
pub enum ParameterValue {
    Integer(i64),
    Float(f64),
    Boolean(bool),
    String(String),
    Duration(Duration),
}

// 策略参数
#[derive(Clone, Debug)]
pub struct StrategyParameter {
    name: String,
    value: ParameterValue,
    min_value: Option<ParameterValue>,
    max_value: Option<ParameterValue>,
    step: Option<ParameterValue>,
    description: String,
}

// 策略配置
#[derive(Clone, Debug)]
pub struct StrategyConfiguration {
    name: String,
    parameters: HashMap<String, StrategyParameter>,
    objective: OptimizationObjective,
    created_at: Instant,
    last_updated: Instant,
}

// 性能测量
#[derive(Clone, Debug)]
pub struct PerformanceMeasurement {
    timestamp: Instant,
    throughput: f64,       // 每秒处理的任务数
    p50_latency: Duration, // 50分位延迟
    p95_latency: Duration, // 95分位延迟
    p99_latency: Duration, // 99分位延迟
    error_rate: f64,       // 错误率
    resource_usage: HashMap<ResourceKind, f64>, // 资源使用率
    cost_per_task: f64,    // 每任务成本
    energy_usage: f64,     // 能源使用 (瓦特时)
}

// 优化试验
pub struct OptimizationExperiment {
    id: String,
    strategy_name: String,
    configuration: StrategyConfiguration,
    start_time: Instant,
    end_time: Option<Instant>,
    measurements: Vec<PerformanceMeasurement>,
    score: Option<f64>,
    status: ExperimentStatus,
}

// 试验状态
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ExperimentStatus {
    Pending,
    Running,
    Completed,
    Failed,
    Cancelled,
}

// 策略优化器
pub struct StrategyOptimizer {
    strategies: RwLock<HashMap<String, StrategyConfiguration>>,
    experiments: RwLock<HashMap<String, OptimizationExperiment>>,
    history: RwLock<VecDeque<OptimizationExperiment>>,
    current_experiment: RwLock<Option<String>>,
    optimization_algorithms: HashMap<String, Box<dyn OptimizationAlgorithm + Send + Sync>>,
    performance_collector: Box<dyn PerformanceCollector + Send + Sync>,
    max_history_size: usize,
}

// 优化算法特征
pub trait OptimizationAlgorithm {
    fn name(&self) -> &str;
    fn description(&self) -> &str;
    
    fn generate_next_configuration(
        &self,
        strategy: &StrategyConfiguration,
        history: &[OptimizationExperiment],
    ) -> StrategyConfiguration;
    
    fn score_experiment(
        &self,
        experiment: &OptimizationExperiment,
        objective: OptimizationObjective,
    ) -> f64;
}

// 性能收集器特征
pub trait PerformanceCollector {
    fn collect_measurements(&self) -> PerformanceMeasurement;
    fn name(&self) -> &str;
}

impl StrategyOptimizer {
    pub fn new(
        performance_collector: Box<dyn PerformanceCollector + Send + Sync>,
        max_history_size: usize,
    ) -> Self {
        Self {
            strategies: RwLock::new(HashMap::new()),
            experiments: RwLock::new(HashMap::new()),
            history: RwLock::new(VecDeque::with_capacity(max_history_size)),
            current_experiment: RwLock::new(None),
            optimization_algorithms: HashMap::new(),
            performance_collector,
            max_history_size,
        }
    }
    
    // 注册优化算法
    pub fn register_algorithm(&mut self, algorithm: Box<dyn OptimizationAlgorithm + Send + Sync>) {
        let name = algorithm.name().to_string();
        self.optimization_algorithms.insert(name, algorithm);
    }
    
    // 注册策略配置
    pub fn register_strategy(&self, configuration: StrategyConfiguration) {
        let mut strategies = self.strategies.write().unwrap();
        strategies.insert(configuration.name.clone(), configuration);
    }
    
    // 更新策略参数
    pub fn update_strategy_parameter(
        &self,
        strategy_name: &str,
        parameter_name: &str,
        value: ParameterValue,
    ) -> Result<(), OptimizationError> {
        let mut strategies = self.strategies.write().unwrap();
        
        if let Some(strategy) = strategies.get_mut(strategy_name) {
            if let Some(param) = strategy.parameters.get_mut(parameter_name) {
                // 验证参数值是否在允许范围内
                if !self.is_valid_parameter_value(param, &value) {
                    return Err(OptimizationError::InvalidParameterValue);
                }
                
                param.value = value;
                strategy.last_updated = Instant::now();
                Ok(())
            } else {
                Err(OptimizationError::ParameterNotFound)
            }
        } else {
            Err(OptimizationError::StrategyNotFound)
        }
    }
    
    // 检查参数值是否有效
    fn is_valid_parameter_value(&self, param: &StrategyParameter, value: &ParameterValue) -> bool {
        // 类型必须匹配
        if std::mem::discriminant(&param.value) != std::mem::discriminant(value) {
            return false;
        }
        
        // 检查范围约束
        match (value, &param.min_value, &param.max_value) {
            (ParameterValue::Integer(v), Some(ParameterValue::Integer(min)), _) if *v < *min => {
                return false;
            },
            (ParameterValue::Integer(v), _, Some(ParameterValue::Integer(max))) if *v > *max => {
                return false;
            },
            (ParameterValue::Float(v), Some(ParameterValue::Float(min)), _) if *v < *min => {
                return false;
            },
            (ParameterValue::Float(v), _, Some(ParameterValue::Float(max))) if *v > *max => {
                return false;
            },
            (ParameterValue::Duration(v), Some(ParameterValue::Duration(min)), _) if *v < *min => {
                return false;
            },
            (ParameterValue::Duration(v), _, Some(ParameterValue::Duration(max))) if *v > *max => {
                return false;
            },
            _ => {},
        }
        
        true
    }
    
    // 开始优化实验
    pub fn start_experiment(
        &self,
        strategy_name: &str,
        algorithm_name: &str,
        duration: Duration,
    ) -> Result<String, OptimizationError> {
        // 检查是否已有实验在运行
        let current = self.current_experiment.read().unwrap();
        if current.is_some() {
            return Err(OptimizationError::ExperimentAlreadyRunning);
        }
        drop(current);
        
        // 获取策略配置
        let strategies = self.strategies.read().unwrap();
        let strategy = strategies.get(strategy_name)
            .ok_or(OptimizationError::StrategyNotFound)?
            .clone();
        drop(strategies);
        
        // 获取优化算法
        let algorithm = self.optimization_algorithms.get(algorithm_name)
            .ok_or(OptimizationError::AlgorithmNotFound)?;
            
        // 获取历史实验
        let history = self.history.read().unwrap();
        let relevant_history: Vec<_> = history.iter()
            .filter(|exp| exp.strategy_name == strategy_name)
            .cloned()
            .collect();
        drop(history);
        
        // 生成新的实验配置
        let experiment_config = algorithm.generate_next_configuration(&strategy, &relevant_history);
        
        // 创建新实验
        let experiment_id = format!("exp_{}", uuid::Uuid::new_v4());
        let experiment = OptimizationExperiment {
            id: experiment_id.clone(),
            strategy_name: strategy_name.to_string(),
            configuration: experiment_config,
            start_time: Instant::now(),
            end_time: None,
            measurements: Vec::new(),
            score: None,
            status: ExperimentStatus::Running,
        };
        
        // 记录实验
        let mut experiments = self.experiments.write().unwrap();
        experiments.insert(experiment_id.clone(), experiment);
        
        // 更新当前实验
        let mut current = self.current_experiment.write().unwrap();
        *current = Some(experiment_id.clone());
        
        // 启动实验计时器
        let optimizer = Arc::new(self.clone());
        let exp_id = experiment_id.clone();
        
        std::thread::spawn(move || {
            // 收集实验期间的性能数据
            let measurement_interval = Duration::from_secs(10); // 每10秒收集一次
            let end_time = Instant::now() + duration;
            
            while Instant::now() < end_time {
                // 收集性能测量
                let measurement = optimizer.performance_collector.collect_measurements();
                
                // 记录测量结果
                optimizer.record_measurement(&exp_id, measurement);
                
                // 休眠到下一个测量间隔
                std::thread::sleep(measurement_interval);
            }
            
            // 结束实验
            optimizer.complete_experiment(&exp_id);
        });
        
        Ok(experiment_id)
    }
    
    // 记录性能测量
    fn record_measurement(&self, experiment_id: &str, measurement: PerformanceMeasurement) {
        let mut experiments = self.experiments.write().unwrap();
        
        if let Some(experiment) = experiments.get_mut(experiment_id) {
            experiment.measurements.push(measurement);
        }
    }
    
    // 完成实验
    fn complete_experiment(&self, experiment_id: &str) {
        // 更新实验状态
        let mut experiments = self.experiments.write().unwrap();
        
        if let Some(experiment) = experiments.get_mut(experiment_id) {
            experiment.end_time = Some(Instant::now());
            experiment.status = ExperimentStatus::Completed;
            
            // 计算实验得分
            if let Some(algorithm) = self.optimization_algorithms.values().next() {
                let score = algorithm.score_experiment(experiment, experiment.configuration.objective);
                experiment.score = Some(score);
            }
            
            // 复制实验以添加到历史记录
            let completed_experiment = experiment.clone();
            
            // 将实验移动到历史记录
            let mut history = self.history.write().unwrap();
            history.push_back(completed_experiment);
            
            // 保持历史记录大小限制
            while history.len() > self.max_history_size {
                history.pop_front();
            }
        }
        
        // 清除当前实验引用
        let mut current = self.current_experiment.write().unwrap();
        if let Some(current_id) = &*current {
            if current_id == experiment_id {
                *current = None;
            }
        }
    }
    
    // 取消正在运行的实验
    pub fn cancel_current_experiment(&self) -> Result<(), OptimizationError> {
        let current = self.current_experiment.read().unwrap();
        
        if let Some(experiment_id) = &*current {
            drop(current); // 释放读锁
            
            let mut experiments = self.experiments.write().unwrap();
            
            if let Some(experiment) = experiments.get_mut(experiment_id) {
                experiment.end_time = Some(Instant::now());
                experiment.status = ExperimentStatus::Cancelled;
            }
            
            let mut current = self.current_experiment.write().unwrap();
            *current = None;
            
            Ok(())
        } else {
            Err(OptimizationError::NoExperimentRunning)
        }
    }
    
    // 获取最佳策略配置
    pub fn get_best_configuration(
        &self,
        strategy_name: &str,
        objective: OptimizationObjective,
    ) -> Option<StrategyConfiguration> {
        let history = self.history.read().unwrap();
        
        // 筛选相关历史记录
        let relevant_experiments: Vec<_> = history.iter()
            .filter(|exp| exp.strategy_name == strategy_name && 
                          exp.status == ExperimentStatus::Completed)
            .collect();
            
        if relevant_experiments.is_empty() {
            return None;
        }
        
        // 获取任意优化算法计算得分
        if let Some(algorithm) = self.optimization_algorithms.values().next() {
            // 找出得分最高的实验
            let best_experiment = relevant_experiments.iter()
                .max_by(|a, b| {
                    let score_a = a.score.unwrap_or_else(|| 
                        algorithm.score_experiment(*a, objective)
                    );
                    
                    let score_b = b.score.unwrap_or_else(|| 
                        algorithm.score_experiment(*b, objective)
                    );
                    
                    score_a.partial_cmp(&score_b).unwrap_or(std::cmp::Ordering::Equal)
                });
                
            best_experiment.map(|exp| exp.configuration.clone())
        } else {
            None
        }
    }
    
    // 应用最佳配置
    pub fn apply_best_configuration(
        &self,
        strategy_name: &str,
    ) -> Result<(), OptimizationError> {
        let strategies = self.strategies.read().unwrap();
        
        if let Some(strategy) = strategies.get(strategy_name) {
            let objective = strategy.objective;
            drop(strategies); // 释放读锁
            
            if let Some(best_config) = self.get_best_configuration(strategy_name, objective) {
                // 更新当前策略配置
                let mut strategies = self.strategies.write().unwrap();
                strategies.insert(strategy_name.to_string(), best_config);
                
                Ok(())
            } else {
                Err(OptimizationError::NoBestConfiguration)
            }
        } else {
            Err(OptimizationError::StrategyNotFound)
        }
    }
    
    // 获取策略参数值
    pub fn get_parameter_value(
        &self,
        strategy_name: &str,
        parameter_name: &str,
    ) -> Result<ParameterValue, OptimizationError> {
        let strategies = self.strategies.read().unwrap();
        
        if let Some(strategy) = strategies.get(strategy_name) {
            if let Some(param) = strategy.parameters.get(parameter_name) {
                Ok(param.value.clone())
            } else {
                Err(OptimizationError::ParameterNotFound)
            }
        } else {
            Err(OptimizationError::StrategyNotFound)
        }
    }
    
    // 获取实验状态
    pub fn get_experiment_status(&self, experiment_id: &str) -> Result<ExperimentStatus, OptimizationError> {
        let experiments = self.experiments.read().unwrap();
        
        if let Some(experiment) = experiments.get(experiment_id) {
            Ok(experiment.status)
        } else {
            Err(OptimizationError::ExperimentNotFound)
        }
    }
    
    // 获取实验结果
    pub fn get_experiment_results(&self, experiment_id: &str) -> Result<OptimizationResults, OptimizationError> {
        let experiments = self.experiments.read().unwrap();
        
        if let Some(experiment) = experiments.get(experiment_id) {
            // 确保实验已完成
            if experiment.status != ExperimentStatus::Completed {
                return Err(OptimizationError::ExperimentNotCompleted);
            }
            
            // 计算聚合指标
            let mut avg_throughput = 0.0;
            let mut avg_p95_latency = Duration::from_secs(0);
            let mut avg_error_rate = 0.0;
            let mut avg_resource_usage: HashMap<ResourceKind, f64> = HashMap::new();
            
            if !experiment.measurements.is_empty() {
                // 计算平均值
                let count = experiment.measurements.len() as f64;
                
                avg_throughput = experiment.measurements.iter()
                    .map(|m| m.throughput)
                    .sum::<f64>() / count;
                    
                let total_p95_latency = experiment.measurements.iter()
                    .map(|m| m.p95_latency.as_nanos() as f64)
                    .sum::<f64>();
                avg_p95_latency = Duration::from_nanos((total_p95_latency / count) as u64);
                
                avg_error_rate = experiment.measurements.iter()
                    .map(|m| m.error_rate)
                    .sum::<f64>() / count;
                    
                // 计算每种资源类型的平均使用率
                let resource_types: HashSet<_> = experiment.measurements.iter()
                    .flat_map(|m| m.resource_usage.keys())
                    .collect();
                    
                for resource_type in resource_types {
                    let avg = experiment.measurements.iter()
                        .filter_map(|m| m.resource_usage.get(resource_type))
                        .sum::<f64>() / count;
                        
                    avg_resource_usage.insert(*resource_type, avg);
                }
            }
            
            Ok(OptimizationResults {
                experiment_id: experiment_id.to_string(),
                start_time: experiment.start_time,
                end_time: experiment.end_time.unwrap_or(experiment.start_time),
                configuration: experiment.configuration.clone(),
                measurements_count: experiment.measurements.len(),
                score: experiment.score,
                avg_throughput,
                avg_p95_latency,
                avg_error_rate,
                avg_resource_usage,
            })
        } else {
            Err(OptimizationError::ExperimentNotFound)
        }
    }
}

// 优化结果
pub struct OptimizationResults {
    experiment_id: String,
    start_time: Instant,
    end_time: Instant,
    configuration: StrategyConfiguration,
    measurements_count: usize,
    score: Option<f64>,
    avg_throughput: f64,
    avg_p95_latency: Duration,
    avg_error_rate: f64,
    avg_resource_usage: HashMap<ResourceKind, f64>,
}

// 优化错误
pub enum OptimizationError {
    StrategyNotFound,
    ParameterNotFound,
    InvalidParameterValue,
    ExperimentAlreadyRunning,
    NoExperimentRunning,
    ExperimentNotFound,
    ExperimentNotCompleted,
    AlgorithmNotFound,
    NoBestConfiguration,
}

// 贝叶斯优化算法
pub struct BayesianOptimizationAlgorithm {
    name: String,
    description: String,
    exploration_factor: f64,
}

impl BayesianOptimizationAlgorithm {
    pub fn new(exploration_factor: f64) -> Self {
        Self {
            name: "BayesianOptimization".to_string(),
            description: "Bayesian optimization algorithm for parameter tuning".to_string(),
            exploration_factor,
        }
    }
}

impl OptimizationAlgorithm for BayesianOptimizationAlgorithm {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn description(&self) -> &str {
        &self.description
    }
    
    fn generate_next_configuration(
        &self,
        strategy: &StrategyConfiguration,
        history: &[OptimizationExperiment],
    ) -> StrategyConfiguration {
        // 实际贝叶斯优化算法的实现非常复杂，需要高斯过程回归等
        // 这里提供一个简化的实现，基于探索-利用权衡
        
        // 如果没有历史记录，随机生成一个配置
        if history.is_empty() {
            return self.generate_random_configuration(strategy);
        }
        
        // 找出历史最佳配置
        let best_experiment = history.iter()
            .max_by(|a, b| {
                let score_a = a.score.unwrap_or(0.0);
                let score_b = b.score.unwrap_or(0.0);
                score_a.partial_cmp(&score_b).unwrap_or(std::cmp::Ordering::Equal)
            });
            
        // 随机决定是探索新配置还是基于最佳配置进行微调
        let random_value: f64 = rand::random();
        
        if random_value < self.exploration_factor {
            // 探索：生成随机配置
            self.generate_random_configuration(strategy)
        } else if let Some(best) = best_experiment {
            // 利用：基于最佳配置进行小幅度变化
            self.perturb_configuration(&best.configuration)
        } else {
            // 兜底：生成随机配置
            self.generate_random_configuration(strategy)
        }
    }
    
    fn score_experiment(
        &self,
        experiment: &OptimizationExperiment,
        objective: OptimizationObjective,
    ) -> f64 {
        if experiment.measurements.is_empty() {
            return 0.0;
        }
        
        // 计算各指标的平均值
        let count = experiment.measurements.len() as f64;
        
        let avg_throughput = experiment.measurements.iter()
            .map(|m| m.throughput)
            .sum::<f64>() / count;
            
        let avg_p95_latency = experiment.measurements.iter()
            .map(|m| m.p95_latency.as_nanos() as f64)
            .sum::<f64>() / count;
            
        let avg_error_rate = experiment.measurements.iter()
            .map(|m| m.error_rate)
            .sum::<f64>() / count;
            
        let avg_cost = experiment.measurements.iter()
            .map(|m| m.cost_per_task)
            .sum::<f64>() / count;
            
        let avg_energy = experiment.measurements.iter()
            .map(|m| m.energy_usage)
            .sum::<f64>() / count;
            
        // 根据优化目标计算得分
        match objective {
            OptimizationObjective::Throughput => {
                // 更高的吞吐量更好
                avg_throughput
            },
            OptimizationObjective::Latency => {
                // 更低的延迟更好（使用倒数转换为越大越好）
                1_000_000_000.0 / avg_p95_latency.max(1.0)
            },
            OptimizationObjective::ResourceUtilization => {
                // 计算平均资源利用率
                let resource_utilization = experiment.measurements.iter()
                    .flat_map(|m| m.resource_usage.values())
                    .sum::<f64>() / (count * 3.0); // 假设有3种资源类型
                    
                // 目标是接近80%利用率
                1.0 - (resource_utilization - 0.8).abs()
            },
            OptimizationObjective::CostEfficiency => {
                // 更低的每任务成本更好（使用倒数转换为越大越好）
                1.0 / avg_cost.max(0.01)
            },
            OptimizationObjective::EnergyEfficiency => {
                // 更低的能源使用更好（使用倒数转换为越大越好）
                1.0 / avg_energy.max(0.01)
            },
            OptimizationObjective::Resilience => {
                // 更低的错误率更好（使用倒数转换为越大越好）
                1.0 / (avg_error_rate + 0.01)
            },
            OptimizationObjective::Balanced => {
                // 综合考虑多个指标
                let throughput_score = avg_throughput / 100.0; // 归一化
                let latency_score = 1_000_000_000.0 / avg_p95_latency.max(1.0) / 10000.0; // 归一化
                let error_score = 1.0 - avg_error_rate;
                let cost_score = 1.0 / avg_cost.max(0.01) / 100.0; // 归一化
                
                // 平均得分
                (throughput_score + latency_score + error_score + cost_score) / 4.0
            },
        }
    }
}

impl BayesianOptimizationAlgorithm {
    // 生成随机配置
    fn generate_random_configuration(&self, base: &StrategyConfiguration) -> StrategyConfiguration {
        let mut new_params = HashMap::new();
        
        for (name, param) in &base.parameters {
            let new_value = self.generate_random_parameter_value(param);
            new_params.insert(name.clone(), StrategyParameter {
                name: param.name.clone(),
                value: new_value,
                min_value: param.min_value.clone(),
                max_value: param.max_value.clone(),
                step: param.step.clone(),
                description: param.description.clone(),
            });
        }
        
        StrategyConfiguration {
            name: base.name.clone(),
            parameters: new_params,
            objective: base.objective,
            created_at: base.created_at,
            last_updated: Instant::now(),
        }
    }
    
    // 生成随机参数值
    fn generate_random_parameter_value(&self, param: &StrategyParameter) -> ParameterValue {
        match (&param.value, &param.min_value, &param.max_value) {
            (ParameterValue::Integer(_), Some(ParameterValue::Integer(min)), Some(ParameterValue::Integer(max))) => {
                let range = max - min;
                let random = rand::random::<f64>();
                let value = min + (random * range as f64) as i64;
                ParameterValue::Integer(value)
            },
            (ParameterValue::Float(_), Some(ParameterValue::Float(min)), Some(ParameterValue::Float(max))) => {
                let range = max - min;
                let random = rand::random::<f64>();
                let value = min + random * range;
                ParameterValue::Float(value)
            },
            (ParameterValue::Boolean(_), _, _) => {
                ParameterValue::Boolean(rand::random())
            },
            (ParameterValue::Duration(_), Some(ParameterValue::Duration(min)), Some(ParameterValue::Duration(max))) => {
                let min_ns = min.as_nanos() as u64;
                let max_ns = max.as_nanos() as u64;
                let range = max_ns - min_ns;
                let random = rand::random::<f64>();
                let value_ns = min_ns + (random * range as f64) as u64;
                ParameterValue::Duration(Duration::from_nanos(value_ns))
            },
            // 默认情况：返回原始值
            _ => param.value.clone(),
        }
    }
    
    // 微调配置（在最佳配置基础上进行小变化）
    fn perturb_configuration(&self, base: &StrategyConfiguration) -> StrategyConfiguration {
        let mut new_params = HashMap::new();
        
        for (name, param) in &base.parameters {
            let new_value = self.perturb_parameter_value(param);
            new_params.insert(name.clone(), StrategyParameter {
                name: param.name.clone(),
                value: new_value,
                min_value: param.min_value.clone(),
                max_value: param.max_value.clone(),
                step: param.step.clone(),
                description: param.description.clone(),
            });
        }
        
        StrategyConfiguration {
            name: base.name.clone(),
            parameters: new_params,
            objective: base.objective,
            created_at: base.created_at,
            last_updated: Instant::now(),
        }
    }
    
    // 微调参数值
    fn perturb_parameter_value(&self, param: &StrategyParameter) -> ParameterValue {
        match (&param.value, &param.min_value, &param.max_value) {
            (ParameterValue::Integer(current), Some(ParameterValue::Integer(min)), Some(ParameterValue::Integer(max))) => {
                // 在当前值周围生成新值，最大变化幅度为范围的10%
                let range = (max - min) as f64;
                let max_change = (range * 0.1).max(1.0) as i64;
                let change = rand::random::<i64>() % (2 * max_change + 1) - max_change;
                let new_value = (*current + change).max(*min).min(*max);
                ParameterValue::Integer(new_value)
            },
            (ParameterValue::Float(current), Some(ParameterValue::Float(min)), Some(ParameterValue::Float(max))) => {
                // 在当前值周围生成新值，最大变化幅度为范围的10%
                let range = max - min;
                let max_change = range * 0.1;
                let change = rand::random::<f64>() * 2.0 * max_change - max_change;
                let new_value = (*current + change).max(*min).min(*max);
                ParameterValue::Float(new_value)
            },
            (ParameterValue::Boolean(current), _, _) => {
                // 20%概率翻转布尔值
                if rand::random::<f64>() < 0.2 {
                    ParameterValue::Boolean(!current)
                } else {
                    ParameterValue::Boolean(*current)
                }
            },
            (ParameterValue::Duration(current), Some(ParameterValue::Duration(min)), Some(ParameterValue::Duration(max))) => {
                // 在当前值周围生成新值，最大变化幅度为范围的10%
                let min_ns = min.as_nanos() as u64;
                let max_ns = max.as_nanos() as u64;
                let current_ns = current.as_nanos() as u64;
                let range = max_ns - min_ns;
                let max_change = (range / 10).max(1);
                let change = rand::random::<u64>() % (2 * max_change + 1) - max_change;
                let new_value_ns = current_ns.saturating_add(change).max(min_ns).min(max_ns);
                ParameterValue::Duration(Duration::from_nanos(new_value_ns))
            },
            // 默认情况：返回原始值
            _ => param.value.clone(),
        }
    }
}

// 系统性能收集器
pub struct SystemPerformanceCollector {
    metrics_provider: Box<dyn MetricsProvider + Send + Sync>,
}

// 指标提供者特征
pub trait MetricsProvider {
    fn get_throughput(&self) -> f64;
    fn get_latency_percentiles(&self) -> (Duration, Duration, Duration); // p50, p95, p99
    fn get_error_rate(&self) -> f64;
    fn get_resource_usage(&self) -> HashMap<ResourceKind, f64>;
    fn get_cost_metrics(&self) -> (f64, f64); // cost_per_task, energy_usage
}

impl SystemPerformanceCollector {
    pub fn new(metrics_provider: Box<dyn MetricsProvider + Send + Sync>) -> Self {
        Self {
            metrics_provider,
        }
    }
}

impl PerformanceCollector for SystemPerformanceCollector {
    fn collect_measurements(&self) -> PerformanceMeasurement {
        // 从指标提供者获取各项指标
        let throughput = self.metrics_provider.get_throughput();
        let (p50_latency, p95_latency, p99_latency) = self.metrics_provider.get_latency_percentiles();
        let error_rate = self.metrics_provider.get_error_rate();
        let resource_usage = self.metrics_provider.get_resource_usage();
        let (cost_per_task, energy_usage) = self.metrics_provider.get_cost_metrics();
        
        PerformanceMeasurement {
            timestamp: Instant::now(),
            throughput,
            p50_latency,
            p95_latency,
            p99_latency,
            error_rate,
            resource_usage,
            cost_per_task,
            energy_usage,
        }
    }
    
    fn name(&self) -> &str {
        "SystemPerformanceCollector"
    }
}

// 实现Clone以支持线程间共享
impl Clone for StrategyOptimizer {
    fn clone(&self) -> Self {
        Self {
            strategies: RwLock::new(self.strategies.read().unwrap().clone()),
            experiments: RwLock::new(self.experiments.read().unwrap().clone()),
            history: RwLock::new(self.history.read().unwrap().clone()),
            current_experiment: RwLock::new(self.current_experiment.read().unwrap().clone()),
            optimization_algorithms: self.optimization_algorithms.clone(),
            performance_collector: self.performance_collector.clone_box(),
            max_history_size: self.max_history_size,
        }
    }
}

// 支持性能收集器的Clone
pub trait PerformanceCollectorClone {
    fn clone_box(&self) -> Box<dyn PerformanceCollector + Send + Sync>;
}

impl<T> PerformanceCollectorClone for T
where
    T: 'static + PerformanceCollector + Clone + Send + Sync
{
    fn clone_box(&self) -> Box<dyn PerformanceCollector + Send + Sync> {
        Box::new(self.clone())
    }
}

impl Clone for Box<dyn PerformanceCollector + Send + Sync> {
    fn clone(&self) -> Self {
        self.clone_box()
    }
}

// 实现OptimizationExperiment的Clone
impl Clone for OptimizationExperiment {
    fn clone(&self) -> Self {
        Self {
            id: self.id.clone(),
            strategy_name: self.strategy_name.clone(),
            configuration: self.configuration.clone(),
            start_time: self.start_time,
            end_time: self.end_time,
            measurements: self.measurements.clone(),
            score: self.score,
            status: self.status,
        }
    }
}

// 实现资源自适应调度策略
pub struct ResourceAdaptiveSchedulingStrategy {
    name: String,
    task_batch_size: StrategyParameter,
    max_concurrent_tasks: StrategyParameter,
    preemption_threshold: StrategyParameter,
    locality_preference_weight: StrategyParameter,
    load_balancing_interval: StrategyParameter,
    objective: OptimizationObjective,
}

impl ResourceAdaptiveSchedulingStrategy {
    pub fn new(objective: OptimizationObjective) -> Self {
        Self {
            name: "ResourceAdaptiveScheduling".to_string(),
            task_batch_size: StrategyParameter {
                name: "task_batch_size".to_string(),
                value: ParameterValue::Integer(10),
                min_value: Some(ParameterValue::Integer(1)),
                max_value: Some(ParameterValue::Integer(100)),
                step: Some(ParameterValue::Integer(1)),
                description: "Number of tasks to batch for scheduling".to_string(),
            },
            max_concurrent_tasks: StrategyParameter {
                name: "max_concurrent_tasks".to_string(),
                value: ParameterValue::Integer(100),
                min_value: Some(ParameterValue::Integer(10)),
                max_value: Some(ParameterValue::Integer(1000)),
                step: Some(ParameterValue::Integer(10)),
                description: "Maximum number of concurrent tasks".to_string(),
            },
            preemption_threshold: StrategyParameter {
                name: "preemption_threshold".to_string(),
                value: ParameterValue::Float(0.8),
                min_value: Some(ParameterValue::Float(0.5)),
                max_value: Some(ParameterValue::Float(0.95)),
                step: Some(ParameterValue::Float(0.05)),
                description: "Resource utilization threshold for task preemption".to_string(),
            },
            locality_preference_weight: StrategyParameter {
                name: "locality_preference_weight".to_string(),
                value: ParameterValue::Float(0.7),
                min_value: Some(ParameterValue::Float(0.0)),
                max_value: Some(ParameterValue::Float(1.0)),
                step: Some(ParameterValue::Float(0.1)),
                description: "Weight for data locality preference".to_string(),
            },
            load_balancing_interval: StrategyParameter {
                name: "load_balancing_interval".to_string(),
                value: ParameterValue::Duration(Duration::from_secs(30)),
                min_value: Some(ParameterValue::Duration(Duration::from_secs(5))),
                max_value: Some(ParameterValue::Duration(Duration::from_secs(300))),
                step: Some(ParameterValue::Duration(Duration::from_secs(5))),
                description: "Interval between load balancing operations".to_string(),
            },
            objective,
        }
    }
    
    // 转换为策略配置
    pub fn to_configuration(&self) -> StrategyConfiguration {
        let mut parameters = HashMap::new();
        parameters.insert("task_batch_size".to_string(), self.task_batch_size.clone());
        parameters.insert("max_concurrent_tasks".to_string(), self.max_concurrent_tasks.clone());
        parameters.insert("preemption_threshold".to_string(), self.preemption_threshold.clone());
        parameters.insert("locality_preference_weight".to_string(), self.locality_preference_weight.clone());
        parameters.insert("load_balancing_interval".to_string(), self.load_balancing_interval.clone());
        
        StrategyConfiguration {
            name: self.name.clone(),
            parameters,
            objective: self.objective,
            created_at: Instant::now(),
            last_updated: Instant::now(),
        }
    }
    
    // 应用策略配置
    pub fn apply_configuration(&mut self, config: &StrategyConfiguration) {
        if let Some(param) = config.parameters.get("task_batch_size") {
            self.task_batch_size = param.clone();
        }
        
        if let Some(param) = config.parameters.get("max_concurrent_tasks") {
            self.max_concurrent_tasks = param.clone();
        }
        
        if let Some(param) = config.parameters.get("preemption_threshold") {
            self.preemption_threshold = param.clone();
        }
        
        if let Some(param) = config.parameters.get("locality_preference_weight") {
            self.locality_preference_weight = param.clone();
        }
        
        if let Some(param) = config.parameters.get("load_balancing_interval") {
            self.load_balancing_interval = param.clone();
        }
        
        self.objective = config.objective;
    }
    
    // 获取当前批处理大小
    pub fn get_batch_size(&self) -> i64 {
        if let ParameterValue::Integer(value) = self.task_batch_size.value {
            value
        } else {
            10 // 默认值
        }
    }
    
    // 获取最大并发任务数
    pub fn get_max_concurrent_tasks(&self) -> i64 {
        if let ParameterValue::Integer(value) = self.max_concurrent_tasks.value {
            value
        } else {
            100 // 默认值
        }
    }
    
    // 获取抢占阈值
    pub fn get_preemption_threshold(&self) -> f64 {
        if let ParameterValue::Float(value) = self.preemption_threshold.value {
            value
        } else {
            0.8 // 默认值
        }
    }
    
    // 获取位置偏好权重
    pub fn get_locality_preference_weight(&self) -> f64 {
        if let ParameterValue::Float(value) = self.locality_preference_weight.value {
            value
        } else {
            0.7 // 默认值
        }
    }
    
    // 获取负载均衡间隔
    pub fn get_load_balancing_interval(&self) -> Duration {
        if let ParameterValue::Duration(value) = self.load_balancing_interval.value {
            value
        } else {
            Duration::from_secs(30) // 默认值
        }
    }
}

// 工作流优化应用示例
pub fn optimize_workflow_system() {
    // 创建资源自适应调度策略
    let strategy = ResourceAdaptiveSchedulingStrategy::new(OptimizationObjective::Balanced);
    let strategy_config = strategy.to_configuration();
    
    // 创建性能收集器
    let metrics_provider = SimpleMetricsProvider::new();
    let performance_collector = Box::new(SystemPerformanceCollector::new(
        Box::new(metrics_provider)
    ));
    
    // 创建策略优化器
    let mut optimizer = StrategyOptimizer::new(performance_collector, 100);
    
    // 注册贝叶斯优化算法
    optimizer.register_algorithm(Box::new(BayesianOptimizationAlgorithm::new(0.3)));
    
    // 注册策略配置
    optimizer.register_strategy(strategy_config);
    
    // 开始优化实验
    let experiment_id = optimizer.start_experiment(
        "ResourceAdaptiveScheduling",
        "BayesianOptimization",
        Duration::from_secs(300),
    ).unwrap();
    
    println!("Started optimization experiment: {}", experiment_id);
    
    // 在实际应用中，我们会等待实验完成
    // 这里简化为休眠一段时间
    std::thread::sleep(Duration::from_secs(5));
    
    // 应用最佳配置
    match optimizer.apply_best_configuration("ResourceAdaptiveScheduling") {
        Ok(_) => println!("Applied best configuration"),
        Err(e) => println!("Failed to apply best configuration: {:?}", e),
    }
}

// 简单指标提供者实现（模拟）
pub struct SimpleMetricsProvider {
    last_update: Instant,
    oscillation_phase: f64,
}

impl SimpleMetricsProvider {
    pub fn new() -> Self {
        Self {
            last_update: Instant::now(),
            oscillation_phase: 0.0,
        }
    }
}

impl MetricsProvider for SimpleMetricsProvider {
    fn get_throughput(&self) -> f64 {
        // 模拟吞吐量变化
        let base = 100.0;
        let time_factor = self.last_update.elapsed().as_secs_f64() * 0.1;
        let oscillation = (self.oscillation_phase + time_factor).sin() * 20.0;
        
        base + oscillation + rand::random::<f64>() * 10.0
    }
    
    fn get_latency_percentiles(&self) -> (Duration, Duration, Duration) {
        // 模拟延迟变化
        let base_ms = 50.0;
        let time_factor = self.last_update.elapsed().as_secs_f64() * 0.1;
        let oscillation = (self.oscillation_phase + time_factor).cos() * 10.0;
        
        let p50 = base_ms + oscillation;
        let p95 = p50 * 1.5 + rand::random::<f64>() * 10.0;
        let p99 = p95 * 1.3 + rand::random::<f64>() * 15.0;
        
        (
            Duration::from_millis(p50 as u64),
            Duration::from_millis(p95 as u64),
            Duration::from_millis(p99 as u64),
        )
    }
    
    fn get_error_rate(&self) -> f64 {
        // 模拟错误率变化
        let base = 0.01; // 1%基础错误率
        let time_factor = self.last_update.elapsed().as_secs_f64() * 0.05;
        let oscillation = (self.oscillation_phase + time_factor).sin().abs() * 0.02;
        
        base + oscillation
    }
    
    fn get_resource_usage(&self) -> HashMap<ResourceKind, f64> {
        // 模拟资源使用率变化
        let time_factor = self.last_update.elapsed().as_secs_f64() * 0.1;
        let cpu_oscillation = (self.oscillation_phase + time_factor).sin() * 0.15;
        let memory_oscillation = (self.oscillation_phase + time_factor + 1.0).cos() * 0.1;
        let disk_oscillation = (self.oscillation_phase + time_factor + 2.0).sin() * 0.05;
        
        let mut usage = HashMap::new();
        usage.insert(ResourceKind::CPU, 0.6 + cpu_oscillation + rand::random::<f64>() * 0.05);
        usage.insert(ResourceKind::Memory, 0.7 + memory_oscillation + rand::random::<f64>() * 0.03);
        usage.insert(ResourceKind::Disk, 0.4 + disk_oscillation + rand::random::<f64>() * 0.02);
        
        usage
    }
    
    fn get_cost_metrics(&self) -> (f64, f64) {
        // 模拟成本和能源使用变化
        let cost_per_task = 0.01 + rand::random::<f64>() * 0.002;
        let energy_usage = 100.0 + rand::random::<f64>() * 20.0;
        
        (cost_per_task, energy_usage)
    }
}

impl Clone for SimpleMetricsProvider {
    fn clone(&self) -> Self {
        Self {
            last_update: self.last_update,
            oscillation_phase: self.oscillation_phase,
        }
    }
}

impl Clone for SystemPerformanceCollector {
    fn clone(&self) -> Self {
        Self {
            metrics_provider: self.metrics_provider.clone_box(),
        }
    }
}

// 支持指标提供者的Clone
pub trait MetricsProviderClone {
    fn clone_box(&self) -> Box<dyn MetricsProvider + Send + Sync>;
}

impl<T> MetricsProviderClone for T
where
    T: 'static + MetricsProvider + Clone + Send + Sync
{
    fn clone_box(&self) -> Box<dyn MetricsProvider + Send + Sync> {
        Box::new(self.clone())
    }
}

impl Clone for Box<dyn MetricsProvider + Send + Sync> {
    fn clone(&self) -> Self {
        self.clone_box()
    }
}
```

## 系统演化框架

### 演化代数

演化代数提供了一种形式化方法，用于描述系统如何随时间变化，以及如何保持关键不变量。

```rust
// 演化代数实现
use std::collections::{HashMap, HashSet};
use std::fmt::{Debug, Display};
use std::marker::PhantomData;
use std::sync::{Arc, RwLock};
use semver::{Version, VersionReq};

// 系统状态特征
pub trait SystemState: Clone + Send + Sync + 'static {
    type Id: Clone + Eq + std::hash::Hash + Send + Sync + 'static;
    
    fn id(&self) -> Self::Id;
    fn version(&self) -> Version;
}

// 系统进化特征
pub trait EvolutionAlgebra<S: SystemState> {
    type Error: Debug + Display;
    
    // 基本操作：升级系统状态到新版本
    fn upgrade(&self, state: S, target_version: &Version) -> Result<S, Self::Error>;
    
    // 基本操作：降级系统状态到旧版本
    fn downgrade(&self, state: S, target_version: &Version) -> Result<S, Self::Error>;
    
    // 基本操作：检查状态是否兼容目标版本
    fn is_compatible(&self, state: &S, target_version: &Version) -> bool;
    
    // 衍生操作：检查系统是否可以直接迁移
    fn can_migrate(&self, state: &S, target_version: &Version) -> bool {
        self.is_compatible(state, target_version) || 
        self.get_migration_path(state.version(), target_version).is_some()
    }
    
    // 衍生操作：获取版本迁移路径
    fn get_migration_path(&self, from: Version, to: &Version) -> Option<Vec<Version>>;
    
    // 衍生操作：获取所有兼容的版本
    fn get_compatible_versions(&self, state: &S) -> HashSet<Version>;
}

// 进化记录
#[derive(Clone, Debug)]
pub struct EvolutionRecord<S: SystemState> {
    from_version: Version,
    to_version: Version,
    timestamp: chrono::DateTime<chrono::Utc>,
    state_id: S::Id,
    success: bool,
    error_message: Option<String>,
    duration_ms: u64,
}

// 演化注册表
pub struct EvolutionRegistry<S: SystemState, E: EvolutionAlgebra<S>> {
    // 版本兼容性管理
    version_map: VersionMap,
    // 升级转换器
    upgrade_transformers: HashMap<(Version, Version), Box<dyn Fn(S) -> Result<S, E::Error> + Send + Sync>>,
    // 降级转换器
    downgrade_transformers: HashMap<(Version, Version), Box<dyn Fn(S) -> Result<S, E::Error> + Send + Sync>>,
    // 版本兼容性验证器
    compatibility_validators: HashMap<Version, Box<dyn Fn(&S) -> bool + Send + Sync>>,
    // 演化历史记录
    evolution_history: RwLock<Vec<EvolutionRecord<S>>>,
    // 幻影数据（用于类型标记）
    _phantom: PhantomData<E>,
}

// 版本映射
pub struct VersionMap {
    // 直接兼容关系：版本 -> 兼容的版本集合
    direct_compatibility: HashMap<Version, HashSet<Version>>,
    // 升级路径：(源版本, 目标版本) -> 中间版本路径
    upgrade_paths: HashMap<(Version, Version), Vec<Version>>,
    // 所有已知版本
    known_versions: HashSet<Version>,
    // 版本顺序（按语义版本排序）
    ordered_versions: Vec<Version>,
}

impl VersionMap {
    pub fn new() -> Self {
        Self {
            direct_compatibility: HashMap::new(),
            upgrade_paths: HashMap::new(),
            known_versions: HashSet::new(),
            ordered_versions: Vec::new(),
        }
    }
    
    // 注册新版本
    pub fn register_version(&mut self, version: Version) {
        if !self.known_versions.contains(&version) {
            self.known_versions.insert(version.clone());
            
            // 添加到有序版本列表
            self.ordered_versions.push(version.clone());
            self.ordered_versions.sort();
            
            // 初始化兼容性集合
            if !self.direct_compatibility.contains_key(&version) {
                let mut compatibility_set = HashSet::new();
                compatibility_set.insert(version.clone());
                self.direct_compatibility.insert(version, compatibility_set);
            }
        }
    }
    
    // 设置直接兼容关系
    pub fn set_compatible(&mut self, from: &Version, to: &Version) {
        // 确保两个版本都已注册
        self.register_version(from.clone());
        self.register_version(to.clone());
        
        // 添加兼容性关系
        if let Some(compatibility_set) = self.direct_compatibility.get_mut(from) {
            compatibility_set.insert(to.clone());
        }
    }
    
    // 计算所有升级路径
    pub fn compute_upgrade_paths(&mut self) {
        // 清除现有路径
        self.upgrade_paths.clear();
        
        // 按版本顺序计算路径
        for i in 0..self.ordered_versions.len() {
            for j in i+1..self.ordered_versions.len() {
                let from = &self.ordered_versions[i];
                let to = &self.ordered_versions[j];
                
                // 如果直接兼容，则路径为空
                if self.is_directly_compatible(from, to) {
                    self.upgrade_paths.insert((from.clone(), to.clone()), Vec::new());
                    continue;
                }
                
                // 否则尝试找到中间版本路径
                if let Some(path) = self.find_shortest_path(from, to) {
                    self.upgrade_paths.insert((from.clone(), to.clone()), path);
                }
            }
        }
    }
    
    // 检查两个版本是否直接兼容
    pub fn is_directly_compatible(&self, from: &Version, to: &Version) -> bool {
        if let Some(compatibility_set) = self.direct_compatibility.get(from) {
            compatibility_set.contains(to)
        } else {
            false
        }
    }
    
    // 获取升级路径
    pub fn get_upgrade_path(&self, from: &Version, to: &Version) -> Option<Vec<Version>> {
        self.upgrade_paths.get(&(from.clone(), to.clone())).cloned()
    }
    
    // 获取兼容版本集合
    pub fn get_compatible_versions(&self, version: &Version) -> HashSet<Version> {
        if let Some(compatibility_set) = self.direct_compatibility.get(version) {
            compatibility_set.clone()
        } else {
            let mut set = HashSet::new();
            set.insert(version.clone());
            set
        }
    }
    
    // 寻找从from到to的最短路径
    fn find_shortest_path(&self, from: &Version, to: &Version) -> Option<Vec<Version>> {
        // 使用广度优先搜索找最短路径
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();
        let mut paths = HashMap::new();
        
        visited.insert(from.clone());
        queue.push_back(from.clone());
        paths.insert(from.clone(), Vec::new());
        
        while let Some(current) = queue.pop_front() {
            // 获取当前版本直接兼容的所有版本
            if let Some(compatibility_set) = self.direct_compatibility.get(&current) {
                for next in compatibility_set {
                    if !visited.contains(next) {
                        visited.insert(next.clone());
                        
                        // 构建到这个版本的路径
                        let mut path = paths.get(&current).cloned().unwrap_or_default();
                        path.push(next.clone());
                        paths.insert(next.clone(), path.clone());
                        
                        // 如果找到目标版本，返回路径
                        if next == to {
                            return Some(path);
                        }
                        
                        queue.push_back(next.clone());
                    }
                }
            }
        }
        
        None // 没有找到路径
    }
}

impl<S: SystemState, E: EvolutionAlgebra<S>> EvolutionRegistry<S, E> {
    pub fn new() -> Self {
        Self {
            version_map: VersionMap::new(),
            upgrade_transformers: HashMap::new(),
            downgrade_transformers: HashMap::new(),
            compatibility_validators: HashMap::new(),
            evolution_history: RwLock::new(Vec::new()),
            _phantom: PhantomData,
        }
    }
    
    // 注册版本
    pub fn register_version(&mut self, version: Version) {
        self.version_map.register_version(version);
    }
    
    // 设置版本兼容性
    pub fn set_compatible(&mut self, from: &Version, to: &Version) {
        self.version_map.set_compatible(from, to);
    }
    
    // 注册升级转换器
    pub fn register_upgrade<F>(&mut self, from: Version, to: Version, transformer: F)
    where
        F: Fn(S) -> Result<S, E::Error> + Send + Sync + 'static,
    {
        // 注册版本
        self.register_version(from.clone());
        self.register_version(to.clone());
        
        // 存储转换器
        self.upgrade_transformers.insert((from, to), Box::new(transformer));
        
        // 重新计算升级路径
        self.version_map.compute_upgrade_paths();
    }
    
    // 注册降级转换器
    pub fn register_downgrade<F>(&mut self, from: Version, to: Version, transformer: F)
    where
        F: Fn(S) -> Result<S, E::Error> + Send + Sync + 'static,
    {
        // 注册版本
        self.register_version(from.clone());
        self.register_version(to.clone());
        
        // 存储转换器
        self.downgrade_transformers.insert((from, to), Box::new(transformer));
    }
    
    // 注册兼容性验证器
    pub fn register_validator<F>(&mut self, version: Version, validator: F)
    where
        F: Fn(&S) -> bool + Send + Sync + 'static,
    {
        // 注册版本
        self.register_version(version.clone());
        
        // 存储验证器
        self.compatibility_validators.insert(version, Box::new(validator));
    }
    
    // 执行升级
    pub fn execute_upgrade(&self, state: S, target_version: &Version) -> Result<S, E::Error> {
        let start_time = std::time::Instant::now();
        let state_id = state.id();
        let from_version = state.version();
        
        // 检查目标版本是否已注册
        if !self.version_map.known_versions.contains(target_version) {
            let error = format!("Unknown target version: {}", target_version);
            self.record_evolution(
                from_version.clone(),
                target_version.clone(),
                state_id,
                false,
                Some(error),
                start_time.elapsed().as_millis() as u64,
            );
            return Err(E::Error::from(error));
        }
        
        // 如果已经是目标版本，直接返回
        if from_version == *target_version {
            return Ok(state);
        }
        
        // 检查是否可以直接升级
        if self.version_map.is_directly_compatible(&from_version, target_version) {
            // 直接兼容，尝试使用转换器
            if let Some(transformer) = self.upgrade_transformers.get(&(from_version.clone(), target_version.clone())) {
                match transformer(state) {
                    Ok(new_state) => {
                        // 记录成功的演化
                        self.record_evolution(
                            from_version,
                            target_version.clone(),
                            state_id,
                            true,
                            None,
                            start_time.elapsed().as_millis() as u64,
                        );
                        
                        return Ok(new_state);
                    },
                    Err(e) => {
                        // 记录失败的演化
                        self.record_evolution(
                            from_version,
                            target_version.clone(),
                            state_id,
                            false,
                            Some(format!("{}", e)),
                            start_time.elapsed().as_millis() as u64,
                        );
                        
                        return Err(e);
                    }
                }
            }
        }
        
        // 尝试找升级路径
        if let Some(path) = self.version_map.get_upgrade_path(&from_version, target_version) {
            // 沿路径逐步升级
            let mut current_state = state;
            let mut current_version = from_version;
            
            for intermediate_version in path {
                if let Some(transformer) = self.upgrade_transformers.get(&(current_version.clone(), intermediate_version.clone())) {
                    match transformer(current_state) {
                        Ok(new_state) => {
                            current_state = new_state;
                            current_version = intermediate_version;
                        },
                        Err(e) => {
                            // 记录失败的演化
                            self.record_evolution(
                                from_version,
                                target_version.clone(),
                                state_id,
                                false,
                                Some(format!("Failed at intermediate version {}: {}", intermediate_version, e)),
                                start_time.elapsed().as_millis() as u64,
                            );
                            
                            return Err(e);
                        }
                    }
                } else {
                    let error = format!("Missing transformer from {} to {}", current_version, intermediate_version);
                    self.record_evolution(
                        from_version,
                        target_version.clone(),
                        state_id,
                        false,
                        Some(error.clone()),
                        start_time.elapsed().as_millis() as u64,
                    );
                    
                    return Err(E::Error::from(error));
                }
            }
            
            // 完成最后一步升级
            if let Some(transformer) = self.upgrade_transformers.get(&(current_version.clone(), target_version.clone())) {
                match transformer(current_state) {
                    Ok(final_state) => {
                        // 记录成功的演化
                        self.record_evolution(
                            from_version,
                            target_version.clone(),
                            state_id,
                            true,
                            None,
                            start_time.elapsed().as_millis() as u64,
                        );
                        
                        return Ok(final_state);
                    },
                    Err(e) => {
                        // 记录失败的演化
                        self.record_evolution(
                            from_version,
                            target_version.clone(),
                            state_id,
                            false,
                            Some(format!("Failed at final step: {}", e)),
                            start_time.elapsed().as_millis() as u64,
                        );
                        
                        return Err(e);
                    }
                }
            }
        }
        
        // 无法找到升级路径
        let error = format!("No upgrade path from {} to {}", from_version, target_version);
        self.record_evolution(
            from_version,
            target_version.clone(),
            state_id,
            false,
            Some(error.clone()),
            start_time.elapsed().as_millis() as u64,
        );
        
        Err(E::Error::from(error))
    }
    
    // 执行降级
    pub fn execute_downgrade(&self, state: S, target_version: &Version) -> Result<S, E::Error> {
        let start_time = std::time::Instant::now();
        let state_id = state.id();
        let from_version = state.version();
        
        // 检查目标版本是否已注册
        if !self.version_map.known_versions.contains(target_version) {
            let error = format!("Unknown target version: {}", target_version);
            self.record_evolution(
                from_version.clone(),
                target_version.clone(),
                state_id,
                false,
                Some(error.clone()),
                start_time.elapsed().as_millis() as u64,
            );
            
            return Err(E::Error::from(error));
        }
        
        // 如果已经是目标版本，直接返回
        if from_version == *target_version {
            return Ok(state);
        }
        
        // 尝试使用降级转换器
        if let Some(transformer) = self.downgrade_transformers.get(&(from_version.clone(), target_version.clone())) {
            match transformer(state) {
                Ok(new_state) => {
                    // 记录成功的演化
                    self.record_evolution(
                        from_version,
                        target_version.clone(),
                        state_id,
                        true,
                        None,
                        start_time.elapsed().as_millis() as u64,
                    );
                    
                    return Ok(new_state);
                },
                Err(e) => {
                    // 记录失败的演化
                    self.record_evolution(
                        from_version,
                        target_version.clone(),
                        state_id,
                        false,
                        Some(format!("{}", e)),
                        start_time.elapsed().as_millis() as u64,
                    );
                    
                    return Err(e);
                }
            }
        }
        
        // 无法直接降级，尝试找路径
        // 注意：降级路径可能与升级路径不同，这里简化处理
        let error = format!("No direct downgrade path from {} to {}", from_version, target_version);
        self.record_evolution(
            from_version,
            target_version.clone(),
            state_id,
            false,
            Some(error.clone()),
            start_time.elapsed().as_millis() as u64,
        );
        
        Err(E::Error::from(error))
    }
    
    // 检查状态是否兼容目标版本
    pub fn check_compatibility(&self, state: &S, target_version: &Version) -> bool {
        // 首先检查版本是否相同
        if state.version() == *target_version {
            return true;
        }
        
        // 检查是否直接兼容
        if self.version_map.is_directly_compatible(&state.version(), target_version) {
            // 如果有验证器，使用验证器检查
            if let Some(validator) = self.compatibility_validators.get(target_version) {
                return validator(state);
            }
            
            // 没有验证器，默认兼容
            return true;
        }
        
        false
    }
    
    // 获取版本兼容性报告
    pub fn get_compatibility_report(&self, state: &S) -> CompatibilityReport {
        let current_version = state.version();
        let compatible_versions = self.version_map.get_compatible_versions(&current_version);
        
        // 找出所有可升级版本
        let mut upgradable_versions = HashSet::new();
        for version in &self.version_map.known_versions {
            if *version > current_version && 
               (self.version_map.is_directly_compatible(&current_version, version) || 
                self.version_map.get_upgrade_path(&current_version, version).is_some()) {
                upgradable_versions.insert(version.clone());
            }
        }
        
        // 找出所有可降级版本
        let mut downgradable_versions = HashSet::new();
        for version in &self.version_map.known_versions {
            if *version < current_version && 
               self.downgrade_transformers.contains_key(&(current_version.clone(), version.clone())) {
                downgradable_versions.insert(version.clone());
            }
        }
        
        CompatibilityReport {
            current_version,
            compatible_versions,
            upgradable_versions,
            downgradable_versions,
        }
    }
    
    // 记录演化历史
    fn record_evolution(
        &self,
        from_version: Version,
        to_version: Version,
        state_id: S::Id,
        success: bool,
        error_message: Option<String>,
        duration_ms: u64,
    ) {
        let record = EvolutionRecord {
            from_version,
            to_version,
            timestamp: chrono::Utc::now(),
            state_id,
            success,
            error_message,
            duration_ms,
        };
        
        let mut history = self.evolution_history.write().unwrap();
        history.push(record);
    }
    
    // 获取演化历史
    pub fn get_evolution_history(&self) -> Vec<EvolutionRecord<S>> {
        let history = self.evolution_history.read().unwrap();
        history.clone()
    }
    
    // 获取特定状态的演化历史
    pub fn get_state_evolution_history(&self, state_id: &S::Id) -> Vec<EvolutionRecord<S>> {
        let history = self.evolution_history.read().unwrap();
        history.iter()
            .filter(|record| &record.state_id == state_id)
            .cloned()
            .collect()
    }
}

// 兼容性报告
#[derive(Clone, Debug)]
pub struct CompatibilityReport {
    pub current_version: Version,
    pub compatible_versions: HashSet<Version>,
    pub upgradable_versions: HashSet<Version>,
    pub downgradable_versions: HashSet<Version>,
}

// 演化代数实现
pub struct SystemEvolutionAlgebra<S: SystemState> {
    registry: Arc<EvolutionRegistry<S, Self>>,
}

// 演化错误
#[derive(Debug)]
pub struct EvolutionError {
    message: String,
}

impl Display for EvolutionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Evolution Error: {}", self.message)
    }
}

impl std::error::Error for EvolutionError {}

impl From<String> for EvolutionError {
    fn from(message: String) -> Self {
        Self { message }
    }
}

impl<S: SystemState> SystemEvolutionAlgebra<S> {
    pub fn new() -> Self {
        let registry = Arc::new(EvolutionRegistry::new());
        Self { registry }
    }
    
    // 获取注册表引用
    pub fn registry(&self) -> Arc<EvolutionRegistry<S, Self>> {
        self.registry.clone()
    }
}

impl<S: SystemState> EvolutionAlgebra<S> for SystemEvolutionAlgebra<S> {
    type Error = EvolutionError;
    
    fn upgrade(&self, state: S, target_version: &Version) -> Result<S, Self::Error> {
        self.registry.execute_upgrade(state, target_version)
    }
    
    fn downgrade(&self, state: S, target_version: &Version) -> Result<S, Self::Error> {
        self.registry.execute_downgrade(state, target_version)
    }
    
    fn is_compatible(&self, state: &S, target_version: &Version) -> bool {
        self.registry.check_compatibility(state, target_version)
    }
    
    fn get_migration_path(&self, from: Version, to: &Version) -> Option<Vec<Version>> {
        self.registry.version_map.get_upgrade_path(&from, to)
    }
    
    fn get_compatible_versions(&self, state: &S) -> HashSet<Version> {
        self.registry.version_map.get_compatible_versions(&state.version())
    }
}

// 使用VecDeque
use std::collections::VecDeque;

// 演化代数使用示例
fn evolution_algebra_example() {
    // 定义工作流状态
    #[derive(Clone, Debug)]
    struct WorkflowState {
        id: String,
        version: Version,
        definition: WorkflowDefinition,
    }
    
    #[derive(Clone, Debug)]
    struct WorkflowDefinition {
        name: String,
        tasks: Vec<TaskDefinition>,
        connections: Vec<(String, String)>,
    }
    
    #[derive(Clone, Debug)]
    struct TaskDefinition {
        id: String,
        name: String,
        task_type: String,
        config: HashMap<String, String>,
    }
    
    impl SystemState for WorkflowState {
        type Id = String;
        
        fn id(&self) -> Self::Id {
            self.id.clone()
        }
        
        fn version(&self) -> Version {
            self.version.clone()
        }
    }
    
    // 创建演化代数
    let evolution_algebra = SystemEvolutionAlgebra::<WorkflowState>::new();
    let registry = evolution_algebra.registry();
    
    // 注册版本
    let mut registry_mut = Arc::get_mut(&mut evolution_algebra.registry()).unwrap();
    registry_mut.register_version(Version::new(1, 0, 0));
    registry_mut.register_version(Version::new(1, 1, 0));
    registry_mut.register_version(Version::new(2, 0, 0));
    
    // 设置兼容性
    registry_mut.set_compatible(&Version::new(1, 0, 0), &Version::new(1, 1, 0));
    
    // 注册升级转换器
    registry_mut.register_upgrade(
        Version::new(1, 0, 0), 
        Version::new(1, 1, 0), 
        |mut state| {
            // 升级v1.0.0到v1.1.0的逻辑
            state.version = Version::new(1, 1, 0);
            
            // 添加新的配置项到所有任务
            for task in &mut state.definition.tasks {
                task.config.insert("added_in_1_1_0".to_string(), "true".to_string());
            }
            
            Ok(state)
        }
    );
    
    registry_mut.register_upgrade(
        Version::new(1, 1, 0), 
        Version::new(2, 0, 0), 
        |mut state| {
            // 升级v1.1.0到v2.0.0的逻辑
            state.version = Version::new(2, 0, 0);
            
            // 修改连接格式
            let new_connections = state.definition.connections.iter()
                .map(|(from, to)| (format!("task:{}", from), format!("task:{}", to)))
                .collect();
            
            state.definition.connections = new_connections;
            
            Ok(state)
        }
    );
    
    registry_mut.register_downgrade(
        Version::new(2, 0, 0), 
        Version::new(1, 1, 0), 
        |mut state| {
            // 降级v2.0.0到v1.1.0的逻辑
            state.version = Version::new(1, 1, 0);
            
            // 恢复旧的连接格式
            let old_connections = state.definition.connections.iter()
                .filter_map(|(from, to)| {
                    let from = from.strip_prefix("task:")?;
                    let to = to.strip_prefix("task:")?;
                    Some((from.to_string(), to.to_string()))
                })
                .collect();
            
            state.definition.connections = old_connections;
            
            Ok(state)
        }
    );
    
    // 创建测试状态
    let test_state = WorkflowState {
        id: "test-workflow".to_string(),
        version: Version::new(1, 0, 0),
        definition: WorkflowDefinition {
            name: "Test Workflow".to_string(),
            tasks: vec![
                TaskDefinition {
                    id: "task1".to_string(),
                    name: "Task 1".to_string(),
                    task_type: "action".to_string(),
                    config: HashMap::new(),
                },
                TaskDefinition {
                    id: "task2".to_string(),
                    name: "Task 2".to_string(),
                    task_type: "action".to_string(),
                    config: HashMap::new(),
                },
            ],
            connections: vec![
                ("task1".to_string(), "task2".to_string()),
            ],
        },
    };
    
    // 测试升级
    match evolution_algebra.upgrade(test_state.clone(), &Version::new(2, 0, 0)) {
        Ok(upgraded_state) => {
            println!("Successfully upgraded to v2.0.0");
            println!("New connections: {:?}", upgraded_state.definition.connections);
            
            // 测试降级
            match evolution_algebra.downgrade(upgraded_state, &Version::new(1, 1, 0)) {
                Ok(downgraded_state) => {
                    println!("Successfully downgraded to v1.1.0");
                    println!("Reverted connections: {:?}", downgraded_state.definition.connections);
                },
                Err(e) => println!("Failed to downgrade: {}", e),
            }
        },
        Err(e) => println!("Failed to upgrade: {}", e),
    }
    
    // 测试兼容性
    let compatibility = evolution_algebra.is_compatible(&test_state, &Version::new(1, 1, 0));
    println!("Is v1.0.0 compatible with v1.1.0? {}", compatibility);
    
    // 获取兼容性报告
    let report = registry.get_compatibility_report(&test_state);
    println!("Current version: {}", report.current_version);
    println!("Compatible versions: {:?}", report.compatible_versions);
    println!("Upgradable versions: {:?}", report.upgradable_versions);
    println!("Downgradable versions: {:?}", report.downgradable_versions);
}
```

### 渐进式类型演化

渐进式类型演化允许在保持系统运行的同时，安全地变更数据模型和API接口。

```rust
// 渐进式类型演化实现
use std::any::{Any, TypeId};
use std::collections::{HashMap, HashSet};
use std::marker::PhantomData;
use std::sync::{Arc, RwLock};

// 类型演化追踪器
pub struct TypeEvolution {
    // 类型注册表：类型ID -> 类型信息
    type_registry: RwLock<HashMap<TypeId, TypeInfo>>,
    // 类型演化映射：(源类型ID, 目标类型ID) -> 转换函数
    type_converters: RwLock<HashMap<(TypeId, TypeId), Box<dyn TypeConverter>>>,
    // 类型版本映射：类型名称 -> 版本 -> 类型ID
    versioned_types: RwLock<HashMap<String, HashMap<Version, TypeId>>>,
}

// 类型信息
#[derive(Clone)]
struct TypeInfo {
    type_name: String,
    version: Version,
    fields: HashMap<String, FieldInfo>,
}

// 字段信息
#[derive(Clone)]
struct FieldInfo {
    field_name: String,
    field_type: String,
    optional: bool,
}

// 类型转换器特征
pub trait TypeConverter: Send + Sync {
    fn convert(&self, source: &dyn Any) -> Box<dyn Any>;
    fn source_type_id(&self) -> TypeId;
    fn target_type_id(&self) -> TypeId;
}

// 具体类型转换器
pub struct ConcreteTypeConverter<S: 'static, T: 'static> {
    converter: Box<dyn Fn(&S) -> T + Send + Sync>,
}

impl<S: 'static, T: 'static> ConcreteTypeConverter<S, T> {
    pub fn new<F>(converter: F) -> Self
    where
        F: Fn(&S) -> T + Send + Sync + 'static,
    {
        Self {
            converter: Box::new(converter),
        }
    }
}

impl<S: 'static, T: 'static> TypeConverter for ConcreteTypeConverter<S, T> {
    fn convert(&self, source: &dyn Any) -> Box<dyn Any> {
        if let Some(typed_source) = source.downcast_ref::<S>() {
            let result = (self.converter)(typed_source);
            Box::new(result)
        } else {
            panic!("Type mismatch in conversion");
        }
    }
    
    fn source_type_id(&self) -> TypeId {
        TypeId::of::<S>()
    }
    
    fn target_type_id(&self) -> TypeId {
        TypeId::of::<T>()
    }
}

// 类型注册特征
pub trait TypeRegistration {
    fn register_type<T: 'static>(&self, type_name: &str, version: Version) -> TypeRegistrationBuilder<T>;
    fn register_converter<S: 'static, T: 'static, F>(&self, converter: F)
    where
        F: Fn(&S) -> T + Send + Sync + 'static;
}

// 类型注册构建器
pub struct TypeRegistrationBuilder<'a, T: 'static> {
    evolution: &'a TypeEvolution,
    type_name: String,
    version: Version,
    fields: HashMap<String, FieldInfo>,
    _phantom: PhantomData<T>,
}

impl<'a, T: 'static> TypeRegistrationBuilder<'a, T> {
    fn new(evolution: &'a TypeEvolution, type_name: String, version: Version) -> Self {
        Self {
            evolution,
            type_name,
            version,
            fields: HashMap::new(),
            _phantom: PhantomData,
        }
    }
    
    // 添加字段
    pub fn field(mut self, field_name: &str, field_type: &str, optional: bool) -> Self {
        self.fields.insert(field_name.to_string(), FieldInfo {
            field_name: field_name.to_string(),
            field_type: field_type.to_string(),
            optional,
        });
        self
    }
    
    // 完成注册
    pub fn register(self) {
        let type_info = TypeInfo {
            type_name: self.type_name.clone(),
            version: self.version.clone(),
            fields: self.fields,
        };
        
        let type_id = TypeId::of::<T>();
        
        // 注册类型信息
        {
            let mut registry = self.evolution.type_registry.write().unwrap();
            registry.insert(type_id, type_info);
        }
        
        // 注册版本映射
        {
            let mut versioned = self.evolution.versioned_types.write().unwrap();
            let type_versions = versioned.entry(self.type_name).or_insert_with(HashMap::new);
            type_versions.insert(self.version, type_id);
        }
    }
}

impl TypeEvolution {
    pub fn new() -> Self {
        Self {
            type_registry: RwLock::new(HashMap::new()),
            type_converters: RwLock::new(HashMap::new()),
            versioned_types: RwLock::new(HashMap::new()),
        }
    }
    
    // 转换类型
    pub fn convert<S: 'static, T: 'static>(&self, source: &S) -> Option<T> {
        let source_id = TypeId::of::<S>();
        let target_id = TypeId::of::<T>();
        
        // 如果类型相同，尝试直接克隆
        if source_id == target_id {
            if let Some(cloned) = (source as &dyn Any).downcast_ref::<T>() {
                // 这里需要T实现Clone特征才能真正克隆
                // 简化处理：假设可以从引用创建值
                return Some(unsafe { std::ptr::read(cloned) });
            }
        }
        
        // 查找转换器
        let converters = self.type_converters.read().unwrap();
        
        if let Some(converter) = converters.get(&(source_id, target_id)) {
            let result = converter.convert(source as &dyn Any);
            
            if let Ok(typed_result) = result.downcast::<T>() {
                return Some(*typed_result);
            }
        }
        
        None
    }
    
    // 检查类型是否兼容
    pub fn is_compatible<S: 'static, T: 'static>(&self) -> bool {
        let source_id = TypeId::of::<S>();
        let target_id = TypeId::of::<T>();
        
        // 相同类型直接兼容
        if source_id == target_id {
            return true;
        }
        
        // 检查是否有直接转换器
        let converters = self.type_converters.read().unwrap();
        converters.contains_key(&(source_id, target_id))
    }
    
    // 获取类型信息
    pub fn get_type_info<T: 'static>(&self) -> Option<TypeInfo> {
        let type_id = TypeId::of::<T>();
        let registry = self.type_registry.read().unwrap();
        registry.get(&type_id).cloned()
    }
    
    // 获取类型版本
    pub fn get_type_version<T: 'static>(&self) -> Option<Version> {
        let type_info = self.get_type_info::<T>()?;
        Some(type_info.version)
    }
    
    // 获取类型名称的所有版本
    pub fn get_all_versions(&self, type_name: &str) -> Vec<Version> {
        let versioned = self.versioned_types.read().unwrap();
        
        if let Some(versions) = versioned.get(type_name) {
            versions.keys().cloned().collect()
        } else {
            Vec::new()
        }
    }
    
    // 检查字段兼容性
    pub fn check_field_compatibility<S: 'static, T: 'static>(&self) -> FieldCompatibilityReport {
        let source_info = self.get_type_info::<S>();
        let target_info = self.get_type_info::<T>();
        
        if source_info.is_none() || target_info.is_none() {
            return FieldCompatibilityReport {
                compatible: false,
                missing_fields: Vec::new(),
                type_mismatches: Vec::new(),
                new_fields: Vec::new(),
            };
        }
        
        let source_info = source_info.unwrap();
        let target_info = target_info.unwrap();
        
        let mut missing_fields = Vec::new();
        let mut type_mismatches = Vec::new();
        let mut new_fields = Vec::new();
        
        // 检查源类型中的每个字段
        for (field_name, source_field) in &source_info.fields {
            if let Some(target_field) = target_info.fields.get(field_name) {
                // 检查字段类型是否匹配
                if source_field.field_type != target_field.field_type {
                    type_mismatches.push(field_name.clone());
                }
            } else if !source_field.optional {
                // 目标类型缺少必需字段
                missing_fields.push(field_name.clone());
            }
        }
        
        // 检查目标类型中的新字段
        for (field_name, target_field) in &target_info.fields {
            if !source_info.fields.contains_key(field_name) && !target_field.optional {
                new_fields.push(field_name.clone());
            }
        }
        
        FieldCompatibilityReport {
            compatible: missing_fields.is_empty() && type_mismatches.is_empty(),
            missing_fields,
            type_mismatches,
            new_fields,
        }
    }
}

// 字段兼容性报告
#[derive(Debug)]
pub struct FieldCompatibilityReport {
    pub compatible: bool,
    pub missing_fields: Vec<String>,
    pub type_mismatches: Vec<String>,
    pub new_fields: Vec<String>,
}

impl TypeRegistration for TypeEvolution {
    fn register_type<T: 'static>(&self, type_name: &str, version: Version) -> TypeRegistrationBuilder<T> {
        TypeRegistrationBuilder::new(self, type_name.to_string(), version)
    }
    
    fn register_converter<S: 'static, T: 'static, F>(&self, converter: F)
    where
        F: Fn(&S) -> T + Send + Sync + 'static,
    {
        let converter_obj = ConcreteTypeConverter::new(converter);
        
        let source_id = TypeId::of::<S>();
        let target_id = TypeId::of::<T>();
        
        let mut converters = self.type_converters.write().unwrap();
        converters.insert((source_id, target_id), Box::new(converter_obj));
    }
}

// 类型演化策略
pub enum EvolutionStrategy {
    // 严格模式：要求完全兼容
    Strict,
    // 宽松模式：允许添加可选字段
    Lenient,
    // 兼容模式：使用转换器处理不兼容
    Compatible,
}

// 类型迁移管理器
pub struct TypeMigrationManager {
    evolution: Arc<TypeEvolution>,
    strategy: EvolutionStrategy,
}

impl TypeMigrationManager {
    pub fn new(evolution: Arc<TypeEvolution>, strategy: EvolutionStrategy) -> Self {
        Self {
            evolution,
            strategy,
        }
    }
    
    // 迁移对象
    pub fn migrate<S: 'static, T: 'static>(&self, source: &S) -> Result<T, MigrationError> {
        match self.strategy {
            EvolutionStrategy::Strict => {
                // 检查严格兼容性
                let report = self.evolution.check_field_compatibility::<S, T>();
                
                if !report.compatible {
                    return Err(MigrationError::IncompatibleTypes {
                        source_type: std::any::type_name::<S>().to_string(),
                        target_type: std::any::type_name::<T>().to_string(),
                        missing_fields: report.missing_fields,
                        type_mismatches: report.type_mismatches,
                    });
                }
            },
            EvolutionStrategy::Lenient => {
                // 宽松模式：只检查缺失的非可选字段
                let report = self.evolution.check_field_compatibility::<S, T>();
                
                if !report.missing_fields.is_empty() {
                    return Err(MigrationError::MissingRequiredFields {
                        fields: report.missing_fields,
                    });
                }
            },
            EvolutionStrategy::Compatible => {
                // 兼容模式：尝试使用转换器
                if !self.evolution.is_compatible::<S, T>() {
                    return Err(MigrationError::NoConverterAvailable {
                        source_type: std::any::type_name::<S>().to_string(),
                        target_type: std::any::type_name::<T>().to_string(),
                    });
                }
            }
        }
        
        // 执行转换
        if let Some(result) = self.evolution.convert::<S, T>(source) {
            Ok(result)
        } else {
            Err(MigrationError::ConversionFailed {
                source_type: std::any::type_name::<S>().to_string(),
                target_type: std::any::type_name::<T>().to_string(),
            })
        }
    }
    
    // 获取版本迁移路径
    pub fn get_migration_path(&self, source_type: &str, source_version: &Version, target_version: &Version) -> Option<Vec<Version>> {
        let versioned = self.evolution.versioned_types.read().unwrap();
        
        if let Some(versions) = versioned.get(source_type) {
            // 检查源版本和目标版本是否存在
            if !versions.contains_key(source_version) || !versions.contains_key(target_version) {
                return None;
            }
            
            // 获取所有版本并排序
            let mut all_versions: Vec<Version> = versions.keys().cloned().collect();
            all_versions.sort();
            
            // 找出源版本和目标版本之间的所有版本
            let source_idx = all_versions.iter().position(|v| v == source_version)?;
            let target_idx = all_versions.iter().position(|v| v == target_version)?;
            
            if source_idx == target_idx {
                return Some(Vec::new());
            }
            
            if source_idx < target_idx {
                // 升级路径
                Some(all_versions[source_idx+1..=target_idx].to_vec())
            } else {
                // 降级路径
                let mut path: Vec<_> = all_versions[target_idx..source_idx].to_vec();
                path.reverse();
                Some(path)
            }
        } else {
            None
        }
    }
    
    // 检查类型演化
    pub fn check_evolution<T: 'static>(&self, type_name: &str) -> TypeEvolutionReport {
        let current_version = self.evolution.get_type_version::<T>();
        let all_versions = self.evolution.get_all_versions(type_name);
        
        if current_version.is_none() || all_versions.is_empty() {
            return TypeEvolutionReport {
                type_name: type_name.to_string(),
                current_version: None,
                all_versions: Vec::new(),
                compatible_versions: Vec::new(),
                incompatible_versions: Vec::new(),
            };
        }
        
        let current_version = current_version.unwrap();
        let type_id = TypeId::of::<T>();
        
        let mut compatible_versions = Vec::new();
        let mut incompatible_versions = Vec::new();
        
        // 获取所有版本的类型ID
        let versioned = self.evolution.versioned_types.read().unwrap();
        let versions = versioned.get(type_name).unwrap();
        
        // 检查每个版本的兼容性
        let converters = self.evolution.type_converters.read().unwrap();
        
        for version in &all_versions {
            if *version == current_version {
                compatible_versions.push(version.clone());
                continue;
            }
            
            if let Some(&other_type_id) = versions.get(version) {
                if converters.contains_key(&(type_id, other_type_id)) {
                    compatible_versions.push(version.clone());
                } else {
                    incompatible_versions.push(version.clone());
                }
            }
        }
        
        TypeEvolutionReport {
            type_name: type_name.to_string(),
            current_version: Some(current_version),
            all_versions,
            compatible_versions,
            incompatible_versions,
        }
    }
}

// 类型演化报告
#[derive(Debug)]
pub struct TypeEvolutionReport {
    pub type_name: String,
    pub current_version: Option<Version>,
    pub all_versions: Vec<Version>,
    pub compatible_versions: Vec<Version>,
    pub incompatible_versions: Vec<Version>,
}

// 迁移错误
#[derive(Debug)]
pub enum MigrationError {
    IncompatibleTypes {
        source_type: String,
        target_type: String,
        missing_fields: Vec<String>,
        type_mismatches: Vec<String>,
    },
    MissingRequiredFields {
        fields: Vec<String>,
    },
    NoConverterAvailable {
        source_type: String,
        target_type: String,
    },
    ConversionFailed {
        source_type: String,
        target_type: String,
    },
}

impl Display for MigrationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MigrationError::IncompatibleTypes { source_type, target_type, missing_fields, type_mismatches } => {
                write!(f, "Incompatible types: {} -> {}\n", source_type, target_type)?;
                if !missing_fields.is_empty() {
                    write!(f, "Missing fields: {:?}\n", missing_fields)?;
                }
                if !type_mismatches.is_empty() {
                    write!(f, "Type mismatches: {:?}", type_mismatches)?;
                }
                Ok(())
            },
            MigrationError::MissingRequiredFields { fields } => {
                write!(f, "Missing required fields: {:?}", fields)
            },
            MigrationError::NoConverterAvailable { source_type, target_type } => {
                write!(f, "No converter available from {} to {}", source_type, target_type)
            },
            MigrationError::ConversionFailed { source_type, target_type } => {
                write!(f, "Conversion failed from {} to {}", source_type, target_type)
            },
        }
    }
}

impl std::error::Error for MigrationError {}

// 渐进式类型演化使用示例
fn type_evolution_example() {
    // 定义数据模型 v1.0.0
    #[derive(Clone, Debug)]
    struct UserV1 {
        id: String,
        name: String,
        email: String,
    }
    
    // 定义数据模型 v1.1.0
    #[derive(Clone, Debug)]
    struct UserV2 {
        id: String,
        name: String,
        email: String,
        age: Option<u32>,
    }
    
    // 定义数据模型 v2.0.0
    #[derive(Clone, Debug)]
    struct UserV3 {
        id: String,
        name: String,
        email: String,
        age: Option<u32>,
        address: Option<String>,
        preferences: HashMap<String, String>,
    }
    
    // 创建类型演化系统
    let evolution = Arc::new(TypeEvolution::new());
    
    // 注册类型
    evolution.register_type::<UserV1>("User", Version::new(1, 0, 0))
        .field("id", "String", false)
        .field("name", "String", false)
        .field("email", "String", false)
        .register();
        
    evolution.register_type::<UserV2>("User", Version::new(1, 1, 0))
        .field("id", "String", false)
        .field("name", "String", false)
        .field("email", "String", false)
        .field("age", "Option<u32>", true)
        .register();
        
    evolution.register_type::<UserV3>("User", Version::new(2, 0, 0))
        .field("id", "String", false)
        .field("name", "String", false)
        .field("email", "String", false)
        .field("age", "Option<u32>", true)
        .field("address", "Option<String>", true)
        .field("preferences", "HashMap<String, String>", false)
        .register();
    
    // 注册转换器
    evolution.register_converter(|user: &UserV1| -> UserV2 {
        UserV2 {
            id: user.id.clone(),
            name: user.name.clone(),
            email: user.email.clone(),
            age: None,
        }
    });
    
    evolution.register_converter(|user: &UserV2| -> UserV3 {
        UserV3 {
            id: user.id.clone(),
            name: user.name.clone(),
            email: user.email.clone(),
            age: user.age,
            address: None,
            preferences: HashMap::new(),
        }
    });
    
    evolution.register_converter(|user: &UserV1| -> UserV3 {
        UserV3 {
            id: user.id.clone(),
            name: user.name.clone(),
            email: user.email.clone(),
            age: None,
            address: None,
            preferences: HashMap::new(),
        }
    });
    
    // 创建迁移管理器
    let migration_manager = TypeMigrationManager::new(evolution.clone(), EvolutionStrategy::Compatible);
    
    // 测试数据
    let user_v1 = UserV1 {
        id: "user1".to_string(),
        name: "John Doe".to_string(),
        email: "john@example.com".to_string(),
    };
    
    // 迁移到V2
    match migration_manager.migrate::<UserV1, UserV2>(&user_v1) {
        Ok(user_v2) => {
            println!("Successfully migrated to UserV2: {:?}", user_v2);
            
            // 迁移到V3
            match migration_manager.migrate::<UserV2, UserV3>(&user_v2) {
                Ok(user_v3) => {
                    println!("Successfully migrated to UserV3: {:?}", user_v3);
                },
                Err(e) => println!("Failed to migrate to UserV3: {}", e),
            }
        },
        Err(e) => println!("Failed to migrate to UserV2: {}", e),
    }
    
    // 直接迁移从V1到V3
    match migration_manager.migrate::<UserV1, UserV3>(&user_v1) {
        Ok(user_v3) => {
            println!("Successfully migrated directly to UserV3: {:?}", user_v3);
        },
        Err(e) => println!("Failed to migrate directly to UserV3: {}", e),
    }
    
    // 检查类型演化
    let evolution_report = migration_manager.check_evolution::<UserV1>("User");
    println!("Type evolution report for UserV1:");
    println!("Current version: {:?}", evolution_report.current_version);
    println!("All versions: {:?}", evolution_report.all_versions);
    println!("Compatible versions: {:?}", evolution_report.compatible_versions);
    println!("Incompatible versions: {:?}", evolution_report.incompatible_versions);
}
```

### 共变分离原则

共变分离原则是设计能够安全演化的接口和数据结构的关键，它允许子类型在不破坏兼容性的情况下扩展功能。

```rust
// 共变分离原则实现
use std::marker::PhantomData;
use std::sync::Arc;

// 版本标记特征
pub trait VersionMarker {
    type PreviousVersion: VersionMarker;
    const VERSION: Version;
}

// 最老版本标记（无前任版本）
pub struct V1_0_0;
impl VersionMarker for V1_0_0 {
    type PreviousVersion = V1_0_0; // 自引用表示没有前任
    const VERSION: Version = Version::new(1, 0, 0);
}

// 版本1.1.0
pub struct V1_1_0;
impl VersionMarker for V1_1_0 {
    type PreviousVersion = V1_0_0;
    const VERSION: Version = Version::new(1, 1, 0);
}

// 版本2.0.0
pub struct V2_0_0;
impl VersionMarker for V2_0_0 {
    type PreviousVersion = V1_1_0;
    const VERSION: Version = Version::new(2, 0, 0);
}

// 带版本的接口
pub trait VersionedInterface<V: VersionMarker> {
    // 接口方法
}

// 带版本的数据结构
pub struct VersionedData<T, V: VersionMarker> {
    data: T,
    _marker: PhantomData<V>,
}

impl<T, V: VersionMarker> VersionedData<T, V> {
    pub fn new(data: T) -> Self {
        Self {
            data,
            _marker: PhantomData,
        }
    }
    
    pub fn get(&self) -> &T {
        &self.data
    }
    
    pub fn get_mut(&mut self) -> &mut T {
        &mut self.data
    }
    
    pub fn into_inner(self) -> T {
        self.data
    }
    
    // 向下转换到之前的版本
    pub fn downgrade<F>(self, converter: F) -> VersionedData<F::Output, V::PreviousVersion>
    where
        F: FnOnce(T) -> F::Output,
    {
        VersionedData::new(converter(self.data))
    }
}

// 接口升级包装器
pub struct UpgradedInterface<I, V: VersionMarker, NewV: VersionMarker> {
    inner: I,
    _marker: PhantomData<(V, NewV)>,
}

impl<I, V: VersionMarker, NewV: VersionMarker> UpgradedInterface<I, V, NewV> {
    pub fn new(inner: I) -> Self {
        Self {
            inner,
            _marker: PhantomData,
        }
    }
    
    pub fn inner(&self) -> &I {
        &self.inner
    }
    
    pub fn inner_mut(&mut self) -> &mut I {
        &mut self.inner
    }
    
    pub fn into_inner(self) -> I {
        self.inner
    }
}

// 协变数据封装
// 协变：如果A是B的子类型，那么F<A>是F<B>的子类型
pub struct Covariant<T> {
    data: T,
}

impl<T> Covariant<T> {
    pub fn new(data: T) -> Self {
        Self { data }
    }
    
    pub fn get(&self) -> &T {
        &self.data
    }
    
    pub fn map<U, F: FnOnce(T) -> U>(self, f: F) -> Covariant<U> {
        Covariant::new(f(self.data))
    }
}

// 逆变数据封装
// 逆变：如果A是B的子类型，那么F<B>是F<A>的子类型
pub struct Contravariant<T> {
    processor: Box<dyn Fn(T)>,
}

impl<T> Contravariant<T> {
    pub fn new<F: Fn(T) + 'static>(processor: F) -> Self {
        Self {
            processor: Box::new(processor),
        }
    }
    
    pub fn process(&self, value: T) {
        (self.processor)(value);
    }
    
    // 逆变转换
    pub fn contramap<U, F: Fn(U) -> T + 'static>(self, f: F) -> Contravariant<U> {
        let original_processor = self.processor;
        Contravariant::new(move |u| {
            let t = f(u);
            (original_processor)(t);
        })
    }
}

// 不变数据封装
// 不变：A和B之间的子类型关系与F<A>和F<B>之间无关
pub struct Invariant<T> {
    data: T,
}

impl<T> Invariant<T> {
    pub fn new(data: T) -> Self {
        Self { data }
    }
    
    pub fn get(&self) -> &T {
        &self.data
    }
    
    // 不变转换
    pub fn bimap<U, F: FnOnce(T) -> U, G: FnOnce(U) -> T>(self, f: F, _g: G) -> Invariant<U> {
        Invariant::new(f(self.data))
    }
}

// 版本化API示例
// V1 API
pub trait UserServiceV1 {
    fn get_user(&self, id: &str) -> Result<User, ApiError>;
    fn create_user(&self, name: &str, email: &str) -> Result<User, ApiError>;
}

// V2 API (扩展V1)
pub trait UserServiceV2: UserServiceV1 {
    fn get_user_by_email(&self, email: &str) -> Result<User, ApiError>;
    fn update_user(&self, id: &str, name: Option<&str>, email: Option<&str>) -> Result<User, ApiError>;
}

// V3 API (扩展V2)
pub trait UserServiceV3: UserServiceV2 {
    fn delete_user(&self, id: &str) -> Result<(), ApiError>;
    fn list_users(&self, page: usize, size: usize) -> Result<Vec<User>, ApiError>;
}

// 共变演化包装器
pub struct ApiWrapper<T, V: VersionMarker> {
    inner: T,
    _marker: PhantomData<V>,
}

impl<T, V: VersionMarker> ApiWrapper<T, V> {
    pub fn new(inner: T) -> Self {
        Self {
            inner,
            _marker: PhantomData,
        }
    }
    
    pub fn inner(&self) -> &T {
        &self.inner
    }
    
    pub fn into_inner(self) -> T {
        self.inner
    }
    
    // 升级API版本（共变升级）
    pub fn upgrade<NewV: VersionMarker, U, F: FnOnce(T) -> U>(self, f: F) -> ApiWrapper<U, NewV> {
        ApiWrapper::new(f(self.inner))
    }
}

// 支持向后兼容的实现示例
struct UserServiceImplV3 {
    // 实现细节...
}

impl UserServiceV1 for UserServiceImplV3 {
    fn get_user(&self, id: &str) -> Result<User, ApiError> {
        // V3实现get_user
        println!("V3 impl getting user by id: {}", id);
        Ok(User {
            id: id.to_string(),
            name: "Test User".to_string(),
            email: "test@example.com".to_string(),
            created_at: chrono::Utc::now(),
        })
    }
    
    fn create_user(&self, name: &str, email: &str) -> Result<User, ApiError> {
        // V3实现create_user
        println!("V3 impl creating user: {}, {}", name, email);
        Ok(User {
            id: "new-user-id".to_string(),
            name: name.to_string(),
            email: email.to_string(),
            created_at: chrono::Utc::now(),
        })
    }
}

impl UserServiceV2 for UserServiceImplV3 {
    fn get_user_by_email(&self, email: &str) -> Result<User, ApiError> {
        // V3实现get_user_by_email
        println!("V3 impl getting user by email: {}", email);
        Ok(User {
            id: "user-by-email".to_string(),
            name: "Email User".to_string(),
            email: email.to_string(),
            created_at: chrono::Utc::now(),
        })
    }
    
    fn update_user(&self, id: &str, name: Option<&str>, email: Option<&str>) -> Result<User, ApiError> {
        // V3实现update_user
        println!("V3 impl updating user: {}, {:?}, {:?}", id, name, email);
        Ok(User {
            id: id.to_string(),
            name: name.unwrap_or("Default Name").to_string(),
            email: email.unwrap_or("default@example.com").to_string(),
            created_at: chrono::Utc::now(),
        })
    }
}

impl UserServiceV3 for UserServiceImplV3 {
    fn delete_user(&self, id: &str) -> Result<(), ApiError> {
        // V3实现delete_user
        println!("V3 impl deleting user: {}", id);
        Ok(())
    }
    
    fn list_users(&self, page: usize, size: usize) -> Result<Vec<User>, ApiError> {
        // V3实现list_users
        println!("V3 impl listing users: page={}, size={}", page, size);
        Ok(vec![
            User {
                id: "user1".to_string(),
                name: "User 1".to_string(),
                email: "user1@example.com".to_string(),
                created_at: chrono::Utc::now(),
            },
            User {
                id: "user2".to_string(),
                name: "User 2".to_string(),
                email: "user2@example.com".to_string(),
                created_at: chrono::Utc::now(),
            },
        ])
    }
}

// 版本化数据模型示例
// V1 数据模型
#[derive(Debug, Clone)]
pub struct UserDataV1 {
    pub id: String,
    pub name: String,
    pub email: String,
}

// V2 数据模型
#[derive(Debug, Clone)]
pub struct UserDataV2 {
    pub id: String,
    pub name: String,
    pub email: String,
    pub created_at: chrono::DateTime<chrono::Utc>,
}

// V3 数据模型
#[derive(Debug, Clone)]
pub struct UserDataV3 {
    pub id: String,
    pub name: String,
    pub email: String,
    pub created_at: chrono::DateTime<chrono::Utc>,
    pub updated_at: Option<chrono::DateTime<chrono::Utc>>,
    pub settings: HashMap<String, String>,
}

// 数据转换函数
fn convert_user_v1_to_v2(v1: UserDataV1) -> UserDataV2 {
    UserDataV2 {
        id: v1.id,
        name: v1.name,
        email: v1.email,
        created_at: chrono::Utc::now(),
    }
}

fn convert_user_v2_to_v3(v2: UserDataV2) -> UserDataV3 {
    UserDataV3 {
        id: v2.id,
        name: v2.name,
        email: v2.email,
        created_at: v2.created_at,
        updated_at: None,
        settings: HashMap::new(),
    }
}

fn convert_user_v3_to_v2(v3: UserDataV3) -> UserDataV2 {
    UserDataV2 {
        id: v3.id,
        name: v3.name,
        email: v3.email,
        created_at: v3.created_at,
    }
}

fn convert_user_v2_to_v1(v2: UserDataV2) -> UserDataV1 {
    UserDataV1 {
        id: v2.id,
        name: v2.name,
        email: v2.email,
    }
}

// 共变接口示例
// 请求处理器 - 演示共变接口设计
trait RequestHandler<Req, Resp> {
    fn handle(&self, request: Req) -> Resp;
}

// V1 请求/响应
struct RequestV1 {
    id: String,
    data: String,
}

struct ResponseV1 {
    success: bool,
    message: String,
}

// V2 请求/响应（扩展V1）
struct RequestV2 {
    id: String,
    data: String,
    metadata: HashMap<String, String>,
}

struct ResponseV2 {
    success: bool,
    message: String,
    data: Option<String>,
}

// 共变处理器
struct CovariantHandler<H, ReqIn, ReqOut, RespIn, RespOut> {
    handler: H,
    request_mapper: Box<dyn Fn(ReqIn) -> ReqOut>,
    response_mapper: Box<dyn Fn(RespIn) -> RespOut>,
}

impl<H, ReqIn, ReqOut, RespIn, RespOut> CovariantHandler<H, ReqIn, ReqOut, RespIn, RespOut>
where
    H: RequestHandler<ReqOut, RespIn>,
{
    fn new<F, G>(handler: H, request_mapper: F, response_mapper: G) -> Self
    where
        F: Fn(ReqIn) -> ReqOut + 'static,
        G: Fn(RespIn) -> RespOut + 'static,
    {
        Self {
            handler,
            request_mapper: Box::new(request_mapper),
            response_mapper: Box::new(response_mapper),
        }
    }
}

impl<H, ReqIn, ReqOut, RespIn, RespOut> RequestHandler<ReqIn, RespOut> 
    for CovariantHandler<H, ReqIn, ReqOut, RespIn, RespOut>
where
    H: RequestHandler<ReqOut, RespIn>,
{
    fn handle(&self, request: ReqIn) -> RespOut {
        let mapped_request = (self.request_mapper)(request);
        let response = self.handler.handle(mapped_request);
        (self.response_mapper)(response)
    }
}

// V1 处理器实现
struct UserHandlerV1;

impl RequestHandler<RequestV1, ResponseV1> for UserHandlerV1 {
    fn handle(&self, request: RequestV1) -> ResponseV1 {
        println!("Handling V1 request: {}", request.id);
        ResponseV1 {
            success: true,
            message: format!("Processed request {}", request.id),
        }
    }
}

// 共变分离原则使用示例
fn covariant_separation_example() {
    // 创建V3版本的服务实现
    let service_v3 = UserServiceImplV3 {};
    
    // 可以用作V1服务
    let service_v1: &dyn UserServiceV1 = &service_v3;
    let user = service_v1.get_user("user1").unwrap();
    println!("Got user with V1 interface: {}", user.name);
    
    // 可以用作V2服务
    let service_v2: &dyn UserServiceV2 = &service_v3;
    let user = service_v2.get_user_by_email("user@example.com").unwrap();
    println!("Got user with V2 interface: {}", user.name);
    
    // 使用完整V3服务
    let user_list = service_v3.list_users(0, 10).unwrap();
    println!("Listed {} users with V3 interface", user_list.len());
    
    // 使用版本化数据
    let user_data_v1 = UserDataV1 {
        id: "user1".to_string(),
        name: "John Doe".to_string(),
        email: "john@example.com".to_string(),
    };
    
    // 创建版本化数据容器
    let versioned_v1 = VersionedData::<_, V1_0_0>::new(user_data_v1.clone());
    
    // 升级到V2
    let user_data_v2 = convert_user_v1_to_v2(user_data_v1);
    let versioned_v2 = VersionedData::<_, V1_1_0>::new(user_data_v2.clone());
    
    // 升级到V3
    let user_data_v3 = convert_user_v2_to_v3(user_data_v2);
    let versioned_v3 = VersionedData::<_, V2_0_0>::new(user_data_v3.clone());
    
    // 降级回V2
    let downgraded_v2 = versioned_v3.downgrade(convert_user_v3_to_v2);
    
    // 降级回V1
    let downgraded_v1 = downgraded_v2.downgrade(convert_user_v2_to_v1);
    
    println!("Successfully downgraded from V3 to V1: {:?}", downgraded_v1.get());
    
    // 共变包装器示例
    let v1_handler = UserHandlerV1 {};
    
    // 创建一个V1->V2的请求/响应映射器
    let request_mapper = |req: RequestV2| RequestV1 {
        id: req.id,
        data: req.data,
    };
    
    let response_mapper = |resp: ResponseV1| ResponseV2 {
        success: resp.success,
        message: resp.message,
        data: None,
    };
    
    let v2_handler = CovariantHandler::new(v1_handler, request_mapper, response_mapper);
    
    // 使用V2接口调用V1处理器
    let v2_request = RequestV2 {
        id: "req-001".to_string(),
        data: "test-data".to_string(),
        metadata: HashMap::new(),
    };
    
    let v2_response = v2_handler.handle(v2_request);
    println!("V2 response from V1 handler: success={}, message={}", 
             v2_response.success, v2_response.message);
}

// 实际使用中的API版本控制示例
enum ApiVersionStrategy {
    UrlPath,     // 路径中包含版本: /v1/users
    QueryParam,  // 查询参数指定版本: /users?version=1
    Header,      // HTTP头指定版本: X-API-Version: 1
    AcceptHeader, // Accept头指定版本: Accept: application/vnd.api+json;version=1
}

// API版本管理器
struct ApiVersionManager {
    strategy: ApiVersionStrategy,
    available_versions: HashMap<Version, Arc<dyn Any + Send + Sync>>,
    default_version: Version,
}

impl ApiVersionManager {
    fn new(strategy: ApiVersionStrategy, default_version: Version) -> Self {
        Self {
            strategy,
            available_versions: HashMap::new(),
            default_version,
        }
    }
    
    fn register_version<T: 'static + Send + Sync>(&mut self, version: Version, handler: T) {
        self.available_versions.insert(version, Arc::new(handler));
    }
    
    fn get_version_from_request(&self, request: &HttpRequest) -> Version {
        match self.strategy {
            ApiVersionStrategy::UrlPath => {
                // 从URL路径中提取版本
                let path = request.path();
                if let Some(version_str) = path.split('/').nth(1) {
                    if version_str.starts_with('v') {
                        if let Ok(version) = Version::parse(&version_str[1..]) {
                            return version;
                        }
                    }
                }
                self.default_version.clone()
            },
            ApiVersionStrategy::QueryParam => {
                // 从查询参数中提取版本
                if let Some(version_str) = request.query_param("version") {
                    if let Ok(version) = Version::parse(version_str) {
                        return version;
                    }
                }
                self.default_version.clone()
            },
            ApiVersionStrategy::Header => {
                // 从HTTP头中提取版本
                if let Some(version_str) = request.header("X-API-Version") {
                    if let Ok(version) = Version::parse(version_str) {
                        return version;
                    }
                }
                self.default_version.clone()
            },
            ApiVersionStrategy::AcceptHeader => {
                // 从Accept头中提取版本
                if let Some(accept) = request.header("Accept") {
                    // 解析如: application/vnd.api+json;version=1
                    if accept.contains(";version=") {
                        if let Some(version_part) = accept.split(';').find(|p| p.trim().starts_with("version=")) {
                            let version_str = version_part.trim()[8..].trim();
                            if let Ok(version) = Version::parse(version_str) {
                                return version;
                            }
                        }
                    }
                }
                self.default_version.clone()
            },
        }
    }
    
    fn handle_request<T: 'static>(&self, request: &HttpRequest) -> Option<Result<HttpResponse, ApiError>> {
        let version = self.get_version_from_request(request);
        
        // 找到对应版本的处理器
        if let Some(handler_any) = self.available_versions.get(&version) {
            if let Some(handler) = handler_any.downcast_ref::<T>() {
                // 处理请求
                return Some(self.dispatch_to_handler(handler, request));
            }
        }
        
        // 找不到对应版本的处理器，尝试使用默认版本
        if version != self.default_version {
            if let Some(handler_any) = self.available_versions.get(&self.default_version) {
                if let Some(handler) = handler_any.downcast_ref::<T>() {
                    // 处理请求
                    return Some(self.dispatch_to_handler(handler, request));
                }
            }
        }
        
        None
    }
    
    fn dispatch_to_handler<T>(&self, handler: &T, request: &HttpRequest) -> Result<HttpResponse, ApiError> {
        // 实际分发逻辑将取决于处理器类型
        // 这里简化为示例
        Ok(HttpResponse::new(200, "OK".to_string()))
    }
}

// 简化的HTTP请求/响应模型
struct HttpRequest {
    method: String,
    path: String,
    query_params: HashMap<String, String>,
    headers: HashMap<String, String>,
    body: Option<String>,
}

impl HttpRequest {
    fn path(&self) -> &str {
        &self.path
    }
    
    fn query_param(&self, name: &str) -> Option<&str> {
        self.query_params.get(name).map(|s| s.as_str())
    }
    
    fn header(&self, name: &str) -> Option<&str> {
        self.headers.get(name).map(|s| s.as_str())
    }
}

struct HttpResponse {
    status: u16,
    body: String,
    headers: HashMap<String, String>,
}

impl HttpResponse {
    fn new(status: u16, body: String) -> Self {
        Self {
            status,
            body,
            headers: HashMap::new(),
        }
    }
}
```

### 无停机演化路径

无停机演化路径允许系统在不中断服务的情况下完成升级，这对于高可用系统至关重要。

```rust
// 无停机演化路径实现
use std::collections::{HashMap, HashSet, VecDeque};
use std::sync::{Arc, Mutex, RwLock};
use std::time::{Duration, Instant};

// 部署单元
#[derive(Clone, Debug)]
pub struct DeploymentUnit {
    id: String,
    version: Version,
    components: Vec<ComponentInfo>,
    dependencies: HashMap<String, VersionReq>,
    state: DeploymentState,
    health: HealthStatus,
    last_updated: chrono::DateTime<chrono::Utc>,
    metadata: HashMap<String, String>,
}

// 组件信息
#[derive(Clone, Debug)]
pub struct ComponentInfo {
    name: String,
    version: Version,
    required: bool,
    health_check: Option<String>,
}

// 部署状态
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum DeploymentState {
    Staged,      // 已准备但未激活
    Active,      // 当前活动
    Deprecated,  // 已弃用但仍可用
    Retired,     // 已退役，不应使用
}

// 健康状态
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum HealthStatus {
    Healthy,    // 完全健康
    Degraded,   // 功能降级
    Unhealthy,  // 不健康
    Unknown,    // 未知状态
}

// 部署策略
#[derive(Clone, Debug)]
pub enum DeploymentStrategy {
    BlueGreen {
        verify_timeout: Duration,
        rollback_threshold: f64,
    },
    Canary {
        initial_percentage: f64,
        increment_step: f64,
        verification_period: Duration,
        max_verification_rounds: usize,
    },
    Rolling {
        batch_size: usize,
        batch_delay: Duration,
        verify_per_batch: bool,
    },
    Shadowing {
        shadow_duration: Duration,
        comparison_strategy: ShadowComparisonStrategy,
    },
}

// 影子流量比较策略
#[derive(Clone, Debug)]
pub enum ShadowComparisonStrategy {
    ResponseMatch { required_match_percentage: f64 },
    PerformanceOnly { max_latency_increase_percentage: f64 },
    ErrorRateOnly { max_error_rate_increase: f64 },
    ComprehensiveComparison {
        response_match_weight: f64,
        performance_weight: f64,
        error_rate_weight: f64,
        min_total_score: f64,
    },
}

// 部署计划
#[derive(Clone, Debug)]
pub struct DeploymentPlan {
    id: String,
    source_version: Version,
    target_version: Version,
    strategy: DeploymentStrategy,
    stages: Vec<DeploymentStage>,
    verification_steps: Vec<VerificationStep>,
    rollback_steps: Vec<RollbackStep>,
    started_at: Option<chrono::DateTime<chrono::Utc>>,
    completed_at: Option<chrono::DateTime<chrono::Utc>>,
    status: DeploymentPlanStatus,
    current_stage_index: usize,
}

// 部署阶段
#[derive(Clone, Debug)]
pub struct DeploymentStage {
    name: String,
    units: Vec<DeploymentUnit>,
    dependencies: Vec<String>, // 依赖的前置阶段
    status: StageStatus,
    started_at: Option<chrono::DateTime<chrono::Utc>>,
    completed_at: Option<chrono::DateTime<chrono::Utc>>,
    retries: usize,
    max_retries: usize,
}

// 验证步骤
#[derive(Clone, Debug)]
pub struct VerificationStep {
    name: String,
    verification_type: VerificationType,
    timeout: Duration,
    status: VerificationStatus,
    result: Option<VerificationResult>,
}

// 验证类型
#[derive(Clone, Debug)]
pub enum VerificationType {
    HealthCheck { endpoint: String, expected_status: u16 },
    FunctionalTest { test_suite: String },
    MetricThreshold { metric: String, operator: String, threshold: f64 },
    ManualApproval { approvers: Vec<String> },
}

// 回滚步骤
#[derive(Clone, Debug)]
pub struct RollbackStep {
    name: String,
    units: Vec<String>, // 要回滚的部署单元ID
    status: RollbackStatus,
    triggered_by: Option<String>, // 触发回滚的验证步骤
}

// 阶段状态
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum StageStatus {
    Pending,    // 等待执行
    Running,    // 正在执行
    Succeeded,  // 成功完成
    Failed,     // 失败
    Skipped,    // 已跳过
}

// 验证状态
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum VerificationStatus {
    Pending,    // 等待执行
    Running,    // 正在执行
    Succeeded,  // 成功完成
    Failed,     // 失败
}

// 验证结果
#[derive(Clone, Debug)]
pub struct VerificationResult {
    success: bool,
    message: String,
    metrics: HashMap<String, f64>,
    timestamp: chrono::DateTime<chrono::Utc>,
}

// 回滚状态
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum RollbackStatus {
    NotNeeded,  // 不需要回滚
    Pending,    // 等待回滚
    Running,    // 正在回滚
    Completed,  // 回滚完成
    Failed,     // 回滚失败
}

// 部署计划状态
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum DeploymentPlanStatus {
    Planned,    // 已计划
    Running,    // 正在执行
    Succeeded,  // 成功完成
    PartiallySucceeded, // 部分成功
    Failed,     // 完全失败
    Canceled,   // 已取消
    RollingBack, // 正在回滚
    RolledBack, // 已回滚
}

// 无停机部署管理器
pub struct ZeroDowntimeDeploymentManager {
    active_deployments: RwLock<HashMap<String, DeploymentUnit>>,
    staged_deployments: RwLock<HashMap<String, DeploymentUnit>>,
    deployment_history: RwLock<Vec<DeploymentUnit>>,
    current_plans: RwLock<HashMap<String, DeploymentPlan>>,
    plan_history: RwLock<Vec<DeploymentPlan>>,
    version_registry: Arc<VersionCompatibilityRegistry>,
    health_checks: HashMap<String, Box<dyn HealthCheck + Send + Sync>>,
    metrics_collector: Arc<dyn MetricsCollector + Send + Sync>,
    notification_manager: Arc<dyn NotificationManager + Send + Sync>,
}

// 健康检查特征
pub trait HealthCheck {
    fn check_health(&self, component: &ComponentInfo) -> HealthStatus;
    fn get_details(&self, component: &ComponentInfo) -> HashMap<String, String>;
}

// 指标收集器特征
pub trait MetricsCollector {
    fn collect_deployment_metrics(&self, unit: &DeploymentUnit) -> HashMap<String, f64>;
    fn collect_verification_metrics(&self, step: &VerificationStep) -> HashMap<String, f64>;
    fn record_deployment_event(&self, event_type: &str, unit: &DeploymentUnit, details: HashMap<String, String>);
}

// 通知管理器特征
pub trait NotificationManager {
    fn send_deployment_notification(&self, event_type: &str, plan: &DeploymentPlan);
    fn send_verification_notification(&self, step: &VerificationStep, result: &VerificationResult);
    fn send_rollback_notification(&self, step: &RollbackStep, success: bool, message: &str);
}

// 版本兼容性注册表
pub struct VersionCompatibilityRegistry {
    compatibility_matrix: RwLock<HashMap<(Version, Version), CompatibilityLevel>>,
    version_metadata: RwLock<HashMap<Version, VersionMetadata>>,
    migration_paths: RwLock<HashMap<(Version, Version), Vec<Version>>>,
}

// 兼容性级别
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum CompatibilityLevel {
    Incompatible,      // 不兼容
    BackwardCompatible, // 向后兼容（新版本可以理解旧版本的数据）
    ForwardCompatible,  // 向前兼容（旧版本可以理解新版本的数据）
    FullyCompatible,    // 完全兼容（双向兼容）
}

// 版本元数据
#[derive(Clone, Debug)]
pub struct VersionMetadata {
    version: Version,
    release_date: chrono::DateTime<chrono::Utc>,
    end_of_support: Option<chrono::DateTime<chrono::Utc>>,
    breaking_changes: Vec<String>,
    features: Vec<String>,
    dependencies: HashMap<String, VersionReq>,
}

impl VersionCompatibilityRegistry {
    pub fn new() -> Self {
        Self {
            compatibility_matrix: RwLock::new(HashMap::new()),
            version_metadata: RwLock::new(HashMap::new()),
            migration_paths: RwLock::new(HashMap::new()),
        }
    }
    
    // 注册版本元数据
    pub fn register_version(&self, metadata: VersionMetadata) {
        let mut versions = self.version_metadata.write().unwrap();
        versions.insert(metadata.version.clone(), metadata);
    }
    
    // 设置版本兼容性
    pub fn set_compatibility(&self, from: &Version, to: &Version, level: CompatibilityLevel) {
        let mut matrix = self.compatibility_matrix.write().unwrap();
        matrix.insert((from.clone(), to.clone()), level);
        
        // 如果是完全兼容，也设置反向兼容性
        if level == CompatibilityLevel::FullyCompatible {
            matrix.insert((to.clone(), from.clone()), level);
        }
    }
    
    // 注册迁移路径
    pub fn register_migration_path(&self, from: &Version, to: &Version, path: Vec<Version>) {
        let mut paths = self.migration_paths.write().unwrap();
        paths.insert((from.clone(), to.clone()), path);
    }
    
    // 检查兼容性
    pub fn check_compatibility(&self, from: &Version, to: &Version) -> CompatibilityLevel {
        let matrix = self.compatibility_matrix.read().unwrap();
        
        // 直接查找兼容性
        if let Some(&level) = matrix.get(&(from.clone(), to.clone())) {
            return level;
        }
        
        // 如果版本相同，默认完全兼容
        if from == to {
            return CompatibilityLevel::FullyCompatible;
        }
        
        // 默认不兼容
        CompatibilityLevel::Incompatible
    }
    
    // 获取迁移路径
    pub fn get_migration_path(&self, from: &Version, to: &Version) -> Option<Vec<Version>> {
        let paths = self.migration_paths.read().unwrap();
        
        // 直接查找路径
        if let Some(path) = paths.get(&(from.clone(), to.clone())) {
            return Some(path.clone());
        }
        
        // 如果版本相同，返回空路径
        if from == to {
            return Some(Vec::new());
        }
        
        // 尝试寻找可能的路径
        self.find_migration_path(from, to)
    }
    
    // 寻找可能的迁移路径
    fn find_migration_path(&self, from: &Version, to: &Version) -> Option<Vec<Version>> {
        // 从已知的迁移路径中构建图并搜索路径
        let paths = self.migration_paths.read().unwrap();
        
        // 构建版本图
        let mut version_graph: HashMap<Version, Vec<Version>> = HashMap::new();
        
        for ((src, dst), _) in paths.iter() {
            version_graph.entry(src.clone())
                .or_insert_with(Vec::new)
                .push(dst.clone());
        }
        
        // 广度优先搜索寻找路径
        let mut queue = VecDeque::new();
        let mut visited = HashSet::new();
        let mut path_map = HashMap::new();
        
        queue.push_back(from.clone());
        visited.insert(from.clone());
        
        while let Some(current) = queue.pop_front() {
            // 找到目标版本
            if current == *to {
                // 从路径映射中重建完整路径
                let mut result = Vec::new();
                let mut current_version = current;
                
                while current_version != *from {
                    result.push(current_version.clone());
                    current_version = path_map.get(&current_version).unwrap().clone();
                }
                
                // 反转路径（从源到目标）
                result.reverse();
                return Some(result);
            }
            
            // 探索下一个版本
            if let Some(next_versions) = version_graph.get(&current) {
                for next_version in next_versions {
                    if !visited.contains(next_version) {
                        visited.insert(next_version.clone());
                        path_map.insert(next_version.clone(), current.clone());
                        queue.push_back(next_version.clone());
                    }
                }
            }
        }
        
        None // 没有找到路径
    }
    
    // 检查多个组件的兼容性
    pub fn check_components_compatibility(&self, components: &[ComponentInfo]) -> bool {
        // 检查每对组件之间的兼容性
        for i in 0..components.len() {
            for j in i+1..components.len() {
                let comp_a = &components[i];
                let comp_b = &components[j];
                
                // 检查兼容性级别
                let level = self.check_compatibility(&comp_a.version, &comp_b.version);
                
                // 如果任何一对组件不兼容，整体不兼容
                if level == CompatibilityLevel::Incompatible {
                    return false;
                }
            }
        }
        
        true
    }
}

impl ZeroDowntimeDeploymentManager {
    pub fn new(
        version_registry: Arc<VersionCompatibilityRegistry>,
        metrics_collector: Arc<dyn MetricsCollector + Send + Sync>,
        notification_manager: Arc<dyn NotificationManager + Send + Sync>,
    ) -> Self {
        Self {
            active_deployments: RwLock::new(HashMap::new()),
            staged_deployments: RwLock::new(HashMap::new()),
            deployment_history: RwLock::new(Vec::new()),
            current_plans: RwLock::new(HashMap::new()),
            plan_history: RwLock::new(Vec::new()),
            version_registry,
            health_checks: HashMap::new(),
            metrics_collector,
            notification_manager,
        }
    }
    
    // 注册健康检查
    pub fn register_health_check<H: HealthCheck + Send + Sync + 'static>(
        &mut self,
        component_type: String,
        health_check: H,
    ) {
        self.health_checks.insert(component_type, Box::new(health_check));
    }
    
    // 创建部署计划
    pub fn create_deployment_plan(
        &self,
        source_version: Version,
        target_version: Version,
        strategy: DeploymentStrategy,
        units: Vec<DeploymentUnit>,
    ) -> Result<DeploymentPlan, DeploymentError> {
        // 检查版本兼容性
        let compatibility = self.version_registry.check_compatibility(&source_version, &target_version);
        if compatibility == CompatibilityLevel::Incompatible {
            return Err(DeploymentError::IncompatibleVersions {
                from: source_version.to_string(),
                to: target_version.to_string(),
            });
        }
        
        // 生成部署ID
        let plan_id = format!("deploy-{}-{}-{}", 
            source_version, 
            target_version, 
            chrono::Utc::now().timestamp()
        );
        
        // 根据策略构建部署阶段
        let stages = self.build_deployment_stages(&strategy, units)?;
        
        // 构建验证步骤
        let verification_steps = self.build_verification_steps(&strategy, &source_version, &target_version)?;
        
        // 构建回滚步骤
        let rollback_steps = self.build_rollback_steps(&stages)?;
        
        // 创建部署计划
        let plan = DeploymentPlan {
            id: plan_id,
            source_version,
            target_version,
            strategy,
            stages,
            verification_steps,
            rollback_steps,
            started_at: None,
            completed_at: None,
            status: DeploymentPlanStatus::Planned,
            current_stage_index: 0,
        };
        
        // 保存部署计划
        let mut current_plans = self.current_plans.write().unwrap();
        current_plans.insert(plan.id.clone(), plan.clone());
        
        Ok(plan)
    }
    
    // 构建部署阶段
    fn build_deployment_stages(
        &self,
        strategy: &DeploymentStrategy,
        units: Vec<DeploymentUnit>,
    ) -> Result<Vec<DeploymentStage>, DeploymentError> {
        let mut stages = Vec::new();
        
        match strategy {
            DeploymentStrategy::BlueGreen { .. } => {
                // 蓝绿部署：创建两个阶段
                // 1. 准备阶段：部署新版本但不接收流量
                let prepare_stage = DeploymentStage {
                    name: "准备新环境".to_string(),
                    units: units.clone(),
                    dependencies: vec![],
                    status: StageStatus::Pending,
                    started_at: None,
                    completed_at: None,
                    retries: 0,
                    max_retries: 3,
                };
                
                // 2. 切换阶段：将流量切换到新版本
                let switch_stage = DeploymentStage {
                    name: "切换流量".to_string(),
                    units: units,
                    dependencies: vec!["准备新环境".to_string()],
                    status: StageStatus::Pending,
                    started_at: None,
                    completed_at: None,
                    retries: 0,
                    max_retries: 2,
                };
                
                stages.push(prepare_stage);
                stages.push(switch_stage);
            },
            DeploymentStrategy::Canary { 
                initial_percentage, 
                increment_step, 
                max_verification_rounds,
                ..
            } => {
                // 金丝雀部署：创建多个阶段，逐步增加流量
                let mut current_percentage = *initial_percentage;
                let mut stage_count = 0;
                
                while stage_count < *max_verification_rounds && current_percentage < 100.0 {
                    let stage_name = if stage_count == 0 {
                        format!("初始部署 ({}%)", current_percentage * 100.0)
                    } else {
                        format!("增加流量 ({}%)", current_percentage * 100.0)
                    };
                    
                    let dependencies = if stage_count == 0 {
                        vec![]
                    } else {
                        vec![format!("增加流量 ({}%)", (current_percentage - increment_step) * 100.0)]
                    };
                    
                    let stage = DeploymentStage {
                        name: stage_name,
                        units: units.clone(),
                        dependencies,
                        status: StageStatus::Pending,
                        started_at: None,
                        completed_at: None,
                        retries: 0,
                        max_retries: 2,
                    };
                    
                    stages.push(stage);
                    
                    current_percentage += increment_step;
                    stage_count += 1;
                }
                
                // 最终阶段：100%流量
                let final_stage = DeploymentStage {
                    name: "完全部署 (100%)".to_string(),
                    units,
                    dependencies: if stages.is_empty() {
                        vec![]
                    } else {
                        vec![stages.last().unwrap().name.clone()]
                    },
                    status: StageStatus::Pending,
                    started_at: None,
                    completed_at: None,
                    retries: 0,
                    max_retries: 1,
                };
                
                stages.push(final_stage);
            },
            DeploymentStrategy::Rolling { batch_size, .. } => {
                // 滚动部署：按批次部署
                let total_units = units.len();
                let mut remaining_units = units;
                let mut batch_number = 1;
                
                while !remaining_units.is_empty() {
                    let batch_units_count = std::cmp::min(*batch_size, remaining_units.len());
                    let batch_units: Vec<_> = remaining_units.drain(..batch_units_count).collect();
                    
                    let stage_name = format!("批次 {} ({}/{})", 
                        batch_number, 
                        batch_number * batch_size,
                        total_units
                    );
                    
                    let dependencies = if batch_number == 1 {
                        vec![]
                    } else {
                        vec![format!("批次 {} ({}/{})", 
                            batch_number - 1, 
                            (batch_number - 1) * batch_size,
                            total_units
                        )]
                    };
                    
                    let stage = DeploymentStage {
                        name: stage_name,
                        units: batch_units,
                        dependencies,
                        status: StageStatus::Pending,
                        started_at: None,
                        completed_at: None,
                        retries: 0,
                        max_retries: 3,
                    };
                    
                    stages.push(stage);
                    batch_number += 1;
                }
            },
            DeploymentStrategy::Shadowing { .. } => {
                // 影子部署：创建两个阶段
                // 1. 启动影子实例
                let shadow_stage = DeploymentStage {
                    name: "启动影子实例".to_string(),
                    units: units.clone(),
                    dependencies: vec![],
                    status: StageStatus::Pending,
                    started_at: None,
                    completed_at: None,
                    retries: 0,
                    max_retries: 3,
                };
                
                // 2. 切换到新版本
                let switch_stage = DeploymentStage {
                    name: "切换到新版本".to_string(),
                    units,
                    dependencies: vec!["启动影子实例".to_string()],
                    status: StageStatus::Pending,
                    started_at: None,
                    completed_at: None,
                    retries: 0,
                    max_retries: 2,
                };
                
                stages.push(shadow_stage);
                stages.push(switch_stage);
            },
        }
        
        Ok(stages)
    }
    
    // 构建验证步骤
    fn build_verification_steps(
        &self,
        strategy: &DeploymentStrategy,
        source_version: &Version,
        target_version: &Version,
    ) -> Result<Vec<VerificationStep>, DeploymentError> {
        let mut steps = Vec::new();
        
        // 基本健康检查
        let health_check = VerificationStep {
            name: "基本健康检查".to_string(),
            verification_type: VerificationType::HealthCheck { 
                endpoint: "/health".to_string(), 
                expected_status: 200,
            },
            timeout: Duration::from_secs(30),
            status: VerificationStatus::Pending,
            result: None,
        };
        steps.push(health_check);
        
        // 功能测试
        let functional_test = VerificationStep {
            name: "功能测试套件".to_string(),
            verification_type: VerificationType::FunctionalTest { 
                test_suite: "basic-workflows".to_string(),
            },
            timeout: Duration::from_secs(300),
            status: VerificationStatus::Pending,
            result: None,
        };
        steps.push(functional_test);
        
        // 根据部署策略添加特定的验证步骤
        match strategy {
            DeploymentStrategy::BlueGreen { .. } => {
                // 蓝绿部署特定验证
                let traffic_verification = VerificationStep {
                    name: "流量切换验证".to_string(),
                    verification_type: VerificationType::MetricThreshold { 
                        metric: "error_rate".to_string(), 
                        operator: "<".to_string(), 
                        threshold: 0.01,
                    },
                    timeout: Duration::from_secs(180),
                    status: VerificationStatus::Pending,
                    result: None,
                };
                steps.push(traffic_verification);
            },
            DeploymentStrategy::Canary { .. } => {
                // 金丝雀部署特定验证
                let latency_verification = VerificationStep {
                    name: "延迟指标验证".to_string(),
                    verification_type: VerificationType::MetricThreshold { 
                        metric: "p95_latency".to_string(), 
                        operator: "<".to_string(), 
                        threshold: 500.0,
                    },
                    timeout: Duration::from_secs(120),
                    status: VerificationStatus::Pending,
                    result: None,
                };
                steps.push(latency_verification);
                
                let error_rate_verification = VerificationStep {
                    name: "错误率验证".to_string(),
                    verification_type: VerificationType::MetricThreshold { 
                        metric: "error_rate".to_string(), 
                        operator: "<".to_string(), 
                        threshold: 0.02,
                    },
                    timeout: Duration::from_secs(120),
                    status: VerificationStatus::Pending,
                    result: None,
                };
                steps.push(error_rate_verification);
            },
            DeploymentStrategy::Shadowing { comparison_strategy, .. } => {
                // 影子部署特定验证
                match comparison_strategy {
                    ShadowComparisonStrategy::ResponseMatch { required_match_percentage } => {
                        let response_match_verification = VerificationStep {
                            name: "响应匹配度验证".to_string(),
                            verification_type: VerificationType::MetricThreshold { 
                                metric: "response_match_percentage".to_string(), 
                                operator: ">".to_string(), 
                                threshold: *required_match_percentage * 100.0,
                            },
                            timeout: Duration::from_secs(300),
                            status: VerificationStatus::Pending,
                            result: None,
                        };
                        steps.push(response_match_verification);
                    },
                    ShadowComparisonStrategy::PerformanceOnly { max_latency_increase_percentage } => {
                        let performance_verification = VerificationStep {
                            name: "性能指标验证".to_string(),
                            verification_type: VerificationType::MetricThreshold { 
                                metric: "latency_increase_percentage".to_string(), 
                                operator: "<".to_string(), 
                                threshold: *max_latency_increase_percentage * 100.0,
                            },
                            timeout: Duration::from_secs(300),
                            status: VerificationStatus::Pending,
                            result: None,
                        };
                        steps.push(performance_verification);
                    },
                    _ => {
                        // 其他比较策略的验证步骤...
                    }
                }
            },
            _ => {
                // 其他策略特定验证...
            }
        }
        
        // 版本兼容性验证
        let compatibility_verification = VerificationStep {
            name: "版本兼容性验证".to_string(),
            verification_type: VerificationType::FunctionalTest { 
                test_suite: format!("compatibility-{}-to-{}", source_version, target_version),
            },
            timeout: Duration::from_secs(180),
            status: VerificationStatus::Pending,
            result: None,
        };
        steps.push(compatibility_verification);
        
        Ok(steps)
    }
    
    // 构建回滚步骤
    fn build_rollback_steps(
        &self,
        stages: &[DeploymentStage],
    ) -> Result<Vec<RollbackStep>, DeploymentError> {
        let mut rollback_steps = Vec::new();
        
        // 为每个阶段创建对应的回滚步骤（逆序）
        for (i, stage) in stages.iter().enumerate().rev() {
            let unit_ids: Vec<_> = stage.units.iter().map(|u| u.id.clone()).collect();
            
            let rollback_step = RollbackStep {
                name: format!("回滚：{}", stage.name),
                units: unit_ids,
                status: RollbackStatus::NotNeeded,
                triggered_by: None,
            };
            
            rollback_steps.push(rollback_step);
        }
        
        Ok(rollback_steps)
    }
    
    // 启动部署计划
    pub fn start_deployment_plan(&self, plan_id: &str) -> Result<(), DeploymentError> {
        let mut current_plans = self.current_plans.write().unwrap();
        
        let plan = current_plans.get_mut(plan_id).ok_or(DeploymentError::PlanNotFound {
            plan_id: plan_id.to_string(),
        })?;
        
        // 检查计划状态
        if plan.status != DeploymentPlanStatus::Planned {
            return Err(DeploymentError::InvalidPlanState {
                plan_id: plan_id.to_string(),
                current_state: format!("{:?}", plan.status),
                expected_state: format!("{:?}", DeploymentPlanStatus::Planned),
            });
        }
        
        // 更新计划状态
        plan.status = DeploymentPlanStatus::Running;
        plan.started_at = Some(chrono::Utc::now());
        
        // 开始执行第一个阶段
        if !plan.stages.is_empty() {
            let first_stage = &mut plan.stages[0];
            first_stage.status = StageStatus::Running;
            first_stage.started_at = Some(chrono::Utc::now());
        }
        
        // 发送通知
        self.notification_manager.send_deployment_notification("deployment_started", plan);
        
        // 创建异步任务执行部署计划
        let plan_clone = plan.clone();
        let self_clone = Arc::new(self.clone());
        
        tokio::spawn(async move {
            self_clone.execute_deployment_plan(plan_clone).await;
        });
        
        Ok(())
    }
    
    // 执行部署计划
    async fn execute_deployment_plan(&self, mut plan: DeploymentPlan) {
        let mut current_stage_index = plan.current_stage_index;
        
        while current_stage_index < plan.stages.len() {
            let stage_result = self.execute_deployment_stage(&mut plan, current_stage_index).await;
            
            // 更新计划
            {
                let mut current_plans = self.current_plans.write().unwrap();
                if let Some(stored_plan) = current_plans.get_mut(&plan.id) {
                    *stored_plan = plan.clone();
                }
            }
            
            match stage_result {
                Ok(()) => {
                    // 阶段成功，继续下一个阶段
                    current_stage_index += 1;
                    plan.current_stage_index = current_stage_index;
                },
                Err(e) => {
                    // 阶段失败，触发回滚
                    let error_msg = format!("阶段执行失败: {}", e);
                    self.trigger_rollback(&mut plan, &error_msg).await;
                    
                    // 更新计划状态为已回滚
                    plan.status = DeploymentPlanStatus::RolledBack;
                    
                    // 更新存储的计划
                    {
                        let mut current_plans = self.current_plans.write().unwrap();
                        if let Some(stored_plan) = current_plans.get_mut(&plan.id) {
                            *stored_plan = plan.clone();
                        }
                    }
                    
                    // 发送通知
                    self.notification_manager.send_deployment_notification("deployment_rolled_back", &plan);
                    
                    return;
                }
            }
        }
        
        // 所有阶段成功完成
        plan.status = DeploymentPlanStatus::Succeeded;
        plan.completed_at = Some(chrono::Utc::now());
        
        // 更新存储的计划
        {
            let mut current_plans = self.current_plans.write().unwrap();
            if let Some(stored_plan) = current_plans.get_mut(&plan.id) {
                *stored_plan = plan.clone();
            }
            
            // 将完成的计划移至历史记录
            let plan_to_archive = current_plans.remove(&plan.id).unwrap();
            let mut plan_history = self.plan_history.write().unwrap();
            plan_history.push(plan_to_archive);
        }
        
        // 发送通知
        self.notification_manager.send_deployment_notification("deployment_completed", &plan);
    }
    
    // 执行部署阶段
    async fn execute_deployment_stage(
        &self,
        plan: &mut DeploymentPlan,
        stage_index: usize,
    ) -> Result<(), DeploymentError> {
        let stage = &mut plan.stages[stage_index];
        
        // 检查依赖的阶段是否完成
        for dep_name in &stage.dependencies {
            let dep_index = plan.stages.iter().position(|s| &s.name == dep_name);
            
            if let Some(idx) = dep_index {
                let dep_stage = &plan.stages[idx];
                if dep_stage.status != StageStatus::Succeeded {
                    return Err(DeploymentError::DependencyNotSatisfied {
                        stage: stage.name.clone(),
                        dependency: dep_name.clone(),
                    });
                }
            } else {
                return Err(DeploymentError::DependencyNotFound {
                    stage: stage.name.clone(),
                    dependency: dep_name.clone(),
                });
            }
        }
        
        // 更新阶段状态
        stage.status = StageStatus::Running;
        stage.started_at = Some(chrono::Utc::now());
        
        // 部署所有单元
        for unit in &mut stage.units {
            match self.deploy_unit(unit, plan).await {
                Ok(()) => {
                    // 部署成功，单元状态更新为Active
                    unit.state = DeploymentState::Active;
                },
                Err(e) => {
                    // 部署失败，重试
                    if stage.retries < stage.max_retries {
                        stage.retries += 1;
                        
                        // 等待5秒后重试
                        tokio::time::sleep(Duration::from_secs(5)).await;
                        
                        // 递归调用自身重试
                        return self.execute_deployment_stage(plan, stage_index).await;
                    } else {
                        // 超过最大重试次数，阶段失败
                        stage.status = StageStatus::Failed;
                        stage.completed_at = Some(chrono::Utc::now());
                        
                        return Err(DeploymentError::DeploymentFailed {
                            unit: unit.id.clone(),
                            reason: format!("部署单元失败: {}", e),
                        });
                    }
                }
            }
        }
        
        // 执行验证
        self.execute_verification_steps(plan).await?;
        
        // 阶段成功完成
        stage.status = StageStatus::Succeeded;
        stage.completed_at = Some(chrono::Utc::now());
        
        Ok(())
    }
    
    // 部署单个单元
    async fn deploy_unit(
        &self,
        unit: &mut DeploymentUnit,
        plan: &DeploymentPlan,
    ) -> Result<(), DeploymentError> {
        // 记录部署开始
        let start_time = Instant::now();
        self.metrics_collector.record_deployment_event(
            "unit_deployment_started",
            unit,
            HashMap::new(),
        );
        
        // 根据部署策略执行不同的部署步骤
        match &plan.strategy {
            DeploymentStrategy::BlueGreen { .. } => {
                // 蓝绿部署：首先将单元部署为暂存状态
                unit.state = DeploymentState::Staged;
                
                // 将单元添加到暂存部署
                {
                    let mut staged = self.staged_deployments.write().unwrap();
                    staged.insert(unit.id.clone(), unit.clone());
                }
                
                // 检查是否需要切换流量
                if plan.stages[plan.current_stage_index].name.contains("切换流量") {
                    // 切换流量：将单元从暂存移至活动
                    let mut staged = self.staged_deployments.write().unwrap();
                    let mut active = self.active_deployments.write().unwrap();
                    
                    if let Some(staged_unit) = staged.remove(&unit.id) {
                        // 将旧单元移至历史记录
                        if let Some(old_unit) = active.remove(&unit.id) {
                            old_unit.state = DeploymentState::Deprecated;
                            let mut history = self.deployment_history.write().unwrap();
                            history.push(old_unit);
                        }
                        
                        // 激活新单元
                        unit.state = DeploymentState::Active;
                        active.insert(unit.id.clone(), staged_unit);
                    }
                }
            },
            DeploymentStrategy::Canary { .. } => {
                // 金丝雀部署：根据阶段名称确定流量百分比
                let stage_name = &plan.stages[plan.current_stage_index].name;
                let percentage = if let Some(p) = stage_name.find('(') {
                    if let Some(e) = stage_name.find('%') {
                        if let Ok(percent) = stage_name[p+1..e].trim().parse::<f64>() {
                            percent / 100.0
                        } else {
                            0.0
                        }
                    } else {
                        0.0
                    }
                } else {
                    0.0
                };
                
                // 设置流量比例
                unit.metadata.insert("traffic_percentage".to_string(), percentage.to_string());
                
                // 部署单元
                {
                    let mut active = self.active_deployments.write().unwrap();
                    
                    if percentage >= 0.99 {
                        // 近似100%流量：完全切换
                        if let Some(old_unit) = active.get(&unit.id) {
                            let mut old_unit = old_unit.clone();
                            old_unit.state = DeploymentState::Deprecated;
                            
                            let mut history = self.deployment_history.write().unwrap();
                            history.push(old_unit);
                        }
                        
                        // 设置为活动状态
                        unit.state = DeploymentState::Active;
                        active.insert(unit.id.clone(), unit.clone());
                    } else {
                        // 部分流量：记录流量比例
                        if active.contains_key(&unit.id) {
                            let active_unit = active.get_mut(&unit.id).unwrap();
                            active_unit.metadata.insert("traffic_percentage".to_string(), percentage.to_string());
                        } else {
                            unit.state = DeploymentState::Active;
                            active.insert(unit.id.clone(), unit.clone());
                        }
                    }
                }
            },
            DeploymentStrategy::Rolling { .. } => {
                // 滚动部署：直接替换旧版本
                {
                    let mut active = self.active_deployments.write().unwrap();
                    
                    // 将旧单元移至历史记录
                    if let Some(old_unit) = active.remove(&unit.id) {
                        old_unit.state = DeploymentState::Deprecated;
                        let mut history = self.deployment_history.write().unwrap();
                        history.push(old_unit);
                    }
                    
                    // 激活新单元
                    unit.state = DeploymentState::Active;
                    active.insert(unit.id.clone(), unit.clone());
                }
            },
            DeploymentStrategy::Shadowing { .. } => {
                // 影子部署：根据阶段处理
                if plan.stages[plan.current_stage_index].name.contains("影子") {
                    // 影子阶段：部署但不接收实际流量
                    unit.metadata.insert("shadow_mode".to_string(), "true".to_string());
                    unit.state = DeploymentState::Staged;
                    
                    {
                        let mut staged = self.staged_deployments.write().unwrap();
                        staged.insert(unit.id.clone(), unit.clone());
                    }
                } else {
                    // 切换阶段：替换旧版本
                    {
                        let mut staged = self.staged_deployments.write().unwrap();
                        let mut active = self.active_deployments.write().unwrap();
                        
                        if let Some(mut staged_unit) = staged.remove(&unit.id) {
                            // 将旧单元移至历史记录
                            if let Some(old_unit) = active.remove(&unit.id) {
                                old_unit.state = DeploymentState::Deprecated;
                                let mut history = self.deployment_history.write().unwrap();
                                history.push(old_unit);
                            }
                            
                            // 清除影子模式标记
                            staged_unit.metadata.remove("shadow_mode");
                            
                            // 激活新单元
                            staged_unit.state = DeploymentState::Active;
                            active.insert(unit.id.clone(), staged_unit);
                        }
                    }
                }
            },
        }
        
        // 检查健康状态
        self.check_deployment_health(unit).await?;
        
        // 记录部署完成
        let duration = start_time.elapsed();
        let mut details = HashMap::new();
        details.insert("duration_ms".to_string(), duration.as_millis().to_string());
        
        self.metrics_collector.record_deployment_event(
            "unit_deployment_completed",
            unit,
            details,
        );
        
        Ok(())
    }
    
    // 检查部署单元的健康状态
    async fn check_deployment_health(
        &self,
        unit: &DeploymentUnit,
    ) -> Result<(), DeploymentError> {
        // 检查所有组件的健康状态
        for component in &unit.components {
            if let Some(health_check_type) = &component.health_check {
                if let Some(health_checker) = self.health_checks.get(health_check_type) {
                    let health_status = health_checker.check_health(component);
                    
                    if health_status == HealthStatus::Unhealthy {
                        let details = health_checker.get_details(component);
                        return Err(DeploymentError::HealthCheckFailed {
                            component: component.name.clone(),
                            details: format!("{:?}", details),
                        });
                    }
                }
            }
        }
        
        Ok(())
    }
    
    // 执行验证步骤
    async fn execute_verification_steps(
        &self,
        plan: &mut DeploymentPlan,
    ) -> Result<(), DeploymentError> {
        for (i, step) in plan.verification_steps.iter_mut().enumerate() {
            // 检查是否需要执行此验证步骤
            let should_execute = match &step.verification_type {
                VerificationType::HealthCheck { .. } => true, // 总是执行健康检查
                VerificationType::FunctionalTest { .. } => {
                    // 根据当前阶段决定是否执行功能测试
                    let current_stage = &plan.stages[plan.current_stage_index];
                    current_stage.name.contains("完全") || plan.current_stage_index == plan.stages.len() - 1
                },
                VerificationType::MetricThreshold { .. } => {
                    // 指标阈值验证通常在每个阶段后执行
                    true
                },
                VerificationType::ManualApproval { .. } => {
                    // 手动审批通常只在关键阶段执行
                    let current_stage = &plan.stages[plan.current_stage_index];
                    current_stage.name.contains("切换") || current_stage.name.contains("100%")
                },
            };
            
            if !should_execute {
                continue;
            }
            
            // 更新验证步骤状态
            step.status = VerificationStatus::Running;
            
            // 执行验证
            match &step.verification_type {
                VerificationType::HealthCheck { endpoint, expected_status } => {
                    // 执行健康检查验证
                    let result = self.execute_health_check_verification(endpoint, *expected_status).await;
                    
                    match result {
                        Ok(verification_result) => {
                            step.result = Some(verification_result);
                            step.status = VerificationStatus::Succeeded;
                        },
                        Err(e) => {
                            let error_result = VerificationResult {
                                success: false,
                                message: format!("健康检查失败: {}", e),
                                metrics: HashMap::new(),
                                timestamp: chrono::Utc::now(),
                            };
                            
                            step.result = Some(error_result);
                            step.status = VerificationStatus::Failed;
                            
                            return Err(DeploymentError::VerificationFailed {
                                step: step.name.clone(),
                                reason: format!("健康检查失败: {}", e),
                            });
                        }
                    }
                },
                VerificationType::FunctionalTest { test_suite } => {
                    // 执行功能测试验证
                    let result = self.execute_functional_test_verification(test_suite).await;
                    
                    match result {
                        Ok(verification_result) => {
                            step.result = Some(verification_result);
                            step.status = VerificationStatus::Succeeded;
                        },
                        Err(e) => {
                            let error_result = VerificationResult {
                                success: false,
                                message: format!("功能测试失败: {}", e),
                                metrics: HashMap::new(),
                                timestamp: chrono::Utc::now(),
                            };
                            
                            step.result = Some(error_result);
                            step.status = VerificationStatus::Failed;
                            
                            return Err(DeploymentError::VerificationFailed {
                                step: step.name.clone(),
                                reason: format!("功能测试失败: {}", e),
                            });
                        }
                    }
                },
                VerificationType::MetricThreshold { metric, operator, threshold } => {
                    // 执行指标阈值验证
                    let result = self.execute_metric_threshold_verification(metric, operator, *threshold).await;
                    
                    match result {
                        Ok(verification_result) => {
                            step.result = Some(verification_result);
                            step.status = VerificationStatus::Succeeded;
                        },
                        Err(e) => {
                            let error_result = VerificationResult {
                                success: false,
                                message: format!("指标阈值验证失败: {}", e),
                                metrics: HashMap::new(),
                                timestamp: chrono::Utc::now(),
                            };
                            
                            step.result = Some(error_result);
                            step.status = VerificationStatus::Failed;
                            
                            return Err(DeploymentError::VerificationFailed {
                                step: step.name.clone(),
                                reason: format!("指标阈值验证失败: {}", e),
                            });
                        }
                    }
                },
                VerificationType::ManualApproval { approvers } => {
                    // 执行手动审批验证
                    let result = self.execute_manual_approval_verification(approvers).await;
                    
                    match result {
                        Ok(verification_result) => {
                            step.result = Some(verification_result);
                            step.status = VerificationStatus::Succeeded;
                        },
                        Err(e) => {
                            let error_result = VerificationResult {
                                success: false,
                                message: format!("手动审批验证失败: {}", e),
                                metrics: HashMap::new(),
                                timestamp: chrono::Utc::now(),
                            };
                            
                            step.result = Some(error_result);
                            step.status = VerificationStatus::Failed;
                            
                            return Err(DeploymentError::VerificationFailed {
                                step: step.name.clone(),
                                reason: format!("手动审批验证失败: {}", e),
                            });
                        }
                    }
                },
            }
            
            // 发送验证结果通知
            if let Some(result) = &step.result {
                self.notification_manager.send_verification_notification(step, result);
            }
        }
        
        Ok(())
    }
    
    // 执行健康检查验证
    async fn execute_health_check_verification(
        &self,
        endpoint: &str,
        expected_status: u16,
    ) -> Result<VerificationResult, String> {
        // 模拟健康检查验证
        println!("执行健康检查: {} (期望状态码: {})", endpoint, expected_status);
        
        // 假设检查成功
        let mut metrics = HashMap::new();
        metrics.insert("response_time_ms".to_string(), 45.0);
        metrics.insert("status_code".to_string(), expected_status as f64);
        
        let result = VerificationResult {
            success: true,
            message: format!("健康检查成功: {}", endpoint),
            metrics,
            timestamp: chrono::Utc::now(),
        };
        
        Ok(result)
    }
    
    // 执行功能测试验证
    async fn execute_functional_test_verification(
        &self,
        test_suite: &str,
    ) -> Result<VerificationResult, String> {
        // 模拟功能测试验证
        println!("执行功能测试套件: {}", test_suite);
        
        // 假设测试成功
        let mut metrics = HashMap::new();
        metrics.insert("tests_total".to_string(), 42.0);
        metrics.insert("tests_passed".to_string(), 42.0);
        metrics.insert("duration_ms".to_string(), 3500.0);
        
        let result = VerificationResult {
            success: true,
            message: format!("功能测试套件 {} 通过", test_suite),
            metrics,
            timestamp: chrono::Utc::now(),
        };
        
        Ok(result)
    }
    
    // 执行指标阈值验证
    async fn execute_metric_threshold_verification(
        &self,
        metric: &str,
        operator: &str,
        threshold: f64,
    ) -> Result<VerificationResult, String> {
        // 模拟指标阈值验证
        println!("验证指标: {} {} {}", metric, operator, threshold);
        
        // 获取当前指标值（模拟）
        let current_value = match metric {
            "error_rate" => 0.005, // 0.5% 错误率
            "p95_latency" => 320.0, // 320ms p95延迟
            "cpu_usage" => 65.0,   // 65% CPU使用率
            "memory_usage" => 70.0, // 70% 内存使用率
            _ => 0.0,
        };
        
        // 验证指标是否满足阈值要求
        let success = match operator {
            "<" => current_value < threshold,
            "<=" => current_value <= threshold,
            ">" => current_value > threshold,
            ">=" => current_value >= threshold,
            "=" | "==" => (current_value - threshold).abs() < 0.0001, // 浮点数比较
            "!=" => (current_value - threshold).abs() >= 0.0001,     // 浮点数比较
            _ => false,
        };
        
        let mut metrics = HashMap::new();
        metrics.insert(metric.to_string(), current_value);
        metrics.insert("threshold".to_string(), threshold);
        
        let result = if success {
            VerificationResult {
                success: true,
                message: format!("指标验证通过: {} 当前值为 {} {} {}", 
                               metric, current_value, operator, threshold),
                metrics,
                timestamp: chrono::Utc::now(),
            }
        } else {
            VerificationResult {
                success: false,
                message: format!("指标验证失败: {} 当前值为 {} 不满足 {} {}", 
                               metric, current_value, operator, threshold),
                metrics,
                timestamp: chrono::Utc::now(),
            }
        };
        
        if success {
            Ok(result)
        } else {
            Err(result.message)
        }
    }
    
    // 执行手动审批验证
    async fn execute_manual_approval_verification(
        &self,
        approvers: &[String],
    ) -> Result<VerificationResult, String> {
        // 模拟手动审批验证
        println!("等待手动审批, 审批人: {:?}", approvers);
        
        // 在实际系统中，这里应该创建一个审批请求，并等待审批结果
        // 为了演示，我们假设审批已通过
        
        let mut metrics = HashMap::new();
        metrics.insert("approval_time_ms".to_string(), 60000.0); // 1分钟审批时间
        metrics.insert("approvers_count".to_string(), approvers.len() as f64);
        
        let result = VerificationResult {
            success: true,
            message: format!("手动审批通过，审批人: {:?}", approvers),
            metrics,
            timestamp: chrono::Utc::now(),
        };
        
        Ok(result)
    }
    
    // 触发回滚
    async fn trigger_rollback(
        &self,
        plan: &mut DeploymentPlan,
        reason: &str,
    ) {
        println!("触发部署回滚: {}", reason);
        
        // 更新计划状态
        plan.status = DeploymentPlanStatus::RollingBack;
        
        // 发送回滚开始通知
        self.notification_manager.send_deployment_notification("rollback_started", plan);
        
        // 执行回滚步骤
        for (i, step) in plan.rollback_steps.iter_mut().enumerate() {
            step.status = RollbackStatus::Running;
            
            let mut success = true;
            let mut error_message = String::new();
            
            // 回滚每个部署单元
            for unit_id in &step.units {
                if let Err(e) = self.rollback_unit(unit_id).await {
                    success = false;
                    error_message = format!("单元 {} 回滚失败: {}", unit_id, e);
                    break;
                }
            }
            
            if success {
                step.status = RollbackStatus::Completed;
                
                // 发送回滚步骤成功通知
                self.notification_manager.send_rollback_notification(
                    step,
                    true,
                    &format!("回滚步骤成功完成: {}", step.name),
                );
            } else {
                step.status = RollbackStatus::Failed;
                
                // 发送回滚步骤失败通知
                self.notification_manager.send_rollback_notification(
                    step,
                    false,
                    &error_message,
                );
                
                // 回滚失败，更新计划状态
                plan.status = DeploymentPlanStatus::Failed;
                
                return;
            }
        }
        
        // 所有回滚步骤成功完成
        plan.status = DeploymentPlanStatus::RolledBack;
        plan.completed_at = Some(chrono::Utc::now());
        
        // 发送回滚完成通知
        self.notification_manager.send_deployment_notification("rollback_completed", plan);
    }
    
    // 回滚单个部署单元
    async fn rollback_unit(&self, unit_id: &str) -> Result<(), DeploymentError> {
        println!("回滚部署单元: {}", unit_id);
        
        // 查找活动部署中的单元
        let mut staged_unit = None;
        let mut active_unit = None;
        
        {
            let staged = self.staged_deployments.read().unwrap();
            if let Some(unit) = staged.get(unit_id) {
                staged_unit = Some(unit.clone());
            }
            
            let active = self.active_deployments.read().unwrap();
            if let Some(unit) = active.get(unit_id) {
                active_unit = Some(unit.clone());
            }
        }
        
        // 查找最近的历史版本
        let mut historical_unit = None;
        
        {
            let history = self.deployment_history.read().unwrap();
            
            // 找到最近的非Retired版本
            for unit in history.iter().rev() {
                if unit.id == unit_id && unit.state != DeploymentState::Retired {
                    historical_unit = Some(unit.clone());
                    break;
                }
            }
        }
        
        // 执行回滚
        if let Some(hist_unit) = historical_unit {
            // 有历史版本可回滚
            
            // 从活动部署中移除当前版本
            if active_unit.is_some() {
                let mut active = self.active_deployments.write().unwrap();
                active.remove(unit_id);
            }
            
            // 从暂存部署中移除新版本
            if staged_unit.is_some() {
                let mut staged = self.staged_deployments.write().unwrap();
                staged.remove(unit_id);
            }
            
            // 恢复历史版本到活动部署
            let mut restored_unit = hist_unit.clone();
            restored_unit.state = DeploymentState::Active;
            
            {
                let mut active = self.active_deployments.write().unwrap();
                active.insert(unit_id.to_string(), restored_unit);
            }
            
            Ok(())
        } else if active_unit.is_some() {
            // 没有历史版本但有活动版本，保持现状
            Ok(())
        } else {
            // 既没有历史版本也没有活动版本，无法回滚
            Err(DeploymentError::RollbackFailed {
                unit: unit_id.to_string(),
                reason: "找不到可回滚的历史版本".to_string(),
            })
        }
    }
}

// 版本化的数据容器
#[derive(Clone)]
pub struct VersionedData<T, V: VersionMarker> {
    data: T,
    _marker: PhantomData<V>,
}

impl<T, V: VersionMarker> VersionedData<T, V> {
    pub fn new(data: T) -> Self {
        Self {
            data,
            _marker: PhantomData,
        }
    }
    
    pub fn get(&self) -> &T {
        &self.data
    }
    
    pub fn into_inner(self) -> T {
        self.data
    }
    
    // 升级到新版本
    pub fn upgrade<NewV: VersionMarker, U, F: FnOnce(T) -> U>(self, f: F) -> VersionedData<U, NewV> {
        VersionedData::new(f(self.data))
    }
    
    // 降级到旧版本
    pub fn downgrade<OldV: VersionMarker, U, F: FnOnce(T) -> U>(self, f: F) -> VersionedData<U, OldV> {
        VersionedData::new(f(self.data))
    }
}

// 版本标记特征
pub trait VersionMarker: 'static {}

// 版本标记示例
#[derive(Debug, Clone, Copy)]
pub struct V1_0_0;
#[derive(Debug, Clone, Copy)]
pub struct V1_1_0;
#[derive(Debug, Clone, Copy)]
pub struct V2_0_0;

impl VersionMarker for V1_0_0 {}
impl VersionMarker for V1_1_0 {}
impl VersionMarker for V2_0_0 {}

// 部署错误类型
#[derive(Debug, Clone)]
pub enum DeploymentError {
    IncompatibleVersions {
        from: String,
        to: String,
    },
    PlanNotFound {
        plan_id: String,
    },
    InvalidPlanState {
        plan_id: String,
        current_state: String,
        expected_state: String,
    },
    DependencyNotSatisfied {
        stage: String,
        dependency: String,
    },
    DependencyNotFound {
        stage: String,
        dependency: String,
    },
    DeploymentFailed {
        unit: String,
        reason: String,
    },
    HealthCheckFailed {
        component: String,
        details: String,
    },
    VerificationFailed {
        step: String,
        reason: String,
    },
    RollbackFailed {
        unit: String,
        reason: String,
    },
}

impl std::fmt::Display for DeploymentError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            DeploymentError::IncompatibleVersions { from, to } => {
                write!(f, "不兼容的版本: {} -> {}", from, to)
            }
            DeploymentError::PlanNotFound { plan_id } => {
                write!(f, "找不到部署计划: {}", plan_id)
            }
            DeploymentError::InvalidPlanState { plan_id, current_state, expected_state } => {
                write!(f, "部署计划状态无效: {} 当前: {} 期望: {}", plan_id, current_state, expected_state)
            }
            DeploymentError::DependencyNotSatisfied { stage, dependency } => {
                write!(f, "阶段 {} 的依赖未满足: {}", stage, dependency)
            }
            DeploymentError::DependencyNotFound { stage, dependency } => {
                write!(f, "阶段 {} 的依赖不存在: {}", stage, dependency)
            }
            DeploymentError::DeploymentFailed { unit, reason } => {
                write!(f, "部署单元 {} 失败: {}", unit, reason)
            }
            DeploymentError::HealthCheckFailed { component, details } => {
                write!(f, "组件 {} 健康检查失败: {}", component, details)
            }
            DeploymentError::VerificationFailed { step, reason } => {
                write!(f, "验证步骤 {} 失败: {}", step, reason)
            }
            DeploymentError::RollbackFailed { unit, reason } => {
                write!(f, "回滚单元 {} 失败: {}", unit, reason)
            }
        }
    }
}

impl std::error::Error for DeploymentError {}

// 使用示例
fn zero_downtime_demo() {
    // 创建版本兼容性注册表
    let version_registry = Arc::new(VersionCompatibilityRegistry::new());
    
    // 注册版本和兼容性
    let v1_0_0 = Version::parse("1.0.0").unwrap();
    let v1_1_0 = Version::parse("1.1.0").unwrap();
    let v2_0_0 = Version::parse("2.0.0").unwrap();
    
    // 注册版本元数据
    version_registry.register_version(VersionMetadata {
        version: v1_0_0.clone(),
        release_date: chrono::Utc::now() - chrono::Duration::days(100),
        end_of_support: Some(chrono::Utc::now() + chrono::Duration::days(265)),
        breaking_changes: vec![],
        features: vec!["基础工作流".to_string(), "用户管理".to_string()],
        dependencies: HashMap::new(),
    });
    
    version_registry.register_version(VersionMetadata {
        version: v1_1_0.clone(),
        release_date: chrono::Utc::now() - chrono::Duration::days(30),
        end_of_support: Some(chrono::Utc::now() + chrono::Duration::days(335)),
        breaking_changes: vec![],
        features: vec!["基础工作流".to_string(), "用户管理".to_string(), "高级调度".to_string()],
        dependencies: HashMap::new(),
    });
    
    version_registry.register_version(VersionMetadata {
        version: v2_0_0.clone(),
        release_date: chrono::Utc::now() - chrono::Duration::days(5),
        end_of_support: None,
        breaking_changes: vec!["API路径变更".to_string(), "配置格式更新".to_string()],
        features: vec!["分布式工作流".to_string(), "多租户支持".to_string(), "高级调度".to_string()],
        dependencies: HashMap::new(),
    });
    
    // 设置版本兼容性
    version_registry.set_compatibility(&v1_0_0, &v1_1_0, CompatibilityLevel::BackwardCompatible);
    version_registry.set_compatibility(&v1_1_0, &v1_0_0, CompatibilityLevel::ForwardCompatible);
    version_registry.set_compatibility(&v1_1_0, &v2_0_0, CompatibilityLevel::BackwardCompatible);
    
    // 注册迁移路径
    version_registry.register_migration_path(&v1_0_0, &v2_0_0, vec![v1_1_0.clone()]);
    
    // 创建指标收集器和通知管理器（这里使用简单实现）
    let metrics_collector = Arc::new(SimpleMetricsCollector {});
    let notification_manager = Arc::new(SimpleNotificationManager {});
    
    // 创建部署管理器
    let mut deployment_manager = ZeroDowntimeDeploymentManager::new(
        version_registry.clone(),
        metrics_collector,
        notification_manager,
    );
    
    // 注册健康检查
    deployment_manager.register_health_check(
        "workflow-engine".to_string(),
        SimpleHealthCheck {},
    );
    
    // 创建部署单元
    let components = vec![
        ComponentInfo {
            name: "workflow-engine".to_string(),
            version: v1_0_0.clone(),
            required: true,
            health_check: Some("workflow-engine".to_string()),
        },
        ComponentInfo {
            name: "user-service".to_string(),
            version: v1_0_0.clone(),
            required: true,
            health_check: None,
        },
    ];
    
    let deployment_unit = DeploymentUnit {
        id: "workflow-system".to_string(),
        version: v1_0_0.clone(),
        components,
        dependencies: HashMap::new(),
        state: DeploymentState::Active,
        health: HealthStatus::Healthy,
        last_updated: chrono::Utc::now(),
        metadata: HashMap::new(),
    };
    
    // 创建升级到v1.1.0的部署计划
    let canary_strategy = DeploymentStrategy::Canary {
        initial_percentage: 0.1,
        increment_step: 0.2,
        verification_period: Duration::from_secs(300),
        max_verification_rounds: 4,
    };
    
    let new_components = vec![
        ComponentInfo {
            name: "workflow-engine".to_string(),
            version: v1_1_0.clone(),
            required: true,
            health_check: Some("workflow-engine".to_string()),
        },
        ComponentInfo {
            name: "user-service".to_string(),
            version: v1_1_0.clone(),
            required: true,
            health_check: None,
        },
        ComponentInfo {
            name: "scheduler".to_string(),
            version: v1_1_0.clone(),
            required: true,
            health_check: None,
        },
    ];
    
    let new_deployment_unit = DeploymentUnit {
        id: "workflow-system".to_string(),
        version: v1_1_0.clone(),
        components: new_components,
        dependencies: HashMap::new(),
        state: DeploymentState::Staged,
        health: HealthStatus::Unknown,
        last_updated: chrono::Utc::now(),
        metadata: HashMap::new(),
    };
    
    // 创建部署计划
    let plan_result = deployment_manager.create_deployment_plan(
        v1_0_0.clone(), 
        v1_1_0.clone(), 
        canary_strategy,
        vec![new_deployment_unit],
    );
    
    match plan_result {
        Ok(plan) => {
            println!("成功创建部署计划: {}", plan.id);
            println!("计划包含 {} 个阶段", plan.stages.len());
            
            // 启动部署计划
            match deployment_manager.start_deployment_plan(&plan.id) {
                Ok(()) => {
                    println!("部署计划启动成功");
                },
                Err(e) => {
                    println!("部署计划启动失败: {}", e);
                }
            }
        },
        Err(e) => {
            println!("创建部署计划失败: {}", e);
        }
    }
}

// 简单的指标收集器实现
struct SimpleMetricsCollector {}

impl MetricsCollector for SimpleMetricsCollector {
    fn collect_deployment_metrics(&self, unit: &DeploymentUnit) -> HashMap<String, f64> {
        println!("收集部署指标: {}", unit.id);
        let mut metrics = HashMap::new();
        metrics.insert("deployment_duration_ms".to_string(), 1500.0);
        metrics
    }
    
    fn collect_verification_metrics(&self, step: &VerificationStep) -> HashMap<String, f64> {
        println!("收集验证指标: {}", step.name);
        let mut metrics = HashMap::new();
        metrics.insert("verification_duration_ms".to_string(), 800.0);
        metrics
    }
    
    fn record_deployment_event(&self, event_type: &str, unit: &DeploymentUnit, details: HashMap<String, String>) {
        println!("记录部署事件: {} 单元: {} 详情: {:?}", event_type, unit.id, details);
    }
}

// 简单的通知管理器实现
struct SimpleNotificationManager {}

impl NotificationManager for SimpleNotificationManager {
    fn send_deployment_notification(&self, event_type: &str, plan: &DeploymentPlan) {
        println!("发送部署通知: {} 计划: {}", event_type, plan.id);
    }
    
    fn send_verification_notification(&self, step: &VerificationStep, result: &VerificationResult) {
        println!("发送验证通知: {} 结果: {}", step.name, if result.success { "成功" } else { "失败" });
    }
    
    fn send_rollback_notification(&self, step: &RollbackStep, success: bool, message: &str) {
        println!("发送回滚通知: {} 结果: {} 消息: {}", step.name, if success { "成功" } else { "失败" }, message);
    }
}

// 简单的健康检查实现
struct SimpleHealthCheck {}

impl HealthCheck for SimpleHealthCheck {
    fn check_health(&self, component: &ComponentInfo) -> HealthStatus {
        println!("检查组件健康状态: {}", component.name);
        HealthStatus::Healthy
    }
    
    fn get_details(&self, component: &ComponentInfo) -> HashMap<String, String> {
        let mut details = HashMap::new();
        details.insert("status".to_string(), "运行中".to_string());
        details.insert("uptime".to_string(), "120s".to_string());
        details
    }
}
```

## 结论与未来方向

### 系统演化与版本兼容性

在本文中，我们探讨了一个完整的分布式工作流系统的设计与实现，特别关注了系统在不停机条件下的演化能力。
通过引入类型理论和版本化数据结构，我们实现了一个可靠的演化框架，能够安全地升级系统并保持向后兼容性。

主要贡献包括：

1. **类型驱动设计**：利用Rust的类型系统确保状态转换的安全性和正确性。
2. **组合式架构**：通过小型、专注的组件构建复杂系统，提高可维护性和可扩展性。
3. **共变与逆变模式**：引入函数式编程的类型转换概念，实现安全的数据模型演化。
4. **无停机部署策略**：提供多种部署策略（蓝绿、金丝雀、滚动、影子），支持系统在持续运行中平滑升级。
5. **版本兼容性管理**：通过兼容性矩阵和迁移路径，确保不同版本间的互操作性。

### 应用场景与未来研究方向

该系统适用于需要高可用性和演化能力的企业级应用，特别是在以下场景：

1. **业务流程自动化**：支持不断变化的业务流程，无需停机即可更新流程定义。
2. **多租户SaaS平台**：在不影响部分租户的情况下，为其他租户提供新功能。
3. **关键任务系统**：需要持续可用并且定期更新的系统，如金融交易、医疗系统等。

未来研究方向包括：

1. **形式化验证**：进一步利用Rust类型系统和依赖类型理论，形式化证明系统演化的正确性。
2. **自适应演化**：研究基于运行时反馈的自动演化决策机制。
3. **跨语言兼容性**：扩展演化框架以支持多语言微服务环境。
4. **演化性能优化**：研究如何在保持兼容性的同时最小化性能损失。
5. **分布式类型理论**：探索分布式环境中类型安全的理论基础。

通过此架构，我们展示了现代软件系统如何在满足业务需求的同时，保持技术债务最小化并支持长期演化。
Rust语言的安全性和表达能力使其成为构建这类系统的理想选择。

### 系统架构图

```text
┌─────────────────────────────────────────────────────────────────┐
│                     分布式工作流系统架构                          │
├─────────────────┬─────────────────────────┬─────────────────────┤
│                 │                         │                     │
│   核心工作流引擎 │     零停机部署管理器      │   版本兼容性管理     │
│                 │                         │                     │
├─────────────────┴───────┬─────────────────┴─────────────────────┤
│                         │                                       │
│     类型安全转换层       │           系统演化代数                 │
│                         │                                       │
├─────────────────────────┴───────────────────────────────────────┤
│                                                                 │
│                       验证与监控系统                             │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

```text
<think>Let me analyze this query:

The user has asked me to respond in Chinese and wants me to discuss several advanced computer science topics:
1. Formal verification (形式化验证)
2. Adaptive evolution (自适应演化)
3. Distributed type theory (分布式类型理论)
4. Maintaining compatibility while minimizing performance loss (保持兼容性同时最小化性能损失)
5. Being able to integrate external open-source software stacks (能集成外部开源软件堆栈)

These seem to be requirements or focus areas for some kind of system or framework, though the user hasn't specified exactly what they're trying to build or understand. I'll provide an overview of these concepts and how they might interrelate in a modern software engineering context, responding entirely in Chinese as requested.</think># 软件系统核心技术点分析

## 1. 形式化验证

形式化验证是使用严格的数学方法证明软件系统正确性的技术。在现代软件开发中，这一领域变得越来越重要：

- **定理证明**：使用Coq、Isabelle/HOL等工具对关键算法进行形式化证明
- **模型检验**：通过TLA+、SPIN等工具验证并发系统的正确性
- **静态分析**：Rust的所有权系统、F*等依赖类型系统提供的内置验证能力

形式化验证可以显著降低关键系统的错误率，尤其适用于金融、医疗和安全关键领域。

## 2. 自适应演化

自适应演化指系统能够根据环境变化和需求调整自身行为：

- **在线学习算法**：系统在运行时收集数据并优化自身参数
- **自调优机制**：动态调整资源分配、缓存策略等配置参数
- **渐进式部署**：通过灰度发布和A/B测试验证新特性的有效性
- **自修复能力**：检测故障并进行自动恢复

这些技术使系统具备更强的鲁棒性和可持续性。

## 3. 分布式类型理论

分布式类型理论是类型理论在分布式系统中的应用和扩展：

- **会话类型**：形式化验证分布式通信协议的正确性
- **线性类型**：确保分布式资源的正确使用和释放
- **依赖类型**：在编译时验证复杂的不变量
- **渐进式类型系统**：允许静态和动态类型检查共存

这些理论基础可以帮助构建更可靠的分布式系统，减少并发错误。

## 4. 保持兼容性同时最小化性能损失

平衡兼容性和性能是系统设计的关键挑战：

- **向后兼容API设计**：精心设计接口，确保新版本不破坏现有客户端
- **性能分析与优化**：利用分析工具识别和解决性能瓶颈
- **异步与非阻塞模式**：减少资源等待时间
- **编译时优化**：使用LLVM等现代编译基础设施进行代码优化
- **实时系统监控**：持续评估性能指标并进行调整

## 5. 集成外部开源软件堆栈

有效集成开源组件可以加速开发并提高系统质量：

- **模块化架构**：通过明确定义的接口集成外部组件
- **依赖管理**：使用先进的包管理工具处理版本和冲突
- **适配器模式**：开发适配层以集成不同风格的API
- **容器化与微服务**：隔离外部依赖以减少集成风险
- **开源社区参与**：积极参与相关项目以确保长期维护

## 综合应用

这五个方面相互补充并强化：形式化验证可以证明分布式类型系统的正确性；自适应演化机制可以在保持兼容性的同时优化性能；而开源集成能力则可以利用已有的成熟解决方案加速开发。

结合这些技术点，可以构建出既安全可靠又灵活高效的现代软件系统，特别适合关键业务应用和大规模分布式环境。
```
