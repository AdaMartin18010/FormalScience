
# 计算系统进阶模型与架构设计

## 目录

- [计算系统进阶模型与架构设计](#计算系统进阶模型与架构设计)
  - [目录](#目录)
  - [思维导图](#思维导图)
  - [1. 自适应与学习模型](#1-自适应与学习模型)
    - [1.1 强化学习控制系统](#11-强化学习控制系统)
    - [1.2 在线学习与自适应](#12-在线学习与自适应)
    - [1.3 元学习框架](#13-元学习框架)
    - [1.4 智能系统架构](#14-智能系统架构)
  - [2. 形式化方法与验证](#2-形式化方法与验证)
    - [2.1 形式规范](#21-形式规范)
    - [2.2 模型检验](#22-模型检验)
    - [2.3 类型系统与静态分析](#23-类型系统与静态分析)
    - [2.4 定理证明](#24-定理证明)
  - [3. 实时与响应式系统](#3-实时与响应式系统)
    - [3.1 硬实时约束](#31-硬实时约束)
    - [3.2 软实时策略](#32-软实时策略)
    - [3.3 调度理论](#33-调度理论)
    - [3.4 响应式编程模型](#34-响应式编程模型)
  - [4. 分布式计算模型](#4-分布式计算模型)
    - [4.1 一致性模型](#41-一致性模型)
    - [4.2 共识算法](#42-共识算法)
    - [4.3 分布式事务框架](#43-分布式事务框架)
    - [4.4 分布式追踪系统](#44-分布式追踪系统)
    - [4.5 Gossip协议和失败检测](#45-gossip协议和失败检测)
    - [4.6 服务发现与负载均衡](#46-服务发现与负载均衡)
    - [4.7 分布式锁](#47-分布式锁)
    - [4.8 分布式工作队列](#48-分布式工作队列)
    - [4.9 批处理框架](#49-批处理框架)
    - [4.10 分布式状态机](#410-分布式状态机)
    - [4.11 分布式配置和服务发现](#411-分布式配置和服务发现)
    - [4.12 分布式缓存系统](#412-分布式缓存系统)

## 思维导图

```text
计算系统进阶模型与架构设计
├── 自适应与学习模型
│   ├── 强化学习控制系统
│   │   ├── 基于模型的强化学习
│   │   ├── 无模型强化学习
│   │   ├── 奖励函数设计
│   │   └── 探索与利用平衡
│   ├── 在线学习与自适应
│   │   ├── 增量学习算法
│   │   ├── 概念漂移处理
│   │   ├── 自适应特征选择
│   │   └── 动态模型更新
│   ├── 元学习框架
│   │   ├── 学习如何学习
│   │   ├── 少样本学习
│   │   ├── 迁移学习策略
│   │   └── 多任务学习
│   └── 智能系统架构
│       ├── 分层认知架构
│       ├── BDI代理模型
│       ├── 混合推理系统
│       └── 自主决策框架
│
├── 形式化方法与验证
│   ├── 形式规范
│   │   ├── 时态逻辑
│   │   ├── Z规范
│   │   ├── 契约设计
│   │   └── 状态机描述
│   ├── 模型检验
│   │   ├── 状态空间探索
│   │   ├── 反例生成
│   │   ├── 抽象与精化
│   │   └── 符号执行
│   ├── 类型系统与静态分析
│   │   ├── 依赖类型
│   │   ├── 线性类型
│   │   ├── 效果系统
│   │   └── 抽象解释
│   └── 定理证明
│       ├── 归纳证明
│       ├── 协同证明
│       ├── 不变式验证
│       └── 精化证明
│
├── 实时与响应式系统
│   ├── 硬实时约束
│   │   ├── 最坏执行时间分析
│   │   ├── 确定性执行
│   │   ├── 优先级反转避免
│   │   └── 资源预留
│   ├── 软实时策略
│   │   ├── 确定性缺失处理
│   │   ├── 质量退化模型
│   │   ├── 弹性时间管理
│   │   └── 最佳努力服务
│   ├── 调度理论
│   │   ├── 抢占式调度
│   │   ├── 非抢占式调度
│   │   ├── 速率单调调度
│   │   └── 最早截止期限优先
│   └── 响应式编程模型
│       ├── 事件驱动架构
│       ├── 数据流编程
│       ├── 流处理模型
│       └── 背压处理
│
├── 分布式计算模型
│   ├── 一致性模型
│   │   ├── 强一致性
│   │   ├── 最终一致性
│   │   ├── 因果一致性
│   │   └── 会话一致性
│   ├── 共识算法
│   │   ├── Paxos算法
│   │   ├── Raft算法
│   │   ├── PBFT算法
│   │   └── 区块链共识
│   ├── 拜占庭容错
│   │   ├── 拜占庭将军问题
│   │   ├── 容错算法
│   │   ├── 身份验证机制
│   │   └── 失效检测
│   └── 分区容忍性
│       ├── CAP定理
│       ├── 分区恢复策略
│       ├── 冲突解决
│       └── 数据同步
│
└── 异构计算架构
    ├── CPU-GPU协同计算
    │   ├── 并行任务分解
    │   ├── 内存访问优化
    │   ├── 异步执行模型
    │   └── 负载平衡
    ├── FPGA加速系统
    │   ├── 硬件描述语言
    │   ├── 高级综合工具
    │   ├── CPU-FPGA接口
    │   └── 可重配置逻辑
    ├── 专用加速器
    │   ├── 神经网络加速器
    │   ├── 密码学处理器
    │   ├── 视频编解码器
    │   └── 量子加速器
    └── 计算卸载策略
        ├── 卸载决策模型
        ├── 能耗优化
        ├── 延迟敏感处理
        └── 移动边缘计算
```

## 1. 自适应与学习模型

### 1.1 强化学习控制系统

强化学习控制系统通过交互与环境学习最优策略，适用于复杂的控制问题和决策过程。

```rust
// 强化学习控制器
struct RLController<S, A> {
    policy: Box<dyn Fn(&S) -> A>,
    value_function: Box<dyn Fn(&S) -> f64>,
    learning_rate: f64,
    discount_factor: f64,
    exploration_rate: f64,
    state_history: Vec<(S, A, f64, S)>, // (状态,动作,奖励,下一状态)
}

impl<S: Clone, A: Clone> RLController<S, A> {
    fn new(
        initial_policy: Box<dyn Fn(&S) -> A>,
        initial_value_function: Box<dyn Fn(&S) -> f64>,
        learning_rate: f64,
        discount_factor: f64,
        exploration_rate: f64,
    ) -> Self {
        RLController {
            policy: initial_policy,
            value_function: initial_value_function,
            learning_rate,
            discount_factor,
            exploration_rate,
            state_history: Vec::new(),
        }
    }
    
    fn select_action(&self, state: &S) -> A {
        // 探索vs利用
        if rand::random::<f64>() < self.exploration_rate {
            // 探索: 随机动作 (简化)
            self.random_action()
        } else {
            // 利用: 使用当前策略
            (self.policy)(state)
        }
    }
    
    fn random_action(&self) -> A {
        // 这是一个简化版本，实际中需要根据动作空间生成
        unimplemented!("需要根据具体动作空间实现")
    }
    
    fn update_from_experience(&mut self, state: S, action: A, reward: f64, next_state: S) {
        // 记录经验
        self.state_history.push((state.clone(), action, reward, next_state.clone()));
        
        // Q-learning更新逻辑 (简化版)
        let current_value = (self.value_function)(&state);
        let next_value = (self.value_function)(&next_state);
        
        // TD误差
        let td_error = reward + self.discount_factor * next_value - current_value;
        
        // 更新值函数 (简化，实际中需要更复杂的函数近似器)
        let new_value_function = Box::new(move |s: &S| {
            if s == &state {
                current_value + self.learning_rate * td_error
            } else {
                (self.value_function)(s)
            }
        });
        
        self.value_function = new_value_function;
        
        // 更新策略 (简化，实际中需要更复杂的策略更新)
        self.update_policy();
    }
    
    fn update_policy(&mut self) {
        // 简化的策略更新，实际中通常基于值函数派生策略
        // 例如，贪婪策略选择最大Q值的动作
    }
    
    fn batch_update(&mut self, batch_size: usize) {
        if self.state_history.len() < batch_size {
            return;
        }
        
        // 从经验中随机采样进行批量更新
        let mut rng = rand::thread_rng();
        let batch_indices: Vec<usize> = (0..self.state_history.len())
            .choose_multiple(&mut rng, batch_size)
            .collect();
        
        for &idx in &batch_indices {
            let (state, action, reward, next_state) = self.state_history[idx].clone();
            
            // 执行Q-learning更新 (简化)
            let current_value = (self.value_function)(&state);
            let next_value = (self.value_function)(&next_state);
            let td_error = reward + self.discount_factor * next_value - current_value;
            
            // 更新值函数
            // 注意: 这是一个简化实现，实际应用需要更复杂的函数近似
        }
    }
    
    fn decrease_exploration(&mut self, decay_rate: f64) {
        self.exploration_rate *= decay_rate;
        self.exploration_rate = self.exploration_rate.max(0.01); // 保持最小探索率
    }
}

// 基于模型的强化学习
struct ModelBasedRL<S, A> {
    model: Box<dyn Fn(&S, &A) -> (S, f64)>, // 环境模型: (状态,动作) -> (下一状态,奖励)
    planner: Box<dyn Fn(&Box<dyn Fn(&S, &A) -> (S, f64)>, &S) -> A>, // 使用模型规划最佳动作
    model_learning_rate: f64,
    observed_transitions: Vec<(S, A, S, f64)>, // (状态,动作,下一状态,奖励)
}

impl<S: Clone, A: Clone> ModelBasedRL<S, A> {
    fn new(
        initial_model: Box<dyn Fn(&S, &A) -> (S, f64)>,
        planner: Box<dyn Fn(&Box<dyn Fn(&S, &A) -> (S, f64)>, &S) -> A>,
        model_learning_rate: f64,
    ) -> Self {
        ModelBasedRL {
            model: initial_model,
            planner,
            model_learning_rate,
            observed_transitions: Vec::new(),
        }
    }
    
    fn act(&self, state: &S) -> A {
        // 使用当前模型和规划器选择动作
        (self.planner)(&self.model, state)
    }
    
    fn update_model(&mut self, state: S, action: A, next_state: S, reward: f64) {
        // 记录观察到的转换
        self.observed_transitions.push((state, action, next_state, reward));
        
        // 更新环境模型 (简化)
        // 实际应用中，这里应该使用更复杂的函数近似或概率模型
    }
    
    fn monte_carlo_planning(&self, state: &S, depth: usize, rollouts: usize) -> A {
        // 蒙特卡洛树搜索示例 (简化)
        let mut action_values = HashMap::new();
        
        // 为每个可能的动作评估值
        for action in self.possible_actions(state) {
            let mut total_reward = 0.0;
            
            for _ in 0..rollouts {
                total_reward += self.simulate_trajectory(state, &action, depth);
            }
            
            let avg_reward = total_reward / rollouts as f64;
            action_values.insert(action.clone(), avg_reward);
        }
        
        // 选择价值最高的动作
        action_values.into_iter()
            .max_by(|a, b| a.1.partial_cmp(&b.1).unwrap())
            .map(|(a, _)| a)
            .unwrap_or_else(|| self.default_action())
    }
    
    fn simulate_trajectory(&self, state: &S, initial_action: &A, depth: usize) -> f64 {
        // 使用当前模型模拟轨迹并返回累积奖励
        let mut current_state = state.clone();
        let mut cumulative_reward = 0.0;
        let mut discount = 1.0;
        
        // 执行初始动作
        let (next_state, reward) = (self.model)(&current_state, initial_action);
        current_state = next_state;
        cumulative_reward += reward;
        discount *= 0.95; // 折扣因子
        
        // 继续模拟直到指定深度
        for _ in 1..depth {
            let action = self.random_action();
            let (next_state, reward) = (self.model)(&current_state, &action);
            current_state = next_state;
            cumulative_reward += discount * reward;
            discount *= 0.95;
        }
        
        cumulative_reward
    }
    
    fn possible_actions(&self, state: &S) -> Vec<A> {
        // 返回当前状态下的可能动作
        // 简化版本，实际应用需根据具体问题定义
        unimplemented!("需要根据具体问题实现")
    }
    
    fn default_action(&self) -> A {
        // 返回默认动作
        unimplemented!("需要根据具体问题实现")
    }
    
    fn random_action(&self) -> A {
        // 返回随机动作
        unimplemented!("需要根据具体问题实现")
    }
}
```

### 1.2 在线学习与自适应

在线学习系统能够从持续的数据流中学习，并适应数据分布的变化。

```rust
// 在线学习框架
struct OnlineLearner<T, P> {
    model: Box<dyn OnlineModel<T, P>>,
    learning_rate: f64,
    regularization: f64,
    drift_detector: Option<Box<dyn ConceptDriftDetector<T>>>,
    performance_history: Vec<f64>,
}

trait OnlineModel<T, P> {
    fn predict(&self, features: &T) -> P;
    fn update(&mut self, features: &T, target: &P, learning_rate: f64);
    fn reset(&mut self);
    fn get_model_state(&self) -> Vec<f64>;
    fn set_model_state(&mut self, state: Vec<f64>);
}

trait ConceptDriftDetector<T> {
    fn add_sample(&mut self, prediction_error: f64, sample: &T);
    fn drift_detected(&self) -> bool;
    fn warning_detected(&self) -> bool;
    fn reset(&mut self);
}

impl<T, P: PartialEq> OnlineLearner<T, P> {
    fn new(
        model: Box<dyn OnlineModel<T, P>>,
        learning_rate: f64,
        regularization: f64,
        drift_detector: Option<Box<dyn ConceptDriftDetector<T>>>,
    ) -> Self {
        OnlineLearner {
            model,
            learning_rate,
            regularization,
            drift_detector,
            performance_history: Vec::new(),
        }
    }
    
    fn predict(&self, features: &T) -> P {
        self.model.predict(features)
    }
    
    fn learn(&mut self, features: &T, target: &P) {
        // 进行预测
        let prediction = self.model.predict(features);
        
        // 计算误差（简化，实际中需要根据任务类型定义）
        let error = self.calculate_error(&prediction, target);
        
        // 检测概念漂移
        if let Some(ref mut detector) = self.drift_detector {
            detector.add_sample(error, features);
            
            if detector.drift_detected() {
                println!("检测到概念漂移，重置模型");
                self.model.reset();
                detector.reset();
            } else if detector.warning_detected() {
                // 可以开始准备备用模型
                println!("概念漂移警告");
            }
        }
        
        // 更新模型
        self.model.update(features, target, self.learning_rate);
        
        // 记录性能
        self.performance_history.push(error);
    }
    
    fn calculate_error<U: PartialEq>(&self, prediction: &U, target: &U) -> f64 {
        // 简化的错误计算，实际应根据问题类型定义
        if prediction == target {
            0.0
        } else {
            1.0
        }
    }
    
    fn adapt_learning_rate(&mut self, window_size: usize) {
        if self.performance_history.len() < window_size {
            return;
        }
        
        // 计算最近性能
        let recent_performance: f64 = self.performance_history.iter()
            .rev()
            .take(window_size)
            .sum::<f64>() / window_size as f64;
        
        // 动态调整学习率
        if recent_performance < 0.1 {
            // 性能良好，减小学习率
            self.learning_rate *= 0.9;
        } else {
            // 性能不佳，增大学习率
            self.learning_rate *= 1.1;
        }
        
        // 限制学习率范围
        self.learning_rate = self.learning_rate.clamp(0.001, 1.0);
    }
    
    fn save_model_snapshot(&self) -> Vec<f64> {
        self.model.get_model_state()
    }
    
    fn restore_model_snapshot(&mut self, state: Vec<f64>) {
        self.model.set_model_state(state);
    }
}

// ADWIN概念漂移检测器
struct AdwinDriftDetector {
    window: VecDeque<f64>,
    delta: f64, // 置信度参数
    max_buckets: usize,
    min_clock: usize,
    min_window_length: usize,
    last_detection_time: usize,
    total_elements: usize,
}

impl AdwinDriftDetector {
    fn new(delta: f64) -> Self {
        AdwinDriftDetector {
            window: VecDeque::new(),
            delta,
            max_buckets: 5,
            min_clock: 32,
            min_window_length: 10,
            last_detection_time: 0,
            total_elements: 0,
        }
    }
}

impl<T> ConceptDriftDetector<T> for AdwinDriftDetector {
    fn add_sample(&mut self, prediction_error: f64, _sample: &T) {
        self.window.push_back(prediction_error);
        self.total_elements += 1;
        
        // 窗口过大时删除最旧的元素
        if self.window.len() > 20000 {
            self.window.pop_front();
        }
        
        // 检测漂移
        self.detect_drift();
    }
    
    fn drift_detected(&self) -> bool {
        // 如果最近检测到漂移
        self.total_elements - self.last_detection_time < 10
    }
    
    fn warning_detected(&self) -> bool {
        // 预警逻辑
        false
    }
    
    fn reset(&mut self) {
        self.window.clear();
        self.last_detection_time = self.total_elements;
    }
}

impl AdwinDriftDetector {
    fn detect_drift(&mut self) {
        if self.window.len() < self.min_window_length {
            return;
        }
        
        // 尝试各种可能的切割点
        for i in self.min_window_length..self.window.len() {
            let w0 = i;
            let w1 = self.window.len() - i;
            
            if w0 < self.min_window_length || w1 < self.min_window_length {
                continue;
            }
            
            // 计算两个子窗口的平均值
            let mean0: f64 = self.window.iter().take(w0).sum::<f64>() / w0 as f64;
            let mean1: f64 = self.window.iter().skip(w0).sum::<f64>() / w1 as f64;
            
            // 计算方差
            let n0 = w0 as f64;
            let n1 = w1 as f64;
            let n = n0 + n1;
            
            // 计算截断霍夫丁界
            let delta_prime = self.delta / ((self.window.len() as f64).ln());
            let epsilon = (2.0 / n * (self.delta_prime(delta_prime))).sqrt();
            
            // 检测漂移
            if (mean0 - mean1).abs() > epsilon {
                // 漂移检测
                self.last_detection_time = self.total_elements;
                
                // 移除旧数据
                for _ in 0..w0 {
                    self.window.pop_front();
                }
                
                break;
            }
        }
    }
    
    fn delta_prime(&self, delta: f64) -> f64 {
        // 计算修正的delta值
        -0.5 * (delta).ln()
    }
}
```

### 1.3 元学习框架

元学习（学习如何学习）框架能够从多个任务中学习通用知识，并快速适应新任务。

```rust
// 元学习框架
struct MetaLearningSystem<T, P> {
    meta_model: Box<dyn MetaModel<T, P>>,
    meta_optimizer: Box<dyn MetaOptimizer>,
    tasks: HashMap<String, Task<T, P>>,
    meta_batch_size: usize,
}

trait MetaModel<T, P> {
    fn initialize_model_for_task(&self) -> Box<dyn Model<T, P>>;
    fn adapt_model(&self, model: &mut Box<dyn Model<T, P>>, support_set: &[(T, P)], steps: usize);
    fn meta_update(&mut self, task_gradients: Vec<Vec<f64>>);
    fn get_parameters(&self) -> Vec<f64>;
    fn set_parameters(&mut self, parameters: Vec<f64>);
}

trait Model<T, P> {
    fn predict(&self, input: &T) -> P;
    fn get_parameters(&self) -> Vec<f64>;
    fn set_parameters(&mut self, parameters: Vec<f64>);
    fn compute_gradients(&self, inputs: &[T], targets: &[P]) -> Vec<f64>;
}

trait MetaOptimizer {
    fn optimize(&self, gradients: Vec<Vec<f64>>, current_parameters: Vec<f64>) -> Vec<f64>;
}

struct Task<T, P> {
    name: String,
    support_set: Vec<(T, P)>,
    query_set: Vec<(T, P)>,
}

impl<T: Clone, P: Clone> MetaLearningSystem<T, P> {
    fn new(
        meta_model: Box<dyn MetaModel<T, P>>,
        meta_optimizer: Box<dyn MetaOptimizer>,
        meta_batch_size: usize,
    ) -> Self {
        MetaLearningSystem {
            meta_model,
            meta_optimizer,
            tasks: HashMap::new(),
            meta_batch_size,
        }
    }
    
    fn add_task(&mut self, task: Task<T, P>) {
        self.tasks.insert(task.name.clone(), task);
    }
    
    fn meta_train(&mut self, epochs: usize) {
        for _ in 0..epochs {
            // 从任务池中随机采样任务进行元训练
            let task_names: Vec<String> = self.tasks.keys().cloned().collect();
            let mut task_gradients = Vec::new();
            
            // 为每个任务计算梯度
            for task_name in task_names.iter().take(self.meta_batch_size) {
                if let Some(task) = self.tasks.get(task_name) {
                    // 为当前任务初始化模型
                    let mut model = self.meta_model.initialize_model_for_task();
                    
                    // 使用支持集适应模型
                    self.meta_model.adapt_model(&mut model, &task.support_set, 5);
                    
                    // 使用查询集计算梯度
                    let inputs: Vec<T> = task.query_set.iter().map(|(x, _)| x.clone()).collect();
                    let targets: Vec<P> = task.query_set.iter().map(|(_, y)| y.clone()).collect();
                    
                    let gradients = model.compute_gradients(&inputs, &targets);
                    task_gradients.push(gradients);
                }
            }
            
            // 元更新
            self.meta_model.meta_update(task_gradients);
        }
    }
    
    fn adapt_to_new_task(&self, support_set: &[(T, P)], adaptation_steps: usize) -> Box<dyn Model<T, P>> {
        // 初始化模型
        let mut model = self.meta_model.initialize_model_for_task();
        
        // 使用支持集适应模型
        self.meta_model.adapt_model(&mut model, support_set, adaptation_steps);
        
        model
    }
    
    fn evaluate_on_task(&self, task_name: &str) -> f64 {
        if let Some(task) = self.tasks.get(task_name) {
            // 初始化模型
            let mut model = self.meta_model.initialize_model_for_task();
            
            // 使用支持集适应模型
            self.meta_model.adapt_model(&mut model, &task.support_set, 5);
            
            // 评估查询集性能
            let mut correct = 0;
            for (input, target) in &task.query_set {
                let prediction = model.predict(input);
                if self.is_correct(&prediction, target) {
                    correct += 1;
                }
            }
            
            correct as f64 / task.query_set.len() as f64
        } else {
            0.0
        }
    }
    
    fn is_correct(&self, prediction: &P, target: &P) -> bool {
        // 简化的正确性检查，实际实现取决于问题类型
        prediction == target
    }
    
    fn save_meta_model(&self, path: &str) -> Result<(), String> {
        // 保存元模型参数
        let parameters = self.meta_model.get_parameters();
        
        // 序列化和保存 (简化)
        println!("保存元模型到 {} (参数数量: {})", path, parameters.len());
        Ok(())
    }
    
    fn load_meta_model(&mut self, path: &str) -> Result<(), String> {
        // 加载元模型参数 (简化)
        println!("从 {} 加载元模型", path);
        
        // 模拟加载参数
        let parameters = vec![0.0; 100]; // 示例
        self.meta_model.set_parameters(parameters);
        
        Ok(())
    }
}

// MAML (Model-Agnostic Meta-Learning) 实现示例
struct MAMLMetaModel<T, P> {
    parameters: Vec<f64>,
    model_architecture: ModelArchitecture,
    inner_learning_rate: f64,
    meta_learning_rate: f64,
}

enum ModelArchitecture {
    LinearModel { input_dim: usize, output_dim: usize },
    NeuralNetwork { layers: Vec<usize> },
}

impl<T: Clone, P: Clone> MAMLMetaModel<T, P> {
    fn new(
        model_architecture: ModelArchitecture,
        inner_learning_rate: f64,
        meta_learning_rate: f64,
    ) -> Self {
        // 初始化参数
        let param_count = match &model_architecture {
            ModelArchitecture::LinearModel { input_dim, output_dim } => {
                input_dim * output_dim + output_dim // 权重 + 偏置
            },
            ModelArchitecture::NeuralNetwork { layers } => {
                let mut count = 0;
                for i in 0..layers.len()-1 {
                    count += layers[i] * layers[i+1] + layers[i+1]; // 权重 + 偏置
                }
                count
            }
        };
        
        MAMLMetaModel {
            parameters: vec![0.0; param_count], // 初始化为零或随机值
            model_architecture,
            inner_learning_rate,
            meta_learning_rate,
        }
    }
}

impl<T, P> MetaModel<T, P> for MAMLMetaModel<T, P> 
where T: 'static + Clone, P: 'static + Clone
{
    fn initialize_model_for_task(&self) -> Box<dyn Model<T, P>> {
        // 创建新模型并使用当前元参数初始化
        match &self.model_architecture {
            ModelArchitecture::LinearModel { input_dim, output_dim } => {
                // 创建线性模型并初始化
                Box::new(LinearModel::<T, P>::new(*input_dim, *output_dim, self.parameters.clone()))
            },
            ModelArchitecture::NeuralNetwork { layers } => {
                // 创建神经网络并初始化
                // 这里简化处理
                Box::new(LinearModel::<T, P>::new(layers[0], layers.last().unwrap(), self.parameters.clone()))
            }
        }
    }
    
    fn adapt_model(&self, model: &mut Box<dyn Model<T, P>>, support_set: &[(T, P)], steps: usize) {
        // 使用支持集进行快速适应
        let inputs: Vec<T> = support_set.iter().map(|(x, _)| x.clone()).collect();
        let targets: Vec<P> = support_set.iter().map(|(_, y)| y.clone()).collect();
        
        for _ in 0..steps {
            // 计算梯度
            let gradients = model.compute_gradients(&inputs, &targets);
            
            // 获取当前参数
            let mut parameters = model.get_parameters();
            
            // 应用梯度下降
            for i in 0..parameters.len() {
                parameters[i] -= self.inner_learning_rate * gradients[i];
            }
            
            // 更新模型参数
            model.set_parameters(parameters);
        }
    }
    
    fn meta_update(&mut self, task_gradients: Vec<Vec<f64>>) {
        if task_gradients.is_empty() {
            return;
        }
        
        // 计算平均梯度
        let mut avg_gradients = vec![0.0; self.parameters.len()];
        
        for gradients in &task_gradients {
            for i in 0..self.parameters.len() {
                avg_gradients[i] += gradients[i] / task_gradients.len() as f64;
            }
        }
        
        // 应用元优化器更新
        for i in 0..self.parameters.len() {
            self.parameters[i] -= self.meta_learning_rate * avg_gradients[i];
        }
    }
    
    fn get_parameters(&self) -> Vec<f64> {
        self.parameters.clone()
    }
    
    fn set_parameters(&mut self, parameters: Vec<f64>) {
        assert_eq!(self.parameters.len(), parameters.len(), "参数维度不匹配");
        self.parameters = parameters;
    }
}

// 简化的线性模型实现
struct LinearModel<T, P> {
    input_dim: usize,
    output_dim: usize,
    weights: Vec<f64>,
    _phantom: PhantomData<(T, P)>,
}

impl<T, P> LinearModel<T, P> {
    fn new(input_dim: usize, output_dim: usize, parameters: Vec<f64>) -> Self {
        LinearModel {
            input_dim,
            output_dim,
            weights: parameters,
            _phantom: PhantomData,
        }
    }
}

impl<T, P> Model<T, P> for LinearModel<T, P> {
    fn predict(&self, input: &T) -> P {
        // 简化实现，实际应该根据T和P类型进行正确的线性变换
        unimplemented!("需要根据具体类型实现预测逻辑")
    }
    
    fn get_parameters(&self) -> Vec<f64> {
        self.weights.clone()
    }
    
    fn set_parameters(&mut self, parameters: Vec<f64>) {
        assert_eq!(self.weights.len(), parameters.len(), "参数维度不匹配");
        self.weights = parameters;
    }
    
    fn compute_gradients(&self, inputs: &[T], targets: &[P]) -> Vec<f64> {
        // 简化实现，实际应该计算损失函数对参数的梯度
        vec![0.0; self.weights.len()]
    }
}
```

### 1.4 智能系统架构

智能系统架构整合了感知、推理、学习和行动的能力，形成具有自主性和适应性的系统。

```rust
// 分层认知架构
struct CognitiveArchitecture {
    perception_layer: PerceptionLayer,
    reasoning_layer: ReasoningLayer,
    planning_layer: PlanningLayer,
    execution_layer: ExecutionLayer,
    memory: SharedMemory,
}

struct PerceptionLayer {
    sensors: Vec<Box<dyn Sensor>>,
    feature_extractors: Vec<Box<dyn FeatureExtractor>>,
    attention_mechanism: Box<dyn AttentionMechanism>,
}

struct ReasoningLayer {
    inference

```rust
struct ReasoningLayer {
    inference_engine: Box<dyn InferenceEngine>,
    knowledge_base: Box<dyn KnowledgeBase>,
    uncertainty_model: Box<dyn UncertaintyModel>,
}

struct PlanningLayer {
    goal_manager: GoalManager,
    planner: Box<dyn Planner>,
    action_selector: ActionSelector,
}

struct ExecutionLayer {
    action_controllers: HashMap<String, Box<dyn ActionController>>,
    execution_monitor: ExecutionMonitor,
    feedback_processor: FeedbackProcessor,
}

struct SharedMemory {
    working_memory: HashMap<String, Box<dyn Any>>,
    episodic_memory: Vec<Episode>,
    semantic_memory: SemanticNetwork,
    procedural_memory: Vec<Procedure>,
}

// 基本特性和接口
trait Sensor {
    fn get_reading(&self) -> SensorData;
    fn get_type(&self) -> String;
}

trait FeatureExtractor {
    fn extract_features(&self, data: &SensorData) -> Features;
}

trait AttentionMechanism {
    fn focus_attention(&self, features: &[Features]) -> Vec<Features>;
    fn update_saliency(&mut self, feedback: &AttentionalFeedback);
}

trait InferenceEngine {
    fn infer(&self, facts: &[Fact], rules: &[Rule]) -> Vec<Fact>;
    fn explain(&self, conclusion: &Fact) -> Vec<InferenceStep>;
}

trait KnowledgeBase {
    fn query(&self, query: &Query) -> Vec<Fact>;
    fn add_fact(&mut self, fact: Fact);
    fn add_rule(&mut self, rule: Rule);
}

trait UncertaintyModel {
    fn update_belief(&mut self, evidence: &Evidence);
    fn get_belief(&self, proposition: &Proposition) -> f64;
}

trait Planner {
    fn generate_plan(&self, initial_state: &State, goal: &Goal) -> Option<Plan>;
    fn repair_plan(&self, current_plan: &Plan, current_state: &State) -> Option<Plan>;
}

// 数据结构
struct SensorData {
    timestamp: Instant,
    sensor_type: String,
    data: Vec<f64>,
    metadata: HashMap<String, String>,
}

struct Features {
    feature_type: String,
    values: Vec<f64>,
    source_sensor: String,
    confidence: f64,
}

struct AttentionalFeedback {
    feature_id: usize,
    importance: f64,
    context: HashMap<String, f64>,
}

struct Fact {
    statement: String,
    confidence: f64,
    source: String,
    timestamp: Instant,
}

struct Rule {
    conditions: Vec<String>,
    consequences: Vec<String>,
    certainty_factor: f64,
}

struct Query {
    pattern: String,
    constraints: Vec<String>,
}

struct Evidence {
    source: String,
    reliability: f64,
    observations: HashMap<String, f64>,
}

struct Proposition {
    statement: String,
    variables: HashMap<String, String>,
}

struct State {
    variables: HashMap<String, Value>,
    timestamp: Instant,
}

struct Goal {
    conditions: HashMap<String, Value>,
    priority: usize,
    deadline: Option<Instant>,
}

struct Plan {
    actions: Vec<Action>,
    expected_states: Vec<State>,
    total_cost: f64,
    expected_duration: Duration,
}

struct Action {
    name: String,
    parameters: HashMap<String, Value>,
    preconditions: Vec<Condition>,
    effects: Vec<Effect>,
    duration: Duration,
}

struct GoalManager {
    active_goals: Vec<Goal>,
    goal_priorities: HashMap<String, usize>,
    conflict_resolver: Box<dyn ConflictResolver>,
}

struct ActionSelector {
    utility_function: Box<dyn Fn(&Action, &State) -> f64>,
    decision_threshold: f64,
}

struct ExecutionMonitor {
    expected_states: HashMap<Instant, State>,
    tolerance_thresholds: HashMap<String, f64>,
    failure_handlers: HashMap<String, Box<dyn FailureHandler>>,
}

struct FeedbackProcessor {
    feedback_sources: Vec<String>,
    reward_model: Box<dyn RewardModel>,
    adaptation_mechanism: Box<dyn AdaptationMechanism>,
}

struct Episode {
    start_time: Instant,
    end_time: Instant,
    initial_state: State,
    goal: Goal,
    actions_taken: Vec<Action>,
    outcome: Outcome,
    feedback: Vec<Feedback>,
}

struct SemanticNetwork {
    concepts: HashMap<String, Concept>,
    relations: Vec<Relation>,
}

struct Concept {
    id: String,
    properties: HashMap<String, Value>,
    instances: Vec<String>,
    parent_concepts: Vec<String>,
}

struct Relation {
    source: String,
    relation_type: String,
    target: String,
    weight: f64,
}

struct Procedure {
    name: String,
    trigger_conditions: Vec<Condition>,
    steps: Vec<ProcedureStep>,
    success_rate: f64,
}

struct ProcedureStep {
    action: Action,
    next_steps: HashMap<Outcome, usize>,
}

enum Value {
    Boolean(bool),
    Integer(i64),
    Float(f64),
    Text(String),
    List(Vec<Value>),
}

struct Condition {
    variable: String,
    operator: ConditionOperator,
    value: Value,
}

enum ConditionOperator {
    Equals,
    NotEquals,
    GreaterThan,
    LessThan,
    Contains,
}

struct Effect {
    variable: String,
    operation: EffectOperation,
    value: Value,
}

enum EffectOperation {
    Set,
    Add,
    Subtract,
    Multiply,
    Divide,
}

enum Outcome {
    Success,
    Failure(String),
    PartialSuccess(f64),
}

struct Feedback {
    source: String,
    value: f64,
    aspects: HashMap<String, f64>,
}

// BDI (信念-欲望-意图) 代理模型
struct BDIAgent {
    beliefs: BeliefBase,
    desires: Vec<Desire>,
    intentions: Vec<Intention>,
    plan_library: PlanLibrary,
    reasoner: Box<dyn BDIReasoner>,
}

struct BeliefBase {
    facts: HashMap<String, Fact>,
    rules: Vec<Rule>,
    belief_revision_strategy: Box<dyn BeliefRevisionStrategy>,
}

struct Desire {
    goal: Goal,
    importance: f64,
    urgency: f64,
    context_condition: Option<Box<dyn Fn(&BeliefBase) -> bool>>,
}

struct Intention {
    desire: Desire,
    plan: Plan,
    commitment_strategy: CommitmentStrategy,
    progress: f64,
    last_updated: Instant,
}

struct PlanLibrary {
    plans: HashMap<String, Vec<Plan>>,
    applicability_conditions: HashMap<String, Box<dyn Fn(&BeliefBase, &Goal) -> bool>>,
}

trait BDIReasoner {
    fn update_beliefs(&mut self, agent: &mut BDIAgent, percepts: &[Percept]);
    fn generate_options(&self, agent: &BDIAgent) -> Vec<Desire>;
    fn filter_options(&self, agent: &BDIAgent, options: &[Desire]) -> Vec<Desire>;
    fn select_intentions(&self, agent: &BDIAgent, filtered_options: &[Desire]) -> Vec<Intention>;
    fn execute_intentions(&self, agent: &mut BDIAgent);
}

trait BeliefRevisionStrategy {
    fn revise(&self, current_beliefs: &mut HashMap<String, Fact>, new_evidence: &[Fact]);
}

enum CommitmentStrategy {
    BlindCommitment,
    OpenMindedCommitment,
    SingleMindedCommitment,
}

struct Percept {
    source: String,
    content: HashMap<String, Value>,
    reliability: f64,
}

impl BDIAgent {
    fn new(
        reasoner: Box<dyn BDIReasoner>,
        belief_revision_strategy: Box<dyn BeliefRevisionStrategy>,
    ) -> Self {
        BDIAgent {
            beliefs: BeliefBase {
                facts: HashMap::new(),
                rules: Vec::new(),
                belief_revision_strategy,
            },
            desires: Vec::new(),
            intentions: Vec::new(),
            plan_library: PlanLibrary {
                plans: HashMap::new(),
                applicability_conditions: HashMap::new(),
            },
            reasoner,
        }
    }
    
    fn perceive(&mut self, percepts: Vec<Percept>) {
        self.reasoner.update_beliefs(self, &percepts);
    }
    
    fn deliberate(&mut self) {
        let options = self.reasoner.generate_options(self);
        let filtered_options = self.reasoner.filter_options(self, &options);
        let new_intentions = self.reasoner.select_intentions(self, &filtered_options);
        
        for intention in new_intentions {
            self.intentions.push(intention);
        }
    }
    
    fn execute(&mut self) {
        self.reasoner.execute_intentions(self);
    }
    
    fn run_bdi_cycle(&mut self, percepts: Vec<Percept>) {
        self.perceive(percepts);
        self.deliberate();
        self.execute();
    }
    
    fn add_plan(&mut self, goal_type: &str, plan: Plan, 
                applicability: Box<dyn Fn(&BeliefBase, &Goal) -> bool>) {
        self.plan_library.plans.entry(goal_type.to_string())
            .or_insert_with(Vec::new)
            .push(plan);
        
        self.plan_library.applicability_conditions.insert(
            goal_type.to_string(),
            applicability
        );
    }
    
    fn add_desire(&mut self, desire: Desire) {
        self.desires.push(desire);
    }
    
    fn drop_intention(&mut self, index: usize) {
        if index < self.intentions.len() {
            self.intentions.remove(index);
        }
    }
}

// 混合推理系统
struct HybridReasoningSystem {
    rule_based_component: RuleBasedReasoner,
    case_based_component: CaseBasedReasoner,
    statistical_component: StatisticalReasoner,
    fusion_strategy: Box<dyn ReasoningFusionStrategy>,
}

struct RuleBasedReasoner {
    rules: Vec<Rule>,
    inference_engine: Box<dyn InferenceEngine>,
}

struct CaseBasedReasoner {
    case_library: Vec<Case>,
    similarity_measure: Box<dyn Fn(&Case, &Problem) -> f64>,
    adaptation_strategy: Box<dyn CaseAdaptationStrategy>,
}

struct StatisticalReasoner {
    model: Box<dyn ProbabilisticModel>,
    inference_method: StatisticalInferenceMethod,
}

struct Case {
    problem: Problem,
    solution: Solution,
    outcome: Outcome,
    adaptations: Vec<Adaptation>,
}

struct Problem {
    features: HashMap<String, Value>,
    constraints: Vec<Constraint>,
}

struct Solution {
    actions: Vec<Action>,
    resources: HashMap<String, f64>,
    expected_outcome: Outcome,
}

struct Adaptation {
    modified_features: HashMap<String, (Value, Value)>, // (old, new)
    modified_solution: HashMap<String, (Value, Value)>, // (old, new)
    success_rate: f64,
}

struct Constraint {
    feature: String,
    operator: ConstraintOperator,
    value: Value,
}

enum ConstraintOperator {
    MustEqual,
    MustNotEqual,
    MustBeLessThan,
    MustBeGreaterThan,
    MustBeInRange(Value, Value),
}

trait ReasoningFusionStrategy {
    fn fuse_results(
        &self,
        rule_based_result: Option<Vec<Fact>>,
        case_based_result: Option<Solution>,
        statistical_result: Option<HashMap<String, f64>>,
    ) -> ReasoningResult;
}

trait CaseAdaptationStrategy {
    fn adapt_case(&self, case: &Case, problem: &Problem) -> Solution;
}

trait ProbabilisticModel {
    fn infer(&self, evidence: &HashMap<String, Value>) -> HashMap<String, f64>;
    fn update(&mut self, data: &[(HashMap<String, Value>, HashMap<String, Value>)]);
}

enum StatisticalInferenceMethod {
    MonteCarlo { samples: usize },
    VariationalInference,
    ExpectationMaximization,
    MCMC { iterations: usize, burnin: usize },
}

struct ReasoningResult {
    facts: Vec<Fact>,
    actions: Vec<Action>,
    probabilities: HashMap<String, f64>,
    confidence: f64,
    explanation: String,
}

impl HybridReasoningSystem {
    fn new(
        rules: Vec<Rule>,
        inference_engine: Box<dyn InferenceEngine>,
        cases: Vec<Case>,
        similarity_measure: Box<dyn Fn(&Case, &Problem) -> f64>,
        adaptation_strategy: Box<dyn CaseAdaptationStrategy>,
        probabilistic_model: Box<dyn ProbabilisticModel>,
        inference_method: StatisticalInferenceMethod,
        fusion_strategy: Box<dyn ReasoningFusionStrategy>,
    ) -> Self {
        HybridReasoningSystem {
            rule_based_component: RuleBasedReasoner {
                rules,
                inference_engine,
            },
            case_based_component: CaseBasedReasoner {
                case_library: cases,
                similarity_measure,
                adaptation_strategy,
            },
            statistical_component: StatisticalReasoner {
                model: probabilistic_model,
                inference_method,
            },
            fusion_strategy,
        }
    }
    
    fn reason(&self, facts: &[Fact], problem: &Problem, evidence: &HashMap<String, Value>) -> ReasoningResult {
        // 使用规则推理
        let rule_result = self.rule_based_reasoning(facts);
        
        // 使用案例推理
        let case_result = self.case_based_reasoning(problem);
        
        // 使用统计推理
        let statistical_result = self.statistical_reasoning(evidence);
        
        // 融合结果
        self.fusion_strategy.fuse_results(rule_result, case_result, statistical_result)
    }
    
    fn rule_based_reasoning(&self, facts: &[Fact]) -> Option<Vec<Fact>> {
        Some(self.rule_based_component.inference_engine.infer(facts, &self.rule_based_component.rules))
    }
    
    fn case_based_reasoning(&self, problem: &Problem) -> Option<Solution> {
        if self.case_based_component.case_library.is_empty() {
            return None;
        }
        
        // 找到最相似的案例
        let mut best_case = &self.case_based_component.case_library[0];
        let mut best_similarity = (self.case_based_component.similarity_measure)(best_case, problem);
        
        for case in &self.case_based_component.case_library[1..] {
            let similarity = (self.case_based_component.similarity_measure)(case, problem);
            if similarity > best_similarity {
                best_similarity = similarity;
                best_case = case;
            }
        }
        
        // 如果相似度太低，返回None
        if best_similarity < 0.5 {
            return None;
        }
        
        // 调整案例以适应当前问题
        Some(self.case_based_component.adaptation_strategy.adapt_case(best_case, problem))
    }
    
    fn statistical_reasoning(&self, evidence: &HashMap<String, Value>) -> Option<HashMap<String, f64>> {
        Some(self.statistical_component.model.infer(evidence))
    }
    
    fn add_rule(&mut self, rule: Rule) {
        self.rule_based_component.rules.push(rule);
    }
    
    fn add_case(&mut self, case: Case) {
        self.case_based_component.case_library.push(case);
    }
    
    fn update_statistical_model(&mut self, data: &[(HashMap<String, Value>, HashMap<String, Value>)]) {
        self.statistical_component.model.update(data);
    }
}
```

## 2. 形式化方法与验证

### 2.1 形式规范

形式规范使用严格的数学符号和逻辑来精确地描述系统的预期行为，避免歧义。

```rust
// 形式规范框架
struct FormalSpecification {
    entities: HashMap<String, Entity>,
    state_variables: HashMap<String, StateVariable>,
    invariants: Vec<Invariant>,
    pre_post_conditions: HashMap<String, (Predicate, Predicate)>,
    temporal_properties: Vec<TemporalProperty>,
}

struct Entity {
    name: String,
    attributes: HashMap<String, Type>,
    operations: Vec<Operation>,
}

struct StateVariable {
    name: String,
    data_type: Type,
    initial_value: Option<Value>,
    constraints: Vec<Constraint>,
}

struct Invariant {
    name: String,
    predicate: Predicate,
    scope: Vec<String>, // 相关状态变量
}

struct Operation {
    name: String,
    parameters: Vec<(String, Type)>,
    return_type: Option<Type>,
    precondition: Option<Predicate>,
    postcondition: Option<Predicate>,
}

enum Type {
    Boolean,
    Integer { min: Option<i64>, max: Option<i64> },
    Real { min: Option<f64>, max: Option<f64> },
    Set(Box<Type>),
    Sequence(Box<Type>),
    Enumeration(Vec<String>),
    Record(HashMap<String, Type>),
}

enum Predicate {
    True,
    False,
    Equal(Box<Expression>, Box<Expression>),
    NotEqual(Box<Expression>, Box<Expression>),
    LessThan(Box<Expression>, Box<Expression>),
    GreaterThan(Box<Expression>, Box<Expression>),
    And(Vec<Predicate>),
    Or(Vec<Predicate>),
    Not(Box<Predicate>),
    Implies(Box<Predicate>, Box<Predicate>),
    ForAll { var: String, domain: Box<Expression>, body: Box<Predicate> },
    Exists { var: String, domain: Box<Expression>, body: Box<Predicate> },
}

enum Expression {
    Literal(Value),
    Variable(String),
    FunctionCall { name: String, args: Vec<Expression> },
    BinaryOp { op: BinaryOperator, left: Box<Expression>, right: Box<Expression> },
    UnaryOp { op: UnaryOperator, expr: Box<Expression> },
    SetComprehension { var: String, domain: Box<Expression>, condition: Box<Predicate> },
    IfThenElse { condition: Box<Predicate>, then_expr: Box<Expression>, else_expr: Box<Expression> },
}

enum BinaryOperator {
    Add, Subtract, Multiply, Divide, Modulo,
    Union, Intersection, Difference,
    Concatenate,
}

enum UnaryOperator {
    Negate, Cardinality, Length,
}

enum TemporalProperty {
    Always(Box<Predicate>),
    Eventually(Box<Predicate>),
    Until(Box<Predicate>, Box<Predicate>),
    Next(Box<Predicate>),
    Leads { from: Box<Predicate>, to: Box<Predicate> },
}

impl FormalSpecification {
    fn new() -> Self {
        FormalSpecification {
            entities: HashMap::new(),
            state_variables: HashMap::new(),
            invariants: Vec::new(),
            pre_post_conditions: HashMap::new(),
            temporal_properties: Vec::new(),
        }
    }
    
    fn add_entity(&mut self, entity: Entity) {
        self.entities.insert(entity.name.clone(), entity);
    }
    
    fn add_state_variable(&mut self, variable: StateVariable) {
        self.state_variables.insert(variable.name.clone(), variable);
    }
    
    fn add_invariant(&mut self, invariant: Invariant) {
        self.invariants.push(invariant);
    }
    
    fn add_operation_specification(&mut self, 
                                  operation_name: &str, 
                                  precondition: Predicate, 
                                  postcondition: Predicate) {
        self.pre_post_conditions.insert(
            operation_name.to_string(), 
            (precondition, postcondition)
        );
    }
    
    fn add_temporal_property(&mut self, property: TemporalProperty) {
        self.temporal_properties.push(property);
    }
    
    fn verify_against_model(&self, model: &SystemModel) -> VerificationResult {
        // 在实际实现中，这会调用模型检验器或定理证明器
        // 这里只是简化示例
        let mut violations = Vec::new();
        
        // 检查所有状态变量是否在模型中有对应
        for (name, var) in &self.state_variables {
            if !model.has_state_variable(name) {
                violations.push(Violation::MissingStateVariable(name.clone()));
            }
        }
        
        // 检查所有操作是否在模型中有对应
        for (name, _) in &self.pre_post_conditions {
            if !model.has_operation(name) {
                violations.push(Violation::MissingOperation(name.clone()));
            }
        }
        
        // 其他更复杂的检查...
        
        if violations.is_empty() {
            VerificationResult::Success
        } else {
            VerificationResult::Failure(violations)
        }
    }
}

struct SystemModel {
    state_variables: HashMap<String, Type>,
    operations: HashMap<String, OperationModel>,
    transitions: Vec<Transition>,
}

struct OperationModel {
    name: String,
    effect: Box<dyn Fn(&mut HashMap<String, Value>)>,
}

struct Transition {
    from_state: HashMap<String, Value>,
    operation: String,
    parameters: HashMap<String, Value>,
    to_state: HashMap<String, Value>,
}

impl SystemModel {
    fn has_state_variable(&self, name: &str) -> bool {
        self.state_variables.contains_key(name)
    }
    
    fn has_operation(&self, name: &str) -> bool {
        self.operations.contains_key(name)
    }
}

enum VerificationResult {
    Success,
    Failure(Vec<Violation>),
}

enum Violation {
    MissingStateVariable(String),
    MissingOperation(String),
    InvariantViolation(String, HashMap<String, Value>),
    PreconditionViolation(String, HashMap<String, Value>),
    PostconditionViolation(String, HashMap<String, Value>, HashMap<String, Value>),
    TemporalPropertyViolation(usize, Vec<HashMap<String, Value>>),
}
```

### 2.2 模型检验

模型检验系统地探索状态空间，验证系统是否满足特定属性，并在发现违反时提供反例。

```rust
// 模型检验框架
struct ModelChecker {
    model: TransitionSystem,
    properties: Vec<Property>,
    exploration_strategy: ExplorationStrategy,
    state_storage: StateStorage,
    optimization_techniques: Vec<OptimizationTechnique>,
}

struct TransitionSystem {
    states: HashSet<State>,
    initial_states: HashSet<State>,
    transitions: HashMap<State, Vec<(Action, State)>>,
    atomic_propositions: HashSet<String>,
    labeling: HashMap<State, HashSet<String>>,
}

struct State {
    id: usize,
    variables: HashMap<String, Value>,
}

struct Action {
    name: String,
    parameters: HashMap<String, Value>,
}

enum Property {
    Safety(Predicate),
    Liveness(Predicate),
    Fairness { strong: bool, condition: Predicate, consequence: Predicate },
    CTL(CTLFormula),
    LTL(LTLFormula),
}

enum CTLFormula {
    Atom(String),
    Not(Box<CTLFormula>),
    And(Box<CTLFormula>, Box<CTLFormula>),
    Or(Box<CTLFormula>, Box<CTLFormula>),
    Implies(Box<CTLFormula>, Box<CTLFormula>),
    AX(Box<CTLFormula>),  // 所有下一状态
    EX(Box<CTLFormula>),  // 存在下一状态
    AG(Box<CTLFormula>),  // 所有路径总是
    EG(Box<CTLFormula>),  // 存在路径总是
    AF(Box<CTLFormula>),  // 所有路径最终
    EF(Box<CTLFormula>),  // 存在路径最终
    AU(Box<CTLFormula>, Box<CTLFormula>),  // 所有路径直到
    EU(Box<CTLFormula>, Box<CTLFormula>),  // 存在路径直到
}

enum LTLFormula {
    Atom(String),
    Not(Box<LTLFormula>),
    And(Box<LTLFormula>, Box<LTLFormula>),
    Or(Box<LTLFormula>, Box<LTLFormula>),
    Implies(Box<LTLFormula>, Box<LTLFormula>),
    Next(Box<LTLFormula>),
    Always(Box<LTLFormula>),
    Eventually(Box<LTLFormula>),
    Until(Box<LTLFormula>, Box<LTLFormula>),
    Release(Box<LTLFormula>, Box<LTLFormula>),
}

enum ExplorationStrategy {
    DepthFirst { max_depth: Option<usize> },
    BreadthFirst,
    RandomWalk { steps: usize, runs: usize },
    GuidedSearch { heuristic: Box<dyn Fn(&State, &Property) -> f64> },
}

enum StateStorage {
    Explicit { max_states: Option<usize> },
    Symbolic { variables: Vec<String> },
    Hybrid { explicit_threshold: usize },
}

enum OptimizationTechnique {
    PartialOrderReduction,
    Symmetry { equivalence_relation: Box<dyn Fn(&State, &State) -> bool> },
    Abstraction { abstraction_function: Box<dyn Fn(&State) -> State> },
    Slicing { relevant_variables: HashSet<String> },
}

struct CounterExample {
    property_index: usize,
    path: Vec<(State, Action)>,
}

impl ModelChecker {
    fn new(model: TransitionSystem, strategy: ExplorationStrategy, storage: StateStorage) -> Self {
        ModelChecker {
            model,
            properties: Vec::new(),
            exploration_strategy: strategy,
            state_storage: storage,
            optimization_techniques: Vec::new(),
        }
    }
    
    fn add_property(&mut self, property: Property) {
        self.properties.push(property);
    }
    
    fn add_optimization(&mut self, technique: OptimizationTechnique) {
        self.optimization_techniques.push(technique);
    }
    
    fn check(&self) -> Vec<CheckResult> {
        let mut results = Vec::new();
        
        for (index, property) in self.properties.iter().enumerate() {
            match property {
                Property::Safety(predicate) => {
                    results.push(self.check_safety(index, predicate));
                },
                Property::Liveness(predicate) => {
                    results.push(self.check_liveness(index, predicate));
                },
                Property::CTL(formula) => {
                    results.push(self.check_ctl(index, formula));
                },
                Property::LTL(formula) => {
                    results.push(self.check_ltl(index, formula));
                },
                Property::Fairness { strong, condition, consequence } => {
                    results.push(self.check_fairness(index, *strong, condition, consequence));
                },
            }
        }
        
        results
    }
    
    fn check_safety(&self, property_index: usize, predicate: &Predicate) -> CheckResult {
        // 安全属性检查：确保坏事从不发生
        // 简化实现，实际检查需要遍历可达状态
        
        println!("检查安全属性 #{}", property_index);
        
        // 模拟找到违反
        if rand::random::<bool>() {
            let counter_example = self.generate_counter_example(property_index);
            CheckResult::Violation(counter_example)
        } else {
            CheckResult::Satisfied
        }
    }
    
    fn check_liveness(&self, property_index: usize, predicate: &Predicate) -> CheckResult {
        // 活性属性检查：确保好事最终发生
        // 简化实现
        
        println!("检查活性属性 #{}", property_index);
        
        // 模拟找到违反
        if rand::random::<bool>() {
            let counter_example = self.generate_counter_example(property_index);
            CheckResult::Violation(counter_example)
        } else {
            CheckResult::Satisfied
        }
    }
    
    fn check_ctl(&self, property_index: usize, formula: &CTLFormula) -> CheckResult {
        // CTL公式检查
        // 简化实现
        
        println!("检查CTL属性 #{}", property_index);
        
        // 模拟找到违反
        if rand::random::<bool>() {
            let counter_example = self.generate_counter_example(property_index);
            CheckResult::Violation(counter_example)
        } else {
            CheckResult::Satisfied
        }
    }
    
    fn check_ltl(&self, property_index: usize, formula: &LTLFormula) -> CheckResult {
        // LTL公式检查，通常转换为Büchi自动机
        // 简化实现
        
        println!("检查LTL属性 #{}", property_index);
        
        // 模拟找到违反
        if rand::random::<bool>() {
            let counter_example = self.generate_counter_example(property_index);
            CheckResult::Violation(counter_example)
        } else {
            CheckResult::Satisfied
        }
    }
    
    fn check_fairness(&self, property_index: usize, strong: bool, condition: &Predicate, consequence: &Predicate) -> CheckResult {
        // 公平性属性检查
        // 简化实现
        
        println!("检查{}公平性属性 #{}", if strong { "强" } else { "弱" }, property_index);
        
        // 模拟找到违反
        if rand::random::<bool>() {
            let counter_example = self.generate_counter_example(property_index);
            CheckResult::Violation(counter_example)
        } else {
            CheckResult::Satisfied
        }
    }
    
    fn generate_counter_example(&self, property_index: usize) -> CounterExample {
        // 生成反例（简化）
        CounterExample {
            property_index,
            path: vec![], // 在实际实现中，这应该是一条状态路径
        }
    }
}

enum CheckResult {
    Satisfied,
    Violation(CounterExample),
    Unknown(String),
}
```

### 2.3 类型系统与静态分析

类型系统和静态分析在编译时捕获潜在错误，提供强大的正确性保证。

```rust
// 高级类型系统
struct TypeSystem {
    basic_types: HashMap<String, BasicType>,
    composite_types: HashMap<String, CompositeType>,
    function_types: HashMap<String, FunctionType>,
    subtyping_relations: Vec<(String, String)>,
    type_constraints: Vec<TypeConstraint>,
}

enum BasicType {
    Unit,
    Boolean,
    Integer { bits: usize, signed: bool },
    Float { bits: usize },
    Char,
}

enum CompositeType {
    Tuple(Vec<String>),
    Record { fields: HashMap<String, String> },
    Sum { variants: HashMap<String, Option<String>> },
    Array { element_type: String, size: Option<usize> },
    List(String),
    Map { key_type: String, value_type: String },
}

struct FunctionType {
    parameter_types: Vec<String>,
    return_type: String,
    effects: Effects,
}

struct Effects {
    read_effects: HashSet<String>,
    write_effects: HashSet<String>,
    exception_effects: HashSet<String>,
    allocate_effects: bool,
    io_effects: bool,
}

enum TypeConstraint {
    Equal(String, String),
    Subtype(String, String),
    Bounded { type_var: String, upper_bound: String, lower_bound: String },
    Generic { type_var: String, constraints: Vec<String> },
}

// 依赖类型
struct DependentType {
    name: String,
    parameters: Vec<(String, String)>,
    refinement: Predicate,
}

// 线性类型
struct LinearType {
    base_type: String,
    consumed_at: Option<String>, // 函数名或None
}

// 静态分析框架
struct StaticAnalyzer {
    analyses: Vec<Box<dyn StaticAnalysis>>,
    program: Program,
    type_system: TypeSystem,
}

trait StaticAnalysis {
    fn name(&self) -> &str;
    fn analyze(&self, program: &Program) -> AnalysisResult;
    fn is_sound(&self) -> bool;
    fn is_complete(&self) -> bool;
}

struct Program {
    source_files: HashMap<String, SourceFile>,
    entry_points: Vec<String>,
    dependencies: HashMap<String, Vec<String>>,
}

struct SourceFile {
    path: String,
    ast: AST,
}

enum AST {
    Module { name: String, declarations: Vec<Declaration> },
    // 其他AST节点...
}

enum Declaration {
    Function { name: String, params: Vec<Parameter>, return_type: String, body: Box<Expression> },
    TypeDecl { name: String, definition: TypeDefinition },
    Variable { name: String, type_annotation: Option<String>, initializer: Box<Expression> },
    // 其他声明...
}

struct Parameter {
    name: String,
    type_annotation: String,
}

enum TypeDefinition {
    Alias(String),
    Struct { fields: Vec<(String, String)> },
    Enum { variants: Vec<(String, Option<Vec<String>>)> },
    Interface { methods: Vec<(String, FunctionType)> },
    // 其他类型定义...
}

enum Expression {
    // 简化AST表示
    Literal(Value),
    Variable(String),
    Function { params: Vec<Parameter>, body: Box<Expression> },
    Application { function: Box<Expression>, arguments: Vec<Expression> },
    Conditional { condition: Box<Expression>, then_branch: Box<Expression>, else_branch: Box<Expression> },
    Assignment { target: Box<Expression>, value: Box<Expression> },
    Block(Vec<Expression>),
    // 其他表达式...
}

struct AnalysisResult {
    issues: Vec<Issue>,
    properties: HashMap<String, Property>,
    is_safe: bool,
}

struct Issue {
    severity: IssueSeverity,
    message: String,
    location: SourceLocation,
    rule_id: String,
}

enum IssueSeverity {
    Error,
    Warning,
    Info,
}

struct SourceLocation {
    file: String,
    line: usize,
    column: usize,
    length: usize,
}

impl StaticAnalyzer {
    fn new(program: Program, type_system: TypeSystem) -> Self {
        StaticAnalyzer {
            analyses: Vec::new(),
            program,
            type_system,
        }
    }
    
    fn add_analysis(&mut self, analysis: Box<dyn StaticAnalysis>) {
        self.analyses.push(analysis);
    }
    
    fn run_all_analyses(&self) -> HashMap<String, AnalysisResult> {
        let mut results = HashMap::new();
        
        for analysis in &self.analyses {
            let name = analysis.name().to_string();
            let result = analysis.analyze(&self.program);
            results.insert(name, result);
        }
        
        results
    }
    
    fn is_program_well_typed(&self) -> Result<(), Vec<TypeCheckError>> {
        // 类型检查逻辑
        let mut errors = Vec::new();
        
        // 实际应用中应遍历AST检查类型
        // ...
        
        if errors.is_empty() {

```rust
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
    
    fn check_dependent_types(&self) -> Result<(), Vec<DependentTypeError>> {
        // 依赖类型检查逻辑
        let mut errors = Vec::new();
        
        // 检查每个依赖类型的精化谓词是否满足
        // ...
        
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
    
    fn analyze_effects(&self) -> EffectsAnalysisResult {
        // 效果分析
        let mut function_effects = HashMap::new();
        
        // 实际应用中应分析每个函数的效果
        // ...
        
        EffectsAnalysisResult { function_effects }
    }
}

struct TypeCheckError {
    message: String,
    location: SourceLocation,
    expected_type: String,
    actual_type: String,
}

struct DependentTypeError {
    message: String,
    location: SourceLocation,
    refinement: String,
    value: Value,
}

struct EffectsAnalysisResult {
    function_effects: HashMap<String, Effects>,
}

// 控制流分析
struct ControlFlowAnalysis;

impl StaticAnalysis for ControlFlowAnalysis {
    fn name(&self) -> &str {
        "控制流分析"
    }
    
    fn analyze(&self, program: &Program) -> AnalysisResult {
        let mut issues = Vec::new();
        let mut properties = HashMap::new();
        
        // 构建控制流图
        let cfg = self.build_control_flow_graph(program);
        
        // 检查未到达的代码
        let unreachable_nodes = self.find_unreachable_nodes(&cfg);
        for node in unreachable_nodes {
            issues.push(Issue {
                severity: IssueSeverity::Warning,
                message: format!("不可达代码在函数 {}", node.function_name),
                location: node.location.clone(),
                rule_id: "CFG-001".to_string(),
            });
        }
        
        // 检查可能的无限循环
        let potential_infinite_loops = self.find_potential_infinite_loops(&cfg);
        for loop_info in potential_infinite_loops {
            issues.push(Issue {
                severity: IssueSeverity::Warning,
                message: format!("可能的无限循环在函数 {}", loop_info.function_name),
                location: loop_info.location.clone(),
                rule_id: "CFG-002".to_string(),
            });
        }
        
        // 分析是否可能有未初始化变量的使用
        let uninit_vars = self.find_uninitialized_variables(program, &cfg);
        for var_use in uninit_vars {
            issues.push(Issue {
                severity: IssueSeverity::Error,
                message: format!("可能使用未初始化的变量 {}", var_use.variable_name),
                location: var_use.location.clone(),
                rule_id: "CFG-003".to_string(),
            });
        }
        
        AnalysisResult {
            issues,
            properties,
            is_safe: issues.iter().all(|i| i.severity != IssueSeverity::Error),
        }
    }
    
    fn is_sound(&self) -> bool {
        true // 本分析是声音的
    }
    
    fn is_complete(&self) -> bool {
        false // 本分析不完备
    }
}

impl ControlFlowAnalysis {
    fn build_control_flow_graph(&self, program: &Program) -> ControlFlowGraph {
        // 构建控制流图的逻辑
        ControlFlowGraph {
            nodes: Vec::new(),
            edges: Vec::new(),
        }
    }
    
    fn find_unreachable_nodes(&self, cfg: &ControlFlowGraph) -> Vec<CFGNode> {
        // 查找不可达节点的逻辑
        Vec::new()
    }
    
    fn find_potential_infinite_loops(&self, cfg: &ControlFlowGraph) -> Vec<LoopInfo> {
        // 查找潜在无限循环的逻辑
        Vec::new()
    }
    
    fn find_uninitialized_variables(&self, program: &Program, cfg: &ControlFlowGraph) -> Vec<VariableUse> {
        // 查找未初始化变量使用的逻辑
        Vec::new()
    }
}

struct ControlFlowGraph {
    nodes: Vec<CFGNode>,
    edges: Vec<CFGEdge>,
}

struct CFGNode {
    id: usize,
    function_name: String,
    statement: String,
    location: SourceLocation,
}

struct CFGEdge {
    from: usize,
    to: usize,
    condition: Option<String>,
}

struct LoopInfo {
    function_name: String,
    loop_header_id: usize,
    location: SourceLocation,
}

struct VariableUse {
    variable_name: String,
    location: SourceLocation,
}

// 数据流分析
struct DataFlowAnalysis {
    analysis_type: DataFlowAnalysisType,
}

enum DataFlowAnalysisType {
    ReachingDefinitions,
    LiveVariables,
    AvailableExpressions,
    Constants,
}

impl StaticAnalysis for DataFlowAnalysis {
    fn name(&self) -> &str {
        match self.analysis_type {
            DataFlowAnalysisType::ReachingDefinitions => "到达定义分析",
            DataFlowAnalysisType::LiveVariables => "活跃变量分析",
            DataFlowAnalysisType::AvailableExpressions => "可用表达式分析",
            DataFlowAnalysisType::Constants => "常量传播分析",
        }
    }
    
    fn analyze(&self, program: &Program) -> AnalysisResult {
        let mut issues = Vec::new();
        let mut properties = HashMap::new();
        
        match self.analysis_type {
            DataFlowAnalysisType::ReachingDefinitions => {
                // 到达定义分析
                let result = self.analyze_reaching_definitions(program);
                
                // 检查可能的未定义变量使用
                for undefined_use in result.potential_undefined_uses {
                    issues.push(Issue {
                        severity: IssueSeverity::Error,
                        message: format!("可能使用未定义的变量 {}", undefined_use.variable_name),
                        location: undefined_use.location.clone(),
                        rule_id: "DF-001".to_string(),
                    });
                }
                
                // 存储分析属性
                properties.insert("reaching_definitions".to_string(), Property::Map(result.reaching_definitions));
            },
            DataFlowAnalysisType::LiveVariables => {
                // 活跃变量分析
                let result = self.analyze_live_variables(program);
                
                // 检查可能的死代码（未使用的赋值）
                for dead_assignment in result.dead_assignments {
                    issues.push(Issue {
                        severity: IssueSeverity::Warning,
                        message: format!("未使用的赋值给变量 {}", dead_assignment.variable_name),
                        location: dead_assignment.location.clone(),
                        rule_id: "DF-002".to_string(),
                    });
                }
                
                // 存储分析属性
                properties.insert("live_variables".to_string(), Property::Map(result.live_variables));
            },
            DataFlowAnalysisType::AvailableExpressions => {
                // 可用表达式分析
                let result = self.analyze_available_expressions(program);
                
                // 检查冗余计算
                for redundant_expr in result.redundant_expressions {
                    issues.push(Issue {
                        severity: IssueSeverity::Info,
                        message: format!("冗余计算表达式 {}", redundant_expr.expression),
                        location: redundant_expr.location.clone(),
                        rule_id: "DF-003".to_string(),
                    });
                }
                
                // 存储分析属性
                properties.insert("available_expressions".to_string(), Property::Map(result.available_expressions));
            },
            DataFlowAnalysisType::Constants => {
                // 常量传播分析
                let result = self.analyze_constants(program);
                
                // 检查可折叠的常量表达式
                for foldable_expr in result.foldable_expressions {
                    issues.push(Issue {
                        severity: IssueSeverity::Info,
                        message: format!("可折叠的常量表达式 {} = {}", foldable_expr.expression, foldable_expr.constant_value),
                        location: foldable_expr.location.clone(),
                        rule_id: "DF-004".to_string(),
                    });
                }
                
                // 存储分析属性
                properties.insert("constant_values".to_string(), Property::Map(result.constant_values));
            },
        }
        
        AnalysisResult {
            issues,
            properties,
            is_safe: issues.iter().all(|i| i.severity != IssueSeverity::Error),
        }
    }
    
    fn is_sound(&self) -> bool {
        true // 这些数据流分析是声音的
    }
    
    fn is_complete(&self) -> bool {
        false // 这些数据流分析不完备
    }
}

impl DataFlowAnalysis {
    fn analyze_reaching_definitions(&self, program: &Program) -> ReachingDefinitionsResult {
        // 到达定义分析的逻辑
        ReachingDefinitionsResult {
            reaching_definitions: HashMap::new(),
            potential_undefined_uses: Vec::new(),
        }
    }
    
    fn analyze_live_variables(&self, program: &Program) -> LiveVariablesResult {
        // 活跃变量分析的逻辑
        LiveVariablesResult {
            live_variables: HashMap::new(),
            dead_assignments: Vec::new(),
        }
    }
    
    fn analyze_available_expressions(&self, program: &Program) -> AvailableExpressionsResult {
        // 可用表达式分析的逻辑
        AvailableExpressionsResult {
            available_expressions: HashMap::new(),
            redundant_expressions: Vec::new(),
        }
    }
    
    fn analyze_constants(&self, program: &Program) -> ConstantsResult {
        // 常量传播分析的逻辑
        ConstantsResult {
            constant_values: HashMap::new(),
            foldable_expressions: Vec::new(),
        }
    }
}

struct ReachingDefinitionsResult {
    reaching_definitions: HashMap<String, String>, // 简化表示
    potential_undefined_uses: Vec<VariableUse>,
}

struct LiveVariablesResult {
    live_variables: HashMap<String, String>, // 简化表示
    dead_assignments: Vec<VariableAssignment>,
}

struct AvailableExpressionsResult {
    available_expressions: HashMap<String, String>, // 简化表示
    redundant_expressions: Vec<ExpressionInfo>,
}

struct ConstantsResult {
    constant_values: HashMap<String, String>, // 简化表示
    foldable_expressions: Vec<FoldableExpression>,
}

struct VariableAssignment {
    variable_name: String,
    location: SourceLocation,
}

struct ExpressionInfo {
    expression: String,
    location: SourceLocation,
}

struct FoldableExpression {
    expression: String,
    constant_value: String,
    location: SourceLocation,
}

enum Property {
    Boolean(bool),
    Integer(i64),
    Float(f64),
    String(String),
    List(Vec<Property>),
    Map(HashMap<String, String>), // 简化表示
}
```

### 2.4 定理证明

定理证明使用形式逻辑来证明程序的正确性，通过机器化证明提供最高级别的保证。

```rust
// 定理证明框架
struct TheoremProver {
    logic_system: LogicSystem,
    theorem_database: HashMap<String, Theorem>,
    axioms: Vec<Formula>,
    inference_rules: Vec<InferenceRule>,
    proof_strategies: Vec<Box<dyn ProofStrategy>>,
}

enum LogicSystem {
    PropositionalLogic,
    FirstOrderLogic,
    HigherOrderLogic,
    TypeTheory,
    HoareLogic,
    SeparationLogic,
}

struct Theorem {
    name: String,
    statement: Formula,
    proof: Option<Proof>,
    dependencies: Vec<String>, // 依赖的其他定理
}

enum Formula {
    Atom(String),
    Negation(Box<Formula>),
    Conjunction(Vec<Formula>),
    Disjunction(Vec<Formula>),
    Implication(Box<Formula>, Box<Formula>),
    Universal { variable: String, domain: Option<Box<Formula>>, body: Box<Formula> },
    Existential { variable: String, domain: Option<Box<Formula>>, body: Box<Formula> },
    Equals(Box<Term>, Box<Term>),
    Predicate { name: String, arguments: Vec<Term> },
}

enum Term {
    Variable(String),
    Constant(String),
    Function { name: String, arguments: Vec<Term> },
}

struct InferenceRule {
    name: String,
    premises: Vec<Formula>,
    conclusion: Formula,
}

struct Proof {
    steps: Vec<ProofStep>,
    conclusion: Formula,
}

enum ProofStep {
    Axiom { axiom_index: usize },
    Assumption(Formula),
    InferenceApplication { rule_name: String, premise_indices: Vec<usize> },
    TheoremApplication { theorem_name: String, substitutions: HashMap<String, Term> },
    DischargeAssumption { assumption_index: usize, conclusion_index: usize },
}

trait ProofStrategy {
    fn name(&self) -> &str;
    fn prove(&self, goal: &Formula, context: &ProofContext) -> Option<Proof>;
    fn is_complete(&self) -> bool;
}

struct ProofContext<'a> {
    prover: &'a TheoremProver,
    assumptions: Vec<Formula>,
    proven_statements: Vec<Formula>,
}

impl TheoremProver {
    fn new(logic_system: LogicSystem) -> Self {
        TheoremProver {
            logic_system,
            theorem_database: HashMap::new(),
            axioms: Vec::new(),
            inference_rules: Vec::new(),
            proof_strategies: Vec::new(),
        }
    }
    
    fn add_axiom(&mut self, axiom: Formula) {
        self.axioms.push(axiom);
    }
    
    fn add_inference_rule(&mut self, rule: InferenceRule) {
        self.inference_rules.push(rule);
    }
    
    fn add_theorem(&mut self, theorem: Theorem) -> Result<(), String> {
        // 检查依赖是否满足
        for dep in &theorem.dependencies {
            if !self.theorem_database.contains_key(dep) {
                return Err(format!("依赖的定理 '{}' 未找到", dep));
            }
        }
        
        // 检查证明是否有效
        if let Some(proof) = &theorem.proof {
            if !self.verify_proof(proof, &theorem.statement) {
                return Err("定理证明无效".to_string());
            }
        }
        
        self.theorem_database.insert(theorem.name.clone(), theorem);
        Ok(())
    }
    
    fn add_proof_strategy(&mut self, strategy: Box<dyn ProofStrategy>) {
        self.proof_strategies.push(strategy);
    }
    
    fn prove_formula(&self, formula: &Formula) -> Option<Proof> {
        let context = ProofContext {
            prover: self,
            assumptions: Vec::new(),
            proven_statements: Vec::new(),
        };
        
        // 尝试所有策略
        for strategy in &self.proof_strategies {
            if let Some(proof) = strategy.prove(formula, &context) {
                if self.verify_proof(&proof, formula) {
                    return Some(proof);
                }
            }
        }
        
        None
    }
    
    fn verify_proof(&self, proof: &Proof, expected_conclusion: &Formula) -> bool {
        let mut verified_steps = Vec::new();
        
        for (i, step) in proof.steps.iter().enumerate() {
            match step {
                ProofStep::Axiom { axiom_index } => {
                    if *axiom_index >= self.axioms.len() {
                        return false; // 无效的公理索引
                    }
                    verified_steps.push(self.axioms[*axiom_index].clone());
                },
                ProofStep::Assumption(formula) => {
                    verified_steps.push(formula.clone());
                },
                ProofStep::InferenceApplication { rule_name, premise_indices } => {
                    // 检查规则是否存在
                    let rule = self.inference_rules.iter()
                        .find(|r| r.name == *rule_name)
                        .ok_or(false)?;
                    
                    // 检查前提是否匹配
                    if premise_indices.len() != rule.premises.len() {
                        return false;
                    }
                    
                    for (i, &premise_idx) in premise_indices.iter().enumerate() {
                        if premise_idx >= verified_steps.len() {
                            return false; // 无效的前提索引
                        }
                        
                        if !self.formulas_equivalent(&verified_steps[premise_idx], &rule.premises[i]) {
                            return false; // 前提不匹配
                        }
                    }
                    
                    verified_steps.push(rule.conclusion.clone());
                },
                ProofStep::TheoremApplication { theorem_name, substitutions } => {
                    // 检查定理是否存在
                    let theorem = self.theorem_database.get(theorem_name)
                        .ok_or(false)?;
                    
                    // 应用替换
                    let instantiated_statement = self.substitute_variables(&theorem.statement, substitutions);
                    verified_steps.push(instantiated_statement);
                },
                ProofStep::DischargeAssumption { assumption_index, conclusion_index } => {
                    if *assumption_index >= verified_steps.len() || *conclusion_index >= verified_steps.len() {
                        return false; // 无效的索引
                    }
                    
                    let assumption = &verified_steps[*assumption_index];
                    let conclusion = &verified_steps[*conclusion_index];
                    
                    // 创建蕴含式
                    let implication = Formula::Implication(
                        Box::new(assumption.clone()),
                        Box::new(conclusion.clone())
                    );
                    
                    verified_steps.push(implication);
                },
            }
        }
        
        // 检查最后一步是否是期望的结论
        if let Some(last_step) = verified_steps.last() {
            self.formulas_equivalent(last_step, expected_conclusion)
        } else {
            false
        }
    }
    
    fn formulas_equivalent(&self, f1: &Formula, f2: &Formula) -> bool {
        // 检查两个公式是否逻辑等价
        // 简化实现，实际应用中需要更复杂的逻辑
        format!("{:?}", f1) == format!("{:?}", f2)
    }
    
    fn substitute_variables(&self, formula: &Formula, substitutions: &HashMap<String, Term>) -> Formula {
        // 将变量替换为项
        // 简化实现
        formula.clone()
    }
    
    fn verify_program(&self, program: &Program, specification: &FormalSpecification) -> VerificationResult {
        // 将程序转换为逻辑公式
        let program_formula = self.translate_program_to_formula(program);
        
        // 将规范转换为逻辑公式
        let spec_formula = self.translate_specification_to_formula(specification);
        
        // 构造验证条件：程序 => 规范
        let verification_condition = Formula::Implication(
            Box::new(program_formula),
            Box::new(spec_formula)
        );
        
        // 尝试证明验证条件
        if let Some(proof) = self.prove_formula(&verification_condition) {
            VerificationResult::Success
        } else {
            VerificationResult::Failure(vec![])
        }
    }
    
    fn translate_program_to_formula(&self, program: &Program) -> Formula {
        // 将程序转换为逻辑公式
        // 简化实现
        Formula::Atom("program_semantics".to_string())
    }
    
    fn translate_specification_to_formula(&self, specification: &FormalSpecification) -> Formula {
        // 将规范转换为逻辑公式
        // 简化实现
        Formula::Atom("specification_semantics".to_string())
    }
}

// 各种证明策略实现

// 归纳证明策略
struct InductionStrategy;

impl ProofStrategy for InductionStrategy {
    fn name(&self) -> &str {
        "归纳证明"
    }
    
    fn prove(&self, goal: &Formula, context: &ProofContext) -> Option<Proof> {
        // 尝试识别可归纳的变量
        let induction_variables = self.identify_induction_variables(goal);
        
        if induction_variables.is_empty() {
            return None; // 没有可归纳的变量
        }
        
        // 尝试对每个变量进行归纳证明
        for var in induction_variables {
            if let Some(proof) = self.prove_by_induction(goal, &var, context) {
                return Some(proof);
            }
        }
        
        None
    }
    
    fn is_complete(&self) -> bool {
        false // 归纳证明不完备
    }
}

impl InductionStrategy {
    fn identify_induction_variables(&self, formula: &Formula) -> Vec<String> {
        // 识别公式中可归纳的变量
        // 简化实现
        let mut vars = Vec::new();
        
        match formula {
            Formula::Universal { variable, domain, body } => {
                // 检查domain是否是自然数等可归纳结构
                vars.push(variable.clone());
                
                // 递归检查body
                vars.extend(self.identify_induction_variables(body));
            },
            Formula::Existential { variable, domain, body } => {
                // 类似Universal的处理
                vars.extend(self.identify_induction_variables(body));
            },
            Formula::Conjunction(formulas) | Formula::Disjunction(formulas) => {
                for f in formulas {
                    vars.extend(self.identify_induction_variables(f));
                }
            },
            Formula::Implication(premise, conclusion) => {
                vars.extend(self.identify_induction_variables(premise));
                vars.extend(self.identify_induction_variables(conclusion));
            },
            Formula::Negation(sub_formula) => {
                vars.extend(self.identify_induction_variables(sub_formula));
            },
            _ => {},
        }
        
        // 去重
        vars.sort();
        vars.dedup();
        
        vars
    }
    
    fn prove_by_induction(&self, goal: &Formula, induction_var: &str, context: &ProofContext) -> Option<Proof> {
        // 基本情况证明
        let base_case = self.substitute_base_case(goal, induction_var);
        let base_proof = context.prover.prove_formula(&base_case)?;
        
        // 归纳步骤
        let induction_hyp = self.create_induction_hypothesis(goal, induction_var);
        let induction_step = self.create_induction_step(goal, induction_var);
        
        // 创建包含归纳假设的新上下文
        let mut extended_context = ProofContext {
            prover: context.prover,
            assumptions: context.assumptions.clone(),
            proven_statements: context.proven_statements.clone(),
        };
        extended_context.assumptions.push(induction_hyp);
        
        // 证明归纳步骤
        let step_proof = context.prover.prove_formula(&induction_step)?;
        
        // 构建完整证明
        // 简化实现
        Some(Proof {
            steps: vec![],
            conclusion: goal.clone(),
        })
    }
    
    fn substitute_base_case(&self, formula: &Formula, var: &str) -> Formula {
        // 替换变量为基本情况（如0）
        // 简化实现
        formula.clone()
    }
    
    fn create_induction_hypothesis(&self, formula: &Formula, var: &str) -> Formula {
        // 创建归纳假设
        // 简化实现
        formula.clone()
    }
    
    fn create_induction_step(&self, formula: &Formula, var: &str) -> Formula {
        // 创建归纳步骤
        // 简化实现
        formula.clone()
    }
}

// 自动定理证明策略
struct ResolutionStrategy;

impl ProofStrategy for ResolutionStrategy {
    fn name(&self) -> &str {
        "分解策略"
    }
    
    fn prove(&self, goal: &Formula, context: &ProofContext) -> Option<Proof> {
        // 将目标和假设转换为子句形式
        let mut clauses = self.convert_to_clauses(context.assumptions.clone());
        
        // 添加目标的否定
        let negated_goal = Formula::Negation(Box::new(goal.clone()));
        clauses.extend(self.convert_to_clauses(vec![negated_goal]));
        
        // 应用分解规则直到产生空子句或达到步骤限制
        let max_steps = 1000;
        let result = self.apply_resolution(&mut clauses, max_steps);
        
        if result {
            // 构建证明
            // 简化实现
            Some(Proof {
                steps: vec![],
                conclusion: goal.clone(),
            })
        } else {
            None
        }
    }
    
    fn is_complete(&self) -> bool {
        true // 分解规则对一阶逻辑是完备的
    }
}

impl ResolutionStrategy {
    fn convert_to_clauses(&self, formulas: Vec<Formula>) -> Vec<Clause> {
        // 将公式转换为子句形式
        // 简化实现
        vec![]
    }
    
    fn apply_resolution(&self, clauses: &mut Vec<Clause>, max_steps: usize) -> bool {
        // 应用分解规则
        // 简化实现
        false
    }
}

struct Clause {
    literals: HashSet<Literal>,
}

enum Literal {
    Positive(Atom),
    Negative(Atom),
}

struct Atom {
    predicate: String,
    arguments: Vec<Term>,
}

// Hoare逻辑证明策略
struct HoareLogicStrategy;

impl ProofStrategy for HoareLogicStrategy {
    fn name(&self) -> &str {
        "Hoare逻辑"
    }
    
    fn prove(&self, goal: &Formula, context: &ProofContext) -> Option<Proof> {
        // 识别和分解Hoare三元组 {P} C {Q}
        if let Some((pre, program, post)) = self.extract_hoare_triple(goal) {
            return self.verify_hoare_triple(&pre, &program, &post, context);
        }
        
        None
    }
    
    fn is_complete(&self) -> bool {
        false // Hoare逻辑对某些程序构造是不完备的
    }
}

impl HoareLogicStrategy {
    fn extract_hoare_triple(&self, formula: &Formula) -> Option<(Formula, String, Formula)> {
        // 从公式中提取Hoare三元组
        // 简化实现
        None
    }
    
    fn verify_hoare_triple(&self, pre: &Formula, program: &str, post: &Formula, context: &ProofContext) -> Option<Proof> {
        // 解析程序语句
        let statement = self.parse_program(program)?;
        
        // 根据语句类型应用Hoare规则
        match statement {
            ProgramStatement::Assignment { var, expr } => {
                self.verify_assignment(pre, &var, &expr, post, context)
            },
            ProgramStatement::Sequence { statements } => {
                self.verify_sequence(pre, &statements, post, context)
            },
            ProgramStatement::Conditional { condition, then_branch, else_branch } => {
                self.verify_conditional(pre, &condition, &then_branch, &else_branch, post, context)
            },
            ProgramStatement::While { condition, body } => {
                self.verify_while(pre, &condition, &body, post, context)
            },
            ProgramStatement::Skip => {
                // 对于Skip语句，前条件应该蕴含后条件
                let implication = Formula::Implication(
                    Box::new(pre.clone()),
                    Box::new(post.clone())
                );
                
                context.prover.prove_formula(&implication)
            },
        }
    }
    
    fn parse_program(&self, program: &str) -> Option<ProgramStatement> {
        // 解析程序文本为语句结构
        // 简化实现
        None
    }
    
    fn verify_assignment(&self, pre: &Formula, var: &str, expr: &str, post: &Formula, context: &ProofContext) -> Option<Proof> {
        // 应用赋值规则：{Q[x/E]} x := E {Q}
        // 因此我们需要检查：pre => post[var/expr]
        let substituted_post = self.substitute_var_with_expr(post, var, expr);
        let implication = Formula::Implication(
            Box::new(pre.clone()),
            Box::new(substituted_post)
        );
        
        context.prover.prove_formula(&implication)
    }
    
    fn verify_sequence(&self, pre: &Formula, statements: &[ProgramStatement], post: &Formula, context: &ProofContext) -> Option<Proof> {
        // 处理语句序列的Hoare规则
        // 简化实现
        None
    }
    
    fn verify_conditional(&self, pre: &Formula, condition: &str, then_branch: &ProgramStatement, else_branch: &ProgramStatement, post: &Formula, context: &ProofContext) -> Option<Proof> {
        // 处理条件语句的Hoare规则
        // 简化实现
        None
    }
    
    fn verify_while(&self, pre: &Formula, condition: &str, body: &ProgramStatement, post: &Formula, context: &ProofContext) -> Option<Proof> {
        // 处理循环语句的Hoare规则
        // 简化实现
        None
    }
    
    fn substitute_var_with_expr(&self, formula: &Formula, var: &str, expr: &str) -> Formula {
        // 在公式中将变量替换为表达式
        // 简化实现
        formula.clone()
    }
}

enum ProgramStatement {
    Assignment { var: String, expr: String },
    Sequence { statements: Vec<ProgramStatement> },
    Conditional { condition: String, then_branch: Box<ProgramStatement>, else_branch: Box<ProgramStatement> },
    While { condition: String, body: Box<ProgramStatement> },
    Skip,
}
```

## 3. 实时与响应式系统

### 3.1 硬实时约束

硬实时系统必须在严格的时间约束内完成操作，任何违反都可能导致系统失败。

```rust
// 硬实时系统框架
struct HardRealTimeSystem {
    tasks: Vec<RealTimeTask>,
    scheduler: Box<dyn RealTimeScheduler>,
    resource_manager: ResourceManager,
    timing_analyzer: TimingAnalyzer,
    execution_monitor: ExecutionMonitor,
}

struct RealTimeTask {
    id: String,
    priority: usize,
    period: Duration, // 周期任务的周期
    deadline: Duration, // 相对截止期限
    wcet: Duration, // 最坏情况执行时间
    offset: Duration, // 首次释放时间
    criticality_level: CriticalityLevel,
    handler: Box<dyn Fn() -> TaskResult>,
    dependencies: Vec<String>, // 依赖的任务ID
    resources: Vec<String>, // 需要的资源
}

enum CriticalityLevel {
    Low,
    Medium,
    High,
    Critical,
}

struct TaskResult {
    execution_time: Duration,
    success: bool,
    message: Option<String>,
}

trait RealTimeScheduler {
    fn name(&self) -> &str;
    fn schedule(&self, tasks: &[RealTimeTask]) -> SchedulingResult;
    fn is_schedulable(&self, tasks: &[RealTimeTask]) -> bool;
    fn dispatch(&self, ready_tasks: &[&RealTimeTask]) -> Option<String>; // 返回要执行的任务ID
}

struct SchedulingResult {
    schedule: Vec<ScheduledTask>,
    is_feasible: bool,
    utilization: f64,
    slack_time: HashMap<String, Duration>,
}

struct ScheduledTask {
    task_id: String,
    start_time: Duration,
    finish_time: Duration,
}

struct ResourceManager {
    resources: HashMap<String, Resource>,
    ceiling_protocol: bool, // 是否使用优先级天花板协议
    inheritance_protocol: bool, // 是否使用优先级继承协议
}

struct Resource {
    name: String,
    current_owner: Option<String>, // 持有资源的任务ID
    waiting_queue: VecDeque<String>, // 等待资源的任务队列
    ceiling_priority: Option<usize>, // 优先级天花板
}

struct TimingAnalyzer {
    wcet_analysis_technique: WCETAnalysisTechnique,
    cache_analysis_enabled: bool,
    pipeline_analysis_enabled: bool,
    path_analysis_enabled: bool,
}

enum WCETAnalysisTechnique {
    StaticAnalysis,
    MeasurementBased,
    Hybrid,
}

struct ExecutionMonitor {
    deadline_misses: HashMap<String, usize>,
    execution_times: HashMap<String, Vec<Duration>>,
    mode_changes: Vec<ModeChange>,
}

struct ModeChange {
    timestamp: Instant,
    from_mode: String,
    to_mode: String,
    cause: String,
}

impl HardRealTimeSystem {
    fn new(scheduler: Box<dyn RealTimeScheduler>, wcet_technique: WCETAnalysisTechnique) -> Self {
        HardRealTimeSystem {
            tasks: Vec::new(),
            scheduler,
            resource_manager: ResourceManager {
                resources: HashMap::new(),
                ceiling_protocol: true,
                inheritance_protocol: false,
            },
            timing_analyzer: TimingAnalyzer {
                wcet_analysis_technique: wcet_technique,
                cache_analysis_enabled: true,
                pipeline_analysis_enabled: true,
                path_analysis_enabled: true,
            },
            execution_monitor: ExecutionMonitor {
                deadline_misses: HashMap::new(),
                execution_times: HashMap::new(),
                mode_changes: Vec::new(),
            },
        }
    }
    
    fn add_task(&mut self, task: RealTimeTask) -> Result<(), String> {
        // 检查任务的硬实时约束是否可以满足
        let schedulability_test_passed = self.check_schedulability_with_new_task(&task);
        
        if !schedulability_test_passed {
            return Err(format!("添加任务'{}'后系统不可调度", task.id));
        }
        
        // 检查资源依赖
        for resource_name in &task.resources {
            if !self.resource_manager.resources.contains_key(resource_name) {
                return Err(format!("任务'{}'依赖未知资源'{}'", task.id, resource_name));
            }
        }
        
        // 添加任务
        self.tasks.push(task);
        
        // 重新计算调度
        let _ = self.scheduler.schedule(&self.tasks);
        
        Ok(())
    }
    
    fn add_resource(&mut self, name: &str, ceiling_priority: Option<usize>) -> Result<(), String> {
        if self.resource_manager.resources.contains_key(name) {
            return Err(format!("资源'{}'已存在", name));
        }
        
        let resource = Resource {
            name: name.to_string(),
            current_owner: None,
            waiting_queue: VecDeque::new(),
            ceiling_priority,
        };
        
        self.resource_manager.resources.insert(name.to_string(), resource);
        
        Ok(())
    }
    
    fn check_schedulability_with_new_task(&self, new_task: &RealTimeTask) -> bool {
        let mut extended_tasks = self.tasks.clone();
        extended_tasks.push(new_task.clone());
        
        self.scheduler.is_schedulable(&extended_tasks)
    }
    
    fn start(&mut self) -> Result<(), String> {
        // 检查系统是否可调度
        if !self.scheduler.is_schedulable(&self.tasks) {
            return Err("任务集不可调度".to_string());
        }
        
        println!("启动硬实时系统，任务数量: {}", self.tasks.len());
        
        // 在实际系统中，这里会初始化硬件定时器和中断
        // 简化实现
        
        Ok(())
    }
    
    fn execute_cycle(&mut self) -> Vec<TaskExecutionResult> {
        let current_time = Instant::now();
        let mut results = Vec::new();
        
        // 确定当前周期中可以运行的任务
        let ready_tasks: Vec<&RealTimeTask> = self.tasks.iter()
            .filter(|task| self.is_task_ready(task, current_time))
            .collect();
        
        // 使用调度器决定执行顺序
        while let Some(task_id) = self.scheduler.dispatch(&ready_tasks) {
            let task = self.tasks.iter()
                .find(|t| t.id == task_id)
                .unwrap();
            
            // 获取所需资源
            if !self.acquire_resources_for_task(task) {
                // 无法获取所有资源，跳过此任务
                continue;
            }
            
            // 执行任务
            let start_time = Instant::now();
            let result = (task.handler)();
            let end_time = Instant::now();
            let execution_duration = end_time.duration_since(start_time);
            
            // 记录执行时间
            self.execution_monitor.execution_times
                .entry(task.id.clone())
                .or_insert_with(Vec::new)
                .push(execution_duration);
            
            // 检查截止期限
            let deadline_time = start_time + task.deadline;
            let deadline_missed = end_time > deadline_time;
            
            if deadline_missed {
                *self.execution_monitor.deadline_misses
                    .entry(task.id.clone())
                    .or_insert(0) += 1;
                
                println!("任务'{}'错过截止期限: 执行时间 {:?}, 截止期限 {:?}",
                       task.id, execution_duration, task.deadline);
            }
            
            // 释放资源
            self.release_resources_for_task(task);
            
            // 记录结果
            results.push(TaskExecutionResult {
                task_id: task.id.clone(),
                execution_time: execution_duration,
                deadline_missed,
                success: result.success,
                message: result.message,
            });
        }
        
        results
    }
    
    fn is_task_ready(&self, task: &RealTimeTask, current_time: Instant) -> bool {
        // 检查任务是否准备好执行
        // 简化实现，实际中需要考虑周期、偏移等
        true
    }
    
    fn acquire_resources_for_task(&mut self, task: &RealTimeTask) -> bool {
        // 尝试获取任务所需的所有资源
        for resource_name in &task.resources {
            if let Some(resource) = self.resource_manager.resources.get_mut(resource_name) {
                if resource.current_owner.is_some() {
                    // 资源已被占用
                    if self.resource_manager.ceiling_protocol {
                        // 使用优先级天花板协议
                        // 简化实现
                    } else if self.resource_manager.inheritance_protocol {
                        // 使用优先级继承协议
                        // 简化实现
                    } else {
                        // 无法获取资源
                        return false;
                    }
                } else {
                    // 获取资源
                    resource.current_owner = Some(task.id.clone());
                }
            } else {
                return false;
            }
        }
        
        true
    }
    
    fn release_resources_for_task(&mut self, task: &RealTimeTask) {
        // 释放任务持有的资源
        for resource_name in &task.resources {
            if let Some(resource) = self.resource_manager.resources.get_mut(resource_name) {
                if resource.current_owner.as_ref() == Some(&task.id) {
                    // 释放资源
                    resource.current_owner = None;
                    
                    // 检查等待队列
                    if let Some(next_task_id) = resource.waiting_queue.pop_front() {
                        resource.current_owner = Some(next_task_id);
                    }
                }
            }
        }
    }
    
    fn analyze_wcet(&self, task_id: &str) -> Option<Duration> {
        let task = self.tasks.iter().find(|t| t.id == task_id)?;
        
        match self.timing_analyzer.wcet_analysis_technique {
            WCETAnalysisTechnique::StaticAnalysis => {
                // 静态分析WCET
                // 简化实现
                Some(task.wcet)
            },
            WCETAnalysisTechnique::MeasurementBased => {
                // 基于测量的WCET
                if let Some(times) = self.execution_monitor.execution_times.get(task_id) {
                    if times.is_empty() {
                        return None;
                    }
                    
                    // 使用最大观测值加安全余量
                    let max_observed = times.iter().max().unwrap();
                    let safety_margin = max_observed.mul_f32(1.2); // 20%安全边际
                    
                    Some(safety_margin)
                } else {
                    None
                }
            },
            WCETAnalysisTechnique::Hybrid => {
                // 混合方法
                // 简化实现
                Some(task.wcet)
            },
        }
    }
    
    fn generate_timing_report(&self) -> TimingReport {
        let mut task_reports = HashMap::new();
        
        for task in &self.tasks {
            let execution_times = self.execution_monitor.execution_times
                .get(&task.id)
                .cloned()
                .unwrap_or_default();
            
            let deadline_misses = self.execution_monitor.deadline_misses
                .get(&task.id)
                .cloned()
                .unwrap_or_default();
            
            let wcet_estimate = self.analyze_wcet(&task.id).unwrap_or(task.wcet);
            
            let report = TaskTimingReport {
                task_id: task.id.clone(),
                min_observed: execution_times.iter().min().cloned().unwrap_or_default(),
                max_observed: execution_times.iter().max().cloned().unwrap_or_default(),
                avg_observed: if execution_times.is_empty() {
                    Duration::default()
                } else {
                    let sum: Duration = execution_times.iter().sum();
                    sum / execution_times.len() as u32
                },
                wcet_estimate,
                deadline_misses,
                total_executions: execution_times.len(),
            };
            
            task_reports.insert(task.id.clone(), report);
        }
        
        TimingReport {
            task_reports,
            system_utilization: self.calculate_utilization(),
        }
    }
    
    fn calculate_utilization(&self) -> f64 {
        let mut total_utilization = 0.0;
        
        for task in &self.tasks {
            let wcet_secs = task.wcet.as_secs_f64();
            let period_secs = task.period.as_secs_f64();
            
            if period_secs > 0.0 {
                total_utilization += wcet_secs / period_secs;
            }
        }
        
        total_utilization
    }
}

struct TaskExecutionResult {
    task_id: String,
    execution_time: Duration,
    deadline_missed: bool,
    success: bool,
    message: Option<String>,
}

struct TimingReport {
    task_reports: HashMap<String, TaskTimingReport>,
    system_utilization: f64,
}

struct TaskTimingReport {
    task_id: String,
    min_observed: Duration,
    max_observed: Duration,
    avg_observed: Duration,
    wcet_estimate: Duration,
    deadline_misses: usize,
    total_executions: usize,
}

// 速率单调调度器
struct RateMonotonicScheduler;

impl RealTimeScheduler for RateMonotonicScheduler {
    fn name(&self) -> &str {
        "速率单调调度器"
    }
    
    fn schedule(&self, tasks: &[RealTimeTask]) -> SchedulingResult {
        // 按周期从小到大排序任务（速率单调）
        let mut sorted_tasks = tasks.to_vec();
        sorted_tasks.sort_by(|a, b| a.period.cmp(&b.period));
        
        // 检查可调度性
        let is_feasible = self.is_schedulable(tasks);
        
        // 创建调度
        let mut schedule = Vec::new();
        let mut current_time = Duration::from_secs(0);
        
        // 简化实现，创建简单的时间线
        // 实际的RM调度会更复杂
        
        // 计算每个任务的松弛时间
        let mut slack_time = HashMap::new();
        for task in tasks {
            let utilization = task.wcet.as_secs_f64() / task.period.as_secs_f64();
            let slack = task.deadline.as_secs_f64() - task.wcet.as_secs_f64();
            slack_time.insert(task.id.clone(), Duration::from_secs_f64(slack));
        }
        
        SchedulingResult {
            schedule,
            is_feasible,
            utilization: self.calculate_utilization(tasks),
            slack_time,
        }
    }
    
    fn is_schedulable(&self, tasks: &[RealTimeTask]) -> bool {
        // 使用速率单调可调度性测试
        // 对于n个任务，如果U <= n(2^(1/n) - 1)，则可调度
        let n = tasks.len() as f64;
        let utilization_bound = n * (2.0_f64.powf(1.0 / n) - 1.0);
        
        let actual_utilization = self.calculate_utilization(tasks);
        
        if actual_utilization <= utilization_bound {
            return true; // 利用率测试通过
        }
        
        // 如果利用率测试失败，进行更精确的响应时间分析
        self.response_time_analysis(tasks)
    }
    
    fn dispatch(&self, ready_tasks: &[&RealTimeTask]) -> Option<String> {
        if ready_tasks.is_empty() {
            return None;
        }
        
        // 按周期（优先级）排序
        let mut sorted_tasks = ready_tasks.to_vec();
        sorted_tasks.sort_by(|a, b| a.period.cmp(&b.period));
        
        // 返回优先级最高的任务
        Some(sorted_tasks[0].id.clone())
    }
}

impl RateMonotonicScheduler {
    fn calculate_utilization(&self, tasks: &[RealTimeTask]) -> f64 {
        let mut total_utilization = 0.0;
        
        for task in tasks {
            let wcet_secs = task.wcet.as_secs_f64();
            let period_secs = task.period.as_secs_f64();
            
            if period_secs > 0.0 {
                total_utilization += wcet_secs / period_secs;
            }
        }
        
        total_utilization
    }
    
    fn response_time_analysis(&self, tasks: &[RealTimeTask]) -> bool {
        // 响应时间分析，检查每个任务的响应时间是否小于其截止期限
        let mut sorted_tasks = tasks.to_vec();
        sorted_tasks.sort_by(|a, b| a.period.cmp(&b.period));
        
        for i in 0..sorted_tasks.len() {
            let task = &sorted_tasks[i];
            
            // 初始响应时间等于任务的WCET
            let mut response_time = task.wcet;
            
            loop {
                let mut new_response_time = task.wcet;
                
                // 计算干扰
                for j in 0..i {
                    let higher_priority_task = &sorted_tasks[j];
                    
                    // 计算高优先级任务对当前任务的干扰
                    let interference = (response_time.as_secs_f64() / higher_priority_task.period.as_secs_f64()).ceil()
                                       * higher_priority_task.wcet.as_secs_f64();
                    
                    new_response_time += Duration::from_secs_f64(interference);
                }
                
                if new_response_time == response_time {
                    // 响应时间收敛
                    break;
                }
                
                response_time = new_response_time;
                
                if response_time > task.deadline {
                    // 响应时间超过截止期限
                    return false;
                }
            }
        }
        
        true
    }
}

// 最早截止期限优先调度器
struct EarliestDeadlineFirstScheduler;

impl RealTimeScheduler for EarliestDeadlineFirstScheduler {
    fn name(&self) -> &str {
        "最早截止期限优先调度器"
    }
    
    fn schedule(&self, tasks: &[RealTimeTask]) -> SchedulingResult {
        // 检查可调度性
        let is_feasible = self.is_schedulable(tasks);
        
        // 创建调度
        let mut schedule = Vec::new();
        let mut slack_time = HashMap::new();
        
        // 简化实现
        
        SchedulingResult {
            schedule,
            is_feasible,
            utilization: self.calculate_utilization(tasks),
            slack_time,
        }
    }
    
    fn is_schedulable(&self, tasks: &[RealTimeTask]) -> bool {
        // 对于EDF，如果总利用率 <= 1，则任务集可调度
        let utilization = self.calculate_utilization(tasks);
        
        // 检查利用率
        if utilization <= 1.0 {
            return true;
        }
        
        // 实际上，EDF的可调度性判定比这复杂，特别是对于有约束的截止期限
        // 这里简化处理
        
        false
    }
    
    fn dispatch(&self, ready_tasks: &[&RealTimeTask]) -> Option<String> {
        if ready_tasks.is_empty() {
            return None;
        }
        
        // 按绝对截止期限排序
        let current_time = Instant::now();
        let mut sorted_tasks = ready_tasks.to_vec();
        
        sorted_tasks.sort_by(|a, b| {
            let a_deadline = current_time + a.deadline;
            let b_deadline = current_time + b.deadline;
            a_deadline.cmp(&b_deadline)
        });
        
        // 返回截止期限最早的任务
        Some(sorted_tasks[0].id.clone())
    }
}

impl EarliestDeadlineFirstScheduler {
    fn calculate_utilization(&self, tasks: &[RealTimeTask]) -> f64 {
        let mut total_utilization = 0.0;
        
        for task in tasks {
            let wcet_secs = task.wcet.as_secs_f64();
            let period_secs = task.period.as_secs_f64();
            
            if period_secs > 0.0 {
                total_utilization += wcet_secs / period_secs;
            }
        }
        
        total_utilization
    }
}
```

### 3.2 软实时策略

软实时系统允许偶尔的截止期限超出，但仍然需要管理时间缺失和性能退化的方式。

```rust
// 软实时系统框架
struct SoftRealTimeSystem {
    tasks: Vec<SoftRealTimeTask>,
    scheduler: Box<dyn SoftRealTimeScheduler>,
    qos_manager: QoSManager,
    adaptation_manager: AdaptationManager,
    performance_monitor: PerformanceMonitor,
}

struct SoftRealTimeTask {
    id: String,
    priority: usize,
    execution_time_distribution: ExecutionTimeDistribution,
    deadline: Duration,
    importance: f64, // 任务重要性，用于QoS决策
    utility_function: Box<dyn Fn(Duration, Duration) -> f64>, // 根据完成时间和截止期限计算效用
    adaptation_handlers: HashMap<AdaptationLevel, Box<dyn Fn() -> TaskResult>>,
    current_adaptation_level: AdaptationLevel,
}

enum ExecutionTimeDistribution {
    Constant(Duration),
    Uniform { min: Duration, max: Duration },
    Normal { mean: Duration, std_dev: Duration },
    Empirical { samples: Vec<Duration> },
}

enum AdaptationLevel {
    Full,
    High,
    Medium,
    Low,
    Minimal,
}

trait SoftRealTimeScheduler {
    fn name(&self) -> &str;
    fn schedule(&self, tasks: &[SoftRealTimeTask], current_load: f64) -> SoftSchedulingResult;
    fn dispatch(&self, ready_tasks: &[&SoftRealTimeTask], current_time: Instant) -> Option<String>;
    fn handle_deadline_miss(&mut self, task_id: &str, miss_severity: f64);
}

struct SoftSchedulingResult {
    task_allocation: HashMap<String, f64>, // 任务ID -> 资源分配比例
    expected_quality: f64,
    expected_deadline_misses: HashMap<String, f64>, // 任务ID -> 预期错过率
}

struct QoSManager {
    quality_levels: Vec<QualityLevel>,
    current_level: usize,
    degradation_policy: DegradationPolicy,
    min_acceptable_quality: f64,
}

struct QualityLevel {
    name: String,
    resource_allocation: HashMap<String, f64>, // 任务ID -> 资源分配比例
    expected_quality: f64,
    task_adaptation_levels: HashMap<String, AdaptationLevel>, // 任务ID -> 适应级别
}

enum DegradationPolicy {
    Uniform, // 均匀降低所有任务质量
    PriorityBased, // 基于优先级降低质量
    ImportanceBased, // 基于重要性降低质量
    UtilityMaximizing, // 最大化整体效用
}

struct AdaptationManager {
    triggers: Vec<AdaptationTrigger>,
    strategies: HashMap<String, AdaptationStrategy>,
    adaptation_history: Vec<AdaptationEvent>,
}

enum AdaptationTrigger {
    LoadThreshold { threshold: f64, direction: ThresholdDirection },
    DeadlineMissRate { task_id: String, threshold: f64 },
    QualityThreshold { threshold: f64, direction: ThresholdDirection },
    ExternalEvent { event_type: String },
}

enum ThresholdDirection {
    Above,
    Below,
}

struct AdaptationStrategy {
    name: String,
    description: String,
    actions: Vec<AdaptationAction>,
}

enum AdaptationAction {
    ChangeTaskAdaptationLevel { task_id: String, new_level: AdaptationLevel },
    ChangeQualityLevel { new_level: usize },
    ActivateTask { task_id: String },
    DeactivateTask { task_id: String },
    AdjustTaskPriority { task_id: String, new_priority: usize },
}

struct AdaptationEvent {
    timestamp: Instant,
    trigger: String,
    strategy_applied: String,
    actions_taken: Vec<AdaptationAction>,
    result_quality: f64,
}

struct PerformanceMonitor {
    task_statistics: HashMap<String, TaskStatistics>,
    system_load_history: Vec<(Instant, f64)>,
    quality_history: Vec<(Instant, f64)>,
}

struct TaskStatistics {
    execution_times: Vec<Duration>,
    completion_times: Vec<(Instant, Duration)>, // (完成时间，执行时间)
    deadline_misses: Vec<(Instant, Duration)>, // (错过时间，超出量)
    utility_values: Vec<f64>,
}

impl SoftRealTimeSystem {
    fn new(
        scheduler: Box<dyn SoftRealTimeScheduler>,
        initial_quality_level: usize,
        min_acceptable_quality: f64,
    ) -> Self {
        SoftRealTimeSystem {
            tasks: Vec::new(),
            scheduler,
            qos_manager: QoSManager {
                quality_levels: Vec::new(),
                current_level: initial_quality_level,
                degradation_policy: DegradationPolicy::ImportanceBased,
                min_acceptable_quality,
            },
            adaptation_manager: AdaptationManager {
                triggers: Vec::new(),
                strategies: HashMap::new(),
                adaptation_history: Vec::new(),
            },
            performance_monitor: PerformanceMonitor {
                task_statistics: HashMap::new(),
                system_load_history: Vec::new(),
                quality_history: Vec::new(),
            },
        }
    }
    
    fn add_task(&mut self, task: SoftRealTimeTask) {
        // 添加任务到系统
        self.tasks.push(task.clone());
        
        // 初始化任务统计
        self.performance_monitor.task_statistics.insert(
            task.id.clone(),
            TaskStatistics {
                execution_times: Vec::new(),
                completion_times: Vec::new(),
                deadline_misses: Vec::new(),
                utility_values: Vec::new(),
            },
        );
    }
    
    fn add_quality_level(&mut self, level: QualityLevel) {
        self.qos_manager.quality_levels.push(level);
    }
    
    fn add_adaptation_trigger(&mut self, trigger: AdaptationTrigger) {
        self.adaptation_manager.triggers.push(trigger);
    }
    
    fn add_adaptation_strategy(&mut self, name: &str, strategy: AdaptationStrategy) {
        self.adaptation_manager.strategies.insert(name.to_string(), strategy);
    }
    
    fn execute_cycle(&mut self) -> Vec<SoftTaskExecutionResult> {
        let current_time = Instant::now();
        let mut results = Vec::new();
        
        // 获取当前系统负载
        let current_load = self.estimate_current_load();
        
        // 记录系统负载
        self.performance_monitor.system_load_history.push((current_time, current_load));
        
        // 检查适应触发器
        self.check_adaptation_triggers();
        
        // 调度任务
        let scheduling_result = self.scheduler.schedule(&self.tasks, current_load);
        
        // 记录当前质量
        self.performance_monitor.quality_history.push((current_time, scheduling_result.expected_quality));
        
        // 确定准备好的任务
        let ready_tasks: Vec<&SoftRealTimeTask> = self.tasks.iter()
            .filter(|task| self.is_task_ready(task, current_time))
            .collect();
        
        // 执行最高优先级的任务
        while let Some(task_id) = self.scheduler.dispatch(&ready_tasks, current_time) {
            let task = self.tasks.iter_mut()
                .find(|t| t.id == task_id)
                .unwrap();
            
            // 获取当前适应级别的处理函数
            let handler = task.adaptation_handlers.get(&task.current_adaptation_level)
                .unwrap_or_else(|| task.adaptation_handlers.get(&AdaptationLevel::Full).unwrap());
            
            // 执行任务
            let start_time = Instant::now();
            let result = handler();
            let end_time = Instant::now();
            let execution_duration = end_time.duration_since(start_time);
            
            // 检查截止期限
            let deadline_time = start_time + task.deadline;
            let deadline_missed = end_time > deadline_time;
            let miss_duration = if deadline_missed {
                end_time.duration_since(deadline_time)
            } else {
                Duration::from_secs(0)
            };
            
            // 计算任务效用
            let utility = (task.utility_function)(execution_duration, task.deadline);
            
            // 更新统计信息
            if let Some(stats) = self.performance_monitor.task_statistics.get_mut(&task.id) {
                stats.execution_times.push(execution_duration);
                stats.completion_times.push((end_time, execution_duration));
                stats.utility_values.push(utility);
                
                if deadline_missed {
                    stats.deadline_misses.push((end_time, miss_duration));
                    
                    // 通知调度器截止期限错过
                    let miss_severity = miss_duration.as_secs_f64() / task.deadline.as_secs_f64();
                    self.scheduler.handle_deadline_miss(&task.id, miss_severity);
                }
            }
            
            // 记录结果
            results.push(SoftTaskExecutionResult {
                task_id: task.id.clone(),
                execution_time: execution_duration,
                deadline_missed,
                miss_duration,
                utility,
                adaptation_level: task.current_adaptation_level.clone(),
                success: result.success,
                message: result.message,
            });
        }
        
        results
    }
    
    fn is_task_ready(&self, task: &SoftRealTimeTask, current_time: Instant) -> bool {
        // 检查任务是否准备好执行
        // 简化实现
        true
    }
    
    fn estimate_current_load(&self) -> f64 {
        // 估计当前系统负载
        // 简化实现，使用最近的执行时间与WCET比例
        
        let mut total_load = 0.0;
        let mut task_count = 0;
        
        for (task_id, stats) in &self.performance_monitor.task_statistics {
            if let Some(task) = self.tasks.iter().find(|t| &t.id == task_id) {
                if let Some(recent_times) = stats.execution_times.iter().rev().take(5).collect::<Vec<_>>().last() {
                    let expected_time = match &task.execution_time_distribution {
                        ExecutionTimeDistribution::Constant(duration) => *duration,
                        ExecutionTimeDistribution::Uniform { min, max } => (*min + *max) / 2,
                        ExecutionTimeDistribution::Normal { mean, std_dev: _ } => *mean,
                        ExecutionTimeDistribution::Empirical { samples } => {
                            if samples.is_empty() {
                                Duration::from_secs(0)
                            } else {
                                samples.iter().sum::<Duration>() / samples.len() as u32
                            }
                        },
                    };
                    
                    let load_factor = recent_times.as_secs_f64() / expected_time.as_secs_f64();
                    total_load += load_factor;
                    task_count += 1;
                }
            }
        }
        
        if task_count > 0 {
            total_load / task_count as f64
        } else {
            0.0
        }
    }
    
    fn check_adaptation_triggers(&mut self) {
        let current_time = Instant::now();
        let current_load = self.estimate_current_load();
        let current_quality = self.get_current_quality();
        
        let mut triggered_adaptations = Vec::new();
        
        for trigger in &self.adaptation_manager.triggers {
            match trigger {
                AdaptationTrigger::LoadThreshold { threshold, direction } => {
                    match direction {
                        ThresholdDirection::Above if current_load > *threshold => {
                            triggered_adaptations.push("负载过高".to_string());
                        },
                        ThresholdDirection::Below if current_load < *threshold => {
                            triggered_adaptations.push("负载过低".to_string());
                        },
                        _ => {},
                    }
                },
                AdaptationTrigger::DeadlineMissRate { task_id, threshold } => {
                    if let Some(stats) = self.performance_monitor.task_statistics.get(task_id) {
                        let total_executions = stats.completion_times.len();
                        let total_misses = stats.deadline_misses.len();
                        
                        if total_executions > 0 {
                            let miss_rate = total_misses as f64 / total_executions as f64;
                            if miss_rate > *threshold {
                                triggered_adaptations.push(format!("任务'{}'截止期限错过率过高", task_id));
                            }
                        }
                    }
                },
                AdaptationTrigger::QualityThreshold { threshold, direction } => {
                    match direction {
                        ThresholdDirection::Below if current_quality < *threshold => {
                            triggered_adaptations.push("质量低于阈值".to_string());
                        },
                        ThresholdDirection::Above if current_quality > *threshold => {
                            triggered_adaptations.push("质量高于阈值".to_string());
                        },
                        _ => {},
                    }
                },
                AdaptationTrigger::ExternalEvent { event_type } => {
                    // 外部事件需要通过其他方式触发
                    // 简化实现
                },
            }
        }
        
        // 如果有触发的适应性策略，应用相应的策略
        for trigger in triggered_adaptations {
            self.apply_adaptation_strategy(&trigger);
        }
    }
    
    fn apply_adaptation_strategy(&mut self, trigger: &str) {
        // 简化实现，选择第一个可用的策略
        let strategy_name = match trigger {
            "负载过高" => "降低质量",
            "质量低于阈值" => "最小化功能",
            _ => "默认适应",
        };
        
        if let Some(strategy) = self.adaptation_manager.strategies.get(strategy_name) {
            let mut actions_taken = Vec::new();
            
            // 应用策略中的所有动作
            for action in &strategy.actions {
                match action {
                    AdaptationAction::ChangeTaskAdaptationLevel { task_id, new_level } => {
                        if let Some(task) = self.tasks.iter_mut().find(|t| t.id == *task_id) {
                            task.current_adaptation_level = new_level.clone();
                            actions_taken.push(action.clone());
                        }
                    },
                    AdaptationAction::ChangeQualityLevel { new_level } => {
                        if *new_level < self.qos_manager.quality_levels.len() {
                            self.qos_manager.current_level = *new_level;
                            
                            // 应用新质量级别的任务适应级别
                            let quality_level = &self.qos_manager.quality_levels[*new_level];
                            
                            for (task_id, level) in &quality_level.task_adaptation_levels {
                                if let Some(task) = self.tasks.iter_mut().find(|t| t.id == *task_id) {
                                    task.current_adaptation_level = level.clone();
                                }
                            }
                            
                            actions_taken.push(action.clone());
                        }
                    },
                    _ => {
                        // 处理其他类型的动作
                        actions_taken.push(action.clone());
                    }
                }
            }
            
            // 记录适应事件
            self.adaptation_manager.adaptation_history.push(AdaptationEvent {
                timestamp: Instant::now(),
                trigger: trigger.to_string(),
                strategy_applied: strategy_name.to_string(),
                actions_taken,
                result_quality: self.get_current_quality(),
            });
        }
    }
    
    fn get_current_quality(&self) -> f64 {
        // 简化实现，返回当前质量级别的预期质量
        if self.qos_manager.current_level < self.qos_manager.quality_levels.len() {
            self.qos_manager.quality_levels[self.qos_manager.current_level].expected_quality
        } else {
            0.0
        }
    }
    
    fn generate_performance_report(&self) -> PerformanceReport {
        let mut task_reports = HashMap::new();
        
        for task in &self.tasks {
            if let Some(stats) = self.performance_monitor.task_statistics.get(&task.id) {
                let total_executions = stats.completion_times.len();
                let deadline_misses = stats.deadline_misses.len();
                
                let miss_rate = if total_executions > 0 {
                    deadline_misses as f64 / total_executions as f64
                } else {
                    0.0
                };
                
                let avg_utility = if !stats.utility_values.is_empty() {
                    stats.utility_values.iter().sum::<f64>() / stats.utility_values.len() as f64
                } else {
                    0.0
                };
                
                let avg_execution_time = if !stats.execution_times.is_empty() {
                    let sum: Duration = stats.execution_times.iter().sum();
                    sum / stats.execution_times.len() as u32
                } else {
                    Duration::from_secs(0)
                };
                
                let report = TaskPerformanceReport {
                    task_id: task.id.clone(),
                    total_executions,
                    deadline_misses,
                    miss_rate,
                    avg_utility,
                    avg_execution_time,
                    current_adaptation_level: task.current_adaptation_level.clone(),
                };
                
                task_reports.insert(task.id.clone(), report);
            }
        }
        
        PerformanceReport {
            task_reports,
            current_quality_level: self.qos_manager.current_level,
            expected_quality: self.get_current_quality(),
            adaptation_count: self.adaptation_manager.adaptation_history.len(),
        }
    }
}

struct SoftTaskExecutionResult {
    task_id: String,
    execution_time: Duration,
    deadline_missed: bool,
    miss_duration: Duration,
    utility: f64,
    adaptation_level: AdaptationLevel,
    success: bool,
    message: Option<String>,
}

struct PerformanceReport {
    task_reports: HashMap<String, TaskPerformanceReport>,
    current_quality_level: usize,
    expected_quality: f64,
    adaptation_count: usize,
}

struct TaskPerformanceReport {
    task_id: String,
    total_executions: usize,
    deadline_misses: usize,
    miss_rate: f64,
    avg_utility: f64,
    avg_execution_time: Duration,
    current_adaptation_level: AdaptationLevel,
}
```

### 3.3 调度理论

调度理论提供了分配资源和时间的数学框架，支持各种实时约束和优化目标。

```rust
// 调度理论框架
struct SchedulingTheory {
    models: Vec<SchedulingModel>,
    algorithms: HashMap<String, Box<dyn SchedulingAlgorithm>>,
    analysis_techniques: Vec<Box<dyn SchedulabilityAnalysis>>,
}

struct SchedulingModel {
    name: String,
    task_model: TaskModel,
    processor_model: ProcessorModel,
    preemption_model: PreemptionModel,
    synchronization_model: Option<SynchronizationModel>,
}

enum TaskModel {
    PeriodicTasks { implicit_deadlines: bool },
    SporadicTasks { min_interarrival: bool },
    AperiodicTasks,
    MixedTasks,
    DAGTasks, // 有向无环图任务模型
}

enum ProcessorModel {
    Uniprocessor,
    Identical { count: usize },
    Uniform { processors: Vec<f64> }, // 处理速度向量
    Unrelated { speed_matrix: Vec<Vec<f64>> }, // 任务-处理器速度矩阵
}

enum PreemptionModel {
    FullyPreemptive,
    NonPreemptive,
    LimitedPreemption { preemption_points: PreemptionPointType },
}

enum PreemptionPointType {
    Fixed,
    Floating,
}

struct SynchronizationModel {
    resource_types: Vec<String>,
    protocol: SynchronizationProtocol,
    critical_sections: Vec<CriticalSection>,
}

enum SynchronizationProtocol {
    PIP, // 优先级继承协议
    PCP, // 优先级上限协议
    SRP, // 栈资源策略
    MPCP, // 多处理器优先级上限协议
    FMLP, // 灵活多处理器锁协议
}

struct CriticalSection {
    task_id: String,
    resource_id: String,
    duration: Duration,
}

trait SchedulingAlgorithm {
    fn name(&self) -> &str;
    fn description(&self) -> &str;
    fn is_optimal(&self, model: &SchedulingModel) -> bool;
    fn worst_case_utilization_bound(&self, model: &SchedulingModel) -> Option<f64>;
    fn schedule(&self, tasks: &[GenericTask], processors: usize, time_horizon: Duration) -> ScheduleResult;
}

trait SchedulabilityAnalysis {
    fn name(&self) -> &str;
    fn analyze(&self, tasks: &[GenericTask], model: &SchedulingModel) -> AnalysisResult;
    fn is_exact(&self) -> bool;
    fn is_sufficient(&self) -> bool;
    fn is_necessary(&self) -> bool;
}

struct GenericTask {
    id: String,
    wcet: Duration,
    period: Option<Duration>,
    deadline: Duration,
    offset: Duration,
    jitter: Duration,
    criticality: usize,
    dependencies: Vec<String>,
    resources: Vec<(String, Duration)>, // (资源ID, 持有时间)
}

struct ScheduleResult {
    is_schedulable: bool,
    schedule: HashMap<String, Vec<(Duration, Duration)>>, // 任务ID -> [(开始时间, 结束时间)]
    processor_assignments: HashMap<String, usize>, // 任务ID -> 处理器ID
    response_times: HashMap<String, Duration>, // 任务ID -> 响应时间
    utilization: f64,
}

struct AnalysisResult {
    is_schedulable: bool,
    response_time_bounds: HashMap<String, Duration>, // 任务ID -> 响应时间上界
    utilization: f64,
    details: HashMap<String, String>, // 分析细节
}

impl SchedulingTheory {
    fn new() -> Self {
        SchedulingTheory {
            models: Vec::new(),
            algorithms: HashMap::new(),
            analysis_techniques: Vec::new(),
        }
    }
    
    fn add_model(&mut self, model: SchedulingModel) {
        self.models.push(model);
    }
    
    fn add_algorithm(&mut self, algorithm: Box<dyn SchedulingAlgorithm>) {
        self.algorithms.insert(algorithm.name().to_string(), algorithm);
    }
    
    fn add_analysis_technique(&mut self, technique: Box<dyn SchedulabilityAnalysis>) {
        self.analysis_techniques.push(technique);
    }
    
    fn find_optimal_algorithms(&self, model: &SchedulingModel) -> Vec<String> {
        self.algorithms.iter()
            .filter(|(_, alg)| alg.is_optimal(model))
            .map(|(name, _)| name.clone())
            .collect()
    }
    
    fn analyze_schedulability(&self, tasks: &[GenericTask], model: &SchedulingModel) -> HashMap<String, AnalysisResult> {
        let mut results = HashMap::new();
        
        for technique in &self.analysis_techniques {
            let result = technique.analyze(tasks, model);
            results.insert(technique.name().to_string(), result);
        }
        
        results
    }
    
    fn generate_schedule(&self, tasks: &[GenericTask], model: &SchedulingModel, algorithm_name: &str, time_horizon: Duration) -> Option<ScheduleResult> {
        let processor_count = match model.processor_model {
            ProcessorModel::Uniprocessor => 1,
            ProcessorModel::Identical { count } => count,
            ProcessorModel::Uniform { ref processors } => processors.len(),
            ProcessorModel::Unrelated { ref speed_matrix } => {
                if speed_matrix.is_empty() { 0 } else { speed_matrix[0].len() }
            },
        };
        
        if let Some(algorithm) = self.algorithms.get(algorithm_name) {
            Some(algorithm.schedule(tasks, processor_count, time_horizon))
        } else {
            None
        }
    }
    
    fn compare_algorithms(&self, tasks: &[GenericTask], model: &SchedulingModel, algorithms: &[&str], time_horizon: Duration) -> HashMap<String, AlgorithmComparison> {
        let mut results = HashMap::new();
        
        for &alg_name in algorithms {
            if let Some(algorithm) = self.algorithms.get(alg_name) {
                let processor_count = match model.processor_model {
                    ProcessorModel::Uniprocessor => 1,
                    ProcessorModel::Identical { count } => count,
                    ProcessorModel::Uniform { ref processors } => processors.len(),
                    ProcessorModel::Unrelated { ref speed_matrix } => {
                        if speed_matrix.is_empty() { 0 } else { speed_matrix[0].len() }
                    },
                };
                
                // 测量调度时间
                let start_time = Instant::now();
                let schedule_result = algorithm.schedule(tasks, processor_count, time_horizon);
                let scheduling_time = start_time.elapsed();
                
                // 计算平均响应时间
                let avg_response_time = if !schedule_result.response_times.is_empty() {
                    let sum: Duration = schedule_result.response_times.values().sum();
                    sum / schedule_result.response_times.len() as u32
                } else {
                    Duration::from_secs(0)
                };
                
                // 计算任务集可调度的子集大小
                let schedulable_subset = schedule_result.response_times.iter()
                    .filter(|(_, &rt)| {
                        if let Some(task) = tasks.iter().find(|t| t.id == **_) {
                            rt <= task.deadline
                        } else {
                            false
                        }
                    })
                    .count();
                
                results.insert(alg_name.to_string(), AlgorithmComparison {
                    algorithm_name: alg_name.to_string(),
                    is_schedulable: schedule_result.is_schedulable,
                    utilization: schedule_result.utilization,
                    avg_response_time,
                    scheduling_time,
                    schedulable_subset,
                    total_tasks: tasks.len(),
                });
            }
        }
        
        results
    }
    
    fn find_minimal_speed_scaling(&self, tasks: &[GenericTask], model: &SchedulingModel, algorithm_name: &str) -> Option<f64> {
        if let Some(algorithm) = self.algorithms.get(algorithm_name) {
            // 二分查找最小处理器速度
            let mut lower_bound = 0.1;
            let mut upper_bound = 10.0;
            let epsilon = 0.01;
            
            while upper_bound - lower_bound > epsilon {
                let mid = (lower_bound + upper_bound) / 2.0;
                
                // 创建缩放后的任务
                let scaled_tasks: Vec<GenericTask> = tasks.iter().map(|task| {
                    let mut scaled_task = task.clone();
                    scaled_task.wcet = Duration::from_secs_f64(task.wcet.as_secs_f64() / mid);
                    scaled_task
                }).collect();
                
                // 检查可调度性
                let processor_count = match model.processor_model {
                    ProcessorModel::Uniprocessor => 1,
                    ProcessorModel::Identical { count } => count,
                    ProcessorModel::Uniform { ref processors } => processors.len(),
                    ProcessorModel::Unrelated { ref speed_matrix } => {
                        if speed_matrix.is_empty() { 0 } else { speed_matrix[0].len() }
                    },
                };
                
                let result = algorithm.schedule(&scaled_tasks, processor_count, Duration::from_secs(3600));
                
                if result.is_schedulable {
                    upper_bound = mid;
                } else {
                    lower_bound = mid;
                }
            }
            
            Some(upper_bound)
        } else {
            None
        }
    }
}

struct AlgorithmComparison {
    algorithm_name: String,
    is_schedulable: bool,
    utilization: f64,
    avg_response_time: Duration,
    scheduling_time: Duration,
    schedulable_subset: usize,
    total_tasks: usize,
}

// 具体的调度算法实现

// 速率单调调度
struct RateMonotonicAlgorithm;

impl SchedulingAlgorithm for RateMonotonicAlgorithm {
    fn name(&self) -> &str {
        "速率单调"
    }
    
    fn description(&self) -> &str {
        "为周期性任务分配固定优先级，周期越短优先级越高"
    }
    
    fn is_optimal(&self, model: &SchedulingModel) -> bool {
        match (&model.task_model, &model.processor_model, &model.preemption_model) {
            (TaskModel::PeriodicTasks { implicit_deadlines: true }, 
             ProcessorModel::Uniprocessor, 
             PreemptionModel::FullyPreemptive) => true,
            _ => false,
        }
    }
    
    fn worst_case_utilization_bound(&self, model: &SchedulingModel) -> Option<f64> {
        match (&model.task_model, &model.processor_model) {
            (TaskModel::PeriodicTasks { .. }, ProcessorModel::Uniprocessor) => {
                // Liu & Layland 界限: n * (2^(1/n) - 1)
                Some(0.693) // 当n趋向无穷时的极限
            },
            _ => None,
        }
    }
    
    fn schedule(&self, tasks: &[GenericTask], processors: usize, time_horizon: Duration) -> ScheduleResult {
        if processors != 1 {
            return ScheduleResult {
                is_schedulable: false,
                schedule: HashMap::new(),
                processor_assignments: HashMap::new(),
                response_times: HashMap::new(),
                utilization: 0.0,
            };
        }
        
        // 按周期排序
        let mut sorted_tasks = tasks.to_vec();
        sorted_tasks.sort_by(|a, b| {
            a.period.unwrap_or(Duration::from_secs(0))
                .cmp(&b.period.unwrap_or(Duration::from_secs(0)))
        });
        
        // 计算响应时间
        let mut response_times = HashMap::new();
        let mut is_schedulable = true;
        
        for (i, task) in sorted_tasks.iter().enumerate() {
            let mut response_time = task.wcet;
            
            // 响应时间分析
            loop {
                let mut new_response_time = task.wcet;
                
                // 来自高优先级任务的干扰
                for j in 0..i {
                    let hp_task = &sorted_tasks[j];
                    let period = hp_task.period.unwrap_or(Duration::from_secs(0));
                    
                    if period.as_nanos() == 0 {
                        continue;
                    }
                    
                    // 计算干扰: ceil(R/T) * C
                    let num_jobs = (response_time.as_nanos() + period.as_nanos() - 1) / period.as_nanos();
                    let interference = Duration::from_nanos((num_jobs * hp_task.wcet.as_nanos()) as u64);
                    
                    new_response_time += interference;
                }
                
                if new_response_time == response_time {
                    // 收敛
                    break;
                }
                
                if new_response_time > task.deadline {
                    // 不可调度
                    is_schedulable = false;
                    break;
                }
                
                response_time = new_response_time;
            }
            
            response_times.insert(task.id.clone(), response_time);
        }
        
        // 计算利用率
        let utilization = tasks.iter()
            .filter_map(|task| {
                if let Some(period) = task.period {
                    if period.as_secs_f64() > 0.0 {
                        Some(task.wcet.as_secs_f64() / period.as_secs_f64())
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .sum();
        
        // 生成调度
        let mut schedule = HashMap::new();
        
        // 简化模拟调度
        // 实际调度生成是复杂的，这里只是示例
        
        // 分配处理器（单处理器情况简单）
        let processor_assignments = sorted_tasks.iter()
            .map(|task| (task.id.clone(), 0))
            .collect();
        
        ScheduleResult {
            is_schedulable,
            schedule,
            processor_assignments,
            response_times,
            utilization,
        }
    }
}

// 最早截止期限优先算法
struct EarliestDeadlineFirstAlgorithm;

impl SchedulingAlgorithm for EarliestDeadlineFirstAlgorithm {
    fn name(&self) -> &str {
        "最早截止期限优先"
    }
    
    fn description(&self) -> &str {
        "动态优先级算法，截止期限越早优先级越高"
    }
    
    fn is_optimal(&self, model: &SchedulingModel) -> bool {
        match (&model.processor_model, &model.preemption_model) {
            (ProcessorModel::Uniprocessor, PreemptionModel::FullyPreemptive) => true,
            _ => false,
        }
    }
    
    fn worst_case_utilization_bound(&self, model: &SchedulingModel) -> Option<f64> {
        match (&model.task_model, &model.processor_model) {
            (TaskModel::PeriodicTasks { .. }, ProcessorModel::Uniprocessor) => {
                // EDF可以达到100%的利用率（对于隐式截止期限的周期任务）
                Some(1.0)
            },
            _ => None,
        }
    }
    
    fn schedule(&self, tasks: &[GenericTask], processors: usize, time_horizon: Duration) -> ScheduleResult {
        // EDF算法实现（简化版）
        if processors != 1 {
            // 多处理器EDF实现更复杂
            return ScheduleResult {
                is_schedulable: false,
                schedule: HashMap::new(),
                processor_assignments: HashMap::new(),
                response_times: HashMap::new(),
                utilization: 0.0,
            };
        }
        
        // 计算利用率
        let utilization: f64 = tasks.iter()
            .filter_map(|task| {
                if let Some(period) = task.period {
                    if period.as_secs_f64() > 0.0 {
                        Some(task.wcet.as_secs_f64() / period.as_secs_f64())
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .sum();
        
        // 对于EDF，如果利用率<=1，则可调度（对于隐式截止期限的周期任务）
        let is_schedulable = utilization <= 1.0;
        
        // 模拟EDF算法（简化）
        let mut schedule = HashMap::new();
        let mut response_times = HashMap::new();
        
        // 处理器分配（单处理器简单）
        let processor_assignments = tasks.iter()
            .map(|task| (task.id.clone(), 0))
            .collect();
        
        // 在此处应添加实际的EDF调度生成和响应时间分析
        // 简化实现
        
        ScheduleResult {
            is_schedulable,
            schedule,
            processor_assignments,
            response_times,
            utilization,
        }
    }
}

// 最小松弛时间优先算法
struct LeastLaxityFirstAlgorithm;

impl SchedulingAlgorithm for LeastLaxityFirstAlgorithm {
    fn name(&self) -> &str {
        "最小松弛时间优先"
    }
    
    fn description(&self) -> &str {
        "动态优先级算法，松弛时间（截止期限-剩余执行时间）越小优先级越高"
    }
    
    fn is_optimal(&self, model: &SchedulingModel) -> bool {
        match (&model.processor_model, &model.preemption_model) {
            (ProcessorModel::Uniprocessor, PreemptionModel::FullyPreemptive) => true,
            _ => false,
        }
    }
    
    fn worst_case_utilization_bound(&self, model: &SchedulingModel) -> Option<f64> {
        match (&model.task_model, &model.processor_model) {
            (TaskModel::PeriodicTasks { .. }, ProcessorModel::Uniprocessor) => {
                // LLF也可以达到100%的利用率
                Some(1.0)
            },
            _ => None,
        }
    }
    
    fn schedule(&self, tasks: &[GenericTask], processors: usize, time_horizon: Duration) -> ScheduleResult {
        // LLF算法实现（简化版）
        // ...省略具体实现
        
        ScheduleResult {
            is_schedulable: false,
            schedule: HashMap::new(),
            processor_assignments: HashMap::new(),
            response_times: HashMap::new(),
            utilization: 0.0,
        }
    }
}

// 响应时间分析
struct ResponseTimeAnalysis;

impl SchedulabilityAnalysis for ResponseTimeAnalysis {
    fn name(&self) -> &str {
        "响应时间分析"
    }
    
    fn analyze(&self, tasks: &[GenericTask], model: &SchedulingModel) -> AnalysisResult {
        match (&model.task_model, &model.processor_model, &model.preemption_model) {
            (_, ProcessorModel::Uniprocessor, PreemptionModel::FullyPreemptive) => {
                // 进行单处理器响应时间分析
                let mut response_time_bounds = HashMap::new();
                let mut is_schedulable = true;
                
                // 按优先级排序（假设速率单调优先级分配）
                let mut sorted_tasks = tasks.to_vec();
                sorted_tasks.sort_by(|a, b| {
                    a.period.unwrap_or(Duration::from_secs(0))
                        .cmp(&b.period.unwrap_or(Duration::from_secs(0)))
                });
                
                // 计算每个任务的响应时间
                for (i, task) in sorted_tasks.iter().enumerate() {
                    let mut response_time = task.wcet;
                    
                    loop {
                        let mut new_response_time = task.wcet;
                        
                        // 计算来自高优先级任务的干扰
                        for j in 0..i {
                            let hp_task = &sorted_tasks[j];
                            let period = hp_task.period.unwrap_or(Duration::from_secs(0));
                            
                            if period.as_nanos() == 0 {
                                continue;
                            }
                            
                            // 计算干扰: ceil(R/T) * C
                            let num_jobs = (response_time.as_nanos() + period.as_nanos() - 1) / period.as_nanos();
                            let interference = Duration::from_nanos((num_jobs * hp_task.wcet.as_nanos()) as u64);
                            
                            new_response_time += interference;
                        }
                        
                        if new_response_time == response_time {
                            // 响应时间收敛
                            break;
                        }
                        
                        if new_response_time > task.deadline {
                            // 不可调度
                            is_schedulable = false;
                            response_time = task.deadline + Duration::from_secs(1); // 超过截止期限
                            break;
                        }
                        
                        response_time = new_response_time;
                    }
                    
                    response_time_bounds.insert(task.id.clone(), response_time);
                }
                
                // 计算利用率
                let utilization = tasks.iter()
                    .filter_map(|task| {
                        if let Some(period) = task.period {
                            if period.as_secs_f64() > 0.0 {
                                Some(task.wcet.as_secs_f64() / period.as_secs_f64())
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    })
                    .sum();
                
                // 分析详情
                let mut details = HashMap::new();
                for task in tasks {
                    if let Some(rt) = response_time_bounds.get(&task.id) {
                        let is_task_schedulable = *rt <= task.deadline;
                        details.insert(
                            task.id.clone(),
                            format!("WCET: {:?}, 周期: {:?}, 截止期限: {:?}, 响应时间: {:?}, 可调度: {}",
                                  task.wcet, task.period, task.deadline, rt, is_task_schedulable)
                        );
                    }
                }
                
                AnalysisResult {
                    is_schedulable,
                    response_time_bounds,
                    utilization,
                    details,
                }
                
            },
            _ => {
                // 不支持的模型
                AnalysisResult {
                    is_schedulable: false,
                    response_time_bounds: HashMap::new(),
                    utilization: 0.0,
                    details: HashMap::new(),
                }
            }
        }
    }
    
    fn is_exact(&self) -> bool {
        true // 对于单处理器固定优先级调度，响应时间分析是精确的
    }
    
    fn is_sufficient(&self) -> bool {
        true
    }
    
    fn is_necessary(&self) -> bool {
        true
    }
}

// 利用率界限分析
struct UtilizationBoundAnalysis;

impl SchedulabilityAnalysis for UtilizationBoundAnalysis {
    fn name(&self) -> &str {
        "利用率界限分析"
    }
    
    fn analyze(&self, tasks: &[GenericTask], model: &SchedulingModel) -> AnalysisResult {
        // 计算利用率
        let utilization = tasks.iter()
            .filter_map(|task| {
                if let Some(period) = task.period {
                    if period.as_secs_f64() > 0.0 {
                        Some(task.wcet.as_secs_f64() / period.as_secs_f64())
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .sum();
        
        let mut is_schedulable = false;
        let mut details = HashMap::new();
        
        match (&model.task_model, &model.processor_model) {
            (TaskModel::PeriodicTasks { implicit_deadlines: true }, ProcessorModel::Uniprocessor) => {
                let n = tasks.len() as f64;
                let rm_bound = n * (2.0_f64.powf(1.0 / n) - 1.0);
                let edf_bound = 1.0;
                
                details.insert("RM界限".to_string(), format!("{:.4}", rm_bound));
                details.insert("EDF界限".to_string(), format!("{:.4}", edf_bound));
                details.insert("实际利用率".to_string(), format!("{:.4}", utilization));
                
                is_schedulable = utilization <= rm_bound; // 假设使用RM调度
            },
            _ => {
                details.insert("错误".to_string(), "不支持此调度模型".to_string());
            }
        }
        
        // 简化响应时间计算（不实际计算，只返回估计值）
        let response_time_bounds = tasks.iter()
            .map(|task| {
                (task.id.clone(), task.wcet * (1.0 / (1.0 - utilization)).ceil() as u32)
            })
            .collect();
        
        AnalysisResult {
            is_schedulable,
            response_time_bounds,
            utilization,
            details,
        }
    }
    
    fn is_exact(&self) -> bool {
        false // 利用率测试通常是充分而非必要的
    }
    
    fn is_sufficient(&self) -> bool {
        true
    }
    
    fn is_necessary(&self) -> bool {
        false
    }
}

// 需求界限函数分析
struct DemandBoundAnalysis;

impl SchedulabilityAnalysis for DemandBoundAnalysis {
    fn name(&self) -> &str {
        "需求界限函数分析"
    }
    
    fn analyze(&self, tasks: &[GenericTask], model: &SchedulingModel) -> AnalysisResult {
        // DBF分析适用于EDF调度
        // 对于每个时间点t，检查所有任务在[0,t]内的处理器需求是否超过t
        
        let mut is_schedulable = true;
        let mut details = HashMap::new();
        
        match (&model.task_model, &model.processor_model, &model.preemption_model) {
            (TaskModel::PeriodicTasks { .. }, ProcessorModel::Uniprocessor, PreemptionModel::FullyPreemptive) => {
                // 对于周期任务，可以使用超周期作为DBF检查的上界
                let hyperperiod = calculate_hyperperiod(tasks);
                
                // 检查系统是否可调度
                let utilization = calculate_utilization(tasks);
                
                if utilization > 1.0 {
                    is_schedulable = false;
                    details.insert("错误".to_string(), format!("利用率 {:.4} 超过100%", utilization));
                } else {
                    // 在[0, hyperperiod]范围内的所有截止期限点检查DBF
                    // 简化实现，实际应检查所有截止期限点
                    
                    is_schedulable = true; // 假设测试通过
                    details.insert("信息".to_string(), format!("利用率 {:.4} <= 1.0", utilization));
                }
            },
            _ => {
                details.insert("错误".to_string(), "不支持此调度模型".to_string());
                is_schedulable = false;
            }
        }
        
        // 估计响应时间（简化）
        let response_time_bounds = tasks.iter()
            .map(|task| (task.id.clone(), task.deadline))
            .collect();
        
        AnalysisResult {
            is_schedulable,
            response_time_bounds,
            utilization: calculate_utilization(tasks),
            details,
        }
    }
    
    fn is_exact(&self) -> bool {
        true // 对于EDF调度，DBF分析是精确的
    }
    
    fn is_sufficient(&self) -> bool {
        true
    }
    
    fn is_necessary(&self) -> bool {
        true
    }
}

// 工具函数
fn calculate_hyperperiod(tasks: &[GenericTask]) -> Duration {
    // 计算任务集的超周期（所有周期的最小公倍数）
    // 简化实现
    let max_period = tasks.iter()
        .filter_map(|task| task.period)
        .max()
        .unwrap_or(Duration::from_secs(1));
    
    max_period * 10 // 简化实现，实际应计算LCM
}

fn calculate_utilization(tasks: &[GenericTask]) -> f64 {
    tasks.iter()
        .filter_map(|task| {
            if let Some(period) = task.period {
                if period.as_secs_f64() > 0.0 {
                    Some(task.wcet.as_secs_f64() / period.as_secs_f64())
                } else {
                    None
                }
            } else {
                None
            }
        })
        .sum()
}
```

### 3.4 响应式编程模型

响应式编程模型使系统能够异步地响应事件流和数据变化，提供高效的并发处理。

```rust
// 响应式编程框架
struct ReactiveSystem {
    event_broker: EventBroker,
    reactive_streams: HashMap<String, ReactiveStream>,
    operators: HashMap<String, Box<dyn StreamOperator>>,
    sinks: HashMap<String, Box<dyn Sink>>,
    scheduler: Box<dyn ExecutionScheduler>,
}

struct EventBroker {
    subscriptions: HashMap<String, Vec<Subscription>>,
    event_buffer: VecDeque<Event>,
    dispatcher: Box<dyn EventDispatcher>,
}

struct ReactiveStream {
    id: String,
    source: Box<dyn Source>,
    pipeline: Vec<String>, // 操作符ID序列
    sink_id: Option<String>,
    buffer_strategy: BufferStrategy,
    backpressure_strategy: BackpressureStrategy,
}

trait Source {
    fn name(&self) -> &str;
    fn emit(&mut self) -> Option<Event>;
    fn is_complete(&self) -> bool;
}

trait StreamOperator {
    fn name(&self) -> &str;
    fn process(&self, event: Event) -> Vec<Event>;
    fn on_error(&self, error: ReactiveError) -> ErrorHandlingAction;
}

trait Sink {
    fn name(&self) -> &str;
    fn accept(&mut self, event: Event) -> Result<(), ReactiveError>;
    fn on_complete(&mut self);
}

trait EventDispatcher {
    fn dispatch(&self, event: Event, subscriptions: &[Subscription]) -> DispatchResult;
}

trait ExecutionScheduler {
    fn schedule(&mut self, task: Box<dyn FnOnce() + Send>) -> SchedulingResult;
    fn shutdown(&mut self);
}

struct Event {
    id: Uuid,
    event_type: String,
    payload: Box<dyn Any + Send + Sync>,
    timestamp: Instant,
    origin: String,
    metadata: HashMap<String, String>,
}

struct Subscription {
    id: String,
    subscriber: Box<dyn Fn(Event) -> Result<(), ReactiveError> + Send + Sync>,
    event_filter: Option<Box<dyn Fn(&Event) -> bool + Send + Sync>>,
    priority: usize,
}

enum BufferStrategy {
    Unbounded,
    Bounded(usize),
    Dropping(usize),
    Sliding(usize),
}

enum BackpressureStrategy {
    Block,
    Drop,
    Latest,
    Error,
    Buffer(BufferStrategy),
}

enum ErrorHandlingAction {
    Propagate,
    Recover(Event),
    SkipElement,
    CompleteStream,
}

struct ReactiveError {
    message: String,
    error_type: ReactiveErrorType,
    source: Option<Box<dyn Error + Send + Sync>>,
    context: HashMap<String, String>,
}

enum ReactiveErrorType {
    Overflow,
    Timeout,
    Disconnected,
    InvalidData,
    OperationFailed,
    Cancelled,
}

enum DispatchResult {
    Success(usize), // 成功派发的订阅数
    Partial(usize, Vec<ReactiveError>), // 部分成功、部分失败
    Failed(ReactiveError),
}

enum SchedulingResult {
    Scheduled,
    Rejected,
    Queued,
}

impl ReactiveSystem {
    fn new(scheduler: Box<dyn ExecutionScheduler>) -> Self {
        ReactiveSystem {
            event_broker: EventBroker {
                subscriptions: HashMap::new(),
                event_buffer: VecDeque::new(),
                dispatcher: Box::new(AsyncEventDispatcher::new()),
            },
            reactive_streams: HashMap::new(),
            operators: HashMap::new(),
            sinks: HashMap::new(),
            scheduler,
        }
    }
    
    fn create_stream(&mut self, id: &str, source: Box<dyn Source>, buffer_strategy: BufferStrategy) -> Result<(), ReactiveError> {
        if self.reactive_streams.contains_key(id) {
            return Err(ReactiveError {
                message: format!("流 '{}' 已存在", id),
                error_type: ReactiveErrorType::InvalidData,
                source: None,
                context: HashMap::new(),
            });
        }
        
        let stream = ReactiveStream {
            id: id.to_string(),
            source,
            pipeline: Vec::new(),
            sink_id: None,
            buffer_strategy,
            backpressure_strategy: BackpressureStrategy::Block,
        };
        
        self.reactive_streams.insert(id.to_string(), stream);
        
        Ok(())
    }
    
    fn add_operator(&mut self, stream_id: &str, operator_id: &str, operator: Box<dyn StreamOperator>) -> Result<(), ReactiveError> {
        if !self.reactive_streams.contains_key(stream_id) {
            return Err(ReactiveError {
                message: format!("流 '{}' 不存在", stream_id),
                error_type: ReactiveErrorType::InvalidData,
                source: None,
                context: HashMap::new(),
            });
        }
        
        if self.operators.contains_key(operator_id) {
            return Err(ReactiveError {
                message: format!("操作符 '{}' 已存在", operator_id),
                error_type: ReactiveErrorType::InvalidData,
                source: None,
                context: HashMap::new(),
            });
        }
        
        self.operators.insert(operator_id.to_string(), operator);
        
        if let Some(stream) = self.reactive_streams.get_mut(stream_id) {
            stream.pipeline.push(operator_id.to_string());
        }
        
        Ok(())
    }
    
    fn set_sink(&mut self, stream_id: &str, sink_id: &str, sink: Box<dyn Sink>) -> Result<(), ReactiveError> {
        if !self.reactive_streams.contains_key(stream_id) {
            return Err(ReactiveError {
                message: format!("流 '{}' 不存在", stream_id),
                error_type: ReactiveErrorType::InvalidData,
                source: None,
                context: HashMap::new(),
            });
        }
        
        if self.sinks.contains_key(sink_id) {
            return Err(ReactiveError {
                message: format!("接收器 '{}' 已存在", sink_id),
                error_type: ReactiveErrorType::InvalidData,
                source: None

```rust
        if self.sinks.contains_key(sink_id) {
            return Err(ReactiveError {
                message: format!("接收器 '{}' 已存在", sink_id),
                error_type: ReactiveErrorType::InvalidData,
                source: None,
                context: HashMap::new(),
            });
        }
        
        self.sinks.insert(sink_id.to_string(), sink);
        
        if let Some(stream) = self.reactive_streams.get_mut(stream_id) {
            stream.sink_id = Some(sink_id.to_string());
        }
        
        Ok(())
    }
    
    fn set_backpressure_strategy(&mut self, stream_id: &str, strategy: BackpressureStrategy) -> Result<(), ReactiveError> {
        if let Some(stream) = self.reactive_streams.get_mut(stream_id) {
            stream.backpressure_strategy = strategy;
            Ok(())
        } else {
            Err(ReactiveError {
                message: format!("流 '{}' 不存在", stream_id),
                error_type: ReactiveErrorType::InvalidData,
                source: None,
                context: HashMap::new(),
            })
        }
    }
    
    fn subscribe(&mut self, event_type: &str, subscription: Subscription) -> Result<(), ReactiveError> {
        self.event_broker.subscriptions
            .entry(event_type.to_string())
            .or_insert_with(Vec::new)
            .push(subscription);
            
        Ok(())
    }
    
    fn publish(&mut self, event: Event) -> Result<DispatchResult, ReactiveError> {
        // 检查是否有对此事件类型的订阅
        if let Some(subscriptions) = self.event_broker.subscriptions.get(&event.event_type) {
            // 使用调度器进行事件分发
            let dispatcher = &self.event_broker.dispatcher;
            let result = dispatcher.dispatch(event, subscriptions);
            Ok(result)
        } else {
            // 没有订阅此事件类型
            self.event_broker.event_buffer.push_back(event);
            Ok(DispatchResult::Success(0))
        }
    }
    
    fn start_stream(&mut self, stream_id: &str) -> Result<(), ReactiveError> {
        if !self.reactive_streams.contains_key(stream_id) {
            return Err(ReactiveError {
                message: format!("流 '{}' 不存在", stream_id),
                error_type: ReactiveErrorType::InvalidData,
                source: None,
                context: HashMap::new(),
            });
        }
        
        // 从流中克隆所需信息，避免借用冲突
        let stream_clone = self.reactive_streams.get(stream_id).unwrap().clone();
        let operators_clone = self.operators.clone();
        let sinks_clone = self.sinks.clone();
        
        // 创建处理任务
        let task = Box::new(move || {
            // 简化版流处理逻辑
            let mut source = stream_clone.source;
            
            while let Some(event) = source.emit() {
                let mut current_events = vec![event];
                
                // 应用管道中的每个操作符
                for operator_id in &stream_clone.pipeline {
                    if let Some(operator) = operators_clone.get(operator_id) {
                        // 处理当前事件批次
                        let mut next_events = Vec::new();
                        
                        for event in current_events {
                            let results = operator.process(event);
                            next_events.extend(results);
                        }
                        
                        current_events = next_events;
                    }
                }
                
                // 将最终事件发送到接收器
                if let Some(sink_id) = &stream_clone.sink_id {
                    if let Some(mut sink) = sinks_clone.get(sink_id) {
                        for event in current_events {
                            if let Err(error) = sink.accept(event) {
                                // 处理错误
                                println!("接收器错误: {}", error.message);
                            }
                        }
                    }
                }
                
                // 如果源已完成，退出循环
                if source.is_complete() {
                    break;
                }
            }
            
            // 流处理完成，通知接收器
            if let Some(sink_id) = &stream_clone.sink_id {
                if let Some(mut sink) = sinks_clone.get(sink_id) {
                    sink.on_complete();
                }
            }
        });
        
        // 调度任务执行
        let result = self.scheduler.schedule(task);
        
        match result {
            SchedulingResult::Scheduled => Ok(()),
            SchedulingResult::Rejected => Err(ReactiveError {
                message: "无法调度流，调度器拒绝".to_string(),
                error_type: ReactiveErrorType::OperationFailed,
                source: None,
                context: HashMap::new(),
            }),
            SchedulingResult::Queued => Ok(()),
        }
    }
    
    fn shutdown(&mut self) {
        // 关闭调度器
        self.scheduler.shutdown();
    }
}

impl Clone for ReactiveStream {
    fn clone(&self) -> Self {
        ReactiveStream {
            id: self.id.clone(),
            source: self.source.clone(),
            pipeline: self.pipeline.clone(),
            sink_id: self.sink_id.clone(),
            buffer_strategy: self.buffer_strategy.clone(),
            backpressure_strategy: self.backpressure_strategy.clone(),
        }
    }
}

impl Clone for Box<dyn Source> {
    fn clone(&self) -> Self {
        // 这是简化实现，实际应实现正确的克隆
        unimplemented!("Source克隆未实现")
    }
}

impl Clone for Box<dyn StreamOperator> {
    fn clone(&self) -> Self {
        // 这是简化实现，实际应实现正确的克隆
        unimplemented!("StreamOperator克隆未实现")
    }
}

impl Clone for Box<dyn Sink> {
    fn clone(&self) -> Self {
        // 这是简化实现，实际应实现正确的克隆
        unimplemented!("Sink克隆未实现")
    }
}

impl Clone for BufferStrategy {
    fn clone(&self) -> Self {
        match self {
            BufferStrategy::Unbounded => BufferStrategy::Unbounded,
            BufferStrategy::Bounded(size) => BufferStrategy::Bounded(*size),
            BufferStrategy::Dropping(size) => BufferStrategy::Dropping(*size),
            BufferStrategy::Sliding(size) => BufferStrategy::Sliding(*size),
        }
    }
}

impl Clone for BackpressureStrategy {
    fn clone(&self) -> Self {
        match self {
            BackpressureStrategy::Block => BackpressureStrategy::Block,
            BackpressureStrategy::Drop => BackpressureStrategy::Drop,
            BackpressureStrategy::Latest => BackpressureStrategy::Latest,
            BackpressureStrategy::Error => BackpressureStrategy::Error,
            BackpressureStrategy::Buffer(strategy) => BackpressureStrategy::Buffer(strategy.clone()),
        }
    }
}

// 异步事件调度器实现
struct AsyncEventDispatcher {
    thread_pool: ThreadPool,
}

impl AsyncEventDispatcher {
    fn new() -> Self {
        AsyncEventDispatcher {
            thread_pool: ThreadPool::new(4), // 使用4个线程
        }
    }
}

impl EventDispatcher for AsyncEventDispatcher {
    fn dispatch(&self, event: Event, subscriptions: &[Subscription]) -> DispatchResult {
        if subscriptions.is_empty() {
            return DispatchResult::Success(0);
        }
        
        let mut successful_count = 0;
        let mut errors = Vec::new();
        
        // 克隆事件和订阅以在线程间安全传递
        for subscription in subscriptions {
            let event_clone = event.clone();
            let subscriber = subscription.subscriber.clone();
            
            // 检查事件过滤器
            if let Some(filter) = &subscription.event_filter {
                if !filter(&event) {
                    continue;
                }
            }
            
            // 在线程池中调度订阅者执行
            self.thread_pool.execute(move || {
                if let Err(error) = subscriber(event_clone) {
                    // 处理错误（实际应用中可能需要日志记录或其他操作）
                    println!("订阅者错误: {}", error.message);
                }
            });
            
            successful_count += 1;
        }
        
        if errors.is_empty() {
            DispatchResult::Success(successful_count)
        } else {
            DispatchResult::Partial(successful_count, errors)
        }
    }
}

impl Clone for Event {
    fn clone(&self) -> Self {
        Event {
            id: self.id,
            event_type: self.event_type.clone(),
            payload: self.payload.clone(),
            timestamp: self.timestamp,
            origin: self.origin.clone(),
            metadata: self.metadata.clone(),
        }
    }
}

impl Clone for Box<dyn Any + Send + Sync> {
    fn clone(&self) -> Self {
        // 这是简化实现，实际应实现正确的克隆
        unimplemented!("Any克隆未实现")
    }
}

impl Clone for Box<dyn Fn(Event) -> Result<(), ReactiveError> + Send + Sync> {
    fn clone(&self) -> Self {
        // 这是简化实现，实际应实现正确的克隆
        unimplemented!("Fn克隆未实现")
    }
}

// 简单的线程池实现
struct ThreadPool {
    workers: Vec<Worker>,
    sender: mpsc::Sender<Message>,
}

struct Worker {
    id: usize,
    thread: Option<thread::JoinHandle<()>>,
}

enum Message {
    NewJob(Box<dyn FnOnce() + Send + 'static>),
    Terminate,
}

impl ThreadPool {
    fn new(size: usize) -> ThreadPool {
        assert!(size > 0);

        let (sender, receiver) = mpsc::channel();
        let receiver = Arc::new(Mutex::new(receiver));

        let mut workers = Vec::with_capacity(size);

        for id in 0..size {
            workers.push(Worker::new(id, Arc::clone(&receiver)));
        }

        ThreadPool { workers, sender }
    }

    fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        let job = Box::new(f);
        self.sender.send(Message::NewJob(job)).unwrap();
    }
}

impl Drop for ThreadPool {
    fn drop(&mut self) {
        for _ in &self.workers {
            self.sender.send(Message::Terminate).unwrap();
        }

        for worker in &mut self.workers {
            if let Some(thread) = worker.thread.take() {
                thread.join().unwrap();
            }
        }
    }
}

impl Worker {
    fn new(id: usize, receiver: Arc<Mutex<mpsc::Receiver<Message>>>) -> Worker {
        let thread = thread::spawn(move || loop {
            let message = receiver.lock().unwrap().recv().unwrap();

            match message {
                Message::NewJob(job) => {
                    job();
                }
                Message::Terminate => {
                    break;
                }
            }
        });

        Worker {
            id,
            thread: Some(thread),
        }
    }
}

// 常见的操作符实现
struct MapOperator<F> {
    mapper: F,
}

impl<F, T, R> StreamOperator for MapOperator<F>
where
    F: Fn(T) -> R + Send + Sync + 'static,
    T: 'static,
    R: 'static,
{
    fn name(&self) -> &str {
        "Map操作符"
    }
    
    fn process(&self, event: Event) -> Vec<Event> {
        // 尝试从事件中提取输入类型
        if let Ok(input) = event.payload.downcast::<T>() {
            // 应用映射函数
            let result = (self.mapper)(*input);
            
            // 创建包含结果的新事件
            let mut new_event = event.clone();
            new_event.payload = Box::new(result);
            
            vec![new_event]
        } else {
            // 类型不匹配，返回原始事件
            vec![event]
        }
    }
    
    fn on_error(&self, error: ReactiveError) -> ErrorHandlingAction {
        // 简单的错误处理：传播错误
        ErrorHandlingAction::Propagate
    }
}

struct FilterOperator<F> {
    predicate: F,
}

impl<F, T> StreamOperator for FilterOperator<F>
where
    F: Fn(&T) -> bool + Send + Sync + 'static,
    T: 'static,
{
    fn name(&self) -> &str {
        "Filter操作符"
    }
    
    fn process(&self, event: Event) -> Vec<Event> {
        // 尝试从事件中提取输入类型
        if let Ok(input) = event.payload.downcast_ref::<T>() {
            // 应用过滤器
            if (self.predicate)(input) {
                vec![event]
            } else {
                // 过滤掉事件
                vec![]
            }
        } else {
            // 类型不匹配，保留原始事件
            vec![event]
        }
    }
    
    fn on_error(&self, error: ReactiveError) -> ErrorHandlingAction {
        // 简单的错误处理：传播错误
        ErrorHandlingAction::Propagate
    }
}

struct DebounceOperator {
    window: Duration,
    last_event_time: Arc<Mutex<Option<Instant>>>,
    timer: Arc<Mutex<Option<Instant>>>,
}

impl StreamOperator for DebounceOperator {
    fn name(&self) -> &str {
        "Debounce操作符"
    }
    
    fn process(&self, event: Event) -> Vec<Event> {
        let now = Instant::now();
        let mut last_time = self.last_event_time.lock().unwrap();
        let mut timer = self.timer.lock().unwrap();
        
        *last_time = Some(now);
        
        // 设置或重置定时器
        *timer = Some(now + self.window);
        
        // Debounce会延迟发送事件，这里简化处理
        // 实际实现应使用定时器等机制
        
        // 简化：如果距离上次事件超过窗口期，则发送
        if let Some(last) = *last_time {
            if now.duration_since(last) > self.window {
                return vec![event];
            }
        } else {
            // 首次事件
            return vec![event];
        }
        
        // 否则抑制事件
        vec![]
    }
    
    fn on_error(&self, error: ReactiveError) -> ErrorHandlingAction {
        ErrorHandlingAction::Propagate
    }
}

impl DebounceOperator {
    fn new(window: Duration) -> Self {
        DebounceOperator {
            window,
            last_event_time: Arc::new(Mutex::new(None)),
            timer: Arc::new(Mutex::new(None)),
        }
    }
}

// 事件源例子
struct IntervalSource {
    interval: Duration,
    count: usize,
    current: usize,
    last_emit: Option<Instant>,
}

impl Source for IntervalSource {
    fn name(&self) -> &str {
        "Interval源"
    }
    
    fn emit(&mut self) -> Option<Event> {
        let now = Instant::now();
        
        if let Some(last) = self.last_emit {
            if now.duration_since(last) < self.interval {
                // 尚未达到下一个间隔
                return None;
            }
        }
        
        // 更新上次发射时间
        self.last_emit = Some(now);
        
        if self.count > 0 && self.current >= self.count {
            // 已达到最大计数
            return None;
        }
        
        // 创建事件
        let event = Event {
            id: Uuid::new_v4(),
            event_type: "interval".to_string(),
            payload: Box::new(self.current),
            timestamp: now,
            origin: "IntervalSource".to_string(),
            metadata: HashMap::new(),
        };
        
        self.current += 1;
        
        Some(event)
    }
    
    fn is_complete(&self) -> bool {
        self.count > 0 && self.current >= self.count
    }
}

impl IntervalSource {
    fn new(interval: Duration, count: usize) -> Self {
        IntervalSource {
            interval,
            count,
            current: 0,
            last_emit: None,
        }
    }
}

// 接收器例子
struct ConsoleLogSink;

impl Sink for ConsoleLogSink {
    fn name(&self) -> &str {
        "Console日志接收器"
    }
    
    fn accept(&mut self, event: Event) -> Result<(), ReactiveError> {
        println!("[{}] 事件 {} (类型: {}): {:?}",
               event.timestamp.elapsed().as_millis(),
               event.id,
               event.event_type,
               event.payload);
        
        Ok(())
    }
    
    fn on_complete(&mut self) {
        println!("流处理完成");
    }
}

// 线程池调度器
struct ThreadPoolScheduler {
    thread_pool: ThreadPool,
}

impl ExecutionScheduler for ThreadPoolScheduler {
    fn schedule(&mut self, task: Box<dyn FnOnce() + Send>) -> SchedulingResult {
        self.thread_pool.execute(move || {
            task();
        });
        
        SchedulingResult::Scheduled
    }
    
    fn shutdown(&mut self) {
        // 线程池会在drop时自动关闭
    }
}

impl ThreadPoolScheduler {
    fn new(thread_count: usize) -> Self {
        ThreadPoolScheduler {
            thread_pool: ThreadPool::new(thread_count),
        }
    }
}

// 示例使用
fn create_reactive_system() -> ReactiveSystem {
    let scheduler = Box::new(ThreadPoolScheduler::new(4));
    let mut system = ReactiveSystem::new(scheduler);
    
    // 创建一个每秒发出10个事件的源
    let source = Box::new(IntervalSource::new(Duration::from_millis(100), 10));
    system.create_stream("ticker", source, BufferStrategy::Bounded(100)).unwrap();
    
    // 添加一个映射操作符
    let map_operator = Box::new(MapOperator {
        mapper: |x: usize| format!("Tick #{}", x),
    });
    system.add_operator("ticker", "string_mapper", map_operator).unwrap();
    
    // 添加一个控制台输出接收器
    let sink = Box::new(ConsoleLogSink);
    system.set_sink("ticker", "console", sink).unwrap();
    
    // 设置背压策略
    system.set_backpressure_strategy("ticker", BackpressureStrategy::Drop).unwrap();
    
    system
}

// 示例运行
fn run_reactive_example() {
    let mut system = create_reactive_system();
    
    // 启动流
    system.start_stream("ticker").unwrap();
    
    // 等待处理完成
    thread::sleep(Duration::from_secs(2));
    
    // 关闭系统
    system.shutdown();
}
```

## 4. 分布式计算模型

### 4.1 一致性模型

分布式系统中的一致性模型定义了数据副本如何保持同步，以及客户端如何感知数据变化。

```rust
// 一致性模型框架
struct ConsistencyModel {
    model_type: ConsistencyModelType,
    constraints: Vec<ConsistencyConstraint>,
    guarantees: Vec<ConsistencyGuarantee>,
}

enum ConsistencyModelType {
    StrongConsistency,
    LinearizableConsistency,
    SequentialConsistency,
    CausalConsistency,
    EventualConsistency,
    SessionConsistency,
    BoundedStaleness,
    CustomConsistency(String),
}

enum ConsistencyConstraint {
    SingleCopy,
    ReadYourWrites,
    MonotonicReads,
    MonotonicWrites,
    WritesFollowReads,
    StalenessLimit(Duration),
    TimeDeviation(Duration),
    OrderPreservation,
    CustomConstraint(String),
}

enum ConsistencyGuarantee {
    AlwaysSatisfied,
    EventuallySatisfied,
    ProbabilisticallySatisfied(f64),
    SatisfiedWithBound(Duration),
    SatisfiedWithProbabilityAndBound(f64, Duration),
    CustomGuarantee(String),
}

// 一致性模型实现者
struct ConsistencyModelImplementer {
    models: HashMap<ConsistencyModelType, Box<dyn ConsistencyProtocol>>,
}

trait ConsistencyProtocol {
    fn name(&self) -> &str;
    fn process_read(&self, object_id: &str, client_id: &str) -> Result<DataVersion, ConsistencyError>;
    fn process_write(&self, object_id: &str, client_id: &str, value: DataValue) -> Result<(), ConsistencyError>;
    fn check_consistency(&self, history: &[Operation]) -> ConsistencyVerificationResult;
    fn get_consistency_metrics(&self) -> HashMap<String, f64>;
}

struct DataVersion {
    value: DataValue,
    version: u64,
    timestamp: Instant,
    causal_dependencies: Option<Vec<(String, u64)>>,
    metadata: HashMap<String, String>,
}

enum DataValue {
    Integer(i64),
    Float(f64),
    Text(String),
    Binary(Vec<u8>),
    Json(serde_json::Value),
}

enum Operation {
    Read { client_id: String, object_id: String, result: DataVersion, timestamp: Instant },
    Write { client_id: String, object_id: String, value: DataValue, timestamp: Instant },
}

struct ConsistencyError {
    message: String,
    error_type: ConsistencyErrorType,
}

enum ConsistencyErrorType {
    Unavailable,
    Timeout,
    Conflict,
    VersionMismatch,
    InvalidData,
    SystemError,
}

enum ConsistencyVerificationResult {
    Consistent,
    Inconsistent(Vec<ConsistencyViolation>),
    Unknown,
}

struct ConsistencyViolation {
    violation_type: ViolationType,
    operations: Vec<Operation>,
    description: String,
}

enum ViolationType {
    ReadWriteOrder,
    CausalViolation,
    LinearizabilityViolation,
    MonotonicityViolation,
    SessionViolation,
    CustomViolation(String),
}

impl ConsistencyModelImplementer {
    fn new() -> Self {
        let mut models = HashMap::new();
        
        // 注册默认一致性模型
        models.insert(
            ConsistencyModelType::StrongConsistency,
            Box::new(StrongConsistencyProtocol::new()) as Box<dyn ConsistencyProtocol>
        );
        
        models.insert(
            ConsistencyModelType::EventualConsistency,
            Box::new(EventualConsistencyProtocol::new()) as Box<dyn ConsistencyProtocol>
        );
        
        models.insert(
            ConsistencyModelType::CausalConsistency,
            Box::new(CausalConsistencyProtocol::new()) as Box<dyn ConsistencyProtocol>
        );
        
        ConsistencyModelImplementer { models }
    }
    
    fn register_protocol(&mut self, model_type: ConsistencyModelType, protocol: Box<dyn ConsistencyProtocol>) {
        self.models.insert(model_type, protocol);
    }
    
    fn get_protocol(&self, model_type: &ConsistencyModelType) -> Option<&Box<dyn ConsistencyProtocol>> {
        self.models.get(model_type)
    }
    
    fn process_read(&self, model_type: &ConsistencyModelType, object_id: &str, client_id: &str) -> Result<DataVersion, ConsistencyError> {
        if let Some(protocol) = self.models.get(model_type) {
            protocol.process_read(object_id, client_id)
        } else {
            Err(ConsistencyError {
                message: format!("不支持的一致性模型: {:?}", model_type),
                error_type: ConsistencyErrorType::SystemError,
            })
        }
    }
    
    fn process_write(&self, model_type: &ConsistencyModelType, object_id: &str, client_id: &str, value: DataValue) -> Result<(), ConsistencyError> {
        if let Some(protocol) = self.models.get(model_type) {
            protocol.process_write(object_id, client_id, value)
        } else {
            Err(ConsistencyError {
                message: format!("不支持的一致性模型: {:?}", model_type),
                error_type: ConsistencyErrorType::SystemError,
            })
        }
    }
    
    fn verify_history(&self, model_type: &ConsistencyModelType, history: &[Operation]) -> ConsistencyVerificationResult {
        if let Some(protocol) = self.models.get(model_type) {
            protocol.check_consistency(history)
        } else {
            ConsistencyVerificationResult::Unknown
        }
    }
}

// 强一致性协议实现
struct StrongConsistencyProtocol {
    data_store: Arc<Mutex<HashMap<String, DataVersion>>>,
    lock_manager: Arc<Mutex<HashMap<String, Instant>>>,
    lock_timeout: Duration,
}

impl StrongConsistencyProtocol {
    fn new() -> Self {
        StrongConsistencyProtocol {
            data_store: Arc::new(Mutex::new(HashMap::new())),
            lock_manager: Arc::new(Mutex::new(HashMap::new())),
            lock_timeout: Duration::from_secs(10),
        }
    }
    
    fn acquire_lock(&self, object_id: &str) -> Result<(), ConsistencyError> {
        let mut locks = self.lock_manager.lock().unwrap();
        let now = Instant::now();
        
        // 检查对象锁
        if let Some(lock_time) = locks.get(object_id) {
            if now.duration_since(*lock_time) < self.lock_timeout {
                // 锁仍然有效
                return Err(ConsistencyError {
                    message: format!("对象 {} 暂时不可用", object_id),
                    error_type: ConsistencyErrorType::Unavailable,
                });
            }
        }
        
        // 获取锁
        locks.insert(object_id.to_string(), now);
        Ok(())
    }
    
    fn release_lock(&self, object_id: &str) {
        let mut locks = self.lock_manager.lock().unwrap();
        locks.remove(object_id);
    }
}

impl ConsistencyProtocol for StrongConsistencyProtocol {
    fn name(&self) -> &str {
        "强一致性协议"
    }
    
    fn process_read(&self, object_id: &str, client_id: &str) -> Result<DataVersion, ConsistencyError> {
        // 对于强一致性，读取需要获取锁
        self.acquire_lock(object_id)?;
        
        let result = {
            let store = self.data_store.lock().unwrap();
            
            if let Some(version) = store.get(object_id) {
                Ok(version.clone())
            } else {
                Err(ConsistencyError {
                    message: format!("对象 {} 不存在", object_id),
                    error_type: ConsistencyErrorType::InvalidData,
                })
            }
        };
        
        self.release_lock(object_id);
        result
    }
    
    fn process_write(&self, object_id: &str, client_id: &str, value: DataValue) -> Result<(), ConsistencyError> {
        // 获取锁
        self.acquire_lock(object_id)?;
        
        {
            let mut store = self.data_store.lock().unwrap();
            
            // 创建新版本
            let new_version = if let Some(old_version) = store.get(object_id) {
                DataVersion {
                    value,
                    version: old_version.version + 1,
                    timestamp: Instant::now(),
                    causal_dependencies: None,
                    metadata: HashMap::new(),
                }
            } else {
                DataVersion {
                    value,
                    version: 1,
                    timestamp: Instant::now(),
                    causal_dependencies: None,
                    metadata: HashMap::new(),
                }
            };
            
            // 更新数据
            store.insert(object_id.to_string(), new_version);
        }
        
        self.release_lock(object_id);
        Ok(())
    }
    
    fn check_consistency(&self, history: &[Operation]) -> ConsistencyVerificationResult {
        // 对于强一致性，每个操作都应该看到最新的写入
        // 实现线性化检查
        
        // 简化版本，实际实现需要更复杂的算法
        let mut last_write_time: HashMap<String, Instant> = HashMap::new();
        let mut violations = Vec::new();
        
        for op in history {
            match op {
                Operation::Write { object_id, timestamp, .. } => {
                    last_write_time.insert(object_id.clone(), *timestamp);
                },
                Operation::Read { object_id, result, timestamp, .. } => {
                    if let Some(last_write) = last_write_time.get(object_id) {
                        if *last_write > *timestamp && result.timestamp < *last_write {
                            // 读取应该看到之前的写入，但没有
                            violations.push(ConsistencyViolation {
                                violation_type: ViolationType::LinearizabilityViolation,
                                operations: vec![op.clone()],
                                description: format!("读取 {:?} 没有看到先前的写入", timestamp),
                            });
                        }
                    }
                }
            }
        }
        
        if violations.is_empty() {
            ConsistencyVerificationResult::Consistent
        } else {
            ConsistencyVerificationResult::Inconsistent(violations)
        }
    }
    
    fn get_consistency_metrics(&self) -> HashMap<String, f64> {
        let mut metrics = HashMap::new();
        metrics.insert("staleness".to_string(), 0.0); // 强一致性没有过时
        metrics.insert("availability".to_string(), 0.95); // 更低的可用性
        metrics.insert("throughput".to_string(), 100.0); // 低吞吐量
        metrics
    }
}

// 最终一致性协议实现
struct EventualConsistencyProtocol {
    data_store: Arc<RwLock<HashMap<String, Vec<DataVersion>>>>,
    replication_delay: Duration,
    propagation_probability: f64,
}

impl EventualConsistencyProtocol {
    fn new() -> Self {
        EventualConsistencyProtocol {
            data_store: Arc::new(RwLock::new(HashMap::new())),
            replication_delay: Duration::from_millis(500),
            propagation_probability: 0.9,
        }
    }
}

impl ConsistencyProtocol for EventualConsistencyProtocol {
    fn name(&self) -> &str {
        "最终一致性协议"
    }
    
    fn process_read(&self, object_id: &str, client_id: &str) -> Result<DataVersion, ConsistencyError> {
        let store = self.data_store.read().unwrap();
        
        if let Some(versions) = store.get(object_id) {
            if versions.is_empty() {
                return Err(ConsistencyError {
                    message: format!("对象 {} 不存在", object_id),
                    error_type: ConsistencyErrorType::InvalidData,
                });
            }
            
            // 最终一致性读取最近的版本
            // 注意：不保证总是最新的，可能有延迟
            Ok(versions.last().unwrap().clone())
        } else {
            Err(ConsistencyError {
                message: format!("对象 {} 不存在", object_id),
                error_type: ConsistencyErrorType::InvalidData,
            })
        }
    }
    
    fn process_write(&self, object_id: &str, client_id: &str, value: DataValue) -> Result<(), ConsistencyError> {
        let mut store = self.data_store.write().unwrap();
        
        // 创建新版本
        let new_version = DataVersion {
            value,
            version: Uuid::new_v4().as_u128() as u64, // 使用随机版本号
            timestamp: Instant::now(),
            causal_dependencies: None,
            metadata: HashMap::new(),
        };
        
        // 更新版本历史
        let versions = store.entry(object_id.to_string())
            .or_insert_with(Vec::new);
        
        versions.push(new_version);
        
        // 异步复制
        let versions_clone = versions.clone();
        let data_store_clone = self.data_store.clone();
        let object_id_clone = object_id.to_string();
        let delay = self.replication_delay;
        let probability = self.propagation_probability;
        
        thread::spawn(move || {
            thread::sleep(delay);
            
            // 模拟随机传播失败
            if rand::random::<f64>() <= probability {
                let mut store = data_store_clone.write().unwrap();
                if let Some(current_versions) = store.get_mut(&object_id_clone) {
                    *current_versions = versions_clone;
                }
            }
        });
        
        Ok(())
    }
    
    fn check_consistency(&self, history: &[Operation]) -> ConsistencyVerificationResult {
        // 对于最终一致性，我们检查是否所有的写入最终都被所有的读取看到
        // 简化版本，只检查最后的读取是否看到所有的写入
        
        let mut violations = Vec::new();
        let mut last_writes: HashMap<String, HashMap<String, (DataValue, Instant)>> = HashMap::new();
        let mut last_reads: HashMap<String, HashMap<String, (DataVersion, Instant)>> = HashMap::new();
        
        // 收集所有写入
        for op in history {
            match op {
                Operation::Write { client_id, object_id, value, timestamp } => {
                    let client_writes = last_writes.entry(client_id.clone())
                        .or_insert_with(HashMap::new);
                    client_writes.insert(object_id.clone(), (value.clone(), *timestamp));
                },
                Operation::Read { client_id, object_id, result, timestamp } => {
                    let client_reads = last_reads.entry(client_id.clone())
                        .or_insert_with(HashMap::new);
                    client_reads.insert(object_id.clone(), (result.clone(), *timestamp));
                }
            }
        }
        
        // 检查每个客户端的最后一次读取是否包含所有写入
        for (client_id, reads) in &last_reads {
            for (object_id, (read_version, read_time)) in reads {
                for (write_client, writes) in &last_writes {
                    if let Some((write_value, write_time)) = writes.get(object_id) {
                        // 如果写入发生在很久之前（超过合理的传播时间），读取应该看到它
                        let reasonable_delay = Duration::from_secs(5); // 假设5秒是合理的延迟
                        
                        if *write_time + reasonable_delay < *read_time && 
                           !Self::value_equals(&read_version.value, write_value) {
                            violations.push(ConsistencyViolation {
                                violation_type: ViolationType::EventualConsistencyViolation,
                                operations: vec![],
                                description: format

```rust
                                violation_type: ViolationType::EventualConsistencyViolation,
                                operations: vec![],
                                description: format!("客户端 {} 在 {:?} 的读取没有看到客户端 {} 在 {:?} 的写入", 
                                                   client_id, read_time, write_client, write_time),
                            });
                        }
                    }
                }
            }
        }
        
        if violations.is_empty() {
            ConsistencyVerificationResult::Consistent
        } else {
            ConsistencyVerificationResult::Inconsistent(violations)
        }
    }
    
    fn get_consistency_metrics(&self) -> HashMap<String, f64> {
        let mut metrics = HashMap::new();
        metrics.insert("staleness".to_string(), self.replication_delay.as_secs_f64());
        metrics.insert("availability".to_string(), 0.99); // 更高的可用性
        metrics.insert("throughput".to_string(), 1000.0); // 高吞吐量
        metrics.insert("propagation_probability".to_string(), self.propagation_probability);
        metrics
    }
}

impl EventualConsistencyProtocol {
    fn value_equals(a: &DataValue, b: &DataValue) -> bool {
        match (a, b) {
            (DataValue::Integer(a_val), DataValue::Integer(b_val)) => a_val == b_val,
            (DataValue::Float(a_val), DataValue::Float(b_val)) => (a_val - b_val).abs() < 1e-10,
            (DataValue::Text(a_val), DataValue::Text(b_val)) => a_val == b_val,
            (DataValue::Binary(a_val), DataValue::Binary(b_val)) => a_val == b_val,
            (DataValue::Json(a_val), DataValue::Json(b_val)) => a_val == b_val,
            _ => false,
        }
    }
}

enum EventualConsistencyViolation {
    StaleRead,
    InconsistentRead,
}

// 因果一致性协议实现
struct CausalConsistencyProtocol {
    data_store: Arc<RwLock<HashMap<String, Vec<DataVersion>>>>,
    client_context: Arc<RwLock<HashMap<String, Vec<(String, u64)>>>>, // 客户端ID -> 依赖列表(对象ID, 版本)
}

impl CausalConsistencyProtocol {
    fn new() -> Self {
        CausalConsistencyProtocol {
            data_store: Arc::new(RwLock::new(HashMap::new())),
            client_context: Arc::new(RwLock::new(HashMap::new())),
        }
    }
}

impl ConsistencyProtocol for CausalConsistencyProtocol {
    fn name(&self) -> &str {
        "因果一致性协议"
    }
    
    fn process_read(&self, object_id: &str, client_id: &str) -> Result<DataVersion, ConsistencyError> {
        let store = self.data_store.read().unwrap();
        
        // 获取客户端的因果上下文
        let client_deps = {
            let contexts = self.client_context.read().unwrap();
            contexts.get(client_id).cloned().unwrap_or_else(Vec::new)
        };
        
        if let Some(versions) = store.get(object_id) {
            if versions.is_empty() {
                return Err(ConsistencyError {
                    message: format!("对象 {} 不存在", object_id),
                    error_type: ConsistencyErrorType::InvalidData,
                });
            }
            
            // 查找满足因果依赖的最新版本
            let mut best_version = None;
            let mut best_version_time = Instant::now() - Duration::from_secs(3600 * 24 * 365); // 一年前
            
            for version in versions.iter().rev() {
                // 检查版本是否满足所有因果依赖
                let satisfies_deps = if let Some(deps) = &version.causal_dependencies {
                    // 遍历客户端依赖，确保每个都被当前版本满足
                    client_deps.iter().all(|(dep_obj, dep_ver)| {
                        // 如果依赖是当前对象，直接比较版本
                        if dep_obj == object_id {
                            version.version >= *dep_ver
                        } else {
                            // 否则检查因果依赖列表
                            deps.iter().any(|(obj, ver)| obj == dep_obj && ver >= dep_ver)
                        }
                    })
                } else {
                    // 没有依赖信息，默认满足（这是简化的处理）
                    true
                };
                
                if satisfies_deps && version.timestamp > best_version_time {
                    best_version = Some(version);
                    best_version_time = version.timestamp;
                }
            }
            
            if let Some(version) = best_version {
                // 更新客户端上下文
                let mut contexts = self.client_context.write().unwrap();
                let context = contexts.entry(client_id.to_string()).or_insert_with(Vec::new);
                
                // 添加或更新对象的版本依赖
                let mut updated = false;
                for (obj, ver) in context.iter_mut() {
                    if obj == object_id {
                        *ver = version.version.max(*ver);
                        updated = true;
                        break;
                    }
                }
                
                if !updated {
                    context.push((object_id.to_string(), version.version));
                }
                
                Ok(version.clone())
            } else {
                // 没有满足依赖的版本
                Err(ConsistencyError {
                    message: format!("没有满足因果依赖的版本可用"),
                    error_type: ConsistencyErrorType::Unavailable,
                })
            }
        } else {
            Err(ConsistencyError {
                message: format!("对象 {} 不存在", object_id),
                error_type: ConsistencyErrorType::InvalidData,
            })
        }
    }
    
    fn process_write(&self, object_id: &str, client_id: &str, value: DataValue) -> Result<(), ConsistencyError> {
        let mut store = self.data_store.write().unwrap();
        
        // 获取客户端的因果上下文
        let client_deps = {
            let contexts = self.client_context.read().unwrap();
            contexts.get(client_id).cloned().unwrap_or_else(Vec::new)
        };
        
        // 创建新版本
        let new_version = DataVersion {
            value,
            version: Uuid::new_v4().as_u128() as u64, // 使用随机版本号
            timestamp: Instant::now(),
            causal_dependencies: Some(client_deps.clone()),
            metadata: HashMap::new(),
        };
        
        // 更新版本历史
        let versions = store.entry(object_id.to_string())
            .or_insert_with(Vec::new);
        
        versions.push(new_version);
        
        // 更新客户端上下文
        let mut contexts = self.client_context.write().unwrap();
        let context = contexts.entry(client_id.to_string()).or_insert_with(Vec::new);
        
        // 添加或更新对象的版本依赖
        let mut updated = false;
        for (obj, ver) in context.iter_mut() {
            if obj == object_id {
                *ver = versions.last().unwrap().version;
                updated = true;
                break;
            }
        }
        
        if !updated {
            context.push((object_id.to_string(), versions.last().unwrap().version));
        }
        
        Ok(())
    }
    
    fn check_consistency(&self, history: &[Operation]) -> ConsistencyVerificationResult {
        // 对于因果一致性，需要检查因果关系是否得到维护
        // 对于每个读操作，它应该看到所有因果前导的写操作
        
        let mut violations = Vec::new();
        let mut operation_graph = HashMap::new();
        
        // 构建因果图
        for (i, op) in history.iter().enumerate() {
            operation_graph.insert(i, (op, Vec::new()));
        }
        
        // 添加因果边
        for (i, op_i) in history.iter().enumerate() {
            for (j, op_j) in history.iter().enumerate() {
                if i == j { continue; }
                
                // 检查是否存在因果关系
                if Self::causally_precedes(op_i, op_j) {
                    operation_graph.get_mut(&i).unwrap().1.push(j);
                }
            }
        }
        
        // 检查每个读操作是否满足因果一致性
        for (i, (op, predecessors)) in &operation_graph {
            if let Operation::Read { object_id, result, .. } = op {
                // 对于每个前导写入，检查读取是否反映了它
                for &pred_idx in predecessors {
                    if let (Operation::Write { object_id: pred_obj, value, .. }, _) = &operation_graph[&pred_idx] {
                        if pred_obj == object_id && !EventualConsistencyProtocol::value_equals(&result.value, value) {
                            violations.push(ConsistencyViolation {
                                violation_type: ViolationType::CausalViolation,
                                operations: vec![op.clone(), history[pred_idx].clone()],
                                description: format!("读取没有反映因果前导的写入"),
                            });
                        }
                    }
                }
            }
        }
        
        if violations.is_empty() {
            ConsistencyVerificationResult::Consistent
        } else {
            ConsistencyVerificationResult::Inconsistent(violations)
        }
    }
    
    fn get_consistency_metrics(&self) -> HashMap<String, f64> {
        let mut metrics = HashMap::new();
        metrics.insert("staleness".to_string(), 0.5); // 中等过时
        metrics.insert("availability".to_string(), 0.98); // 较高可用性
        metrics.insert("throughput".to_string(), 500.0); // 中等吞吐量
        metrics
    }
}

impl CausalConsistencyProtocol {
    fn causally_precedes(op1: &Operation, op2: &Operation) -> bool {
        match (op1, op2) {
            (Operation::Write { client_id: client1, timestamp: time1, .. }, 
             Operation::Write { client_id: client2, timestamp: time2, .. }) => {
                // 同一客户端的写入有因果关系
                client1 == client2 && time1 < time2
            },
            (Operation::Write { object_id: obj1, timestamp: time1, .. },
             Operation::Read { object_id: obj2, result, .. }) => {
                // 写入对应同一对象的读取，且时间上写入在先
                obj1 == obj2 && *time1 < result.timestamp && result.version > 0
            },
            (Operation::Read { result, .. },
             Operation::Write { client_id, timestamp, .. }) => {
                // 读取后同一客户端的写入
                if let Some(deps) = &result.causal_dependencies {
                    deps.iter().any(|(_, ver)| *ver > 0)
                } else {
                    false
                }
            },
            _ => false,
        }
    }
}

// 会话一致性协议实现
struct SessionConsistencyProtocol {
    data_store: Arc<RwLock<HashMap<String, Vec<DataVersion>>>>,
    session_context: Arc<RwLock<HashMap<String, HashMap<String, u64>>>>, // 会话ID -> (对象ID -> 最后读取的版本)
}

impl SessionConsistencyProtocol {
    fn new() -> Self {
        SessionConsistencyProtocol {
            data_store: Arc::new(RwLock::new(HashMap::new())),
            session_context: Arc::new(RwLock::new(HashMap::new())),
        }
    }
}

impl ConsistencyProtocol for SessionConsistencyProtocol {
    fn name(&self) -> &str {
        "会话一致性协议"
    }
    
    fn process_read(&self, object_id: &str, client_id: &str) -> Result<DataVersion, ConsistencyError> {
        let store = self.data_store.read().unwrap();
        
        // 获取会话上下文
        let min_version = {
            let contexts = self.session_context.read().unwrap();
            if let Some(session) = contexts.get(client_id) {
                session.get(object_id).cloned().unwrap_or(0)
            } else {
                0
            }
        };
        
        if let Some(versions) = store.get(object_id) {
            if versions.is_empty() {
                return Err(ConsistencyError {
                    message: format!("对象 {} 不存在", object_id),
                    error_type: ConsistencyErrorType::InvalidData,
                });
            }
            
            // 查找大于等于最小版本的最新版本
            let mut suitable_version = None;
            
            for version in versions.iter().rev() {
                if version.version >= min_version {
                    suitable_version = Some(version);
                    break;
                }
            }
            
            if let Some(version) = suitable_version {
                // 更新会话上下文
                let mut contexts = self.session_context.write().unwrap();
                let session = contexts.entry(client_id.to_string()).or_insert_with(HashMap::new);
                
                // 更新对象的最后读取版本
                session.insert(object_id.to_string(), version.version);
                
                Ok(version.clone())
            } else {
                // 没有找到合适的版本
                Err(ConsistencyError {
                    message: format!("没有满足会话一致性要求的版本可用"),
                    error_type: ConsistencyErrorType::Unavailable,
                })
            }
        } else {
            Err(ConsistencyError {
                message: format!("对象 {} 不存在", object_id),
                error_type: ConsistencyErrorType::InvalidData,
            })
        }
    }
    
    fn process_write(&self, object_id: &str, client_id: &str, value: DataValue) -> Result<(), ConsistencyError> {
        let mut store = self.data_store.write().unwrap();
        
        // 创建新版本
        let new_version = DataVersion {
            value,
            version: Uuid::new_v4().as_u128() as u64, // 使用随机版本号
            timestamp: Instant::now(),
            causal_dependencies: None,
            metadata: HashMap::new(),
        };
        
        // 更新版本历史
        let versions = store.entry(object_id.to_string())
            .or_insert_with(Vec::new);
        
        versions.push(new_version.clone());
        
        // 更新会话上下文
        let mut contexts = self.session_context.write().unwrap();
        let session = contexts.entry(client_id.to_string()).or_insert_with(HashMap::new);
        
        // 更新对象的最后写入版本
        session.insert(object_id.to_string(), new_version.version);
        
        Ok(())
    }
    
    fn check_consistency(&self, history: &[Operation]) -> ConsistencyVerificationResult {
        // 对于会话一致性，需要检查每个会话中的读操作是否单调递增
        // 简化版本：确保每个客户端的读取看到越来越新的版本
        
        let mut violations = Vec::new();
        let mut session_reads: HashMap<String, HashMap<String, Vec<(u64, usize)>>> = HashMap::new(); // 客户端ID -> 对象ID -> [(版本, 操作索引)]
        
        // 收集所有读取
        for (i, op) in history.iter().enumerate() {
            if let Operation::Read { client_id, object_id, result, .. } = op {
                let session = session_reads.entry(client_id.clone())
                    .or_insert_with(HashMap::new);
                
                let object_reads = session.entry(object_id.clone())
                    .or_insert_with(Vec::new);
                
                object_reads.push((result.version, i));
            }
        }
        
        // 检查每个会话的读取是否单调递增
        for (client_id, objects) in &session_reads {
            for (object_id, reads) in objects {
                let mut prev_version = 0;
                
                for &(version, op_idx) in reads {
                    if version < prev_version {
                        violations.push(ConsistencyViolation {
                            violation_type: ViolationType::MonotonicityViolation,
                            operations: vec![history[op_idx].clone()],
                            description: format!("客户端 {} 的读取违反了单调读取属性", client_id),
                        });
                    }
                    
                    prev_version = version;
                }
            }
        }
        
        if violations.is_empty() {
            ConsistencyVerificationResult::Consistent
        } else {
            ConsistencyVerificationResult::Inconsistent(violations)
        }
    }
    
    fn get_consistency_metrics(&self) -> HashMap<String, f64> {
        let mut metrics = HashMap::new();
        metrics.insert("staleness".to_string(), 0.2); // 较低过时
        metrics.insert("availability".to_string(), 0.985); // 较高可用性
        metrics.insert("throughput".to_string(), 800.0); // 较高吞吐量
        metrics
    }
}
```

### 4.2 共识算法

共识算法使分布式系统中的节点能够就某个值达成一致，即使在存在故障的情况下。

```rust
// 共识算法框架
struct ConsensusFramework {
    algorithms: HashMap<String, Box<dyn ConsensusAlgorithm>>,
    running_instances: HashMap<String, ConsensusInstance>,
}

trait ConsensusAlgorithm: Send + Sync {
    fn name(&self) -> &str;
    fn create_instance(&self, config: ConsensusConfig) -> Box<dyn ConsensusInstance>;
    fn fault_tolerance(&self, nodes: usize) -> usize;
    fn message_complexity(&self) -> MessageComplexity;
    fn supports_byzantine_faults(&self) -> bool;
}

trait ConsensusInstance: Send + Sync {
    fn id(&self) -> &str;
    fn propose(&mut self, value: Vec<u8>) -> Result<(), ConsensusError>;
    fn receive_message(&mut self, from: &NodeId, message: ConsensusMessage) -> Result<(), ConsensusError>;
    fn is_decided(&self) -> bool;
    fn get_decision(&self) -> Option<Vec<u8>>;
    fn get_status(&self) -> InstanceStatus;
    fn get_metrics(&self) -> HashMap<String, f64>;
}

struct ConsensusConfig {
    id: String,
    nodes: Vec<NodeId>,
    self_id: NodeId,
    timeout: Duration,
    max_retries: usize,
    message_sender: Box<dyn Fn(NodeId, ConsensusMessage) -> Result<(), SendError>>,
}

struct ConsensusInstance {
    id: String,
    algorithm: String,
    start_time: Instant,
    status: InstanceStatus,
    decision: Option<Vec<u8>>,
    metrics: HashMap<String, f64>,
}

enum InstanceStatus {
    Initializing,
    Running,
    Decided,
    Failed(ConsensusError),
}

struct ConsensusMessage {
    instance_id: String,
    message_type: ConsensusMessageType,
    sender: NodeId,
    round: u64,
    payload: Vec<u8>,
}

enum ConsensusMessageType {
    Prepare,
    Promise,
    Accept,
    Accepted,
    Learn,
    Value,
    Heartbeat,
    ViewChange,
    NewView,
}

struct NodeId {
    id: String,
    address: String,
    public_key: Option<Vec<u8>>,
}

struct ConsensusError {
    message: String,
    error_type: ConsensusErrorType,
}

enum ConsensusErrorType {
    Timeout,
    WrongLeader,
    InconsistentValue,
    NetworkError,
    ByzantineBehavior,
    InternalError,
}

struct SendError {
    message: String,
    error_type: SendErrorType,
}

enum SendErrorType {
    NetworkFailure,
    NodeUnavailable,
    MessageTooLarge,
    Timeout,
}

enum MessageComplexity {
    Constant,
    Linear,
    Quadratic,
    Cubic,
    Custom(String),
}

impl ConsensusFramework {
    fn new() -> Self {
        let mut algorithms = HashMap::new();
        
        // 注册内置算法
        algorithms.insert("paxos".to_string(), Box::new(PaxosAlgorithm::new()) as Box<dyn ConsensusAlgorithm>);
        algorithms.insert("raft".to_string(), Box::new(RaftAlgorithm::new()) as Box<dyn ConsensusAlgorithm>);
        algorithms.insert("pbft".to_string(), Box::new(PBFTAlgorithm::new()) as Box<dyn ConsensusAlgorithm>);
        
        ConsensusFramework {
            algorithms,
            running_instances: HashMap::new(),
        }
    }
    
    fn register_algorithm(&mut self, name: &str, algorithm: Box<dyn ConsensusAlgorithm>) -> Result<(), String> {
        if self.algorithms.contains_key(name) {
            return Err(format!("算法 '{}' 已经注册", name));
        }
        
        self.algorithms.insert(name.to_string(), algorithm);
        Ok(())
    }
    
    fn start_instance(&mut self, algorithm: &str, config: ConsensusConfig) -> Result<String, ConsensusError> {
        if let Some(alg) = self.algorithms.get(algorithm) {
            let instance = alg.create_instance(config);
            let instance_id = instance.id().to_string();
            
            self.running_instances.insert(instance_id.clone(), ConsensusInstance {
                id: instance_id.clone(),
                algorithm: algorithm.to_string(),
                start_time: Instant::now(),
                status: InstanceStatus::Initializing,
                decision: None,
                metrics: HashMap::new(),
            });
            
            Ok(instance_id)
        } else {
            Err(ConsensusError {
                message: format!("未知的共识算法: {}", algorithm),
                error_type: ConsensusErrorType::InternalError,
            })
        }
    }
    
    fn get_instance_status(&self, instance_id: &str) -> Option<InstanceStatus> {
        self.running_instances.get(instance_id).map(|i| i.status.clone())
    }
    
    fn get_instance_decision(&self, instance_id: &str) -> Option<Vec<u8>> {
        self.running_instances.get(instance_id).and_then(|i| i.decision.clone())
    }
    
    fn get_instance_metrics(&self, instance_id: &str) -> Option<HashMap<String, f64>> {
        self.running_instances.get(instance_id).map(|i| i.metrics.clone())
    }
    
    fn terminate_instance(&mut self, instance_id: &str) -> Result<(), ConsensusError> {
        if self.running_instances.remove(instance_id).is_some() {
            Ok(())
        } else {
            Err(ConsensusError {
                message: format!("实例 '{}' 不存在", instance_id),
                error_type: ConsensusErrorType::InternalError,
            })
        }
    }
    
    fn compare_algorithms(&self, node_count: usize, byzantine_nodes: usize) -> Vec<AlgorithmComparison> {
        let mut comparisons = Vec::new();
        
        for (name, algorithm) in &self.algorithms {
            let fault_tolerance = algorithm.fault_tolerance(node_count);
            let supports_byzantine = algorithm.supports_byzantine_faults();
            let safe_against_byzantine = supports_byzantine && fault_tolerance >= byzantine_nodes;
            
            comparisons.push(AlgorithmComparison {
                name: name.clone(),
                fault_tolerance,
                message_complexity: algorithm.message_complexity(),
                supports_byzantine_faults: supports_byzantine,
                safe_against_byzantine,
            });
        }
        
        comparisons
    }
}

struct AlgorithmComparison {
    name: String,
    fault_tolerance: usize,
    message_complexity: MessageComplexity,
    supports_byzantine_faults: bool,
    safe_against_byzantine: bool,
}

// Paxos算法实现
struct PaxosAlgorithm;

impl PaxosAlgorithm {
    fn new() -> Self {
        PaxosAlgorithm
    }
}

impl ConsensusAlgorithm for PaxosAlgorithm {
    fn name(&self) -> &str {
        "Paxos"
    }
    
    fn create_instance(&self, config: ConsensusConfig) -> Box<dyn ConsensusInstance> {
        Box::new(PaxosInstance::new(config))
    }
    
    fn fault_tolerance(&self, nodes: usize) -> usize {
        (nodes - 1) / 2 // Paxos容忍少于一半的节点故障
    }
    
    fn message_complexity(&self) -> MessageComplexity {
        MessageComplexity::Quadratic // O(n²)
    }
    
    fn supports_byzantine_faults(&self) -> bool {
        false // 标准Paxos不支持拜占庭故障
    }
}

struct PaxosInstance {
    config: ConsensusConfig,
    role: PaxosRole,
    state: PaxosState,
    current_round: u64,
    highest_accepted_round: u64,
    highest_accepted_value: Option<Vec<u8>>,
    promises_received: HashMap<NodeId, (u64, Option<Vec<u8>>)>,
    accepts_received: HashMap<NodeId, u64>,
    decided_value: Option<Vec<u8>>,
    retries: usize,
    status: InstanceStatus,
    metrics: HashMap<String, f64>,
}

enum PaxosRole {
    Proposer,
    Acceptor,
    Learner,
    All,
}

enum PaxosState {
    Idle,
    Preparing,
    Accepting,
    Learning,
    Decided,
}

impl PaxosInstance {
    fn new(config: ConsensusConfig) -> Self {
        PaxosInstance {
            config,
            role: PaxosRole::All, // 简化：所有节点具有所有角色
            state: PaxosState::Idle,
            current_round: 0,
            highest_accepted_round: 0,
            highest_accepted_value: None,
            promises_received: HashMap::new(),
            accepts_received: HashMap::new(),
            decided_value: None,
            retries: 0,
            status: InstanceStatus::Initializing,
            metrics: HashMap::new(),
        }
    }
    
    fn get_quorum_size(&self) -> usize {
        self.config.nodes.len() / 2 + 1
    }
    
    fn start_prepare(&mut self, value: Option<Vec<u8>>) -> Result<(), ConsensusError> {
        // 开始准备阶段
        self.current_round += 1;
        self.promises_received.clear();
        self.state = PaxosState::Preparing;
        
        // 构建Prepare消息
        let prepare_message = ConsensusMessage {
            instance_id: self.config.id.clone(),
            message_type: ConsensusMessageType::Prepare,
            sender: self.config.self_id.clone(),
            round: self.current_round,
            payload: Vec::new(),
        };
        
        // 向所有节点发送Prepare消息
        for node in &self.config.nodes {
            if let Err(err) = (self.config.message_sender)(node.clone(), prepare_message.clone()) {
                // 记录发送错误，但继续尝试其他节点
                println!("向节点 {} 发送Prepare消息失败: {}", node.id, err.message);
            }
        }
        
        // 启动超时计时器
        // 简化：实际实现应该使用定时器API
        
        Ok(())
    }
    
    fn handle_prepare(&mut self, from: &NodeId, message: &ConsensusMessage) -> Result<(), ConsensusError> {
        let round = message.round;
        
        // 如果收到的轮次大于自己接受过的最高轮次，则Promise
        if round > self.highest_accepted_round {
            // 更新最高接受轮次
            self.highest_accepted_round = round;
            
            // 构建Promise消息
            let mut payload = Vec::new();
            if let Some(value) = &self.highest_accepted_value {
                // 包含之前接受的值
                payload.extend_from_slice(value);
            }
            
            let promise_message = ConsensusMessage {
                instance_id: self.config.id.clone(),
                message_type: ConsensusMessageType::Promise,
                sender: self.config.self_id.clone(),
                round,
                payload,
            };
            
            // 发送Promise消息给Proposer
            (self.config.message_sender)(from.clone(), promise_message)?;
        }
        
        Ok(())
    }
    
    fn handle_promise(&mut self, from: &NodeId, message: &ConsensusMessage) -> Result<(), ConsensusError> {
        if message.round != self.current_round || self.state != PaxosState::Preparing {
            // 忽略不是当前轮次的Promise
            return Ok(());
        }
        
        // 记录Promise
        let accepted_value = if message.payload.is_empty() {
            None
        } else {
            Some(message.payload.clone())
        };
        
        self.promises_received.insert(from.clone(), (message.round, accepted_value));
        
        // 检查是否收到足够的Promise
        if self.promises_received.len() >= self.get_quorum_size() {
            // 决定要发送的值
            let mut highest_promised_round = 0;
            let mut highest_promised_value = None;
            
            for (_, (round, value)) in &self.promises_received {
                if *round > highest_promised_round && value.is_some() {
                    highest_promised_round = *round;
                    highest_promised_value = value.clone();
                }
            }
            
            // 如果有节点已经接受了值，则使用最高轮次的值
            // 否则，使用我们要提议的值
            let value_to_propose = highest_promised_value.unwrap_or_else(|| {
                self.highest_accepted_value.clone().unwrap_or_else(|| Vec::new())
            });
            
            // 进入接受阶段
            self.start_accept(value_to_propose)?;
        }
        
        Ok(())
    }
    
    fn start_accept(&mut self, value: Vec<u8>) -> Result<(), ConsensusError> {
        // 开始接受阶段
        self.state = PaxosState::Accepting;
        self.accepts_received.clear();
        
        // 构建Accept消息
        let accept_message = ConsensusMessage {
            instance_id: self.config.id.clone(),
            message_type: ConsensusMessageType::Accept,
            sender: self.config.self_id.clone(),
            round: self.current_round,
            payload: value,
        };
        
        // 向所有节点发送Accept消息
        for node in &self.config.nodes {
            if let Err(err) = (self.config.message_sender)(node.clone(), accept_message.clone()) {
                // 记录发送错误，但继续尝试其他节点
                println!("向节点 {} 发送Accept消息失败: {}", node.id, err.message);
            }
        }
        
        Ok(())
    }
    
    fn handle_accept(&mut self, from: &NodeId, message: &ConsensusMessage) -> Result<(), ConsensusError> {
        let round = message.round;
        
        // 如果收到的轮次大于等于自己接受过的最高轮次，则接受
        if round >= self.highest_accepted_round {
            self.highest_accepted_round = round;
            self.highest_accepted_value = Some(message.payload.clone());
            
            // 构建Accepted消息
            let accepted_message = ConsensusMessage {
                instance_id: self.config.id.clone(),
                message_type: ConsensusMessageType::Accepted,
                sender: self.config.self_id.clone(),
                round,
                payload: message.payload.clone(),
            };
            
            // 发送Accepted消息给所有节点（简化：实际中通常只发给Learners或Proposer）
            for node in &self.config.nodes {
                if let Err(err) = (self.config.message_sender)(node.clone(), accepted_message.clone()) {
                    println!("向节点 {} 发送Accepted消息失败: {}", node.id, err.message);
                }
            }
        }
        
        Ok(())
    }
    
    fn handle_accepted(&mut self, from: &NodeId, message: &ConsensusMessage) -> Result<(), ConsensusError> {
        if message.round != self.current_round || self.state != PaxosState::Accepting {
            // 忽略不是当前轮次的Accepted
            return Ok(());
        }
        
        // 记录Accepted
        self.accepts_received.insert(from.clone(), message.round);
        
        // 检查是否收到足够的Accepted
        if self.accepts_received.len() >= self.get_quorum_size() {
            // 达成共识
            self.decided_value = Some(message.payload.clone());
            self.state = PaxosState::Decided;
            self.status = InstanceStatus::Decided;
            
            // 记录指标
            self.metrics.insert("decision_rounds".to_string(), self.current_round as f64);
            self.metrics.insert("decision_time".to_string(), 
                               self.config.start_time.elapsed().as_secs_f64());
            
            // 广播决议
            let learn_message = ConsensusMessage {
                instance_id: self.config.id.clone(),
                message_type: ConsensusMessageType::Learn,
                sender: self.config.self_id.clone(),
                round: self.current_round,
                payload: message.payload.clone(),
            };
            
            for node in &self.config.nodes {
                if let Err(err) = (self.config.message_sender)(node.clone(), learn_message.clone()) {
                    println!("向节点 {} 发送Learn消息失败: {}", node.id, err.message);
                }
            }
        }
        
        Ok(())
    }
    
    fn handle_learn(&mut self, from: &NodeId, message: &ConsensusMessage) -> Result<(), ConsensusError> {
        // 学习最终决议
        self.decided_value = Some(message.payload.clone());
        self.state = PaxosState::Decided;
        self.status = InstanceStatus::Decided;
        
        Ok(())
    }
}

impl ConsensusInstance for PaxosInstance {
    fn id(&self) -> &str {
        &self.config.id
    }
    
    fn propose(&mut self, value: Vec<u8>) -> Result<(), ConsensusError> {
        if self.decided_value.is_some() {
            return Err(ConsensusError {
                message: "实例已经达成决议".to_string(),
                error_type: ConsensusErrorType::InternalError,
            });
        }
        
        self.highest_accepted_value = Some(value);
        self.start_prepare(self.highest_accepted_value.clone())
    }
    
    fn receive_message(&mut self, from: &NodeId, message: ConsensusMessage) -> Result<(), ConsensusError> {
        if message.instance_id != self.config.id {
            return Err(ConsensusError {
                message: "消息实例ID不匹配".to_string(),
                error_type: ConsensusErrorType::InternalError,
            });
        }
        
        match message.message_type {

```rust
ConsensusMessageType::Prepare => self.handle_prepare(from, &message),
ConsensusMessageType::Promise => self.handle_promise(from, &message),
ConsensusMessageType::Accept => self.handle_accept(from, &message),
ConsensusMessageType::Accepted => self.handle_accepted(from, &message),
ConsensusMessageType::Learn => self.handle_learn(from, &message),
_ => Err(ConsensusError {
    message: "不支持的消息类型".to_string(),
    error_type: ConsensusErrorType::InternalError,
}),
```

```rust
fn is_decided(&self) -> bool {
    self.decided_value.is_some()
}

fn get_decision(&self) -> Option<Vec<u8>> {
    self.decided_value.clone()
}

fn get_status(&self) -> InstanceStatus {
    self.status.clone()
}

fn get_metrics(&self) -> HashMap<String, f64> {
    self.metrics.clone()
}
```

// Raft算法实现

```rust
struct RaftAlgorithm;

impl RaftAlgorithm {
    fn new() -> Self {
        RaftAlgorithm
    }
}

impl ConsensusAlgorithm for RaftAlgorithm {
    fn name(&self) -> &str {
        "Raft"
    }
    
    fn create_instance(&self, config: ConsensusConfig) -> Box<dyn ConsensusInstance> {
        Box::new(RaftInstance::new(config))
    }
    
    fn fault_tolerance(&self, nodes: usize) -> usize {
        (nodes - 1) / 2 // Raft容忍少于一半的节点故障
    }
    
    fn message_complexity(&self) -> MessageComplexity {
        MessageComplexity::Linear // 每个操作的消息复杂度为O(n)
    }
    
    fn supports_byzantine_faults(&self) -> bool {
        false // Raft不支持拜占庭故障
    }
}

struct RaftInstance {
    config: ConsensusConfig,
    state: RaftState,
    role: RaftRole,
    current_term: u64,
    voted_for: Option<NodeId>,
    leader_id: Option<NodeId>,
    log: Vec<LogEntry>,
    commit_index: usize,
    last_applied: usize,
    next_index: HashMap<NodeId, usize>,
    match_index: HashMap<NodeId, usize>,
    votes_received: HashSet<NodeId>,
    election_timeout: Duration,
    heartbeat_interval: Duration,
    last_heartbeat: Instant,
    decided_value: Option<Vec<u8>>,
    status: InstanceStatus,
    metrics: HashMap<String, f64>,
}

struct LogEntry {
    term: u64,
    index: usize,
    data: Vec<u8>,
}

enum RaftRole {
    Follower,
    Candidate,
    Leader,
}

enum RaftState {
    Initializing,
    Running,
    Decided,
}

impl RaftInstance {
    fn new(config: ConsensusConfig) -> Self {
        // 初始化随机选举超时，通常在150-300ms之间
        let mut rng = rand::thread_rng();
        let timeout_ms = rng.gen_range(150..300);
        let election_timeout = Duration::from_millis(timeout_ms);
        
        let mut instance = RaftInstance {
            config,
            state: RaftState::Initializing,
            role: RaftRole::Follower,
            current_term: 0,
            voted_for: None,
            leader_id: None,
            log: Vec::new(),
            commit_index: 0,
            last_applied: 0,
            next_index: HashMap::new(),
            match_index: HashMap::new(),
            votes_received: HashSet::new(),
            election_timeout,
            heartbeat_interval: Duration::from_millis(50),
            last_heartbeat: Instant::now(),
            decided_value: None,
            status: InstanceStatus::Initializing,
            metrics: HashMap::new(),
        };
        
        // 初始化每个节点的next_index和match_index
        for node in &instance.config.nodes {
            if &node.id != &instance.config.self_id.id {
                instance.next_index.insert(node.clone(), 1);
                instance.match_index.insert(node.clone(), 0);
            }
        }
        
        instance
    }
    
    fn check_election_timeout(&mut self) {
        if let RaftRole::Follower | RaftRole::Candidate = self.role {
            if self.last_heartbeat.elapsed() > self.election_timeout {
                self.start_election();
            }
        }
    }
    
    fn start_election(&mut self) {
        self.role = RaftRole::Candidate;
        self.current_term += 1;
        self.voted_for = Some(self.config.self_id.clone());
        self.votes_received.clear();
        self.votes_received.insert(self.config.self_id.clone()); // 自己给自己投票
        
        // 重置选举超时
        let mut rng = rand::thread_rng();
        let timeout_ms = rng.gen_range(150..300);
        self.election_timeout = Duration::from_millis(timeout_ms);
        self.last_heartbeat = Instant::now();
        
        // 发送RequestVote消息
        let request_vote_message = ConsensusMessage {
            instance_id: self.config.id.clone(),
            message_type: ConsensusMessageType::RequestVote,
            sender: self.config.self_id.clone(),
            round: self.current_term,
            payload: Vec::new(), // 简化：应包含last_log_index和last_log_term
        };
        
        for node in &self.config.nodes {
            if &node.id != &self.config.self_id.id {
                if let Err(err) = (self.config.message_sender)(node.clone(), request_vote_message.clone()) {
                    println!("向节点 {} 发送RequestVote消息失败: {}", node.id, err.message);
                }
            }
        }
    }
    
    fn handle_request_vote(&mut self, from: &NodeId, message: &ConsensusMessage) -> Result<(), ConsensusError> {
        let term = message.round;
        
        // 如果消息的任期小于当前任期，拒绝投票
        if term < self.current_term {
            let response = ConsensusMessage {
                instance_id: self.config.id.clone(),
                message_type: ConsensusMessageType::RequestVoteResponse,
                sender: self.config.self_id.clone(),
                round: self.current_term,
                payload: vec![0], // 0表示拒绝
            };
            
            (self.config.message_sender)(from.clone(), response)?;
            return Ok(());
        }
        
        // 如果消息的任期大于当前任期，更新任期并转为follower
        if term > self.current_term {
            self.current_term = term;
            self.role = RaftRole::Follower;
            self.voted_for = None;
        }
        
        // 决定是否投票
        let vote_granted = if self.voted_for.is_none() || self.voted_for.as_ref() == Some(from) {
            // 简化：在完整实现中，这里还需要检查日志是否足够新
            true
        } else {
            false
        };
        
        if vote_granted {
            self.voted_for = Some(from.clone());
            self.last_heartbeat = Instant::now(); // 重置选举超时
        }
        
        // 发送投票响应
        let response = ConsensusMessage {
            instance_id: self.config.id.clone(),
            message_type: ConsensusMessageType::RequestVoteResponse,
            sender: self.config.self_id.clone(),
            round: self.current_term,
            payload: if vote_granted { vec![1] } else { vec![0] },
        };
        
        (self.config.message_sender)(from.clone(), response)?;
        
        Ok(())
    }
    
    fn handle_request_vote_response(&mut self, from: &NodeId, message: &ConsensusMessage) -> Result<(), ConsensusError> {
        if message.round != self.current_term || self.role != RaftRole::Candidate {
            return Ok(()); // 忽略过期的响应
        }
        
        // 检查是否获得投票
        if !message.payload.is_empty() && message.payload[0] == 1 {
            self.votes_received.insert(from.clone());
            
            // 检查是否获得多数票
            if self.votes_received.len() > self.config.nodes.len() / 2 {
                // 成为领导者
                self.become_leader();
            }
        }
        
        Ok(())
    }
    
    fn become_leader(&mut self) {
        if self.role != RaftRole::Candidate {
            return;
        }
        
        self.role = RaftRole::Leader;
        self.leader_id = Some(self.config.self_id.clone());
        
        // 初始化领导者状态
        for node in &self.config.nodes {
            if &node.id != &self.config.self_id.id {
                self.next_index.insert(node.clone(), self.log.len() + 1);
                self.match_index.insert(node.clone(), 0);
            }
        }
        
        // 立即发送心跳
        self.send_heartbeat()?;
    }
    
    fn send_heartbeat(&mut self) -> Result<(), ConsensusError> {
        self.last_heartbeat = Instant::now();
        
        // 发送AppendEntries消息作为心跳
        for node in &self.config.nodes {
            if &node.id != &self.config.self_id.id {
                let next_idx = self.next_index.get(node).unwrap_or(&1);
                let prev_log_index = next_idx - 1;
                let prev_log_term = if prev_log_index > 0 && prev_log_index <= self.log.len() {
                    self.log[prev_log_index - 1].term
                } else {
                    0
                };
                
                // 构建心跳消息
                let heartbeat_message = ConsensusMessage {
                    instance_id: self.config.id.clone(),
                    message_type: ConsensusMessageType::AppendEntries,
                    sender: self.config.self_id.clone(),
                    round: self.current_term,
                    payload: Vec::new(), // 简化：应包含prev_log_index、prev_log_term等
                };
                
                if let Err(err) = (self.config.message_sender)(node.clone(), heartbeat_message) {
                    println!("向节点 {} 发送心跳失败: {}", node.id, err.message);
                }
            }
        }
        
        Ok(())
    }
    
    fn handle_append_entries(&mut self, from: &NodeId, message: &ConsensusMessage) -> Result<(), ConsensusError> {
        let term = message.round;
        
        // 如果消息的任期小于当前任期，拒绝
        if term < self.current_term {
            let response = ConsensusMessage {
                instance_id: self.config.id.clone(),
                message_type: ConsensusMessageType::AppendEntriesResponse,
                sender: self.config.self_id.clone(),
                round: self.current_term,
                payload: vec![0], // 0表示失败
            };
            
            (self.config.message_sender)(from.clone(), response)?;
            return Ok(());
        }
        
        // 更新当前任期并转为follower
        if term > self.current_term {
            self.current_term = term;
            self.role = RaftRole::Follower;
            self.voted_for = None;
        }
        
        // 更新领导者ID和选举超时
        self.leader_id = Some(from.clone());
        self.last_heartbeat = Instant::now();
        
        // 简化：在完整实现中，这里需要处理日志复制逻辑
        
        // 发送成功响应
        let response = ConsensusMessage {
            instance_id: self.config.id.clone(),
            message_type: ConsensusMessageType::AppendEntriesResponse,
            sender: self.config.self_id.clone(),
            round: self.current_term,
            payload: vec![1], // 1表示成功
        };
        
        (self.config.message_sender)(from.clone(), response)?;
        
        Ok(())
    }
    
    fn handle_append_entries_response(&mut self, from: &NodeId, message: &ConsensusMessage) -> Result<(), ConsensusError> {
        if message.round != self.current_term || self.role != RaftRole::Leader {
            return Ok(()); // 忽略过期的响应
        }
        
        let success = !message.payload.is_empty() && message.payload[0] == 1;
        
        if success {
            // 更新matchIndex和nextIndex
            // 简化：在完整实现中，这里需要处理提交逻辑
        } else {
            // 减少nextIndex并重试
            if let Some(next_idx) = self.next_index.get_mut(from) {
                *next_idx = (*next_idx).saturating_sub(1);
            }
            
            // 重新发送AppendEntries
            // 简化：完整实现应该立即发送新的AppendEntries
        }
        
        Ok(())
    }
}

impl ConsensusInstance for RaftInstance {
    fn id(&self) -> &str {
        &self.config.id
    }
    
    fn propose(&mut self, value: Vec<u8>) -> Result<(), ConsensusError> {
        if self.role != RaftRole::Leader {
            return Err(ConsensusError {
                message: "只有领导者可以提出值".to_string(),
                error_type: ConsensusErrorType::WrongLeader,
            });
        }
        
        // 添加新的日志条目
        let log_entry = LogEntry {
            term: self.current_term,
            index: self.log.len() + 1,
            data: value,
        };
        
        self.log.push(log_entry);
        
        // 复制日志到所有节点
        // 简化：在完整实现中，这里应该调用replicate_log方法
        
        Ok(())
    }
    
    fn receive_message(&mut self, from: &NodeId, message: ConsensusMessage) -> Result<(), ConsensusError> {
        if message.instance_id != self.config.id {
            return Err(ConsensusError {
                message: "消息实例ID不匹配".to_string(),
                error_type: ConsensusErrorType::InternalError,
            });
        }
        
        match message.message_type {
            ConsensusMessageType::RequestVote => self.handle_request_vote(from, &message),
            ConsensusMessageType::RequestVoteResponse => self.handle_request_vote_response(from, &message),
            ConsensusMessageType::AppendEntries => self.handle_append_entries(from, &message),
            ConsensusMessageType::AppendEntriesResponse => self.handle_append_entries_response(from, &message),
            _ => Err(ConsensusError {
                message: "不支持的消息类型".to_string(),
                error_type: ConsensusErrorType::InternalError,
            }),
        }
    }
    
    fn is_decided(&self) -> bool {
        self.decided_value.is_some()
    }
    
    fn get_decision(&self) -> Option<Vec<u8>> {
        self.decided_value.clone()
    }
    
    fn get_status(&self) -> InstanceStatus {
        self.status.clone()
    }
    
    fn get_metrics(&self) -> HashMap<String, f64> {
        self.metrics.clone()
    }
}

// PBFT (实用拜占庭容错)算法实现
struct PBFTAlgorithm;

impl PBFTAlgorithm {
    fn new() -> Self {
        PBFTAlgorithm
    }
}

impl ConsensusAlgorithm for PBFTAlgorithm {
    fn name(&self) -> &str {
        "PBFT"
    }
    
    fn create_instance(&self, config: ConsensusConfig) -> Box<dyn ConsensusInstance> {
        Box::new(PBFTInstance::new(config))
    }
    
    fn fault_tolerance(&self, nodes: usize) -> usize {
        (nodes - 1) / 3 // PBFT容忍不超过1/3的节点故障
    }
    
    fn message_complexity(&self) -> MessageComplexity {
        MessageComplexity::Cubic // O(n³)
    }
    
    fn supports_byzantine_faults(&self) -> bool {
        true // PBFT支持拜占庭故障
    }
}

struct PBFTInstance {
    config: ConsensusConfig,
    state: PBFTState,
    view: u64,
    sequence_number: u64,
    prepared_messages: HashMap<u64, (Vec<u8>, HashSet<NodeId>)>,
    committed_messages: HashMap<u64, HashSet<NodeId>>,
    is_primary: bool,
    last_checkpoint: u64,
    checkpoint_interval: u64,
    checkpoint_states: HashMap<u64, HashSet<NodeId>>,
    decided_value: Option<Vec<u8>>,
    status: InstanceStatus,
    metrics: HashMap<String, f64>,
}

enum PBFTState {
    Normal,
    ViewChange,
    Decided,
}

impl PBFTInstance {
    fn new(config: ConsensusConfig) -> Self {
        // 确定自己是否是主节点
        let nodes = &config.nodes;
        let self_id = &config.self_id;
        let primary_idx = 0; // 简化：始终选择第一个节点作为主节点
        let is_primary = nodes.get(primary_idx).map(|n| n.id == self_id.id).unwrap_or(false);
        
        PBFTInstance {
            config,
            state: PBFTState::Normal,
            view: 0,
            sequence_number: 0,
            prepared_messages: HashMap::new(),
            committed_messages: HashMap::new(),
            is_primary,
            last_checkpoint: 0,
            checkpoint_interval: 100,
            checkpoint_states: HashMap::new(),
            decided_value: None,
            status: InstanceStatus::Initializing,
            metrics: HashMap::new(),
        }
    }
    
    fn get_primary(&self) -> Option<NodeId> {
        let primary_idx = (self.view as usize) % self.config.nodes.len();
        self.config.nodes.get(primary_idx).cloned()
    }
    
    fn is_self_primary(&self) -> bool {
        if let Some(primary) = self.get_primary() {
            primary.id == self.config.self_id.id
        } else {
            false
        }
    }
    
    fn get_quorum_size(&self) -> usize {
        // PBFT需要2f+1个节点达成共识，其中f是最大容错数量
        let f = self.config.nodes.len() / 3;
        2 * f + 1
    }
    
    fn start_pre_prepare(&mut self, value: Vec<u8>) -> Result<(), ConsensusError> {
        if !self.is_self_primary() {
            return Err(ConsensusError {
                message: "只有主节点可以发起PrePrepare".to_string(),
                error_type: ConsensusErrorType::WrongLeader,
            });
        }
        
        self.sequence_number += 1;
        let seq_num = self.sequence_number;
        
        // 构建PrePrepare消息
        let pre_prepare_message = ConsensusMessage {
            instance_id: self.config.id.clone(),
            message_type: ConsensusMessageType::PrePrepare,
            sender: self.config.self_id.clone(),
            round: seq_num,
            payload: value.clone(),
        };
        
        // 向所有副本发送PrePrepare消息
        for node in &self.config.nodes {
            if &node.id != &self.config.self_id.id {
                if let Err(err) = (self.config.message_sender)(node.clone(), pre_prepare_message.clone()) {
                    println!("向节点 {} 发送PrePrepare消息失败: {}", node.id, err.message);
                }
            }
        }
        
        // 自己处理这条消息
        let mut prepared = HashSet::new();
        prepared.insert(self.config.self_id.clone());
        self.prepared_messages.insert(seq_num, (value, prepared));
        
        Ok(())
    }
    
    fn handle_pre_prepare(&mut self, from: &NodeId, message: &ConsensusMessage) -> Result<(), ConsensusError> {
        let seq_num = message.round;
        
        // 验证发送者是当前视图的主节点
        if let Some(primary) = self.get_primary() {
            if primary.id != from.id {
                return Err(ConsensusError {
                    message: "发送者不是当前视图的主节点".to_string(),
                    error_type: ConsensusErrorType::WrongLeader,
                });
            }
        } else {
            return Err(ConsensusError {
                message: "无法确定主节点".to_string(),
                error_type: ConsensusErrorType::InternalError,
            });
        }
        
        // 检查序列号是否在水位线之内
        // 简化：在完整实现中，需要检查序列号是否在水位线范围内
        
        // 存储PrepareMessage以便后续步骤
        let data = message.payload.clone();
        
        // 构建Prepare消息
        let prepare_message = ConsensusMessage {
            instance_id: self.config.id.clone(),
            message_type: ConsensusMessageType::Prepare,
            sender: self.config.self_id.clone(),
            round: seq_num,
            payload: data.clone(),
        };
        
        // 向所有节点发送Prepare消息
        for node in &self.config.nodes {
            if &node.id != &self.config.self_id.id {
                if let Err(err) = (self.config.message_sender)(node.clone(), prepare_message.clone()) {
                    println!("向节点 {} 发送Prepare消息失败: {}", node.id, err.message);
                }
            }
        }
        
        // 记录自己的Prepare
        if let Some((_, prepared)) = self.prepared_messages.get_mut(&seq_num) {
            prepared.insert(self.config.self_id.clone());
        } else {
            let mut prepared = HashSet::new();
            prepared.insert(self.config.self_id.clone());
            self.prepared_messages.insert(seq_num, (data, prepared));
        }
        
        Ok(())
    }
    
    fn handle_prepare(&mut self, from: &NodeId, message: &ConsensusMessage) -> Result<(), ConsensusError> {
        let seq_num = message.round;
        
        // 记录Prepare消息
        if let Some((data, prepared)) = self.prepared_messages.get_mut(&seq_num) {
            if data == &message.payload {
                prepared.insert(from.clone());
                
                // 检查是否有足够的Prepare
                if prepared.len() >= self.get_quorum_size() {
                    // 进入Commit阶段
                    self.start_commit(seq_num, data.clone())?;
                }
            }
        } else {
            let mut prepared = HashSet::new();
            prepared.insert(from.clone());
            self.prepared_messages.insert(seq_num, (message.payload.clone(), prepared));
        }
        
        Ok(())
    }
    
    fn start_commit(&mut self, seq_num: u64, data: Vec<u8>) -> Result<(), ConsensusError> {
        // 构建Commit消息
        let commit_message = ConsensusMessage {
            instance_id: self.config.id.clone(),
            message_type: ConsensusMessageType::Commit,
            sender: self.config.self_id.clone(),
            round: seq_num,
            payload: data,
        };
        
        // 向所有节点发送Commit消息
        for node in &self.config.nodes {
            if &node.id != &self.config.self_id.id {
                if let Err(err) = (self.config.message_sender)(node.clone(), commit_message.clone()) {
                    println!("向节点 {} 发送Commit消息失败: {}", node.id, err.message);
                }
            }
        }
        
        // 记录自己的Commit
        let mut committed = self.committed_messages.entry(seq_num).or_insert_with(HashSet::new);
        committed.insert(self.config.self_id.clone());
        
        Ok(())
    }
    
    fn handle_commit(&mut self, from: &NodeId, message: &ConsensusMessage) -> Result<(), ConsensusError> {
        let seq_num = message.round;
        
        // 记录Commit消息
        let committed = self.committed_messages.entry(seq_num).or_insert_with(HashSet::new);
        committed.insert(from.clone());
        
        // 检查是否有足够的Commit
        if committed.len() >= self.get_quorum_size() {
            // 确认请求已提交
            if let Some((data, _)) = self.prepared_messages.get(&seq_num) {
                self.decided_value = Some(data.clone());
                self.state = PBFTState::Decided;
                self.status = InstanceStatus::Decided;
                
                // 记录指标
                self.metrics.insert("decision_time".to_string(), 
                                   self.config.start_time.elapsed().as_secs_f64());
                
                // 检查是否需要做检查点
                if seq_num >= self.last_checkpoint + self.checkpoint_interval {
                    self.start_checkpoint(seq_num)?;
                }
            }
        }
        
        Ok(())
    }
    
    fn start_checkpoint(&mut self, seq_num: u64) -> Result<(), ConsensusError> {
        self.last_checkpoint = seq_num;
        
        // 构建Checkpoint消息
        let checkpoint_message = ConsensusMessage {
            instance_id: self.config.id.clone(),
            message_type: ConsensusMessageType::Checkpoint,
            sender: self.config.self_id.clone(),
            round: seq_num,
            payload: Vec::new(), // 简化：应包含状态摘要
        };
        
        // 向所有节点发送Checkpoint消息
        for node in &self.config.nodes {
            if &node.id != &self.config.self_id.id {
                if let Err(err) = (self.config.message_sender)(node.clone(), checkpoint_message.clone()) {
                    println!("向节点 {} 发送Checkpoint消息失败: {}", node.id, err.message);
                }
            }
        }
        
        // 记录自己的Checkpoint
        let checkpoint_states = self.checkpoint_states.entry(seq_num).or_insert_with(HashSet::new);
        checkpoint_states.insert(self.config.self_id.clone());
        
        Ok(())
    }
    
    fn handle_checkpoint(&mut self, from: &NodeId, message: &ConsensusMessage) -> Result<(), ConsensusError> {
        let seq_num = message.round;
        
        // 记录Checkpoint消息
        let checkpoint_states = self.checkpoint_states.entry(seq_num).or_insert_with(HashSet::new);
        checkpoint_states.insert(from.clone());
        
        // 检查是否有足够的Checkpoint
        if checkpoint_states.len() >= self.get_quorum_size() {
            // 稳定检查点
            // 简化：在完整实现中，应该在这里垃圾回收已确认的消息
            
            // 更新最后的检查点
            if seq_num > self.last_checkpoint {
                self.last_checkpoint = seq_num;
            }
        }
        
        Ok(())
    }
    
    fn start_view_change(&mut self, new_view: u64) -> Result<(), ConsensusError> {
        if new_view <= self.view {
            return Ok(());
        }
        
        self.state = PBFTState::ViewChange;
        
        // 构建ViewChange消息
        let view_change_message = ConsensusMessage {
            instance_id: self.config.id.clone(),
            message_type: ConsensusMessageType::ViewChange,
            sender: self.config.self_id.clone(),
            round: new_view,
            payload: Vec::new(), // 简化：应包含检查点和准备好的消息
        };
        
        // 向所有节点发送ViewChange消息
        for node in &self.config.nodes {
            if &node.id != &self.config.self_id.id {
                if let Err(err) = (self.config.message_sender)(node.clone(), view_change_message.clone()) {
                    println!("向节点 {} 发送ViewChange消息失败: {}", node.id, err.message);
                }
            }
        }
        
        Ok(())
    }
}

impl ConsensusInstance for PBFTInstance {
    fn id(&self) -> &str {
        &self.config.id
    }
    
    fn propose(&mut self, value: Vec<u8>) -> Result<(), ConsensusError> {
        if !self.is_self_primary() {
            return Err(ConsensusError {
                message: "只有主节点可以提出值".to_string(),
                error_type: ConsensusErrorType::WrongLeader,
            });
        }
        
        self.start_pre_prepare(value)
    }
    
    fn receive_message(&mut self, from: &NodeId, message: ConsensusMessage) -> Result<(), ConsensusError> {
        if message.instance_id != self.config.id {
            return Err(ConsensusError {
                message: "消息实例ID不匹配".to_string(),
                error_type: ConsensusErrorType::InternalError,
            });
        }
        
        match message.message_type {
            ConsensusMessageType::PrePrepare => self.handle_pre_prepare(from, &message),
            ConsensusMessageType::Prepare => self.handle_prepare(from, &message),
            ConsensusMessageType::Commit => self.handle_commit(from, &message),
            ConsensusMessageType::Checkpoint => self.handle_checkpoint(from, &message),
            ConsensusMessageType::ViewChange => {
                // 简化：在完整实现中，应该处理视图变更
                Ok(())
            },
            _ => Err(ConsensusError {
                message: "不支持的消息类型".to_string(),
                error_type: ConsensusErrorType::InternalError,
            }),
        }
    }
    
    fn is_decided(&self) -> bool {
        self.decided_value.is_some()
    }
    
    fn get_decision(&self) -> Option<Vec<u8>> {
        self.decided_value.clone()
    }
    
    fn get_status(&self) -> InstanceStatus {
        self.status.clone()
    }
    
    fn get_metrics(&self) -> HashMap<String, f64> {
        self.metrics.clone()
    }
}
```

### 4.3 分布式事务框架

分布式事务框架允许跨多个节点的原子操作，确保所有节点要么全部提交，要么全部回滚。

```rust
struct DistributedTransactionFramework {
    transaction_managers: HashMap<String, Box<dyn TransactionManager>>,
    active_transactions: HashMap<String, TransactionState>,
}

trait TransactionManager: Send + Sync {
    fn name(&self) -> &str;
    fn begin_transaction(&self, tx_id: &str) -> Result<(), TransactionError>;
    fn prepare(&self, tx_id: &str) -> Result<PrepareResult, TransactionError>;
    fn commit(&self, tx_id: &str) -> Result<(), TransactionError>;
    fn abort(&self, tx_id: &str) -> Result<(), TransactionError>;
    fn get_status(&self, tx_id: &str) -> Result<TransactionStatus, TransactionError>;
}

enum TransactionStatus {
    Active,
    Preparing,
    Prepared,
    Committing,
    Committed,
    Aborting,
    Aborted,
    Unknown,
}

struct TransactionState {
    id: String,
    coordinator: String,
    participants: Vec<String>,
    status: TransactionStatus,
    start_time: Instant,
    prepare_results: HashMap<String, PrepareResult>,
    commit_results: HashMap<String, bool>,
    abort_results: HashMap<String, bool>,
}

enum PrepareResult {
    Ready,
    NotReady,
}

struct TransactionError {
    message: String,
    error_type: TransactionErrorType,
}

enum TransactionErrorType {
    AlreadyExists,
    NotFound,
    Timeout,
    NetworkError,
    ParticipantError,
    InternalError,
}

impl DistributedTransactionFramework {
    fn new() -> Self {
        DistributedTransactionFramework {
            transaction_managers: HashMap::new(),
            active_transactions: HashMap::new(),
        }
    }
    
    fn register_manager(&mut self, name: &str, manager: Box<dyn TransactionManager>) -> Result<(), String> {
        if self.transaction_managers.contains_key(name) {
            return Err(format!("事务管理器 '{}' 已经注册", name));
        }
        
        self.transaction_managers.insert(name.to_string(), manager);
        Ok(())
    }
    
    fn begin_transaction(&mut self, tx_id: &str, coordinator: &str, participants: Vec<String>) -> Result<(), TransactionError> {
        // 检查事务ID是否已存在
        if self.active_transactions.contains_key(tx_id) {
            return Err(TransactionError {
                message: format!("事务 '{}' 已经存在", tx_id),
                error_type: TransactionErrorType::AlreadyExists,
            });
        }
        
        // 检查协调者和参与者是否都已注册
        if !self.transaction_managers.contains_key(coordinator) {
            return Err(TransactionError {
                message: format!("协调者 '{}' 未注册", coordinator),
                error_type: TransactionErrorType::NotFound,
            });
        }
        
        for participant in &participants {
            if !self.transaction_managers.contains_key(participant) {
                return Err(TransactionError {
                    message: format!("参与者 '{}' 未注册", participant),
                    error_type: TransactionErrorType::NotFound,
                });
            }
        }
        
        // 创建事务状态
        let transaction_state = TransactionState {
            id: tx_id.to_string(),
            coordinator: coordinator.to_string(),
            participants,
            status: TransactionStatus::Active,
            start_time: Instant::now(),
            prepare_results: HashMap::new(),
            commit_results: HashMap::new(),
            abort_results: HashMap::new(),
        };
        
        // 在所有参与者中开始事务
        if let Some(coordinator_manager) = self.transaction_managers.get(coordinator) {
            if let Err(err) = coordinator_manager.begin_transaction(tx_id) {
                return Err(err);
            }
        }
        
        for participant in &transaction_state.participants {
            if let Some(participant_manager) = self.transaction_managers.get(participant) {
                if let Err(err) = participant_manager.begin_transaction(tx_id) {
                    // 如果开始失败，应该回滚已经开始的事务
                    // 简化：在完整实现中，应该回滚已经开始的事务
                    return Err(err);
                }
            }
        }
        
        self.active_transactions.insert(tx_id.to_string(), transaction_state);
        
        Ok(())
    }
    
fn prepare_transaction(&mut self, tx_id: &str) -> Result<bool, TransactionError> {
    // 检查事务是否存在
    let transaction = match self.active_transactions.get_mut(tx_id) {
        Some(tx) => tx,
        None => return Err(TransactionError {
            message: format!("事务 '{}' 不存在", tx_id),
            error_type: TransactionErrorType::NotFound,
        }),
    };
    
    // 更新事务状态
    transaction.status = TransactionStatus::Preparing;
    
    // 向所有参与者发送Prepare消息
    for participant in &transaction.participants {
        if let Some(participant_manager) = self.transaction_managers.get(participant) {
            match participant_manager.prepare(tx_id) {
                Ok(result) => {
                    transaction.prepare_results.insert(participant.clone(), result);
                },
                Err(err) => {
                    // 如果任何参与者Prepare失败，则中止事务
                    transaction.status = TransactionStatus::Aborting;
                    return Err(err);
                }
            }
        }
    }
    
    // 检查所有参与者是否都准备好
    let all_ready = transaction.prepare_results.values()
        .all(|result| matches!(result, PrepareResult::Ready));
    
    // 根据Prepare结果更新事务状态
    if all_ready {
        transaction.status = TransactionStatus::Prepared;
        Ok(true)
    } else {
        transaction.status = TransactionStatus::Aborting;
        Ok(false)
    }
}

fn commit_transaction(&mut self, tx_id: &str) -> Result<(), TransactionError> {
    // 检查事务是否存在
    let transaction = match self.active_transactions.get_mut(tx_id) {
        Some(tx) => tx,
        None => return Err(TransactionError {
            message: format!("事务 '{}' 不存在", tx_id),
            error_type: TransactionErrorType::NotFound,
        }),
    };
    
    // 检查事务是否处于Prepared状态
    if !matches!(transaction.status, TransactionStatus::Prepared) {
        return Err(TransactionError {
            message: format!("事务 '{}' 不处于Prepared状态", tx_id),
            error_type: TransactionErrorType::InternalError,
        });
    }
    
    // 更新事务状态
    transaction.status = TransactionStatus::Committing;
    
    // 向所有参与者发送Commit消息
    for participant in &transaction.participants {
        if let Some(participant_manager) = self.transaction_managers.get(participant) {
            match participant_manager.commit(tx_id) {
                Ok(()) => {
                    transaction.commit_results.insert(participant.clone(), true);
                },
                Err(err) => {
                    // 记录提交错误，但继续尝试其他参与者
                    transaction.commit_results.insert(participant.clone(), false);
                    println!("参与者 {} 提交失败: {}", participant, err.message);
                }
            }
        }
    }
    
    // 更新事务状态为Committed
    transaction.status = TransactionStatus::Committed;
    
    Ok(())
}

fn abort_transaction(&mut self, tx_id: &str) -> Result<(), TransactionError> {
    // 检查事务是否存在
    let transaction = match self.active_transactions.get_mut(tx_id) {
        Some(tx) => tx,
        None => return Err(TransactionError {
            message: format!("事务 '{}' 不存在", tx_id),
            error_type: TransactionErrorType::NotFound,
        }),
    };
    
    // 更新事务状态
    transaction.status = TransactionStatus::Aborting;
    
    // 向所有参与者发送Abort消息
    for participant in &transaction.participants {
        if let Some(participant_manager) = self.transaction_managers.get(participant) {
            match participant_manager.abort(tx_id) {
                Ok(()) => {
                    transaction.abort_results.insert(participant.clone(), true);
                },
                Err(err) => {
                    // 记录中止错误，但继续尝试其他参与者
                    transaction.abort_results.insert(participant.clone(), false);
                    println!("参与者 {} 中止失败: {}", participant, err.message);
                }
            }
        }
    }
    
    // 更新事务状态为Aborted
    transaction.status = TransactionStatus::Aborted;
    
    Ok(())
}

fn get_transaction_status(&self, tx_id: &str) -> Result<TransactionStatus, TransactionError> {
    // 检查事务是否存在
    match self.active_transactions.get(tx_id) {
        Some(tx) => Ok(tx.status.clone()),
        None => Err(TransactionError {
            message: format!("事务 '{}' 不存在", tx_id),
            error_type: TransactionErrorType::NotFound,
        }),
    }
}

fn cleanup_transaction(&mut self, tx_id: &str) -> Result<(), TransactionError> {
    // 检查事务是否存在
    if !self.active_transactions.contains_key(tx_id) {
        return Err(TransactionError {
            message: format!("事务 '{}' 不存在", tx_id),
            error_type: TransactionErrorType::NotFound,
        });
    }
    
    // 移除事务
    self.active_transactions.remove(tx_id);
    
    Ok(())
}

fn execute_two_phase_commit(&mut self, tx_id: &str) -> Result<bool, TransactionError> {
    // 第一阶段：准备
    let prepare_result = self.prepare_transaction(tx_id)?;
    
    // 第二阶段：根据准备结果决定提交或中止
    if prepare_result {
        // 所有参与者都准备好，提交事务
        self.commit_transaction(tx_id)?;
        Ok(true)
    } else {
        // 至少有一个参与者未准备好，中止事务
        self.abort_transaction(tx_id)?;
        Ok(false)
    }
}

fn get_transaction_metrics(&self, tx_id: &str) -> Result<HashMap<String, f64>, TransactionError> {
    // 检查事务是否存在
    let transaction = match self.active_transactions.get(tx_id) {
        Some(tx) => tx,
        None => return Err(TransactionError {
            message: format!("事务 '{}' 不存在", tx_id),
            error_type: TransactionErrorType::NotFound,
        }),
    };
    
    let mut metrics = HashMap::new();
    
    // 计算事务持续时间
    metrics.insert("duration".to_string(), transaction.start_time.elapsed().as_secs_f64());
    
    // 计算参与者数量
    metrics.insert("participants".to_string(), transaction.participants.len() as f64);
    
    // 计算准备率
    let prepare_rate = if transaction.prepare_results.is_empty() {
        0.0
    } else {
        let ready_count = transaction.prepare_results.values()
            .filter(|result| matches!(result, PrepareResult::Ready))
            .count();
        ready_count as f64 / transaction.prepare_results.len() as f64
    };
    metrics.insert("prepare_rate".to_string(), prepare_rate);
    
    // 计算提交率
    let commit_rate = if transaction.commit_results.is_empty() {
        0.0
    } else {
        let success_count = transaction.commit_results.values()
            .filter(|&success| *success)
            .count();
        success_count as f64 / transaction.commit_results.len() as f64
    };
    metrics.insert("commit_rate".to_string(), commit_rate);
    
    Ok(metrics)
}
```

// 两阶段提交实现

```rust
struct TwoPhaseCommitManager {
    resource_manager: Arc<RwLock<ResourceManager>>,
    transaction_log: Arc<RwLock<TransactionLog>>,
    node_id: String,
    timeout: Duration,
}

struct ResourceManager {
    resources: HashMap<String, Resource>,
    locks: HashMap<String, String>, // 资源ID -> 事务ID
    prepared_resources: HashMap<String, HashMap<String, Resource>>, // 事务ID -> (资源ID -> 资源)
}

struct Resource {
    id: String,
    value: Vec<u8>,
    version: u64,
}

struct TransactionLog {
    entries: HashMap<String, TransactionLogEntry>,
}

struct TransactionLogEntry {
    tx_id: String,
    status: TransactionStatus,
    participants: Vec<String>,
    resources: Vec<String>,
    coordinator: String,
    timestamp: Instant,
}

impl TwoPhaseCommitManager {
    fn new(node_id: &str, timeout: Duration) -> Self {
        TwoPhaseCommitManager {
            resource_manager: Arc::new(RwLock::new(ResourceManager {
                resources: HashMap::new(),
                locks: HashMap::new(),
                prepared_resources: HashMap::new(),
            })),
            transaction_log: Arc::new(RwLock::new(TransactionLog {
                entries: HashMap::new(),
            })),
            node_id: node_id.to_string(),
            timeout,
        }
    }
    
    fn create_resource(&self, resource_id: &str, value: Vec<u8>) -> Result<(), TransactionError> {
        let mut resource_manager = self.resource_manager.write().unwrap();
        
        if resource_manager.resources.contains_key(resource_id) {
            return Err(TransactionError {
                message: format!("资源 '{}' 已经存在", resource_id),
                error_type: TransactionErrorType::AlreadyExists,
            });
        }
        
        resource_manager.resources.insert(resource_id.to_string(), Resource {
            id: resource_id.to_string(),
            value,
            version: 1,
        });
        
        Ok(())
    }
    
    fn update_resource(&self, tx_id: &str, resource_id: &str, value: Vec<u8>) -> Result<(), TransactionError> {
        let mut resource_manager = self.resource_manager.write().unwrap();
        
        // 检查资源是否存在
        if !resource_manager.resources.contains_key(resource_id) {
            return Err(TransactionError {
                message: format!("资源 '{}' 不存在", resource_id),
                error_type: TransactionErrorType::NotFound,
            });
        }
        
        // 检查资源是否被锁定
        if let Some(lock_tx_id) = resource_manager.locks.get(resource_id) {
            if lock_tx_id != tx_id {
                return Err(TransactionError {
                    message: format!("资源 '{}' 已被事务 '{}' 锁定", resource_id, lock_tx_id),
                    error_type: TransactionErrorType::ParticipantError,
                });
            }
        } else {
            // 锁定资源
            resource_manager.locks.insert(resource_id.to_string(), tx_id.to_string());
        }
        
        // 更新资源的待提交版本
        let prepared_resources = resource_manager.prepared_resources
            .entry(tx_id.to_string())
            .or_insert_with(HashMap::new);
        
        if let Some(resource) = resource_manager.resources.get(resource_id) {
            prepared_resources.insert(resource_id.to_string(), Resource {
                id: resource_id.to_string(),
                value,
                version: resource.version + 1,
            });
        }
        
        Ok(())
    }
    
    fn prepare_resources(&self, tx_id: &str) -> Result<(), TransactionError> {
        let resource_manager = self.resource_manager.read().unwrap();
        
        // 检查事务是否有准备好的资源
        if !resource_manager.prepared_resources.contains_key(tx_id) {
            return Err(TransactionError {
                message: format!("事务 '{}' 没有准备好的资源", tx_id),
                error_type: TransactionErrorType::NotFound,
            });
        }
        
        // 在实际实现中，这里应该将准备好的资源写入持久化存储
        
        Ok(())
    }
    
    fn commit_resources(&self, tx_id: &str) -> Result<(), TransactionError> {
        let mut resource_manager = self.resource_manager.write().unwrap();
        
        // 检查事务是否有准备好的资源
        let prepared_resources = match resource_manager.prepared_resources.remove(tx_id) {
            Some(resources) => resources,
            None => return Err(TransactionError {
                message: format!("事务 '{}' 没有准备好的资源", tx_id),
                error_type: TransactionErrorType::NotFound,
            }),
        };
        
        // 提交所有准备好的资源
        for (resource_id, prepared_resource) in prepared_resources {
            resource_manager.resources.insert(resource_id.clone(), prepared_resource);
            resource_manager.locks.remove(&resource_id);
        }
        
        Ok(())
    }
    
    fn abort_resources(&self, tx_id: &str) -> Result<(), TransactionError> {
        let mut resource_manager = self.resource_manager.write().unwrap();
        
        // 移除所有准备好的资源
        resource_manager.prepared_resources.remove(tx_id);
        
        // 释放所有被事务锁定的资源
        for (resource_id, lock_tx_id) in resource_manager.locks.clone() {
            if lock_tx_id == tx_id {
                resource_manager.locks.remove(&resource_id);
            }
        }
        
        Ok(())
    }
    
    fn log_transaction(&self, tx_id: &str, status: TransactionStatus, participants: Vec<String>, resources: Vec<String>, coordinator: &str) -> Result<(), TransactionError> {
        let mut transaction_log = self.transaction_log.write().unwrap();
        
        transaction_log.entries.insert(tx_id.to_string(), TransactionLogEntry {
            tx_id: tx_id.to_string(),
            status,
            participants,
            resources,
            coordinator: coordinator.to_string(),
            timestamp: Instant::now(),
        });
        
        Ok(())
    }
    
    fn update_log_status(&self, tx_id: &str, status: TransactionStatus) -> Result<(), TransactionError> {
        let mut transaction_log = self.transaction_log.write().unwrap();
        
        if let Some(entry) = transaction_log.entries.get_mut(tx_id) {
            entry.status = status;
            Ok(())
        } else {
            Err(TransactionError {
                message: format!("事务日志 '{}' 不存在", tx_id),
                error_type: TransactionErrorType::NotFound,
            })
        }
    }
}

impl TransactionManager for TwoPhaseCommitManager {
    fn name(&self) -> &str {
        &self.node_id
    }
    
    fn begin_transaction(&self, tx_id: &str) -> Result<(), TransactionError> {
        // 记录事务开始
        self.log_transaction(tx_id, TransactionStatus::Active, Vec::new(), Vec::new(), "")?;
        
        Ok(())
    }
    
    fn prepare(&self, tx_id: &str) -> Result<PrepareResult, TransactionError> {
        // 准备阶段
        match self.prepare_resources(tx_id) {
            Ok(()) => {
                // 更新事务日志
                self.update_log_status(tx_id, TransactionStatus::Prepared)?;
                Ok(PrepareResult::Ready)
            },
            Err(err) => {
                // 准备失败
                self.update_log_status(tx_id, TransactionStatus::Aborted)?;
                Err(err)
            }
        }
    }
    
    fn commit(&self, tx_id: &str) -> Result<(), TransactionError> {
        // 提交阶段
        match self.commit_resources(tx_id) {
            Ok(()) => {
                // 更新事务日志
                self.update_log_status(tx_id, TransactionStatus::Committed)?;
                Ok(())
            },
            Err(err) => {
                // 提交失败（极少发生，因为已经准备好）
                self.update_log_status(tx_id, TransactionStatus::Aborted)?;
                Err(err)
            }
        }
    }
    
    fn abort(&self, tx_id: &str) -> Result<(), TransactionError> {
        // 中止阶段
        match self.abort_resources(tx_id) {
            Ok(()) => {
                // 更新事务日志
                self.update_log_status(tx_id, TransactionStatus::Aborted)?;
                Ok(())
            },
            Err(err) => {
                // 中止失败（应该很少发生）
                Err(err)
            }
        }
    }
    
    fn get_status(&self, tx_id: &str) -> Result<TransactionStatus, TransactionError> {
        let transaction_log = self.transaction_log.read().unwrap();
        
        if let Some(entry) = transaction_log.entries.get(tx_id) {
            Ok(entry.status.clone())
        } else {
            Err(TransactionError {
                message: format!("事务 '{}' 不存在", tx_id),
                error_type: TransactionErrorType::NotFound,
            })
        }
    }
}

// 三阶段提交实现
struct ThreePhaseCommitManager {
    resource_manager: Arc<RwLock<ResourceManager>>,
    transaction_log: Arc<RwLock<TransactionLog>>,
    node_id: String,
    timeout: Duration,
}

impl ThreePhaseCommitManager {
    fn new(node_id: &str, timeout: Duration) -> Self {
        ThreePhaseCommitManager {
            resource_manager: Arc::new(RwLock::new(ResourceManager {
                resources: HashMap::new(),
                locks: HashMap::new(),
                prepared_resources: HashMap::new(),
            })),
            transaction_log: Arc::new(RwLock::new(TransactionLog {
                entries: HashMap::new(),
            })),
            node_id: node_id.to_string(),
            timeout,
        }
    }
    
    // 可重用TwoPhaseCommitManager中的大部分方法
    
    fn pre_commit(&self, tx_id: &str) -> Result<(), TransactionError> {
        // 检查事务状态
        let transaction_log = self.transaction_log.read().unwrap();
        
        if let Some(entry) = transaction_log.entries.get(tx_id) {
            if entry.status != TransactionStatus::Prepared {
                return Err(TransactionError {
                    message: format!("事务 '{}' 不处于Prepared状态", tx_id),
                    error_type: TransactionErrorType::InternalError,
                });
            }
        } else {
            return Err(TransactionError {
                message: format!("事务 '{}' 不存在", tx_id),
                error_type: TransactionErrorType::NotFound,
            });
        }
        
        drop(transaction_log);
        
        // 更新事务日志状态为PreCommitted
        self.update_log_status(tx_id, TransactionStatus::PreCommitted)?;
        
        Ok(())
    }
}

impl TransactionManager for ThreePhaseCommitManager {
    fn name(&self) -> &str {
        &self.node_id
    }
    
    fn begin_transaction(&self, tx_id: &str) -> Result<(), TransactionError> {
        // 复用TwoPhaseCommitManager的实现
        let two_phase_manager = TwoPhaseCommitManager {
            resource_manager: self.resource_manager.clone(),
            transaction_log: self.transaction_log.clone(),
            node_id: self.node_id.clone(),
            timeout: self.timeout,
        };
        
        two_phase_manager.begin_transaction(tx_id)
    }
    
    fn prepare(&self, tx_id: &str) -> Result<PrepareResult, TransactionError> {
        // 复用TwoPhaseCommitManager的实现
        let two_phase_manager = TwoPhaseCommitManager {
            resource_manager: self.resource_manager.clone(),
            transaction_log: self.transaction_log.clone(),
            node_id: self.node_id.clone(),
            timeout: self.timeout,
        };
        
        two_phase_manager.prepare(tx_id)
    }
    
    fn commit(&self, tx_id: &str) -> Result<(), TransactionError> {
        // 三阶段提交的提交流程：先PreCommit，再Commit
        self.pre_commit(tx_id)?;
        
        // 然后执行实际的提交
        let two_phase_manager = TwoPhaseCommitManager {
            resource_manager: self.resource_manager.clone(),
            transaction_log: self.transaction_log.clone(),
            node_id: self.node_id.clone(),
            timeout: self.timeout,
        };
        
        two_phase_manager.commit(tx_id)
    }
    
    fn abort(&self, tx_id: &str) -> Result<(), TransactionError> {
        // 复用TwoPhaseCommitManager的实现
        let two_phase_manager = TwoPhaseCommitManager {
            resource_manager: self.resource_manager.clone(),
            transaction_log: self.transaction_log.clone(),
            node_id: self.node_id.clone(),
            timeout: self.timeout,
        };
        
        two_phase_manager.abort(tx_id)
    }
    
    fn get_status(&self, tx_id: &str) -> Result<TransactionStatus, TransactionError> {
        // 复用TwoPhaseCommitManager的实现
        let two_phase_manager = TwoPhaseCommitManager {
            resource_manager: self.resource_manager.clone(),
            transaction_log: self.transaction_log.clone(),
            node_id: self.node_id.clone(),
            timeout: self.timeout,
        };
        
        two_phase_manager.get_status(tx_id)
    }
}
```

### 4.4 分布式追踪系统

分布式追踪系统对跨多个服务边界的请求进行追踪，帮助识别性能瓶颈和故障根源。

```rust
struct DistributedTracingSystem {
    tracers: HashMap<String, Box<dyn Tracer>>,
    active_traces: HashMap<String, TraceContext>,
    exporters: Vec<Box<dyn TraceExporter>>,
    sampling_rate: f64,
    propagation_headers: Vec<String>,
}

trait Tracer: Send + Sync {
    fn name(&self) -> &str;
    fn start_span(&self, trace_id: &str, parent_span_id: Option<&str>, operation_name: &str) -> Result<String, TracingError>;
    fn end_span(&self, span_id: &str) -> Result<(), TracingError>;
    fn add_event(&self, span_id: &str, event_name: &str, attributes: HashMap<String, String>) -> Result<(), TracingError>;
    fn set_attribute(&self, span_id: &str, key: &str, value: &str) -> Result<(), TracingError>;
    fn set_status(&self, span_id: &str, status: SpanStatus) -> Result<(), TracingError>;
    fn get_context(&self, span_id: &str) -> Result<TraceContext, TracingError>;
}

trait TraceExporter: Send + Sync {
    fn name(&self) -> &str;
    fn export(&self, spans: Vec<SpanData>) -> Result<(), ExportError>;
    fn shutdown(&self) -> Result<(), ExportError>;
}

struct TraceContext {
    trace_id: String,
    span_id: String,
    parent_span_id: Option<String>,
    attributes: HashMap<String, String>,
    baggage: HashMap<String, String>,
}

struct SpanData {
    trace_id: String,
    span_id: String,
    parent_span_id: Option<String>,
    operation_name: String,
    start_time: Instant,
    end_time: Option<Instant>,
    status: SpanStatus,
    attributes: HashMap<String, String>,
    events: Vec<SpanEvent>,
}

struct SpanEvent {
    name: String,
    timestamp: Instant,
    attributes: HashMap<String, String>,
}

enum SpanStatus {
    Ok,
    Error(String),
    Unset,
}

struct TracingError {
    message: String,
    error_type: TracingErrorType,
}

enum TracingErrorType {
    SpanNotFound,
    TraceNotFound,
    InvalidContext,
    ExportError,
    InternalError,
}

struct ExportError {
    message: String,
    error_type: ExportErrorType,
}

enum ExportErrorType {
    ConnectionFailed,
    Timeout,
    InvalidData,
    ShutdownError,
}

impl DistributedTracingSystem {
    fn new(sampling_rate: f64) -> Self {
        let mut propagation_headers = Vec::new();
        propagation_headers.push("traceparent".to_string());
        propagation_headers.push("tracestate".to_string());
        propagation_headers.push("baggage".to_string());
        
        DistributedTracingSystem {
            tracers: HashMap::new(),
            active_traces: HashMap::new(),
            exporters: Vec::new(),
            sampling_rate,
            propagation_headers,
        }
    }
    
    fn register_tracer(&mut self, name: &str, tracer: Box<dyn Tracer>) -> Result<(), String> {
        if self.tracers.contains_key(name) {
            return Err(format!("追踪器 '{}' 已经注册", name));
        }
        
        self.tracers.insert(name.to_string(), tracer);
        Ok(())
    }
    
    fn add_exporter(&mut self, exporter: Box<dyn TraceExporter>) {
        self.exporters.push(exporter);
    }
    
    fn should_sample(&self) -> bool {
        let mut rng = rand::thread_rng();
        rng.gen::<f64>() < self.sampling_rate
    }
    
    fn generate_trace_id() -> String {
        let mut rng = rand::thread_rng();
        let random_bytes: [u8; 16] = rng.gen();
        hex::encode(random_bytes)
    }
    
    fn generate_span_id() -> String {
        let mut rng = rand::thread_rng();
        let random_bytes: [u8; 8] = rng.gen();
        hex::encode(random_bytes)
    }
    
    fn start_trace(&mut self, operation_name: &str, tracer_name: &str) -> Result<TraceContext, TracingError> {
        // 决定是否采样
        if !self.should_sample() {
            // 返回一个无操作的上下文
            return Ok(TraceContext {
                trace_id: "00000000000000000000000000000000".to_string(),
                span_id: "0000000000000000".to_string(),
                parent_span_id: None,
                attributes: HashMap::new(),
                baggage: HashMap::new(),
            });
        }
        
        // 生成新的追踪ID
        let trace_id = Self::generate_trace_id();
        
        // 通过指定的追踪器创建根span
        if let Some(tracer) = self.tracers.get(tracer_name) {
            let span_id = tracer.start_span(&trace_id, None, operation_name)?;
            
            // 创建追踪上下文
            let context = TraceContext {
                trace_id: trace_id.clone(),
                span_id,
                parent_span_id: None,
                attributes: HashMap::new(),
                baggage: HashMap::new(),
            };
            
            // 保存活动追踪
            self.active_traces.insert(trace_id.clone(), context.clone());
            
            Ok(context)
        } else {
            Err(TracingError {
                message: format!("追踪器 '{}' 未注册", tracer_name),
                error_type: TracingErrorType::InternalError,
            })
        }
    }
    
    fn start_span(&mut self, parent_context: &TraceContext, operation_name: &str, tracer_name: &str) -> Result<TraceContext, TracingError> {
        // 检查追踪ID是否有效
        if parent_context.trace_id == "00000000000000000000000000000000" {
            // 无操作的上下文
            return Ok(TraceContext {
                trace_id: "00000000000000000000000000000000".to_string(),
                span_id: "0000000000000000".to_string(),
                parent_span_id: None,
                attributes: HashMap::new(),
                baggage: HashMap::new(),
            });
        }
        
        // 通过指定的追踪器创建子span
        if let Some(tracer) = self.tracers.get(tracer_name) {
            let span_id = tracer.start_span(
                &parent_context.trace_id, 
                Some(&parent_context.span_id), 
                operation_name
            )?;
            
            // 创建新的上下文
            let context = TraceContext {
                trace_id: parent_context.trace_id.clone(),
                span_id,
                parent_span_id: Some(parent_context.span_id.clone()),
                attributes: HashMap::new(),
                baggage: parent_context.baggage.clone(), // 继承baggage
            };
            
            Ok(context)
        } else {
            Err(TracingError {
                message: format!("追踪器 '{}' 未注册", tracer_name),
                error_type: TracingErrorType::InternalError,
            })
        }
    }
    
    fn end_span(&mut self, context: &TraceContext, tracer_name: &str) -> Result<(), TracingError> {
        // 检查上下文是否有效
        if context.trace_id == "00000000000000000000000000000000" {
            // 无操作的上下文
            return Ok(());
        }
        
        // 通过指定的追踪器结束span
        if let Some(tracer) = self.tracers.get(tracer_name) {
            tracer.end_span(&context.span_id)?;
            
            // 如果是根span，导出追踪数据
            if context.parent_span_id.is_none() {
                if let Some(active_context) = self.active_traces.remove(&context.trace_id) {
                    // 从追踪器中获取span数据
                    if let Ok(span_data) = self.collect_spans(&context.trace_id, tracer_name) {
                        // 导出span数据
                        for exporter in &self.exporters {
                            if let Err(err) = exporter.export(span_data.clone()) {
                                println!("导出追踪数据失败: {}", err.message);
                            }
                        }
                    }
                }
            }
            
            Ok(())
        } else {
            Err(TracingError {
                message: format!("追踪器 '{}' 未注册", tracer_name),
                error_type: TracingErrorType::InternalError,
            })
        }
    }
    
    fn collect_spans(&self, trace_id: &str, tracer_name: &str) -> Result<Vec<SpanData>, TracingError> {
        // 实际实现中，这会从追踪器存储中检索所有与给定trace_id相关的span
        // 简化实现：返回一个空向量
        Ok(Vec::new())
    }
    
    fn inject_context(&self, context: &TraceContext, carrier: &mut HashMap<String, String>) {
        // 检查上下文是否有效
        if context.trace_id == "00000000000000000000000000000000" {
            return;
        }
        
        // 注入W3C TraceContext格式
        let version = "00";
        let trace_flags = "01"; // 采样
        let traceparent = format!(
            "{}-{}-{}-{}",
            version,
            context.trace_id,
            context.span_id,
            trace_flags
        );
        carrier.insert("traceparent".to_string(), traceparent);
        
        // 注入baggage
        if !context.baggage.is_empty() {
            let baggage: Vec<String> = context.baggage
                .iter()
                .map(|(k, v)| format!("{}={}", k, v))
                .collect();
            
            carrier.insert("baggage".to_string(), baggage.join(","));
        }
    }
    
    fn extract_context(&self, carrier: &HashMap<String, String>) -> Result<TraceContext, TracingError> {
        // 尝试提取W3C TraceContext
        if let Some(traceparent) = carrier.get("traceparent") {
            let parts: Vec<&str> = traceparent.split('-').collect();
            if parts.len() == 4 {
                let trace_id = parts[1].to_string();
                let span_id = parts[2].to_string();
                
                // 解析baggage
                let mut baggage = HashMap::new();
                if let Some(baggage_str) = carrier.get("baggage") {
                    for pair in baggage_str.split(',') {
                        let kv: Vec<&str> = pair.split('=').collect();
                        if kv.len() == 2 {
                            baggage.insert(kv[0].trim().to_string(), kv[1].trim().to_string());
                        }
                    }
                }
                
                return Ok(TraceContext {
                    trace_id,
                    span_id,
                    parent_span_id: None, // 父span标识符在远程调用中不相关
                    attributes: HashMap::new(),
                    baggage,
                });
            }
        }
        
        Err(TracingError {
            message: "无法从载体中提取追踪上下文".to_string(),
            error_type: TracingErrorType::InvalidContext,
        })
    }
    
    fn add_baggage(&mut self, context: &mut TraceContext, key: &str, value: &str) {
        if context.trace_id != "00000000000000000000000000000000" {
            context.baggage.insert(key.to_string(), value.to_string());
        }
    }
    
    fn get_baggage(&self, context: &TraceContext, key: &str) -> Option<String> {
        context.baggage.get(key).cloned()
    }
    
    fn shutdown(&mut self) -> Result<(), ExportError> {
        for exporter in &self.exporters {
            if let Err(err) = exporter.shutdown() {
                return Err(err);
            }
        }
        
        Ok(())
    }
}
```

```rust
// 内存中追踪器实现
struct InMemoryTracer {
    spans: Arc<RwLock<HashMap<String, SpanData>>>,
    id_prefix: String,
}

impl InMemoryTracer {
    fn new(id_prefix: &str) -> Self {
        InMemoryTracer {
            spans: Arc::new(RwLock::new(HashMap::new())),
            id_prefix: id_prefix.to_string(),
        }
    }
}

impl Tracer for InMemoryTracer {
    fn name(&self) -> &str {
        "内存追踪器"
    }
    
    fn start_span(&self, trace_id: &str, parent_span_id: Option<&str>, operation_name: &str) -> Result<String, TracingError> {
        let span_id = format!("{}-{}", self.id_prefix, DistributedTracingSystem::generate_span_id());
        
        let mut spans = self.spans.write().unwrap();
        
        spans.insert(span_id.clone(), SpanData {
            trace_id: trace_id.to_string(),
            span_id: span_id.clone(),
            parent_span_id: parent_span_id.map(|id| id.to_string()),
            operation_name: operation_name.to_string(),
            start_time: Instant::now(),
            end_time: None,
            status: SpanStatus::Unset,
            attributes: HashMap::new(),
            events: Vec::new(),
        });
        
        Ok(span_id)
    }
    
    fn end_span(&self, span_id: &str) -> Result<(), TracingError> {
        let mut spans = self.spans.write().unwrap();
        
        if let Some(span) = spans.get_mut(span_id) {
            span.end_time = Some(Instant::now());
            Ok(())
        } else {
            Err(TracingError {
                message: format!("Span ID '{}' 不存在", span_id),
                error_type: TracingErrorType::SpanNotFound,
            })
        }
    }
    
    fn add_event(&self, span_id: &str, event_name: &str, attributes: HashMap<String, String>) -> Result<(), TracingError> {
        let mut spans = self.spans.write().unwrap();
        
        if let Some(span) = spans.get_mut(span_id) {
            span.events.push(SpanEvent {
                name: event_name.to_string(),
                timestamp: Instant::now(),
                attributes,
            });
            Ok(())
        } else {
            Err(TracingError {
                message: format!("Span ID '{}' 不存在", span_id),
                error_type: TracingErrorType::SpanNotFound,
            })
        }
    }
    
    fn set_attribute(&self, span_id: &str, key: &str, value: &str) -> Result<(), TracingError> {
        let mut spans = self.spans.write().unwrap();
        
        if let Some(span) = spans.get_mut(span_id) {
            span.attributes.insert(key.to_string(), value.to_string());
            Ok(())
        } else {
            Err(TracingError {
                message: format!("Span ID '{}' 不存在", span_id),
                error_type: TracingErrorType::SpanNotFound,
            })
        }
    }
    
    fn set_status(&self, span_id: &str, status: SpanStatus) -> Result<(), TracingError> {
        let mut spans = self.spans.write().unwrap();
        
        if let Some(span) = spans.get_mut(span_id) {
            span.status = status;
            Ok(())
        } else {
            Err(TracingError {
                message: format!("Span ID '{}' 不存在", span_id),
                error_type: TracingErrorType::SpanNotFound,
            })
        }
    }
    
    fn get_context(&self, span_id: &str) -> Result<TraceContext, TracingError> {
        let spans = self.spans.read().unwrap();
        
        if let Some(span) = spans.get(span_id) {
            Ok(TraceContext {
                trace_id: span.trace_id.clone(),
                span_id: span.span_id.clone(),
                parent_span_id: span.parent_span_id.clone(),
                attributes: span.attributes.clone(),
                baggage: HashMap::new(), // baggage通常存储在TraceContext中，而不是Span中
            })
        } else {
            Err(TracingError {
                message: format!("Span ID '{}' 不存在", span_id),
                error_type: TracingErrorType::SpanNotFound,
            })
        }
    }
}

// 控制台导出器
struct ConsoleExporter;

impl ConsoleExporter {
    fn new() -> Self {
        ConsoleExporter
    }
}

impl TraceExporter for ConsoleExporter {
    fn name(&self) -> &str {
        "控制台导出器"
    }
    
    fn export(&self, spans: Vec<SpanData>) -> Result<(), ExportError> {
        for span in spans {
            println!("导出追踪: {} - {}", span.trace_id, span.operation_name);
            println!("  Span ID: {}", span.span_id);
            
            if let Some(parent_id) = &span.parent_span_id {
                println!("  父Span ID: {}", parent_id);
            }
            
            let duration = if let Some(end_time) = span.end_time {
                end_time.duration_since(span.start_time).as_millis()
            } else {
                0
            };
            
            println!("  持续时间: {}ms", duration);
            println!("  状态: {:?}", span.status);
            
            println!("  属性:");
            for (key, value) in &span.attributes {
                println!("    {}: {}", key, value);
            }
            
            println!("  事件:");
            for event in &span.events {
                println!("    {} @ {:?}", event.name, event.timestamp);
                for (key, value) in &event.attributes {
                    println!("      {}: {}", key, value);
                }
            }
            
            println!("");
        }
        
        Ok(())
    }
    
    fn shutdown(&self) -> Result<(), ExportError> {
        // 无需特殊清理
        Ok(())
    }
}

// HTTP JSON导出器
struct HttpJsonExporter {
    endpoint: String,
    client: reqwest::Client,
    batch_size: usize,
    headers: HashMap<String, String>,
}

impl HttpJsonExporter {
    fn new(endpoint: &str, batch_size: usize) -> Self {
        let mut headers = HashMap::new();
        headers.insert("Content-Type".to_string(), "application/json".to_string());
        
        HttpJsonExporter {
            endpoint: endpoint.to_string(),
            client: reqwest::Client::new(),
            batch_size,
            headers,
        }
    }
    
    fn add_header(&mut self, key: &str, value: &str) {
        self.headers.insert(key.to_string(), value.to_string());
    }
    
    fn span_to_json(&self, span: &SpanData) -> serde_json::Value {
        json!({
            "traceId": span.trace_id,
            "spanId": span.span_id,
            "parentSpanId": span.parent_span_id,
            "name": span.operation_name,
            "startTime": format!("{:?}", span.start_time),
            "endTime": span.end_time.map(|t| format!("{:?}", t)),
            "status": match span.status {
                SpanStatus::Ok => "ok",
                SpanStatus::Error(ref msg) => msg,
                SpanStatus::Unset => "unset",
            },
            "attributes": span.attributes,
            "events": span.events.iter().map(|e| {
                json!({
                    "name": e.name,
                    "time": format!("{:?}", e.timestamp),
                    "attributes": e.attributes,
                })
            }).collect::<Vec<_>>(),
        })
    }
}

impl TraceExporter for HttpJsonExporter {
    fn name(&self) -> &str {
        "HTTP JSON导出器"
    }
    
    fn export(&self, spans: Vec<SpanData>) -> Result<(), ExportError> {
        if spans.is_empty() {
            return Ok(());
        }
        
        // 将span转换为JSON
        let json_spans: Vec<serde_json::Value> = spans.iter()
            .map(|span| self.span_to_json(span))
            .collect();
        
        // 分批导出
        for chunk in json_spans.chunks(self.batch_size) {
            let json_body = json!({
                "spans": chunk
            });
            
            // 在实际实现中，这应该是一个异步发送
            // 简化实现：同步发送
            match self.client.post(&self.endpoint)
                .json(&json_body)
                .send() {
                Ok(response) => {
                    if !response.status().is_success() {
                        return Err(ExportError {
                            message: format!("导出失败: HTTP状态码 {}", response.status()),
                            error_type: ExportErrorType::ConnectionFailed,
                        });
                    }
                },
                Err(err) => {
                    return Err(ExportError {
                        message: format!("导出失败: {}", err),
                        error_type: ExportErrorType::ConnectionFailed,
                    });
                }
            }
        }
        
        Ok(())
    }
    
    fn shutdown(&self) -> Result<(), ExportError> {
        // 简化实现：仅返回成功
        Ok(())
    }
}

// OpenTelemetry兼容性
struct OpenTelemetryBridge {
    tracing_system: Arc<Mutex<DistributedTracingSystem>>,
    resource: HashMap<String, String>,
}

impl OpenTelemetryBridge {
    fn new(tracing_system: Arc<Mutex<DistributedTracingSystem>>) -> Self {
        let mut resource = HashMap::new();
        resource.insert("service.name".to_string(), "unknown_service".to_string());
        resource.insert("service.version".to_string(), "0.1.0".to_string());
        
        OpenTelemetryBridge {
            tracing_system,
            resource,
        }
    }
    
    fn set_resource(&mut self, key: &str, value: &str) {
        self.resource.insert(key.to_string(), value.to_string());
    }
    
    fn convert_span_data(&self, span: &SpanData) -> serde_json::Value {
        // 转换为OpenTelemetry格式
        json!({
            "name": span.operation_name,
            "context": {
                "trace_id": span.trace_id,
                "span_id": span.span_id,
                "trace_state": ""
            },
            "parent_span_id": span.parent_span_id,
            "start_time": format!("{:?}", span.start_time),
            "end_time": span.end_time.map(|t| format!("{:?}", t)),
            "status": {
                "code": match span.status {
                    SpanStatus::Ok => "OK",
                    SpanStatus::Error(_) => "ERROR",
                    SpanStatus::Unset => "UNSET"
                },
                "message": match span.status {
                    SpanStatus::Error(ref msg) => msg,
                    _ => ""
                }
            },
            "attributes": span.attributes,
            "events": span.events.iter().map(|e| {
                json!({
                    "name": e.name,
                    "timestamp": format!("{:?}", e.timestamp),
                    "attributes": e.attributes
                })
            }).collect::<Vec<_>>(),
            "links": [],
            "resource": self.resource
        })
    }
}
```

### 4.5 Gossip协议和失败检测

Gossip协议是一种去中心化的通信方式，用于在分布式系统中传播信息和检测节点故障。

```rust
struct GossipProtocol {
    node_id: String,
    members: Arc<RwLock<HashMap<String, MemberInfo>>>,
    message_queue: Arc<Mutex<VecDeque<GossipMessage>>>,
    failure_detector: Box<dyn FailureDetector>,
    dissemination_factor: usize,
    gossip_interval: Duration,
    running: Arc<AtomicBool>,
}

trait FailureDetector: Send + Sync {
    fn name(&self) -> &str;
    fn record_heartbeat(&mut self, node_id: &str, timestamp: Instant);
    fn suspect_failure(&self, node_id: &str) -> bool;
    fn confirm_failure(&self, node_id: &str) -> bool;
    fn get_suspect_timeout(&self) -> Duration;
    fn get_failure_timeout(&self) -> Duration;
}

struct MemberInfo {
    node_id: String,
    address: String,
    heartbeat: u64,
    incarnation: u64,
    status: MemberStatus,
    last_updated: Instant,
    metadata: HashMap<String, String>,
}

enum MemberStatus {
    Alive,
    Suspect,
    Failed,
    Left,
}

struct GossipMessage {
    sender_id: String,
    message_type: GossipMessageType,
    sequence: u64,
    payload: Vec<u8>,
}

enum GossipMessageType {
    Heartbeat,
    MembershipUpdate,
    DirectMessage,
    Broadcast,
}

struct PhiAccrualFailureDetector {
    phi_threshold: f64,
    window_size: usize,
    min_std_dev: f64,
    heartbeat_history: HashMap<String, VecDeque<Duration>>,
    last_heartbeat: HashMap<String, Instant>,
    suspect_timeout: Duration,
    failure_timeout: Duration,
}

impl PhiAccrualFailureDetector {
    fn new(phi_threshold: f64, window_size: usize, min_std_dev: f64) -> Self {
        PhiAccrualFailureDetector {
            phi_threshold,
            window_size,
            min_std_dev,
            heartbeat_history: HashMap::new(),
            last_heartbeat: HashMap::new(),
            suspect_timeout: Duration::from_secs(5),
            failure_timeout: Duration::from_secs(15),
        }
    }
    
    fn calculate_phi(&self, node_id: &str) -> f64 {
        if let Some(history) = self.heartbeat_history.get(node_id) {
            if history.len() < 2 {
                return 0.0; // 历史记录太少，无法计算
            }
            
            let now = Instant::now();
            let last = self.last_heartbeat.get(node_id).cloned().unwrap_or(now);
            let elapsed = now.duration_since(last);
            
            // 计算平均间隔
            let total: Duration = history.iter().sum();
            let mean = total / history.len() as u32;
            
            // 计算标准差
            let variance: f64 = history.iter()
                .map(|interval| {
                    let diff = interval.as_secs_f64() - mean.as_secs_f64();
                    diff * diff
                })
                .sum::<f64>() / history.len() as f64;
            
            let std_dev = variance.sqrt().max(self.min_std_dev);
            
            // 计算phi值 (基于正态分布的CDF)
            let x = elapsed.as_secs_f64() - mean.as_secs_f64();
            
            if x <= 0.0 {
                return 0.0;
            }
            
            let y = x / (std_dev * std::f64::consts::SQRT_2);
            let phi = -y.error_function_complement().ln();
            
            phi
        } else {
            0.0
        }
    }
}

impl FailureDetector for PhiAccrualFailureDetector {
    fn name(&self) -> &str {
        "Phi失效检测器"
    }
    
    fn record_heartbeat(&mut self, node_id: &str, timestamp: Instant) {
        let now = Instant::now();
        
        // 计算心跳间隔
        if let Some(last) = self.last_heartbeat.get(node_id) {
            let interval = now.duration_since(*last);
            
            // 更新心跳历史
            let history = self.heartbeat_history
                .entry(node_id.to_string())
                .or_insert_with(|| VecDeque::with_capacity(self.window_size));
            
            history.push_back(interval);
            
            // 保持历史窗口大小
            if history.len() > self.window_size {
                history.pop_front();
            }
        }
        
        // 更新上次心跳时间
        self.last_heartbeat.insert(node_id.to_string(), timestamp);
    }
    
    fn suspect_failure(&self, node_id: &str) -> bool {
        // 如果phi值超过阈值，则怀疑节点故障
        let phi = self.calculate_phi(node_id);
        phi > self.phi_threshold
    }
    
    fn confirm_failure(&self, node_id: &str) -> bool {
        // 检查上一次心跳是否超过失败超时
        if let Some(last) = self.last_heartbeat.get(node_id) {
            let elapsed = Instant::now().duration_since(*last);
            elapsed > self.failure_timeout
        } else {
            false
        }
    }
    
    fn get_suspect_timeout(&self) -> Duration {
        self.suspect_timeout
    }
    
    fn get_failure_timeout(&self) -> Duration {
        self.failure_timeout
    }
}

impl GossipProtocol {
    fn new(node_id: &str, address: &str, failure_detector: Box<dyn FailureDetector>) -> Self {
        let mut members = HashMap::new();
        
        // 添加自己作为成员
        members.insert(node_id.to_string(), MemberInfo {
            node_id: node_id.to_string(),
            address: address.to_string(),
            heartbeat: 0,
            incarnation: 0,
            status: MemberStatus::Alive,
            last_updated: Instant::now(),
            metadata: HashMap::new(),
        });
        
        GossipProtocol {
            node_id: node_id.to_string(),
            members: Arc::new(RwLock::new(members)),
            message_queue: Arc::new(Mutex::new(VecDeque::new())),
            failure_detector,
            dissemination_factor: 3, // 每次与几个随机节点通信
            gossip_interval: Duration::from_millis(1000),
            running: Arc::new(AtomicBool::new(false)),
        }
    }
    
    fn start(&mut self) -> Result<(), String> {
        if self.running.load(Ordering::SeqCst) {
            return Err("Gossip协议已经在运行".to_string());
        }
        
        self.running.store(true, Ordering::SeqCst);
        
        // 启动gossip线程
        let members = self.members.clone();
        let message_queue = self.message_queue.clone();
        let node_id = self.node_id.clone();
        let dissemination_factor = self.dissemination_factor;
        let gossip_interval = self.gossip_interval;
        let running = self.running.clone();
        
        std::thread::spawn(move || {
            while running.load(Ordering::SeqCst) {
                // 增加自己的心跳计数
                {
                    let mut members_lock = members.write().unwrap();
                    if let Some(self_info) = members_lock.get_mut(&node_id) {
                        self_info.heartbeat += 1;
                        self_info.last_updated = Instant::now();
                    }
                }
                
                // 选择随机目标节点进行gossip
                let targets = GossipProtocol::select_random_members(&members, &node_id, dissemination_factor);
                
                for target in targets {
                    // 准备gossip消息
                    let gossip_data = GossipProtocol::prepare_gossip_message(&members, &node_id);
                    
                    // 在实际实现中，这里会通过网络发送gossip消息
                    println!("向节点 {} 发送gossip消息", target);
                    
                    // 处理消息队列中的消息
                    let mut queue = message_queue.lock().unwrap();
                    while let Some(message) = queue.pop_front() {
                        // 处理接收到的消息
                        // 在实际实现中，这将涉及更新成员状态和转发消息
                        println!("处理来自 {} 的消息", message.sender_id);
                    }
                }
                
                // 等待下一个gossip间隔
                std::thread::sleep(gossip_interval);
            }
        });
        
        Ok(())
    }
    
    fn stop(&mut self) {
        self.running.store(false, Ordering::SeqCst);
    }
    
    fn join(&mut self, seed_node: &str, seed_address: &str) -> Result<(), String> {
        if seed_node == self.node_id {
            return Err("不能使用自己作为种子节点".to_string());
        }
        
        // 添加种子节点作为成员
        let mut members = self.members.write().unwrap();
        members.insert(seed_node.to_string(), MemberInfo {
            node_id: seed_node.to_string(),
            address: seed_address.to_string(),
            heartbeat: 0,
            incarnation: 0,
            status: MemberStatus::Alive,
            last_updated: Instant::now(),
            metadata: HashMap::new(),
        });
        
        // 准备加入消息
        let self_info = members.get(&self.node_id).unwrap().clone();
        
        // 在实际实现中，这里会通过网络发送加入请求到种子节点
        println!("向种子节点 {} 发送加入请求", seed_node);
        
        Ok(())
    }
    
    fn leave(&mut self) -> Result<(), String> {
        // 更新自己的状态为已离开
        let mut members = self.members.write().unwrap();
        if let Some(self_info) = members.get_mut(&self.node_id) {
            self_info.status = MemberStatus::Left;
            self_info.incarnation += 1;
            self_info.last_updated = Instant::now();
        }
        
        // 广播离开消息
        // 在实际实现中，这会向其他节点广播离开消息
        println!("广播离开消息");
        
        // 停止gossip线程
        self.stop();
        
        Ok(())
    }
    
    fn handle_message(&mut self, message: GossipMessage) -> Result<(), String> {
        // 将消息添加到队列
        let mut queue = self.message_queue.lock().unwrap();
        queue.push_back(message);
        
        Ok(())
    }
    
    fn select_random_members(members: &Arc<RwLock<HashMap<String, MemberInfo>>>, exclude_id: &str, count: usize) -> Vec<String> {
        let members_lock = members.read().unwrap();
        
        // 过滤出活跃成员，排除自己
        let active_members: Vec<String> = members_lock.iter()
            .filter(|(id, info)| *id != exclude_id && matches!(info.status, MemberStatus::Alive))
            .map(|(id, _)| id.clone())
            .collect();
        
        if active_members.is_empty() {
            return Vec::new();
        }
        
        // 选择随机成员
        let mut rng = rand::thread_rng();
        let mut selected = Vec::new();
        
        // 如果活跃成员数量小于要选择的数量，返回所有活跃成员
        if active_members.len() <= count {
            return active_members;
        }
        
        // 随机选择不重复的成员
        let mut available = active_members.clone();
        for _ in 0..count {
            if available.is_empty() {
                break;
            }
            
            let index = rng.gen_range(0..available.len());
            let member = available.remove(index);
            selected.push(member);
        }
        
        selected
    }
    
    fn prepare_gossip_message(members: &Arc<RwLock<HashMap<String, MemberInfo>>>, sender_id: &str) -> Vec<u8> {
        let members_lock = members.read().unwrap();
        
        // 在实际实现中，这会序列化所有成员状态
        // 简化实现：返回空向量
        Vec::new()
    }
    
    fn merge_gossip_state(&mut self, sender_id: &str, gossip_data: &[u8]) -> Result<(), String> {
        // 在实际实现中，这会解析gossip数据并合并成员状态
        println!("合并来自 {} 的gossip状态", sender_id);
        
        Ok(())
    }
    
    fn check_failures(&mut self) {
        let mut members = self.members.write().unwrap();
        let now = Instant::now();
        
        // 检查所有成员的失败状态
        for (_, member) in members.iter_mut() {
            if member.node_id == self.node_id {
                continue; // 跳过自己
            }
            
            match member.status {
                MemberStatus::Alive => {
                    // 检查是否应该怀疑
                    if self.failure_detector.suspect_failure(&member.node_id) {
                        member.status = MemberStatus::Suspect;
                        member.last_updated = now;
                        println!("怀疑节点 {} 可能故障", member.node_id);
                    }
                },
                MemberStatus::Suspect => {
                    // 检查是否应该确认失败
                    if self.failure_detector.confirm_failure(&member.node_id) {
                        member.status = MemberStatus::Failed;
                        member.last_updated = now;
                        println!("确认节点 {} 已故障", member.node_id);
                    }
                },
                _ => {} // 对于其他状态不做处理
            }
        }
    }
    
    fn get_members(&self) -> HashMap<String, MemberInfo> {
        let members = self.members.read().unwrap();
        members.clone()
    }
    
    fn get_alive_members(&self) -> HashMap<String, MemberInfo> {
        let members = self.members.read().unwrap();
        members.iter()
            .filter(|(_, info)| matches!(info.status, MemberStatus::Alive))
            .map(|(id, info)| (id.clone(), info.clone()))
            .collect()
    }
    
    fn set_metadata(&mut self, key: &str, value: &str) -> Result<(), String> {
        let mut members = self.members.write().unwrap();
        
        if let Some(self_info) = members.get_mut(&self.node_id) {
            self_info.metadata.insert(key.to_string(), value.to_string());
            self_info.incarnation += 1;
            self_info.last_updated = Instant::now();
            Ok(())
        } else {
            Err("找不到自己的成员信息".to_string())
        }
    }
    
    fn get_metadata(&self, node_id: &str, key: &str) -> Option<String> {
        let members = self.members.read().unwrap();
        
        members.get(node_id)
            .and_then(|info| info.metadata.get(key).cloned())
    }
}
```

### 4.6 服务发现与负载均衡

服务发现允许客户端找到可用的服务实例，而负载均衡确保请求分布在多个服务实例上。

```rust
struct ServiceDiscovery {
    services: Arc<RwLock<HashMap<String, Vec<ServiceInstance>>>>,
    resolvers: Vec<Box<dyn ServiceResolver>>,
    load_balancers: HashMap<String, Box<dyn LoadBalancer>>,
    health_checker: Box<dyn HealthChecker>,
    update_interval: Duration,
    running: Arc<AtomicBool>,
}

trait ServiceResolver: Send + Sync {
    fn name(&self) -> &str;
    fn resolve(&self, service_name: &str) -> Result<Vec<ServiceInstance>, ResolveError>;
}

trait LoadBalancer: Send + Sync {
    fn name(&self) -> &str;
    fn select(&self, service_name: &str, instances: &[ServiceInstance]) -> Option<ServiceInstance>;
    fn report_success(&mut self, service_name: &str, instance: &ServiceInstance);
    fn report_failure(&mut self, service_name: &str, instance: &ServiceInstance);
}

trait HealthChecker: Send + Sync {
    fn name(&self) -> &str;
    fn check(&self, instance: &ServiceInstance) -> HealthStatus;
    fn get_check_interval(&self) -> Duration;
}

struct ServiceInstance {
    id: String,
    service_name: String,
    host: String,
    port: u16,
    metadata: HashMap<String, String>,
    health_status: HealthStatus,
    last_checked: Instant,
    weight: u32,
}

enum HealthStatus {
    Healthy,
    Unhealthy,
    Unknown,
}

struct ResolveError {
    message: String,
    error_type: ResolveErrorType,
}

enum ResolveErrorType {
    ServiceNotFound,
    ConnectionFailed,
    Timeout,
    InternalError,
}

impl ServiceDiscovery {
    fn new(health_checker: Box<dyn HealthChecker>, update_interval: Duration) -> Self {
        ServiceDiscovery {
            services: Arc::new(RwLock::new(HashMap::new())),
            resolvers: Vec::new(),
            load_balancers: HashMap::new(),
            health_checker,
            update_interval,
            running: Arc::new(AtomicBool::new(false)),
        }
    }
    
    fn add_resolver(&mut self, resolver: Box<dyn ServiceResolver>) {
        self.resolvers.push(resolver);
    }
    
    fn add_load_balancer(&mut self, service_name: &str, load_balancer: Box<dyn LoadBalancer>) {
        self.load_balancers.insert(service_name.to_string(), load_balancer);
    }
    
    fn start(&mut self) -> Result<(), String> {
        if self.running.load(Ordering::SeqCst) {
            return Err("服务发现已经在运行".to_string());
        }
        
        self.running.store(true, Ordering::SeqCst);
        
        // 启动更新线程
        let services = self.services.clone();
        let resolvers_count = self.resolvers.len();
        let update_interval = self.update_interval;
        let running = self.running.clone();
        let health_check_interval = self.health_checker.get_check_interval();
        
        std::thread::spawn(move || {
            while running.load(Ordering::SeqCst) {
                // 这里应该定期从所有解析器更新服务列表
                println!("从 {} 个解析器更新服务列表", resolvers_count);
                
                // 然后检查所有服务实例的健康状态
                {
                    let mut services_lock = services.write().unwrap();
                    for (_, instances) in services_lock.iter_mut() {
                        for instance in instances.iter_mut() {
                            if instance.last_checked.elapsed() >= health_check_interval {
                                // 应该调用健康检查器检查实例状态
                                println!("检查服务 {} 实例 {} 的健康状态", 
                                         instance.service_name, instance.id);
                                instance.last_checked = Instant::now();
                            }
                        }
                    }
                }
                
                // 等待下一个更新间隔
                std::thread::sleep(update_interval);
            }
        });
        
        Ok(())
    }
    
    fn stop(&mut self) {
        self.running.store(false, Ordering::SeqCst);
    }
    
    fn register_service(&mut self, instance: ServiceInstance) -> Result<(), String> {
        let mut services = self.services.write().unwrap();
        
        let instances = services
            .entry(instance.service_name.clone())
            .or_insert_with(Vec::new);
        
        // 检查实例是否已经存在
        if instances.iter().any(|i| i.id == instance.id) {
            return Err(format!("服务实例 {} 已经注册", instance.id));
        }
        
        instances.push(instance);
        
        Ok(())
    }
    
    fn deregister_service(&mut self, service_name: &str, instance_id: &str) -> Result<(), String> {
        let mut services = self.services.write().unwrap();
        
        if let Some(instances) = services.get_mut(service_name) {
            let prev_len = instances.len();
            instances.retain(|i| i.id != instance_id);
            
            if instances.len() < prev_len {
                Ok(())
            } else {
                Err(format!("找不到服务实例 {}", instance_id))
            }
        } else {
            Err(format!("找不到服务 {}", service_name))
        }
    }
    
    fn get_instances(&self, service_name: &str) -> Result<Vec<ServiceInstance>, ResolveError> {
        // 首先从本地缓存中查找
        let services = self.services.read().unwrap();
        
        if let Some(instances) = services.get(service_name) {
            if !instances.is_empty() {
                // 返回健康的实例
                let healthy_instances: Vec<ServiceInstance> = instances.iter()
                    .filter(|i| matches!(i.health_status, HealthStatus::Healthy))
                    .cloned()
                    .collect();
                
                if !healthy_instances.is_empty() {
                    return Ok(healthy_instances);
                }
            }
        }
        
        // 如果本地没有或者没有健康的实例，尝试从解析器获取
        drop(services);
        
        for resolver in &self.resolvers {
            match resolver.resolve(service_name) {
                Ok(instances) => {
                    // 更新本地缓存
                    let mut services = self.services.write().unwrap();
                    services.insert(service_name.to_string(), instances.clone());
                    
                    return Ok(instances);
                },
                Err(_) => continue, // 尝试下一个解析器
            }
        }
        
        Err(ResolveError {
            message: format!("找不到服务 {}", service_name),
            error_type: ResolveErrorType::ServiceNotFound,
        })
    }
    
    fn select_instance(&mut self, service_name: &str) -> Result<ServiceInstance, ResolveError> {
        // 获取服务实例
        let instances = self.get_instances(service_name)?;
        
        // 使用负载均衡器选择一个实例
        if let Some(load_balancer) = self.load_balancers.get(service_name) {
            if let Some(instance) = load_balancer.select(service_name, &instances) {
                return Ok(instance);
            }
        }
        
        // 如果没有特定的负载均衡器或负载均衡器没有选择实例，使用默认策略
        if !instances.is_empty() {
            let mut rng = rand::thread_rng();
            let index = rng.gen_range(0..instances.len());
            return Ok(instances[index].clone());
        }
        
        Err(ResolveError {
            message: format!("没有可用的服务实例 {}", service_name),
            error_type: ResolveErrorType::ServiceNotFound,})
    }
    
    fn report_result(&mut self, service_name: &str, instance: &ServiceInstance, success: bool) {
        // 向负载均衡器报告调用结果
        if let Some(load_balancer) = self.load_balancers.get_mut(service_name) {
            if success {
                load_balancer.report_success(service_name, instance);
            } else {
                load_balancer.report_failure(service_name, instance);
            }
        }
    }
    
    fn watch_service(&self, service_name: &str, callback: Box<dyn Fn(&[ServiceInstance]) + Send + Sync + 'static>) -> Result<String, String> {
        // 注册一个监视器，当服务实例变化时调用回调函数
        // 简化实现：返回一个虚拟的监视器ID
        Ok(uuid::Uuid::new_v4().to_string())
    }
    
    fn unwatch_service(&self, watch_id: &str) -> Result<(), String> {
        // 取消服务监视
        // 简化实现：假装取消成功
        Ok(())
    }
}

// 随机负载均衡器
struct RandomLoadBalancer;

impl RandomLoadBalancer {
    fn new() -> Self {
        RandomLoadBalancer
    }
}

impl LoadBalancer for RandomLoadBalancer {
    fn name(&self) -> &str {
        "随机负载均衡器"
    }
    
    fn select(&self, _service_name: &str, instances: &[ServiceInstance]) -> Option<ServiceInstance> {
        if instances.is_empty() {
            return None;
        }
        
        let mut rng = rand::thread_rng();
        let index = rng.gen_range(0..instances.len());
        Some(instances[index].clone())
    }
    
    fn report_success(&mut self, _service_name: &str, _instance: &ServiceInstance) {
        // 随机负载均衡器不需要跟踪成功或失败
    }
    
    fn report_failure(&mut self, _service_name: &str, _instance: &ServiceInstance) {
        // 随机负载均衡器不需要跟踪成功或失败
    }
}

// 轮询负载均衡器
struct RoundRobinLoadBalancer {
    counters: HashMap<String, usize>,
}

impl RoundRobinLoadBalancer {
    fn new() -> Self {
        RoundRobinLoadBalancer {
            counters: HashMap::new(),
        }
    }
}

impl LoadBalancer for RoundRobinLoadBalancer {
    fn name(&self) -> &str {
        "轮询负载均衡器"
    }
    
    fn select(&self, service_name: &str, instances: &[ServiceInstance]) -> Option<ServiceInstance> {
        if instances.is_empty() {
            return None;
        }
        
        let mut counters = self.counters.clone();
        let current = *counters.get(service_name).unwrap_or(&0);
        let next = (current + 1) % instances.len();
        counters.insert(service_name.to_string(), next);
        
        Some(instances[current].clone())
    }
    
    fn report_success(&mut self, _service_name: &str, _instance: &ServiceInstance) {
        // 轮询负载均衡器不需要跟踪成功或失败
    }
    
    fn report_failure(&mut self, _service_name: &str, _instance: &ServiceInstance) {
        // 轮询负载均衡器不需要跟踪成功或失败
    }
}

// 加权负载均衡器
struct WeightedLoadBalancer {
    current_weights: HashMap<String, HashMap<String, i32>>,
}

impl WeightedLoadBalancer {
    fn new() -> Self {
        WeightedLoadBalancer {
            current_weights: HashMap::new(),
        }
    }
}

impl LoadBalancer for WeightedLoadBalancer {
    fn name(&self) -> &str {
        "加权负载均衡器"
    }
    
    fn select(&self, service_name: &str, instances: &[ServiceInstance]) -> Option<ServiceInstance> {
        if instances.is_empty() {
            return None;
        }
        
        let mut current_weights = self.current_weights.clone();
        let weights = current_weights.entry(service_name.to_string()).or_insert_with(HashMap::new);
        
        let mut total_weight = 0;
        let mut best_instance = None;
        let mut best_weight = -1;
        
        for instance in instances {
            // 初始化实例权重
            let weight = instance.weight as i32;
            total_weight += weight;
            
            // 增加当前权重
            let current = weights.entry(instance.id.clone()).or_insert(0);
            *current += weight;
            
            // 选择最大的当前权重
            if *current > best_weight {
                best_weight = *current;
                best_instance = Some(instance.clone());
            }
        }
        
        // 更新选择的实例的权重
        if let Some(ref instance) = best_instance {
            let current = weights.get_mut(&instance.id).unwrap();
            *current -= total_weight;
        }
        
        best_instance
    }
    
    fn report_success(&mut self, _service_name: &str, _instance: &ServiceInstance) {
        // 加权负载均衡器不需要跟踪成功或失败
    }
    
    fn report_failure(&mut self, _service_name: &str, _instance: &ServiceInstance) {
        // 加权负载均衡器不需要跟踪成功或失败
    }
}

// 最少连接数负载均衡器
struct LeastConnectionsLoadBalancer {
    connection_counts: HashMap<String, HashMap<String, usize>>,
}

impl LeastConnectionsLoadBalancer {
    fn new() -> Self {
        LeastConnectionsLoadBalancer {
            connection_counts: HashMap::new(),
        }
    }
}

impl LoadBalancer for LeastConnectionsLoadBalancer {
    fn name(&self) -> &str {
        "最少连接数负载均衡器"
    }
    
    fn select(&self, service_name: &str, instances: &[ServiceInstance]) -> Option<ServiceInstance> {
        if instances.is_empty() {
            return None;
        }
        
        let counts = self.connection_counts.get(service_name).unwrap_or(&HashMap::new());
        
        // 寻找连接数最少的实例
        let mut least_instance = &instances[0];
        let mut least_count = counts.get(&least_instance.id).unwrap_or(&0);
        
        for instance in instances.iter().skip(1) {
            let count = counts.get(&instance.id).unwrap_or(&0);
            if count < least_count {
                least_instance = instance;
                least_count = count;
            }
        }
        
        Some(least_instance.clone())
    }
    
    fn report_success(&mut self, service_name: &str, instance: &ServiceInstance) {
        // 连接开始，增加计数
        let counts = self.connection_counts.entry(service_name.to_string())
            .or_insert_with(HashMap::new);
        
        let count = counts.entry(instance.id.clone()).or_insert(0);
        *count += 1;
    }
    
    fn report_failure(&mut self, service_name: &str, instance: &ServiceInstance) {
        // 连接结束，减少计数
        if let Some(counts) = self.connection_counts.get_mut(service_name) {
            if let Some(count) = counts.get_mut(&instance.id) {
                if *count > 0 {
                    *count -= 1;
                }
            }
        }
    }
}

// 响应时间负载均衡器
struct ResponseTimeLoadBalancer {
    response_times: HashMap<String, HashMap<String, Duration>>,
    decay_factor: f64,
}

impl ResponseTimeLoadBalancer {
    fn new(decay_factor: f64) -> Self {
        ResponseTimeLoadBalancer {
            response_times: HashMap::new(),
            decay_factor,
        }
    }
    
    fn update_response_time(&mut self, service_name: &str, instance_id: &str, new_time: Duration) {
        let times = self.response_times.entry(service_name.to_string())
            .or_insert_with(HashMap::new);
        
        let current = times.entry(instance_id.to_string()).or_insert(new_time);
        
        // 使用指数移动平均更新响应时间
        let current_ms = current.as_millis() as f64;
        let new_ms = new_time.as_millis() as f64;
        let updated_ms = current_ms * self.decay_factor + new_ms * (1.0 - self.decay_factor);
        *current = Duration::from_millis(updated_ms as u64);
    }
}

impl LoadBalancer for ResponseTimeLoadBalancer {
    fn name(&self) -> &str {
        "响应时间负载均衡器"
    }
    
    fn select(&self, service_name: &str, instances: &[ServiceInstance]) -> Option<ServiceInstance> {
        if instances.is_empty() {
            return None;
        }
        
        let times = self.response_times.get(service_name).unwrap_or(&HashMap::new());
        
        // 寻找响应时间最短的实例
        let mut best_instance = &instances[0];
        let mut best_time = times.get(&best_instance.id)
            .unwrap_or(&Duration::from_secs(60)); // 默认假设60秒
        
        for instance in instances.iter().skip(1) {
            let time = times.get(&instance.id)
                .unwrap_or(&Duration::from_secs(60));
            
            if time < best_time {
                best_instance = instance;
                best_time = time;
            }
        }
        
        Some(best_instance.clone())
    }
    
    fn report_success(&mut self, service_name: &str, instance: &ServiceInstance) {
        // 在实际实现中，这应该使用测量的响应时间而不是固定值
        let response_time = Duration::from_millis(100); // 示例值
        self.update_response_time(service_name, &instance.id, response_time);
    }
    
    fn report_failure(&mut self, service_name: &str, instance: &ServiceInstance) {
        // 失败会增加响应时间惩罚
        let penalty = Duration::from_secs(1);
        self.update_response_time(service_name, &instance.id, penalty);
    }
}

// DNS服务解析器
struct DnsServiceResolver {
    dns_suffix: String,
    dns_cache: HashMap<String, (Vec<ServiceInstance>, Instant)>,
    ttl: Duration,
}

impl DnsServiceResolver {
    fn new(dns_suffix: &str, ttl: Duration) -> Self {
        DnsServiceResolver {
            dns_suffix: dns_suffix.to_string(),
            dns_cache: HashMap::new(),
            ttl,
        }
    }
}

impl ServiceResolver for DnsServiceResolver {
    fn name(&self) -> &str {
        "DNS服务解析器"
    }
    
    fn resolve(&self, service_name: &str) -> Result<Vec<ServiceInstance>, ResolveError> {
        // 检查缓存
        if let Some((instances, timestamp)) = self.dns_cache.get(service_name) {
            if timestamp.elapsed() < self.ttl {
                return Ok(instances.clone());
            }
        }
        
        // 构建DNS查询名称
        let dns_name = format!("{}.{}", service_name, self.dns_suffix);
        
        // 在实际实现中，这会执行真正的DNS查询
        println!("执行DNS查询: {}", dns_name);
        
        // 模拟查询结果
        let mut instances = Vec::new();
        let mut rng = rand::thread_rng();
        
        for i in 1..=3 {
            let port = 8000 + rng.gen_range(0..1000);
            instances.push(ServiceInstance {
                id: format!("{}-{}", service_name, i),
                service_name: service_name.to_string(),
                host: format!("host-{}.{}", i, self.dns_suffix),
                port: port as u16,
                metadata: HashMap::new(),
                health_status: HealthStatus::Healthy,
                last_checked: Instant::now(),
                weight: 100,
            });
        }
        
        // 更新缓存
        self.dns_cache.insert(service_name.to_string(), (instances.clone(), Instant::now()));
        
        Ok(instances)
    }
}

// 文件系统服务解析器
struct FileSystemServiceResolver {
    config_path: String,
    last_modified: HashMap<String, SystemTime>,
}

impl FileSystemServiceResolver {
    fn new(config_path: &str) -> Self {
        FileSystemServiceResolver {
            config_path: config_path.to_string(),
            last_modified: HashMap::new(),
        }
    }
    
    fn read_service_config(&self, service_name: &str) -> Result<(Vec<ServiceInstance>, SystemTime), ResolveError> {
        // 构建配置文件路径
        let config_file = format!("{}/{}.json", self.config_path, service_name);
        
        // 检查文件是否存在
        let metadata = match std::fs::metadata(&config_file) {
            Ok(meta) => meta,
            Err(_) => {
                return Err(ResolveError {
                    message: format!("配置文件 {} 不存在", config_file),
                    error_type: ResolveErrorType::ServiceNotFound,
                });
            }
        };
        
        // 获取修改时间
        let modified = match metadata.modified() {
            Ok(time) => time,
            Err(_) => {
                return Err(ResolveError {
                    message: format!("无法获取配置文件 {} 的修改时间", config_file),
                    error_type: ResolveErrorType::InternalError,
                });
            }
        };
        
        // 如果文件未修改，返回缓存
        if let Some(last_time) = self.last_modified.get(service_name) {
            if *last_time >= modified {
                // 这里应该返回缓存的实例
                // 简化实现：假设需要重新读取
            }
        }
        
        // 读取文件内容
        let content = match std::fs::read_to_string(&config_file) {
            Ok(content) => content,
            Err(_) => {
                return Err(ResolveError {
                    message: format!("无法读取配置文件 {}", config_file),
                    error_type: ResolveErrorType::InternalError,
                });
            }
        };
        
        // 解析JSON
        let instances: Vec<ServiceInstance> = match serde_json::from_str(&content) {
            Ok(instances) => instances,
            Err(_) => {
                return Err(ResolveError {
                    message: format!("无法解析配置文件 {}", config_file),
                    error_type: ResolveErrorType::InternalError,
                });
            }
        };
        
        Ok((instances, modified))
    }
}

impl ServiceResolver for FileSystemServiceResolver {
    fn name(&self) -> &str {
        "文件系统服务解析器"
    }
    
    fn resolve(&self, service_name: &str) -> Result<Vec<ServiceInstance>, ResolveError> {
        // 读取服务配置
        let (instances, modified) = self.read_service_config(service_name)?;
        
        // 更新最后修改时间
        self.last_modified.insert(service_name.to_string(), modified);
        
        Ok(instances)
    }
}

// HTTP健康检查器
struct HttpHealthChecker {
    path: String,
    timeout: Duration,
    http_client: reqwest::Client,
}

impl HttpHealthChecker {
    fn new(path: &str, timeout: Duration) -> Self {
        HttpHealthChecker {
            path: path.to_string(),
            timeout,
            http_client: reqwest::Client::builder()
                .timeout(timeout)
                .build()
                .unwrap(),
        }
    }
}

impl HealthChecker for HttpHealthChecker {
    fn name(&self) -> &str {
        "HTTP健康检查器"
    }
    
    fn check(&self, instance: &ServiceInstance) -> HealthStatus {
        // 构建健康检查URL
        let url = format!("http://{}:{}{}", instance.host, instance.port, self.path);
        
        // 执行HTTP请求
        match self.http_client.get(&url).send() {
            Ok(response) => {
                if response.status().is_success() {
                    HealthStatus::Healthy
                } else {
                    HealthStatus::Unhealthy
                }
            },
            Err(_) => HealthStatus::Unhealthy,
        }
    }
    
    fn get_check_interval(&self) -> Duration {
        Duration::from_secs(10) // 默认每10秒检查一次
    }
}

// TCP健康检查器
struct TcpHealthChecker {
    timeout: Duration,
}

impl TcpHealthChecker {
    fn new(timeout: Duration) -> Self {
        TcpHealthChecker {
            timeout,
        }
    }
}

impl HealthChecker for TcpHealthChecker {
    fn name(&self) -> &str {
        "TCP健康检查器"
    }
    
    fn check(&self, instance: &ServiceInstance) -> HealthStatus {
        // 尝试建立TCP连接
        let addr = format!("{}:{}", instance.host, instance.port);
        
        match std::net::TcpStream::connect_timeout(&addr.parse().unwrap(), self.timeout) {
            Ok(_) => HealthStatus::Healthy,
            Err(_) => HealthStatus::Unhealthy,
        }
    }
    
    fn get_check_interval(&self) -> Duration {
        Duration::from_secs(15) // 默认每15秒检查一次
    }
}
```

### 4.7 分布式锁

分布式锁提供了一种机制，允许分布式系统中的多个节点对共享资源进行互斥访问。

```rust
struct DistributedLockManager {
    lock_providers: HashMap<String, Box<dyn LockProvider>>,
    active_locks: Arc<RwLock<HashMap<String, Lock>>>,
    default_provider: String,
}

trait LockProvider: Send + Sync {
    fn name(&self) -> &str;
    fn acquire(&self, lock_name: &str, timeout: Duration) -> Result<LockHandle, LockError>;
    fn release(&self, handle: &LockHandle) -> Result<(), LockError>;
    fn refresh(&self, handle: &LockHandle) -> Result<(), LockError>;
    fn is_locked(&self, lock_name: &str) -> Result<bool, LockError>;
    fn get_owner(&self, lock_name: &str) -> Result<Option<String>, LockError>;
}

struct Lock {
    name: String,
    owner: String,
    provider: String,
    acquired_at: Instant,
    expires_at: Option<Instant>,
    handle: LockHandle,
    metadata: HashMap<String, String>,
}

struct LockHandle {
    id: String,
    name: String,
    provider: String,
    token: String,
}

struct LockError {
    message: String,
    error_type: LockErrorType,
}

enum LockErrorType {
    AlreadyLocked,
    NotLocked,
    Timeout,
    ConnectionFailed,
    InternalError,
}

impl DistributedLockManager {
    fn new(default_provider: &str) -> Self {
        DistributedLockManager {
            lock_providers: HashMap::new(),
            active_locks: Arc::new(RwLock::new(HashMap::new())),
            default_provider: default_provider.to_string(),
        }
    }
    
    fn register_provider(&mut self, provider: Box<dyn LockProvider>) -> Result<(), String> {
        let name = provider.name().to_string();
        
        if self.lock_providers.contains_key(&name) {
            return Err(format!("锁提供器 '{}' 已经注册", name));
        }
        
        self.lock_providers.insert(name, provider);
        Ok(())
    }
    
    fn set_default_provider(&mut self, provider_name: &str) -> Result<(), String> {
        if !self.lock_providers.contains_key(provider_name) {
            return Err(format!("锁提供器 '{}' 未注册", provider_name));
        }
        
        self.default_provider = provider_name.to_string();
        Ok(())
    }
    
    fn acquire_lock(&self, lock_name: &str, timeout: Duration) -> Result<Lock, LockError> {
        self.acquire_lock_with_provider(lock_name, &self.default_provider, timeout)
    }
    
    fn acquire_lock_with_provider(&self, lock_name: &str, provider_name: &str, timeout: Duration) -> Result<Lock, LockError> {
        // 检查锁提供器是否存在
        let provider = match self.lock_providers.get(provider_name) {
            Some(provider) => provider,
            None => {
                return Err(LockError {
                    message: format!("锁提供器 '{}' 未注册", provider_name),
                    error_type: LockErrorType::InternalError,
                });
            }
        };
        
        // 尝试获取锁
        let handle = provider.acquire(lock_name, timeout)?;
        
        // 创建锁对象
        let lock = Lock {
            name: lock_name.to_string(),
            owner: "current-node".to_string(), // 在实际实现中，这应该是当前节点的唯一标识符
            provider: provider_name.to_string(),
            acquired_at: Instant::now(),
            expires_at: Some(Instant::now() + timeout),
            handle: handle.clone(),
            metadata: HashMap::new(),
        };
        
        // 记录活动锁
        let mut active_locks = self.active_locks.write().unwrap();
        active_locks.insert(lock_name.to_string(), lock.clone());
        
        Ok(lock)
    }
    
    fn release_lock(&self, lock: &Lock) -> Result<(), LockError> {
        // 检查锁提供器是否存在
        let provider = match self.lock_providers.get(&lock.provider) {
            Some(provider) => provider,
            None => {
                return Err(LockError {
                    message: format!("锁提供器 '{}' 未注册", lock.provider),
                    error_type: LockErrorType::InternalError,
                });
            }
        };
        
        // 释放锁
        provider.release(&lock.handle)?;
        
        // 移除活动锁
        let mut active_locks = self.active_locks.write().unwrap();
        active_locks.remove(&lock.name);
        
        Ok(())
    }
    
    fn refresh_lock(&self, lock: &Lock) -> Result<Lock, LockError> {
        // 检查锁提供器是否存在
        let provider = match self.lock_providers.get(&lock.provider) {
            Some(provider) => provider,
            None => {
                return Err(LockError {
                    message: format!("锁提供器 '{}' 未注册", lock.provider),
                    error_type: LockErrorType::InternalError,
                });
            }
        };
        
        // 刷新锁
        provider.refresh(&lock.handle)?;
        
        // 更新锁对象
        let mut updated_lock = lock.clone();
        if let Some(expiry) = lock.expires_at {
            let now = Instant::now();
            let timeout = expiry.duration_since(lock.acquired_at);
            updated_lock.expires_at = Some(now + timeout);
        }
        
        // 更新活动锁
        let mut active_locks = self.active_locks.write().unwrap();
        active_locks.insert(lock.name.clone(), updated_lock.clone());
        
        Ok(updated_lock)
    }
    
    fn is_locked(&self, lock_name: &str) -> Result<bool, LockError> {
        self.is_locked_with_provider(lock_name, &self.default_provider)
    }
    
    fn is_locked_with_provider(&self, lock_name: &str, provider_name: &str) -> Result<bool, LockError> {
        // 检查锁提供器是否存在
        let provider = match self.lock_providers.get(provider_name) {
            Some(provider) => provider,
            None => {
                return Err(LockError {
                    message: format!("锁提供器 '{}' 未注册", provider_name),
                    error_type: LockErrorType::InternalError,
                });
            }
        };
        
        // 检查锁状态
        provider.is_locked(lock_name)
    }
    
    fn get_active_locks(&self) -> HashMap<String, Lock> {
        let active_locks = self.active_locks.read().unwrap();
        active_locks.clone()
    }
}

// Redis分布式锁提供器
struct RedisLockProvider {
    client: redis::Client,
    lock_prefix: String,
    node_id: String,
    default_timeout: Duration,
    clock_drift_factor: f64,
}

impl RedisLockProvider {
    fn new(redis_url: &str, lock_prefix: &str, node_id: &str) -> Result<Self, redis::RedisError> {
        let client = redis::Client::open(redis_url)?;
        
        Ok(RedisLockProvider {
            client,
            lock_prefix: lock_prefix.to_string(),
            node_id: node_id.to_string(),
            default_timeout: Duration::from_secs(30),
            clock_drift_factor: 0.01, // 1%的时钟漂移容忍度
        })
    }
    
    fn get_lock_key(&self, lock_name: &str) -> String {
        format!("{}:{}", self.lock_prefix, lock_name)
    }
    
    fn get_token(&self, lock_name: &str) -> String {
        format!("{}:{}:{}", self.node_id, lock_name, uuid::Uuid::new_v4())
    }
}

impl LockProvider for RedisLockProvider {
    fn name(&self) -> &str {
        "Redis锁提供器"
    }
    
    fn acquire(&self, lock_name: &str, timeout: Duration) -> Result<LockHandle, LockError> {
        let mut conn = match self.client.get_connection() {
            Ok(conn) => conn,
            Err(err) => {
                return Err(LockError {
                    message: format!("无法连接到Redis: {}", err),
                    error_type: LockErrorType::ConnectionFailed,
                });
            }
        };
        
        let lock_key = self.get_lock_key(lock_name);
        let token = self.get_token(lock_name);
        let expiry = timeout.as_millis() as usize;
        
        // 使用Redlock算法设置锁
        // 使用NX选项只有在键不存在时才设置
        // 使用PX选项设置毫秒级过期时间
        let result: bool = redis::cmd("SET")
            .arg(&lock_key)
            .arg(&token)
            .arg("NX")
            .arg("PX")
            .arg(expiry)
            .query(&mut conn)
            .map_err(|err| LockError {
                message: format!("Redis SET操作失败: {}", err),
                error_type: LockErrorType::InternalError,
            })?;
        
        if result {
            // 成功获取锁
            Ok(LockHandle {
                id: uuid::Uuid::new_v4().to_string(),
                name: lock_name.to_string(),
                provider: self.name().to_string(),
                token,
            })
        } else {
            // 锁已被其他节点持有
            Err(LockError {
                message: format!("锁 '{}' 已被其他节点持有", lock_name),
                error_type: LockErrorType::AlreadyLocked,
            })
        }
    }
    
    fn release(&self, handle: &LockHandle) -> Result<(), LockError> {
        let mut conn = match self.client.get_connection() {
            Ok(conn) => conn,
            Err(err) => {
                return Err(LockError {
                    message: format!("无法连接到Redis: {}", err),
                    error_type: LockErrorType::ConnectionFailed,
                });
            }
        };
        
        let lock_key = self.get_lock_key(&handle.name);
        
        // 使用Lua脚本原子性地检查并释放锁
        // 这确保我们只释放自己的锁，避免意外释放其他节点的锁
        let script = r"
            if redis.call('get', KEYS[1]) == ARGV[1] then
                return redis.call('del', KEYS[1])
            else
                return 0
            end
        ";
        
        let result: i32 = redis::cmd("EVAL")
            .arg(script)
            .arg(1) // 1个键
            .arg(&lock_key)
            .arg(&handle.token)
            .query(&mut conn)
            .map_err(|err| LockError {
                message: format!("Redis EVAL操作失败: {}", err),
                error_type: LockErrorType::InternalError,
            })?;
        
        if result == 1 {
            // 成功释放锁
            Ok(())
        } else {
            // 锁不存在或已被其他节点持有
            Err(LockError {
                message: format!("锁 '{}' 不存在或已被其他节点持有", handle.name),
                error_type: LockErrorType::NotLocked,
            })
        }
    }
    
    fn refresh(&self, handle: &LockHandle) -> Result<(), LockError> {
        let mut conn = match self.client.get_connection() {
            Ok(conn) => conn,
            Err(err) => {
                return Err(LockError {
                    message: format!("无法连接到Redis: {}", err),
                    error_type: LockErrorType::ConnectionFailed,
                });
            }
        };
        
        let lock_key = self.get_lock_key(&handle.name);
        let expiry = self.default_timeout.as_millis() as usize;
        
        // 使用Lua脚本原子性地检查并刷新锁
        let script = r"
            if redis.call('get', KEYS[1]) == ARGV[1] then
                return redis.call('pexpire', KEYS[1], ARGV[2])
            else
                return 0
            end
        ";
        
        let result: i32 = redis::cmd("EVAL")
            .arg(script)
            .arg(1) // 1个键
            .arg(&lock_key)
            .arg(&handle.token)
            .arg(expiry)
            .query(&mut conn)
            .map_err(|err| LockError {
                message: format!("Redis EVAL操作失败: {}", err),
                error_type: LockErrorType::InternalError,
            })?;
        
        if result == 1 {
            // 成功刷新锁
            Ok(())
        } else {
            // 锁不存在或已被其他节点持有
            Err(LockError {
                message: format!("锁 '{}' 不存在或已被其他节点持有", handle.name),
                error_type: LockErrorType::NotLocked,
            })
        }
    }
    
    fn is_locked(&self, lock_name: &str) -> Result<bool, LockError> {
        let mut conn = match self.client.get_connection() {
            Ok(conn) => conn,
            Err(err) => {
                return Err(LockError {
                    message: format!("无法连接到Redis: {}", err),
                    error_type: LockErrorType::ConnectionFailed,
                });
            }
        };
        
        let lock_key = self.get_lock_key(lock_name);
        
        // 检查键是否存在
        let exists: bool = redis::cmd("EXISTS")
            .arg(&lock_key)
            .query(&mut conn)
            .map_err(|err| LockError {
                message: format!("Redis EXISTS操作失败: {}", err),
                error_type: LockErrorType::InternalError,
            })?;
        
        Ok(exists)
    }
    
    fn get_owner(&self, lock_name: &str) -> Result<Option<String>, LockError> {
        let mut conn = match self.client.get_connection() {
            Ok(conn) => conn,
            Err(err) => {
                return Err(LockError {
                    message: format!("无法连接到Redis: {}", err),
                    error_type: LockErrorType::ConnectionFailed,
                });
            }
        };
        
        let lock_key = self.get_lock_key(lock_name);
        
        // 获取锁的值
        let value: Option<String> = redis::cmd("GET")
            .arg(&lock_key)
            .query(&mut conn)
            .map_err(|err| LockError {
                message: format!("Redis GET操作失败: {}", err),
                error_type: LockErrorType::InternalError,
            })?;
        
        match value {
            Some(token) => {
                // 解析令牌以获取所有者信息
                let parts: Vec<&str> = token.split(':').collect();
                if parts.len() >= 2 {
                    Ok(Some(parts[0].to_string()))
                } else {
                    Ok(None)
                }
            },
            None => Ok(None),
        }
    }
}

// 内存锁提供器（单节点使用，用于测试）
struct InMemoryLockProvider {
    locks: Arc<RwLock<HashMap<String, (String, Instant)>>>,
    node_id: String,
}

impl InMemoryLockProvider {
    fn new(node_id: &str) -> Self {
        InMemoryLockProvider {
            locks: Arc::new(RwLock::new(HashMap::new())),
            node_id: node_id.to_string(),
        }
    }
    
    fn get_token(&self, lock_name: &str) -> String {
        format!("{}:{}:{}", self.node_id, lock_name, uuid::Uuid::new_v4())
    }
    
    fn cleanup_expired_locks(&self) {
        let mut locks = self.locks.write().unwrap();
        let now = Instant::now();
        
        // 移除所有过期的锁
        locks.retain(|_, (_, expires_at)| *expires_at > now);
    }
}

impl LockProvider for InMemoryLockProvider {
    fn name(&self) -> &str {
        "内存锁提供器"
    }
    
    fn acquire(&self, lock_name: &str, timeout: Duration) -> Result<LockHandle, LockError> {
        // 先清理过期的锁
        self.cleanup_expired_locks();
        
        let mut locks = self.locks.write().unwrap();
        
        // 检查锁是否已存在
        if let Some((_, expires_at)) = locks.get(lock_name) {
            if *expires_at > Instant::now() {
                return Err(LockError {
                    message: format!("锁 '{}' 已被持有", lock_name),
                    error_type: LockErrorType::AlreadyLocked,
                });
            }
        }
        
        // 创建新的锁
        let token = self.get_token(lock_name);
        let expires_at = Instant::now() + timeout;
        
        locks.insert(lock_name.to_string(), (token.clone(), expires_at));
        
        Ok(LockHandle {
            id: uuid::Uuid::new_v4().to_string(),
            name: lock_name.to_string(),
            provider: self.name().to_string(),
            token,
        })
    }
    
    fn release(&self, handle: &LockHandle) -> Result<(), LockError> {
        let mut locks = self.locks.write().unwrap();
        
        // 检查锁是否存在并且令牌匹配
        if let Some((token, _)) = locks.get(&handle.name) {
            if token == &handle.token {
                locks.remove(&handle.name);
                return Ok(());
            }
        }
        
        Err(LockError {
            message: format!("锁 '{}' 不存在或已被其他节点持有", handle.name),
            error_type: LockErrorType::NotLocked,
        })
    }
    
    fn refresh(&self, handle: &LockHandle) -> Result<(), LockError> {
        let mut locks = self.locks.write().unwrap();
        
        // 检查锁是否存在并且令牌匹配
        if let Some((token, _)) = locks.get(&handle.name) {
            if token == &handle.token {
                // 更新过期时间
                let expires_at = Instant::now() + Duration::from_secs(30); // 默认30秒
                locks.insert(handle.name.clone(), (token.clone(), expires_at));
                return Ok(());
            }
        }
        
        Err(LockError {
            message: format!("锁 '{}' 不存在或已被其他节点持有", handle.name),
            error_type: LockErrorType::NotLocked,
        })
    }
    
    fn is_locked(&self, lock_name: &str) -> Result<bool, LockError> {
        // 先清理过期的锁
        self.cleanup_expired_locks();
        
        let locks = self.locks.read().unwrap();
        
        if let Some((_, expires_at)) = locks.get(lock_name) {
            return Ok(*expires_at > Instant::now());
        }
        
        Ok(false)
    }
    
    fn get_owner(&self, lock_name: &str) -> Result<Option<String>, LockError> {
        // 先清理过期的锁
        self.cleanup_expired_locks();
        
        let locks = self.locks.read().unwrap();
        
        if let Some((token, expires_at)) = locks.get(lock_name) {
            if *expires_at > Instant::now() {
                // 解析令牌以获取所有者信息
                let parts: Vec<&str> = token.split(':').collect();
                if parts.len() >= 2 {
                    return Ok(Some(parts[0].to_string()));
                }
            }
        }
        
        Ok(None)
    }
}

// 分布式锁监控器
struct LockMonitor {
    lock_manager: Arc<DistributedLockManager>,
    monitor_interval: Duration,
    active_monitors: Arc<RwLock<HashMap<String, JoinHandle<()>>>>,
    running: Arc<AtomicBool>,
}

impl LockMonitor {
    fn new(lock_manager: Arc<DistributedLockManager>, monitor_interval: Duration) -> Self {
        LockMonitor {
            lock_manager,
            monitor_interval,
            active_monitors: Arc::new(RwLock::new(HashMap::new())),
            running: Arc::new(AtomicBool::new(false)),
        }
    }
    
    fn start(&self) -> Result<(), String> {
        if self.running.load(Ordering::SeqCst) {
            return Err("锁监控器已经在运行".to_string());
        }
        
        self.running.store(true, Ordering::SeqCst);
        
        // 启动主监控线程
        let lock_manager = self.lock_manager.clone();
        let monitor_interval = self.monitor_interval;
        let active_monitors = self.active_monitors.clone();
        let running = self.running.clone();
        
        std::thread::spawn(move || {
            while running.load(Ordering::SeqCst) {
                // 获取所有活动锁
                let active_locks = lock_manager.get_active_locks();
                
                // 更新监控器
                for (lock_name, lock) in active_locks {
                    let active_monitors_clone = active_monitors.clone();
                    
                    // 检查是否已经有监控器在运行
                    let exists = {
                        let monitors = active_monitors_clone.read().unwrap();
                        monitors.contains_key(&lock_name)
                    };
                    
                    if !exists {
                        // 为锁创建新的监控器
                        let lock_manager_clone = lock_manager.clone();
                        let lock_clone = lock.clone();
                        let running_clone = running.clone();
                        
                        let handle = std::thread::spawn(move || {
                            Self::monitor_lock(lock_manager_clone, lock_clone, running_clone);
                        });
                        
                        // 保存监控器句柄
                        let mut monitors = active_monitors_clone.write().unwrap();
                        monitors.insert(lock_name.clone(), handle);
                    }
                }
                
                // 清理已完成的监控器
                {
                    let mut monitors = active_monitors.write().unwrap();
                    let mut to_remove = Vec::new();
                    
                    for (lock_name, handle) in monitors.iter() {
                        if handle.is_finished() {
                            to_remove.push(lock_name.clone());
                        }
                    }
                    
                    for lock_name in to_remove {
                        monitors.remove(&lock_name);
                    }
                }
                
                // 等待下一个监控间隔
                std::thread::sleep(monitor_interval);
            }
        });
        
        Ok(())
    }
    
    fn stop(&self) {
        self.running.store(false, Ordering::SeqCst);
        
        // 等待所有监控器完成
        let monitors = self.active_monitors.read().unwrap();
        for (_, handle) in monitors.iter() {
            // 在实际实现中，我们可能需要更优雅地终止线程
            // 例如使用通道发送终止信号
        }
    }
    
    fn monitor_lock(lock_manager: Arc<DistributedLockManager>, lock: Lock, running: Arc<AtomicBool>) {
        let refresh_interval = Duration::from_secs(5); // 每5秒刷新一次
        
        while running.load(Ordering::SeqCst) {
            // 检查锁是否快要过期
            if let Some(expires_at) = lock.expires_at {
                let now = Instant::now();
                let remaining = expires_at.saturating_duration_since(now);
                
                // 如果剩余时间少于刷新间隔的两倍，则刷新锁
                if remaining < refresh_interval * 2 {
                    match lock_manager.refresh_lock(&lock) {
                        Ok(refreshed_lock) => {
                            // 更新锁对象
                            // 在实际实现中，我们可能需要一个更复杂的机制来更新其他监控线程的锁对象
                            println!("成功刷新锁 '{}'", lock.name);
                        },
                        Err(err) => {
                            println!("刷新锁 '{}' 失败: {}", lock.name, err.message);
                            return; // 退出监控
                        }
                    }
                }
            }
            
            // 等待下一个刷新间隔
            std::thread::sleep(refresh_interval);
        }
    }
}

// 分布式速率限制器
struct DistributedRateLimiter {
    rate_limiters: HashMap<String, Box<dyn RateLimiter>>,
    default_limiter: String,
}

trait RateLimiter: Send + Sync {
    fn name(&self) -> &str;
    fn try_acquire(&self, key: &str, permits: u32) -> Result<bool, RateLimitError>;
    fn get_rate(&self, key: &str) -> Result<f64, RateLimitError>;
    fn update_rate(&self, key: &str, rate: f64) -> Result<(), RateLimitError>;
    fn reset(&self, key: &str) -> Result<(), RateLimitError>;
}

struct RateLimitError {
    message: String,
    error_type: RateLimitErrorType,
}

enum RateLimitErrorType {
    KeyNotFound,
    ConnectionFailed,
    InternalError,
}

impl DistributedRateLimiter {
    fn new(default_limiter: &str) -> Self {
        DistributedRateLimiter {
            rate_limiters: HashMap::new(),
            default_limiter: default_limiter.to_string(),
        }
    }
    
    fn register_limiter(&mut self, limiter: Box<dyn RateLimiter>) -> Result<(), String> {
        let name = limiter.name().to_string();
        
        if self.rate_limiters.contains_key(&name) {
            return Err(format!("速率限制器 '{}' 已经注册", name));
        }
        
        self.rate_limiters.insert(name, limiter);
        Ok(())
    }
    
    fn set_default_limiter(&mut self, limiter_name: &str) -> Result<(), String> {
        if !self.rate_limiters.contains_key(limiter_name) {
            return Err(format!("速率限制器 '{}' 未注册", limiter_name));
        }
        
        self.default_limiter = limiter_name.to_string();
        Ok(())
    }
    
    fn try_acquire(&self, key: &str, permits: u32) -> Result<bool, RateLimitError> {
        self.try_acquire_with_limiter(key, permits, &self.default_limiter)
    }
    
    fn try_acquire_with_limiter(&self, key: &str, permits: u32, limiter_name: &str) -> Result<bool, RateLimitError> {
        // 检查限制器是否存在
        let limiter = match self.rate_limiters.get(limiter_name) {
            Some(limiter) => limiter,
            None => {
                return Err(RateLimitError {
                    message: format!("速率限制器 '{}' 未注册", limiter_name),
                    error_type: RateLimitErrorType::InternalError,
                });
            }
        };
        
        // 尝试获取令牌
        limiter.try_acquire(key, permits)
    }
    
    fn get_rate(&self, key: &str) -> Result<f64, RateLimitError> {
        self.get_rate_with_limiter(key, &self.default_limiter)
    }
    
    fn get_rate_with_limiter(&self, key: &str, limiter_name: &str) -> Result<f64, RateLimitError> {
        // 检查限制器是否存在
        let limiter = match self.rate_limiters.get(limiter_name) {
            Some(limiter) => limiter,
            None => {
                return Err(RateLimitError {
                    message: format!("速率限制器 '{}' 未注册", limiter_name),
                    error_type: RateLimitErrorType::InternalError,
                });
            }
        };
        
        // 获取速率
        limiter.get_rate(key)
    }
    
    fn update_rate(&self, key: &str, rate: f64) -> Result<(), RateLimitError> {
        self.update_rate_with_limiter(key, rate, &self.default_limiter)
    }
    
    fn update_rate_with_limiter(&self, key: &str, rate: f64, limiter_name: &str) -> Result<(), RateLimitError> {
        // 检查限制器是否存在
        let limiter = match self.rate_limiters.get(limiter_name) {
            Some(limiter) => limiter,
            None => {
                return Err(RateLimitError {
                    message: format!("速率限制器 '{}' 未注册", limiter_name),
                    error_type: RateLimitErrorType::InternalError,
                });
            }
        };
        
        // 更新速率
        limiter.update_rate(key, rate)
    }
    
    fn reset(&self, key: &str) -> Result<(), RateLimitError> {
        self.reset_with_limiter(key, &self.default_limiter)
    }
    
    fn reset_with_limiter(&self, key: &str, limiter_name: &str) -> Result<(), RateLimitError> {
        // 检查限制器是否存在
        let limiter = match self.rate_limiters.get(limiter_name) {
            Some(limiter) => limiter,
            None => {
                return Err(RateLimitError {
                    message: format!("速率限制器 '{}' 未注册", limiter_name),
                    error_type: RateLimitErrorType::InternalError,
                });
            }
        };
        
        // 重置限制器
        limiter.reset(key)
    }
}

// Redis令牌桶限速器
struct RedisTokenBucketRateLimiter {
    client: redis::Client,
    key_prefix: String,
    default_capacity: u32,
    default_rate: f64,
}

impl RedisTokenBucketRateLimiter {
    fn new(redis_url: &str, key_prefix: &str, default_capacity: u32, default_rate: f64) -> Result<Self, redis::RedisError> {
        let client = redis::Client::open(redis_url)?;
        
        Ok(RedisTokenBucketRateLimiter {
            client,
            key_prefix: key_prefix.to_string(),
            default_capacity,
            default_rate,
        })
    }
    
    fn get_bucket_key(&self, key: &str) -> String {
        format!("{}:bucket:{}", self.key_prefix, key)
    }
    
    fn get_rate_key(&self, key: &str) -> String {
        format!("{}:rate:{}", self.key_prefix, key)
    }
}

impl RateLimiter for RedisTokenBucketRateLimiter {
    fn name(&self) -> &str {
        "Redis令牌桶限速器"
    }
    
    fn try_acquire(&self, key: &str, permits: u32) -> Result<bool, RateLimitError> {
        let mut conn = match self.client.get_connection() {
            Ok(conn) => conn,
            Err(err) => {
                return Err(RateLimitError {
                    message: format!("无法连接到Redis: {}", err),
                    error_type: RateLimitErrorType::ConnectionFailed,
                });
            }
        };
        
        let bucket_key = self.get_bucket_key(key);
        let rate_key = self.get_rate_key(key);
        
        // 使用Lua脚本原子性地实现令牌桶算法
        let script = r"
            -- 获取速率和上次更新时间
            local rate = redis.call('GET', KEYS[2])
            if not rate then
                rate = ARGV[2] -- 默认速率
                redis.call('SET', KEYS[2], rate)
            end
            rate = tonumber(rate)
            
            -- 获取当前桶状态
            local bucket = redis.call('HMGET', KEYS[1], 'tokens', 'last_refill')
            local tokens = tonumber(bucket[1] or ARGV[3]) -- 默认容量
            local last_refill = tonumber(bucket[2] or 0)
            
            -- 计算经过的时间和新增的令牌
            local now = tonumber(ARGV[1])
            local delta = math.max(0, now - last_refill)
            local new_tokens = math.min(ARGV[3], tokens + delta * rate)
            
            -- 检查是否有足够的令牌
            if new_tokens >= tonumber(ARGV[4]) then
                -- 扣除令牌并更新桶
                new_tokens = new_tokens - tonumber(ARGV[4])
                redis.call('HMSET', KEYS[1], 'tokens', new_tokens, 'last_refill', now)
                return 1
            else
                -- 保持桶状态不变
                redis.call('HMSET', KEYS[1], 'tokens', tokens, 'last_refill', last_refill)
                return 0
            end
        ";
        
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        let result: i32 = redis::cmd("EVAL")
            .arg(script)
            .arg(2) // 2个键
            .arg(&bucket_key)
            .arg(&rate_key)
            .arg(now)
            .arg(self.default_rate)
            .arg(self.default_capacity)
            .arg(permits)
            .query(&mut conn)
            .map_err(|err| RateLimitError {
                message: format!("Redis EVAL操作失败: {}", err),
                error_type: RateLimitErrorType::InternalError,
            })?;
        
        Ok(result == 1)
    }
    
    fn get_rate(&self, key: &str) -> Result<f64, RateLimitError> {
        let mut conn = match self.client.get_connection() {
            Ok(conn) => conn,
            Err(err) => {
                return Err(RateLimitError {
                    message: format!("无法连接到Redis: {}", err),
                    error_type: RateLimitErrorType::ConnectionFailed,
                });
            }
        };
        
        let rate_key = self.get_rate_key(key);
        
        let rate: Option<String> = redis::cmd("GET")
            .arg(&rate_key)
            .query(&mut conn)
            .map_err(|err| RateLimitError {
                message: format!("Redis GET操作失败: {}", err),
                error_type: RateLimitErrorType::InternalError,
            })?;
        
        match rate {
            Some(rate_str) => {
                let rate = rate_str.parse::<f64>().map_err(|_| RateLimitError {
                    message: format!("无法解析速率值: {}", rate_str),
                    error_type: RateLimitErrorType::InternalError,
                })?;
                
                Ok(rate)
            },
            None => Ok(self.default_rate),
        }
    }
    
    fn update_rate(&self, key: &str, rate: f64) -> Result<(), RateLimitError> {
        let mut conn = match self.client.get_connection() {
            Ok(conn) => conn,
            Err(err) => {
                return Err(RateLimitError {
                    message: format!("无法连接到Redis: {}", err),
                    error_type: RateLimitErrorType::ConnectionFailed,
                });
            }
        };
        
        let rate_key = self.get_rate_key(key);
        
        let _: () = redis::cmd("SET")
            .arg(&rate_key)
            .arg(rate.to_string())
            .query(&mut conn)
            .map_err(|err| RateLimitError {
                message: format!("Redis SET操作失败: {}", err),
                error_type: RateLimitErrorType::InternalError,
            })?;
        
        Ok(())
    }
    
    fn reset(&self, key: &str) -> Result<(), RateLimitError> {
        let mut conn = match self.client.get_connection() {
            Ok(conn) => conn,
            Err(err) => {
                return Err(RateLimitError {
                    message: format!("无法连接到Redis: {}", err),
                    error_type: RateLimitErrorType::ConnectionFailed,
                });
            }
        };
        
        let bucket_key = self.get_bucket_key(key);
        
        let _: () = redis::cmd("DEL")
            .arg(&bucket_key)
            .query(&mut conn)
            .map_err(|err| RateLimitError {
                message: format!("Redis DEL操作失败: {}", err),
                error_type: RateLimitErrorType::InternalError,
            })?;
        
        Ok(())
    }
}
```

### 4.8 分布式工作队列

分布式工作队列允许将任务发送到远程执行者上执行，实现分布式任务处理。

```rust
struct DistributedWorkQueue {
    queue_providers: HashMap<String, Box<dyn QueueProvider>>,
    worker_pools: HashMap<String, WorkerPool>,
    default_provider: String,
}

trait QueueProvider: Send + Sync {
    fn name(&self) -> &str;
    fn push(&self, queue_name: &str, task: Task) -> Result<String, QueueError>;
    fn pop(&self, queue_name: &str) -> Result<Option<Task>, QueueError>;
    fn peek(&self, queue_name: &str, task_id: &str) -> Result<Option<Task>, QueueError>;
    fn delete(&self, queue_name: &str, task_id: &str) -> Result<(), QueueError>;
    fn size(&self, queue_name: &str) -> Result<usize, QueueError>;
    fn clear(&self, queue_name: &str) -> Result<(), QueueError>;
}

struct Task {
    id: String,
    payload: Vec<u8>,
    created_at: SystemTime,
    priority: u32,
    retry_count: u32,
    max_retries: u32,
    delay_until: Option<SystemTime>,
    metadata: HashMap<String, String>,
}

struct WorkerPool {
    queue_name: String,
    provider_name: String,
    workers: Vec<JoinHandle<()>>,
    handler: Arc<dyn Fn(Task) -> Result<(), String> + Send + Sync>,
    running: Arc<AtomicBool>,
    concurrency: usize,
}

struct QueueError {
    message: String,
    error_type: QueueErrorType,
}

enum QueueErrorType {
    QueueNotFound,
    TaskNotFound,
    ConnectionFailed,
    InternalError,
}

impl DistributedWorkQueue {
    fn new(default_provider: &str) -> Self {
        DistributedWorkQueue {
            queue_providers: HashMap::new(),
            worker_pools: HashMap::new(),
            default_provider: default_provider.to_string(),
        }
    }
    
    fn register_provider(&mut self, provider: Box<dyn QueueProvider>) -> Result<(), String> {
        let name = provider.name().to_string();
        
        if self.queue_providers.contains_key(&name) {
            return Err(format!("队列提供器 '{}' 已经注册", name));
        }
        
        self.queue_providers.insert(name, provider);
        Ok(())
    }
    
    fn set_default_provider(&mut self, provider_name: &str) -> Result<(), String> {
        if !self.queue_providers.contains_key(provider_name) {
            return Err(format!("队列提供器 '{}' 未注册", provider_name));
        }
        
        self.default_provider = provider_name.to_string();
        Ok(())
    }
    
    fn push_task(&self, queue_name: &str, task: Task) -> Result<String, QueueError> {
        self.push_task_with_provider(queue_name, task, &self.default_provider)
    }
    
    fn push_task_with_provider(&self, queue_name: &str, task: Task, provider_name: &str) -> Result<String, QueueError> {
        // 检查提供器是否存在
        let provider = match self.queue_providers.get(provider_name) {
            Some(provider) => provider,
            None => {
                return Err(QueueError {
                    message: format!("队列提供器 '{}' 未注册", provider_name),
                    error_type: QueueErrorType::InternalError,
                });
            }
        };
        
        // 推送任务
        provider.push(queue_name, task)
    }
    
    fn pop_task(&self, queue_name: &str) -> Result<Option<Task>, QueueError> {
        self.pop_task_from_provider(queue_name, &self.default_provider)
    }
    
    fn pop_task_from_provider(&self, queue_name: &str, provider_name: &str) -> Result<Option<Task>, QueueError> {
        // 检查提供器是否存在
        let provider = match self.queue_providers.get(provider_name) {
            Some(provider) => provider,
            None => {
                return Err(QueueError {
                    message: format!("队列提供器 '{}' 未注册", provider_name),
                    error_type: QueueErrorType::InternalError,
                });
            }
        };
        
        // 弹出任务
        provider.pop(queue_name)
    }
    
    fn register_worker<F>(&mut self, queue_name: &str, provider_name: &str, concurrency: usize, handler: F) -> Result<(), String>
    where
        F: Fn(Task) -> Result<(), String> + Send + Sync + 'static,
    {
        // 检查提供器是否存在
        if !self.queue_providers.contains_key(provider_name) {
            return

```rust
Err(format!("队列提供器 '{}' 未注册", provider_name));
        }
        
        // 创建工作池
        let handler_arc = Arc::new(handler);
        let running = Arc::new(AtomicBool::new(true));
        let mut workers = Vec::with_capacity(concurrency);
        
        for _ in 0..concurrency {
            let provider_name_clone = provider_name.to_string();
            let queue_name_clone = queue_name.to_string();
            let handler_clone = handler_arc.clone();
            let providers_clone = self.queue_providers.clone();
            let running_clone = running.clone();
            
            // 启动工作线程
            let handle = std::thread::spawn(move || {
                let provider = providers_clone.get(&provider_name_clone).unwrap();
                
                while running_clone.load(Ordering::SeqCst) {
                    // 尝试从队列中获取任务
                    match provider.pop(&queue_name_clone) {
                        Ok(Some(task)) => {
                            // 处理任务
                            match handler_clone(task.clone()) {
                                Ok(()) => {
                                    // 任务处理成功
                                    println!("任务 {} 处理成功", task.id);
                                },
                                Err(err) => {
                                    // 任务处理失败，如果还有重试次数，重新放入队列
                                    println!("任务 {} 处理失败: {}", task.id, err);
                                    
                                    if task.retry_count < task.max_retries {
                                        let mut retried_task = task;
                                        retried_task.retry_count += 1;
                                        
                                        // 增加延迟，实现退避策略
                                        let delay = std::time::Duration::from_secs(2u64.pow(retried_task.retry_count));
                                        retried_task.delay_until = Some(SystemTime::now() + delay);
                                        
                                        if let Err(push_err) = provider.push(&queue_name_clone, retried_task) {
                                            println!("重新入队任务失败: {}", push_err.message);
                                        }
                                    }
                                }
                            }
                        },
                        Ok(None) => {
                            // 队列为空，等待一段时间
                            std::thread::sleep(std::time::Duration::from_millis(500));
                        },
                        Err(err) => {
                            // 出现错误，等待一段时间
                            println!("从队列 {} 获取任务失败: {}", queue_name_clone, err.message);
                            std::thread::sleep(std::time::Duration::from_secs(1));
                        }
                    }
                }
            });
            
            workers.push(handle);
        }
        
        // 保存工作池
        self.worker_pools.insert(queue_name.to_string(), WorkerPool {
            queue_name: queue_name.to_string(),
            provider_name: provider_name.to_string(),
            workers,
            handler: handler_arc,
            running,
            concurrency,
        });
        
        Ok(())
    }
    
    fn stop_workers(&mut self, queue_name: &str) -> Result<(), String> {
        if let Some(pool) = self.worker_pools.get_mut(queue_name) {
            // 停止工作线程
            pool.running.store(false, Ordering::SeqCst);
            
            // 等待所有工作线程完成
            let mut workers = Vec::new();
            std::mem::swap(&mut workers, &mut pool.workers);
            
            for handle in workers {
                if let Err(err) = handle.join() {
                    println!("等待工作线程完成时出错: {:?}", err);
                }
            }
            
            // 移除工作池
            self.worker_pools.remove(queue_name);
            
            Ok(())
        } else {
            Err(format!("队列 '{}' 的工作池不存在", queue_name))
        }
    }
    
    fn get_queue_size(&self, queue_name: &str) -> Result<usize, QueueError> {
        self.get_queue_size_from_provider(queue_name, &self.default_provider)
    }
    
    fn get_queue_size_from_provider(&self, queue_name: &str, provider_name: &str) -> Result<usize, QueueError> {
        // 检查提供器是否存在
        let provider = match self.queue_providers.get(provider_name) {
            Some(provider) => provider,
            None => {
                return Err(QueueError {
                    message: format!("队列提供器 '{}' 未注册", provider_name),
                    error_type: QueueErrorType::InternalError,
                });
            }
        };
        
        // 获取队列大小
        provider.size(queue_name)
    }
    
    fn clear_queue(&self, queue_name: &str) -> Result<(), QueueError> {
        self.clear_queue_from_provider(queue_name, &self.default_provider)
    }
    
    fn clear_queue_from_provider(&self, queue_name: &str, provider_name: &str) -> Result<(), QueueError> {
        // 检查提供器是否存在
        let provider = match self.queue_providers.get(provider_name) {
            Some(provider) => provider,
            None => {
                return Err(QueueError {
                    message: format!("队列提供器 '{}' 未注册", provider_name),
                    error_type: QueueErrorType::InternalError,
                });
            }
        };
        
        // 清空队列
        provider.clear(queue_name)
    }
}

// Redis队列提供器
struct RedisQueueProvider {
    client: redis::Client,
    queue_prefix: String,
}

impl RedisQueueProvider {
    fn new(redis_url: &str, queue_prefix: &str) -> Result<Self, redis::RedisError> {
        let client = redis::Client::open(redis_url)?;
        
        Ok(RedisQueueProvider {
            client,
            queue_prefix: queue_prefix.to_string(),
        })
    }
    
    fn get_queue_key(&self, queue_name: &str) -> String {
        format!("{}:{}", self.queue_prefix, queue_name)
    }
    
    fn get_delayed_queue_key(&self, queue_name: &str) -> String {
        format!("{}:{}:delayed", self.queue_prefix, queue_name)
    }
    
    fn get_task_key(&self, queue_name: &str, task_id: &str) -> String {
        format!("{}:{}:task:{}", self.queue_prefix, queue_name, task_id)
    }
    
    fn move_delayed_to_ready(&self, queue_name: &str) -> Result<(), QueueError> {
        let mut conn = match self.client.get_connection() {
            Ok(conn) => conn,
            Err(err) => {
                return Err(QueueError {
                    message: format!("无法连接到Redis: {}", err),
                    error_type: QueueErrorType::ConnectionFailed,
                });
            }
        };
        
        let queue_key = self.get_queue_key(queue_name);
        let delayed_queue_key = self.get_delayed_queue_key(queue_name);
        
        // 获取当前时间戳
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        // 使用Lua脚本原子性地移动延迟队列中的任务到就绪队列
        let script = r"
            local delayed_key = KEYS[1]
            local ready_key = KEYS[2]
            local now = tonumber(ARGV[1])
            
            -- 获取所有小于等于当前时间的延迟任务
            local tasks = redis.call('ZRANGEBYSCORE', delayed_key, 0, now)
            
            if #tasks > 0 then
                -- 移除这些任务从延迟队列
                redis.call('ZREMRANGEBYSCORE', delayed_key, 0, now)
                
                -- 将任务添加到就绪队列
                for i, task_id in ipairs(tasks) do
                    redis.call('LPUSH', ready_key, task_id)
                end
            end
            
            return #tasks
        ";
        
        let _: i32 = redis::cmd("EVAL")
            .arg(script)
            .arg(2) // 2个键
            .arg(&delayed_queue_key)
            .arg(&queue_key)
            .arg(now)
            .query(&mut conn)
            .map_err(|err| QueueError {
                message: format!("Redis EVAL操作失败: {}", err),
                error_type: QueueErrorType::InternalError,
            })?;
        
        Ok(())
    }
}

impl QueueProvider for RedisQueueProvider {
    fn name(&self) -> &str {
        "Redis队列提供器"
    }
    
    fn push(&self, queue_name: &str, task: Task) -> Result<String, QueueError> {
        let mut conn = match self.client.get_connection() {
            Ok(conn) => conn,
            Err(err) => {
                return Err(QueueError {
                    message: format!("无法连接到Redis: {}", err),
                    error_type: QueueErrorType::ConnectionFailed,
                });
            }
        };
        
        let task_id = if task.id.is_empty() {
            uuid::Uuid::new_v4().to_string()
        } else {
            task.id.clone()
        };
        
        let mut task_with_id = task;
        task_with_id.id = task_id.clone();
        
        // 序列化任务
        let task_data = serde_json::to_string(&task_with_id).map_err(|err| QueueError {
            message: format!("序列化任务失败: {}", err),
            error_type: QueueErrorType::InternalError,
        })?;
        
        let task_key = self.get_task_key(queue_name, &task_id);
        
        // 存储任务数据
        let _: () = redis::cmd("SET")
            .arg(&task_key)
            .arg(&task_data)
            .query(&mut conn)
            .map_err(|err| QueueError {
                message: format!("Redis SET操作失败: {}", err),
                error_type: QueueErrorType::InternalError,
            })?;
        
        // 检查是否是延迟任务
        if let Some(delay_until) = task_with_id.delay_until {
            let delayed_queue_key = self.get_delayed_queue_key(queue_name);
            
            // 将任务ID添加到延迟队列中，使用时间戳作为分数
            let timestamp = delay_until
                .duration_since(UNIX_EPOCH)
                .unwrap_or_else(|_| Duration::from_secs(0))
                .as_secs();
            
            let _: () = redis::cmd("ZADD")
                .arg(&delayed_queue_key)
                .arg(timestamp)
                .arg(&task_id)
                .query(&mut conn)
                .map_err(|err| QueueError {
                    message: format!("Redis ZADD操作失败: {}", err),
                    error_type: QueueErrorType::InternalError,
                })?;
        } else {
            // 将任务ID添加到队列中
            let queue_key = self.get_queue_key(queue_name);
            
            let _: () = redis::cmd("LPUSH")
                .arg(&queue_key)
                .arg(&task_id)
                .query(&mut conn)
                .map_err(|err| QueueError {
                    message: format!("Redis LPUSH操作失败: {}", err),
                    error_type: QueueErrorType::InternalError,
                })?;
        }
        
        Ok(task_id)
    }
    
    fn pop(&self, queue_name: &str) -> Result<Option<Task>, QueueError> {
        // 先移动延迟队列中的任务到就绪队列
        self.move_delayed_to_ready(queue_name)?;
        
        let mut conn = match self.client.get_connection() {
            Ok(conn) => conn,
            Err(err) => {
                return Err(QueueError {
                    message: format!("无法连接到Redis: {}", err),
                    error_type: QueueErrorType::ConnectionFailed,
                });
            }
        };
        
        let queue_key = self.get_queue_key(queue_name);
        
        // 从队列中弹出任务ID
        let task_id: Option<String> = redis::cmd("RPOP")
            .arg(&queue_key)
            .query(&mut conn)
            .map_err(|err| QueueError {
                message: format!("Redis RPOP操作失败: {}", err),
                error_type: QueueErrorType::InternalError,
            })?;
        
        if let Some(task_id) = task_id {
            let task_key = self.get_task_key(queue_name, &task_id);
            
            // 获取任务数据
            let task_data: Option<String> = redis::cmd("GET")
                .arg(&task_key)
                .query(&mut conn)
                .map_err(|err| QueueError {
                    message: format!("Redis GET操作失败: {}", err),
                    error_type: QueueErrorType::InternalError,
                })?;
            
            if let Some(task_data) = task_data {
                // 删除任务数据
                let _: () = redis::cmd("DEL")
                    .arg(&task_key)
                    .query(&mut conn)
                    .map_err(|err| QueueError {
                        message: format!("Redis DEL操作失败: {}", err),
                        error_type: QueueErrorType::InternalError,
                    })?;
                
                // 反序列化任务
                let task: Task = serde_json::from_str(&task_data).map_err(|err| QueueError {
                    message: format!("反序列化任务失败: {}", err),
                    error_type: QueueErrorType::InternalError,
                })?;
                
                Ok(Some(task))
            } else {
                // 任务数据不存在，可能已被删除
                Ok(None)
            }
        } else {
            // 队列为空
            Ok(None)
        }
    }
    
    fn peek(&self, queue_name: &str, task_id: &str) -> Result<Option<Task>, QueueError> {
        let mut conn = match self.client.get_connection() {
            Ok(conn) => conn,
            Err(err) => {
                return Err(QueueError {
                    message: format!("无法连接到Redis: {}", err),
                    error_type: QueueErrorType::ConnectionFailed,
                });
            }
        };
        
        let task_key = self.get_task_key(queue_name, task_id);
        
        // 获取任务数据
        let task_data: Option<String> = redis::cmd("GET")
            .arg(&task_key)
            .query(&mut conn)
            .map_err(|err| QueueError {
                message: format!("Redis GET操作失败: {}", err),
                error_type: QueueErrorType::InternalError,
            })?;
        
        if let Some(task_data) = task_data {
            // 反序列化任务
            let task: Task = serde_json::from_str(&task_data).map_err(|err| QueueError {
                message: format!("反序列化任务失败: {}", err),
                error_type: QueueErrorType::InternalError,
            })?;
            
            Ok(Some(task))
        } else {
            // 任务不存在
            Ok(None)
        }
    }
    
    fn delete(&self, queue_name: &str, task_id: &str) -> Result<(), QueueError> {
        let mut conn = match self.client.get_connection() {
            Ok(conn) => conn,
            Err(err) => {
                return Err(QueueError {
                    message: format!("无法连接到Redis: {}", err),
                    error_type: QueueErrorType::ConnectionFailed,
                });
            }
        };
        
        let task_key = self.get_task_key(queue_name, task_id);
        let queue_key = self.get_queue_key(queue_name);
        let delayed_queue_key = self.get_delayed_queue_key(queue_name);
        
        // 删除任务数据
        let _: () = redis::cmd("DEL")
            .arg(&task_key)
            .query(&mut conn)
            .map_err(|err| QueueError {
                message: format!("Redis DEL操作失败: {}", err),
                error_type: QueueErrorType::InternalError,
            })?;
        
        // 从队列中删除任务ID
        let _: () = redis::cmd("LREM")
            .arg(&queue_key)
            .arg(0) // 删除所有匹配的元素
            .arg(task_id)
            .query(&mut conn)
            .map_err(|err| QueueError {
                message: format!("Redis LREM操作失败: {}", err),
                error_type: QueueErrorType::InternalError,
            })?;
        
        // 从延迟队列中删除任务ID
        let _: () = redis::cmd("ZREM")
            .arg(&delayed_queue_key)
            .arg(task_id)
            .query(&mut conn)
            .map_err(|err| QueueError {
                message: format!("Redis ZREM操作失败: {}", err),
                error_type: QueueErrorType::InternalError,
            })?;
        
        Ok(())
    }
    
    fn size(&self, queue_name: &str) -> Result<usize, QueueError> {
        let mut conn = match self.client.get_connection() {
            Ok(conn) => conn,
            Err(err) => {
                return Err(QueueError {
                    message: format!("无法连接到Redis: {}", err),
                    error_type: QueueErrorType::ConnectionFailed,
                });
            }
        };
        
        let queue_key = self.get_queue_key(queue_name);
        let delayed_queue_key = self.get_delayed_queue_key(queue_name);
        
        // 获取队列长度
        let queue_len: usize = redis::cmd("LLEN")
            .arg(&queue_key)
            .query(&mut conn)
            .map_err(|err| QueueError {
                message: format!("Redis LLEN操作失败: {}", err),
                error_type: QueueErrorType::InternalError,
            })?;
        
        // 获取延迟队列长度
        let delayed_len: usize = redis::cmd("ZCARD")
            .arg(&delayed_queue_key)
            .query(&mut conn)
            .map_err(|err| QueueError {
                message: format!("Redis ZCARD操作失败: {}", err),
                error_type: QueueErrorType::InternalError,
            })?;
        
        Ok(queue_len + delayed_len)
    }
    
    fn clear(&self, queue_name: &str) -> Result<(), QueueError> {
        let mut conn = match self.client.get_connection() {
            Ok(conn) => conn,
            Err(err) => {
                return Err(QueueError {
                    message: format!("无法连接到Redis: {}", err),
                    error_type: QueueErrorType::ConnectionFailed,
                });
            }
        };
        
        let queue_key = self.get_queue_key(queue_name);
        let delayed_queue_key = self.get_delayed_queue_key(queue_name);
        let task_pattern = self.get_task_key(queue_name, "*");
        
        // 删除队列
        let _: () = redis::cmd("DEL")
            .arg(&queue_key)
            .query(&mut conn)
            .map_err(|err| QueueError {
                message: format!("Redis DEL操作失败: {}", err),
                error_type: QueueErrorType::InternalError,
            })?;
        
        // 删除延迟队列
        let _: () = redis::cmd("DEL")
            .arg(&delayed_queue_key)
            .query(&mut conn)
            .map_err(|err| QueueError {
                message: format!("Redis DEL操作失败: {}", err),
                error_type: QueueErrorType::InternalError,
            })?;
        
        // 删除所有任务数据
        let task_keys: Vec<String> = redis::cmd("KEYS")
            .arg(&task_pattern)
            .query(&mut conn)
            .map_err(|err| QueueError {
                message: format!("Redis KEYS操作失败: {}", err),
                error_type: QueueErrorType::InternalError,
            })?;
        
        if !task_keys.is_empty() {
            let _: () = redis::cmd("DEL")
                .arg(&task_keys)
                .query(&mut conn)
                .map_err(|err| QueueError {
                    message: format!("Redis DEL操作失败: {}", err),
                    error_type: QueueErrorType::InternalError,
                })?;
        }
        
        Ok(())
    }
}

// 内存队列提供器
struct InMemoryQueueProvider {
    queues: Arc<RwLock<HashMap<String, VecDeque<String>>>>,
    delayed_queues: Arc<RwLock<HashMap<String, BTreeMap<SystemTime, Vec<String>>>>>,
    tasks: Arc<RwLock<HashMap<String, Task>>>,
}

impl InMemoryQueueProvider {
    fn new() -> Self {
        InMemoryQueueProvider {
            queues: Arc::new(RwLock::new(HashMap::new())),
            delayed_queues: Arc::new(RwLock::new(HashMap::new())),
            tasks: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    fn get_task_key(&self, queue_name: &str, task_id: &str) -> String {
        format!("{}:{}", queue_name, task_id)
    }
    
    fn move_delayed_to_ready(&self) {
        let now = SystemTime::now();
        
        // 获取所有需要移动的任务
        let mut to_move = Vec::new();
        
        {
            let delayed_queues = self.delayed_queues.read().unwrap();
            
            for (queue_name, delayed_tasks) in delayed_queues.iter() {
                let mut tasks_to_move = Vec::new();
                
                for (time, tasks) in delayed_tasks.iter() {
                    if *time <= now {
                        for task_id in tasks {
                            tasks_to_move.push(task_id.clone());
                        }
                    } else {
                        break; // BTreeMap是有序的，一旦遇到未到期的时间，可以停止遍历
                    }
                }
                
                if !tasks_to_move.is_empty() {
                    to_move.push((queue_name.clone(), tasks_to_move));
                }
            }
        }
        
        // 移动任务
        if !to_move.is_empty() {
            let mut delayed_queues = self.delayed_queues.write().unwrap();
            let mut queues = self.queues.write().unwrap();
            
            for (queue_name, tasks) in to_move {
                let queue = queues.entry(queue_name.clone()).or_insert_with(VecDeque::new);
                let delayed_queue = delayed_queues.get_mut(&queue_name).unwrap();
                
                for task_id in tasks {
                    queue.push_back(task_id.clone());
                    
                    // 从延迟队列中移除任务
                    for (_, tasks) in delayed_queue.iter_mut() {
                        tasks.retain(|id| *id != task_id);
                    }
                }
                
                // 清理空的时间条目
                delayed_queue.retain(|_, tasks| !tasks.is_empty());
            }
        }
    }
}

impl QueueProvider for InMemoryQueueProvider {
    fn name(&self) -> &str {
        "内存队列提供器"
    }
    
    fn push(&self, queue_name: &str, task: Task) -> Result<String, QueueError> {
        let task_id = if task.id.is_empty() {
            uuid::Uuid::new_v4().to_string()
        } else {
            task.id.clone()
        };
        
        let mut task_with_id = task;
        task_with_id.id = task_id.clone();
        
        // 存储任务
        let task_key = self.get_task_key(queue_name, &task_id);
        
        {
            let mut tasks = self.tasks.write().unwrap();
            tasks.insert(task_key, task_with_id.clone());
        }
        
        // 检查是否是延迟任务
        if let Some(delay_until) = task_with_id.delay_until {
            let mut delayed_queues = self.delayed_queues.write().unwrap();
            let delayed_queue = delayed_queues.entry(queue_name.to_string()).or_insert_with(BTreeMap::new);
            
            delayed_queue.entry(delay_until).or_insert_with(Vec::new).push(task_id.clone());
        } else {
            // 将任务添加到队列
            let mut queues = self.queues.write().unwrap();
            let queue = queues.entry(queue_name.to_string()).or_insert_with(VecDeque::new);
            
            queue.push_back(task_id.clone());
        }
        
        Ok(task_id)
    }
    
    fn pop(&self, queue_name: &str) -> Result<Option<Task>, QueueError> {
        // 移动延迟队列中的任务到就绪队列
        self.move_delayed_to_ready();
        
        // 从队列中弹出任务
        let task_id = {
            let mut queues = self.queues.write().unwrap();
            
            if let Some(queue) = queues.get_mut(queue_name) {
                queue.pop_front()
            } else {
                None
            }
        };
        
        if let Some(task_id) = task_id {
            let task_key = self.get_task_key(queue_name, &task_id);
            
            // 获取任务数据
            let mut tasks = self.tasks.write().unwrap();
            
            if let Some(task) = tasks.remove(&task_key) {
                Ok(Some(task))
            } else {
                Ok(None)
            }
        } else {
            Ok(None)
        }
    }
    
    fn peek(&self, queue_name: &str, task_id: &str) -> Result<Option<Task>, QueueError> {
        let task_key = self.get_task_key(queue_name, task_id);
        
        // 获取任务数据
        let tasks = self.tasks.read().unwrap();
        
        if let Some(task) = tasks.get(&task_key) {
            Ok(Some(task.clone()))
        } else {
            Ok(None)
        }
    }
    
    fn delete(&self, queue_name: &str, task_id: &str) -> Result<(), QueueError> {
        let task_key = self.get_task_key(queue_name, task_id);
        
        // 删除任务数据
        {
            let mut tasks = self.tasks.write().unwrap();
            tasks.remove(&task_key);
        }
        
        // 从队列中删除任务
        {
            let mut queues = self.queues.write().unwrap();
            
            if let Some(queue) = queues.get_mut(queue_name) {
                queue.retain(|id| id != task_id);
            }
        }
        
        // 从延迟队列中删除任务
        {
            let mut delayed_queues = self.delayed_queues.write().unwrap();
            
            if let Some(delayed_queue) = delayed_queues.get_mut(queue_name) {
                for (_, tasks) in delayed_queue.iter_mut() {
                    tasks.retain(|id| id != task_id);
                }
                
                // 清理空的时间条目
                delayed_queue.retain(|_, tasks| !tasks.is_empty());
            }
        }
        
        Ok(())
    }
    
    fn size(&self, queue_name: &str) -> Result<usize, QueueError> {
        let mut size = 0;
        
        // 计算就绪队列大小
        {
            let queues = self.queues.read().unwrap();
            
            if let Some(queue) = queues.get(queue_name) {
                size += queue.len();
            }
        }
        
        // 计算延迟队列大小
        {
            let delayed_queues = self.delayed_queues.read().unwrap();
            
            if let Some(delayed_queue) = delayed_queues.get(queue_name) {
                for (_, tasks) in delayed_queue {
                    size += tasks.len();
                }
            }
        }
        
        Ok(size)
    }
    
    fn clear(&self, queue_name: &str) -> Result<(), QueueError> {
        // 清空就绪队列
        {
            let mut queues = self.queues.write().unwrap();
            queues.remove(queue_name);
        }
        
        // 清空延迟队列
        {
            let mut delayed_queues = self.delayed_queues.write().unwrap();
            delayed_queues.remove(queue_name);
        }
        
        // 删除所有相关的任务数据
        {
            let mut tasks = self.tasks.write().unwrap();
            tasks.retain(|key, _| !key.starts_with(&format!("{}:", queue_name)));
        }
        
        Ok(())
    }
}
```

### 4.9 批处理框架

分布式批处理框架可用于高效处理大量数据，通常包括任务划分、调度、执行和结果聚合。

```rust
struct BatchProcessingFramework {
    job_registry: Arc<RwLock<HashMap<String, JobDefinition>>>,
    running_jobs: Arc<RwLock<HashMap<String, JobStatus>>>,
    executors: Vec<Box<dyn JobExecutor>>,
    scheduler: Box<dyn JobScheduler>,
}

trait JobExecutor: Send + Sync {
    fn name(&self) -> &str;
    fn execute(&self, job: &Job) -> Result<JobResult, JobError>;
    fn get_capabilities(&self) -> ExecutorCapabilities;
    fn is_available(&self) -> bool;
}

trait JobScheduler: Send + Sync {
    fn name(&self) -> &str;
    fn schedule(&self, job: &Job, executors: &[Box<dyn JobExecutor>]) -> Result<Vec<TaskAssignment>, JobError>;
    fn handle_failure(&self, job: &Job, task: &Task, executor: &dyn JobExecutor) -> Result<FailureAction, JobError>;
}

struct ExecutorCapabilities {
    supported_job_types: Vec<String>,
    max_concurrent_tasks: usize,
    resource_limits: HashMap<String, usize>,
    features: HashSet<String>,
}

struct JobDefinition {
    id: String,
    name: String,
    description: String,
    job_type: String,
    parameters: HashMap<String, String>,
    input_data: Vec<DataSource>,
    output_data: Vec<DataSink>,
    tasks: Vec<TaskDefinition>,
    dependencies: Vec<JobDependency>,
    schedule: Option<JobSchedule>,
    retry_strategy: RetryStrategy,
    timeout: Duration,
    created_at: SystemTime,
}

struct Job {
    definition: JobDefinition,
    instance_id: String,
    parent_job_id: Option<String>,
    tasks: Vec<Task>,
    status: JobStatus,
    start_time: Option<SystemTime>,
    end_time: Option<SystemTime>,
    progress: f64,
    metrics: HashMap<String, f64>,
}

struct Task {
    id: String,
    job_id: String,
    name: String,
    task_type: String,
    parameters: HashMap<String, String>,
    dependencies: Vec<String>,
    status: TaskStatus,
    assigned_executor: Option<String>,
    start_time: Option<SystemTime>,
    end_time: Option<SystemTime>,
    retry_count: usize,
}

struct TaskDefinition {
    name: String,
    task_type: String,
    parameters: HashMap<String, String>,
    dependencies: Vec<String>,
    retry_strategy: RetryStrategy,
    timeout: Duration,
}

struct TaskAssignment {
    task_id: String,
    executor_name: String,
    priority: u32,
}

struct JobDependency {
    job_id: String,
    dependency_type: DependencyType,
}

enum DependencyType {
    Success,
    Completion,
    Custom(String),
}

struct JobSchedule {
    cron_expression: String,
    start_date: Option<SystemTime>,
    end_date: Option<SystemTime>,
    time_zone: String,
}

enum JobStatus {
    Pending,
    Running,
    Succeeded,
    Failed(String),
    Canceled,
    Paused,
}

enum TaskStatus {
    Pending,
    Running,
    Succeeded,
    Failed(String),
    Canceled,
    Skipped,
}

enum FailureAction {
    Retry,
    Skip,
    FailJob,
    Reassign(String),
}

struct RetryStrategy {
    max_retries: usize,
    retry_delay: Duration,
    backoff_factor: f64,
    max_delay: Duration,
}

struct DataSource {
    name: String,
    source_type: String,
    location: String,
    format: String,
    schema: Option<String>,
    parameters: HashMap<String, String>,
}

struct DataSink {
    name: String,
    sink_type: String,
    location: String,
    format: String,
    parameters: HashMap<String, String>,
}

struct JobResult {
    task_results: HashMap<String, TaskResult>,
    summary: HashMap<String, String>,
    output_locations: HashMap<String, String>,
    metrics: HashMap<String, f64>,
}

struct TaskResult {
    success: bool,
    error_message: Option<String>,
    output: HashMap<String, String>,
    metrics: HashMap<String, f64>,
}

struct JobError {
    message: String,
    error_type: JobErrorType,
    task_id: Option<String>,
}

enum JobErrorType {
    InvalidJob,
    ExecutionError,
    SchedulingError,
    Timeout,
    ResourceExhausted,
    DependencyError,
    InputDataError,
    OutputDataError,
    InternalError,
}

impl BatchProcessingFramework {
    fn new(scheduler: Box<dyn JobScheduler>) -> Self {
        BatchProcessingFramework {
            job_registry: Arc::new(RwLock::new(HashMap::new())),
            running_jobs: Arc::new(RwLock::new(HashMap::new())),
            executors: Vec::new(),
            scheduler,
        }
    }
    
    fn register_executor(&mut self, executor: Box<dyn JobExecutor>) -> Result<(), String> {
        for existing in &self.executors {
            if existing.name() == executor.name() {
                return Err(format!("执行器 '{}' 已经注册", executor.name()));
            }
        }
        
        self.executors.push(executor);
        Ok(())
    }
    
    fn register_job_definition(&self, definition: JobDefinition) -> Result<(), JobError> {
        let mut registry = self.job_registry.write().unwrap();
        
        if registry.contains_key(&definition.id) {
            return Err(JobError {
                message: format!("作业 '{}' 已经注册", definition.id),
                error_type: JobErrorType::InvalidJob,
                task_id: None,
            });
        }
        
        registry.insert(definition.id.clone(), definition);
        Ok(())
    }
    
    fn submit_job(&self, job_id: &str, parameters: HashMap<String, String>) -> Result<String, JobError> {
        // 获取作业定义
        let definition = {
            let registry

```rust
= self.job_registry.read().unwrap();
            
            registry.get(job_id).cloned().ok_or_else(|| JobError {
                message: format!("作业 '{}' 未注册", job_id),
                error_type: JobErrorType::InvalidJob,
                task_id: None,
            })?
        };
        
        // 合并参数
        let mut merged_parameters = definition.parameters.clone();
        for (key, value) in parameters {
            merged_parameters.insert(key, value);
        }
        
        // 创建作业实例
        let instance_id = uuid::Uuid::new_v4().to_string();
        
        // 创建任务
        let tasks = self.create_tasks(&definition, &instance_id)?;
        
        let job = Job {
            definition: JobDefinition {
                parameters: merged_parameters,
                ..definition
            },
            instance_id: instance_id.clone(),
            parent_job_id: None,
            tasks,
            status: JobStatus::Pending,
            start_time: None,
            end_time: None,
            progress: 0.0,
            metrics: HashMap::new(),
        };
        
        // 将作业添加到运行中的作业列表
        {
            let mut running_jobs = self.running_jobs.write().unwrap();
            running_jobs.insert(instance_id.clone(), JobStatus::Pending);
        }
        
        // 启动作业执行线程
        self.execute_job_async(job)?;
        
        Ok(instance_id)
    }
    
    fn create_tasks(&self, definition: &JobDefinition, instance_id: &str) -> Result<Vec<Task>, JobError> {
        let mut tasks = Vec::new();
        
        for (index, task_def) in definition.tasks.iter().enumerate() {
            let task_id = format!("{}-{}", instance_id, index);
            
            tasks.push(Task {
                id: task_id,
                job_id: instance_id.to_string(),
                name: task_def.name.clone(),
                task_type: task_def.task_type.clone(),
                parameters: task_def.parameters.clone(),
                dependencies: task_def.dependencies.clone(),
                status: TaskStatus::Pending,
                assigned_executor: None,
                start_time: None,
                end_time: None,
                retry_count: 0,
            });
        }
        
        Ok(tasks)
    }
    
    fn execute_job_async(&self, job: Job) -> Result<(), JobError> {
        let job_arc = Arc::new(Mutex::new(job));
        let job_registry = self.job_registry.clone();
        let running_jobs = self.running_jobs.clone();
        let executors = self.executors.clone();
        let scheduler = Arc::new(self.scheduler.clone());
        
        std::thread::spawn(move || {
            let instance_id;
            {
                let job = job_arc.lock().unwrap();
                instance_id = job.instance_id.clone();
                
                // 更新作业状态为运行中
                running_jobs
                    .write()
                    .unwrap()
                    .insert(instance_id.clone(), JobStatus::Running);
            }
            
            // 执行作业
            let result = Self::execute_job(job_arc.clone(), executors, scheduler);
            
            // 更新作业状态
            let status = match result {
                Ok(_) => JobStatus::Succeeded,
                Err(error) => JobStatus::Failed(error.message),
            };
            
            running_jobs.write().unwrap().insert(instance_id, status);
        });
        
        Ok(())
    }
    
    fn execute_job(
        job: Arc<Mutex<Job>>, 
        executors: Vec<Box<dyn JobExecutor>>, 
        scheduler: Arc<Box<dyn JobScheduler>>
    ) -> Result<JobResult, JobError> {
        // 获取作业信息
        let mut job_instance = job.lock().unwrap();
        
        // 设置作业开始时间
        job_instance.start_time = Some(SystemTime::now());
        job_instance.status = JobStatus::Running;
        
        // 检查依赖的作业是否满足
        // 简化：实际实现中，这应该检查所有依赖作业的状态
        
        // 计算可以立即执行的任务
        let ready_tasks = Self::get_ready_tasks(&job_instance);
        drop(job_instance);
        
        if ready_tasks.is_empty() {
            return Err(JobError {
                message: "没有可执行的任务".to_string(),
                error_type: JobErrorType::InvalidJob,
                task_id: None,
            });
        }
        
        // 调度和执行任务
        let mut task_results = HashMap::new();
        let mut remaining_tasks = ready_tasks;
        
        while !remaining_tasks.is_empty() {
            // 调度任务
            let assignments = scheduler.schedule(&*job.lock().unwrap(), &executors)?;
            
            if assignments.is_empty() {
                return Err(JobError {
                    message: "无法调度任务".to_string(),
                    error_type: JobErrorType::SchedulingError,
                    task_id: None,
                });
            }
            
            // 执行分配的任务
            for assignment in assignments {
                let task_id = assignment.task_id.clone();
                let executor_name = assignment.executor_name.clone();
                
                // 找到执行器
                let executor = executors.iter()
                    .find(|e| e.name() == executor_name)
                    .ok_or_else(|| JobError {
                        message: format!("找不到执行器 '{}'", executor_name),
                        error_type: JobErrorType::InternalError,
                        task_id: Some(task_id.clone()),
                    })?;
                
                // 更新任务状态
                {
                    let mut job_instance = job.lock().unwrap();
                    for task in &mut job_instance.tasks {
                        if task.id == task_id {
                            task.status = TaskStatus::Running;
                            task.start_time = Some(SystemTime::now());
                            task.assigned_executor = Some(executor_name.clone());
                            break;
                        }
                    }
                }
                
                // 执行任务
                let result = match executor.execute(&*job.lock().unwrap()) {
                    Ok(result) => {
                        // 成功执行任务
                        let task_result = TaskResult {
                            success: true,
                            error_message: None,
                            output: result.task_results.get(&task_id)
                                .map(|r| r.output.clone())
                                .unwrap_or_default(),
                            metrics: result.task_results.get(&task_id)
                                .map(|r| r.metrics.clone())
                                .unwrap_or_default(),
                        };
                        task_results.insert(task_id.clone(), task_result);
                        
                        // 更新任务状态
                        {
                            let mut job_instance = job.lock().unwrap();
                            for task in &mut job_instance.tasks {
                                if task.id == task_id {
                                    task.status = TaskStatus::Succeeded;
                                    task.end_time = Some(SystemTime::now());
                                    break;
                                }
                            }
                        }
                        
                        true
                    },
                    Err(error) => {
                        // 任务执行失败
                        // 根据失败策略决定下一步操作
                        let task = job.lock().unwrap().tasks.iter()
                            .find(|t| t.id == task_id)
                            .unwrap()
                            .clone();
                        
                        match scheduler.handle_failure(&*job.lock().unwrap(), &task, &**executor)? {
                            FailureAction::Retry => {
                                // 重试任务
                                let mut job_instance = job.lock().unwrap();
                                for task in &mut job_instance.tasks {
                                    if task.id == task_id {
                                        if task.retry_count < job_instance.definition.retry_strategy.max_retries {
                                            task.status = TaskStatus::Pending;
                                            task.retry_count += 1;
                                            task.assigned_executor = None;
                                        } else {
                                            task.status = TaskStatus::Failed(error.message.clone());
                                            task.end_time = Some(SystemTime::now());
                                            
                                            let task_result = TaskResult {
                                                success: false,
                                                error_message: Some(error.message.clone()),
                                                output: HashMap::new(),
                                                metrics: HashMap::new(),
                                            };
                                            task_results.insert(task_id.clone(), task_result);
                                        }
                                        break;
                                    }
                                }
                                
                                // 继续执行下一个任务
                                false
                            },
                            FailureAction::Skip => {
                                // 跳过任务
                                let mut job_instance = job.lock().unwrap();
                                for task in &mut job_instance.tasks {
                                    if task.id == task_id {
                                        task.status = TaskStatus::Skipped;
                                        task.end_time = Some(SystemTime::now());
                                        break;
                                    }
                                }
                                
                                let task_result = TaskResult {
                                    success: false,
                                    error_message: Some(error.message.clone()),
                                    output: HashMap::new(),
                                    metrics: HashMap::new(),
                                };
                                task_results.insert(task_id.clone(), task_result);
                                
                                true
                            },
                            FailureAction::FailJob => {
                                // 整个作业失败
                                let mut job_instance = job.lock().unwrap();
                                job_instance.status = JobStatus::Failed(error.message.clone());
                                job_instance.end_time = Some(SystemTime::now());
                                
                                // 更新失败任务的状态
                                for task in &mut job_instance.tasks {
                                    if task.id == task_id {
                                        task.status = TaskStatus::Failed(error.message.clone());
                                        task.end_time = Some(SystemTime::now());
                                        break;
                                    }
                                }
                                
                                return Err(JobError {
                                    message: format!("任务 '{}' 失败导致作业失败: {}", task_id, error.message),
                                    error_type: JobErrorType::ExecutionError,
                                    task_id: Some(task_id),
                                });
                            },
                            FailureAction::Reassign(new_executor) => {
                                // 重新分配任务到不同的执行器
                                let mut job_instance = job.lock().unwrap();
                                for task in &mut job_instance.tasks {
                                    if task.id == task_id {
                                        task.status = TaskStatus::Pending;
                                        task.assigned_executor = Some(new_executor);
                                        break;
                                    }
                                }
                                
                                false
                            },
                        }
                    }
                };
                
                // 如果任务成功完成，更新剩余任务集合
                if result {
                    remaining_tasks = Self::get_ready_tasks(&*job.lock().unwrap());
                }
            }
        }
        
        // 设置作业结束时间和状态
        {
            let mut job_instance = job.lock().unwrap();
            job_instance.end_time = Some(SystemTime::now());
            
            // 检查所有任务的状态，决定作业的最终状态
            let all_succeeded = job_instance.tasks.iter()
                .all(|task| matches!(task.status, TaskStatus::Succeeded | TaskStatus::Skipped));
            
            if all_succeeded {
                job_instance.status = JobStatus::Succeeded;
            } else {
                let failed_tasks: Vec<&Task> = job_instance.tasks.iter()
                    .filter(|task| matches!(task.status, TaskStatus::Failed(_)))
                    .collect();
                
                if !failed_tasks.is_empty() {
                    let error_messages: Vec<String> = failed_tasks.iter()
                        .filter_map(|task| {
                            if let TaskStatus::Failed(msg) = &task.status {
                                Some(format!("任务 '{}': {}", task.name, msg))
                            } else {
                                None
                            }
                        })
                        .collect();
                    
                    job_instance.status = JobStatus::Failed(error_messages.join("; "));
                }
            }
        }
        
        // 构建作业结果
        let result = JobResult {
            task_results,
            summary: HashMap::new(), // 简化：实际应该生成摘要
            output_locations: HashMap::new(), // 简化：实际应该包含输出位置
            metrics: HashMap::new(), // 简化：实际应该汇总指标
        };
        
        Ok(result)
    }
    
    fn get_ready_tasks(job: &Job) -> Vec<Task> {
        let mut ready_tasks = Vec::new();
        
        for task in &job.tasks {
            // 跳过已完成或正在运行的任务
            match task.status {
                TaskStatus::Pending => {},
                _ => continue,
            }
            
            // 检查依赖是否满足
            let dependencies_met = task.dependencies.iter().all(|dep_id| {
                job.tasks.iter().any(|t| {
                    t.name == *dep_id && matches!(t.status, TaskStatus::Succeeded | TaskStatus::Skipped)
                })
            });
            
            if dependencies_met {
                ready_tasks.push(task.clone());
            }
        }
        
        ready_tasks
    }
    
    fn get_job_status(&self, instance_id: &str) -> Result<JobStatus, JobError> {
        let running_jobs = self.running_jobs.read().unwrap();
        
        running_jobs.get(instance_id).cloned().ok_or_else(|| JobError {
            message: format!("作业实例 '{}' 不存在", instance_id),
            error_type: JobErrorType::InvalidJob,
            task_id: None,
        })
    }
    
    fn get_job_details(&self, instance_id: &str) -> Result<Job, JobError> {
        // 简化：实际应该从存储中获取完整的作业详情
        Err(JobError {
            message: "未实现".to_string(),
            error_type: JobErrorType::InternalError,
            task_id: None,
        })
    }
    
    fn cancel_job(&self, instance_id: &str) -> Result<(), JobError> {
        let mut running_jobs = self.running_jobs.write().unwrap();
        
        if let Some(status) = running_jobs.get(instance_id) {
            match status {
                JobStatus::Pending | JobStatus::Running | JobStatus::Paused => {
                    running_jobs.insert(instance_id.to_string(), JobStatus::Canceled);
                    Ok(())
                },
                _ => {
                    Err(JobError {
                        message: format!("作业 '{}' 已经完成，无法取消", instance_id),
                        error_type: JobErrorType::InvalidJob,
                        task_id: None,
                    })
                }
            }
        } else {
            Err(JobError {
                message: format!("作业实例 '{}' 不存在", instance_id),
                error_type: JobErrorType::InvalidJob,
                task_id: None,
            })
        }
    }
    
    fn pause_job(&self, instance_id: &str) -> Result<(), JobError> {
        let mut running_jobs = self.running_jobs.write().unwrap();
        
        if let Some(status) = running_jobs.get(instance_id) {
            if let JobStatus::Running = status {
                running_jobs.insert(instance_id.to_string(), JobStatus::Paused);
                Ok(())
            } else {
                Err(JobError {
                    message: format!("作业 '{}' 不在运行中，无法暂停", instance_id),
                    error_type: JobErrorType::InvalidJob,
                    task_id: None,
                })
            }
        } else {
            Err(JobError {
                message: format!("作业实例 '{}' 不存在", instance_id),
                error_type: JobErrorType::InvalidJob,
                task_id: None,
            })
        }
    }
    
    fn resume_job(&self, instance_id: &str) -> Result<(), JobError> {
        let mut running_jobs = self.running_jobs.write().unwrap();
        
        if let Some(status) = running_jobs.get(instance_id) {
            if let JobStatus::Paused = status {
                running_jobs.insert(instance_id.to_string(), JobStatus::Running);
                Ok(())
            } else {
                Err(JobError {
                    message: format!("作业 '{}' 不处于暂停状态，无法恢复", instance_id),
                    error_type: JobErrorType::InvalidJob,
                    task_id: None,
                })
            }
        } else {
            Err(JobError {
                message: format!("作业实例 '{}' 不存在", instance_id),
                error_type: JobErrorType::InvalidJob,
                task_id: None,
            })
        }
    }
    
    fn list_running_jobs(&self) -> HashMap<String, JobStatus> {
        let running_jobs = self.running_jobs.read().unwrap();
        running_jobs.clone()
    }
    
    fn list_job_definitions(&self) -> Vec<JobDefinition> {
        let registry = self.job_registry.read().unwrap();
        registry.values().cloned().collect()
    }
}

// 简单任务执行器
struct SimpleTaskExecutor {
    name: String,
    capabilities: ExecutorCapabilities,
    task_handlers: HashMap<String, Box<dyn Fn(&Task) -> Result<TaskResult, JobError> + Send + Sync>>,
}

impl SimpleTaskExecutor {
    fn new(name: &str) -> Self {
        let mut capabilities = ExecutorCapabilities {
            supported_job_types: vec!["batch".to_string()],
            max_concurrent_tasks: 4,
            resource_limits: HashMap::new(),
            features: HashSet::new(),
        };
        
        capabilities.resource_limits.insert("memory".to_string(), 1024);
        capabilities.resource_limits.insert("cpu".to_string(), 2);
        
        capabilities.features.insert("local".to_string());
        
        SimpleTaskExecutor {
            name: name.to_string(),
            capabilities,
            task_handlers: HashMap::new(),
        }
    }
    
    fn register_task_handler<F>(&mut self, task_type: &str, handler: F)
    where
        F: Fn(&Task) -> Result<TaskResult, JobError> + Send + Sync + 'static,
    {
        self.task_handlers.insert(task_type.to_string(), Box::new(handler));
    }
}

impl JobExecutor for SimpleTaskExecutor {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn execute(&self, job: &Job) -> Result<JobResult, JobError> {
        let mut task_results = HashMap::new();
        
        // 找出分配给此执行器的任务
        for task in &job.tasks {
            if let Some(executor) = &task.assigned_executor {
                if executor == &self.name && matches!(task.status, TaskStatus::Running) {
                    // 查找对应的处理器
                    if let Some(handler) = self.task_handlers.get(&task.task_type) {
                        // 执行任务
                        let result = handler(task)?;
                        task_results.insert(task.id.clone(), result);
                    } else {
                        return Err(JobError {
                            message: format!("无法处理任务类型 '{}'", task.task_type),
                            error_type: JobErrorType::ExecutionError,
                            task_id: Some(task.id.clone()),
                        });
                    }
                }
            }
        }
        
        // 构建作业结果
        let result = JobResult {
            task_results,
            summary: HashMap::new(),
            output_locations: HashMap::new(),
            metrics: HashMap::new(),
        };
        
        Ok(result)
    }
    
    fn get_capabilities(&self) -> ExecutorCapabilities {
        self.capabilities.clone()
    }
    
    fn is_available(&self) -> bool {
        true // 简化：实际应该检查资源可用性
    }
}

// 简单作业调度器
struct SimpleJobScheduler;

impl SimpleJobScheduler {
    fn new() -> Self {
        SimpleJobScheduler
    }
}

impl JobScheduler for SimpleJobScheduler {
    fn name(&self) -> &str {
        "简单作业调度器"
    }
    
    fn schedule(&self, job: &Job, executors: &[Box<dyn JobExecutor>]) -> Result<Vec<TaskAssignment>, JobError> {
        let mut assignments = Vec::new();
        
        // 找出待执行的任务
        for task in &job.tasks {
            if matches!(task.status, TaskStatus::Pending) {
                // 检查依赖是否满足
                let dependencies_met = task.dependencies.iter().all(|dep_id| {
                    job.tasks.iter().any(|t| {
                        t.name == *dep_id && matches!(t.status, TaskStatus::Succeeded | TaskStatus::Skipped)
                    })
                });
                
                if dependencies_met {
                    // 找一个合适的执行器
                    for executor in executors {
                        if executor.is_available() && 
                           executor.get_capabilities().supported_job_types.contains(&job.definition.job_type) {
                            // 分配任务
                            assignments.push(TaskAssignment {
                                task_id: task.id.clone(),
                                executor_name: executor.name().to_string(),
                                priority: 1, // 简化：固定优先级
                            });
                            
                            break;
                        }
                    }
                }
            }
        }
        
        Ok(assignments)
    }
    
    fn handle_failure(&self, job: &Job, task: &Task, executor: &dyn JobExecutor) -> Result<FailureAction, JobError> {
        // 简单的重试策略
        if task.retry_count < job.definition.retry_strategy.max_retries {
            Ok(FailureAction::Retry)
        } else {
            // 超过最大重试次数
            Ok(FailureAction::FailJob)
        }
    }
}
```

### 4.10 分布式状态机

分布式状态机提供了一种在分布式系统中协调多节点状态转换的机制。

```rust
struct DistributedStateMachine {
    state_registry: Arc<RwLock<HashMap<String, StateDefinition>>>,
    active_states: Arc<RwLock<HashMap<String, StateInstance>>>,
    transitions: Arc<RwLock<HashMap<String, Vec<TransitionDefinition>>>>,
    persistence: Box<dyn StatePersistence>,
    event_handlers: HashMap<String, Vec<Box<dyn Fn(&Event) -> Result<(), StateError> + Send + Sync>>>,
}

trait StatePersistence: Send + Sync {
    fn save_state(&self, instance: &StateInstance) -> Result<(), StateError>;
    fn load_state(&self, instance_id: &str) -> Result<Option<StateInstance>, StateError>;
    fn list_instances(&self) -> Result<Vec<StateInstance>, StateError>;
    fn delete_instance(&self, instance_id: &str) -> Result<(), StateError>;
}

struct StateDefinition {
    id: String,
    name: String,
    initial_state: String,
    states: HashMap<String, State>,
    metadata: HashMap<String, String>,
    created_at: SystemTime,
}

struct State {
    name: String,
    actions: Vec<Action>,
    timeout: Option<Duration>,
    error_handler: Option<ErrorHandler>,
    is_final: bool,
}

struct StateInstance {
    id: String,
    definition_id: String,
    current_state: String,
    context: HashMap<String, serde_json::Value>,
    history: Vec<StateTransition>,
    created_at: SystemTime,
    updated_at: SystemTime,
    status: InstanceStatus,
    metadata: HashMap<String, String>,
}

struct StateTransition {
    from_state: String,
    to_state: String,
    transition_id: String,
    timestamp: SystemTime,
    data: Option<serde_json::Value>,
}

struct TransitionDefinition {
    id: String,
    from_state: String,
    to_state: String,
    condition: Option<Condition>,
    actions: Vec<Action>,
    metadata: HashMap<String, String>,
}

struct Event {
    id: String,
    instance_id: String,
    event_type: String,
    data: serde_json::Value,
    timestamp: SystemTime,
    source: String,
}

struct Action {
    id: String,
    action_type: String,
    parameters: HashMap<String, serde_json::Value>,
    retry_strategy: Option<RetryStrategy>,
    timeout: Option<Duration>,
}

struct Condition {
    condition_type: String,
    parameters: HashMap<String, serde_json::Value>,
}

struct ErrorHandler {
    action: Action,
    next_state: Option<String>,
}

enum InstanceStatus {
    Active,
    Completed,
    Failed(String),
    Terminated,
}

struct StateError {
    message: String,
    error_type: StateErrorType,
}

enum StateErrorType {
    InvalidState,
    InvalidTransition,
    ActionFailed,
    ConditionFailed,
    PersistenceFailed,
    Timeout,
    InternalError,
}

impl DistributedStateMachine {
    fn new(persistence: Box<dyn StatePersistence>) -> Self {
        DistributedStateMachine {
            state_registry: Arc::new(RwLock::new(HashMap::new())),
            active_states: Arc::new(RwLock::new(HashMap::new())),
            transitions: Arc::new(RwLock::new(HashMap::new())),
            persistence,
            event_handlers: HashMap::new(),
        }
    }
    
    fn register_state_definition(&self, definition: StateDefinition) -> Result<(), StateError> {
        // 验证状态机定义
        if definition.states.is_empty() {
            return Err(StateError {
                message: "状态机定义必须包含至少一个状态".to_string(),
                error_type: StateErrorType::InvalidState,
            });
        }
        
        if !definition.states.contains_key(&definition.initial_state) {
            return Err(StateError {
                message: format!("初始状态 '{}' 未在状态列表中定义", definition.initial_state),
                error_type: StateErrorType::InvalidState,
            });
        }
        
        // 注册状态机定义
        let mut registry = self.state_registry.write().unwrap();
        
        if registry.contains_key(&definition.id) {
            return Err(StateError {
                message: format!("状态机定义 '{}' 已存在", definition.id),
                error_type: StateErrorType::InvalidState,
            });
        }
        
        registry.insert(definition.id.clone(), definition);
        
        Ok(())
    }
    
    fn register_transition(&self, transition: TransitionDefinition) -> Result<(), StateError> {
        let registry = self.state_registry.read().unwrap();
        
        // 验证状态是否存在
        let mut valid_states = false;
        
        for definition in registry.values() {
            if definition.states.contains_key(&transition.from_state) && 
               definition.states.contains_key(&transition.to_state) {
                valid_states = true;
                break;
            }
        }
        
        if !valid_states {
            return Err(StateError {
                message: format!("无效的状态转换: {} -> {}", transition.from_state, transition.to_state),
                error_type: StateErrorType::InvalidTransition,
            });
        }
        
        // 注册转换
        let mut transitions = self.transitions.write().unwrap();
        
        let transition_list = transitions
            .entry(transition.from_state.clone())
            .or_insert_with(Vec::new);
        
        transition_list.push(transition);
        
        Ok(())
    }
    
    fn create_instance(&self, definition_id: &str, context: HashMap<String, serde_json::Value>) -> Result<String, StateError> {
        let registry = self.state_registry.read().unwrap();
        
        // 获取状态机定义
        let definition = registry.get(definition_id).ok_or_else(|| StateError {
            message: format!("状态机定义 '{}' 不存在", definition_id),
            error_type: StateErrorType::InvalidState,
        })?;
        
        // 创建实例
        let instance_id = uuid::Uuid::new_v4().to_string();
        let now = SystemTime::now();
        
        let instance = StateInstance {
            id: instance_id.clone(),
            definition_id: definition_id.to_string(),
            current_state: definition.initial_state.clone(),
            context,
            history: Vec::new(),
            created_at: now,
            updated_at: now,
            status: InstanceStatus::Active,
            metadata: HashMap::new(),
        };
        
        // 保存实例
        self.persistence.save_state(&instance)?;
        
        // 添加到活动实例列表
        let mut active_states = self.active_states.write().unwrap();
        active_states.insert(instance_id.clone(), instance);
        
        // 触发初始状态的动作
        self.execute_state_actions(definition_id, &instance_id, &definition.initial_state)?;
        
        Ok(instance_id)
    }
    
    fn trigger_event(&self, event: Event) -> Result<(), StateError> {
        // 查找实例
        let instance = {
            let active_states = self.active_states.read().unwrap();
            
            active_states.get(&event.instance_id).cloned().ok_or_else(|| StateError {
                message: format!("实例 '{}' 不存在", event.instance_id),
                error_type: StateErrorType::InvalidState,
            })?
        };
        
        // 处理事件
        self.process_event(&instance, &event)?;
        
        // 调用事件处理器
        if let Some(handlers) = self.event_handlers.get(&event.event_type) {
            for handler in handlers {
                handler(&event)?;
            }
        }
        
        Ok(())
    }
    
    fn process_event(&self, instance: &StateInstance, event: &Event) -> Result<(), StateError> {
        // 获取可能的转换
        let transitions = {
            let transitions = self.transitions.read().unwrap();
            
            transitions.get(&instance.current_state)
                .cloned()
                .unwrap_or_default()
        };
        
        // 找到匹配的转换
        let mut matched_transition = None;
        
        for transition in transitions {
            // 检查条件
            if let Some(condition) = &transition.condition {
                if !self.evaluate_condition(condition, instance, event)? {
                    continue;
                }
            }
            
            matched_transition = Some(transition);
            break;
        }
        
        // 如果找到匹配的转换，执行转换
        if let Some(transition) = matched_transition {
            self.execute_transition(instance, &transition, event)?;
        }
        
        Ok(())
    }
    
    fn evaluate_condition(&self, condition: &Condition, instance: &StateInstance, event: &Event) -> Result<bool, StateError> {
        // 简化：实际应该根据条件类型实现不同的计算逻辑
        
        match condition.condition_type.as_str() {
            "event_type_equals" => {
                if let Some(event_type) = condition.parameters.get("event_type") {
                    if let Some(expected_type) = event_type.as_str() {
                        return Ok(event.event_type == expected_type);
                    }
                }
                Ok(false)
            },
            "context_value_equals" => {
                if let (Some(path), Some(value)) = (
                    condition.parameters.get("path").and_then(|v| v.as_str()),
                    condition.parameters.get("value")
                ) {
                    if let Some(context_value) = instance.context.get(path) {
                        return Ok(context_value == value);
                    }
                }
                Ok(false)
            },
            "always" => Ok(true),
            _ => {
                Err(StateError {
                    message: format!("未知的条件类型: {}", condition.condition_type),
                    error_type: StateErrorType::ConditionFailed,
                })
            }
        }
    }
    
    fn execute_transition(&self, instance: &StateInstance, transition: &TransitionDefinition, event: &Event) -> Result<(), StateError> {
        // 执行转换的动作
        for action in &transition.actions {
            self.execute_action(action, instance, event)?;
        }
        
        // 创建新的实例状态
        let mut updated_instance = instance.clone();
        updated_instance.current_state = transition.to_state.clone();
        updated_instance.updated_at = SystemTime::now();
        
        // 添加转换历史
        updated_instance.history.push(StateTransition {
            from_state: instance.current_state.clone(),
            to_state: transition.to_state.clone(),
            transition_id: transition.id.clone(),
            timestamp: SystemTime::now(),
            data: Some(event.data.clone()),
        });
        
        // 检查是否是最终状态
        let is_final_state = {
            let registry = self.state_registry.read().unwrap();
            
            if let Some(definition) = registry.get(&instance.definition_id) {
                if let Some(state) = definition.states.get(&transition.to_state) {
                    state.is_final
                } else {
                    false
                }
            } else {
                false
            }
        };
        
        if is_final_state {
            updated_instance.status = InstanceStatus::Completed;
        }
        
        // 保存更新后的实例
        self.persistence.save_state(&updated_instance)?;
        
        // 更新活动实例
        {
            let mut active_states = self.active_states.write().unwrap();
            
            if is_final_state {
                active_states.remove(&instance.id);
            } else {
                active_states.insert(instance.id.clone(), updated_instance.clone());
            }
        }
        
        // 执行新状态的动作
        self.execute_state_actions(&instance.definition_id, &instance.id, &transition.to_state)?;
        
        Ok(())
    }
    
    fn execute_state_actions(&self, definition_id: &str, instance_id: &str, state_name: &str) -> Result<(), StateError> {
        let registry = self.state_registry.read().unwrap();
        
        if let Some(definition) = registry.get(definition_id) {
            if let Some(state) = definition.states.get(state_name) {
                let instance = {
                    let active_states = self.active_states.read().unwrap();
                    active_states.get(instance_id).cloned().ok_or_else(|| StateError {
                        message: format!("实例 '{}' 不存在", instance_id),
                        error_type: StateErrorType::InvalidState,
                    })?
                };
                
                // 执行状态的动作
                for action in &state.actions {
                    // 创建空事件
                    let event = Event {
                        id: uuid::Uuid::new_v4().to_string(),
                        instance_id: instance_id.to_string(),
                        event_type: "state_entered".to_string(),
                        data: serde_json::Value::Null,
                        timestamp: SystemTime::now(),
                        source: "system".to_string(),
                    };
                    
                    self.execute_action(action, &instance, &event)?;
                }
            }
        }
        
        Ok(())
    }
    
    fn execute_action(&self, action: &Action, instance: &StateInstance, event: &Event) -> Result<(), StateError> {
        // 简化：实际

```rust
应该根据动作类型实现不同的逻辑
        
        match action.action_type.as_str() {
            "send_notification" => {
                // 模拟发送通知
                println!("发送通知: {:?}", action.parameters);
                Ok(())
            },
            "update_context" => {
                // 更新实例上下文
                if let (Some(key), Some(value)) = (
                    action.parameters.get("key").and_then(|v| v.as_str()),
                    action.parameters.get("value")
                ) {
                    let mut updated_instance = instance.clone();
                    updated_instance.context.insert(key.to_string(), value.clone());
                    updated_instance.updated_at = SystemTime::now();
                    
                    // 保存更新后的实例
                    self.persistence.save_state(&updated_instance)?;
                    
                    // 更新活动实例
                    let mut active_states = self.active_states.write().unwrap();
                    active_states.insert(instance.id.clone(), updated_instance);
                    
                    Ok(())
                } else {
                    Err(StateError {
                        message: "更新上下文动作缺少必要参数".to_string(),
                        error_type: StateErrorType::ActionFailed,
                    })
                }
            },
            "http_request" => {
                // 模拟HTTP请求
                if let Some(url) = action.parameters.get("url").and_then(|v| v.as_str()) {
                    println!("发送HTTP请求到: {}", url);
                    Ok(())
                } else {
                    Err(StateError {
                        message: "HTTP请求动作缺少URL参数".to_string(),
                        error_type: StateErrorType::ActionFailed,
                    })
                }
            },
            "log" => {
                // 记录日志
                if let Some(message) = action.parameters.get("message").and_then(|v| v.as_str()) {
                    println!("日志: {} - 实例: {}", message, instance.id);
                    Ok(())
                } else {
                    Err(StateError {
                        message: "日志动作缺少消息参数".to_string(),
                        error_type: StateErrorType::ActionFailed,
                    })
                }
            },
            _ => {
                Err(StateError {
                    message: format!("未知的动作类型: {}", action.action_type),
                    error_type: StateErrorType::ActionFailed,
                })
            }
        }
    }
    
    fn register_event_handler<F>(&mut self, event_type: &str, handler: F)
    where
        F: Fn(&Event) -> Result<(), StateError> + Send + Sync + 'static,
    {
        let handlers = self.event_handlers
            .entry(event_type.to_string())
            .or_insert_with(Vec::new);
        
        handlers.push(Box::new(handler));
    }
    
    fn get_instance(&self, instance_id: &str) -> Result<StateInstance, StateError> {
        // 先从活动实例中查找
        {
            let active_states = self.active_states.read().unwrap();
            
            if let Some(instance) = active_states.get(instance_id) {
                return Ok(instance.clone());
            }
        }
        
        // 从持久化存储中加载
        if let Some(instance) = self.persistence.load_state(instance_id)? {
            Ok(instance)
        } else {
            Err(StateError {
                message: format!("实例 '{}' 不存在", instance_id),
                error_type: StateErrorType::InvalidState,
            })
        }
    }
    
    fn terminate_instance(&self, instance_id: &str) -> Result<(), StateError> {
        // 获取实例
        let instance = self.get_instance(instance_id)?;
        
        // 更新实例状态
        let mut terminated_instance = instance;
        terminated_instance.status = InstanceStatus::Terminated;
        terminated_instance.updated_at = SystemTime::now();
        
        // 保存更新后的实例
        self.persistence.save_state(&terminated_instance)?;
        
        // 从活动实例中移除
        let mut active_states = self.active_states.write().unwrap();
        active_states.remove(instance_id);
        
        Ok(())
    }
    
    fn list_instances(&self) -> Result<Vec<StateInstance>, StateError> {
        self.persistence.list_instances()
    }
    
    fn list_active_instances(&self) -> Vec<StateInstance> {
        let active_states = self.active_states.read().unwrap();
        active_states.values().cloned().collect()
    }
    
    fn get_instance_history(&self, instance_id: &str) -> Result<Vec<StateTransition>, StateError> {
        let instance = self.get_instance(instance_id)?;
        Ok(instance.history)
    }
}

// 内存状态持久化实现
struct InMemoryStatePersistence {
    states: Arc<RwLock<HashMap<String, StateInstance>>>,
}

impl InMemoryStatePersistence {
    fn new() -> Self {
        InMemoryStatePersistence {
            states: Arc::new(RwLock::new(HashMap::new())),
        }
    }
}

impl StatePersistence for InMemoryStatePersistence {
    fn save_state(&self, instance: &StateInstance) -> Result<(), StateError> {
        let mut states = self.states.write().unwrap();
        states.insert(instance.id.clone(), instance.clone());
        Ok(())
    }
    
    fn load_state(&self, instance_id: &str) -> Result<Option<StateInstance>, StateError> {
        let states = self.states.read().unwrap();
        Ok(states.get(instance_id).cloned())
    }
    
    fn list_instances(&self) -> Result<Vec<StateInstance>, StateError> {
        let states = self.states.read().unwrap();
        Ok(states.values().cloned().collect())
    }
    
    fn delete_instance(&self, instance_id: &str) -> Result<(), StateError> {
        let mut states = self.states.write().unwrap();
        states.remove(instance_id);
        Ok(())
    }
}

// 文件系统状态持久化实现
struct FileSystemStatePersistence {
    base_path: String,
}

impl FileSystemStatePersistence {
    fn new(base_path: &str) -> Self {
        // 确保目录存在
        std::fs::create_dir_all(base_path).unwrap_or_else(|e| {
            eprintln!("无法创建目录 {}: {}", base_path, e);
        });
        
        FileSystemStatePersistence {
            base_path: base_path.to_string(),
        }
    }
    
    fn get_instance_path(&self, instance_id: &str) -> String {
        format!("{}/{}.json", self.base_path, instance_id)
    }
}

impl StatePersistence for FileSystemStatePersistence {
    fn save_state(&self, instance: &StateInstance) -> Result<(), StateError> {
        let path = self.get_instance_path(&instance.id);
        
        let json = serde_json::to_string_pretty(instance).map_err(|e| StateError {
            message: format!("序列化实例失败: {}", e),
            error_type: StateErrorType::PersistenceFailed,
        })?;
        
        std::fs::write(&path, json).map_err(|e| StateError {
            message: format!("写入文件失败: {}", e),
            error_type: StateErrorType::PersistenceFailed,
        })?;
        
        Ok(())
    }
    
    fn load_state(&self, instance_id: &str) -> Result<Option<StateInstance>, StateError> {
        let path = self.get_instance_path(instance_id);
        
        if !std::path::Path::new(&path).exists() {
            return Ok(None);
        }
        
        let json = std::fs::read_to_string(&path).map_err(|e| StateError {
            message: format!("读取文件失败: {}", e),
            error_type: StateErrorType::PersistenceFailed,
        })?;
        
        let instance: StateInstance = serde_json::from_str(&json).map_err(|e| StateError {
            message: format!("反序列化实例失败: {}", e),
            error_type: StateErrorType::PersistenceFailed,
        })?;
        
        Ok(Some(instance))
    }
    
    fn list_instances(&self) -> Result<Vec<StateInstance>, StateError> {
        let mut instances = Vec::new();
        
        for entry in std::fs::read_dir(&self.base_path).map_err(|e| StateError {
            message: format!("读取目录失败: {}", e),
            error_type: StateErrorType::PersistenceFailed,
        })? {
            let entry = entry.map_err(|e| StateError {
                message: format!("读取目录条目失败: {}", e),
                error_type: StateErrorType::PersistenceFailed,
            })?;
            
            let path = entry.path();
            
            if path.is_file() && path.extension().map_or(false, |ext| ext == "json") {
                if let Some(file_stem) = path.file_stem() {
                    if let Some(instance_id) = file_stem.to_str() {
                        if let Some(instance) = self.load_state(instance_id)? {
                            instances.push(instance);
                        }
                    }
                }
            }
        }
        
        Ok(instances)
    }
    
    fn delete_instance(&self, instance_id: &str) -> Result<(), StateError> {
        let path = self.get_instance_path(instance_id);
        
        if std::path::Path::new(&path).exists() {
            std::fs::remove_file(&path).map_err(|e| StateError {
                message: format!("删除文件失败: {}", e),
                error_type: StateErrorType::PersistenceFailed,
            })?;
        }
        
        Ok(())
    }
}
```

### 4.11 分布式配置和服务发现

分布式配置和服务发现系统允许应用程序查找服务和获取配置，支持动态扩展和故障恢复。

```rust
struct DistributedConfigSystem {
    providers: HashMap<String, Box<dyn ConfigProvider>>,
    observers: HashMap<String, Vec<Box<dyn Fn(&str, &ConfigValue) -> Result<(), ConfigError> + Send + Sync>>>,
    cache: Arc<RwLock<HashMap<String, ConfigValue>>>,
    default_provider: String,
    refresh_interval: Duration,
    running: Arc<AtomicBool>,
}

trait ConfigProvider: Send + Sync {
    fn name(&self) -> &str;
    fn get(&self, key: &str) -> Result<Option<ConfigValue>, ConfigError>;
    fn set(&self, key: &str, value: ConfigValue) -> Result<(), ConfigError>;
    fn delete(&self, key: &str) -> Result<(), ConfigError>;
    fn list(&self, prefix: &str) -> Result<Vec<String>, ConfigError>;
    fn watch(&self, key: &str, callback: Box<dyn Fn(&str, &ConfigValue) -> Result<(), ConfigError> + Send + Sync>) -> Result<WatchId, ConfigError>;
    fn unwatch(&self, watch_id: &WatchId) -> Result<(), ConfigError>;
}

#[derive(Clone, Debug)]
struct ConfigValue {
    value: serde_json::Value,
    version: u64,
    last_modified: SystemTime,
    metadata: HashMap<String, String>,
}

struct WatchId {
    id: String,
    provider: String,
    key: String,
}

struct ConfigError {
    message: String,
    error_type: ConfigErrorType,
}

enum ConfigErrorType {
    KeyNotFound,
    InvalidValue,
    AccessDenied,
    ConnectionFailed,
    WatchError,
    InternalError,
}

impl DistributedConfigSystem {
    fn new(default_provider: &str, refresh_interval: Duration) -> Self {
        DistributedConfigSystem {
            providers: HashMap::new(),
            observers: HashMap::new(),
            cache: Arc::new(RwLock::new(HashMap::new())),
            default_provider: default_provider.to_string(),
            refresh_interval,
            running: Arc::new(AtomicBool::new(false)),
        }
    }
    
    fn register_provider(&mut self, provider: Box<dyn ConfigProvider>) -> Result<(), String> {
        let name = provider.name().to_string();
        
        if self.providers.contains_key(&name) {
            return Err(format!("配置提供器 '{}' 已经注册", name));
        }
        
        self.providers.insert(name, provider);
        Ok(())
    }
    
    fn set_default_provider(&mut self, provider_name: &str) -> Result<(), String> {
        if !self.providers.contains_key(provider_name) {
            return Err(format!("配置提供器 '{}' 未注册", provider_name));
        }
        
        self.default_provider = provider_name.to_string();
        Ok(())
    }
    
    fn start(&self) -> Result<(), String> {
        if self.running.load(Ordering::SeqCst) {
            return Err("配置系统已经在运行".to_string());
        }
        
        self.running.store(true, Ordering::SeqCst);
        
        // 启动刷新缓存的线程
        let cache = self.cache.clone();
        let providers = self.providers.clone();
        let refresh_interval = self.refresh_interval;
        let running = self.running.clone();
        
        std::thread::spawn(move || {
            while running.load(Ordering::SeqCst) {
                // 刷新缓存
                let keys: Vec<String> = {
                    let cache_lock = cache.read().unwrap();
                    cache_lock.keys().cloned().collect()
                };
                
                for key in keys {
                    // 对于每个提供器，尝试获取最新值
                    for provider in providers.values() {
                        if let Ok(Some(value)) = provider.get(&key) {
                            let mut cache_lock = cache.write().unwrap();
                            
                            // 只有当版本更新时才更新缓存
                            if let Some(cached_value) = cache_lock.get(&key) {
                                if value.version > cached_value.version {
                                    cache_lock.insert(key.clone(), value);
                                }
                            } else {
                                cache_lock.insert(key.clone(), value);
                            }
                            
                            break;
                        }
                    }
                }
                
                // 等待下一个刷新周期
                std::thread::sleep(refresh_interval);
            }
        });
        
        Ok(())
    }
    
    fn stop(&self) {
        self.running.store(false, Ordering::SeqCst);
    }
    
    fn get(&self, key: &str) -> Result<ConfigValue, ConfigError> {
        self.get_from_provider(key, &self.default_provider)
    }
    
    fn get_from_provider(&self, key: &str, provider_name: &str) -> Result<ConfigValue, ConfigError> {
        // 先从缓存中查找
        {
            let cache = self.cache.read().unwrap();
            
            if let Some(value) = cache.get(key) {
                return Ok(value.clone());
            }
        }
        
        // 从提供器中获取
        let provider = self.providers.get(provider_name).ok_or_else(|| ConfigError {
            message: format!("配置提供器 '{}' 未注册", provider_name),
            error_type: ConfigErrorType::InternalError,
        })?;
        
        let value = provider.get(key)?.ok_or_else(|| ConfigError {
            message: format!("配置键 '{}' 不存在", key),
            error_type: ConfigErrorType::KeyNotFound,
        })?;
        
        // 更新缓存
        {
            let mut cache = self.cache.write().unwrap();
            cache.insert(key.to_string(), value.clone());
        }
        
        Ok(value)
    }
    
    fn set(&self, key: &str, value: ConfigValue) -> Result<(), ConfigError> {
        self.set_with_provider(key, value, &self.default_provider)
    }
    
    fn set_with_provider(&self, key: &str, value: ConfigValue, provider_name: &str) -> Result<(), ConfigError> {
        // 更新提供器中的值
        let provider = self.providers.get(provider_name).ok_or_else(|| ConfigError {
            message: format!("配置提供器 '{}' 未注册", provider_name),
            error_type: ConfigErrorType::InternalError,
        })?;
        
        provider.set(key, value.clone())?;
        
        // 更新缓存
        {
            let mut cache = self.cache.write().unwrap();
            cache.insert(key.to_string(), value.clone());
        }
        
        // 通知观察者
        if let Some(observers) = self.observers.get(key) {
            for observer in observers {
                if let Err(err) = observer(key, &value) {
                    eprintln!("通知观察者失败: {}", err.message);
                }
            }
        }
        
        Ok(())
    }
    
    fn delete(&self, key: &str) -> Result<(), ConfigError> {
        self.delete_from_provider(key, &self.default_provider)
    }
    
    fn delete_from_provider(&self, key: &str, provider_name: &str) -> Result<(), ConfigError> {
        // 从提供器中删除
        let provider = self.providers.get(provider_name).ok_or_else(|| ConfigError {
            message: format!("配置提供器 '{}' 未注册", provider_name),
            error_type: ConfigErrorType::InternalError,
        })?;
        
        provider.delete(key)?;
        
        // 从缓存中删除
        {
            let mut cache = self.cache.write().unwrap();
            cache.remove(key);
        }
        
        Ok(())
    }
    
    fn watch(&self, key: &str, callback: Box<dyn Fn(&str, &ConfigValue) -> Result<(), ConfigError> + Send + Sync>) -> Result<WatchId, ConfigError> {
        self.watch_with_provider(key, callback, &self.default_provider)
    }
    
    fn watch_with_provider(
        &mut self, 
        key: &str, 
        callback: Box<dyn Fn(&str, &ConfigValue) -> Result<(), ConfigError> + Send + Sync>,
        provider_name: &str
    ) -> Result<WatchId, ConfigError> {
        // 注册到提供器
        let provider = self.providers.get(provider_name).ok_or_else(|| ConfigError {
            message: format!("配置提供器 '{}' 未注册", provider_name),
            error_type: ConfigErrorType::InternalError,
        })?;
        
        let watch_id = provider.watch(key, callback.clone())?;
        
        // 添加到观察者列表
        let observers = self.observers.entry(key.to_string()).or_insert_with(Vec::new);
        observers.push(callback);
        
        Ok(watch_id)
    }
    
    fn unwatch(&self, watch_id: &WatchId) -> Result<(), ConfigError> {
        // 从提供器中取消注册
        let provider = self.providers.get(&watch_id.provider).ok_or_else(|| ConfigError {
            message: format!("配置提供器 '{}' 未注册", watch_id.provider),
            error_type: ConfigErrorType::InternalError,
        })?;
        
        provider.unwatch(watch_id)?;
        
        // 从观察者列表中删除
        // 注意：这里简化了实现，没有真正从观察者列表中删除
        
        Ok(())
    }
    
    fn list(&self, prefix: &str) -> Result<Vec<String>, ConfigError> {
        self.list_from_provider(prefix, &self.default_provider)
    }
    
    fn list_from_provider(&self, prefix: &str, provider_name: &str) -> Result<Vec<String>, ConfigError> {
        let provider = self.providers.get(provider_name).ok_or_else(|| ConfigError {
            message: format!("配置提供器 '{}' 未注册", provider_name),
            error_type: ConfigErrorType::InternalError,
        })?;
        
        provider.list(prefix)
    }
}

// Etcd配置提供器
struct EtcdConfigProvider {
    client: etcd_client::Client,
    name: String,
    watches: Arc<Mutex<HashMap<String, etcd_client::WatchStream>>>,
}

impl EtcdConfigProvider {
    async fn new(endpoints: &[&str], name: &str) -> Result<Self, etcd_client::Error> {
        let client = etcd_client::Client::connect(endpoints, None).await?;
        
        Ok(EtcdConfigProvider {
            client,
            name: name.to_string(),
            watches: Arc::new(Mutex::new(HashMap::new())),
        })
    }
    
    fn config_value_from_kv(&self, kv: etcd_client::KeyValue) -> Result<ConfigValue, ConfigError> {
        let value_str = String::from_utf8_lossy(&kv.value()).to_string();
        
        let value: serde_json::Value = serde_json::from_str(&value_str).map_err(|err| ConfigError {
            message: format!("无法解析配置值: {}", err),
            error_type: ConfigErrorType::InvalidValue,
        })?;
        
        let mut metadata = HashMap::new();
        metadata.insert("create_revision".to_string(), kv.create_revision().to_string());
        metadata.insert("mod_revision".to_string(), kv.mod_revision().to_string());
        metadata.insert("version".to_string(), kv.version().to_string());
        
        Ok(ConfigValue {
            value,
            version: kv.mod_revision() as u64,
            last_modified: SystemTime::now(), // Etcd没有提供最后修改时间
            metadata,
        })
    }
}

impl ConfigProvider for EtcdConfigProvider {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn get(&self, key: &str) -> Result<Option<ConfigValue>, ConfigError> {
        // 使用tokio运行时执行异步操作
        let runtime = tokio::runtime::Runtime::new().unwrap();
        
        runtime.block_on(async {
            match self.client.get(key, None).await {
                Ok(response) => {
                    if let Some(kv) = response.kvs().first() {
                        Ok(Some(self.config_value_from_kv(kv.clone())?))
                    } else {
                        Ok(None)
                    }
                },
                Err(err) => {
                    Err(ConfigError {
                        message: format!("从Etcd获取配置失败: {}", err),
                        error_type: ConfigErrorType::ConnectionFailed,
                    })
                }
            }
        })
    }
    
    fn set(&self, key: &str, value: ConfigValue) -> Result<(), ConfigError> {
        // 使用tokio运行时执行异步操作
        let runtime = tokio::runtime::Runtime::new().unwrap();
        
        let value_str = serde_json::to_string(&value.value).map_err(|err| ConfigError {
            message: format!("序列化配置值失败: {}", err),
            error_type: ConfigErrorType::InvalidValue,
        })?;
        
        runtime.block_on(async {
            match self.client.put(key, value_str, None).await {
                Ok(_) => Ok(()),
                Err(err) => {
                    Err(ConfigError {
                        message: format!("向Etcd设置配置失败: {}", err),
                        error_type: ConfigErrorType::ConnectionFailed,
                    })
                }
            }
        })
    }
    
    fn delete(&self, key: &str) -> Result<(), ConfigError> {
        // 使用tokio运行时执行异步操作
        let runtime = tokio::runtime::Runtime::new().unwrap();
        
        runtime.block_on(async {
            match self.client.delete(key, None).await {
                Ok(_) => Ok(()),
                Err(err) => {
                    Err(ConfigError {
                        message: format!("从Etcd删除配置失败: {}", err),
                        error_type: ConfigErrorType::ConnectionFailed,
                    })
                }
            }
        })
    }
    
    fn list(&self, prefix: &str) -> Result<Vec<String>, ConfigError> {
        // 使用tokio运行时执行异步操作
        let runtime = tokio::runtime::Runtime::new().unwrap();
        
        runtime.block_on(async {
            let options = etcd_client::GetOptions::new().with_prefix();
            
            match self.client.get(prefix, Some(options)).await {
                Ok(response) => {
                    let keys: Vec<String> = response.kvs()
                        .iter()
                        .map(|kv| String::from_utf8_lossy(kv.key()).to_string())
                        .collect();
                    
                    Ok(keys)
                },
                Err(err) => {
                    Err(ConfigError {
                        message: format!("从Etcd列出配置失败: {}", err),
                        error_type: ConfigErrorType::ConnectionFailed,
                    })
                }
            }
        })
    }
    
    fn watch(&self, key: &str, callback: Box<dyn Fn(&str, &ConfigValue) -> Result<(), ConfigError> + Send + Sync>) -> Result<WatchId, ConfigError> {
        // 使用tokio运行时执行异步操作
        let runtime = tokio::runtime::Runtime::new().unwrap();
        
        let watch_id = WatchId {
            id: uuid::Uuid::new_v4().to_string(),
            provider: self.name.clone(),
            key: key.to_string(),
        };
        
        let watches = self.watches.clone();
        let provider_name = self.name.clone();
        let key_clone = key.to_string();
        let client = self.client.clone();
        let watch_id_clone = watch_id.clone();
        
        // 启动监视线程
        std::thread::spawn(move || {
            runtime.block_on(async {
                let (watcher, mut stream) = match client.watch(key_clone.as_str(), None).await {
                    Ok((watcher, stream)) => (watcher, stream),
                    Err(err) => {
                        eprintln!("创建Etcd监视失败: {}", err);
                        return;
                    }
                };
                
                // 存储监视流
                {
                    let mut watches = watches.lock().unwrap();
                    watches.insert(watch_id_clone.id.clone(), stream);
                }
                
                // 处理监视事件
                while let Some(resp) = watcher.clone().await {
                    match resp {
                        Ok(resp) => {
                            for event in resp.events() {
                                match event.event_type() {
                                    etcd_client::EventType::Put => {
                                        if let Some(kv) = event.kv() {
                                            let config_provider = EtcdConfigProvider {
                                                client: client.clone(),
                                                name: provider_name.clone(),
                                                watches: watches.clone(),
                                            };
                                            
                                            if let Ok(config_value) = config_provider.config_value_from_kv(kv.clone()) {
                                                let key = String::from_utf8_lossy(kv.key()).to_string();
                                                
                                                // 调用回调函数
                                                if let Err(err) = callback(&key, &config_value) {
                                                    eprintln!("调用监视回调失败: {}", err.message);
                                                }
                                            }
                                        }
                                    },
                                    _ => {}
                                }
                            }
                        },
                        Err(err) => {
                            eprintln!("Etcd监视错误: {}", err);
                            break;
                        }
                    }
                }
            });
        });
        
        Ok(watch_id)
    }
    
    fn unwatch(&self, watch_id: &WatchId) -> Result<(), ConfigError> {
        let mut watches = self.watches.lock().unwrap();
        
        if watches.remove(&watch_id.id).is_some() {
            Ok(())
        } else {
            Err(ConfigError {
                message: format!("监视ID '{}' 不存在", watch_id.id),
                error_type: ConfigErrorType::WatchError,
            })
        }
    }
}

// 内存配置提供器
struct InMemoryConfigProvider {
    name: String,
    configs: Arc<RwLock<HashMap<String, ConfigValue>>>,
    watches: Arc<RwLock<HashMap<String, Vec<(WatchId, Box<dyn Fn(&str, &ConfigValue) -> Result<(), ConfigError> + Send + Sync>)>>>>,
}

impl InMemoryConfigProvider {
    fn new(name: &str) -> Self {
        InMemoryConfigProvider {
            name: name.to_string(),
            configs: Arc::new(RwLock::new(HashMap::new())),
            watches: Arc::new(RwLock::new(HashMap::new())),
        }
    }
}

impl ConfigProvider for InMemoryConfigProvider {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn get(&self, key: &str) -> Result<Option<ConfigValue>, ConfigError> {
        let configs = self.configs.read().unwrap();
        Ok(configs.get(key).cloned())
    }
    
    fn set(&self, key: &str, value: ConfigValue) -> Result<(), ConfigError> {
        let mut configs = self.configs.write().unwrap();
        
        // 更新配置
        configs.insert(key.to_string(), value.clone());
        
        // 触发监视回调
        let watches = self.watches.read().unwrap();
        
        if let Some(watchers) = watches.get(key) {
            for (_, callback) in watchers {
                if let Err(err) = callback(key, &value) {
                    eprintln!("调用监视回调失败: {}", err.message);
                }
            }
        }
        
        Ok(())
    }
    
    fn delete(&self, key: &str) -> Result<(), ConfigError> {
        let mut configs = self.configs.write().unwrap();
        configs.remove(key);
        Ok(())
    }
    
    fn list(&self, prefix: &str) -> Result<Vec<String>, ConfigError> {
        let configs = self.configs.read().unwrap();
        
        let keys: Vec<String> = configs.keys()
            .filter(|k| k.starts_with(prefix))
            .cloned()
            .collect();
        
        Ok(keys)
    }
    
    fn watch(&self, key: &str, callback: Box<dyn Fn(&str, &ConfigValue) -> Result<(), ConfigError> + Send + Sync>) -> Result<WatchId, ConfigError> {
        let watch_id = WatchId {
            id: uuid::Uuid::new_v4().to_string(),
            provider: self.name.clone(),
            key: key.to_string(),
        };
        
        let mut watches = self.watches.write().unwrap();
        let watchers = watches.entry(key.to_string()).or_insert_with(Vec::new);
        
        watchers.push((watch_id.clone(), callback));
        
        Ok(watch_id)
    }
    
    fn unwatch(&self, watch_id: &WatchId) -> Result<(), ConfigError> {
        let mut watches = self.watches.write().unwrap();
        
        if let Some(watchers) = watches.get_mut(&watch_id.key) {
            watchers.retain(|(id, _)| id.id != watch_id.id);
            
            if watchers.is_empty() {
                watches.remove(&watch_id.key);
            }
            
            Ok(())
        } else {
            Err(ConfigError {
                message: format!("键 '{}' 没有监视器", watch_id.key),
                error_type: ConfigErrorType::WatchError,
            })
        }
    }
}

// 分布式服务注册与发现系统
struct ServiceRegistry {
    providers: HashMap<String, Box<dyn ServiceRegistryProvider>>,
    cache: Arc<RwLock<HashMap<String, Vec<ServiceInstance>>>>,
    default_provider: String,
    refresh_interval: Duration,
    running: Arc<AtomicBool>,
}

trait ServiceRegistryProvider: Send + Sync {
    fn name(&self) -> &str;
    fn register(&self, service: &ServiceRegistration) -> Result<(), ServiceError>;
    fn deregister(&self, service_id: &str) -> Result<(), ServiceError>;
    fn renew(&self, service_id: &str) -> Result<(), ServiceError>;
    fn get_service(&self, service_name: &str) -> Result<Vec<ServiceInstance>, ServiceError>;
    fn get_services(&self) -> Result<Vec<String>, ServiceError>;
    fn watch(&self, service_name: &str, callback: Box<dyn Fn(&str, &Vec<ServiceInstance>) -> Result<(), ServiceError> + Send + Sync>) -> Result<WatchId, ServiceError>;
    fn unwatch(&self, watch_id: &WatchId) -> Result<(), ServiceError>;
}

struct ServiceRegistration {
    id: String,
    name: String,
    address: String,
    port: u16,
    tags: Vec<String>,
    metadata: HashMap<String, String>,
    health_check: Option<HealthCheck>,
    ttl: Option<Duration>,
}

#[derive(Clone, Debug)]
struct ServiceInstance {
    id: String,
    name: String,
    address: String,
    port: u16,
    tags: Vec<String>,
    metadata: HashMap<String, String>,
    health_status: HealthStatus,
    last_updated: SystemTime,
}

struct HealthCheck {
    check_type: HealthCheckType,
    interval: Duration,
    timeout: Duration,
    deregister_after: Option<Duration>,
    http_path: Option<String>,
    tcp_port: Option<u16>,
    command: Option<String>,
    args: Vec<String>,
}

enum HealthCheckType {
    HTTP,
    TCP,
    Command,
    TTL,
}

#[derive(Clone, Debug, PartialEq)]
enum HealthStatus {
    Passing,
    Warning,
    Critical,
    Unknown,
}

struct ServiceError {
    message: String,
    error_type: ServiceErrorType,
}

enum ServiceErrorType {
    ServiceNotFound,
    RegistrationFailed,
    DeregistrationFailed,
    RenewalFailed,
    ConnectionFailed,
    WatchError,
    InternalError,
}

impl ServiceRegistry {
    fn new(default_provider: &str, refresh_interval: Duration) -> Self {
        ServiceRegistry {
            providers: HashMap::new(),
            cache: Arc::new(RwLock::new(HashMap::new())),
            default_provider: default_provider.to_string(),
            refresh_interval,
            running: Arc::new(AtomicBool::new(false)),
        }
    }
    
    fn register_provider(&mut self, provider: Box<dyn ServiceRegistryProvider>) -> Result<(), String> {
        let name = provider.name().to_string();
        
        if self.providers.contains_key(&name) {
            return Err(format!("服务注册提供器 '{}' 已经注册", name));
        }
        
        self.providers.insert(name, provider);
        Ok(())
    }
    
    fn set_default_provider(&mut self, provider_name: &str) -> Result<(), String> {
        if !self.providers.contains_key(provider_name) {
            return Err(format!("服务注册提供器 '{}' 未注册", provider_name));
        }
        
        self.default_provider = provider_name.to_string();
        Ok(())
    }
    
    fn start(&self) -> Result<(), String> {
        if self.running.load(Ordering::SeqCst) {
            return Err("服务注册系统已经在运行".to_string());
        }
        
        self.running.store(true, Ordering::SeqCst);
        
        // 启动刷新缓存的线程
        let cache = self.cache.clone();
        let providers = self.providers.clone();
        let refresh_interval = self.refresh_interval;
        let running = self.running.clone();
        
        std::thread::spawn(move || {
            while running.load(Ordering::SeqCst) {
                // 获取所有服务名称
                let mut service_names = HashSet::new();
                
                for provider in providers.values() {
                    if let Ok(names) = provider.get_services() {
                        for name in names {
                            service_names.insert(name);
                        }
                    }
                }
                
                // 刷新每个服务的实例列表
                for service_name in service_names {
                    for provider in providers.values() {
                        if let Ok(instances) = provider.get_service(&service_name) {
                            let mut cache_lock = cache.write().unwrap();
                            cache_lock.insert(service_name.clone(), instances);
                            break;
                        }
                    }
                }
                
                // 等待下一个刷新周期
                std::thread::sleep(refresh_interval);
            }
        });
        
        Ok(())
    }
    
    fn stop(&self) {
        self.running.store(false, Ordering::SeqCst);
    }
    
    fn register(&self, service: &ServiceRegistration) -> Result<(), ServiceError> {
        self.register_with_provider(service, &self.default_provider)
    }
    
    fn register_with_provider(&self, service: &ServiceRegistration, provider_name: &str) -> Result<(), ServiceError> {
        let provider = self.providers.get(provider_name).ok_or_else(|| ServiceError {
            message: format!("服务注册提供器 '{}' 未注册", provider_name),
            error_type: ServiceErrorType::InternalError,
        })?;
        
        provider.register(service)
    }
    
    fn deregister(&self, service_id: &str) -> Result<(), ServiceError> {
        self.deregister_with_provider(service_id, &self.default_provider)
    }
    
    fn deregister_with_provider(&self, service_id: &str, provider_name: &str) -> Result<(), ServiceError> {
        let provider = self.providers.get(provider_name).ok_or_else(|| ServiceError {
            message: format!("服务注册提供器 '{}' 未注册", provider_name),
            error_type: ServiceErrorType::InternalError,
        })?;
        
        provider.deregister(service_id)
    }
    
    fn renew(&self, service_id: &str) -> Result<(), ServiceError> {
        self.renew_with_provider(service_id, &self.default_provider)
    }
    
    fn renew_with_provider(&self, service_id: &str, provider_name: &str) -> Result<(), ServiceError> {
        let provider = self.providers.get(provider_name).ok_or_else(|| ServiceError {
            message: format!("服务注册提供器 '{}' 未注册", provider_name),
            error_type: ServiceErrorType::InternalError,
        })?;
        
        provider.renew(service_id)
    }
    
    fn get_service(&self, service_name: &str) -> Result<Vec<ServiceInstance>, ServiceError> {
        // 先从缓存中查找
        {
            let cache = self.cache.read().unwrap();
            
            if let Some(instances) = cache.get(service_name) {
                if !instances.is_empty() {
                    return Ok(instances.clone());
                }
            }
        }
        
        // 从提供器中获取
        self.get_service_from_provider(service_name, &self.default_provider)
    }
    
    fn get_service_from_provider(&self, service_name: &str, provider_name: &str) -> Result<Vec<ServiceInstance>, ServiceError> {
        let provider = self.providers.get(provider_name).ok_or_else(|| ServiceError {
            message: format!("服务注册提供器 '{}' 未注册", provider_name),
            error_type: ServiceErrorType::InternalError,
        })?;
        
        let instances = provider.get_service(service_name)?;
        
        // 更新缓存
        {
            let mut cache = self.cache.write().unwrap();
            cache.insert(service_name.to_string(), instances.clone());
        }
        
        Ok(instances)
    }
    
    fn get_services(&self) -> Result<Vec<String>, ServiceError> {
        self.get_services_from_provider(&self.default_provider)
    }
    
    fn get_services_from_provider(&self, provider_name: &str) -> Result<Vec<String>, ServiceError> {
        let provider = self.providers.get(provider_name).ok_or_else(|| ServiceError {
            message: format!("服务注册提供器 '{}' 未注册", provider_name),
            error_type: ServiceErrorType::InternalError,
        })?;
        
        provider.get_services()
    }
    
    fn watch(&self, service_name: &str, callback: Box<dyn Fn(&str, &Vec<ServiceInstance>) -> Result<(), ServiceError> + Send + Sync>) -> Result<WatchId, ServiceError> {
        self.watch_with_provider(service_name, callback, &self.default_provider)
    }
    
    fn watch_with_provider(
        &self,
        service_name: &str,
        callback: Box<dyn Fn(&str, &Vec<ServiceInstance>) -> Result<(), ServiceError> + Send + Sync>,
        provider_name: &str
    ) -> Result<WatchId, ServiceError> {
        let provider = self.providers.get(provider_name).ok_or_else(|| ServiceError {
            message: format!("服务注册提供器 '{}' 未注册", provider_name),
            error_type: ServiceErrorType::InternalError,
        })?;
        
        provider.watch(service_name, callback)
    }
    
    fn unwatch(&self, watch_id: &WatchId) -> Result<(), ServiceError> {
        let provider = self.providers.get(&watch_id.provider).ok_or_else(|| ServiceError {
            message: format!("服务注册提供器 '{}' 未注册", watch_id.provider),
            error_type: ServiceErrorType::InternalError,
        })?;
        
        provider.unwatch(watch_id)
    }
}

// Consul服务注册提供器
struct ConsulServiceRegistryProvider {
    client: reqwest::Client,
    base_url: String,
    name: String,
    watches: Arc<Mutex<HashMap<String, JoinHandle<()>>>>,
}

impl ConsulServiceRegistryProvider {
    fn new(base_url: &str, name: &str) -> Self {
        ConsulServiceRegistryProvider {
            client: reqwest::Client::new(),
            base_url: base_url.to_string(),
            name: name.to_string(),
            watches: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    fn service_instance_from_json(&self, json: &serde_json::Value) -> Result<ServiceInstance, ServiceError> {
        let id = json["ServiceID"].as_str().ok_or_else(|| ServiceError {
            message: "服务实例缺少ID".to_string(),
            error_type: ServiceErrorType::InternalError,
        })?.to_string();
        
        let name = json["ServiceName"].as_str().ok_or_else(|| ServiceError {
            message: "服务实例缺少名称".to_string(),
            error_type: ServiceErrorType::InternalError,
        })?.to_string();
        
        let address = json["ServiceAddress"].as_str().ok_or_else(|| ServiceError {
            message: "服务实例缺少地址".to_string(),
            error_type: ServiceErrorType::InternalError,
        })?.to_string();
        
        let port = json["ServicePort"].as_u64().ok_or_else(|| ServiceError {
            message: "服务实例缺少端口".to_string(),
            error_type: ServiceErrorType::InternalError,
        })? as u16;
        
        let mut tags = Vec::new();
        if let Some(tags_array) = json["ServiceTags"].as_array() {
            for tag in tags_array {
                if let Some(tag_str) = tag.as_str() {
                    tags.push(tag_str.to_string());
                }
            }
        }
        
        let mut metadata = HashMap::new();
        if let Some(meta_obj) = json["ServiceMeta"].as_object() {
            for (key, value) in meta_obj {
                if let Some(value_str) = value.as_str() {
                    metadata.insert(key.clone(), value_str.to_string());
                }
            }
        }
        
        let health_status = if let Some(checks) = json["Checks"].as_array() {
            let mut status = HealthStatus::Passing;
            
            for check in checks {
                if let Some(check_status) = check["Status"].as_str() {
                    match check_status {
                        "critical" => {
                            status = HealthStatus::Critical;
                            break;
                        },
                        "warning" => {
                            if status == HealthStatus::Passing {
                                status = HealthStatus::Warning;
                            }
                        },
                        _ => {}
                    }
                }
            }
            
            status
        } else {
            HealthStatus::Unknown
        };
        
        Ok(ServiceInstance {
            id,
            name,
            address,
            port,
            tags,
            metadata,
            health_status,
            last_updated: SystemTime::now(),
        })
    }
}

impl ServiceRegistryProvider for ConsulServiceRegistryProvider {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn register(&self, service: &ServiceRegistration) -> Result<(), ServiceError> {
        let url = format!("{}/v1/agent/service/register", self.base_url);
        
        let mut registration = serde_json::Map::new();
        registration.insert("ID".to_string(), serde_json::Value::String(service.id.clone()));
        registration.insert("Name".to_string(), serde_json::Value::String(service.name.clone()));
        registration.insert("Address".to_string(), serde_json::Value::String(service.address.clone()));
        registration.insert("Port".to_string(), serde_json::Value::Number(serde_json::Number::from(service.port)));
        
        if !service.tags.is_empty() {
            let tags = serde_json::Value::Array(
                service.tags.iter()
                    .map(|tag| serde_json::Value::String(tag.clone()))
                    .collect()
            );
            registration.insert("Tags".to_string(), tags);
        }
        
        if !service.metadata.is_empty() {
            let mut meta = serde_json::Map::new();
            for (key, value) in &service.metadata {
                meta.insert(key.clone(), serde_json::Value::String(value.clone()));
            }
            registration.insert("Meta".to_string(), serde_json::Value::Object(meta));
        }
        
        if let Some(health_check) = &service.health_check {
            let mut check = serde_json::Map::new();
            
            match health_check.check_type {
                HealthCheckType::HTTP => {
                    if let Some(path) = &health_check.http_path {
                        let http_url = format!("http://{}:{}{}", service.address, service.port, path);
                        check.insert("HTTP".to_string(), serde_json::Value::String(http_url));
                    }
                },
                HealthCheckType::TCP => {
                    if let Some(port) = health_check.tcp_port {
                        let address = format!("{}:{}", service.address, port);
                        check.insert("TCP".to_string(), serde_json::Value::String(address));
                    }
                },
                HealthCheckType::Command => {
                    if let Some(cmd) = &health_check.command {
                        check.insert("Args".to_string(), serde_json::Value::Array(
                            std::iter::once(serde_json::Value::String(cmd.clone()))
                                .chain(health_check.args.iter().map(|arg| serde_json::Value::String(arg.clone())))
                                .collect()
                        ));
                    }
                },
                HealthCheckType::TTL => {
                    if let Some(ttl) = service.ttl {
                        let ttl_str = format!("{}s", ttl.as_secs());
                        check.insert("TTL".to_string(), serde_json::Value::String(ttl_str));
                    }
                },
            }
            
            let interval_str = format!("{}s", health_check.interval.as_secs());
            check.insert("Interval".to_string(), serde_json::Value::String(interval_str));
            
            let timeout_str = format!("{}s", health_check.timeout.as_secs());
            check.insert("Timeout".to_string(), serde_json::Value::String(timeout_str));
            
            if let Some(deregister_after) = health_check.deregister_after {
                let deregister_str = format!("{}s", deregister_after.as_secs());
                check.insert("DeregisterCriticalServiceAfter".to_string(), serde_json::Value::String(deregister_str));
            }
            
            registration.insert("Check".to_string(), serde_json::Value::Object(check));
        }
        
        let registration_json = serde_json::Value::Object(registration);
        
        match self.client.put(&url)
            .json(&registration_json)
            .send() {
            Ok(response) => {
                if response.status().is_success() {
                    Ok(())
                } else {
                    Err(ServiceError {
                        message: format!("注册服务失败: HTTP {}", response.status()),
                        error_type: ServiceErrorType::RegistrationFailed,
                    })
                }
            },
            Err(err) => {
                Err(ServiceError {
                    message: format!("注册服务失败: {}", err),
                    error_type: ServiceErrorType::ConnectionFailed,
                })
            }
        }
    }
    
    fn deregister(&self, service_id: &str) -> Result<(), ServiceError> {
        let url = format!("{}/v1/agent/service/deregister/{}", self.base_url, service_id);
        
        match self.client.put(&url).send() {
            Ok(response) => {
                if response.status().is_success() {
                    Ok(())
                } else {
                    Err(ServiceError {
                        message: format!("注销服务失败: HTTP {}", response.status()),
                        error_type: ServiceErrorType::DeregistrationFailed,
                    })
                }
            },
            Err(err) => {
                Err(ServiceError {
                    message: format!("注销服务失败: {}", err),
                    error_type: ServiceErrorType::ConnectionFailed,
                })
            }
        }
    }
    
    fn renew(&self, service_id: &str) -> Result<(), ServiceError> {
        let url = format!("{}/v1/agent/check/pass/service:{}", self.base_url, service_id);
        
        match self.client.put(&url).send() {
            Ok(response) => {
                if response.status().is_success() {
                    Ok(())
                } else {
                    Err(ServiceError {
                        message: format!("续约服务失败: HTTP {}", response.status()),
                        error_type: ServiceErrorType::RenewalFailed,
                    })
                }
            },
            Err(err) => {
                Err(ServiceError {
                    message: format!("续约服务失败: {}", err),
                    error_type: ServiceErrorType::ConnectionFailed,
                })
            }
        }
    }
    
    fn get_service(&self, service_name: &str) -> Result<Vec<ServiceInstance>, ServiceError> {
        let url = format!("{}/v1/health/service/{}", self.base_url, service_name);
        
        match self.client.get(&url).query(&[("passing", "true")]).send() {
            Ok(response) => {
                if response.status().is_success() {
                    let json: serde_json::Value = response.json().map_err(|err| ServiceError {
                        message: format!("解析响应失败: {}", err),
                        error_type: ServiceErrorType::InternalError,
                    })?;
                    
                    if let Some(services) = json.as_array() {
                        let mut instances = Vec::new();
                        
                        for service in services {
                            let instance = self.service_instance_from_json(service)?;
                            instances.push(instance);
                        }
                        
                        Ok(instances)
                    } else {
                        Ok(Vec::new())
                    }
                } else {
                    Err(ServiceError {
                        message: format!("获取服务失败: HTTP {}", response.status()),
                        error_type: ServiceErrorType::ServiceNotFound,
                    })
                }
            },
            Err(err) => {
                Err(ServiceError {
                    message: format!("获取服务失败: {}", err),
                    error_type: ServiceErrorType::ConnectionFailed,
                })
            }
        }
    }
    
    fn get_services(&self) -> Result<Vec<String>, ServiceError> {
        let url = format!("{}/v1/catalog/services", self.base_url);
        
        match self.client.get(&url).send() {
            Ok(response) => {
                if response.status().is_success() {
                    let json: serde_json::Value = response.json().map_err(|err| ServiceError {
                        message: format!("解析响应失败: {}", err),
                        error_type: ServiceErrorType::InternalError,
                    })?;
                    
                    if let Some(services) = json.as_object() {
                        Ok(services.keys().cloned().collect())
                    } else {
                        Ok(Vec::new())
                    }
                } else {
                    Err(ServiceError {
                        message: format!("获取服务列表失败: HTTP {}", response.status()),
                        error_type: ServiceErrorType::ServiceNotFound,
                    })
                }
            },
            Err(err) => {
                Err(ServiceError {
                    message: format!("获取服务列表失败: {}", err),
                    error_type: ServiceErrorType::ConnectionFailed,
                })
            }
        }
    }
    
    fn watch(&self, service_name: &str, callback: Box<dyn Fn(&str, &Vec<ServiceInstance>) -> Result<(), ServiceError> + Send + Sync>) -> Result<WatchId, ServiceError> {
        let watch_id = WatchId {
            id: uuid::Uuid::new_v4().to_string(),
            provider: self.name.clone(),
            key: service_name.to_string(),
        };
        
        let client = self.client.clone();
        let base_url = self.base_url.clone();
        let service_name_clone = service_name.to_string();
        let provider_clone = self.clone();
        
        // 启动监视线程
        let watch_thread = std::thread::spawn(move || {
            let mut last_index = 0;
            
            loop {
                let url = format!("{}/v1/health/service/{}", base_url, service_name_clone);
                
                let response = match client.get(&url)
                    .query(&[("passing", "true"), ("index", &last_index.to_string()), ("wait", "5m")])
                    .send() {
                    Ok(resp) => resp,
                    Err(err) => {
                        eprintln!("监视服务失败: {}", err);
                        std::thread::sleep(Duration::from_secs(5));
                        continue;
                    }
                };
                
                if let Some(index_header) = response.headers().get("X-Consul-Index") {
                    if let Ok(index_str) = index_header.to_str() {
                        if let Ok(index) = index_str.parse::<u64>() {
                            if index != last_index {
                                last_index = index;
                                
                                // 解析响应
                                match response.json::<serde_json::Value>() {
                                    Ok(json) => {
                                        if let Some(services) = json.as_array() {
                                            let mut instances = Vec::new();
                                            
                                            for service in services {
                                                match provider_clone.service_instance_from_json(service) {
                                                    Ok(instance) => instances.push(instance),
                                                    Err(err) => {
                                                        eprintln!("解析服务实例失败: {}", err.message);
                                                    }
                                                }
                                            }
                                            
                                            // 调用回调函数
                                            if let Err(err) = callback(&service_name_clone, &instances) {
                                                eprintln!("调用监视回调失败: {}", err.message);
                                            }
                                        }
                                    },
                                    Err(err) => {
                                        eprintln!("解析响应失败: {}", err);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        });
        
        // 存储监视线程
        let mut watches = self.watches.lock().unwrap();
        watches.insert(watch_id.id.clone(), watch_thread);
        
        Ok(watch_id)
    }
    
    fn unwatch(&self, watch_id: &WatchId) -> Result<(), ServiceError> {
        let mut watches = self.watches.lock().unwrap();
        
        if let Some(handle) = watches.remove(&watch_id.id) {
            // 在实际实现中，我们应该有一种机制来通知线程停止
            // 由于Rust线程没有内置的取消机制，这里简化处理
            
            Ok(())
        } else {
            Err(ServiceError {
                message: format!("监视ID '{}' 不存在", watch_id.id),
                error_type: ServiceErrorType::WatchError,
            })
        }
    }
}

// 内存服务注册提供器
struct InMemoryServiceRegistryProvider {
    name: String,
    services: Arc<RwLock<HashMap<String, Vec<ServiceInstance>>>>,
    watches: Arc<RwLock<HashMap<String, Vec<(WatchId, Box<dyn Fn(&str, &Vec<ServiceInstance>) -> Result<(), ServiceError> + Send + Sync>)>>>>,
}

impl InMemoryServiceRegistryProvider {
    fn new(name: &str) -> Self {
        InMemoryServiceRegistryProvider {
            name: name.to_string(),
            services: Arc::new(RwLock::new(HashMap::new())),
            watches: Arc::new(RwLock::new(HashMap::new())),
        }
    }
}

impl ServiceRegistryProvider for InMemoryServiceRegistryProvider {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn register(&self, service: &ServiceRegistration) -> Result<(), ServiceError> {
        let mut services = self.services.write().unwrap();
        
        // 创建服务实例
        let instance = ServiceInstance {
            id: service.id.clone(),
            name: service.name.clone(),
            address: service.address.clone(),
            port: service.port,
            tags: service.tags.clone(),
            metadata: service.metadata.clone(),
            health_status: HealthStatus::Passing,
            last_updated: SystemTime::now(),
        };
        
        // 获取或创建服务实例列表
        let instances = services.entry(service.name.clone()).or_insert_with(Vec::new);
        
        // 检查是否已存在
        let existing_index = instances.iter().position(|i| i.id == service.id);
        
        if let Some(index) = existing_index {
            // 更新现有实例
            instances[index] = instance;
        } else {
            // 添加新实例
            instances.push(instance);
        }
        
        // 触发监视回调
        let watches = self.watches.read().unwrap();
        
        if let Some(watchers) = watches.get(&service.name) {
            let instances = services.get(&service.name).unwrap();
            
            for (_, callback) in watchers {
                if let Err(err) = callback(&service.name, instances) {
                    eprintln!("调用监视回调失败: {}", err.message);
                }
            }
        }
        
        Ok(())
    }
    
    fn deregister(&self, service_id: &str) -> Result<(), ServiceError> {
        let mut services = self.services.write().unwrap();
        
        // 查找服务实例
        let mut service_name = None;
        
        for (name, instances) in services.iter_mut() {
            let before_len = instances.len();
            instances.retain(|i| i.id != service_id);
            
            if instances.len() < before_len {
                service_name = Some(name.clone());
                break;
            }
        }
        
        if let Some(name) = service_name {
            // 触发监视回调
            let watches = self.watches.read().unwrap();
            
            if let Some(watchers) = watches.get(&name) {
                let instances = services.get(&name).unwrap();
                
                for (_, callback) in watchers {
                    if let Err(err) = callback(&name, instances) {
                        eprintln!("调用监视回调失败: {}", err.message);
                    }
                }
            }
            
            Ok(())
        } else {
            Err(ServiceError {
                message: format!("服务ID '{}' 不存在", service_id),
                error_type: ServiceErrorType::ServiceNotFound,
            })
        }
    }
    
    fn renew(&self, service_id: &str) -> Result<(), ServiceError> {
        let mut services = self.services.write().unwrap();
        
        // 查找并更新服务实例
        for (_, instances) in services.iter_mut() {
            for instance in instances.iter_mut() {
                if instance.id == service_id {
                    instance.last_updated = SystemTime::now();
                    return Ok(());
                }
            }
        }
        
        Err(ServiceError {
            message: format!("服务ID '{}' 不存在", service_id),
            error_type: ServiceErrorType::ServiceNotFound,
        })
    }
    
    fn get_service(&self, service_name: &str) -> Result<Vec<ServiceInstance>, ServiceError> {
        let services = self.services.read().unwrap();
        
        if let Some(instances) = services.get(service_name) {
            Ok(instances.clone())
        } else {
            Ok(Vec::new())
        }
    }
    
    fn get_services(&self) -> Result<Vec<String>, ServiceError> {
        let services = self.services.read().unwrap();
        Ok(services.keys().cloned().collect())
    }
    
    fn watch(&self, service_name: &str, callback: Box<dyn Fn(&str, &Vec<ServiceInstance>) -> Result<(), ServiceError> + Send + Sync>) -> Result<WatchId, ServiceError> {
        let watch_id = WatchId {
            id: uuid::Uuid::new_v4().to_string(),
            provider: self.name.clone(),
            key: service_name.to_string(),
        };
        
        let mut watches = self.watches.write().unwrap();
        let watchers = watches.entry(service_name.to_string()).or_insert_with(Vec::new);
        
        watchers.push((watch_id.clone(), callback));
        
        // 立即调用回调一次
        let services = self.services.read().unwrap();
        
        if let Some(instances) = services.get(service_name) {
            let callback = &watchers.last().unwrap().1;
            if let Err(err) = callback(service_name, instances) {
                eprintln!("调用监视回调失败: {}", err.message);
            }
        }
        
        Ok(watch_id)
    }
    
    fn unwatch(&self, watch_id: &WatchId) -> Result<(), ServiceError> {
        let mut watches = self.watches.write().unwrap();
        
        if let Some(watchers) = watches.get_mut(&watch_id.key) {
            watchers.retain(|(id, _)| id.id != watch_id.id);
            
            if watchers.is_empty() {
                watches.remove(&watch_id.key);
            }
            
            Ok(())
        } else {
            Err(ServiceError {
                message: format!("服务 '{}' 没有监视器", watch_id.key),
                error_type: ServiceErrorType::WatchError,
            })
        }
    }
}

// 简单的服务注册客户端
struct ServiceRegistrationClient {
    registry: Arc<ServiceRegistry>,
    registrations: Vec<ServiceRegistration>,
    provider: String,
    heartbeat_interval: Duration,
    running: Arc<AtomicBool>,
}

impl ServiceRegistrationClient {
    fn new(registry: Arc<ServiceRegistry>, provider: &str, heartbeat_interval: Duration) -> Self {
        ServiceRegistrationClient {
            registry,
            registrations: Vec::new(),
            provider: provider.to_string(),
            heartbeat_interval,
            running: Arc::new(AtomicBool::new(false)),
        }
    }
    
    fn register_service(&mut self, service: ServiceRegistration) -> Result<(), ServiceError> {
        self.registry.register_with_provider(&service, &self.provider)?;
        self.registrations.push(service);
        Ok(())
    }
    
    fn start_heartbeat(&self) -> Result<(), String> {
        if self.running.load(Ordering::SeqCst) {
            return Err("心跳已经在运行".to_string());
        }
        
        self.running.store(true, Ordering::SeqCst);
        
        let registry = self.registry.clone();
        let registrations = self.registrations.clone();
        let provider = self.provider.clone();
        let heartbeat_interval = self.heartbeat_interval;
        let running = self.running.clone();
        
        std::thread::spawn(move || {
            while running.load(Ordering::SeqCst) {
                for service in &registrations {
                    if let Err(err) = registry.renew_with_provider(&service.id, &provider) {
                        eprintln!("服务续约失败: {}", err.message);
                    }
                }
                
                std::thread::sleep(heartbeat_interval);
            }
        });
        
        Ok(())
    }
    
    fn stop_heartbeat(&self) {
        self.running.store(false, Ordering::SeqCst);
    }
    
    fn deregister_all(&self) -> Result<(), ServiceError> {
        for service in &self.registrations {
            if let Err(err) = self.registry.deregister_with_provider(&service.id, &self.provider) {
                eprintln!("注销服务失败: {}", err.message);
            }
        }
        
        Ok(())
    }
}

// 简单的服务发现客户端
struct ServiceDiscoveryClient {
    registry: Arc<ServiceRegistry>,
    provider: String,
    local_cache: HashMap<String, Vec<ServiceInstance>>,
    load_balancers: HashMap<String, Box<dyn LoadBalancer>>,
}

trait LoadBalancer: Send + Sync {
    fn name(&self) -> &str;
    fn select(&self, instances: &[ServiceInstance]) -> Option<ServiceInstance>;
}

struct RoundRobinLoadBalancer {
    name: String,
    counters: HashMap<String, usize>,
}

impl RoundRobinLoadBalancer {
    fn new(name: &str) -> Self {
        RoundRobinLoadBalancer {
            name: name.to_string(),
            counters: HashMap::new(),
        }
    }
}

impl LoadBalancer for RoundRobinLoadBalancer {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn select(&self, instances: &[ServiceInstance]) -> Option<ServiceInstance> {
        if instances.is_empty

```rust
() {
            return None;
        }
        
        let mut counter = self.counters.clone();
        let service_name = &instances[0].name;
        let current = *counter.get(service_name).unwrap_or(&0);
        let next = (current + 1) % instances.len();
        
        counter.insert(service_name.clone(), next);
        self.counters = counter;
        
        Some(instances[current].clone())
    }
}

struct RandomLoadBalancer {
    name: String,
}

impl RandomLoadBalancer {
    fn new(name: &str) -> Self {
        RandomLoadBalancer {
            name: name.to_string(),
        }
    }
}

impl LoadBalancer for RandomLoadBalancer {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn select(&self, instances: &[ServiceInstance]) -> Option<ServiceInstance> {
        if instances.is_empty() {
            return None;
        }
        
        let mut rng = rand::thread_rng();
        let index = rng.gen_range(0..instances.len());
        
        Some(instances[index].clone())
    }
}

impl ServiceDiscoveryClient {
    fn new(registry: Arc<ServiceRegistry>, provider: &str) -> Self {
        ServiceDiscoveryClient {
            registry,
            provider: provider.to_string(),
            local_cache: HashMap::new(),
            load_balancers: HashMap::new(),
        }
    }
    
    fn register_load_balancer(&mut self, service_name: &str, load_balancer: Box<dyn LoadBalancer>) {
        self.load_balancers.insert(service_name.to_string(), load_balancer);
    }
    
    fn discover_service(&mut self, service_name: &str) -> Result<Vec<ServiceInstance>, ServiceError> {
        match self.registry.get_service_from_provider(service_name, &self.provider) {
            Ok(instances) => {
                self.local_cache.insert(service_name.to_string(), instances.clone());
                Ok(instances)
            },
            Err(err) => {
                // 如果远程查询失败，尝试使用本地缓存
                if let Some(cached_instances) = self.local_cache.get(service_name) {
                    Ok(cached_instances.clone())
                } else {
                    Err(err)
                }
            }
        }
    }
    
    fn select_service(&mut self, service_name: &str) -> Result<ServiceInstance, ServiceError> {
        // 发现服务实例
        let instances = self.discover_service(service_name)?;
        
        if instances.is_empty() {
            return Err(ServiceError {
                message: format!("服务 '{}' 没有可用实例", service_name),
                error_type: ServiceErrorType::ServiceNotFound,
            });
        }
        
        // 使用负载均衡器选择实例
        if let Some(lb) = self.load_balancers.get_mut(service_name) {
            if let Some(instance) = lb.select(&instances) {
                return Ok(instance);
            }
        }
        
        // 默认使用第一个实例
        Ok(instances[0].clone())
    }
    
    fn watch_service(&self, service_name: &str, callback: Box<dyn Fn(&str, &Vec<ServiceInstance>) -> Result<(), ServiceError> + Send + Sync>) -> Result<WatchId, ServiceError> {
        self.registry.watch_with_provider(service_name, callback, &self.provider)
    }
}

// 服务网关集成示例
struct ServiceGateway {
    discovery_client: Arc<Mutex<ServiceDiscoveryClient>>,
    router: Router,
    client: reqwest::Client,
}

struct Router {
    routes: HashMap<String, RouteConfig>,
}

struct RouteConfig {
    path: String,
    service_name: String,
    strip_prefix: bool,
    timeout: Duration,
    retry_count: usize,
}

impl ServiceGateway {
    fn new(discovery_client: ServiceDiscoveryClient) -> Self {
        ServiceGateway {
            discovery_client: Arc::new(Mutex::new(discovery_client)),
            router: Router {
                routes: HashMap::new(),
            },
            client: reqwest::Client::new(),
        }
    }
    
    fn add_route(&mut self, path: &str, service_name: &str, strip_prefix: bool, timeout: Duration, retry_count: usize) {
        let route = RouteConfig {
            path: path.to_string(),
            service_name: service_name.to_string(),
            strip_prefix,
            timeout,
            retry_count,
        };
        
        self.router.routes.insert(path.to_string(), route);
    }
    
    fn handle_request(&self, path: &str, method: &str, headers: HashMap<String, String>, body: Vec<u8>) -> Result<(u16, HashMap<String, String>, Vec<u8>), String> {
        // 查找路由
        let route = self.find_route(path).ok_or_else(|| format!("找不到路由: {}", path))?;
        
        // 发现服务
        let mut discovery_client = self.discovery_client.lock().unwrap();
        let service_instance = discovery_client.select_service(&route.service_name)
            .map_err(|err| format!("选择服务实例失败: {}", err.message))?;
        
        // 构建目标URL
        let target_path = if route.strip_prefix {
            path.strip_prefix(&route.path).unwrap_or(path)
        } else {
            path
        };
        
        let target_url = format!("http://{}:{}{}", service_instance.address, service_instance.port, target_path);
        
        // 发送请求
        let mut retry_count = 0;
        let max_retries = route.retry_count;
        
        loop {
            match self.forward_request(&target_url, method, &headers, &body) {
                Ok(response) => return Ok(response),
                Err(err) => {
                    if retry_count >= max_retries {
                        return Err(format!("转发请求失败: {}", err));
                    }
                    
                    retry_count += 1;
                    std::thread::sleep(Duration::from_millis(100 * 2u64.pow(retry_count as u32)));
                }
            }
        }
    }
    
    fn find_route(&self, path: &str) -> Option<&RouteConfig> {
        self.router.routes.iter()
            .filter(|(route_path, _)| path.starts_with(*route_path))
            .max_by_key(|(route_path, _)| route_path.len())
            .map(|(_, route)| route)
    }
    
    fn forward_request(&self, url: &str, method: &str, headers: &HashMap<String, String>, body: &[u8]) -> Result<(u16, HashMap<String, String>, Vec<u8>), reqwest::Error> {
        let mut request_builder = match method {
            "GET" => self.client.get(url),
            "POST" => self.client.post(url),
            "PUT" => self.client.put(url),
            "DELETE" => self.client.delete(url),
            "PATCH" => self.client.patch(url),
            "HEAD" => self.client.head(url),
            _ => self.client.get(url),
        };
        
        for (key, value) in headers {
            request_builder = request_builder.header(key, value);
        }
        
        if !body.is_empty() {
            request_builder = request_builder.body(body.to_vec());
        }
        
        let response = request_builder.send()?;
        
        let status = response.status().as_u16();
        
        let response_headers = response.headers().iter()
            .map(|(name, value)| (name.to_string(), value.to_str().unwrap_or("").to_string()))
            .collect();
        
        let response_body = response.bytes()?.to_vec();
        
        Ok((status, response_headers, response_body))
    }
}

// 配置系统和服务发现集成示例
struct ApplicationConfig {
    config_system: Arc<DistributedConfigSystem>,
    service_registry: Arc<ServiceRegistry>,
    service_client: Option<ServiceRegistrationClient>,
    discovery_client: ServiceDiscoveryClient,
    application_id: String,
}

impl ApplicationConfig {
    fn new(
        config_system: Arc<DistributedConfigSystem>,
        service_registry: Arc<ServiceRegistry>,
        application_id: &str
    ) -> Self {
        let discovery_client = ServiceDiscoveryClient::new(service_registry.clone(), "default");
        
        ApplicationConfig {
            config_system,
            service_registry,
            service_client: None,
            discovery_client,
            application_id: application_id.to_string(),
        }
    }
    
    fn register_service(&mut self, service_name: &str, port: u16) -> Result<(), String> {
        let hostname = hostname::get()
            .map_err(|e| format!("获取主机名失败: {}", e))?
            .to_string_lossy()
            .to_string();
        
        let id = format!("{}-{}-{}", service_name, hostname, port);
        
        let service = ServiceRegistration {
            id,
            name: service_name.to_string(),
            address: hostname,
            port,
            tags: vec![self.application_id.clone()],
            metadata: HashMap::new(),
            health_check: Some(HealthCheck {
                check_type: HealthCheckType::HTTP,
                interval: Duration::from_secs(10),
                timeout: Duration::from_secs(2),
                deregister_after: Some(Duration::from_secs(60)),
                http_path: Some("/health".to_string()),
                tcp_port: None,
                command: None,
                args: Vec::new(),
            }),
            ttl: None,
        };
        
        let mut service_client = ServiceRegistrationClient::new(
            self.service_registry.clone(),
            "default",
            Duration::from_secs(5)
        );
        
        service_client.register_service(service)
            .map_err(|e| format!("注册服务失败: {}", e.message))?;
        
        service_client.start_heartbeat()
            .map_err(|e| format!("启动心跳失败: {}", e))?;
        
        self.service_client = Some(service_client);
        
        Ok(())
    }
    
    fn get_config<T: serde::de::DeserializeOwned>(&self, key: &str) -> Result<T, String> {
        match self.config_system.get(key) {
            Ok(value) => {
                serde_json::from_value(value.value)
                    .map_err(|e| format!("解析配置失败: {}", e))
            },
            Err(err) => Err(format!("获取配置失败: {}", err.message)),
        }
    }
    
    fn get_service_url(&mut self, service_name: &str) -> Result<String, String> {
        match self.discovery_client.select_service(service_name) {
            Ok(instance) => {
                Ok(format!("http://{}:{}", instance.address, instance.port))
            },
            Err(err) => Err(format!("发现服务失败: {}", err.message)),
        }
    }
    
    fn watch_config<F>(&self, key: &str, callback: F) -> Result<WatchId, String>
    where
        F: Fn(&str, &serde_json::Value) -> Result<(), String> + Send + Sync + 'static,
    {
        let wrapped_callback = Box::new(move |key: &str, value: &ConfigValue| -> Result<(), ConfigError> {
            callback(key, &value.value).map_err(|e| ConfigError {
                message: e,
                error_type: ConfigErrorType::InternalError,
            })
        });
        
        self.config_system.watch(key, wrapped_callback)
            .map_err(|e| format!("监视配置失败: {}", e.message))
    }
    
    fn shutdown(&self) -> Result<(), String> {
        if let Some(client) = &self.service_client {
            client.stop_heartbeat();
            client.deregister_all().map_err(|e| format!("注销服务失败: {}", e.message))?;
        }
        
        self.config_system.stop();
        self.service_registry.stop();
        
        Ok(())
    }
}
```

### 4.12 分布式缓存系统

分布式缓存系统允许在多个节点间共享和管理缓存数据，提高应用性能并减轻数据库负载。

```rust
struct DistributedCacheSystem {
    providers: HashMap<String, Box<dyn CacheProvider>>,
    default_provider: String,
}

trait CacheProvider: Send + Sync {
    fn name(&self) -> &str;
    fn get(&self, key: &str) -> Result<Option<CacheEntry>, CacheError>;
    fn set(&self, key: &str, value: &[u8], ttl: Option<Duration>) -> Result<(), CacheError>;
    fn delete(&self, key: &str) -> Result<bool, CacheError>;
    fn exists(&self, key: &str) -> Result<bool, CacheError>;
    fn increment(&self, key: &str, amount: i64) -> Result<i64, CacheError>;
    fn expire(&self, key: &str, ttl: Duration) -> Result<bool, CacheError>;
    fn flush_all(&self) -> Result<(), CacheError>;
    fn get_stats(&self) -> Result<CacheStats, CacheError>;
}

struct CacheEntry {
    value: Vec<u8>,
    ttl: Option<Duration>,
    created_at: SystemTime,
    last_accessed: SystemTime,
}

struct CacheStats {
    hits: u64,
    misses: u64,
    keys: u64,
    memory_usage: u64,
    uptime: Duration,
}

struct CacheError {
    message: String,
    error_type: CacheErrorType,
}

enum CacheErrorType {
    KeyNotFound,
    ConnectionFailed,
    SerializationError,
    OperationFailed,
    InternalError,
}

impl DistributedCacheSystem {
    fn new(default_provider: &str) -> Self {
        DistributedCacheSystem {
            providers: HashMap::new(),
            default_provider: default_provider.to_string(),
        }
    }
    
    fn register_provider(&mut self, provider: Box<dyn CacheProvider>) -> Result<(), String> {
        let name = provider.name().to_string();
        
        if self.providers.contains_key(&name) {
            return Err(format!("缓存提供器 '{}' 已经注册", name));
        }
        
        self.providers.insert(name, provider);
        Ok(())
    }
    
    fn set_default_provider(&mut self, provider_name: &str) -> Result<(), String> {
        if !self.providers.contains_key(provider_name) {
            return Err(format!("缓存提供器 '{}' 未注册", provider_name));
        }
        
        self.default_provider = provider_name.to_string();
        Ok(())
    }
    
    fn get(&self, key: &str) -> Result<Option<CacheEntry>, CacheError> {
        self.get_from_provider(key, &self.default_provider)
    }
    
    fn get_from_provider(&self, key: &str, provider_name: &str) -> Result<Option<CacheEntry>, CacheError> {
        let provider = self.providers.get(provider_name).ok_or_else(|| CacheError {
            message: format!("缓存提供器 '{}' 未注册", provider_name),
            error_type: CacheErrorType::InternalError,
        })?;
        
        provider.get(key)
    }
    
    fn set(&self, key: &str, value: &[u8], ttl: Option<Duration>) -> Result<(), CacheError> {
        self.set_with_provider(key, value, ttl, &self.default_provider)
    }
    
    fn set_with_provider(&self, key: &str, value: &[u8], ttl: Option<Duration>, provider_name: &str) -> Result<(), CacheError> {
        let provider = self.providers.get(provider_name).ok_or_else(|| CacheError {
            message: format!("缓存提供器 '{}' 未注册", provider_name),
            error_type: CacheErrorType::InternalError,
        })?;
        
        provider.set(key, value, ttl)
    }
    
    fn delete(&self, key: &str) -> Result<bool, CacheError> {
        self.delete_from_provider(key, &self.default_provider)
    }
    
    fn delete_from_provider(&self, key: &str, provider_name: &str) -> Result<bool, CacheError> {
        let provider = self.providers.get(provider_name).ok_or_else(|| CacheError {
            message: format!("缓存提供器 '{}' 未注册", provider_name),
            error_type: CacheErrorType::InternalError,
        })?;
        
        provider.delete(key)
    }
    
    fn exists(&self, key: &str) -> Result<bool, CacheError> {
        self.exists_in_provider(key, &self.default_provider)
    }
    
    fn exists_in_provider(&self, key: &str, provider_name: &str) -> Result<bool, CacheError> {
        let provider = self.providers.get(provider_name).ok_or_else(|| CacheError {
            message: format!("缓存提供器 '{}' 未注册", provider_name),
            error_type: CacheErrorType::InternalError,
        })?;
        
        provider.exists(key)
    }
    
    fn increment(&self, key: &str, amount: i64) -> Result<i64, CacheError> {
        self.increment_in_provider(key, amount, &self.default_provider)
    }
    
    fn increment_in_provider(&self, key: &str, amount: i64, provider_name: &str) -> Result<i64, CacheError> {
        let provider = self.providers.get(provider_name).ok_or_else(|| CacheError {
            message: format!("缓存提供器 '{}' 未注册", provider_name),
            error_type: CacheErrorType::InternalError,
        })?;
        
        provider.increment(key, amount)
    }
    
    fn expire(&self, key: &str, ttl: Duration) -> Result<bool, CacheError> {
        self.expire_in_provider(key, ttl, &self.default_provider)
    }
    
    fn expire_in_provider(&self, key: &str, ttl: Duration, provider_name: &str) -> Result<bool, CacheError> {
        let provider = self.providers.get(provider_name).ok_or_else(|| CacheError {
            message: format!("缓存提供器 '{}' 未注册", provider_name),
            error_type: CacheErrorType::InternalError,
        })?;
        
        provider.expire(key, ttl)
    }
    
    fn flush_all(&self) -> Result<(), CacheError> {
        self.flush_all_in_provider(&self.default_provider)
    }
    
    fn flush_all_in_provider(&self, provider_name: &str) -> Result<(), CacheError> {
        let provider = self.providers.get(provider_name).ok_or_else(|| CacheError {
            message: format!("缓存提供器 '{}' 未注册", provider_name),
            error_type: CacheErrorType::InternalError,
        })?;
        
        provider.flush_all()
    }
    
    fn get_stats(&self) -> Result<CacheStats, CacheError> {
        self.get_stats_from_provider(&self.default_provider)
    }
    
    fn get_stats_from_provider(&self, provider_name: &str) -> Result<CacheStats, CacheError> {
        let provider = self.providers.get(provider_name).ok_or_else(|| CacheError {
            message: format!("缓存提供器 '{}' 未注册", provider_name),
            error_type: CacheErrorType::InternalError,
        })?;
        
        provider.get_stats()
    }
}

// Redis缓存提供器
struct RedisCacheProvider {
    client: redis::Client,
    name: String,
    stats: Arc<Mutex<CacheStats>>,
    start_time: Instant,
}

impl RedisCacheProvider {
    fn new(redis_url: &str, name: &str) -> Result<Self, redis::RedisError> {
        let client = redis::Client::open(redis_url)?;
        
        Ok(RedisCacheProvider {
            client,
            name: name.to_string(),
            stats: Arc::new(Mutex::new(CacheStats {
                hits: 0,
                misses: 0,
                keys: 0,
                memory_usage: 0,
                uptime: Duration::from_secs(0),
            })),
            start_time: Instant::now(),
        })
    }
}

impl CacheProvider for RedisCacheProvider {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn get(&self, key: &str) -> Result<Option<CacheEntry>, CacheError> {
        let mut conn = match self.client.get_connection() {
            Ok(conn) => conn,
            Err(err) => {
                return Err(CacheError {
                    message: format!("无法连接到Redis: {}", err),
                    error_type: CacheErrorType::ConnectionFailed,
                });
            }
        };
        
        // 获取值
        let value: Option<Vec<u8>> = redis::cmd("GET")
            .arg(key)
            .query(&mut conn)
            .map_err(|err| CacheError {
                message: format!("Redis GET操作失败: {}", err),
                error_type: CacheErrorType::OperationFailed,
            })?;
        
        if let Some(value) = value {
            // 更新统计信息
            {
                let mut stats = self.stats.lock().unwrap();
                stats.hits += 1;
            }
            
            // 获取TTL
            let ttl_seconds: isize = redis::cmd("TTL")
                .arg(key)
                .query(&mut conn)
                .map_err(|err| CacheError {
                    message: format!("Redis TTL操作失败: {}", err),
                    error_type: CacheErrorType::OperationFailed,
                })?;
            
            let ttl = if ttl_seconds > 0 {
                Some(Duration::from_secs(ttl_seconds as u64))
            } else {
                None
            };
            
            Ok(Some(CacheEntry {
                value,
                ttl,
                created_at: SystemTime::now() - Duration::from_secs(3600), // 无法从Redis获取创建时间，使用一个固定值
                last_accessed: SystemTime::now(),
            }))
        } else {
            // 更新统计信息
            {
                let mut stats = self.stats.lock().unwrap();
                stats.misses += 1;
            }
            
            Ok(None)
        }
    }
    
    fn set(&self, key: &str, value: &[u8], ttl: Option<Duration>) -> Result<(), CacheError> {
        let mut conn = match self.client.get_connection() {
            Ok(conn) => conn,
            Err(err) => {
                return Err(CacheError {
                    message: format!("无法连接到Redis: {}", err),
                    error_type: CacheErrorType::ConnectionFailed,
                });
            }
        };
        
        if let Some(ttl) = ttl {
            // 设置带有过期时间的键
            let ttl_seconds = ttl.as_secs() as usize;
            
            let _: () = redis::cmd("SETEX")
                .arg(key)
                .arg(ttl_seconds)
                .arg(value)
                .query(&mut conn)
                .map_err(|err| CacheError {
                    message: format!("Redis SETEX操作失败: {}", err),
                    error_type: CacheErrorType::OperationFailed,
                })?;
        } else {
            // 设置无过期时间的键
            let _: () = redis::cmd("SET")
                .arg(key)
                .arg(value)
                .query(&mut conn)
                .map_err(|err| CacheError {
                    message: format!("Redis SET操作失败: {}", err),
                    error_type: CacheErrorType::OperationFailed,
                })?;
        }
        
        Ok(())
    }
    
    fn delete(&self, key: &str) -> Result<bool, CacheError> {
        let mut conn = match self.client.get_connection() {
            Ok(conn) => conn,
            Err(err) => {
                return Err(CacheError {
                    message: format!("无法连接到Redis: {}", err),
                    error_type: CacheErrorType::ConnectionFailed,
                });
            }
        };
        
        // 删除键
        let deleted: isize = redis::cmd("DEL")
            .arg(key)
            .query(&mut conn)
            .map_err(|err| CacheError {
                message: format!("Redis DEL操作失败: {}", err),
                error_type: CacheErrorType::OperationFailed,
            })?;
        
        Ok(deleted > 0)
    }
    
    fn exists(&self, key: &str) -> Result<bool, CacheError> {
        let mut conn = match self.client.get_connection() {
            Ok(conn) => conn,
            Err(err) => {
                return Err(CacheError {
                    message: format!("无法连接到Redis: {}", err),
                    error_type: CacheErrorType::ConnectionFailed,
                });
            }
        };
        
        // 检查键是否存在
        let exists: bool = redis::cmd("EXISTS")
            .arg(key)
            .query(&mut conn)
            .map_err(|err| CacheError {
                message: format!("Redis EXISTS操作失败: {}", err),
                error_type: CacheErrorType::OperationFailed,
            })?;
        
        Ok(exists)
    }
    
    fn increment(&self, key: &str, amount: i64) -> Result<i64, CacheError> {
        let mut conn = match self.client.get_connection() {
            Ok(conn) => conn,
            Err(err) => {
                return Err(CacheError {
                    message: format!("无法连接到Redis: {}", err),
                    error_type: CacheErrorType::ConnectionFailed,
                });
            }
        };
        
        // 递增键
        let new_value: i64 = redis::cmd("INCRBY")
            .arg(key)
            .arg(amount)
            .query(&mut conn)
            .map_err(|err| CacheError {
                message: format!("Redis INCRBY操作失败: {}", err),
                error_type: CacheErrorType::OperationFailed,
            })?;
        
        Ok(new_value)
    }
    
    fn expire(&self, key: &str, ttl: Duration) -> Result<bool, CacheError> {
        let mut conn = match self.client.get_connection() {
            Ok(conn) => conn,
            Err(err) => {
                return Err(CacheError {
                    message: format!("无法连接到Redis: {}", err),
                    error_type: CacheErrorType::ConnectionFailed,
                });
            }
        };
        
        // 设置过期时间
        let ttl_seconds = ttl.as_secs() as usize;
        
        let success: bool = redis::cmd("EXPIRE")
            .arg(key)
            .arg(ttl_seconds)
            .query(&mut conn)
            .map_err(|err| CacheError {
                message: format!("Redis EXPIRE操作失败: {}", err),
                error_type: CacheErrorType::OperationFailed,
            })?;
        
        Ok(success)
    }
    
    fn flush_all(&self) -> Result<(), CacheError> {
        let mut conn = match self.client.get_connection() {
            Ok(conn) => conn,
            Err(err) => {
                return Err(CacheError {
                    message: format!("无法连接到Redis: {}", err),
                    error_type: CacheErrorType::ConnectionFailed,
                });
            }
        };
        
        // 清空数据库
        let _: () = redis::cmd("FLUSHDB")
            .query(&mut conn)
            .map_err(|err| CacheError {
                message: format!("Redis FLUSHDB操作失败: {}", err),
                error_type: CacheErrorType::OperationFailed,
            })?;
        
        Ok(())
    }
    
    fn get_stats(&self) -> Result<CacheStats, CacheError> {
        let mut conn = match self.client.get_connection() {
            Ok(conn) => conn,
            Err(err) => {
                return Err(CacheError {
                    message: format!("无法连接到Redis: {}", err),
                    error_type: CacheErrorType::ConnectionFailed,
                });
            }
        };
        
        // 获取键数量
        let keys: usize = redis::cmd("DBSIZE")
            .query(&mut conn)
            .map_err(|err| CacheError {
                message: format!("Redis DBSIZE操作失败: {}", err),
                error_type: CacheErrorType::OperationFailed,
            })?;
        
        // 获取内存使用情况
        let info: HashMap<String, String> = redis::cmd("INFO")
            .arg("memory")
            .query(&mut conn)
            .map_err(|err| CacheError {
                message: format!("Redis INFO操作失败: {}", err),
                error_type: CacheErrorType::OperationFailed,
            })?;
        
        let memory_usage = info.get("used_memory")
            .and_then(|s| s.parse::<u64>().ok())
            .unwrap_or(0);
        
        let mut stats = self.stats.lock().unwrap();
        stats.keys = keys as u64;
        stats.memory_usage = memory_usage;
        stats.uptime = self.start_time.elapsed();
        
        Ok(stats.clone())
    }
}

// 内存缓存提供器
struct InMemoryCacheProvider {
    name: String,
    cache: Arc<RwLock<HashMap<String, CacheEntry>>>,
    stats: Arc<Mutex<CacheStats>>,
    start_time: Instant,
}

impl InMemoryCacheProvider {
    fn new(name: &str) -> Self {
        InMemoryCacheProvider {
            name: name.to_string(),
            cache: Arc::new(RwLock::new(HashMap::new())),
            stats: Arc::new(Mutex::new(CacheStats {
                hits: 0,
                misses: 0,
                keys: 0,
                memory_usage: 0,
                uptime: Duration::from_secs(0),
            })),
            start_time: Instant::now(),
        }
    }
    
    fn cleanup_expired_keys(&self) {
        let mut cache = self.cache.write().unwrap();
        let now = SystemTime::now();
        
        // 移除所有过期的键
        cache.retain(|_, entry| {
            if let Some(ttl) = entry.ttl {
                if entry.created_at + ttl > now {
                    true
                } else {
                    false
                }
            } else {
                true
            }
        });
    }
}

impl CacheProvider for InMemoryCacheProvider {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn get(&self, key: &str) -> Result<Option<CacheEntry>, CacheError> {
        // 清理过期的键
        self.cleanup_expired_keys();
        
        let cache = self.cache.read().unwrap();
        
        if let Some(entry) = cache.get(key) {
            // 更新统计信息
            {
                let mut stats = self.stats.lock().unwrap();
                stats.hits += 1;
            }
            
            // 创建一个新的条目，更新最后访问时间
            let mut updated_entry = entry.clone();
            updated_entry.last_accessed = SystemTime::now();
            
            Ok(Some(updated_entry))
        } else {
            // 更新统计信息
            {
                let mut stats = self.stats.lock().unwrap();
                stats.misses += 1;
            }
            
            Ok(None)
        }
    }
    
    fn set(&self, key: &str, value: &[u8], ttl: Option<Duration>) -> Result<(), CacheError> {
        let mut cache = self.cache.write().unwrap();
        
        let entry = CacheEntry {
            value: value.to_vec(),
            ttl,
            created_at: SystemTime::now(),
            last_accessed: SystemTime::now(),
        };
        
        cache.insert(key.to_string(), entry);
        
        // 更新统计信息
        {
            let mut stats = self.stats.lock().unwrap();
            stats.keys = cache.len() as u64;
            stats.memory_usage += value.len() as u64;
        }
        
        Ok(())
    }
    
    fn delete(&self, key: &str) -> Result<bool, CacheError> {
        let mut cache = self.cache.write().unwrap();
        
        if let Some(entry) = cache.remove(key) {
            // 更新统计信息
            {
                let mut stats = self.stats.lock().unwrap();
                stats.keys = cache.len() as u64;
                stats.memory_usage = stats.memory_usage.saturating_sub(entry.value.len() as u64);
            }
            
            Ok(true)
        } else {
            Ok(false)
        }
    }
    
    fn exists(&self, key: &str) -> Result<bool, CacheError> {
        // 清理过期的键
        self.cleanup_expired_keys();
        
        let cache = self.cache.read().unwrap();
        Ok(cache.contains_key(key))
    }
    
    fn increment(&self, key: &str, amount: i64) -> Result<i64, CacheError> {
        let mut cache = self.cache.write().unwrap();
        
        let current_value = if let Some(entry) = cache.get(key) {
            let value_str = String::from_utf8(entry.value.clone()).map_err(|err| CacheError {
                message: format!("无法解析整数值: {}", err),
                error_type: CacheErrorType::SerializationError,
            })?;
            
            value_str.parse::<i64>().map_err(|err| CacheError {
                message: format!("无法解析整数值: {}", err),
                error_type: CacheErrorType::SerializationError,
            })?
        } else {
            0
        };
        
        let new_value = current_value + amount;
        let new_value_bytes = new_value.to_string().into_bytes();
        
        let entry = CacheEntry {
            value: new_value_bytes,
            ttl: cache.get(key).and_then(|e| e.ttl),
            created_at: SystemTime::now(),
            last_accessed: SystemTime::now(),
        };
        
        cache.insert(key.to_string(), entry);
        
        Ok(new_value)
    }
    
    fn expire(&self, key: &str, ttl: Duration) -> Result<bool, CacheError> {
        let mut cache = self.cache.write().unwrap();
        
        if let Some(entry) = cache.get_mut(key) {
            entry.ttl = Some(ttl);
            entry.created_at = SystemTime::now(); // 重置创建时间
            Ok(true)
        } else {
            Ok(false)
        }
    }
    
    fn flush_all(&self) -> Result<(), CacheError> {
        let mut cache = self.cache.write().unwrap();
        cache.clear();
        
        // 更新统计信息
        {
            let mut stats = self.stats.lock().unwrap();
            stats.keys = 0;
            stats.memory_usage = 0;
        }
        
        Ok(())
    }
    
    fn get_stats(&self) -> Result<CacheStats, CacheError> {
        let cache = self.cache.read().unwrap();
        
        let mut stats = self.stats.lock().unwrap();
        stats.keys = cache.len() as u64;
        stats.uptime = self.start_time.elapsed();
        
        Ok(stats.clone())
    }
}

// 两级缓存提供器
struct TwoLevelCacheProvider {
    name: String,
    local_cache: Box<dyn CacheProvider>,
    remote_cache: Box<dyn CacheProvider>,
    local_ttl: Duration,
}

impl TwoLevelCacheProvider {
    fn new(name: &str, local_cache: Box<dyn CacheProvider>, remote_cache: Box<dyn CacheProvider>, local_ttl: Duration) -> Self {
        TwoLevelCacheProvider {
            name: name.to_string(),
            local_cache,
            remote_cache,
            local_ttl,
        }
    }
}

impl CacheProvider for TwoLevelCacheProvider {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn get(&self, key: &str) -> Result<Option<CacheEntry>, CacheError> {
        // 首先从本地缓存获取
        match self.local_cache.get(key) {
            Ok(Some(entry)) => {
                // 本地缓存命中
                return Ok(Some(entry));
            },
            _ => {
                // 本地缓存未命中，尝试从远程缓存获取
                match self.remote_cache.get(key) {
                    Ok(Some(entry)) => {
                        // 远程缓存命中，填充本地缓存
                        let _ = self.local_cache.set(key, &entry.value, Some(self.local_ttl));
                        return Ok(Some(entry));
                    },
                    Ok(None) => {
                        // 远程缓存也未命中
                        return Ok(None);
                    },
                    Err(err) => {
                        // 远程缓存访问错误
                        return Err(err);
                    }
                }
            }
        }
    }
    
    fn set(&self, key: &str, value: &[u8], ttl: Option<Duration>) -> Result<(), CacheError> {
        // 同时设置远程和本地缓存
        self.remote_cache.set(key, value, ttl)?;
        
        // 本地缓存可能使用更短的TTL
        let local_ttl = if let Some(ttl) = ttl {
            Some(std::cmp::min(ttl, self.local_ttl))
        } else {
            Some(self.local_ttl)
        };
        
        self.local_cache.set(key, value, local_ttl)?;
        
        Ok(())
    }
    
    fn delete(&self, key: &str) -> Result<bool, CacheError> {
        // 先删除远程缓存
        let remote_result = self.remote_cache.delete(key)?;
        
        // 然后删除本地缓存
        let _ = self.local_cache.delete(key);
        
        Ok(remote_result)
    }
    
    fn exists(&self, key: &str) -> Result<bool, CacheError> {
        // 首先检查本地缓存
        if self.local_cache.exists(key)? {
            return Ok(true);
        }
        
        // 如果本地缓存没有，检查远程缓存
        self.remote_cache.exists(key)
    }
    
    fn increment(&self, key: &str, amount: i64) -> Result<i64, CacheError> {
        // 在远程缓存上执行递增操作
        let new_value = self.remote_cache.increment(key, amount)?;
        
        // 更新本地缓存
        let _ = self.local_cache.set(key, new_value.to_string().as_bytes(), Some(self.local_ttl));
        
        Ok(new_value)
    }
    
    fn expire(&self, key: &str, ttl: Duration) -> Result<bool, CacheError> {
        // 设置远程缓存的过期时间
        let result = self.remote_cache.expire(key, ttl)?;
        
        // 同时设置本地缓存的过期时间
        let local_ttl = std::cmp::min(ttl, self.local_ttl);
        let _ = self.local_cache.expire(key, local_ttl);
        
        Ok(result)
    }
    
    fn flush_all(&self) -> Result<(), CacheError> {
        // 清空远程和本地缓存
        self.remote_cache.flush_all()?;
        self.local_cache.flush_all()?;
        
        Ok(())
    }
    
    fn get_stats(&self) -> Result<CacheStats, CacheError> {
        // 只返回远程缓存的统计信息
        self.remote_cache.get_stats()
    }
}

// 缓存工具函数
struct CacheUtils;

impl CacheUtils {
    fn serialize<T: serde::Serialize>(value: &T) -> Result<Vec<u8>, CacheError> {
        bincode::serialize(value).map_err(|err| CacheError {
            message: format!("序列化失败: {}", err),
            error_type: CacheErrorType::SerializationError,
        })
    }
    
    fn deserialize<T: serde::de::DeserializeOwned>(data: &[u8]) -> Result<T, CacheError> {
        bincode::deserialize(data).map_err(|err| CacheError {
            message: format!("反序列化失败: {}", err),
            error_type: CacheErrorType::SerializationError,
        })
    }
    
    fn get_or_compute<T, F>(
        cache: &DistributedCacheSystem,
        key: &str,
        ttl: Option<Duration>,
        compute_fn: F
    ) -> Result<T, CacheError>
    where
        T: serde::de::DeserializeOwned + serde::Serialize,
        F: FnOnce() -> Result<T, CacheError>,
    {
        // 尝试从缓存获取
        if let Some(entry) = cache.get(key)? {
            return Self::deserialize(&entry.value);
        }
        
        // 如果缓存中没有，计算值
        let value = compute_fn()?;
        
        // 序列化并存储在缓存中
        let serialized = Self::serialize(&value)?;
        cache.set(key, &serialized, ttl)?;
        
        Ok(value)
    }
    
    fn invalidate_by_prefix(cache: &DistributedCacheSystem, prefix: &str) -> Result<usize, CacheError> {
        // 这个函数在实际实现中需要依赖缓存提供器支持按前缀搜索键
        // 简化版：默认返回0，表示没有键被删除
        Ok(0)
    }
    
    fn atomic_increment_and_get(cache: &DistributedCacheSystem, key: &str, amount: i64) -> Result<i64, CacheError> {
        cache.increment(key, amount)
    }
    
    fn memoize<F, R, E>(
        cache: &DistributedCacheSystem,
        key_prefix: &str,
        ttl: Option<Duration>,
        function: F,
        args: &[&str]
    ) -> Result<R, E>
    where
        F: Fn() -> Result<R, E>,
        R: serde::Serialize + serde::de::DeserializeOwned,
        E: From<CacheError>,
    {
        // 构建缓存键
        let key = format!("{}:{}", key_prefix, args.join(":"));
        
        // 尝试从缓存获取
        match cache.get(&key) {
            Ok(Some(entry)) => {
                match Self::deserialize(&entry.value) {
                    Ok(result) => Ok(result),
                    Err(err) => {
                        // 如果反序列化失败，删除无效的缓存条目
                        let _ = cache.delete(&key);
                        Err(err.into())
                    }
                }
            },
            _ => {
                // 执行函数
                let result = function()?;
                
                // 序列化并缓存结果
                match Self::serialize(&result) {
                    Ok(serialized) => {
                        let _ = cache.set(&key, &serialized, ttl);
                    },
                    Err(err) => {
                        return Err(err.into());
                    }
                }
                
                Ok(result)
            }
        }
    }
}

// 分布式缓存管理器
struct DistributedCacheManager {
    cache_system: Arc<DistributedCacheSystem>,
    cache_resolver: Box<dyn Fn(&str) -> String>,
    default_ttl: Duration,
}

impl DistributedCacheManager {
    fn new(
        cache_system: Arc<DistributedCacheSystem>,
        cache_resolver: Box<dyn Fn(&str) -> String>,
        default_ttl: Duration
    ) -> Self {
        DistributedCacheManager {
            cache_system,
            cache_resolver,
            default_ttl,
        }
    }
    
    fn get<T: serde::de::DeserializeOwned>(&self, key: &str) -> Result<Option<T>, CacheError> {
        let provider = (self.cache_resolver)(key);
        
        match self.cache_system.get_from_provider(key, &provider)? {
            Some(entry) => {
                let value = CacheUtils::deserialize(&entry.value)?;
                Ok(Some(value))
            },
            None => Ok(None),
        }
    }
    
    fn set<T: serde::Serialize>(&self, key: &str, value: &T, ttl: Option<Duration>) -> Result<(), CacheError> {
        let provider = (self.cache_resolver)(key);
        let serialized = CacheUtils::serialize(value)?;
        
        self.cache_system.set_with_provider(key, &serialized, ttl.or(Some(self.default_ttl)), &provider)
    }
    
    fn delete(&self, key: &str) -> Result<bool, CacheError> {
        let provider = (self.cache_resolver)(key);
        self.cache_system.delete_from_provider(key, &provider)
    }
    
    fn get_or_compute<T, F>(&self, key: &str, compute_fn: F) -> Result<T, CacheError>
    where
        T: serde::de::DeserializeOwned + serde::Serialize,
        F: FnOnce() -> Result<T, CacheError>,
    {
        CacheUtils::get_or_compute(&self.cache_system, key, Some(self.default_ttl), compute_fn)
    }
    
    fn increment(&self, key: &str, amount: i64) -> Result<i64, CacheError> {
        let provider = (self.cache_resolver)(key);
        self.cache_system.increment_in_provider(key, amount, &provider)
    }
    
    fn flush_all(&self) -> Result<(), CacheError> {
        self.cache_system.flush_all()
    }
}

// 分布式缓存事例：数据库查询缓存
struct DbQueryCache {
    cache_manager: Arc<DistributedCacheManager>,
    query_timeout: Duration,
}

impl DbQueryCache {
    fn new(cache_manager: Arc<DistributedCacheManager>, query_timeout: Duration) -> Self {
        DbQueryCache {
            cache_manager,
            query_timeout,
        }
    }
    
    fn get_query_result<T: serde::de::DeserializeOwned + serde::Serialize>(
        &self,
        query: &str,
        params: &[&str],
        executor: impl FnOnce() -> Result<T, String>
    ) -> Result<T, String> {
        // 创建查询缓存键
        let params_str = params.join(":");
        let key = format!("db:query:{}:{}", query, params_str);
        
        // 尝试从缓存获取
        match self.cache_manager.get::<T>(&key) {
            Ok(Some(result)) => {
                return Ok(result);
            },
            Ok(None) => {
                // 缓存未命中，执行查询
                let result = executor()?;
                
                // 缓存结果
                if let Err(err) = self.cache_manager.set(&key, &result, Some(self.query_timeout)) {
                    println!("缓存查询结果失败: {}", err.message);
                }
                
                Ok(result)
            },
            Err(err) => {
                // 缓存访问出错，执行查询
                println!("访问缓存失败: {}", err.message);
                executor()
            }
        }
    }
    
    fn invalidate_query(&self, query: &str) -> Result<(), String> {
        let key_prefix = format!("db:query:{}", query);
        
        match CacheUtils::invalidate_by_prefix(&self.cache_manager.cache_system, &key_prefix) {
            Ok(_) => Ok(()),
            Err(err) => Err(format!("无效化查询缓存失败: {}", err.message)),
        }
    }
    
    fn invalidate_table(&self, table: &str) -> Result<(), String> {
        // 在实际实现中，这需要一个将表名映射到相关查询的机制
        // 简化版：假设我们直接存储了表相关的查询缓存键
        let key_prefix = format!("db:table:{}", table);
        
        match CacheUtils::invalidate_by_prefix(&self.cache_manager.cache_system, &key_prefix) {
            Ok(_) => Ok(()),
            Err(err) => Err(format!("无效化表缓存失败: {}", err.message)),
        }
    }
}

// 分布式缓存事例：Web响应缓存
struct WebResponseCache {
    cache_manager: Arc<DistributedCacheManager>,
    default_cache_time: Duration,
}

struct CachedResponse {
    status_code: u16,
    headers: HashMap<String, String>,
    body: Vec<u8>,
    timestamp: SystemTime,
}

impl WebResponseCache {
    fn new(cache_manager: Arc<DistributedCacheManager>, default_cache_time: Duration) -> Self {
        WebResponseCache {
            cache_manager,
            default_cache_time,
        }
    }
    
    fn get_cached_response(&self, request_key: &str) -> Result<Option<CachedResponse>, String> {
        match self.cache_manager.get::<CachedResponse>(request_key) {
            Ok(response) => Ok(response),
            Err(err) => Err(format!("获取缓存响应失败: {}", err.message)),
        }
    }
    
    fn cache_response(&self, request_key: &str, response: CachedResponse, ttl: Option<Duration>) -> Result<(), String> {
        let cache_time = ttl.unwrap_or(self.default_cache_time);
        
        match self.cache_manager.set(request_key, &response, Some(cache_time)) {
            Ok(_) => Ok(()),
            Err(err) => Err(format!("缓存响应失败: {}", err.message)),
        }
    }
    
    fn invalidate_response(&self, request_key: &str) -> Result<(), String> {
        match self.cache_manager.delete(request_key) {
            Ok(_) => Ok(()),
            Err(err) => Err(format!("无效化缓存响应失败: {}", err.message)),
        }
    }
    
    fn invalidate_by_pattern(&self, pattern: &str) -> Result<(), String> {
        match CacheUtils::invalidate_by_prefix(&self.cache_manager.cache_system, pattern) {
            Ok(_) => Ok(()),
            Err(err) => Err(format!("无效化缓存模式失败: {}", err.message)),
        }
    }
    
    fn generate_cache_key(&self, method: &str, url: &str, query_params: &HashMap<String, String>, headers: &[(&str, &str)]) -> String {
        // 排序查询参数以确保一致性
        let mut sorted_params: Vec<(&String, &String)> = query_params.iter().collect();
        sorted_params.sort_by(|a, b| a.0.cmp(b.0));
        
        let param_str = sorted_params.iter()
            .map(|(k, v)| format!("{}={}", k, v))
            .collect::<Vec<_>>()
            .join("&");
        
        // 添加相关的头信息（例如接受语言）
        let relevant_headers: Vec<String> = headers.iter()
            .filter(|(name, _)| 
                *name == "accept-language" || 
                *name == "user-agent" || 
                *name == "accept"
            )
            .map(|(name, value)| format!("{}:{}", name, value))
            .collect();
        
        let header_str = if !relevant_headers.is_empty() {
            format!("|{}", relevant_headers.join("|"))
        } else {
            "".to_string()
        };
        
        format!("web:{}:{}:{}:{}", method, url, param_str, header_str)
    }
}

// 分布式缓存事例：Session存储
struct SessionCache {
    cache_manager: Arc<DistributedCacheManager>,
    session_timeout: Duration,
}

struct SessionData {
    id: String,
    user_id: Option<String>,
    data: HashMap<String, serde_json::Value>,
    created_at: SystemTime,
    last_accessed: SystemTime,
}

impl SessionCache {
    fn new(cache_manager: Arc<DistributedCacheManager>, session_timeout: Duration) -> Self {
        SessionCache {
            cache_manager,
            session_timeout,
        }
    }
    
    fn get_session(&self, session_id: &str) -> Result<Option<SessionData>, String> {
        let key = format!("session:{}", session_id);
        
        match self.cache_manager.get::<SessionData>(&key) {
            Ok(session) => Ok(session),
            Err(err) => Err(format!("获取会话失败: {}", err.message)),
        }
    }
    
    fn create_session(&self, user_id: Option<String>) -> Result<SessionData, String> {
        let session_id = uuid::Uuid::new_v4().to_string();
        
        let session = SessionData {
            id: session_id.clone(),
            user_id,
            data: HashMap::new(),
            created_at: SystemTime::now(),
            last_accessed: SystemTime::now(),
        };
        
        let key = format!("session:{}", session_id);
        
        match self.cache_manager.set(&key, &session, Some(self.session_timeout)) {
            Ok(_) => Ok(session),
            Err(err) => Err(format!("创建会话失败: {}", err.message)),
        }
    }
    
    fn update_session(&self, session: &SessionData) -> Result<(), String> {
        let key = format!("session:{}", session.id);
        
        let mut updated_session = session.clone();
        updated_session.last_accessed = SystemTime::now();
        
        match self.cache_manager.set(&key, &updated_session, Some(self.session_timeout)) {
            Ok(_) => Ok(()),
            Err(err) => Err(format!("更新会话失败: {}", err.message)),
        }
    }
    
    fn delete_session(&self, session_id: &str) -> Result<(), String> {
        let key = format!("session:{}", session_id);
        
        match self.cache_manager.delete(&key) {
            Ok(_) => Ok(()),
            Err(err) => Err(format!("删除会话失败: {}", err.message)),
        }
    }
    
    fn get_session_data<T: serde::de::DeserializeOwned>(&self, session_id: &str, key: &str) -> Result<Option<T>, String> {
        match self.get_session(session_id)? {
            Some(session) => {
                if let Some(value) = session.data.get(key) {
                    match serde_json::from_value(value.clone()) {
                        Ok(typed_value) => Ok(Some(typed_value)),
                        Err(_) => Err(format!("无法将会话数据反序列化为请求的类型"))
                    }
                } else {
                    Ok(None)
                }
            },
            None => Ok(None)
        }
    }
    
    fn set_session_data<T: serde::Serialize>(&self, session_id: &str, key: &str, value: &T) -> Result<(), String> {
        match self.get_session(session_id)? {
            Some(mut session) => {
                match serde_json::to_value(value) {
                    Ok(json_value) => {
                        session.data.insert(key.to_string(), json_value);
                        self.update_session(&session)
                    },
                    Err(_) => Err(format!("无法将数据序列化为JSON"))
                }
            },
            None => Err(format!("会话不存在"))
        }
    }
    
    fn remove_session_data(&self, session_id: &str, key: &str) -> Result<(), String> {
        match self.get_session(session_id)? {
            Some(mut session) => {
                session.data.remove(key);
                self.update_session(&session)
            },
            None => Err(format!("会话不存在"))
        }
    }
    
    fn clean_expired_sessions(&self) -> Result<usize, String> {
        // 这在实际中需要依赖缓存提供器支持按过期时间查询
        // 简化版：返回0，表示没有会话被清理
        Ok(0)
    }
}

// 分布式队列系统
struct DistributedQueueSystem {
    queue_providers: HashMap<String, Box<dyn QueueProvider>>,
    default_provider: String,
}

trait QueueProvider: Send + Sync {
    fn name(&self) -> &str;
    fn push(&self, queue_name: &str, message: &[u8], ttl: Option<Duration>) -> Result<String, QueueError>;
    fn pop(&self, queue_name: &str, wait_time: Option<Duration>) -> Result<Option<QueueMessage>, QueueError>;
    fn ack(&self, queue_name: &str, message_id: &str) -> Result<bool, QueueError>;
    fn peek(&self, queue_name: &str, count: usize) -> Result<Vec<QueueMessage>, QueueError>;
    fn len(&self, queue_name: &str) -> Result<usize, QueueError>;
    fn is_empty(&self, queue_name: &str) -> Result<bool, QueueError>;
    fn purge(&self, queue_name: &str) -> Result<usize, QueueError>;
    fn delete_queue(&self, queue_name: &str) -> Result<bool, QueueError>;
    fn list_queues(&self) -> Result<Vec<String>, QueueError>;
}

struct QueueMessage {
    id: String,
    payload: Vec<u8>,
    received_count: u32,
    first_received_at: Option<SystemTime>,
    received_at: Option<SystemTime>,
    visible_at: SystemTime,
}

struct QueueError {
    message: String,
    error_type: QueueErrorType,
}

enum QueueErrorType {
    ConnectionFailed,
    OperationFailed,
    InvalidArgument,
    QueueNotFound,
    MessageNotFound,
    SerializationError,
}

impl DistributedQueueSystem {
    fn new(default_provider: &str) -> Self {
        DistributedQueueSystem {
            queue_providers: HashMap::new(),
            default_provider: default_provider.to_string(),
        }
    }
    
    fn register_provider(&mut self, provider: Box<dyn QueueProvider>) -> Result<(), QueueError> {
        let name = provider.name().to_string();
        
        if self.queue_providers.contains_key(&name) {
            return Err(QueueError {
                message: format!("队列提供器 {} 已存在", name),
                error_type: QueueErrorType::InvalidArgument,
            });
        }
        
        self.queue_providers.insert(name, provider);
        Ok(())
    }
    
    fn set_default_provider(&mut self, provider_name: &str) -> Result<(), QueueError> {
        if !self.queue_providers.contains_key(provider_name) {
            return Err(QueueError {
                message: format!("队列提供器 {} 不存在", provider_name),
                error_type: QueueErrorType::InvalidArgument,
            });
        }
        
        self.default_provider = provider_name.to_string();
        Ok(())
    }
    
    fn push(&self, queue_name: &str, message: &[u8], ttl: Option<Duration>) -> Result<String, QueueError> {
        if let Some(provider) = self.queue_providers.get(&self.default_provider) {
            provider.push(queue_name, message, ttl)
        } else {
            Err(QueueError {
                message: format!("默认队列提供器不存在"),
                error_type: QueueErrorType::InvalidArgument,
            })
        }
    }
    
    fn push_with_provider(&self, queue_name: &str, message: &[u8], ttl: Option<Duration>, provider_name: &str) -> Result<String, QueueError> {
        if let Some(provider) = self.queue_providers.get(provider_name) {
            provider.push(queue_name, message, ttl)
        } else {
            Err(QueueError {
                message: format!("队列提供器 {} 不存在", provider_name),
                error_type: QueueErrorType::InvalidArgument,
            })
        }
    }
    
    fn pop(&self, queue_name: &str, wait_time: Option<Duration>) -> Result<Option<QueueMessage>, QueueError> {
        if let Some(provider) = self.queue_providers.get(&self.default_provider) {
            provider.pop(queue_name, wait_time)
        } else {
            Err(QueueError {
                message: format!("默认队列提供器不存在"),
                error_type: QueueErrorType::InvalidArgument,
            })
        }
    }
    
    fn pop_from_provider(&self, queue_name: &str, wait_time: Option<Duration>, provider_name: &str) -> Result<Option<QueueMessage>, QueueError> {
        if let Some(provider) = self.queue_providers.get(provider_name) {
            provider.pop(queue_name, wait_time)
        } else {
            Err(QueueError {
                message: format!("队列提供器 {} 不存在", provider_name),
                error_type: QueueErrorType::InvalidArgument,
            })
        }
    }
    
    fn ack(&self, queue_name: &str, message_id: &str) -> Result<bool, QueueError> {
        if let Some(provider) = self.queue_providers.get(&self.default_provider) {
            provider.ack(queue_name, message_id)
        } else {
            Err(QueueError {
                message: format!("默认队列提供器不存在"),
                error_type: QueueErrorType::InvalidArgument,
            })
        }
    }
    
    fn ack_in_provider(&self, queue_name: &str, message_id: &str, provider_name: &str) -> Result<bool, QueueError> {
        if let Some(provider) = self.queue_providers.get(provider_name) {
            provider.ack(queue_name, message_id)
        } else {
            Err(QueueError {
                message: format!("队列提供器 {} 不存在", provider_name),
                error_type: QueueErrorType::InvalidArgument,
            })
        }
    }
    
    fn peek(&self, queue_name: &str, count: usize) -> Result<Vec<QueueMessage>, QueueError> {
        if let Some(provider) = self.queue_providers.get(&self.default_provider) {
            provider.peek(queue_name, count)
        } else {
            Err(QueueError {
                message: format!("默认队列提供器不存在"),
                error_type: QueueErrorType::InvalidArgument,
            })
        }
    }
    
    fn peek_in_provider(&self, queue_name: &str, count: usize, provider_name: &str) -> Result<Vec<QueueMessage>, QueueError> {
        if let Some(provider) = self.queue_providers.get(provider_name) {
            provider.peek(queue_name, count)
        } else {
            Err(QueueError {
                message: format!("队列提供器 {} 不存在", provider_name),
                error_type: QueueErrorType::InvalidArgument,
            })
        }
    }
    
    fn len(&self, queue_name: &str) -> Result<usize, QueueError> {
        if let Some(provider) = self.queue_providers.get(&self.default_provider) {
            provider.len(queue_name)
        } else {
            Err(QueueError {
                message: format!("默认队列提供器不存在"),
                error_type: QueueErrorType::InvalidArgument,
            })
        }
    }
    
    fn len_in_provider(&self, queue_name: &str, provider_name: &str) -> Result<usize, QueueError> {
        if let Some(provider) = self.queue_providers.get(provider_name) {
            provider.len(queue_name)
        } else {
            Err(QueueError {
                message: format!("队列提供器 {} 不存在", provider_name),
                error_type: QueueErrorType::InvalidArgument,
            })
        }
    }
    
    fn purge(&self, queue_name: &str) -> Result<usize, QueueError> {
        if let Some(provider) = self.queue_providers.get(&self.default_provider) {
            provider.purge(queue_name)
        } else {
            Err(QueueError {
                message: format!("默认队列提供器不存在"),
                error_type: QueueErrorType::InvalidArgument,
            })
        }
    }
    
    fn purge_in_provider(&self, queue_name: &str, provider_name: &str) -> Result<usize, QueueError> {
        if let Some(provider) = self.queue_providers.get(provider_name) {
            provider.purge(queue_name)
        } else {
            Err(QueueError {
                message: format!("队列提供器 {} 不存在", provider_name),
                error_type: QueueErrorType::InvalidArgument,
            })
        }
    }
    
    fn list_queues(&self) -> Result<Vec<String>, QueueError> {
        if let Some(provider) = self.queue_providers.get(&self.default_provider) {
            provider.list_queues()
        } else {
            Err(QueueError {
                message: format!("默认队列提供器不存在"),
                error_type: QueueErrorType::InvalidArgument,
            })
        }
    }
    
    fn list_queues_in_provider(&self, provider_name: &str) -> Result<Vec<String>, QueueError> {
        if let Some(provider) = self.queue_providers.get(provider_name) {
            provider.list_queues()
        } else {
            Err(QueueError {
                message: format!("队列提供器 {} 不存在", provider_name),
                error_type: QueueErrorType::InvalidArgument,
            })
        }
    }
}

struct RedisQueueProvider {
    client: redis::Client,
    name: String,
    visibility_timeout: Duration,
}

impl RedisQueueProvider {
    fn new(redis_url: &str, name: &str, visibility_timeout: Duration) -> Result<Self, redis::RedisError> {
        let client = redis::Client::open(redis_url)?;
        
        Ok(RedisQueueProvider {
            client,
            name: name.to_string(),
            visibility_timeout,
        })
    }
    
    fn get_queue_key(&self, queue_name: &str) -> String {
        format!("queue:{}:messages", queue_name)
    }
    
    fn get_processing_key(&self, queue_name: &str) -> String {
        format!("queue:{}:processing", queue_name)
    }
    
    fn get_message_key(&self, queue_name: &str, message_id: &str) -> String {
        format!("queue:{}:message:{}", queue_name, message_id)
    }
}

impl QueueProvider for RedisQueueProvider {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn push(&self, queue_name: &str, message: &[u8], ttl: Option<Duration>) -> Result<String, QueueError> {
        let mut conn = match self.client.get_connection() {
            Ok(conn) => conn,
            Err(err) => {
                return Err(QueueError {
                    message: format!("无法连接到Redis: {}", err),
                    error_type: QueueErrorType::ConnectionFailed,
                });
            }
        };
        
        // 生成消息ID
        let message_id = uuid::Uuid::new_v4().to_string();
        
        // 创建消息
        let message = QueueMessage {
            id: message_id.clone(),
            payload: message.to_vec(),
            received_count: 0,
            first_received_at: None,
            received_at: None,
            visible_at: SystemTime::now(),
        };
        
        // 序列化消息
        let message_data = match bincode::serialize(&message) {
            Ok(data) => data,
            Err(err) => {
                return Err(QueueError {
                    message: format!("消息序列化失败: {}", err),
                    error_type: QueueErrorType::SerializationError,
                });
            }
        };
        
        // 存储消息
        let message_key = self.get_message_key(queue_name, &message_id);
        let queue_key = self.get_queue_key(queue_name);
        
        let _: () = redis::pipe()
            .cmd("SET").arg(&message_key).arg(&message_data).ignore()
            .cmd("LPUSH").arg(&queue_key).arg(&message_id).ignore()
            .query(&mut conn)
            .map_err(|err| QueueError {
                message: format!("Redis操作失败: {}", err),
                error_type: QueueErrorType::OperationFailed,
            })?;
        
        // 如果指定了TTL，设置消息的过期时间
        if let Some(ttl) = ttl {
            let ttl_seconds = ttl.as_secs() as usize;
            
            let _: () = redis::cmd("EXPIRE")
                .arg(&message_key)
                .arg(ttl_seconds)
                .query(&mut conn)
                .map_err(|err| QueueError {
                    message: format!("Redis EXPIRE操作失败: {}", err),
                    error_type: QueueErrorType::OperationFailed,
                })?;
        }
        
        Ok(message_id)
    }
    
    fn pop(&self, queue_name: &str, wait_time: Option<Duration>) -> Result<Option<QueueMessage>, QueueError> {
        let mut conn = match self.client.get_connection() {
            Ok(conn) => conn,
            Err(err) => {
                return Err(QueueError {
                    message: format!("无法连接到Redis: {}", err),
                    error_type: QueueErrorType::ConnectionFailed,
                });
            }
        };
        
        let queue_key = self.get_queue_key(queue_name);
        let processing_key = self.get_processing_key(queue_name);
        
        // 从队列中弹出消息ID
        let message_id: Option<String> = if let Some(wait_time) = wait_time {
            // 如果指定了等待时间，使用阻塞弹出
            let wait_seconds = wait_time.as_secs() as usize;
            
            let result: Option<(String, String)> = redis::cmd("BRPOPLPUSH")
                .arg(&queue_key)
                .arg(&processing_key)
                .arg(wait_seconds)
                .query(&mut conn)
                .map_err(|err| QueueError {
                    message: format!("Redis BRPOPLPUSH操作失败: {}", err),
                    error_type: QueueErrorType::OperationFailed,
                })?;
            
            result.map(|(_, id)| id)
        } else {
            // 否则使用非阻塞弹出
            redis::cmd("RPOPLPUSH")
                .arg(&queue_key)
                .arg(&processing_key)
                .query(&mut conn)
                .map_err(|err| QueueError {
                    message: format!("Redis RPOPLPUSH操作失败: {}", err),
                    error_type: QueueErrorType::OperationFailed,
                })?
        };
        
        if let Some(message_id) = message_id {
            // 获取消息数据
            let message_key = self.get_message_key(queue_name, &message_id);
            
            let message_data: Option<Vec<u8>> = redis::cmd("GET")
                .arg(&message_key)
                .query(&mut conn)
                .map_err(|err| QueueError {
                    message: format!("Redis GET操作失败: {}", err),
                    error_type: QueueErrorType::OperationFailed,
                })?;
            
            if let Some(message_data) = message_data {
                // 反序列化消息
                let mut message: QueueMessage = match bincode::deserialize(&message_data) {
                    Ok(message) => message,
                    Err(err) => {
                        return Err(QueueError {
                            message: format!("消息反序列化失败: {}", err),
                            error_type: QueueErrorType::SerializationError,
                        });
                    }
                };
                
                // 更新消息接收计数和时间
                let now = SystemTime::now();
                message.received_count += 1;
                
                if message.first_received_at.is_none() {
                    message.first_received_at = Some(now);
                }
                
                message.received_at = Some(now);
                message.visible_at = now + self.visibility_timeout;
                
                // 重新序列化并存储更新后的消息
                let updated_message_data = match bincode::serialize(&message) {
                    Ok(data) => data,
                    Err(err) => {
                        return Err(QueueError {
                            message: format!("消息序列化失败: {}", err),
                            error_type: QueueErrorType::SerializationError,
                        });
                    }
                };
                
                let _: () = redis::cmd("SET")
                    .arg(&message_key)
                    .arg(&updated_message_data)
                    .query(&mut conn)
                    .map_err(|err| QueueError {
                        message: format!("Redis SET操作失败: {}", err),
                        error_type: QueueErrorType::OperationFailed,
                    })?;
                
                return Ok(Some(message));
            }
        }
        
        Ok(None)
    }
    
    fn ack(&self, queue_name: &str, message_id: &str) -> Result<bool, QueueError> {
        let mut conn = match self.client.get_connection() {
            Ok(conn) => conn,
            Err(err) => {
                return Err(QueueError {
                    message: format!("无法连接到Redis: {}", err),
                    error_type: QueueErrorType::ConnectionFailed,
                });
            }
        };
        
        let processing_key = self.get_processing_key(queue_name);
        let message_key = self.get_message_key(queue_name, message_id);
        
        // 从处理中列表移除消息ID
        let removed: i64 = redis::cmd("LREM")
            .arg(&processing_key)
            .arg(1)
            .arg(message_id)
            .query(&mut conn)
            .map_err(|err| QueueError {
                message: format!("Redis LREM操作失败: {}", err),
                error_type: QueueErrorType::OperationFailed,
            })?;
        
        // 删除消息
        let deleted: i64 = redis::cmd("DEL")
            .arg(&message_key)
            .query(&mut conn)
            .map_err(|err| QueueError {
                message: format!("Redis DEL操作失败: {}", err),
                error_type: QueueErrorType::OperationFailed,
            })?;
        
        Ok(removed > 0 && deleted > 0)
    }
    
    fn peek(&self, queue_name: &str, count: usize) -> Result<Vec<QueueMessage>, QueueError> {
        let mut conn = match self.client.get_connection() {
            Ok(conn) => conn,
            Err(err) => {
                return Err(QueueError {
                    message: format!("无法连接到Redis: {}", err),
                    error_type: QueueErrorType::ConnectionFailed,
                });
            }
        };
        
        let queue_key = self.get_queue_key(queue_name);
        
        // 获取队列中的消息ID（右侧为队列头）
        let message_ids: Vec<String> = redis::cmd("LRANGE")
            .arg(&queue_key)
            .arg(-count as isize)
            .arg(-1)
            .query(&mut conn)
            .map_err(|err| QueueError {
                message: format!("Redis LRANGE操作失败: {}", err),
                error_type: QueueErrorType::OperationFailed,
            })?;
        
        let mut messages = Vec::with_capacity(message_ids.len());
        
        for message_id in message_ids {
            let message_key = self.get_message_key(queue_name, &message_id);
            
            let message_data: Option<Vec<u8>> = redis::cmd("GET")
                .arg(&message_key)
                .query(&mut conn)
                .map_err(|err| QueueError {
                    message: format!("Redis GET操作失败: {}", err),
                    error_type: QueueErrorType::OperationFailed,
                })?;
            
            if let Some(message_data) = message_data {
                match bincode::deserialize(&message_data) {
                    Ok(message) => messages.push(message),
                    Err(err) => {
                        return Err(QueueError {
                            message: format!("消息反序列化失败: {}", err),
                            error_type: QueueErrorType::SerializationError,
                        });
                    }
                }
            }
        }
        
        Ok(messages)
    }
    
    fn len(&self, queue_name: &str) -> Result<usize, QueueError> {
        let mut conn = match self.client.get_connection() {
            Ok(conn) => conn,
            Err(err) => {
                return Err(QueueError {
                    message: format!("无法连接到Redis: {}", err),
                    error_type: QueueErrorType::ConnectionFailed,
                });
            }
        };
        
        let queue_key = self.get_queue_key(queue_name);
        
        let length: usize = redis::cmd("LLEN")
            .arg(&queue_key)
            .query(&mut conn)
            .map_err(|err| QueueError {
                message: format!("Redis LLEN操作失败: {}", err),
                error_type: QueueErrorType::OperationFailed,
            })?;
        
        Ok(length)
    }
    
    fn is_empty(&self, queue_name: &str) -> Result<bool, QueueError> {
        let length = self.len(queue_name)?;
        Ok(length == 0)
    }
    
    fn purge(&self, queue_name: &str) -> Result<usize, QueueError> {
        let mut conn = match self.client.get_connection() {
            Ok(conn) => conn,
            Err(err) => {
                return Err(QueueError {
                    message: format!("无法连接到Redis: {}", err),
                    error_type: QueueErrorType::ConnectionFailed,
                });
            }
        };
        
        let queue_key = self.get_queue_key(queue_name);
        let processing_key = self.get_processing_key(queue_name);
        
        // 获取所有消息ID
        let mut message_ids: Vec<String> = redis::cmd("LRANGE")
            .arg(&queue_key)
            .arg(0)
            .arg(-1)
            .query(&mut conn)
            .map_err(|err| QueueError {
                message: format!("Redis LRANGE操作失败: {}", err),
                error_type: QueueErrorType::OperationFailed,
            })?;
        
        let processing_ids: Vec<String> = redis::cmd("LRANGE")
            .arg(&processing_key)
            .arg(0)
            .arg(-1)
            .query(&mut conn)
            .map_err(|err| QueueError {
                message: format!("Redis LRANGE操作失败: {}", err),
                error_type: QueueErrorType::OperationFailed,
            })?;
        
        message_ids.extend(processing_ids);
        
        // 删除所有消息
        let mut pipeline = redis::pipe();
        
        for message_id in &message_ids {
            let message_key = self.get_message_key(queue_name, message_id);
            pipeline.cmd("DEL").arg(&message_key).ignore();
        }
        
        // 清空队列
        pipeline.cmd("DEL").arg(&queue_key).ignore();
        pipeline.cmd("DEL").arg(&processing_key).ignore();
        
        let _: () = pipeline
            .query(&mut conn)
            .map_err(|err| QueueError {
                message: format!("Redis管道操作失败: {}", err),
                error_type: QueueErrorType::OperationFailed,
            })?;
        
        Ok(message_ids.len())
    }
    
    fn delete_queue(&self, queue_name: &str) -> Result<bool, QueueError> {
        // 清空队列然后删除队列键
        let _ = self.purge(queue_name)?;
        Ok(true)
    }
    
    fn list_queues(&self) -> Result<Vec<String>, QueueError> {
        let mut conn = match self.client.get_connection() {
            Ok(conn) => conn,
            Err(err) => {
                return Err(QueueError {
                    message: format!("无法连接到Redis: {}", err),
                    error_type: QueueErrorType::ConnectionFailed,
                });
            }
        };
        
        // 查找所有队列键
        let keys: Vec<String> = redis::cmd("KEYS")
            .arg("queue:*:messages")
            .query(&mut conn)
            .map_err(|err| QueueError {
                message: format!("Redis KEYS操作失败: {}", err),
                error_type: QueueErrorType::OperationFailed,
            })?;
        
        // 提取队列名
        let queues = keys
            .iter()
            .filter_map(|key| {
                let parts: Vec<&str> = key.split(':').collect();
                if parts.len() >= 3 {
                    Some(parts[1].to_string())
                } else {
                    None
                }
            })
            .collect();
        
        Ok(queues)
    }
}

// 内存队列提供器
struct InMemoryQueueProvider {
    name: String,
    queues: Arc<RwLock<HashMap<String, VecDeque<QueueMessage>>>>,
    processing: Arc<RwLock<HashMap<String, HashMap<String, QueueMessage>>>>,
    visibility_timeout: Duration,
}

impl InMemoryQueueProvider {
    fn new(name: &str, visibility_timeout: Duration) -> Self {
        InMemoryQueueProvider {
            name: name.to_string(),
            queues: Arc::new(RwLock::new(HashMap::new())),
            processing: Arc::new(RwLock::new(HashMap::new())),
            visibility_timeout,
        }
    }
    
    fn get_or_create_queue(&self, queue_name: &str) -> Result<(), QueueError> {
        let mut queues = self.queues.write().unwrap();
        if !queues.contains_key(queue_name) {
            queues.insert(queue_name.to_string(), VecDeque::new());
        }
        
        let mut processing = self.processing.write().unwrap();
        if !processing.contains_key(queue_name) {
            processing.insert(queue_name.to_string(), HashMap::new());
        }
        
        Ok(())
    }
    
    fn requeue_expired_messages(&self, queue_name: &str) -> Result<usize, QueueError> {
        let now = SystemTime::now();
        let mut count = 0;
        
        // 获取过期的消息
        let mut expired_messages = Vec::new();
        {
            let processing = self.processing.read().unwrap();
            
            if let Some(queue_processing) = processing.get(queue_name) {
                for (id, message) in queue_processing {
                    if message.visible_at <= now {
                        expired_messages.push(id.clone());
                    }
                }
            }
        }
        
        // 重新入队过期的消息
        if !expired_messages.is_empty() {
            let mut processing = self.processing.write().unwrap();
            let mut queues = self.queues.write().unwrap();
            
            if let Some(queue_processing) = processing.get_mut(queue_name) {
                if let Some(queue) = queues.get_mut(queue_name) {
                    for id in &expired_messages {
                        if let Some(message) = queue_processing.remove(id) {
                            queue.push_back(message);
                            count += 1;
                        }
                    }
                }
            }
        }
        
        Ok(count)
    }
}

impl QueueProvider for InMemoryQueueProvider {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn push(&self, queue_name: &str, message: &[u8], ttl: Option<Duration>) -> Result<String, QueueError> {
        self.get_or_create_queue(queue_name)?;
        
        // 生成消息ID
        let message_id = uuid::Uuid::new_v4().to_string();
        
        // 创建消息
        let message = QueueMessage {
            id: message_id.clone(),
            payload: message.to_vec(),
            received_count: 0,
            first_received_at: None,
            received_at: None,
            visible_at: SystemTime::now(),
        };
        
        // 添加到队列
        let mut queues = self.queues.write().unwrap();
        if let Some(queue) = queues.get_mut(queue_name) {
            queue.push_back(message);
        }
        
        Ok(message_id)
    }
    
    fn pop(&self, queue_name: &str, wait_time: Option<Duration>) -> Result<Option<QueueMessage>, QueueError> {
        self.get_or_create_queue(queue_name)?;
        
        // 重新入队过期的消息
        self.requeue_expired_messages(queue_name)?;
        
        // 尝试获取消息
        let start_time = Instant::now();
        loop {
            {
                let mut queues = self.queues.write().unwrap();
                if let Some(queue) = queues.get_mut(queue_name) {
                    if let Some(mut message) = queue.pop_front() {
                        // 更新消息状态
                        let now = SystemTime::now();
                        message.received_count += 1;
                        
                        if message.first_received_at.is_none() {
                            message.first_received_at = Some(now);
                        }
                        
                        message.received_at = Some(now);
                        message.visible_at = now + self.visibility_timeout;
                        
                        // 添加到处理中消息集合
                        let mut processing = self.processing.write().unwrap();
                        if let Some(queue_processing) = processing.get_mut(queue_name) {
                            queue_processing.insert(message.id.clone(), message.clone());
                        }
                        
                        return Ok(Some(message));
                    }
                }
            }
            
            // 检查是否等待超时
            if let Some(wait_time) = wait_time {
                if start_time.elapsed() >= wait_time {
                    return Ok(None);
                }
                
                // 短暂休眠后重试
                std::thread::sleep(Duration::from_millis(100));
            } else {
                return Ok(None);
            }
        }
    }
    
    fn ack(&self, queue_name: &str, message_id: &str) -> Result<bool, QueueError> {
        let mut processing = self.processing.write().unwrap();
        
        if let Some(queue_processing) = processing.get_mut(queue_name) {
            if queue_processing.remove(message_id).is_some() {
                return Ok(true);
            }
        }
        
        Ok(false)
    }
    
    fn peek(&self, queue_name: &str, count: usize) -> Result<Vec<QueueMessage>, QueueError> {
        self.get_or_create_queue(queue_name)?;
        
        let queues = self.queues.read().unwrap();
        
        if let Some(queue) = queues.get(queue_name) {
            let mut messages = Vec::new();
            for (i, message) in queue.iter().enumerate() {
                if i >= count {
                    break;
                }
                messages.push(message.clone());
            }
            return Ok(messages);
        }
        
        Ok(Vec::new())
    }
    
    fn len(&self, queue_name: &str) -> Result<usize, QueueError> {
        let queues = self.queues.read().unwrap();
        
        if let Some(queue) = queues.get(queue_name) {
            return Ok(queue.len());
        }
        
        Ok(0)
    }
    
    fn is_empty(&self, queue_name: &str) -> Result<bool, QueueError> {
        let length = self.len(queue_name)?;
        Ok(length == 0)
    }
    
    fn purge(&self, queue_name: &str) -> Result<usize, QueueError> {
        let mut total_count = 0;
        
        // 清空队列
        {
            let mut queues = self.queues.write().unwrap();
            if let Some(queue) = queues.get_mut(queue_name) {
                total_count += queue.len();
                queue.clear();
            }
        }
        
        // 清空处理中的消息
        {
            let mut processing = self.processing.write().unwrap();
            if let Some(queue_processing) = processing.get_mut(queue_name) {
                total_count += queue_processing.len();
                queue_processing.clear();
            }
        }
        
        Ok(total_count)
    }
    
    fn delete_queue(&self, queue_name: &str) -> Result<bool, QueueError> {
        let mut queues = self.queues.write().unwrap();
        let mut processing = self.processing.write().unwrap();
        
        let removed_queue = queues.remove(queue_name).is_some();
        let removed_processing = processing.remove(queue_name).is_some();
        
        Ok(removed_queue || removed_processing)
    }
    
    fn list_queues(&self) -> Result<Vec<String>, QueueError> {
        let queues = self.queues.read().unwrap();
        let queue_names = queues.keys().cloned().collect();
        Ok(queue_names)
    }
}

// 分布式消息总线系统
struct DistributedMessageBus {
    providers: HashMap<String, Box<dyn MessageBusProvider>>,
    default_provider: String,
}

trait MessageBusProvider: Send + Sync {
    fn name(&self) -> &str;
    fn publish(&self, topic: &str, message: &[u8], headers: Option<HashMap<String, String>>) -> Result<String, MessageBusError>;
    fn subscribe(&self, subscription_id: &str, topics: &[String], handler: Arc<dyn Fn(Message) -> Result<(), MessageBusError> + Send + Sync>) -> Result<(), MessageBusError>;
    fn unsubscribe(&self, subscription_id: &str) -> Result<bool, MessageBusError>;
    fn list_topics(&self) -> Result<Vec<String>, MessageBusError>;
    fn list_subscriptions(&self) -> Result<Vec<Subscription>, MessageBusError>;
}

struct Message {
    id: String,
    topic: String,
    payload: Vec<u8>,
    headers: HashMap<String, String>,
    timestamp: SystemTime,
    attempts: u32,
}

struct Subscription {
    id: String,
    topics: Vec<String>,
    created_at: SystemTime,
    last_active: SystemTime,
    message_count: u64,
}

struct MessageBusError {
    message: String,
    error_type: MessageBusErrorType,
}

enum MessageBusErrorType {
    ConnectionFailed,
    OperationFailed,
    InvalidArgument,
    TopicNotFound,
    SubscriptionNotFound,
    SerializationError,
}

impl DistributedMessageBus {
    fn new(default_provider: &str) -> Self {
        DistributedMessageBus {
            providers: HashMap::new(),
            default_provider: default_provider.to_string(),
        }
    }
    
    fn register_provider(&mut self, provider: Box<dyn MessageBusProvider>) -> Result<(), MessageBusError> {
        let name = provider.name().to_string();
        
        if self.providers.contains_key(&name) {
            return Err(MessageBusError {
                message: format!("消息总线提供器 {} 已存在", name),
                error_type: MessageBusErrorType::InvalidArgument,
            });
        }
        
        self.providers.insert(name, provider);
        Ok(())
    }
    
    fn set_default_provider(&mut self, provider_name: &str) -> Result<(), MessageBusError> {
        if !self.providers.contains_key(provider_name) {
            return Err(MessageBusError {
                message: format!("消息总线提供器 {} 不存在", provider_name),
                error_type: MessageBusErrorType::InvalidArgument,
            });
        }
        
        self.default_provider = provider_name.to_string();
        Ok(())
    }
    
    fn publish(&self, topic: &str, message: &[u8], headers: Option<HashMap<String, String>>) -> Result<String, MessageBusError> {
        if let Some(provider) = self.providers.get(&self.default_provider) {
            provider.publish(topic, message, headers)
        } else {
            Err(MessageBusError {
                message: format!("默认消息总线提供器不存在"),
                error_type: MessageBusErrorType::InvalidArgument,
            })
        }
    }
    
    fn publish_with_provider(&self, topic: &str, message: &[u8], headers: Option<HashMap<String, String>>, provider_name: &str) -> Result<String, MessageBusError> {
        if let Some(provider) = self.providers.get(provider_name) {
            provider.publish(topic, message, headers)
        } else {
            Err(MessageBusError {
                message: format!("消息总线提供器 {} 不存在", provider_name),
                error_type: MessageBusErrorType::InvalidArgument,
            })
        }
    }
    
    fn subscribe<F>(&self, subscription_id: &str, topics: &[String], handler: F) -> Result<(), MessageBusError>
    where
        F: Fn(Message) -> Result<(), MessageBusError> + Send + Sync + 'static
    {
        if let Some(provider) = self.providers.get(&self.default_provider) {
            provider.subscribe(subscription_id, topics, Arc::new(handler))
        } else {
            Err(MessageBusError {
                message: format!("默认消息总线提供器不存在"),
                error_type: MessageBusErrorType::InvalidArgument,
            })
        }
    }
    
    fn subscribe_with_provider<F>(&self, subscription_id: &str, topics: &[String], handler: F, provider_name: &str) -> Result<(), MessageBusError>
    where
        F: Fn(Message) -> Result<(), MessageBusError> + Send + Sync + 'static
    {
        if let Some(provider) = self.providers.get(provider_name) {
            provider.subscribe(subscription_id, topics, Arc::new(handler))
        } else {
            Err(MessageBusError {
                message: format!("消息总线提供器 {} 不存在", provider_name),
                error_type: MessageBusErrorType::InvalidArgument,
            })
        }
    }
    
    fn unsubscribe(&self, subscription_id: &str) -> Result<bool, MessageBusError> {
        if let Some(provider) = self.providers.get(&self.default_provider) {
            provider.unsubscribe(subscription_id)
        } else {
            Err(MessageBusError {
                message: format!("默认消息总线提供器不存在"),
                error_type: MessageBusErrorType::InvalidArgument,
            })
        }
    }
    
    fn unsubscribe_from_provider(&self, subscription_id: &str, provider_name: &str) -> Result<bool, MessageBusError> {
        if let Some(provider) = self.providers.get(provider_name) {
            provider.unsubscribe(subscription_id)
        } else {
            Err(MessageBusError {
                message: format!("消息总线提供器 {} 不存在", provider_name),
                error_type: MessageBusErrorType::InvalidArgument,
            })
        }
    }
    
    fn list_topics(&self) -> Result<Vec<String>, MessageBusError> {
        if let Some(provider) = self.providers.get(&self.default_provider) {
            provider.list_topics()
        } else {
            Err(MessageBusError {
                message: format!("默认消息总线提供器不存在"),
                error_type: MessageBusErrorType::InvalidArgument,
            })
        }
    }
    
    fn list_topics_from_provider(&self, provider_name: &str) -> Result<Vec<String>, MessageBusError> {
        if let Some(provider) = self.providers.get(provider_name) {
            provider.list_topics()
        } else {
            Err(MessageBusError {
                message: format!("消息总线提供器 {} 不存在", provider_name),
                error_type: MessageBusErrorType::InvalidArgument,
            })
        }
    }
    
    fn list_subscriptions(&self) -> Result<Vec<Subscription>, MessageBusError> {
        if let Some(provider) = self.providers.get(&self.default_provider) {
            provider.list_subscriptions()
        } else {
            Err(MessageBusError {
                message: format!("默认消息总线提供器不存在"),
                error_type: MessageBusErrorType::InvalidArgument,
            })
        }
    }
    
    fn list_subscriptions_from_provider(&self, provider_name: &str) -> Result<Vec<Subscription>, MessageBusError> {
        if let Some(provider) = self.providers.get(provider_name) {
            provider.list_subscriptions()
        } else {
            Err(MessageBusError {
                message: format!("消息总线提供器 {} 不存在", provider_name),
                error_type: MessageBusErrorType::InvalidArgument,
            })
        }
    }
    
    // 工具函数：发布序列化的值
    fn publish_value<T: serde::Serialize>(&self, topic: &str, value: &T, headers: Option<HashMap<String, String>>) -> Result<String, MessageBusError> {
        let data = serde_json::to_vec(value).map_err(|err| MessageBusError {
            message: format!("序列化值失败: {}", err),
            error_type: MessageBusErrorType::SerializationError,
        })?;
        
        self.publish(topic, &data, headers)
    }
    
    // 工具函数：订阅并反序列化消息
    fn subscribe_values<T, F>(&self, subscription_id: &str, topics: &[String], handler: F) -> Result<(), MessageBusError>
    where
        T: serde::de::DeserializeOwned + Send + 'static,
        F: Fn(T, HashMap<String, String>) -> Result<(), MessageBusError> + Send + Sync + 'static
    {
        self.subscribe(subscription_id, topics, move |message| {
            let value = serde_json::from_slice(&message.payload).map_err(|err| MessageBusError {
                message: format!("反序列化消息失败: {}", err),
                error_type: MessageBusErrorType::SerializationError,
            })?;
            
            handler(value, message.headers)
        })
    }
}

// 内存消息总线提供器
struct InMemoryMessageBusProvider {
    name: String,
    topics: Arc<RwLock<HashMap<String, Vec<Message>>>>,
    subscriptions: Arc<RwLock<HashMap<String, SubscriptionInfo>>>,
    worker_pool: ThreadPool,
}

struct SubscriptionInfo {
    id: String,
    topics: Vec<String>,
    handler: Arc<dyn Fn(Message) -> Result<(), MessageBusError> + Send + Sync>,
    created_at: SystemTime,
    last_active: SystemTime,
    message_count: Arc<AtomicU64>,
}

impl InMemoryMessageBusProvider {
    fn new(name: &str, num_workers: usize) -> Self {
        let provider = InMemoryMessageBusProvider {
            name: name.to_string(),
            topics: Arc::new(RwLock::new(HashMap::new())),
            subscriptions: Arc::new(RwLock::new(HashMap::new())),
            worker_pool: ThreadPool::new(num_workers),
        };
        
        // 启动消息分发线程
        let topics = provider.topics.clone();
        let subscriptions = provider.subscriptions.clone();
        let worker_pool = provider.worker_pool.clone();
        
        std::thread::spawn(move || {
            loop {
                // 检查所有主题的消息并分发给订阅者
                let mut messages_to_dispatch = Vec::new();
                
                {
                    let mut topics_lock = topics.write().unwrap();
                    
                    for (topic_name, messages) in topics_lock.iter_mut() {
                        if !messages.is_empty() {
                            // 收集待分发的消息
                            let mut topic_messages = Vec::new();
                            std::mem::swap(&mut topic_messages, messages);
                            
                            for message in topic_messages {
                                messages_to_dispatch.push((topic_name.clone(), message));
                            }
                        }
                    }
                }
                
                // 分发消息
                if !messages_to_dispatch.is_empty() {
                    let subscriptions_lock = subscriptions.read().unwrap();
                    
                    for (topic, message) in messages_to_dispatch {
                        for (_, subscription) in subscriptions_lock.iter() {
                            // 检查是否订阅了该主题
                            if subscription.topics.contains(&topic) || subscription.topics.contains(&"*".to_string()) {
                                // 克隆消息和处理器以便在线程池中使用
                                let message_clone = message.clone();
                                let handler = subscription.handler.clone();
                                let message_count = subscription.message_count.clone();
                                
                                // 分发消息到线程池
                                worker_pool.execute(move || {
                                    // 尝试处理消息
                                    if let Err(err) = handler(message_clone) {
                                        println!("消息处理失败: {}", err.message);
                                    } else {
                                        message_count.fetch_add(1, Ordering::SeqCst);
                                    }
                                });
                            }
                        }
                    }
                }
                
                // 暂停一小段时间
                std::thread::sleep(Duration::from_millis(10));
            }
        });
        
        provider
    }
}

impl MessageBusProvider for InMemoryMessageBusProvider {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn publish(&self, topic: &str, message: &[u8], headers: Option<HashMap<String, String>>) -> Result<String, MessageBusError> {
        let message_id = uuid::Uuid::new_v4().to_string();
        
        let message = Message {
            id: message_id.clone(),
            topic: topic.to_string(),
            payload: message.to_vec(),
            headers: headers.unwrap_or_default(),
            timestamp: SystemTime::now(),
            attempts: 0,
        };
        
        // 添加消息到主题
        let mut topics = self.topics.write().unwrap();
        
        if !topics.contains_key(topic) {
            topics.insert(topic.to_string(), Vec::new());
        }
        
        if let Some(messages) = topics.get_mut(topic) {
            messages.push(message);
        }
        
        Ok(message_id)
    }
    
    fn subscribe(&self, subscription_id: &str, topics: &[String], handler: Arc<dyn Fn(Message) -> Result<(), MessageBusError> + Send + Sync>) -> Result<(), MessageBusError> {
        let mut subscriptions = self.subscriptions.write().unwrap();
        
        if subscriptions.contains_key(subscription_id) {
            return Err(MessageBusError {
                message: format!("订阅ID {} 已存在", subscription_id),
                error_type: MessageBusErrorType::InvalidArgument,
            });
        }
        
        let subscription = SubscriptionInfo {
            id: subscription_id.to_string(),
            topics: topics.to_vec(),
            handler,
            created_at: SystemTime::now(),
            last_active: SystemTime::now(),
            message_count: Arc::new(AtomicU64::new(0)),
        };
        
        subscriptions.insert(subscription_id.to_string(), subscription);
        
        Ok(())
    }
    
    fn unsubscribe(&self, subscription_id: &str) -> Result<bool, MessageBusError> {
        let mut subscriptions = self.subscriptions.write().unwrap();
        
        Ok(subscriptions.remove(subscription_id).is_some())
    }
    
    fn list_topics(&self) -> Result<Vec<String>, MessageBusError> {
        let topics = self.topics.read().unwrap();
        let topic_names = topics.keys().cloned().collect();
        Ok(topic_names)
    }
    
    fn list_subscriptions(&self) -> Result<Vec<Subscription>, MessageBusError> {
        let subscriptions = self.subscriptions.read().unwrap();
        
        let result = subscriptions
            .values()
            .map(|sub| Subscription {
                id: sub.id.clone(),
                topics: sub.topics.clone(),
                created_at: sub.created_at,
                last_active: sub.last_active,
                message_count: sub.message_count.load(Ordering::SeqCst),
            })
            .collect();
        
        Ok(result)
    }
}

// 事件驱动架构
struct EventDrivenSystem {
    message_bus: Arc<DistributedMessageBus>,
    event_serializer: Arc<dyn Fn(&Event) -> Result<Vec<u8>, String> + Send + Sync>,
    event_deserializer: Arc<dyn Fn(&[u8]) -> Result<Event, String> + Send + Sync>,
}

struct Event {
    id: String,
    event_type: String,
    payload: serde_json::Value,
    source: String,
    timestamp: SystemTime,
    correlation_id: Option<String>,
    causation_id: Option<String>,
    metadata: HashMap<String, String>,
}

impl EventDrivenSystem {
    fn new(
        message_bus: Arc<DistributedMessageBus>,
        event_serializer: impl Fn(&Event) -> Result<Vec<u8>, String> + Send + Sync + 'static,
        event_deserializer: impl Fn(&[u8]) -> Result<Event, String> + Send + Sync + 'static
    ) -> Self {
        EventDrivenSystem {
            message_bus,
            event_serializer: Arc::new(event_serializer),
            event_deserializer: Arc::new(event_deserializer),
        }
    }
    
    fn publish_event(&self, event: &Event) -> Result<String, String> {
        // 序列化事件
        let event_data = (self.event_serializer)(event).map_err(|err| {
            format!("序列化事件失败: {}", err)
        })?;
        
        // 创建消息头信息
        let mut headers = HashMap::new();
        headers.insert("event_type".to_string(), event.event_type.clone());
        headers.insert("source".to_string(), event.source.clone());
        
        if let Some(correlation_id) = &event.correlation_id {
            headers.insert("correlation_id".to_string(), correlation_id.clone());
        }
        
        if let Some(causation_id) = &event.causation_id {
            headers.insert("causation_id".to_string(), causation_id.clone());
        }
        
        // 发布到消息总线
        let topic = format!("events.{}", event.event_type);
        self.message_bus.publish(&topic, &event_data, Some(headers))
            .map_err(|err| format!("发布事件失败: {}", err.message))
    }
    
    fn subscribe_to_events<F>(&self, subscription_id: &str, event_types: &[String], handler: F) -> Result<(), String>
    where
        F: Fn(Event) -> Result<(), String> + Send + Sync + 'static
    {
        // 转换事件类型为主题
        let topics = event_types.iter()
            .map(|event_type| format!("events.{}", event_type))
            .collect::<Vec<_>>();
        
        let event_deserializer = self.event_deserializer.clone();
        
        // 订阅消息总线
        self.message_bus.subscribe(
            subscription_id,
            &topics,
            move |message| {
                // 反序列化事件
                let event = event_deserializer(&message.payload)
                    .map_err(|err| MessageBusError {
                        message: format!("反序列化事件失败: {}", err),
                        error_type: MessageBusErrorType::SerializationError,
                    })?;
                
                // 调用处理器
                handler(event).map_err(|err| MessageBusError {
                    message: format!("事件处理失败: {}", err),
                    error_type: MessageBusErrorType::OperationFailed,
                })
            }
        ).map_err(|err| format!("订阅事件失败: {}", err.message))
    }
    
    fn create_event(&self, event_type: &str, payload: serde_json::Value, source: &str) -> Event {
        Event {
            id: uuid::Uuid::new_v4().to_string(),
            event_type: event_type.to_string(),
            payload,
            source: source.to_string(),
            timestamp: SystemTime::now(),
            correlation_id: None,
            causation_id: None,
            metadata: HashMap::new(),
        }
    }
    
    fn create_correlated_event(&self, event_type: &str, payload: serde_json::Value, source: &str, parent_event: &Event) -> Event {
        let mut event = self.create_event(event_type, payload, source);
        
        // 设置关联ID
        event.correlation_id = parent_event.correlation_id.clone().or(Some(parent_event.id.clone()));
        event.causation_id = Some(parent_event.id.clone());
        
        event
    }
}

// 事件溯源系统
struct EventSourcingSystem {
    event_store: Box<dyn EventStore>,
    event_bus: Arc<EventDrivenSystem>,
    snapshotter: Option<Box<dyn Snapshotter>>,
}

trait EventStore: Send + Sync {
    fn append_events(&self, aggregate_type: &str, aggregate_id: &str, events: &[Event], expected_version: Option<u64>) -> Result<u64, String>;
    fn get_events(&self, aggregate_type: &str, aggregate_id: &str, start_version: Option<u64>, end_version: Option<u64>) -> Result<Vec<Event>, String>;
    fn get_aggregate_version(&self, aggregate_type: &str, aggregate_id: &str) -> Result<Option<u64>, String>;
    fn get_events_by_type(&self, event_types: &[String], start_time: Option<SystemTime>, end_time: Option<SystemTime>, limit: Option<usize>) -> Result<Vec<Event>, String>;
}

trait Aggregate: Send + Sync {
    fn aggregate_type(&self) -> &str;
    fn id(&self) -> &str;
    fn version(&self) -> u64;
    fn apply_event(&mut self, event: &Event) -> Result<(), String>;
    fn create_snapshot(&self) -> Result<Snapshot, String>;
    fn restore_from_snapshot(&mut self, snapshot: &Snapshot) -> Result<(), String>;
}

struct Snapshot {
    aggregate_type: String,
    aggregate_id: String,
    version: u64,
    data: Vec<u8>,
    created_at: SystemTime,
}

trait Snapshotter: Send + Sync {
    fn save_snapshot(&self, snapshot: &Snapshot) -> Result<(), String>;
    fn get_latest_snapshot(&self, aggregate_type: &str, aggregate_id: &str) -> Result<Option<Snapshot>, String>;
}

impl EventSourcingSystem {
    fn new(event_store: Box<dyn EventStore>, event_bus: Arc<EventDrivenSystem>, snapshotter: Option<Box<dyn Snapshotter>>) -> Self {
        EventSourcingSystem {
            event_store,
            event_bus,
            snapshotter,
        }
    }
    
    fn save_events<A: Aggregate>(&self, aggregate: &mut A, new_events: &[Event]) -> Result<(), String> {
        if new_events.is_empty() {
            return Ok(());
        }
        
        let current_version = aggregate.version();
        
        // 将事件保存到事件存储
        let new_version = self.event_store.append_events(
            aggregate.aggregate_type(),
            aggregate.id(),
            new_events,
            Some(current_version)
        )?;
        
        // 应用事件到聚合
        for event in new_events {
            aggregate.apply_event(event)?;
        }
        
        // 发布事件到事件总线
        for event in new_events {
            if let Err(err) = self.event_bus.publish_event(event) {
                eprintln!("发布事件失败: {}", err);
            }
        }
        
        // 检查是否需要创建快照
        if let Some(snapshotter) = &self.snapshotter {
            if new_version % 10 == 0 {  // 每10个版本创建一次快照
                let snapshot = aggregate.create_snapshot()?;
                snapshotter.save_snapshot(&snapshot)?;
            }
        }
        
        Ok(())
    }
    
    fn load_aggregate<A: Aggregate + Default>(&self, aggregate_type: &str, aggregate_id: &str) -> Result<A, String> {
        let mut aggregate = A::default();
        
        // 尝试从快照加载
        let mut start_version = 0;
        if let Some(snapshotter) = &self.snapshotter {
            if let Some(snapshot) = snapshotter.get_latest_snapshot(aggregate_type, aggregate_id)? {
                aggregate.restore_from_snapshot(&snapshot)?;
                start_version = snapshot.version;
            }
        }
        
        // 加载剩余事件
        let events = self.event_store.get_events(aggregate_type, aggregate_id, Some(start_version), None)?;
        
        // 应用事件
        for event in &events {
            aggregate.apply_event(event)?;
        }
        
        Ok(aggregate)
    }
    
    fn get_event_history(&self, aggregate_type: &str, aggregate_id: &str) -> Result<Vec<Event>, String> {
        self.event_store.get_events(aggregate_type, aggregate_id, None, None)
    }
    
    fn find_events_by_type(&self, event_types: &[String], start_time: Option<SystemTime>, end_time: Option<SystemTime>, limit: Option<usize>) -> Result<Vec<Event>, String> {
        self.event_store.get_events_by_type(event_types, start_time, end_time, limit)
    }
}

// 命令处理系统
struct CommandProcessor {
    command_handlers: HashMap<String, Box<dyn Fn(&Command) -> Result<Vec<Event>, String> + Send + Sync>>,
    event_sourcing: Arc<EventSourcingSystem>,
}

struct Command {
    id: String,
    command_type: String,
    payload: serde_json::Value,
    metadata: HashMap<String, String>,
    timestamp: SystemTime,
}

impl CommandProcessor {
    fn new(event_sourcing: Arc<EventSourcingSystem>) -> Self {
        CommandProcessor {
            command_handlers: HashMap::new(),
            event_sourcing,
        }
    }
    
    fn register_handler<F>(&mut self, command_type: &str, handler: F)
    where
        F: Fn(&Command) -> Result<Vec<Event>, String> + Send + Sync + 'static
    {
        self.command_handlers.insert(command_type.to_string(), Box::new(handler));
    }
    
    fn process(&self, command: &Command) -> Result<Vec<Event>, String> {
        // 查找命令处理器
        if let Some(handler) = self.command_handlers.get(&command.command_type) {
            // 处理命令
            let events = handler(command)?;
            
            // TODO: 这里我们应该加载聚合并应用事件
            // 但由于我们没有聚合信息，所以简化处理
            
            // 返回生成的事件
            Ok(events)
        } else {
            Err(format!("未找到命令类型 {} 的处理器", command.command_type))
        }
    }
    
    fn create_command(&self, command_type: &str, payload: serde_json::Value) -> Command {
        Command {
            id: uuid::Uuid::new_v4().to_string(),
            command_type: command_type.to_string(),
            payload,
            metadata: HashMap::new(),
            timestamp: SystemTime::now(),
        }
    }
}

// CQRS：命令查询责任分离模式
struct CQRSFramework {
    command_bus: Arc<CommandBus>,
    query_bus: Arc<QueryBus>,
    event_sourcing: Option<Arc<EventSourcingSystem>>,
}

// 命令总线
struct CommandBus {
    handlers: RwLock<HashMap<String, Box<dyn CommandHandler>>>,
}

trait CommandHandler: Send + Sync {
    fn handle(&self, command: &Command) -> Result<CommandResult, CommandError>;
    fn command_type(&self) -> String;
}

struct CommandResult {
    success: bool,
    result_data: Option<serde_json::Value>,
    events: Vec<Event>,
}

struct CommandError {
    code: String,
    message: String,
    details: Option<serde_json::Value>,
}

// 查询总线
struct QueryBus {
    handlers: RwLock<HashMap<String, Box<dyn QueryHandler>>>,
}

trait QueryHandler: Send + Sync {
    fn handle(&self, query: &Query) -> Result<QueryResult, QueryError>;
    fn query_type(&self) -> String;
}

struct Query {
    id: String,
    query_type: String,
    parameters: serde_json::Value,
    metadata: HashMap<String, String>,
}

struct QueryResult {
    data: serde_json::Value,
    metadata: HashMap<String, String>,
}

struct QueryError {
    code: String,
    message: String,
    details: Option<serde_json::Value>,
}

impl CommandBus {
    fn new() -> Self {
        CommandBus {
            handlers: RwLock::new(HashMap::new()),
        }
    }
    
    fn register_handler<H: CommandHandler + 'static>(&self, handler: H) -> Result<(), String> {
        let mut handlers = self.handlers.write().unwrap();
        let command_type = handler.command_type();
        
        if handlers.contains_key(&command_type) {
            return Err(format!("命令处理器已存在: {}", command_type));
        }
        
        handlers.insert(command_type, Box::new(handler));
        Ok(())
    }
    
    fn dispatch(&self, command: &Command) -> Result<CommandResult, CommandError> {
        let handlers = self.handlers.read().unwrap();
        
        if let Some(handler) = handlers.get(&command.command_type) {
            handler.handle(command)
        } else {
            Err(CommandError {
                code: "HANDLER_NOT_FOUND".to_string(),
                message: format!("未找到命令类型 {} 的处理器", command.command_type),
                details: None,
            })
        }
    }
}

impl QueryBus {
    fn new() -> Self {
        QueryBus {
            handlers: RwLock::new(HashMap::new()),
        }
    }
    
    fn register_handler<H: QueryHandler + 'static>(&self, handler: H) -> Result<(), String> {
        let mut handlers = self.handlers.write().unwrap();
        let query_type = handler.query_type();
        
        if handlers.contains_key(&query_type) {
            return Err(format!("查询处理器已存在: {}", query_type));
        }
        
        handlers.insert(query_type, Box::new(handler));
        Ok(())
    }
    
    fn dispatch(&self, query: &Query) -> Result<QueryResult, QueryError> {
        let handlers = self.handlers.read().unwrap();
        
        if let Some(handler) = handlers.get(&query.query_type) {
            handler.handle(query)
        } else {
            Err(QueryError {
                code: "HANDLER_NOT_FOUND".to_string(),
                message: format!("未找到查询类型 {} 的处理器", query.query_type),
                details: None,
            })
        }
    }
}

impl CQRSFramework {
    fn new(command_bus: Arc<CommandBus>, query_bus: Arc<QueryBus>) -> Self {
        CQRSFramework {
            command_bus,
            query_bus,
            event_sourcing: None,
        }
    }
    
    fn with_event_sourcing(mut self, event_sourcing: Arc<EventSourcingSystem>) -> Self {
        self.event_sourcing = Some(event_sourcing);
        self
    }
    
    fn execute_command(&self, command: &Command) -> Result<CommandResult, CommandError> {
        let result = self.command_bus.dispatch(command);
        
        if let Ok(ref command_result) = result {
            // 如果启用了事件溯源，发布事件
            if let Some(event_sourcing) = &self.event_sourcing {
                for event in &command_result.events {
                    if let Err(err) = event_sourcing.event_bus.publish_event(event) {
                        eprintln!("发布事件失败: {}", err);
                    }
                }
            }
        }
        
        result
    }
    
    fn execute_query(&self, query: &Query) -> Result<QueryResult, QueryError> {
        self.query_bus.dispatch(query)
    }
    
    fn create_command(&self, command_type: &str, payload: serde_json::Value) -> Command {
        Command {
            id: uuid::Uuid::new_v4().to_string(),
            command_type: command_type.to_string(),
            payload,
            metadata: HashMap::new(),
            timestamp: SystemTime::now(),
        }
    }
    
    fn create_query(&self, query_type: &str, parameters: serde_json::Value) -> Query {
        Query {
            id: uuid::Uuid::new_v4().to_string(),
            query_type: query_type.to_string(),
            parameters,
            metadata: HashMap::new(),
        }
    }
}

// 容错机制：断路器模式
struct CircuitBreaker {
    name: String,
    state: Arc<RwLock<CircuitState>>,
    failure_threshold: u32,
    success_threshold: u32,
    reset_timeout: Duration,
    half_open_timeout: Duration,
    failure_count: Arc<AtomicU32>,
    success_count: Arc<AtomicU32>,
    last_failure_time: Arc<Mutex<Option<Instant>>>,
    last_success_time: Arc<Mutex<Option<Instant>>>,
    listeners: Arc<RwLock<Vec<Box<dyn Fn(CircuitBreakerEvent) + Send + Sync>>>>,
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum CircuitState {
    Closed,      // 正常工作
    Open,        // 断路，所有请求快速失败
    HalfOpen,    // 半开状态，允许有限数量的请求通过
}

struct CircuitBreakerEvent {
    breaker_name: String,
    old_state: CircuitState,
    new_state: CircuitState,
    timestamp: Instant,
    trip_count: u64,
}

impl CircuitBreaker {
    fn new(name: &str, failure_threshold: u32, reset_timeout: Duration) -> Self {
        CircuitBreaker {
            name: name.to_string(),
            state: Arc::new(RwLock::new(CircuitState::Closed)),
            failure_threshold,
            success_threshold: 1,
            reset_timeout,
            half_open_timeout: Duration::from_secs(5),
            failure_count: Arc::new(AtomicU32::new(0)),
            success_count: Arc::new(AtomicU32::new(0)),
            last_failure_time: Arc::new(Mutex::new(None)),
            last_success_time: Arc::new(Mutex::new(None)),
            listeners: Arc::new(RwLock::new(Vec::new())),
        }
    }
    
    fn with_success_threshold(mut self, threshold: u32) -> Self {
        self.success_threshold = threshold;
        self
    }
    
    fn with_half_open_timeout(mut self, timeout: Duration) -> Self {
        self.half_open_timeout = timeout;
        self
    }
    
    fn add_listener<F>(&self, listener: F)
    where
        F: Fn(CircuitBreakerEvent) + Send + Sync + 'static
    {
        let mut listeners = self.listeners.write().unwrap();
        listeners.push(Box::new(listener));
    }
    
    fn execute<F, T, E>(&self, func: F) -> Result<T, E>
    where
        F: FnOnce() -> Result<T, E>,
        E: std::fmt::Debug,
    {
        // 检查是否应该允许执行
        if !self.allow_request() {
            panic!("断路器已打开: {}", self.name);
        }
        
        // 执行函数
        match func() {
            Ok(result) => {
                self.on_success();
                Ok(result)
            },
            Err(error) => {
                self.on_failure();
                Err(error)
            }
        }
    }
    
    fn allow_request(&self) -> bool {
        let state = *self.state.read().unwrap();
        
        match state {
            CircuitState::Closed => true,
            CircuitState::Open => {
                // 检查是否应该转换到半开状态
                let mut last_failure = self.last_failure_time.lock().unwrap();
                
                if let Some(time) = *last_failure {
                    if time.elapsed() >= self.reset_timeout {
                        // 转换到半开状态
                        self.transit_to(CircuitState::HalfOpen);
                        return true;
                    }
                }
                
                false
            },
            CircuitState::HalfOpen => {
                // 在半开状态下，只允许有限的请求
                true
            }
        }
    }
    
    fn on_success(&self) {
        let state = *self.state.read().unwrap();
        
        // 更新最后成功时间
        let mut last_success = self.last_success_time.lock().unwrap();
        *last_success = Some(Instant::now());
        
        match state {
            CircuitState::Closed => {
                // 在关闭状态下重置失败计数
                self.failure_count.store(0, Ordering::SeqCst);
            },
            CircuitState::HalfOpen => {
                // 在半开状态下，增加成功计数
                let prev_count = self.success_count.fetch_add(1, Ordering::SeqCst);
                
                if prev_count + 1 >= self.success_threshold {
                    // 转换到关闭状态
                    self.transit_to(CircuitState::Closed);
                    self.success_count.store(0, Ordering::SeqCst);
                    self.failure_count.store(0, Ordering::SeqCst);
                }
            },
            _ => {}
        }
    }
    
    fn on_failure(&self) {
        let state = *self.state.read().unwrap();
        
        // 更新最后失败时间
        let mut last_failure = self.last_failure_time.lock().unwrap();
        *last_failure = Some(Instant::now());
        
        match state {
            CircuitState::Closed => {
                // 在关闭状态下增加失败计数
                let prev_count = self.failure_count.fetch_add(1, Ordering::SeqCst);
                
                if prev_count + 1 >= self.failure_threshold {
                    // 转换到打开状态
                    self.transit_to(CircuitState::Open);
                }
            },
            CircuitState::HalfOpen => {
                // 在半开状态下，任何失败都会导致回到打开状态
                self.transit_to(CircuitState::Open);
                self.success_count.store(0, Ordering::SeqCst);
            },
            _ => {}
        }
    }
    
    fn transit_to(&self, new_state: CircuitState) {
        let mut state = self.state.write().unwrap();
        let old_state = *state;
        
        if old_state != new_state {
            *state = new_state;
            
            // 触发事件
            let event = CircuitBreakerEvent {
                breaker_name: self.name.clone(),
                old_state,
                new_state,
                timestamp: Instant::now(),
                trip_count: 0, // TODO: 跟踪断路次数
            };
            
            // 通知监听器
            let listeners = self.listeners.read().unwrap();
            for listener in listeners.iter() {
                listener(event.clone());
            }
        }
    }
    
    fn get_state(&self) -> CircuitState {
        *self.state.read().unwrap()
    }
    
    fn reset(&self) {
        self.transit_to(CircuitState::Closed);
        self.failure_count.store(0, Ordering::SeqCst);
        self.success_count.store(0, Ordering::SeqCst);
    }
}

// 重试机制
struct RetryPolicy {
    max_attempts: u32,
    initial_backoff: Duration,
    backoff_multiplier: f64,
    max_backoff: Duration,
    jitter: bool,
}

impl RetryPolicy {
    fn new(max_attempts: u32, initial_backoff: Duration) -> Self {
        RetryPolicy {
            max_attempts,
            initial_backoff,
            backoff_multiplier: 2.0,
            max_backoff: Duration::from_secs(60),
            jitter: true,
        }
    }
    
    fn with_backoff_multiplier(mut self, multiplier: f64) -> Self {
        self.backoff_multiplier = multiplier;
        self
    }
    
    fn with_max_backoff(mut self, max_backoff: Duration) -> Self {
        self.max_backoff = max_backoff;
        self
    }
    
    fn with_jitter(mut self, jitter: bool) -> Self {
        self.jitter = jitter;
        self
    }
    
    fn calculate_backoff(&self, attempt: u32) -> Duration {
        if attempt == 0 {
            return Duration::from_millis(0);
        }
        
        let mut backoff = self.initial_backoff.as_millis() as f64 * self.backoff_multiplier.powi(attempt as i32 - 1);
        backoff = backoff.min(self.max_backoff.as_millis() as f64);
        
        if self.jitter {
            let jitter_factor = rand::random::<f64>() * 0.25 + 0.75; // 75% to 100% of original
            backoff *= jitter_factor;
        }
        
        Duration::from_millis(backoff as u64)
    }
    
    fn execute<F, T, E>(&self, operation: F) -> Result<T, E>
    where
        F: Fn() -> Result<T, E>,
        E: std::fmt::Debug,
    {
        let mut attempt = 0;
        
        loop {
            attempt += 1;
            
            match operation() {
                Ok(result) => return Ok(result),
                Err(error) => {
                    if attempt >= self.max_attempts {
                        return Err(error);
                    }
                    
                    let backoff = self.calculate_backoff(attempt);
                    std::thread::sleep(backoff);
                }
            }
        }
    }
    
    fn execute_with_check<F, C, T, E>(&self, operation: F, should_retry: C) -> Result<T, E>
    where
        F: Fn() -> Result<T, E>,
        C: Fn(&E) -> bool,
        E: std::fmt::Debug,
    {
        let mut attempt = 0;
        
        loop {
            attempt += 1;
            
            match operation() {
                Ok(result) => return Ok(result),
                Err(error) => {
                    if attempt >= self.max_attempts || !should_retry(&error) {
                        return Err(error);
                    }
                    
                    let backoff = self.calculate_backoff(attempt);
                    std::thread::sleep(backoff);
                }
            }
        }
    }
    
    // 异步版本的重试（为异步代码设计）
    async fn execute_async<F, Fut, T, E>(&self, operation: F) -> Result<T, E>
    where
        F: Fn() -> Fut,
        Fut: std::future::Future<Output = Result<T, E>>,
        E: std::fmt::Debug,
    {
        let mut attempt = 0;
        
        loop {
            attempt += 1;
            
            match operation().await {
                Ok(result) => return Ok(result),
                Err(error) => {
                    if attempt >= self.max_attempts {
                        return Err(error);
                    }
                    
                    let backoff = self.calculate_backoff(attempt);
                    tokio::time::sleep(backoff).await;
                }
            }
        }
    }
}

// 超时处理
struct Timeout {
    duration: Duration,
}

impl Timeout {
    fn new(duration: Duration) -> Self {
        Timeout { duration }
    }
    
    // 同步版本的超时（使用线程）
    fn execute<F, T>(&self, operation: F) -> Result<T, String>
    where
        F: FnOnce() -> T + Send + 'static,
        T: Send + 'static,
    {
        let (tx, rx) = std::sync::mpsc::channel();
        
        // 在新线程中执行操作
        let handle = std::thread::spawn(move || {
            let result = operation();
            let _ = tx.send(result);
        });
        
        // 等待结果或超时
        match rx.recv_timeout(self.duration) {
            Ok(result) => Ok(result),
            Err(_) => {
                // 超时了，但我们不能取消线程，只能让它继续运行
                // 在实际应用中，可能需要更复杂的取消机制
                Err("操作超时".to_string())
            }
        }
    }
    
    // 异步版本的超时（为异步代码设计）
    async fn execute_async<F, Fut, T>(&self, operation: F) -> Result<T, String>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = T>,
    {
        use tokio::time::timeout;
        
        match timeout(self.duration, operation()).await {
            Ok(result) => Ok(result),
            Err(_) => Err("操作超时".to_string()),
        }
    }
}

// 容错模式：舱壁模式（隔离故障）
struct Bulkhead {
    name: String,
    max_concurrent_calls: u32,
    max_wait_duration: Duration,
    active_calls: Arc<AtomicU32>,
    semaphore: Arc<tokio::sync::Semaphore>,
}

impl Bulkhead {
    fn new(name: &str, max_concurrent_calls: u32, max_wait_duration: Duration) -> Self {
        Bulkhead {
            name: name.to_string(),
            max_concurrent_calls,
            max_wait_duration,
            active_calls: Arc::new(AtomicU32::new(0)),
            semaphore: Arc::new(tokio::sync::Semaphore::new(max_concurrent_calls as usize)),
        }
    }
    
    // 同步版本
    fn execute<F, T>(&self, operation: F) -> Result<T, String>
    where
        F: FnOnce() -> Result<T, String>,
    {
        // 尝试获取许可
        if self.active_calls.load(Ordering::SeqCst) >= self.max_concurrent_calls {
            return Err(format!("舱壁 {} 已满", self.name));
        }
        
        // 增加活动调用计数
        self.active_calls.fetch_add(1, Ordering::SeqCst);
        
        let result = operation();
        
        // 减少活动调用计数
        self.active_calls.fetch_sub(1, Ordering::SeqCst);
        
        result
    }
    
    // 异步版本
    async fn execute_async<F, Fut, T, E>(&self, operation: F) -> Result<T, E>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = Result<T, E>>,
        E: From<String>,
    {
        // 尝试获取许可
        let permit = match tokio::time::timeout(
            self.max_wait_duration,
            self.semaphore.acquire()
        ).await {
            Ok(Ok(permit)) => permit,
            Ok(Err(_)) => return Err(format!("舱壁 {} 已损坏", self.name).into()),
            Err(_) => return Err(format!("舱壁 {} 等待超时", self.name).into()),
        };
        
        // 执行操作
        let result = operation().await;
        
        // 释放许可
        drop(permit);
        
        result
    }
    
    fn get_metrics(&self) -> BulkheadMetrics {
        BulkheadMetrics {
            name: self.name.clone(),
            max_concurrent_calls: self.max_concurrent_calls,
            active_calls: self.active_calls.load(Ordering::SeqCst),
            available_calls: self.max_concurrent_calls - self.active_calls.load(Ordering::SeqCst),
        }
    }
}

struct BulkheadMetrics {
    name: String,
    max_concurrent_calls: u32,
    active_calls: u32,
    available_calls: u32,
}

// 容错模式管理器
struct ResilienceManager {
    circuit_breakers: RwLock<HashMap<String, Arc<CircuitBreaker>>>,
    bulkheads: RwLock<HashMap<String, Arc<Bulkhead>>>,
    retry_policies: RwLock<HashMap<String, Arc<RetryPolicy>>>,
    timeouts: RwLock<HashMap<String, Arc<Timeout>>>,
}

impl ResilienceManager {
    fn new() -> Self {
        ResilienceManager {
            circuit_breakers: RwLock::new(HashMap::new()),
            bulkheads: RwLock::new(HashMap::new()),
            retry_policies: RwLock::new(HashMap::new()),
            timeouts: RwLock::new(HashMap::new()),
        }
    }
    
    fn register_circuit_breaker(&self, name: &str, circuit_breaker: Arc<CircuitBreaker>) -> Result<(), String> {
        let mut breakers = self.circuit_breakers.write().unwrap();
        
        if breakers.contains_key(name) {
            return Err(format!("断路器 {} 已存在", name));
        }
        
        breakers.insert(name.to_string(), circuit_breaker);
        Ok(())
    }
    
    fn register_bulkhead(&self, name: &str, bulkhead: Arc<Bulkhead>) -> Result<(), String> {
        let mut bulkheads = self.bulkheads.write().unwrap();
        
        if bulkheads.contains_key(name) {
            return Err(format!("舱壁 {} 已存在", name));
        }
        
        bulkheads.insert(name.to_string(), bulkhead);
        Ok(())
    }
    
    fn register_retry_policy(&self, name: &str, retry_policy: Arc<RetryPolicy>) -> Result<(), String> {
        let mut policies = self.retry_policies.write().unwrap();
        
        if policies.contains_key(name) {
            return Err(format!("重试策略 {} 已存在", name));
        }
        
        policies.insert(name.to_string(), retry_policy);
        Ok(())
    }
    
    fn register_timeout(&self, name: &str, timeout: Arc<Timeout>) -> Result<(), String> {
        let mut timeouts = self.timeouts.write().unwrap();
        
        if timeouts.contains_key(name) {
            return Err(format!("超时 {} 已存在", name));
        }
        
        timeouts.insert(name.to_string(), timeout);
        Ok(())
    }
    
    fn get_circuit_breaker(&self, name: &str) -> Option<Arc<CircuitBreaker>> {
        let breakers = self.circuit_breakers.read().unwrap();
        breakers.get(name).cloned()
    }
    
    fn get_bulkhead(&self, name: &str) -> Option<Arc<Bulkhead>> {
        let bulkheads = self.bulkheads.read().unwrap();
        bulkheads.get(name).cloned()
    }
    
    fn get_retry_policy(&self, name: &str) -> Option<Arc<RetryPolicy>> {
        let policies = self.retry_policies.read().unwrap();
        policies.get(name).cloned()
    }
    
    fn get_timeout(&self, name: &str) -> Option<Arc<Timeout>> {
        let timeouts = self.timeouts.read().unwrap();
        timeouts.get(name).cloned()
    }
    
    // 组合多种容错策略
    fn execute_with_resilience<F, T, E>(
        &self,
        circuit_breaker_name: Option<&str>,
        bulkhead_name: Option<&str>,
        retry_policy_name: Option<&str>,
        timeout_name: Option<&str>,
        operation: F
    ) -> Result<T, E>
    where
        F: Fn() -> Result<T, E> + Clone,
        E: std::fmt::Debug + From<String>,
    {
        let operation_with_timeout = if let Some(name) = timeout_name {
            if let Some(timeout) = self.get_timeout(name) {
                let op = operation.clone();
                Box::new(move || timeout.execute(|| op()).map_err(E::from).and_then(|r| r)) as Box<dyn Fn() -> Result<T, E>>
            } else {
                Box::new(operation.clone())
            }
        } else {
            Box::new(operation.clone())
        };
        
        let operation_with_bulkhead = if let Some(name) = bulkhead_name {
            if let Some(bulkhead) = self.get_bulkhead(name) {
                let op = operation_with_timeout.clone();
                Box::new(move || bulkhead.execute(|| op()).map_err(E::from).and_then(|r| r)) as Box<dyn Fn() -> Result<T, E>>
            } else {
                operation_with_timeout
            }
        } else {
            operation_with_timeout
        };
        
        let operation_with_retry = if let Some(name) = retry_policy_name {
            if let Some(retry_policy) = self.get_retry_policy(name) {
                let op = operation_with_bulkhead.clone();
                Box::new(move || retry_policy.execute(|| op())) as Box<dyn Fn() -> Result<T, E>>
            } else {
                operation_with_bulkhead
            }
        } else {
            operation_with_bulkhead
        };
        
        let operation_with_circuit_breaker = if let Some(name) = circuit_breaker_name {
            if let Some(circuit_breaker) = self.get_circuit_breaker(name) {
                let op = operation_with_retry.clone();
                Box::new(move || circuit_breaker.execute(|| op())) as Box<dyn Fn() -> Result<T, E>>
            } else {
                operation_with_retry
            }
        } else {
            operation_with_retry
        };
        
        operation_with_circuit_breaker()
    }
}

// 分布式跟踪
struct DistributedTracer {
    tracer_name: String,
    sampler: Box<dyn Sampler>,
    spans: RwLock<HashMap<String, Arc<Span>>>,
    active_spans: thread_local!(static ACTIVE_SPANS: RefCell<Vec<Arc<Span>>> = RefCell::new(Vec::new()));
    propagator: Box<dyn Propagator>,
    reporter: Box<dyn Reporter>,
}

trait Sampler: Send + Sync {
    fn should_sample(&self, operation_name: &str, trace_id: &str) -> bool;
}

struct ConstSampler {
    decision: bool,
}

impl Sampler for ConstSampler {
    fn should_sample(&self, _operation_name: &str, _trace_id: &str) -> bool {
        self.decision
    }
}

struct RateLimitingSampler {
    max_traces_per_second: f64,
    last_tick: Mutex<Instant>,
    balance: Mutex<f64>,
    max_balance: f64,
}

impl Sampler for RateLimitingSampler {
    fn should_sample(&self, _operation_name: &str, _trace_id: &str) -> bool {
        let mut last_tick = self.last_tick.lock().unwrap();
        let mut balance = self.balance.lock().unwrap();
        
        let tick = Instant::now();
        let elapsed = tick.duration_since(*last_tick).as_secs_f64();
        *last_tick = tick;
        
        // 添加时间流逝期间积累的点数
        *balance += elapsed * self.max_traces_per_second;
        
        // 限制最大积累点数
        if *balance > self.max_balance {
            *balance = self.max_balance;
        }
        
        if *balance >= 1.0 {
            *balance -= 1.0;
            true
        } else {
            false
        }
    }
}

struct Span {
    span_id: String,
    trace_id: String,
    parent_span_id: Option<String>,
    operation_name: String,
    start_time: SystemTime,
    end_time: Option<SystemTime>,
    tags: RwLock<HashMap<String, String>>,
    logs: RwLock<Vec<LogEntry>>,
    is_finished: AtomicBool,
    references: Vec<SpanReference>,
}

enum SpanReference {
    ChildOf(String),
    FollowsFrom(String),
}

struct LogEntry {
    timestamp: SystemTime,
    fields: HashMap<String, String>,
}

trait Propagator: Send + Sync {
    fn inject(&self, span_context: &SpanContext, carrier: &mut dyn PropagationCarrier);
    fn extract(&self, carrier: &dyn PropagationCarrier) -> Option<SpanContext>;
}

trait PropagationCarrier {
    fn get(&self, key: &str) -> Option<&str>;
    fn set(&mut self, key: &str, value: &str);
    fn keys(&self) -> Vec<&str>;
}

struct SpanContext {
    trace_id: String,
    span_id: String,
    baggage_items: HashMap<String, String>,
}

trait Reporter: Send + Sync {
    fn report(&self, span: &Span);
    fn close(&self);
}

impl DistributedTracer {
    fn new(
        tracer_name: &str,
        sampler: Box<dyn Sampler>,
        propagator: Box<dyn Propagator>,
        reporter: Box<dyn Reporter>
    ) -> Self {
        DistributedTracer {
            tracer_name: tracer_name.to_string(),
            sampler,
            spans: RwLock::new(HashMap::new()),
            propagator,
            reporter,
        }
    }
    
    fn start_span(&self, operation_name: &str) -> Arc<Span> {
        self.start_span_with_options(operation_name, None, Vec::new())
    }
    
    fn start_span_with_options(
        &self,
        operation_name: &str,
        parent_span: Option<Arc<Span>>,
        references: Vec<SpanReference>
    ) -> Arc<Span> {
        // 生成跟踪ID和跨度ID
        let span_id = uuid::Uuid::new_v4().to_string();
        let trace_id = if let Some(parent) = &parent_span {
            parent.trace_id.clone()
        } else {
            uuid::Uuid::new_v4().to_string()
        };
        
        // 确定父跨度ID
        let parent_span_id = parent_span.map(|span| span.span_id.clone());
        
        // 决定是否采样
        if !self.sampler.should_sample(operation_name, &trace_id) {
            // 创建一个不记录的跨度
            // 在真实实现中，这应该是一个特殊的空操作跨度
            // 简化：我们仍然返回一个完整的跨度但不报告它
        }
        
        // 创建新跨度
        let span = Arc::new(Span {
            span_id,
            trace_id,
            parent_span_id,
            operation_name: operation_name.to_string(),
            start_time: SystemTime::now(),
            end_time: None,
            tags: RwLock::new(HashMap::new()),
            logs: RwLock::new(Vec::new()),
            is_finished: AtomicBool::new(false),
            references,
        });
        
        // 存储跨度
        {
            let mut spans = self.spans.write().unwrap();
            spans.insert(span.span_id.clone(), span.clone());
        }
        
        // 设置为当前活动跨度
        Self::active_spans.with(|active_spans| {
            active_spans.borrow_mut().push(span.clone());
        });
        
        span
    }
    
    fn finish_span(&self, span: &Arc<Span>) {
        if span.is_finished.swap(true, Ordering::SeqCst) {
            // 跨度已经完成
            return;
        }
        
        // 设置结束时间
        span.end_time = Some(SystemTime::now());
        
        // 从活动跨度中移除
        Self::active_spans.with(|active_spans| {
            let mut spans = active_spans.borrow_mut();
            if let Some(pos) = spans.iter().position(|s| s.span_id == span.span_id) {
                spans.remove(pos);
            }
        });
        
        // 报告跨度
        self.reporter.report(span);
    }
    
    fn get_active_span(&self) -> Option<Arc<Span>> {
        Self::active_spans.with(|active_spans| {
            active_spans.borrow().last().cloned()
        })
    }
    
    fn set_tag(&self, span: &Arc<Span>, key: &str, value: &str) {
        let mut tags = span.tags.write().unwrap();
        tags.insert(key.to_string(), value.to_string());
    }
    
    fn log_kv(&self, span: &Arc<Span>, fields: HashMap<String, String>) {
        let log_entry = LogEntry {
            timestamp: SystemTime::now(),
            fields,
        };
        
        let mut logs = span.logs.write().unwrap();
        logs.push(log_entry);
    }
    
    fn inject(&self, span: &Arc<Span>, carrier: &mut dyn PropagationCarrier) {
        let context = SpanContext {
            trace_id: span.trace_id.clone(),
            span_id: span.span_id.clone(),
            baggage_items: HashMap::new(), // 这里简化了，没有实现行李项
        };
        
        self.propagator.inject(&context, carrier);
    }
    
    fn extract(&self, carrier: &dyn PropagationCarrier) -> Option<SpanContext> {
        self.propagator.extract(carrier)
    }
    
    fn join_trace(&self, operation_name: &str, context: SpanContext) -> Arc<Span> {
        // 创建一个加入现有跟踪的新跨度
        let span_id = uuid::Uuid::new_v4().to_string();
        
        let span = Arc::new(Span {
            span_id,
            trace_id: context.trace_id,
            parent_span_id: Some(context.span_id),
            operation_name: operation_name.to_string(),
            start_time: SystemTime::now(),
            end_time: None,
            tags: RwLock::new(HashMap::new()),
            logs: RwLock::new(Vec::new()),
            is_finished: AtomicBool::new(false),
            references: vec![SpanReference::ChildOf(context.span_id.clone())],
        });
        
        // 存储跨度
        {
            let mut spans = self.spans.write().unwrap();
            spans.insert(span.span_id.clone(), span.clone());
        }
        
        // 设置为当前活动跨度
        Self::active_spans.with(|active_spans| {
            active_spans.borrow_mut().push(span.clone());
        });
        
        span
    }
    
    fn close(&self) {
        self.reporter.close();
    }
}

// 分布式度量系统
struct MetricsRegistry {
    metrics: RwLock<HashMap<String, Arc<dyn Metric>>>,
    tags: RwLock<HashMap<String, String>>,
    reporters: RwLock<Vec<Box<dyn MetricReporter>>>,
}

trait Metric: Send + Sync {
    fn name(&self) -> &str;
    fn metric_type(&self) -> MetricType;
    fn description(&self) -> &str;
    fn tags(&self) -> HashMap<String, String>;
    fn reset(&self);
}

enum MetricType {
    Counter,
    Gauge,
    Histogram,
    Timer,
    Meter,
}

trait MetricReporter: Send + Sync {
    fn report_counter(&self, counter: &Counter);
    fn report_gauge(&self, gauge: &Gauge);
    fn report_histogram(&self, histogram: &Histogram);
    fn report_timer(&self, timer: &Timer);
    fn report_meter(&self, meter: &Meter);
    fn report_all(&self, registry: &MetricsRegistry);
}

struct Counter {
    name: String,
    description: String,
    tags: RwLock<HashMap<String, String>>,
    value: AtomicU64,
}

impl Counter {
    fn new(name: &str, description: &str) -> Self {
        Counter {
            name: name.to_string(),
            description: description.to_string(),
            tags: RwLock::new(HashMap::new()),
            value: AtomicU64::new(0),
        }
    }
    
    fn with_tags(mut self, tags: HashMap<String, String>) -> Self {
        *self.tags.write().unwrap() = tags;
        self
    }
    
    fn increment(&self) {
        self.value.fetch_add(1, Ordering::SeqCst);
    }
    
    fn increment_by(&self, amount: u64) {
        self.value.fetch_add(amount, Ordering::SeqCst);
    }
    
    fn decrement(&self) {
        self.value.fetch_sub(1, Ordering::SeqCst);
    }
    
    fn decrement_by(&self, amount: u64) {
        self.value.fetch_sub(amount, Ordering::SeqCst);
    }
    
    fn get(&self) -> u64 {
        self.value.load(Ordering::SeqCst)
    }
}

impl Metric for Counter {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn metric_type(&self) -> MetricType {
        MetricType::Counter
    }
    
    fn description(&self) -> &str {
        &self.description
    }
    
    fn tags(&self) -> HashMap<String, String> {
        self.tags.read().unwrap().clone()
    }
    
    fn reset(&self) {
        self.value.store(0, Ordering::SeqCst);
    }
}

struct Gauge {
    name: String,
    description: String,
    tags: RwLock<HashMap<String, String>>,
    value: AtomicU64,
}

impl Gauge {
    fn new(name: &str, description: &str) -> Self {
        Gauge {
            name: name.to_string(),
            description: description.to_string(),
            tags: RwLock::new(HashMap::new()),
            value: AtomicU64::new(0),
        }
    }
    
    fn with_tags(mut self, tags: HashMap<String, String>) -> Self {
        *self.tags.write().unwrap() = tags;
        self
    }
    
    fn set(&self, value: u64) {
        self.value.store(value, Ordering::SeqCst);
    }
    
    fn get(&self) -> u64 {
        self.value.load(Ordering::SeqCst)
    }
    
    fn update<F>(&self, f: F)
    where
        F: Fn(u64) -> u64,
    {
        let mut current = self.value.load(Ordering::SeqCst);
        loop {
            let new_value = f(current);
            match self.value.compare_exchange(
                current,
                new_value,
                Ordering::SeqCst,
                Ordering::SeqCst,
            ) {
                Ok(_) => break,
                Err(val) => current = val,
            }
        }
    }
}

impl Metric for Gauge {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn metric_type(&self) -> MetricType {
        MetricType::Gauge
    }
    
    fn description(&self) -> &str {
        &self.description
    }
    
    fn tags(&self) -> HashMap<String, String> {
        self.tags.read().unwrap().clone()
    }
    
    fn reset(&self) {
        self.value.store(0, Ordering::SeqCst);
    }
}

struct Histogram {
    name: String,
    description: String,
    tags: RwLock<HashMap<String, String>>,
    values: Mutex<Vec<u64>>,
    count: AtomicU64,
    sum: AtomicU64,
    min: AtomicU64,
    max: AtomicU64,
}

impl Histogram {
    fn new(name: &str, description: &str) -> Self {
        Histogram {
            name: name.to_string(),
            description: description.to_string(),
            tags: RwLock::new(HashMap::new()),
            values: Mutex::new(Vec::new()),
            count: AtomicU64::new(0),
            sum: AtomicU64::new(0),
            min: AtomicU64::new(u64::MAX),
            max: AtomicU64::new(0),
        }
    }
    
    fn with_tags(mut self, tags: HashMap<String, String>) -> Self {
        *self.tags.write().unwrap() = tags;
        self
    }
    
    fn update(&self, value: u64) {
        self.count.fetch_add(1, Ordering::SeqCst);
        self.sum.fetch_add(value, Ordering::SeqCst);
        
        // 更新最小值
        let mut current_min = self.min.load(Ordering::SeqCst);
        while value < current_min {
            match self.min.compare_exchange(
                current_min,
                value,
                Ordering::SeqCst,
                Ordering::SeqCst,
            ) {
                Ok(_) => break,
                Err(val) => current_min = val,
            }
        }
        
        // 更新最大值
        let mut current_max = self.max.load(Ordering::SeqCst);
        while value > current_max {
            match self.max.compare_exchange(
                current_max,
                value,
                Ordering::SeqCst,
                Ordering::SeqCst,
            ) {
                Ok(_) => break,
                Err(val) => current_max = val,
            }
        }
        
        // 记录值
        let mut values = self.values.lock().unwrap();
        values.push(value);
    }
    
    fn count(&self) -> u64 {
        self.count.load(Ordering::SeqCst)
    }
    
    fn sum(&self) -> u64 {
        self.sum.load(Ordering::SeqCst)
    }
    
    fn min(&self) -> u64 {
        self.min.load(Ordering::SeqCst)
    }
    
    fn max(&self) -> u64 {
        self.max.load(Ordering::SeqCst)
    }
    
    fn mean(&self) -> f64 {
        let count = self.count.load(Ordering::SeqCst);
        if count == 0 {
            return 0.0;
        }
        self.sum.load(Ordering::SeqCst) as f64 / count as f64
    }
    
    fn percentile(&self, p: f64) -> u64 {
        let values = self.values.lock().unwrap();
        if values.is_empty() {
            return 0;
        }
        
        let mut sorted_values = values.clone();
        sorted_values.sort();
        
        let index = (p * sorted_values.len() as f64).floor() as usize;
        sorted_values[index.min(sorted_values.len() - 1)]
    }
}

impl Metric for Histogram {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn metric_type(&self) -> MetricType {
        MetricType::Histogram
    }
    
    fn description(&self) -> &str {
        &self.description
    }
    
    fn tags(&self) -> HashMap<String, String> {
        self.tags.read().unwrap().clone()
    }
    
    fn reset(&self) {
        self.count.store(0, Ordering::SeqCst);
        self.sum.store(0, Ordering::SeqCst);
        self.min.store(u64::MAX, Ordering::SeqCst);
        self.max.store(0, Ordering::SeqCst);
        let mut values = self.values.lock().unwrap();
        values.clear();
    }
}

struct Timer {
    name: String,
    description: String,
    tags: RwLock<HashMap<String, String>>,
    histogram: Histogram,
    active_timers: Mutex<HashMap<String, Instant>>,
}

impl Timer {
    fn new(name: &str, description: &str) -> Self {
        Timer {
            name: name.to_string(),
            description: description.to_string(),
            tags: RwLock::new(HashMap::new()),
            histogram: Histogram::new(&format!("{}.histogram", name), description),
            active_timers: Mutex::new(HashMap::new()),
        }
    }
    
    fn with_tags(mut self, tags: HashMap<String, String>) -> Self {
        *self.tags.write().unwrap() = tags.clone();
        *self.histogram.tags.write().unwrap() = tags;
        self
    }
    
    fn start(&self) -> String {
        let timer_id = uuid::Uuid::new_v4().to_string();
        let mut active_timers = self.active_timers.lock().unwrap();
        active_timers.insert(timer_id.clone(), Instant::now());
        timer_id
    }
    
    fn stop(&self, timer_id: &str) -> Option<Duration> {
        let mut active_timers = self.active_timers.lock().unwrap();
        
        if let Some(start_time) = active_timers.remove(timer_id) {
            let duration = start_time.elapsed();
            self.histogram.update(duration.as_millis() as u64);
            Some(duration)
        } else {
            None
        }
    }
    
    fn time<F, T>(&self, f: F) -> T
    where
        F: FnOnce() -> T,
    {
        let timer_id = self.start();
        let result = f();
        self.stop(&timer_id);
        result
    }
    
    fn count(&self) -> u64 {
        self.histogram.count()
    }
    
    fn min(&self) -> Duration {
        Duration::from_millis(self.histogram.min())
    }
    
    fn max(&self) -> Duration {
        Duration::from_millis(self.histogram.max())
    }
    
    fn mean(&self) -> Duration {
        Duration::from_millis(self.histogram.mean() as u64)
    }
    
    fn percentile(&self, p: f64) -> Duration {
        Duration::from_millis(self.histogram.percentile(p))
    }
}

impl Metric for Timer {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn metric_type(&self) -> MetricType {
        MetricType::Timer
    }
    
    fn description(&self) -> &str {
        &self.description
    }
    
    fn tags(&self) -> HashMap<String, String> {
        self.tags.read().unwrap().clone()
    }
    
    fn reset(&self) {
        self.histogram.reset();
        let mut active_timers = self.active_timers.lock().unwrap();
        active_timers.clear();
    }
}

struct Meter {
    name: String,
    description: String,
    tags: RwLock<HashMap<String, String>>,
    count: AtomicU64,
    start_time: Instant,
    m1_rate: AtomicU64, // 每分钟速率（以微秒为单位）
    m5_rate: AtomicU64, // 每5分钟速率（以微秒为单位）
    m15_rate: AtomicU64, // 每15分钟速率（以微秒为单位）
    last_tick: Mutex<Instant>,
}

impl Meter {
    fn new(name: &str, description: &str) -> Self {
        let now = Instant::now();
        
        Meter {
            name: name.to_string(),
            description: description.to_string(),
            tags: RwLock::new(HashMap::new()),
            count: AtomicU64::new(0),
            start_time: now,
            m1_rate: AtomicU64::new(0),
            m5_rate: AtomicU64::new(0),
            m15_rate: AtomicU64::new(0),
            last_tick: Mutex::new(now),
        }
    }
    
    fn with_tags(mut self, tags: HashMap<String, String>) -> Self {
        *self.tags.write().unwrap() = tags;
        self
    }
    
    fn mark(&self) {
        self.mark_n(1);
    }
    
    fn mark_n(&self, n: u64) {
        self.count.fetch_add(n, Ordering::SeqCst);
        self.tick();
    }
    
    fn tick(&self) {
        let mut last_tick = self.last_tick.lock().unwrap();
        let now = Instant::now();
        let elapsed = now.duration_since(*last_tick).as_secs_f64();
        
        if elapsed > 5.0 {
            *last_tick = now;
            
            // 更新速率
            let count = self.count.load(Ordering::SeqCst);
            let mean_rate_micros = if count > 0 {
                let elapsed_total = now.duration_since(self.start_time).as_secs_f64();
                ((count as f64) / elapsed_total * 1_000_000.0) as u64
            } else {
                0
            };
            
            // 这里使用了简化的指数加权移动平均计算
            // 在实际实现中，应该使用更精确的EWMA算法
            let m1_rate = self.m1_rate.load(Ordering::SeqCst);
            let m5_rate = self.m5_rate.load(Ordering::SeqCst);
            let m15_rate = self.m15_rate.load(Ordering::SeqCst);
            
            let alpha1 = 1.0 - (-5.0 / 60.0).exp();
            let alpha5 = 1.0 - (-5.0 / 300.0).exp();
            let alpha15 = 1.0 - (-5.0 / 900.0).exp();
            
            let new_m1_rate = ((mean_rate_micros as f64) * alpha1 + (m1_rate as f64) * (1.0 - alpha1)) as u64;
            let new_m5_rate = ((mean_rate_micros as f64) * alpha5 + (m5_rate as f64) * (1.0 - alpha5)) as u64;
            let new_m15_rate = ((mean_rate_micros as f64) * alpha15 + (m15_rate as f64) * (1.0 - alpha15)) as u64;
            
            self.m1_rate.store(new_m1_rate, Ordering::SeqCst);
            self.m5_rate.store(new_m5_rate, Ordering::SeqCst);
            self.m15_rate.store(new_m15_rate, Ordering::SeqCst);
        }
    }
    
    fn count(&self) -> u64 {
        self.count.load(Ordering::SeqCst)
    }
    
    fn mean_rate(&self) -> f64 {
        let count = self.count.load(Ordering::SeqCst);
        if count == 0 {
            return 0.0;
        }
        let elapsed = self.start_time.elapsed().as_secs_f64();
        count as f64 / elapsed
    }
    
    fn one_minute_rate(&self) -> f64 {
        self.tick();
        self.m1_rate.load(Ordering::SeqCst) as f64 / 1_000_000.0
    }
    
    fn five_minute_rate(&self) -> f64 {
        self.tick();
        self.m5_rate.load(Ordering::SeqCst) as f64 / 1_000_000.0
    }
    
    fn fifteen_minute_rate(&self) -> f64 {
        self.tick();
        self.m15_rate.load(Ordering::SeqCst) as f64 / 1_000_000.0
    }
}

impl Metric for Meter {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn metric_type(&self) -> MetricType {
        MetricType::Meter
    }
    
    fn description(&self) -> &str {
        &self.description
    }
    
    fn tags(&self) -> HashMap<String, String> {
        self.tags.read().unwrap().clone()
    }
    
    fn reset(&self) {
        self.count.store(0, Ordering::SeqCst);
        self.m1_rate.store(0, Ordering::SeqCst);
        self.m5_rate.store(0, Ordering::SeqCst);
        self.m15_rate.store(0, Ordering::SeqCst);
        *self.last_tick.lock().unwrap() = Instant::now();
    }
}

impl MetricsRegistry {
    fn new() -> Self {
        MetricsRegistry {
            metrics: RwLock::new(HashMap::new()),
            tags: RwLock::new(HashMap::new()),
            reporters: RwLock::new(Vec::new()),
        }
    }
    
    fn with_tags(mut self, tags: HashMap<String, String>) -> Self {
        *self.tags.write().unwrap() = tags;
        self
    }
    
    fn add_reporter(&self, reporter: Box<dyn MetricReporter>) {
        let mut reporters = self.reporters.write().unwrap();
        reporters.push(reporter);
    }
    
    fn counter(&self, name: &str, description: &str) -> Arc<Counter> {
        let metrics = self.metrics.read().unwrap();
        
        if let Some(metric) = metrics.get(name) {
            if let Some(counter) = metric.downcast_ref::<Counter>() {
                return counter;
            } else {
                panic!("度量 {} 已经存在，但不是计数器", name);
            }
        }
        
        // 创建新计数器
        drop(metrics);
        let tags = self.tags.read().unwrap().clone();
        let counter = Arc::new(Counter::new(name, description).with_tags(tags));
        
        let mut metrics = self.metrics.write().unwrap();
        metrics.insert(name.to_string(), counter.clone() as Arc<dyn Metric>);
        
        counter
    }
    
    fn gauge(&self, name: &str, description: &str) -> Arc<Gauge> {
        let metrics = self.metrics.read().unwrap();
        
        if let Some(metric) = metrics.get(name) {
            if let Some(gauge) = metric.downcast_ref::<Gauge>() {
                return gauge;
            } else {
                panic!("度量 {} 已经存在，但不是仪表", name);
            }
        }
        
        // 创建新仪表
        drop(metrics);
        let tags = self.tags.read().unwrap().clone();
        let gauge = Arc::new(Gauge::new(name, description).with_tags(tags));
        
        let mut metrics = self.metrics.write().unwrap();
        metrics.insert(name.to_string(), gauge.clone() as Arc<dyn Metric>);
        
        gauge
    }
    
    fn histogram(&self, name: &str, description: &str) -> Arc<Histogram> {
        let metrics = self.metrics.read().unwrap();
        
        if let Some(metric) = metrics.get(name) {
            if let Some(histogram) = metric.downcast_ref::<Histogram>() {
                return histogram;
            } else {
                panic!("度量 {} 已经存在，但不是直方图", name);
            }
        }
        
        // 创建新直方图
        drop(metrics);
        let tags = self.tags.read().unwrap().clone();
        let histogram = Arc::new(Histogram::new(name, description).with_tags(tags));
        
        let mut metrics = self.metrics.write().unwrap();
        metrics.insert(name.to_string(), histogram.clone() as Arc<dyn Metric>);
        
        histogram
    }
    
    fn timer(&self, name: &str, description: &str) -> Arc<Timer> {
        let metrics = self.metrics.read().unwrap();
        
        if let Some(metric) = metrics.get(name) {
            if let Some(timer) = metric.downcast_ref::<Timer>() {
                return timer;
            } else {
                panic!("度量 {} 已经存在，但不是计时器", name);
            }
        }
        
        // 创建新计时器
        drop(metrics);
        let tags = self.tags.read().unwrap().clone();
        let timer = Arc::new(Timer::new(name, description).with_tags(tags));
        
        let mut metrics = self.metrics.write().unwrap();
        metrics.insert(name.to_string(), timer.clone() as Arc<dyn Metric>);
        
        timer
    }
    
    fn meter(&self, name: &str, description: &str) -> Arc<Meter> {
        let metrics = self.metrics.read().unwrap();
        
        if let Some(metric) = metrics.get(name) {
            if let Some(meter) = metric.downcast_ref::<Meter>() {
                return meter;
            } else {
                panic!("度量 {} 已经存在，但不是流量计", name);
            }
        }
        
        // 创建新流量计
        drop(metrics);
        let tags = self.tags.read().unwrap().clone();
        let meter = Arc::new(Meter::new(name, description).with_tags(tags));
        
        let mut metrics = self.metrics.write().unwrap();
        metrics.insert(name.to_string(), meter.clone() as Arc<dyn Metric>);
        
        meter
    }
    
    fn get_metric(&self, name: &str) -> Option<Arc<dyn Metric>> {
        let metrics = self.metrics.read().unwrap();
        metrics.get(name).cloned()
    }
    
    fn get_metrics(&self) -> Vec<Arc<dyn Metric>> {
        let metrics = self.metrics.read().unwrap();
        metrics.values().cloned().collect()
    }
    
    fn remove_metric(&self, name: &str) -> bool {
        let mut metrics = self.metrics.write().unwrap();
        metrics.remove(name).is_some()
    }
    
    fn clear(&self) {
        let mut metrics = self.metrics.write().unwrap();
        metrics.clear();
    }
    
    fn report(&self) {
        let reporters = self.reporters.read().unwrap();
        for reporter in reporters.iter() {
            reporter.report_all(self);
        }
    }
}

// 控制台度量报告器
struct ConsoleMetricReporter;

impl MetricReporter for ConsoleMetricReporter {
    fn report_counter(&self, counter: &Counter) {
        println!("计数器 {}: {}", counter.name(), counter.get());
    }
    
    fn report_gauge(&self, gauge: &Gauge) {
        println!("仪表 {}: {}", gauge.name(), gauge.get());
    }
    
    fn report_histogram(&self, histogram: &Histogram) {
        println!("直方图 {}:", histogram.name());
        println!("  计数: {}", histogram.count());
        println!("  最小值: {}", histogram.min());
        println!("  最大值: {}", histogram.max());
        println!("  平均值: {:.2}", histogram.mean());
        println!("  中位数: {}", histogram.percentile(0.5));
        println!("  75%: {}", histogram.percentile(0.75));
        println!("  95%: {}", histogram.percentile(0.95));
        println!("  99%: {}", histogram.percentile(0.99));
    }
    
    fn report_timer(&self, timer: &Timer) {
        println!("计时器 {}:", timer.name());
        println!("  计数: {}", timer.count());
        println!("  最小值: {:?}", timer.min());
        println!("  最大值: {:?}", timer.max());
        println!("  平均值: {:?}", timer.mean());
        println!("  中位数: {:?}", timer.percentile(0.5));
        println!("  75%: {:?}", timer.percentile(0.75));
        println!("  95%: {:?}", timer.percentile(0.95));
        println!("  99%: {:?}", timer.percentile(0.99));
    }
    
    fn report_meter(&self, meter: &Meter) {
        println!("流量计 {}:", meter.name());
        println!("  计数: {}", meter.count());
        println!("  平均速率: {:.2} 次/秒", meter.mean_rate());
        println!("  1分钟速率: {:.2} 次/秒", meter.one_minute_rate());
        println!("  5分钟速率: {:.2} 次/秒", meter.five_minute_rate());
        println!("  15分钟速率: {:.2} 次/秒", meter.fifteen_minute_rate());
    }
    
    fn report_all(&self, registry: &MetricsRegistry) {
        println!("===== 度量报告 =====");
        let metrics = registry.get_metrics();
        
        for metric in metrics {
            match metric.metric_type() {
                MetricType::Counter => {
                    if let Some(counter) = metric.downcast_ref::<Counter>() {
                        self.report_counter(counter);
                    }
                },
                MetricType::Gauge => {
                    if let Some(gauge) = metric.downcast_ref::<Gauge>() {
                        self.report_gauge(gauge);
                    }
                },
                MetricType::Histogram => {
                    if let Some(histogram) = metric.downcast_ref::<Histogram>() {
                        self.report_histogram(histogram);
                    }
                },
                MetricType::Timer => {
                    if let Some(timer) = metric.downcast_ref::<Timer>() {
                        self.report_timer(timer);
                    }
                },
                MetricType::Meter => {
                    if let Some(meter) = metric.downcast_ref::<Meter>() {
                        self.report_meter(meter);
                    }
                },
            }
            println!();
        }
        
        println!("===================");
    }
}

// 分布式系统健康检查
struct HealthCheckRegistry {
    checks: RwLock<HashMap<String, Box<dyn HealthCheck>>>,
}

trait HealthCheck: Send + Sync {
    fn name(&self) -> &str;
    fn check(&self) -> HealthCheckResult;
    fn description(&self) -> &str;
}

struct HealthCheckResult {
    name: String,
    status: HealthStatus,
    message: Option<String>,
    details: Option<serde_json::Value>,
    timestamp: SystemTime,
}

enum HealthStatus {
    Up,
    Down,
    Degraded,
    Unknown,
}

impl HealthCheckRegistry {
    fn new() -> Self {
        HealthCheckRegistry {
            checks: RwLock::new(HashMap::new()),
        }
    }
    
    fn register<H: HealthCheck + 'static>(&self, check: H) -> Result<(), String> {
        let mut checks = self.checks.write().unwrap();
        let name = check.name().to_string();
        
        if checks.contains_key(&name) {
            return Err(format!("健康检查 {} 已经存在", name));
        }
        
        checks.insert(name, Box::new(check));
        Ok(())
    }
    
    fn unregister(&self, name: &str) -> bool {
        let mut checks = self.checks.write().unwrap();
        checks.remove(name).is_some()
    }
    
    fn run_check(&self, name: &str) -> Option<HealthCheckResult> {
        let checks = self.checks.read().unwrap();
        
        if let Some(check) = checks.get(name) {
            Some(check.check())
        } else {
            None
        }
    }
    
    fn run_all_checks(&self) -> Vec<HealthCheckResult> {
        let checks = self.checks.read().unwrap();
        
        checks.values()
            .map(|check| check.check())
            .collect()
    }
    
    fn is_healthy(&self) -> bool {
        let results = self.run_all_checks();
        
        results.iter().all(|result| match result.status {
            HealthStatus::Up => true,
            _ => false,
        })
    }
}

// 组合以上所有功能创建一个分布式系统框架
struct DistributedSystemFramework {
    service_registry: Arc<ServiceRegistry>,
    metrics_registry: Arc<MetricsRegistry>,
    health_check_registry: Arc<HealthCheckRegistry>,
    event_bus: Arc<EventDrivenSystem>,
    cache_system: Arc<DistributedCacheSystem>,
    queue_system: Arc<DistributedQueueSystem>,
    resilience_manager: Arc<ResilienceManager>,
    tracer: Arc<DistributedTracer>,
}

impl DistributedSystemFramework {
    fn new(
        service_registry: Arc<ServiceRegistry>,
        metrics_registry: Arc<MetricsRegistry>,
        health_check_registry: Arc<HealthCheckRegistry>,
        event_bus: Arc<EventDrivenSystem>,
        cache_system: Arc<DistributedCacheSystem>,
        queue_system: Arc<DistributedQueueSystem>,
        resilience_manager: Arc<ResilienceManager>,
        tracer: Arc<DistributedTracer>,
    ) -> Self {
        DistributedSystemFramework {
            service_registry,
            metrics_registry,
            health_check_registry,
            event_bus,
            cache_system,
            queue_system,
            resilience_manager,
            tracer,
        }
    }
    
    // 可以为框架添加各种应用场景的辅助方法
    
    fn build_service_client(&self, service_name: &str) -> ServiceClient {
        ServiceClient {
            service_name: service_name.to_string(),
            service_registry: self.service_registry.clone(),
            metrics_registry: self.metrics_registry.clone(),
            resilience_manager: self.resilience_manager.clone(),
            tracer: self.tracer.clone(),
        }
    }
    
    fn register_service(&self, registration: ServiceRegistration) -> Result<(), String> {
        // 创建并注册服务相关的度量
        let service_counter = self.metrics_registry.counter(
            &format!("service.{}.requests", registration.name),
            &format!("请求计数器 for {}", registration.name),
        );
        
        let service_timer = self.metrics_registry.timer(
            &format!("service.{}.response_time", registration.name),
            &format!("响应时间 for {}", registration.name),
        );
        
        // 注册健康检查
        if let Some(health) = &registration.health_check {
            self.register_service_health_check(&registration.name, health)?;
        }
        
        // 注册服务到注册中心
        self.service_registry.register_service(&registration)
    }
    
    fn register_service_health_check(&self, service_name: &str, health_check: &HealthCheck) -> Result<(), String> {
        self.health_check_registry.register(ServiceHealthCheck {
            service_name: service_name.to_string(),
            inner_check: health_check,
        })
    }
    
    fn create_cache_client(&self, name: &str) -> CacheClient {
        CacheClient {
            name: name.to_string(),
            cache_system: self.cache_system.clone(),
            metrics_registry: self.metrics_registry.clone(),
        }
    }
    
    fn create_queue_client(&self, name: &str) -> QueueClient {
        QueueClient {
            name: name.to_string(),
            queue_system: self.queue_system.clone(),
            metrics_registry: self.metrics_registry.clone(),
        }
    }
    
    fn create_event_publisher(&self, source: &str) -> EventPublisher {
        EventPublisher {
            source: source.to_string(),
            event_bus: self.event_bus.clone(),
            metrics_registry: self.metrics_registry.clone(),
        }
    }
}

// 服务健康检查包装器
struct ServiceHealthCheck<'a> {
    service_name: String,
    inner_check: &'a dyn HealthCheck,
}

impl<'a> HealthCheck for ServiceHealthCheck<'a> {
    fn name(&self) -> &str {
        self.inner_check.name()
    }
    
    fn check(&self) -> HealthCheckResult {
        self.inner_check.check()
    }
    
    fn description(&self) -> &str {
        self.inner_check.description()
    }
}

// 服务客户端
struct ServiceClient {
    service_name: String,
    service_registry: Arc<ServiceRegistry>,
    metrics_registry: Arc<MetricsRegistry>,
    resilience_manager: Arc<ResilienceManager>,
    tracer: Arc<DistributedTracer>,
}

impl ServiceClient {
    fn call<F, T, E>(&self, method: &str, f: F) -> Result<T, E>
    where
        F: Fn(&ServiceInstance) -> Result<T, E> + Clone,
        E: std::fmt::Debug + From<String>,
    {
        // 获取服务度量
        let request_counter = self.metrics_registry.counter(
            &format!("service.{}.requests", self.service_name),
            &format!("请求计数器 for {}", self.service_name),
        );
        
        let timer = self.metrics_registry.timer(
            &format!("service.{}.response_time", self.service_name),
            &format!("响应时间 for {}", self.service_name),
        );
        
        // 创建跟踪跨度
        let span = self.tracer.start_span(&format!("{}.{}", self.service_name, method));
        self.tracer.set_tag(&span, "service", &self.service_name);
        self.tracer.set_tag(&span, "method", method);
        
        // 增加请求计数
        request_counter.increment();
        
        // 使用断路器、舱壁和重试策略
        let circuit_breaker_name = format!("{}-breaker", self.service_name);
        let bulkhead_name = format!("{}-bulkhead", self.service_name);
        let retry_policy_name = format!("{}-retry", self.service_name);
        
        let timer_id = timer.start();
        
        let result = self.resilience_manager.execute_with_resilience(
            Some(&circuit_breaker_name),
            Some(&bulkhead_name),
            Some(&retry_policy_name),
            None,
            move || {
                // 发现服务实例
                let instances = self.service_registry.get_service_instances(&self.service_name)
                    .map_err(|e| format!("无法获取服务实例: {}", e))?;

                if instances.is_empty() {
                    return Err(format!("没有找到可用的服务实例: {}", self.service_name).into());
                }

                // 选择一个实例（简单的负载均衡，随机选择）
                let instance = &instances[rand::random::<usize>() % instances.len()];

                // 调用服务
                f(instance)
            }
        );

        // 停止计时
        timer.stop(&timer_id);

        // 完成跟踪跨度
        self.tracer.finish_span(&span);

        result
    }
}

// 缓存客户端
struct CacheClient {
    name: String,
    cache_system: Arc<DistributedCacheSystem>,
    metrics_registry: Arc<MetricsRegistry>,
}

impl CacheClient {
    fn get<T: serde::de::DeserializeOwned>(&self, key: &str) -> Result<Option<T>, String> {
        // 获取缓存度量
        let hits = self.metrics_registry.counter(
            &format!("cache.{}.hits", self.name),
            &format!("缓存命中计数器 for {}", self.name),
        );
        
        let misses = self.metrics_registry.counter(
            &format!("cache.{}.misses", self.name),
            &format!("缓存未命中计数器 for {}", self.name),
        );
        
        let timer = self.metrics_registry.timer(
            &format!("cache.{}.get_time", self.name),
            &format!("缓存获取时间 for {}", self.name),
        );
        
        // 开始计时
        let timer_id = timer.start();
        
        // 从缓存获取
        let result = match self.cache_system.get(key) {
            Ok(Some(entry)) => {
                // 命中缓存
                hits.increment();
                
                // 反序列化值
                match bincode::deserialize(&entry.value) {
                    Ok(value) => Ok(Some(value)),
                    Err(err) => Err(format!("反序列化缓存项失败: {}", err)),
                }
            },
            Ok(None) => {
                // 未命中缓存
                misses.increment();
                Ok(None)
            },
            Err(err) => {
                Err(format!("缓存获取操作失败: {}", err.message))
            }
        };
        
        // 停止计时
        timer.stop(&timer_id);
        
        result
    }
    
    fn set<T: serde::Serialize>(&self, key: &str, value: &T, ttl: Option<Duration>) -> Result<(), String> {
        // 获取缓存度量
        let timer = self.metrics_registry.timer(
            &format!("cache.{}.set_time", self.name),
            &format!("缓存设置时间 for {}", self.name),
        );
        
        // 开始计时
        let timer_id = timer.start();
        
        // 序列化值
        let data = match bincode::serialize(value) {
            Ok(data) => data,
            Err(err) => {
                return Err(format!("序列化值失败: {}", err));
            }
        };
        
        // 设置到缓存
        let result = match self.cache_system.set(key, &data, ttl) {
            Ok(_) => Ok(()),
            Err(err) => Err(format!("缓存设置操作失败: {}", err.message)),
        };
        
        // 停止计时
        timer.stop(&timer_id);
        
        result
    }
    
    fn get_or_compute<T, F>(&self, key: &str, ttl: Option<Duration>, compute_fn: F) -> Result<T, String>
    where
        T: serde::de::DeserializeOwned + serde::Serialize,
        F: FnOnce() -> Result<T, String>,
    {
        // 尝试从缓存获取
        if let Some(value) = self.get::<T>(key)? {
            return Ok(value);
        }
        
        // 计算值
        let value = compute_fn()?;
        
        // 缓存值
        self.set(key, &value, ttl)?;
        
        Ok(value)
    }
    
    fn delete(&self, key: &str) -> Result<bool, String> {
        match self.cache_system.delete(key) {
            Ok(deleted) => Ok(deleted),
            Err(err) => Err(format!("缓存删除操作失败: {}", err.message)),
        }
    }
}

// 队列客户端
struct QueueClient {
    name: String,
    queue_system: Arc<DistributedQueueSystem>,
    metrics_registry: Arc<MetricsRegistry>,
}

impl QueueClient {
    fn push<T: serde::Serialize>(&self, queue_name: &str, message: &T, ttl: Option<Duration>) -> Result<String, String> {
        // 获取队列度量
        let timer = self.metrics_registry.timer(
            &format!("queue.{}.push_time", self.name),
            &format!("队列推送时间 for {}", self.name),
        );
        
        let size = self.metrics_registry.gauge(
            &format!("queue.{}.size", queue_name),
            &format!("队列大小 for {}", queue_name),
        );
        
        // 开始计时
        let timer_id = timer.start();
        
        // 序列化消息
        let data = match bincode::serialize(message) {
            Ok(data) => data,
            Err(err) => {
                return Err(format!("序列化消息失败: {}", err));
            }
        };
        
        // 推送到队列
        let result = match self.queue_system.push(queue_name, &data, ttl) {
            Ok(message_id) => {
                // 更新队列大小度量
                if let Ok(queue_size) = self.queue_system.len(queue_name) {
                    size.set(queue_size as u64);
                }
                
                Ok(message_id)
            },
            Err(err) => Err(format!("队列推送操作失败: {}", err.message)),
        };
        
        // 停止计时
        timer.stop(&timer_id);
        
        result
    }
    
    fn pop<T: serde::de::DeserializeOwned>(&self, queue_name: &str, wait_time: Option<Duration>) -> Result<Option<(String, T)>, String> {
        // 获取队列度量
        let timer = self.metrics_registry.timer(
            &format!("queue.{}.pop_time", self.name),
            &format!("队列弹出时间 for {}", self.name),
        );
        
        let size = self.metrics_registry.gauge(
            &format!("queue.{}.size", queue_name),
            &format!("队列大小 for {}", queue_name),
        );
        
        // 开始计时
        let timer_id = timer.start();
        
        // 从队列弹出
        let result = match self.queue_system.pop(queue_name, wait_time) {
            Ok(Some(message)) => {
                // 反序列化消息
                match bincode::deserialize(&message.payload) {
                    Ok(value) => {
                        // 更新队列大小度量
                        if let Ok(queue_size) = self.queue_system.len(queue_name) {
                            size.set(queue_size as u64);
                        }
                        
                        Ok(Some((message.id, value)))
                    },
                    Err(err) => Err(format!("反序列化消息失败: {}", err)),
                }
            },
            Ok(None) => Ok(None),
            Err(err) => Err(format!("队列弹出操作失败: {}", err.message)),
        };
        
        // 停止计时
        timer.stop(&timer_id);
        
        result
    }
    
    fn ack(&self, queue_name: &str, message_id: &str) -> Result<bool, String> {
        match self.queue_system.ack(queue_name, message_id) {
            Ok(acknowledged) => Ok(acknowledged),
            Err(err) => Err(format!("队列确认操作失败: {}", err.message)),
        }
    }
}

// 事件发布者
struct EventPublisher {
    source: String,
    event_bus: Arc<EventDrivenSystem>,
    metrics_registry: Arc<MetricsRegistry>,
}

impl EventPublisher {
    fn publish(&self, event_type: &str, payload: serde_json::Value) -> Result<String, String> {
        // 获取事件度量
        let counter = self.metrics_registry.counter(
            &format!("events.{}.published", event_type),
            &format!("已发布事件计数器 for {}", event_type),
        );
        
        let timer = self.metrics_registry.timer(
            &format!("events.{}.publish_time", event_type),
            &format!("事件发布时间 for {}", event_type),
        );
        
        // 开始计时
        let timer_id = timer.start();
        
        // 创建事件
        let event = self.event_bus.create_event(event_type, payload, &self.source);
        
        // 发布事件
        let result = self.event_bus.publish_event(&event);
        
        // 增加计数
        counter.increment();
        
        // 停止计时
        timer.stop(&timer_id);
        
        result
    }
    
    fn publish_correlated(&self, event_type: &str, payload: serde_json::Value, parent_event: &Event) -> Result<String, String> {
        // 获取事件度量
        let counter = self.metrics_registry.counter(
            &format!("events.{}.published", event_type),
            &format!("已发布事件计数器 for {}", event_type),
        );
        
        let timer = self.metrics_registry.timer(
            &format!("events.{}.publish_time", event_type),
            &format!("事件发布时间 for {}", event_type),
        );
        
        // 开始计时
        let timer_id = timer.start();
        
        // 创建关联事件
        let event = self.event_bus.create_correlated_event(event_type, payload, &self.source, parent_event);
        
        // 发布事件
        let result = self.event_bus.publish_event(&event);
        
        // 增加计数
        counter.increment();
        
        // 停止计时
        timer.stop(&timer_id);
        
        result
    }
}

// 这个实现展示了一个具有各种分布式系统功能的完整框架，包括：
// - 服务注册与发现
// - 分布式缓存
// - 分布式队列
// - 事件驱动架构
// - 分布式跟踪
// - 度量和监控
// - 健康检查
// - 容错机制（断路器、舱壁、重试和超时）

// 通过这些组件，可以构建复杂的分布式系统，同时保持高可用性、可扩展性和弹性。
```
