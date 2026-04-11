# 案例10：神经形态计算系统

## 1. 背景介绍

### 1.1 问题背景

神经形态计算是一种受生物神经系统启发的计算范式，使用脉冲神经网络（SNN）而非传统的人工神经网络（ANN）。其核心优势包括：

- **事件驱动计算**：仅在脉冲事件发生时消耗能量
- **时序信息处理**：天然支持时间序列数据
- **低功耗**：适合边缘计算和物联网设备
- **在线学习**：支持实时自适应

神经形态芯片（如Intel Loihi、IBM TrueNorth）的调度需要协调脉冲神经元的大规模并行活动，同时优化能耗和实时性。

### 1.2 挑战与目标

**主要挑战：**

- 脉冲事件的异步性和稀疏性
- 神经元状态的时间演化
- 硬件资源的有限性（突触、神经元数量）
- 实时性要求与功耗的权衡

**设计目标：**

- 形式化SNN的时序动态
- 证明调度策略的实时性保证
- 能耗模型的形式化与优化
- 在线学习算法的收敛性

### 1.3 相关研究

- **Intel Loihi**: 大规模神经形态处理器
- **SpiNNaker**: 百万核心神经形态计算平台
- **STDP**: 脉冲时间依赖可塑性学习规则
- **Brian/Norse**: SNN仿真框架

---

## 2. 形式化规约

### 2.1 脉冲神经网络模型

```
SNN = (Neurons, Synapses, Spikes, Dynamics, Learning)
```

其中：

- `Neurons`: 脉冲神经元集合
- `Synapses`: 突触连接及权重
- `Spikes`: 脉冲事件序列
- `Dynamics`: 神经元膜电位动态
- `Learning`: 学习规则（如STDP）

### 2.2 神经元动态形式化

```lean4
-- 时间
abbrev Time := Float

-- 神经元ID
abbrev NeuronId := Nat

-- 脉冲事件
structure Spike where
  neuron : NeuronId
  time : Time
  deriving Repr, DecidableEq

-- 神经元模型（Leaky Integrate-and-Fire）
structure LIFNeuron where
  id : NeuronId
  tau_m : Float          -- 膜时间常数
  v_rest : Float         -- 静息电位
  v_thresh : Float       -- 发放阈值
  v_reset : Float        -- 重置电位
  r_mem : Float          -- 膜电阻
  refractory_period : Float  -- 不应期

-- 神经元状态
structure NeuronState where
  v_mem : Float          -- 膜电位
  last_spike : Option Time  -- 上次脉冲时间
  in_refractory : Bool   -- 是否处于不应期

-- 膜电位演化（微分方程离散化）
def membraneDynamics (neuron : LIFNeuron) (state : NeuronState)
    (I_in : Float) (dt : Float) : Float :=
  let dv = (-(state.v_mem - neuron.v_rest) + neuron.r_mem * I_in) / neuron.tau_m
  state.v_mem + dv * dt

-- 脉冲发放条件
def shouldFire (neuron : LIFNeuron) (v_mem : Float) : Bool :=
  v_mem ≥ neuron.v_thresh
```

### 2.3 突触与网络拓扑

```lean4
-- 突触类型
inductive SynapseType
  | Excitatory   -- 兴奋性
  | Inhibitory   -- 抑制性
  deriving Repr

-- 突触连接
structure Synapse where
  pre : NeuronId      -- 前突触神经元
  post : NeuronId     -- 后突触神经元
  weight : Float      -- 权重
  delay : Float       -- 突触延迟
  syn_type : SynapseType

-- 脉冲神经网络结构
structure SNNTopology where
  neurons : List LIFNeuron
  synapses : List Synapse
  input_neurons : List NeuronId
  output_neurons : List NeuronId

-- 网络状态
def NetworkState := NeuronId → NeuronState

-- 突触电流计算
def synapticCurrent (state : NetworkState) (synapses : List Synapse)
    (t : Time) : NeuronId → Float :=
  fun post_id =>
    synapses.filter (λ s => s.post = post_id)
      |>.sumBy (λ s =>
        let pre_state := state s.pre
        match pre_state.last_spike with
        | some t_spike =>
          if t - t_spike ≈ s.delay then s.weight else 0.0
        | none => 0.0)
```

### 2.4 调度问题形式化

```lean4
-- 调度事件
def ScheduleEvent := Spike × ProcessorId × Time

-- 调度策略
def SchedulingPolicy := List Spike → Time → List (Spike × Time)

-- 实时性约束
def RealtimeConstraint := Time → Prop

-- 能耗模型
def EnergyModel := Spike → ProcessorId → Energy

structure SchedulerSpec where
  -- 调度产生的执行时间
  execution_time : Schedule → Time
  -- 总能耗
  total_energy : Schedule → Energy
  -- 实时性满足
  meets_deadline : Schedule → Time → Prop

-- 调度优化目标
inductive OptimizationObjective
  | MinimizeMakespan
  | MinimizeEnergy (deadline : Time)
  | MinimizeLatency (energy_budget : Energy)
  | MultiObjective (weights : List Float)
```

---

## 3. 证明/验证过程

### 3.1 神经元动态正确性

```lean4
-- 神经元动态的前向欧拉离散化正确性
theorem euler_discretization_error :
  ∀ (neuron : LIFNeuron) (state : NeuronState) (I : Float → Float) (t : Time),
    let exact := exactSolution neuron state I t
    let euler := eulerStep neuron state (I t) dt
    |exact - euler| ≤ C * dt^2 := by
  -- 证明欧拉方法的局部截断误差为O(dt^2)
  sorry

-- 脉冲发放的周期性行为
theorem periodic_firing :
  ∀ (neuron : LIFNeuron) (I_const : Float),
    I_const > (neuron.v_thresh - neuron.v_rest) / neuron.r_mem →
    ∃ (T : Time),
      ∀ (n : Nat),
        let spike_times := simulate neuron I_const n
        spike_times[n+1] - spike_times[n] ≈ T := by
  -- 证明在恒定输入下，神经元周期性发放
  sorry
```

### 3.2 STDP学习收敛性

```lean4
-- STDP窗口函数
def stdpWindow (dt : Float) : Float :=
  if dt > 0 then A_plus * Float.exp (-dt / tau_plus)
  else if dt < 0 then A_minus * Float.exp (dt / tau_minus)
  else 0.0

-- 权重更新
def updateWeight (w : Float) (pre_t post_t : Time) : Float :=
  let dw := stdpWindow (post_t - pre_t)
  clamp (w + dw) w_min w_max

-- 收敛性：在重复模式下权重收敛到稳定值
theorem stdp_convergence :
  ∀ (pattern : List (Spike × Spike)),  -- 前后突触脉冲对
    let updates := pattern.map (λ (pre, post) => stdpWindow (post.time - pre.time))
    let final_weight := updates.sum
    -- 在固定模式下，权重收敛
    converges final_weight := by
  -- 证明基于重复模式下的权重变化趋于0
  sorry
```

### 3.3 实时调度保证

```lean4
-- 可调度性测试
def Schedulable (tasks : List Task) : Prop :=
  let total_utilization := tasks.sumBy (λ t => t.wcet / t.period)
  total_utilization ≤ 1.0

-- EDF（最早截止时间优先）最优性
theorem edf_optimality :
  ∀ (tasks : List Task),
    Schedulable tasks →
    ∀ (schedule : EDFSchedule tasks),
      ∀ (task ∈ tasks) (instance : Nat),
        meetsDeadline schedule task instance := by
  -- 证明EDF在利用率≤1时可调度所有任务
  sorry

-- 能耗最优调度
theorem energy_optimal_scheduling :
  ∀ (spikes : List Spike) (processors : List Processor) (deadline : Time),
    ∃ (schedule : Schedule),
      makespan schedule ≤ deadline ∧
      ∀ s, ValidSchedule s → makespan s ≤ deadline →
        energy schedule ≤ energy s := by
  -- 证明在截止时间约束下的能耗最优调度存在
  sorry
```

---

## 4. 代码实现

### 4.1 脉冲神经网络仿真（Rust）

```rust
//! 脉冲神经网络(SNN)核心实现
//! LIF神经元模型与STDP学习

use std::collections::{HashMap, VecDeque};
use ndarray::{Array1, Array2};
use serde::{Serialize, Deserialize};

/// 时间类型（毫秒）
pub type TimeMs = f64;

/// 神经元ID
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct NeuronId(pub usize);

/// 脉冲事件
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct Spike {
    pub neuron_id: NeuronId,
    pub time: TimeMs,
}

impl Spike {
    pub fn new(neuron_id: NeuronId, time: TimeMs) -> Self {
        Self { neuron_id, time }
    }
}

/// LIF神经元参数
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub struct LIFParameters {
    pub tau_m: TimeMs,           // 膜时间常数 (ms)
    pub v_rest: f64,             // 静息电位 (mV)
    pub v_thresh: f64,           // 阈值电位 (mV)
    pub v_reset: f64,            // 重置电位 (mV)
    pub r_mem: f64,              // 膜电阻 (MΩ)
    pub tau_ref: TimeMs,         // 不应期 (ms)
}

impl Default for LIFParameters {
    fn default() -> Self {
        Self {
            tau_m: 20.0,
            v_rest: -70.0,
            v_thresh: -55.0,
            v_reset: -75.0,
            r_mem: 10.0,
            tau_ref: 2.0,
        }
    }
}

/// 神经元状态
#[derive(Debug, Clone, Copy)]
pub struct NeuronState {
    pub v_mem: f64,              // 膜电位
    pub last_spike_time: Option<TimeMs>,
    pub refractory_until: TimeMs, // 不应期结束时间
}

impl NeuronState {
    pub fn new(v_rest: f64) -> Self {
        Self {
            v_mem: v_rest,
            last_spike_time: None,
            refractory_until: 0.0,
        }
    }

    /// 检查是否在不应期
    pub fn in_refractory(&self, t: TimeMs) -> bool {
        t < self.refractory_until
    }

    /// 更新膜电位（欧拉法）
    pub fn update(&mut self, params: &LIFParameters, i_syn: f64, dt: TimeMs, t: TimeMs) -> bool {
        // 检查不应期
        if self.in_refractory(t) {
            self.v_mem = params.v_rest;
            return false;
        }

        // LIF动态方程: tau_m * dv/dt = -(v - v_rest) + R * I
        let dv = (-(self.v_mem - params.v_rest) + params.r_mem * i_syn) / params.tau_m;
        self.v_mem += dv * dt;

        // 检查是否发放脉冲
        if self.v_mem >= params.v_thresh {
            self.v_mem = params.v_reset;
            self.last_spike_time = Some(t);
            self.refractory_until = t + params.tau_ref;
            true
        } else {
            false
        }
    }
}

/// 突触连接
#[derive(Debug, Clone, Copy)]
pub struct Synapse {
    pub pre: NeuronId,
    pub post: NeuronId,
    pub weight: f64,
    pub delay: TimeMs,
}

/// 突触后电位（EPSP/IPSP）
#[derive(Debug, Clone)]
pub struct PostSynapticPotential {
    pub target: NeuronId,
    pub weight: f64,
    pub arrival_time: TimeMs,
}

/// 脉冲神经网络
pub struct SpikingNeuralNetwork {
    pub neurons: Vec<(LIFParameters, NeuronState)>,
    pub synapses: Vec<Synapse>,
    pub input_neurons: Vec<NeuronId>,
    pub output_neurons: Vec<NeuronId>,

    // 事件队列
    event_queue: VecDeque<PostSynapticPotential>,

    // 仿真参数
    current_time: TimeMs,
    dt: TimeMs,
}

impl SpikingNeuralNetwork {
    pub fn new(num_neurons: usize, dt: TimeMs) -> Self {
        let neurons: Vec<_> = (0..num_neurons)
            .map(|_| {
                let params = LIFParameters::default();
                let state = NeuronState::new(params.v_rest);
                (params, state)
            })
            .collect();

        Self {
            neurons,
            synapses: vec![],
            input_neurons: vec![],
            output_neurons: vec![],
            event_queue: VecDeque::new(),
            current_time: 0.0,
            dt,
        }
    }

    /// 添加突触连接
    pub fn add_synapse(&mut self, pre: NeuronId, post: NeuronId, weight: f64, delay: TimeMs) {
        self.synapses.push(Synapse { pre, post, weight, delay });
    }

    /// 设置输入电流
    pub fn set_input_current(&mut self, neuron: NeuronId, current: f64) -> Option<()> {
        let (params, state) = self.neurons.get_mut(neuron.0)?;

        // 直接注入电流更新膜电位
        let fired = state.update(params, current, self.dt, self.current_time);

        if fired {
            self.propagate_spike(neuron);
        }

        Some(())
    }

    /// 单步仿真
    pub fn step(&mut self, external_inputs: &[(NeuronId, f64)]) -> Vec<Spike> {
        let mut spikes = vec![];

        // 处理外部输入
        for &(neuron_id, current) in external_inputs {
            if let Some((params, state)) = self.neurons.get_mut(neuron_id.0) {
                let fired = state.update(params, current, self.dt, self.current_time);
                if fired {
                    spikes.push(Spike::new(neuron_id, self.current_time));
                    self.propagate_spike(neuron_id);
                }
            }
        }

        // 处理到达的突触事件
        let current_events: Vec<_> = self.event_queue
            .drain(..)
            .filter(|event| event.arrival_time <= self.current_time + self.dt)
            .collect();

        // 按目标神经元聚合电流
        let mut synaptic_currents: HashMap<NeuronId, f64> = HashMap::new();
        for event in current_events {
            *synaptic_currents.entry(event.target).or_insert(0.0) += event.weight;
        }

        // 更新所有神经元
        for (i, (params, state)) in self.neurons.iter_mut().enumerate() {
            let neuron_id = NeuronId(i);

            // 跳过已处理的外部输入神经元
            if external_inputs.iter().any(|&(id, _)| id == neuron_id) {
                continue;
            }

            let i_syn = synaptic_currents.get(&neuron_id).copied().unwrap_or(0.0);
            let fired = state.update(params, i_syn, self.dt, self.current_time);

            if fired {
                spikes.push(Spike::new(neuron_id, self.current_time));
                self.propagate_spike(neuron_id);
            }
        }

        // 处理未到时间的突触事件（放回队列）
        for event in self.event_queue.drain(..).collect::<Vec<_>>() {
            self.event_queue.push_back(event);
        }

        self.current_time += self.dt;
        spikes
    }

    /// 脉冲传播
    fn propagate_spike(&mut self, source: NeuronId) {
        for synapse in &self.synapses {
            if synapse.pre == source {
                let psp = PostSynapticPotential {
                    target: synapse.post,
                    weight: synapse.weight,
                    arrival_time: self.current_time + synapse.delay,
                };
                self.event_queue.push_back(psp);
            }
        }
    }

    /// 运行仿真
    pub fn run(&mut self, duration: TimeMs, input_pattern: &[(TimeMs, NeuronId, f64)]) -> Vec<Spike> {
        let mut all_spikes = vec![];
        let steps = (duration / self.dt) as usize;

        // 按时间排序输入
        let mut input_iter = input_pattern.iter().peekable();

        for _ in 0..steps {
            // 收集当前时间步的外部输入
            let mut current_inputs = vec![];
            while let Some(&&(t, neuron, current)) = input_iter.peek() {
                if t <= self.current_time {
                    current_inputs.push((neuron, current));
                    input_iter.next();
                } else {
                    break;
                }
            }

            let spikes = self.step(&current_inputs);
            all_spikes.extend(spikes);
        }

        all_spikes
    }

    /// 获取输出神经元的发放率
    pub fn output_firing_rates(&self, window_ms: TimeMs) -> Vec<f64> {
        let window_start = self.current_time - window_ms;

        self.output_neurons.iter()
            .map(|&neuron_id| {
                let state = &self.neurons[neuron_id.0].1;
                if let Some(last_spike) = state.last_spike_time {
                    if last_spike >= window_start {
                        1.0 / window_ms  // 简化为单脉冲估计
                    } else {
                        0.0
                    }
                } else {
                    0.0
                }
            })
            .collect()
    }
}
```

### 4.2 STDP学习实现（Rust）

```rust
//! STDP（脉冲时间依赖可塑性）学习规则实现

use std::collections::HashMap;

/// STDP参数
#[derive(Debug, Clone, Copy)]
pub struct STDPParams {
    pub a_plus: f64,       // 增强幅度
    pub a_minus: f64,      // 抑制幅度
    pub tau_plus: f64,     // 增强时间常数
    pub tau_minus: f64,    // 抑制时间常数
    pub w_max: f64,        // 最大权重
    pub w_min: f64,        // 最小权重
    pub learning_rate: f64,
}

impl Default for STDPParams {
    fn default() -> Self {
        Self {
            a_plus: 0.1,
            a_minus: -0.1,
            tau_plus: 20.0,
            tau_minus: 20.0,
            w_max: 1.0,
            w_min: 0.0,
            learning_rate: 0.01,
        }
    }
}

/// STDP学习器
pub struct STDPLearner {
    params: STDPParams,
    // 记录每个神经元的最近脉冲时间
    pre_trace: HashMap<NeuronId, Vec<f64>>,
    post_trace: HashMap<NeuronId, Vec<f64>>,
}

impl STDPLearner {
    pub fn new(params: STDPParams) -> Self {
        Self {
            params,
            pre_trace: HashMap::new(),
            post_trace: HashMap::new(),
        }
    }

    /// STDP窗口函数
    fn stdp_window(&self, delta_t: f64) -> f64 {
        // delta_t = t_post - t_pre
        if delta_t > 0.0 {
            // 后突触在预突触之后发放 -> 增强（LTP）
            self.params.a_plus * (-delta_t / self.params.tau_plus).exp()
        } else if delta_t < 0.0 {
            // 后突触在预突触之前发放 -> 抑制（LTD）
            self.params.a_minus * (delta_t / self.params.tau_minus).exp()
        } else {
            0.0
        }
    }

    /// 记录脉冲
    pub fn record_spike(&mut self, neuron: NeuronId, is_pre: bool, time: f64) {
        if is_pre {
            self.pre_trace.entry(neuron).or_insert_with(Vec::new).push(time);
        } else {
            self.post_trace.entry(neuron).or_insert_with(Vec::new).push(time);
        }
    }

    /// 计算权重更新
    pub fn compute_weight_update(&self, pre_neuron: NeuronId, post_neuron: NeuronId) -> f64 {
        let pre_times = self.pre_trace.get(&pre_neuron).map(|v| v.as_slice()).unwrap_or(&[]);
        let post_times = self.post_trace.get(&post_neuron).map(|v| v.as_slice()).unwrap_or(&[]);

        let mut dw = 0.0;

        // 对所有脉冲对应用STDP
        for &t_pre in pre_times {
            for &t_post in post_times {
                let delta_t = t_post - t_pre;
                dw += self.stdp_window(delta_t);
            }
        }

        dw * self.params.learning_rate
    }

    /// 更新突触权重
    pub fn update_weights(&self, network: &mut SpikingNeuralNetwork) {
        let mut updates: Vec<(usize, f64)> = vec![];

        // 计算所有突触的权重更新
        for (i, synapse) in network.synapses.iter().enumerate() {
            let dw = self.compute_weight_update(synapse.pre, synapse.post);
            updates.push((i, dw));
        }

        // 应用更新
        for (i, dw) in updates {
            let new_weight = network.synapses[i].weight + dw;
            network.synapses[i].weight = new_weight
                .max(self.params.w_min)
                .min(self.params.w_max);
        }
    }

    /// 清理旧的脉冲记录
    pub fn prune_traces(&mut self, current_time: f64, window: f64) {
        let cutoff = current_time - window;

        for times in self.pre_trace.values_mut() {
            times.retain(|&t| t >= cutoff);
        }

        for times in self.post_trace.values_mut() {
            times.retain(|&t| t >= cutoff);
        }
    }
}

/// 训练函数
pub fn train_epoch(
    network: &mut SpikingNeuralNetwork,
    learner: &mut STDPLearner,
    input_patterns: &[(Vec<f64>, Vec<f64>)],  // (输入模式, 目标输出)
    epoch_duration: f64,
) -> f64 {
    let mut total_error = 0.0;

    for (input, target) in input_patterns {
        // 生成输入脉冲
        let mut input_spikes = vec![];
        for (i, &rate) in input.iter().enumerate() {
            if rate > 0.0 {
                // 泊松发放
                let interval = 1000.0 / rate;  // ms
                let mut t = 0.0;
                while t < epoch_duration {
                    input_spikes.push((t, NeuronId(i), 1.0));
                    t += interval;
                }
            }
        }
        input_spikes.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());

        // 运行仿真
        let spikes = network.run(epoch_duration, &input_spikes);

        // 记录脉冲用于STDP
        for spike in &spikes {
            // 判断是输入神经元还是输出神经元
            let is_pre = network.input_neurons.contains(&spike.neuron_id);
            let is_post = network.output_neurons.contains(&spike.neuron_id);

            if is_pre {
                learner.record_spike(spike.neuron_id, true, spike.time);
            }
            if is_post {
                learner.record_spike(spike.neuron_id, false, spike.time);
            }
        }

        // 计算输出误差
        let output_rates = network.output_firing_rates(epoch_duration);
        let error: f64 = target.iter().zip(output_rates.iter())
            .map(|(t, o)| (t - o).powi(2))
            .sum();
        total_error += error;

        // 更新权重
        learner.update_weights(network);
        learner.prune_traces(network.current_time, 100.0);
    }

    total_error / input_patterns.len() as f64
}
```

### 4.3 能耗模型与优化（Rust）

```rust
//! 神经形态计算的能耗模型与优化调度

/// 能耗参数
#[derive(Debug, Clone)]
pub struct EnergyParams {
    pub static_power: f64,        // 静态功耗 (W)
    pub spike_energy: f64,        // 单次脉冲能量 (J)
    pub synaptic_op_energy: f64,  // 突触操作能量 (J)
    pub learning_energy: f64,     // 权重更新能量 (J)
}

impl Default for EnergyParams {
    fn default() -> Self {
        Self {
            static_power: 1e-6,           // 1 µW
            spike_energy: 1e-12,          // 1 pJ per spike
            synaptic_op_energy: 1e-14,    // 0.01 pJ per synaptic operation
            learning_energy: 1e-13,       // 0.1 pJ per weight update
        }
    }
}

/// 能耗计算器
pub struct EnergyCalculator {
    params: EnergyParams,
    total_spikes: u64,
    total_syn_ops: u64,
    total_weight_updates: u64,
    simulation_time: f64,
}

impl EnergyCalculator {
    pub fn new(params: EnergyParams) -> Self {
        Self {
            params,
            total_spikes: 0,
            total_syn_ops: 0,
            total_weight_updates: 0,
            simulation_time: 0.0,
        }
    }

    pub fn record_spike(&mut self) {
        self.total_spikes += 1;
    }

    pub fn record_synaptic_op(&mut self, count: u64) {
        self.total_syn_ops += count;
    }

    pub fn record_weight_update(&mut self, count: u64) {
        self.total_weight_updates += count;
    }

    pub fn add_simulation_time(&mut self, dt: f64) {
        self.simulation_time += dt;
    }

    /// 计算总能耗
    pub fn total_energy(&self) -> f64 {
        let static_energy = self.params.static_power * self.simulation_time / 1000.0;  // W * s = J
        let spike_energy = self.params.spike_energy * self.total_spikes as f64;
        let syn_energy = self.params.synaptic_op_energy * self.total_syn_ops as f64;
        let learning_energy = self.params.learning_energy * self.total_weight_updates as f64;

        static_energy + spike_energy + syn_energy + learning_energy
    }

    /// 计算能效（操作/焦耳）
    pub fn energy_efficiency(&self) -> f64 {
        let total_ops = self.total_syn_ops + self.total_weight_updates;
        if self.total_energy() > 0.0 {
            total_ops as f64 / self.total_energy()
        } else {
            0.0
        }
    }

    /// 生成能耗报告
    pub fn report(&self) -> String {
        format!(
            "=== Energy Report ===\n\
             Simulation time: {:.2} ms\n\
             Total spikes: {}\n\
             Synaptic operations: {}\n\
             Weight updates: {}\n\
             Static energy: {:.6} J\n\
             Dynamic energy: {:.6} J\n\
             Total energy: {:.6} J\n\
             Energy efficiency: {:.2e} ops/J",
            self.simulation_time,
            self.total_spikes,
            self.total_syn_ops,
            self.total_weight_updates,
            self.params.static_power * self.simulation_time / 1000.0,
            self.params.spike_energy * self.total_spikes as f64 +
                self.params.synaptic_op_energy * self.total_syn_ops as f64 +
                self.params.learning_energy * self.total_weight_updates as f64,
            self.total_energy(),
            self.energy_efficiency()
        )
    }
}

/// 能耗感知调度器
pub struct EnergyAwareScheduler {
    energy_calc: EnergyCalculator,
    energy_budget: f64,
}

impl EnergyAwareScheduler {
    pub fn new(energy_budget: f64) -> Self {
        Self {
            energy_calc: EnergyCalculator::new(EnergyParams::default()),
            energy_budget,
        }
    }

    /// 检查是否超过能耗预算
    pub fn within_budget(&self) -> bool {
        self.energy_calc.total_energy() < self.energy_budget
    }

    /// 根据能耗预算动态调整发放阈值
    pub fn adapt_thresholds(&self, network: &mut SpikingNeuralNetwork, scale: f64) {
        for (params, _) in &mut network.neurons {
            // 提高阈值减少发放，降低能耗
            params.v_thresh = params.v_rest + (params.v_thresh - params.v_rest) * scale;
        }
    }
}
```

---

## 5. 经验总结

### 5.1 关键经验

1. **事件驱动优势**：仅在脉冲事件发生时计算，大幅降低能耗
2. **时序编码**：利用脉冲时间编码信息，提高信息密度
3. **在线学习**：STDP实现无监督的实时权重调整

### 5.2 挑战与解决方案

| 挑战 | 解决方案 |
|------|----------|
| 脉冲稀疏性 | 使用稀疏矩阵和事件队列优化 |
| 数值稳定性 | 使用指数欧拉法替代简单欧拉法 |
| 硬件限制 | 模型压缩和剪枝技术 |
| 能耗约束 | 动态电压频率调节（DVFS） |

### 5.3 未来方向

- 大规模神经形态芯片的编译优化
- 神经形态与深度学习混合架构
- 自适应学习率算法
- 边缘设备上的实时应用

---

## 参考文献

1. Maass, W. (1997). Networks of spiking neurons. Neural Computation.
2. Davies, M., et al. (2018). Loihi: A neuromorphic manycore processor with on-chip learning. IEEE Micro.
3. Markram, H., et al. (1997). Regulation of synaptic efficacy by coincidence of postsynaptic APs and EPSPs. Science.
4. Roy, K., et al. (2019). Towards spike-based machine intelligence. Nature.
