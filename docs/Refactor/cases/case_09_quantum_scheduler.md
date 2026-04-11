# 案例9：量子计算调度系统

## 1. 背景介绍

### 1.1 问题背景

量子计算作为一种新兴计算范式，利用量子叠加和纠缠特性解决经典计算机难以处理的问题。然而，量子硬件面临以下挑战：

- **退相干时间有限**：量子比特（qubit）的相干时间极短（微秒到毫秒级）
- **门操作错误率**：量子门操作存在固有误差
- **拓扑限制**：并非所有量子比特对都能直接交互
- **经典-量子混合**：需要高效的经典控制与量子执行的协同

量子调度系统负责在有限的量子硬件资源上优化量子电路的执行，最大化计算保真度和吞吐量。

### 1.2 挑战与目标

**主要挑战：**

- 量子门之间的依赖关系复杂
- 需要最小化电路深度以减少退相干影响
- 硬件拓扑约束下的最优映射
- 误差累积的动态估计与缓解

**设计目标：**

- 形式化量子电路的调度模型
- 证明调度策略的最优性或近似比
- 量子-经典混合调度的正确性保证
- 实时误差分析和自适应调度

### 1.3 相关研究

- **Qiskit (IBM)**: 量子电路编译与调度框架
- **Cirq (Google)**: 量子电路描述与模拟
- **Surface Code**: 量子纠错码
- **VQE/QAOA**: 变分量子算法

---

## 2. 形式化规约

### 2.1 量子计算模型

```
QuantumSystem = (Qubits, Gates, Circuit, NoiseModel, Scheduler)
```

其中：

- `Qubits`: 量子比特集合及其物理属性
- `Gates`: 可用的量子门集合
- `Circuit`: 量子电路（有向无环图）
- `NoiseModel`: 噪声模型和误差参数
- `Scheduler`: 调度策略

### 2.2 量子电路形式化

```lean4
-- 量子比特标识
abbrev QubitId := Nat

-- 量子门类型
inductive Gate
  | H (q : QubitId)                    -- Hadamard门
  | X (q : QubitId)                    -- Pauli-X门
  | Y (q : QubitId)                    -- Pauli-Y门
  | Z (q : QubitId)                    -- Pauli-Z门
  | CNOT (control target : QubitId)    -- 受控非门
  | RZ (q : QubitId) (θ : Float)       -- Z旋转门
  | RX (q : QubitId) (θ : Float)       -- X旋转门
  | Measure (q : QubitId)              -- 测量门
  deriving DecidableEq, Repr

-- 量子电路为门的偏序集合（DAG）
structure QuantumCircuit where
  num_qubits : Nat
  gates : List GateNode
  dependencies : Graph Nat  -- 门之间的依赖图

structure GateNode where
  id : Nat
  gate : Gate
  duration : Float          -- 执行时间（纳秒）
  error_rate : Float        -- 本征误差率

-- 电路深度：最长路径长度
def CircuitDepth (circuit : QuantumCircuit) : Nat :=
  longestPathLength circuit.dependencies
```

### 2.3 硬件拓扑约束

```lean4
-- 硬件连接图
structure HardwareTopology where
  num_qubits : Nat
  connectivity : Graph QubitId  -- 可交互的量子比特对
  gate_times : Gate → Float     -- 各门的执行时间
  error_rates : Gate → Float    -- 各门的误差率

-- 门是否可在硬件上执行
def Executable (gate : Gate) (topology : HardwareTopology) : Prop :=
  match gate with
  | Gate.H q | Gate.X q | Gate.Y q | Gate.Z q | Gate.RZ q _ | Gate.RX q _ =>
    q < topology.num_qubits
  | Gate.CNOT c t =>
    c < topology.num_qubits ∧ t < topology.num_qubits ∧
    topology.connectivity.hasEdge c t
  | Gate.Measure q =>
    q < topology.num_qubits

-- 电路是否可执行
def CircuitExecutable (circuit : QuantumCircuit) (topology : HardwareTopology) : Prop :=
  ∀ gate ∈ circuit.gates, Executable gate.gate topology
```

### 2.4 调度问题形式化

```lean4
-- 调度：为每个门分配开始时间
def Schedule := GateNode → Float

-- 调度有效性约束
def ValidSchedule (circuit : QuantumCircuit) (schedule : Schedule) : Prop :=
  -- 1. 依赖约束：前置门完成后才能开始
  (∀ g1 g2, dependsOn circuit g1 g2 →
    schedule g1 + g1.duration ≤ schedule g2) ∧
  -- 2. 资源约束：同一量子比特不能同时执行多个门
  (∀ g1 g2, sharesQubit g1 g2 →
    schedule g1 + g1.duration ≤ schedule g2 ∨
    schedule g2 + g2.duration ≤ schedule g1)

-- 调度目标：最小化完成时间（makespan）
def Makespan (circuit : QuantumCircuit) (schedule : Schedule) : Float :=
  List.maximum (circuit.gates.map (fun g => schedule g + g.duration))

-- 最优调度
def OptimalSchedule (circuit : QuantumCircuit) (schedule : Schedule) : Prop :=
  ValidSchedule circuit schedule ∧
  ∀ s', ValidSchedule circuit s' →
    Makespan circuit schedule ≤ Makespan circuit s'
```

---

## 3. 证明/验证过程

### 3.1 门调度优化

```lean4
-- ASAP（尽可能早）调度
def ASAPSchedule (circuit : QuantumCircuit) : Schedule :=
  fun gate =>
    let preds := predecessors circuit.dependencies gate.id
    if preds.isEmpty then 0.0
    else List.maximum (preds.map (fun p =>
      let pred_gate := circuit.gates[p]!
      ASAPSchedule circuit pred_gate + pred_gate.duration))

-- ALAP（尽可能晚）调度
def ALAPSchedule (circuit : QuantumCircuit) (deadline : Float) : Schedule :=
  fun gate =>
    let succs := successors circuit.dependencies gate.id
    if succs.isEmpty then deadline - gate.duration
    else List.minimum (succs.map (fun s =>
      let succ_gate := circuit.gates[s]!
      ALAPSchedule circuit deadline succ_gate - gate.duration))

-- 关键路径调度定理
theorem critical_path_scheduling_optimal :
  ∀ (circuit : QuantumCircuit),
    let schedule := ASAPSchedule circuit
    ValidSchedule circuit schedule ∧
    ∀ s, ValidSchedule circuit s →
      Makespan circuit schedule ≤ Makespan circuit s := by
  -- 证明ASAP调度产生最优makespan
  -- 1. 证明ASAP满足所有约束
  -- 2. 证明任何其他调度的makespan不会更小
  sorry
```

### 3.2 量子比特映射

```lean4
-- 逻辑到物理量子比特的映射
def QubitMapping := QubitId → QubitId

-- 映射的有效性
def ValidMapping (circuit : QuantumCircuit)
    (topology : HardwareTopology) (mapping : QubitMapping) : Prop :=
  -- 单射：一个物理量子比特不能映射多个逻辑量子比特
  Injective mapping ∧
  -- 范围约束
  (∀ q, mapping q < topology.num_qubits)

-- SWAP插入以解决连接性限制
def InsertSwaps (circuit : QuantumCircuit)
    (topology : HardwareTopology) (mapping : QubitMapping) : QuantumCircuit :=
  -- 对于每个非本地CNOT，插入SWAP序列
  sorry

-- 映射质量：估计总执行时间
def MappingCost (circuit : QuantumCircuit)
    (topology : HardwareTopology) (mapping : QubitMapping) : Float :=
  let mapped_circuit := InsertSwaps circuit topology mapping
  let schedule := ASAPSchedule mapped_circuit
  Makespan mapped_circuit schedule

-- 最优映射问题是NP难的，但可以证明近似算法界
theorem swap_insertion_approximation :
  ∀ (circuit : QuantumCircuit) (topology : HardwareTopology),
    ∃ (mapping : QubitMapping) (algorithm : SwapInsertionAlgo),
      let cost := MappingCost circuit topology mapping
      let opt_cost := optimalMappingCost circuit topology
      cost ≤ 2 * opt_cost := by
  -- 证明2-近似算法存在
  sorry
```

### 3.3 误差分析

```lean4
-- 保真度衰减模型
def CircuitFidelity (circuit : QuantumCircuit) (schedule : Schedule)
    (noise : NoiseModel) : Float :=
  circuit.gates.prod (fun g =>
    let idle_time := calculateIdleTime g schedule circuit
    gateFidelity g noise * decoherenceFactor idle_time noise)

-- 门保真度
def gateFidelity (gate : GateNode) (noise : NoiseModel) : Float :=
  1.0 - gate.error_rate - noise.additionalError gate

-- 退相干因子
def decoherenceFactor (idle_time : Float) (noise : NoiseModel) : Float :=
  Float.exp (-idle_time / noise.t2_time)

-- 误差累积上界
theorem error_accumulation_bound :
  ∀ (circuit : QuantumCircuit) (schedule : Schedule) (noise : NoiseModel),
    let depth := CircuitDepth circuit
    let ε := List.maximum (circuit.gates.map (·.error_rate))
    CircuitFidelity circuit schedule noise ≥ (1 - ε) ^ depth := by
  -- 证明误差累积受电路深度限制
  sorry
```

---

## 4. 代码实现

### 4.1 量子电路调度器（Rust）

```rust
//! 量子电路调度系统
//! 实现量子门的最优调度和映射

use std::collections::{HashMap, HashSet, VecDeque};
use petgraph::graph::{DiGraph, NodeIndex};
use petgraph::algo::toposort;
use serde::{Serialize, Deserialize};

/// 量子比特标识
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct QubitId(pub usize);

/// 量子门类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Gate {
    H(QubitId),
    X(QubitId),
    Y(QubitId),
    Z(QubitId),
    CNOT { control: QubitId, target: QubitId },
    RZ(QubitId, f64),
    RX(QubitId, f64),
    Measure(QubitId),
}

impl Gate {
    /// 获取门操作的量子比特
    pub fn qubits(&self) -> Vec<QubitId> {
        match self {
            Gate::H(q) | Gate::X(q) | Gate::Y(q) | Gate::Z(q) |
            Gate::RZ(q, _) | Gate::RX(q, _) | Gate::Measure(q) => vec![*q],
            Gate::CNOT { control, target } => vec![*control, *target],
        }
    }

    /// 是否为双量子比特门
    pub fn is_two_qubit(&self) -> bool {
        matches!(self, Gate::CNOT { .. })
    }
}

/// 门节点（包含调度信息）
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GateNode {
    pub id: usize,
    pub gate: Gate,
    pub duration_ns: f64,      // 执行时间（纳秒）
    pub error_rate: f64,       // 本征误差率
}

/// 量子电路
pub struct QuantumCircuit {
    pub num_qubits: usize,
    pub gates: Vec<GateNode>,
    pub dependency_graph: DiGraph<usize, ()>,
    pub gate_indices: HashMap<usize, NodeIndex>,
}

impl QuantumCircuit {
    pub fn new(num_qubits: usize) -> Self {
        Self {
            num_qubits,
            gates: vec![],
            dependency_graph: DiGraph::new(),
            gate_indices: HashMap::new(),
        }
    }

    /// 添加门到电路
    pub fn add_gate(&mut self, gate: Gate, duration_ns: f64, error_rate: f64) -> usize {
        let id = self.gates.len();
        let node = self.dependency_graph.add_node(id);
        self.gate_indices.insert(id, node);

        self.gates.push(GateNode {
            id,
            gate,
            duration_ns,
            error_rate,
        });

        id
    }

    /// 添加依赖关系
    pub fn add_dependency(&mut self, from: usize, to: usize) {
        if let (Some(&from_node), Some(&to_node)) =
            (self.gate_indices.get(&from), self.gate_indices.get(&to)) {
            self.dependency_graph.add_edge(from_node, to_node, ());
        }
    }

    /// 基于量子比特使用自动构建依赖
    pub fn build_dependencies(&mut self) {
        // 追踪每个量子比特上最后一个门
        let mut last_gate: HashMap<QubitId, usize> = HashMap::new();

        for gate_node in &self.gates {
            let gate_id = gate_node.id;

            for qubit in gate_node.gate.qubits() {
                if let Some(&prev_gate) = last_gate.get(&qubit) {
                    if prev_gate != gate_id {
                        self.add_dependency(prev_gate, gate_id);
                    }
                }
                last_gate.insert(qubit, gate_id);
            }
        }
    }

    /// 获取拓扑排序
    pub fn topological_order(&self) -> Result<Vec<usize>, String> {
        toposort(&self.dependency_graph, None)
            .map(|order| order.iter()
                .filter_map(|&node| self.dependency_graph[node].into())
                .collect())
            .map_err(|e| format!("Cycle detected: {:?}", e))
    }

    /// 计算电路深度
    pub fn depth(&self) -> usize {
        let order = self.topological_order().unwrap_or_default();
        let mut depths: HashMap<usize, usize> = HashMap::new();

        for &gate_id in &order {
            let predecessors: Vec<usize> = self.dependency_graph
                .neighbors_directed(self.gate_indices[&gate_id], petgraph::Direction::Incoming)
                .filter_map(|n| self.dependency_graph[n].into())
                .collect();

            let pred_depth = predecessors.iter()
                .filter_map(|&p| depths.get(&p))
                .max()
                .copied()
                .unwrap_or(0);

            depths.insert(gate_id, pred_depth + 1);
        }

        depths.values().max().copied().unwrap_or(0)
    }
}

/// 调度方案
#[derive(Debug, Clone, Default)]
pub struct Schedule {
    pub start_times: HashMap<usize, f64>,  // gate_id -> start_time (ns)
}

impl Schedule {
    pub fn new() -> Self {
        Self {
            start_times: HashMap::new(),
        }
    }

    pub fn set_start(&mut self, gate_id: usize, time: f64) {
        self.start_times.insert(gate_id, time);
    }

    pub fn get_start(&self, gate_id: usize) -> f64 {
        self.start_times.get(&gate_id).copied().unwrap_or(0.0)
    }

    pub fn get_end(&self, circuit: &QuantumCircuit, gate_id: usize) -> f64 {
        let start = self.get_start(gate_id);
        let duration = circuit.gates.get(gate_id)
            .map(|g| g.duration_ns)
            .unwrap_or(0.0);
        start + duration
    }

    /// 计算makespan
    pub fn makespan(&self, circuit: &QuantumCircuit) -> f64 {
        circuit.gates.iter()
            .map(|g| self.get_end(circuit, g.id))
            .fold(0.0, f64::max)
    }
}

/// 调度器
pub struct Scheduler;

impl Scheduler {
    /// ASAP（尽可能早）调度
    pub fn asap_schedule(circuit: &QuantumCircuit) -> Schedule {
        let mut schedule = Schedule::new();
        let order = circuit.topological_order().unwrap_or_default();

        for &gate_id in &order {
            // 找到所有前驱门的最早完成时间
            let pred_end = circuit.dependency_graph
                .neighbors_directed(circuit.gate_indices[&gate_id], petgraph::Direction::Incoming)
                .filter_map(|n| circuit.dependency_graph[n])
                .map(|pred_id| schedule.get_end(circuit, pred_id))
                .fold(0.0, f64::max);

            schedule.set_start(gate_id, pred_end);
        }

        schedule
    }

    /// ALAP（尽可能晚）调度
    pub fn alap_schedule(circuit: &QuantumCircuit, deadline: f64) -> Schedule {
        let mut schedule = Schedule::new();
        let order = circuit.topological_order().unwrap_or_default();
        let mut reverse_order: Vec<_> = order.iter().copied().rev().collect();

        for &gate_id in &reverse_order {
            let gate = &circuit.gates[gate_id];

            // 找到所有后继门的最晚开始时间
            let succ_start = circuit.dependency_graph
                .neighbors_directed(circuit.gate_indices[&gate_id], petgraph::Direction::Outgoing)
                .filter_map(|n| circuit.dependency_graph[n])
                .map(|succ_id| schedule.get_start(succ_id))
                .fold(deadline, f64::min);

            let start = succ_start - gate.duration_ns;
            schedule.set_start(gate_id, start.max(0.0));
        }

        schedule
    }

    /// 列表调度（考虑资源约束）
    pub fn list_schedule(circuit: &QuantumCircuit, num_qubits: usize) -> Schedule {
        let mut schedule = Schedule::new();
        let mut ready: VecDeque<usize> = VecDeque::new();
        let mut in_degree: HashMap<usize, usize> = HashMap::new();

        // 计算入度
        for gate in &circuit.gates {
            let degree = circuit.dependency_graph
                .neighbors_directed(circuit.gate_indices[&gate.id], petgraph::Direction::Incoming)
                .count();
            in_degree.insert(gate.id, degree);
            if degree == 0 {
                ready.push_back(gate.id);
            }
        }

        // 追踪每个量子比特的可用时间
        let mut qubit_available: Vec<f64> = vec![0.0; num_qubits];

        while let Some(gate_id) = ready.pop_front() {
            let gate = &circuit.gates[gate_id];

            // 计算最早开始时间
            let pred_end = circuit.dependency_graph
                .neighbors_directed(circuit.gate_indices[&gate_id], petgraph::Direction::Incoming)
                .filter_map(|n| circuit.dependency_graph[n])
                .map(|pred_id| schedule.get_end(circuit, pred_id))
                .fold(0.0, f64::max);

            // 考虑量子比特资源
            let qubit_ready = gate.gate.qubits()
                .iter()
                .map(|q| qubit_available[q.0])
                .fold(0.0, f64::max);

            let start = pred_end.max(qubit_ready);
            schedule.set_start(gate_id, start);

            let end = start + gate.duration_ns;

            // 更新量子比特可用时间
            for qubit in gate.gate.qubits() {
                qubit_available[qubit.0] = end;
            }

            // 更新后继门的入度
            for succ_node in circuit.dependency_graph
                .neighbors_directed(circuit.gate_indices[&gate_id], petgraph::Direction::Outgoing) {
                if let Some(succ_id) = circuit.dependency_graph[succ_node] {
                    let count = in_degree.get_mut(&succ_id).unwrap();
                    *count -= 1;
                    if *count == 0 {
                        ready.push_back(succ_id);
                    }
                }
            }
        }

        schedule
    }
}
```

### 4.2 硬件拓扑与映射（Rust）

```rust
//! 量子硬件拓扑与量子比特映射

use std::collections::{HashMap, HashSet};

/// 硬件连接拓扑
#[derive(Debug, Clone)]
pub struct HardwareTopology {
    pub num_qubits: usize,
    pub connections: Vec<(QubitId, QubitId)>,
    pub gate_durations: HashMap<String, f64>,
    pub error_rates: HashMap<String, f64>,
}

impl HardwareTopology {
    /// 创建线性拓扑
    pub fn linear(n: usize) -> Self {
        let mut connections = vec![];
        for i in 0..n-1 {
            connections.push((QubitId(i), QubitId(i+1)));
        }

        Self {
            num_qubits: n,
            connections,
            gate_durations: default_gate_durations(),
            error_rates: default_error_rates(),
        }
    }

    /// 创建网格拓扑
    pub fn grid(width: usize, height: usize) -> Self {
        let mut connections = vec![];
        let n = width * height;

        for y in 0..height {
            for x in 0..width {
                let idx = y * width + x;
                if x < width - 1 {
                    connections.push((QubitId(idx), QubitId(idx + 1)));
                }
                if y < height - 1 {
                    connections.push((QubitId(idx), QubitId(idx + width)));
                }
            }
        }

        Self {
            num_qubits: n,
            connections,
            gate_durations: default_gate_durations(),
            error_rates: default_error_rates(),
        }
    }

    /// 检查两个量子比特是否相邻
    pub fn is_adjacent(&self, q1: QubitId, q2: QubitId) -> bool {
        self.connections.iter().any(|&(a, b)| {
            (a == q1 && b == q2) || (a == q2 && b == q1)
        })
    }

    /// 获取邻居量子比特
    pub fn neighbors(&self, q: QubitId) -> Vec<QubitId> {
        self.connections.iter()
            .filter_map(|&(a, b)| {
                if a == q { Some(b) }
                else if b == q { Some(a) }
                else { None }
            })
            .collect()
    }
}

fn default_gate_durations() -> HashMap<String, f64> {
    let mut map = HashMap::new();
    map.insert("H".to_string(), 35.0);      // 35ns
    map.insert("X".to_string(), 35.0);      // 35ns
    map.insert("CNOT".to_string(), 100.0);  // 100ns
    map.insert("MEASURE".to_string(), 300.0); // 300ns
    map
}

fn default_error_rates() -> HashMap<String, f64> {
    let mut map = HashMap::new();
    map.insert("H".to_string(), 0.001);
    map.insert("X".to_string(), 0.001);
    map.insert("CNOT".to_string(), 0.01);
    map.insert("MEASURE".to_string(), 0.05);
    map
}

/// 量子比特映射：逻辑 -> 物理
pub type QubitMapping = HashMap<QubitId, QubitId>;

/// 映射求解器
pub struct MappingSolver;

impl MappingSolver {
    /// 简单的贪婪映射算法
    pub fn greedy_map(circuit: &QuantumCircuit, topology: &HardwareTopology) -> QubitMapping {
        let mut mapping = HashMap::new();
        let mut used_physical: HashSet<QubitId> = HashSet::new();

        // 统计每个逻辑量子比特的使用频率
        let mut qubit_usage: HashMap<QubitId, usize> = HashMap::new();
        for gate in &circuit.gates {
            for qubit in gate.gate.qubits() {
                *qubit_usage.entry(qubit).or_insert(0) += 1;
            }
        }

        // 按使用频率降序排序
        let mut qubits_by_usage: Vec<_> = qubit_usage.iter().collect();
        qubits_by_usage.sort_by(|a, b| b.1.cmp(a.1));

        // 贪婪映射：最常用的逻辑量子比特映射到连接度最高的物理量子比特
        let mut physical_connectivity: Vec<_> = (0..topology.num_qubits)
            .map(|i| (QubitId(i), topology.neighbors(QubitId(i)).len()))
            .collect();
        physical_connectivity.sort_by(|a, b| b.1.cmp(&a.1));

        for ((logical_qubit, _), (physical_qubit, _)) in
            qubits_by_usage.iter().zip(physical_connectivity.iter()) {
            if !used_physical.contains(physical_qubit) {
                mapping.insert(*logical_qubit, *physical_qubit);
                used_physical.insert(*physical_qubit);
            }
        }

        mapping
    }

    /// 计算映射后的电路（插入必要的SWAP）
    pub fn apply_mapping(circuit: &QuantumCircuit,
                         topology: &HardwareTopology,
                         mapping: &QubitMapping) -> QuantumCircuit {
        let mut new_circuit = QuantumCircuit::new(topology.num_qubits);

        for gate_node in &circuit.gates {
            let mapped_gate = match &gate_node.gate {
                Gate::H(q) => Gate::H(*mapping.get(q).unwrap_or(q)),
                Gate::X(q) => Gate::X(*mapping.get(q).unwrap_or(q)),
                Gate::CNOT { control, target } => {
                    let mapped_control = *mapping.get(control).unwrap_or(control);
                    let mapped_target = *mapping.get(target).unwrap_or(target);

                    if topology.is_adjacent(mapped_control, mapped_target) {
                        Gate::CNOT {
                            control: mapped_control,
                            target: mapped_target
                        }
                    } else {
                        // 需要插入SWAP序列（简化处理）
                        todo!("Insert SWAP chain for non-adjacent qubits")
                    }
                }
                _ => gate_node.gate.clone(),
            };

            new_circuit.add_gate(
                mapped_gate,
                gate_node.duration_ns,
                gate_node.error_rate,
            );
        }

        new_circuit.build_dependencies();
        new_circuit
    }
}
```

---

## 5. 经验总结

### 5.1 关键经验

1. **调度优化**：ASAP/ALAP调度与列表调度结合可获得接近最优的电路深度
2. **误差感知**：调度时需考虑门误差率和退相干时间
3. **硬件协同**：编译器应充分利用特定硬件拓扑

### 5.2 挑战与解决方案

| 挑战 | 解决方案 |
|------|----------|
| 量子比特连接限制 | 启发式映射算法 + SWAP网络插入 |
| 退相干 | 最小化电路深度，动态解码 |
| 门误差累积 | 误差缓解技术（零噪声外推等） |
| 经典-量子通信 | 流水线调度和异步执行 |

### 5.3 未来方向

- 自适应调度（根据实时误差调整）
- 量子纠错的调度优化
- 多量子计算机协同调度
- 量子-经典混合算法的优化

---

## 参考文献

1. Nielsen, M. A., & Chuang, I. L. (2010). Quantum Computation and Quantum Information.
2. Venturelli, D., et al. (2018). Compiling quantum circuits to realistic hardware architectures. Nature Physics.
3. Li, G., et al. (2019). Tackling the qubit mapping problem for NISQ-era quantum devices. ASPLOS.
4. Cross, A. W., et al. (2017). Open Quantum Assembly Language. arXiv.
