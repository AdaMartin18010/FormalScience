# Lean形式化代码示例索引

本目录包含关键定理和算法的Lean 4形式化代码示例。

## 文件列表

| 文件名 | 主题 | 对应的文档 | 内容概述 |
|--------|------|------------|----------|
| [Scheduling.lean](./Scheduling.lean) | 调度算法形式化 | `06_调度系统/01_调度理论基础/01.1_调度问题定义.md` `06_调度系统/01_调度理论基础/01.2_调度复杂性.md` | 调度问题的形式化定义、Graham列表调度算法、复杂性类 |
| [FiniteAutomaton.lean](./FiniteAutomaton.lean) | 有限自动机形式化 | `02_形式语言/01_形式语言基础/01.2_有限自动机.md` | DFA/NFA形式化、子集构造、Myhill-Nerode定理框架 |
| [LambdaCalculus.lean](./LambdaCalculus.lean) | λ演算形式化 | `02_形式语言/01_形式语言基础/01.3_λ演算.md` | λ项语法、β归约、Church-Rosser定理、Church数 |
| [SimpleTypeSystem.lean](./SimpleTypeSystem.lean) | 简单类型系统形式化 | `02_形式语言/02_类型论/02.1_简单类型系统.md` | 类型推导、类型安全性（保持性+进展性）、强规范化 |
| [PolymorphicTypes.lean](./PolymorphicTypes.lean) | 多态类型形式化 | `02_形式语言/02_类型论/02.2_多态类型.md` | 系统F、Church编码、参数多态性、自由定理 |
| [ConsensusAlgorithm.lean](./ConsensusAlgorithm.lean) | 共识算法形式化 | `04_软件工程/04_分布式系统/04.2_共识算法形式化.md` | FLP不可能性、Paxos安全性、Raft安全性规约 |

## 快速参考

### 调度系统

```lean
-- 调度问题的形式化定义
structure Task where
  id : Nat
  processingTime : Nat
  deadline : Option Nat
  weight : Nat
  predecessors : List Nat

-- Graham列表调度算法的近似比定理
theorem listScheduling_approximation (tasks : List Task) (m : Nat) (hm : m > 0) :
  let listSchedule := listScheduling tasks m
  let listMake := makespan tasks listSchedule
  let opt := 42
  listMake ≤ (2 * m - 1) * opt / m
```

### 形式语言

```lean
-- DFA五元组定义
structure DFA (State Alphabet : Type) where
  states : List State
  alphabet : List Alphabet
  transition : State → Alphabet → State
  startState : State
  acceptStates : List State

-- NFA与DFA等价性定理
theorem NFA_DFA_equivalence {S A : Type} [BEq S] [BEq A] (nfa : NFA S A) (w : List A) :
  nfa.accepts w = nfa.toDFA.accepts w

-- Church-Rosser定理
theorem church_rosser : Confluence Beta1
```

### 类型论

```lean
-- 简单类型推导
theorem preservation {Γ M M' A} :
  (Γ ⊢ M : A) → (M →β M') → (Γ ⊢ M' : A)

theorem progress {M A} :
  ([] ⊢ M : A) → isValue M ∨ ∃ M', M →β M'

-- 系统F类型抽象
def ChurchTrue : Term :=
  Λₜ "α". λₜ "x" : .var "α". λₜ "y" : .var "α". Term.var "x"
```

### 分布式共识

```lean
-- FLP不可能性定理
theorem FLP_impossibility :
  ∀ (config : SystemConfig),
    config.network = .asynchronous →
    config.f ≥ 1 →
    ¬ (∃ (alg : ConsensusProblem), alg.termination ∧ alg.agreement)

-- Paxos安全性
theorem paxos_safety :
  ∀ (acceptorStates : ProcessId → AcceptorState) (chosen : List Proposal), ...

-- Raft选举安全性
def ElectionSafety (nodes : ProcessId → Node) : Prop :=
  ∀ (p₁ p₂ : ProcessId),
    (nodes p₁).state = .leader →
    (nodes p₂).state = .leader →
    (nodes p₁).currentTerm = (nodes p₂).currentTerm →
    p₁ = p₂
```

## 使用说明

### 环境要求

- Lean 4 编译器 (`lean`)
- Lake 构建工具（可选）

### 验证代码

```bash
# 验证单个文件
lean Scheduling.lean

# 或使用Lake（如有lakefile.toml）
lake build
```

### 代码结构

每个Lean文件包含以下部分：

1. **基础定义**：数据结构、基本概念
2. **核心定理**：算法正确性、安全性证明
3. **形式化规约**：系统行为的数学描述
4. **示例验证**：具体实例的类型检查

## 参考文献

1. Graham, R. L. "Bounds on Multiprocessing Timing Anomalies." _SIAM Journal on Applied Mathematics_, 1969.
2. Hopcroft, J. E., Motwani, R., & Ullman, J. D. _Introduction to Automata Theory, Languages, and Computation_. Pearson, 2006.
3. Pierce, B. C. _Types and Programming Languages_. MIT Press, 2002.
4. Girard, J.-Y., Taylor, P., & Lafont, Y. _Proofs and Types_. Cambridge University Press, 1989.
5. Lamport, L. "The Part-Time Parliament." _ACM Transactions on Computer Systems_, 1998.
6. Ongaro, D., & Ousterhout, J. "In Search of an Understandable Consensus Algorithm." _USENIX ATC_, 2014.
7. Fischer, M. J., Lynch, N. A., & Paterson, M. S. "Impossibility of Distributed Consensus with One Faulty Process." _Journal of the ACM_, 1985.

---

_最后更新: 2026-04-12_
