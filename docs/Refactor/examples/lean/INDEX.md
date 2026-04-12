# FormalScience Lean 4 形式化代码索引

本文档汇总了 FormalScience 项目中所有的 Lean 4 形式化代码示例。

## 快速导航

| 领域 | 文件 | 定理/概念 |
|------|------|----------|
| **集合论** | [SetTheory.lean](./SetTheory.lean) | 康托尔定理、施罗德-伯恩斯坦定理 |
| **群论** | [GroupTheory.lean](./GroupTheory.lean) | Lagrange定理、同态基本定理 |
| **λ演算** | [LambdaCalculus.lean](./LambdaCalculus.lean) | Church-Rosser定理、Church编码 |
| **类型论** | [SimplyTypedLambda.lean](./SimplyTypedLambda.lean) | 类型安全性、Curry-Howard对应 |
| **时序逻辑** | [LinearTemporalLogic.lean](./LinearTemporalLogic.lean) | LTL语义、安全性/活性 |
| **Petri网** | [PetriNet.lean](./PetriNet.lean) | 可达性、有界性、活性 |
| **调度系统** | [Scheduling.lean](./Scheduling.lean) | 调度约束、SPT最优性 |

## 文件详情

### 1. SetTheory.lean (4.9 KB)

**集合论基础的形式化**

- **康托尔定理**: 证明不存在从集合到其幂集的满射
- **施罗德-伯恩斯坦定理**: 证明基数比较的对称性
- **外延公理**: 集合相等的判定
- **德摩根律**: 集合运算的基本性质

```lean
theorem cantor_theorem (α : Type*) :
    ¬(∃ f : α → Set α, Function.Surjective f)
```

### 2. GroupTheory.lean (7.8 KB)

**群论基础的形式化**

- **群公理**: 封闭性、结合律、单位元、逆元
- **Lagrange定理**: 子群的阶整除群的阶
- **同态基本定理**: G/ker(φ) ≅ im(φ)
- **轨道-稳定子定理**: 群作用的计数公式

```lean
theorem lagrange_theorem {G : Type*} [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H.carrier] :
    ∃ k : ℕ, Fintype.card G = Fintype.card H.carrier * k
```

### 3. LambdaCalculus.lean (7.8 KB)

**λ演算的形式化**

- **语法定义**: 变量、抽象、应用
- **自由变量**: FV函数的定义
- **捕获避免替换**: subst函数
- **β归约**: 一步归约关系
- **Church-Rosser定理**: 合流性声明
- **Church编码**: 自然数、算术运算
- **Y组合子**: 不动点组合子

```lean
inductive Term where
  | var : String → Term
  | abs : String → Term → Term
  | app : Term → Term → Term

theorem church_rosser : Confluence Beta1
```

### 4. SimplyTypedLambda.lean (9.2 KB)

**简单类型λ演算的形式化**

- **类型语法**: 基类型、函数类型
- **类型推导**: Typing归纳关系
- **类型唯一性**: 每个项有唯一类型
- **替换引理**: 替换保持类型
- **进展性定理**: 良类型项可继续归约
- **类型保持定理**: 归约保持类型
- **强正规化**: 良类型项必然终止
- **Curry-Howard对应**: 命题即类型

```lean
theorem typing_uniqueness {Γ : Context} {t : Term} {τ₁ τ₂ : Ty}
    (h₁ : Γ ⊢ t : τ₁) (h₂ : Γ ⊢ t : τ₂) : τ₁ = τ₂

theorem progress {t τ} (ht : [] ⊢ t : τ) :
    Value t ∨ ∃ t', t →₁ t'

theorem preservation {Γ t t' τ} (ht : Γ ⊢ t : τ) (hr : t →₁ t') :
    Γ ⊢ t' : τ
```

### 5. LinearTemporalLogic.lean (8.8 KB)

**线性时序逻辑的形式化**

- **LTL语法**: 原子命题、时序算子(X, F, G, U)
- **Kripke结构**: 状态、转移、标记
- **路径语义**: 满足关系的归纳定义
- **对偶律**: ¬Xφ ≡ X¬φ, ¬Fφ ≡ G¬φ
- **语义等价性**: 算子之间的等价关系
- **性质模式**: 安全性、活性、公平性

```lean
inductive LTL (AP : Type) where
  | true | false | atom : AP → LTL AP
  | neg | and | or | next | until

theorem finally_duality {S AP L π φ} :
    (π ⊨ (¬(F φ)) ↔ π ⊨ (G (¬φ)))
```

### 6. PetriNet.lean (8.9 KB)

**Petri网理论的形式化**

- **网结构**: 库所、变迁、流关系、权重
- **标记**: 令牌分布函数
- **前集/后集**: •t 和 t•
- **变迁使能**: 触发条件
- **变迁触发**: 标记变换函数
- **可达性**: Reachable归纳关系
- **有界性**: k-bounded定义
- **活性**: L1-live定义
- **特殊网类**: 状态机、标记图、自由选择网

```lean
structure PetriNet (P T : Type) where
  places : Finset P
  transitions : Finset T
  flow : Finset ((P × T) ⊕ (T × P))
  weight : Weight P T

inductive Reachable {P T : Type} [DecidableEq P]
    (N : PetriNet P T) (M₀ : Marking P) : Marking P → Prop
```

### 7. Scheduling.lean (10.5 KB)

**调度系统的形式化**

- **任务定义**: id, 处理时间, 截止时间, 权重, 前置任务
- **资源定义**: id, 容量
- **调度方案**: 任务到(资源, 开始时间)的映射
- **约束条件**:
  - 独占性约束（资源互斥）
  - 完整性约束（所有任务被调度）
  - 前置依赖约束
- **目标函数**: 完工时间、流程时间、延迟
- **调度算法**: SPT、EDD、列表调度
- **Graham记号**: 调度问题的分类
- **复杂性结果**: 多项式时间可解性类型类

```lean
structure Task where
  id : Nat
  processingTime : Nat
  deadline : Option Nat
  weight : Nat := 1
  predecessors : List Nat := []

def sptSchedule (tasks : List Task) : List Task

theorem listScheduling_approximation (tasks : List Task)
    (m : Nat) (hm : m > 0) : listMake ≤ (2 * m - 1) * opt / m
```

## 统计信息

| 统计项 | 数量 |
|--------|------|
| 总文件数 | 7 个主要文件 |
| 总代码行数 | ~1500 行 |
| 形式化定义 | ~50 个 |
| 定理陈述 | ~30 个 |
| 完整证明 | ~15 个 |
| 待完成证明 | ~15 个 (使用 sorry) |

## 依赖关系

```
SetTheory.lean
    └── Mathlib

GroupTheory.lean
    └── Mathlib

LambdaCalculus.lean
    └── Mathlib

SimplyTypedLambda.lean
    └── Mathlib

LinearTemporalLogic.lean
    └── Mathlib

PetriNet.lean
    └── Mathlib

Scheduling.lean
    └── Mathlib
```

## 使用建议

1. **初学者**: 从 `SetTheory.lean` 开始，理解基本证明技巧
2. **类型论**: 阅读 `LambdaCalculus.lean` 和 `SimplyTypedLambda.lean`
3. **形式化验证**: 查看 `LinearTemporalLogic.lean` 和 `PetriNet.lean`
4. **系统理论**: 研究 `Scheduling.lean` 中的约束定义

## 扩展方向

- [ ] 完成所有标记为 `sorry` 的证明
- [ ] 添加更多调度算法的形式化（如 EDF、LLF）
- [ ] 形式化 CTL (计算树逻辑)
- [ ] 添加进程代数 (CSP, CCS)
- [ ] 形式化实时调度理论
- [ ] 添加同伦类型论 (HoTT) 基础

## 参考文献

- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Lean 4 API Documentation](https://leanprover-community.github.io/mathlib4_docs/)
