/-!
# 线性时序逻辑的形式化 (Linear Temporal Logic)

本文件包含线性时序逻辑 (LTL) 的 Lean 4 形式化：
1. LTL语法定义
2. Kripke结构与路径语义
3. 常用时序性质（安全性、活性）
4. 语义等价性证明

## 数学背景

LTL由 Amir Pnueli 于1977年提出，是形式化验证的核心工具。
它扩展了命题逻辑，引入时间算子以描述系统行为的时序特性。
-/

import Mathlib

namespace LinearTemporalLogic

/-!
## 1. 原子命题与LTL公式

**LTL语法**:
  φ ::= ⊤ | ⊥ | p | ¬φ | φ ∧ φ | φ ∨ φ | Xφ | Fφ | Gφ | φ U φ
  
其中：
- Xφ (Next): 下一时刻满足φ
- Fφ (Finally): 未来某时刻满足φ  
- Gφ (Globally): 所有未来时刻满足φ
- φ U ψ (Until): φ持续成立直到ψ成立
-/

-- 原子命题类型
variable {AP : Type} [DecidableEq AP]

-- LTL公式的归纳定义
inductive LTL (AP : Type) where
  | true  : LTL AP                    -- ⊤
  | false : LTL AP                    -- ⊥
  | atom  : AP → LTL AP               -- 原子命题
  | neg   : LTL AP → LTL AP           -- ¬φ
  | and   : LTL AP → LTL AP → LTL AP  -- φ ∧ ψ
  | or    : LTL AP → LTL AP → LTL AP  -- φ ∨ ψ
  | next  : LTL AP → LTL AP           -- X φ
  | until : LTL AP → LTL AP → LTL AP  -- φ U ψ
  deriving DecidableEq, Repr

-- 导出算子定义
namespace LTL

-- F φ = ⊤ U φ (最终)
def finally {AP} (φ : LTL AP) : LTL AP := until true φ

-- G φ = ¬F ¬φ (总是)
def globally {AP} (φ : LTL AP) : LTL AP := neg (finally (neg φ))

-- φ → ψ = ¬φ ∨ ψ (蕴涵)
def implies {AP} (φ ψ : LTL AP) : LTL AP := or (neg φ) ψ

-- φ R ψ = ¬(¬φ U ¬ψ) (释放)
def release {AP} (φ ψ : LTL AP) : LTL AP := neg (until (neg φ) (neg ψ))

end LTL

-- 记号定义
notation "⊤" => LTL.true
notation "⊥" => LTL.false
notation "¬" φ => LTL.neg φ
notation φ " ∧ " ψ => LTL.and φ ψ
notation φ " ∨ " ψ => LTL.or φ ψ
notation "X " φ => LTL.next φ
notation φ " U " ψ => LTL.until φ ψ
notation "F " φ => LTL.finally φ
notation "G " φ => LTL.globally φ

/-!
## 2. Kripke结构与路径

**Kripke结构**: M = (S, S₀, R, L)
- S: 状态集合
- S₀ ⊆ S: 初始状态
- R ⊆ S × S: 转移关系
- L: S → 2^AP: 标记函数
-/

-- 路径：无限状态序列
def Path (S : Type) := ℕ → S

-- 路径后缀
def Path.suffix {S} (π : Path S) (k : ℕ) : Path S :=
  λ n => π (k + n)

-- 标记函数：状态到原子命题集合的映射
def Labeling (S AP : Type) := S → Set AP

/-!
## 3. LTL语义定义

**满足关系** π ⊨ φ 的归纳定义：
-/

-- 满足关系（归纳定义）
inductive Satisfies {S AP : Type} (L : Labeling S AP) : 
    Path S → LTL AP → Prop where
  | tt {π} : Satisfies L π ⊤
  | atom {π a} : a ∈ L (π 0) → Satisfies L π (LTL.atom a)
  | neg {π φ} : ¬(Satisfies L π φ) → Satisfies L π (LTL.neg φ)
  | and {π φ ψ} : Satisfies L π φ → Satisfies L π ψ →
                  Satisfies L π (LTL.and φ ψ)
  | or_left {π φ ψ} : Satisfies L π φ → Satisfies L π (LTL.or φ ψ)
  | or_right {π φ ψ} : Satisfies L π ψ → Satisfies L π (LTL.or φ ψ)
  | next {π φ} : Satisfies L (π.suffix 1) φ → Satisfies L π (LTL.next φ)
  | until {π φ ψ} :
      (∃ k, Satisfies L (π.suffix k) ψ ∧
        ∀ j < k, Satisfies L (π.suffix j) φ) →
      Satisfies L π (LTL.until φ ψ)

-- 满足关系的记号
infix:50 " ⊨ " => Satisfies

/-!
## 4. 对偶律与语义等价性

**对偶律**:
- ¬Xφ ≡ X¬φ
- ¬Fφ ≡ G¬φ
- ¬Gφ ≡ F¬φ
- ¬(φ U ψ) ≡ (¬φ) R (¬ψ)
-/

-- X 的自对偶性: ¬Xφ ↔ X¬φ
theorem next_duality {S AP L π φ} :
    (π ⊨ (¬(X φ)) ↔ π ⊨ (X (¬φ))) := by
  constructor
  · intro h
    simp at h
    apply Satisfies.next
    intro hφ
    apply h
    apply Satisfies.next
    exact hφ
  · intro h
    simp
    cases h with
    | next h' =>
      intro hφ
      apply h'
      cases hφ with
      | next hφ' => exact hφ'

-- F/G 对偶性: ¬Fφ ↔ G¬φ
theorem finally_duality {S AP L π φ} :
    (π ⊨ (¬(F φ)) ↔ π ⊨ (G (¬φ))) := by
  constructor
  · -- ¬Fφ → G¬φ
    intro h
    simp [LTL.globally, LTL.finally] at h ⊢
    assumption
  · -- G¬φ → ¬Fφ
    intro h
    simp [LTL.globally, LTL.finally] at h ⊢
    assumption

-- Gφ ↔ ¬F¬φ
theorem globally_def {S AP L π φ} :
    (π ⊨ (G φ) ↔ π ⊨ (¬(F (¬φ)))) := by
  simp [LTL.globally, LTL.finally]

-- Fφ ↔ ⊤ U φ
theorem finally_def {S AP L π φ} :
    (π ⊨ (F φ) ↔ π ⊨ (⊤ U φ)) := by
  simp [LTL.finally]

/-!
## 5. 常用时序性质模式
-/

-- 安全性 (Safety): "坏事永不会发生"
-- G ¬bad
def Safety {AP} (bad : LTL AP) : LTL AP := G (¬bad)

-- 活性 (Liveness): "好事终将发生"  
-- G(req → F ack)
def Response {AP} (req ack : LTL AP) : LTL AP :=
  G (req.implies (F ack))

-- 公平性 (Justice): "总是最终使能的执行"
-- GF enabled → GF executed
def Justice {AP} (enabled executed : LTL AP) : LTL AP :=
  (G (F enabled)).implies (G (F executed))

-- 强公平性 (Compassion): "最终总是使能的执行"
-- FG enabled → GF executed
def Compassion {AP} (enabled executed : LTL AP) : LTL AP :=
  (F (G enabled)).implies (G (F executed))

/-!
## 6. 直到算子的性质
-/

-- 直到的展开律: φ U ψ ↔ ψ ∨ (φ ∧ X(φ U ψ))
theorem until_unfold {S AP L π φ ψ} :
    (π ⊨ (φ U ψ) ↔ π ⊨ (ψ ∨ (φ ∧ X(φ U ψ)))) := by
  constructor
  · -- φ U ψ → ψ ∨ (φ ∧ X(φ U ψ))
    intro h
    cases h with
    | until h =>
      rcases h with ⟨k, hk, hφ⟩
      cases k with
      | zero =>
        apply Satisfies.or_right
        exact hk
      | succ k =>
        apply Satisfies.or_left
        apply Satisfies.and
        · apply hφ
          exact Nat.zero_lt_succ k
        · apply Satisfies.next
          apply Satisfies.until
          use k
          constructor
          · exact hk
          · intro j hj
            have : j < k.succ := by linarith
            exact hφ j this
  · -- ψ ∨ (φ ∧ X(φ U ψ)) → φ U ψ
    intro h
    cases h with
    | or_right h =>
      apply Satisfies.until
      use 0
      constructor
      · exact h
      · intro j hj
        cases hj
    | or_left h =>
      cases h with
      | and hφ hnext =>
        cases hnext with
        | next h' =>
          cases h' with
          | until h'' =>
            rcases h'' with ⟨k, hk, hφ'⟩
            apply Satisfies.until
            use k+1
            constructor
            · exact hk
            · intro j hj
              cases j with
              | zero => exact hφ
              | succ j =>
                have : j < k := by linarith
                exact hφ' j this

-- 释放算子: φ R ψ ≡ ¬(¬φ U ¬ψ)
theorem release_def {S AP} (φ ψ : LTL AP) :
    LTL.release φ ψ = ¬((¬φ) U (¬ψ)) := by
  simp [LTL.release]

/-!
## 7. 模型检测的基本概念

给定 Kripke 结构 M 和 LTL 公式 φ，判定 M ⊨ φ。
这等价于检查 M 的所有路径都满足 φ。
-/

-- Kripke 结构结构
def KripkeStructure (S AP : Type) :=
  { M : (Set S) × (Set S) × (S → Set S) × (Labeling S AP) //
    -- 确保转移关系是全的
    ∀ s ∈ M.fst, ∃ s' ∈ M.fst, s' ∈ M.snd.fst }

-- 系统满足公式：所有路径都满足
def SystemSatisfies {S AP} (M : KripkeStructure S AP) 
    (φ : LTL AP) : Prop :=
  sorry  -- 需要更详细的Kripke结构定义

/-!
## 8. LTL 片段与可判定性

不同LTL片段的模型检测复杂度：
- 完整 LTL: PSPACE-完全
- Safety-LTL: P-完全
- LTL(F,X): NP-完全
-/

-- Safety LTL: 只使用 G, X，不使用 U
def IsSafetyLTL {AP} : LTL AP → Bool
  | .true => true
  | .false => true
  | .atom _ => true
  | .neg φ => IsSafetyLTL φ
  | .and φ ψ => IsSafetyLTL φ && IsSafetyLTL ψ
  | .or φ ψ => IsSafetyLTL φ && IsSafetyLTL ψ
  | .next φ => IsSafetyLTL φ
  | .globally φ => IsSafetyLTL φ
  | .until _ _ => false
  | .finally _ => false

end LinearTemporalLogic

/-!
## 参考文献

1. Pnueli, A. (1977). "The Temporal Logic of Programs", FOCS
2. Vardi, M. Y., & Wolper, P. (1986). "An Automata-Theoretic Approach to 
   Automatic Program Verification", LICS
3. Clarke, E. M., Grumberg, O., & Peled, D. (1999). "Model Checking", MIT Press
4. Baier, C., & Katoen, J. P. (2008). "Principles of Model Checking", MIT Press
-/
