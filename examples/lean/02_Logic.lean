/-
# 数理逻辑的形式化（Lean 4）

本文件包含数理逻辑的形式化定义和定理证明：
- 命题逻辑（命题连接词、真值表、 tautology）
- 谓词逻辑（量词、谓词、语义）
- 经典逻辑与直觉主义逻辑的区别

对应文档: FormalRE/01_形式系统详解/01.5_集合论ZF-ZFC.md
-/

import Mathlib

namespace Logic

-- ============================================================
-- 1. 命题逻辑基础
-- ============================================================

/-
## 1.1 命题逻辑连接词

在Lean中，命题逻辑连接词已经内建：
- ∧ : 合取 (And)
- ∨ : 析取 (Or)  
- → : 蕴含 (Implies)
- ¬ : 否定 (Not)
- ↔ : 等价 (Iff)
- True : 真
- False : 假
-/

/-
## 1.2 合取 (∧) 的性质
-/

-- 合取的交换律：P ∧ Q ↔ Q ∧ P
theorem and_comm (P Q : Prop) : P ∧ Q ↔ Q ∧ P := by
  apply Iff.intro
  · intro h
    exact ⟨h.2, h.1⟩
  · intro h
    exact ⟨h.2, h.1⟩

-- 合取的结合律：(P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R)
theorem and_assoc (P Q R : Prop) : (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R) := by
  apply Iff.intro
  · intro h
    exact ⟨h.1.1, ⟨h.1.2, h.2⟩⟩
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

-- 合取的幂等律：P ∧ P ↔ P
theorem and_idempotent (P : Prop) : P ∧ P ↔ P := by
  apply Iff.intro
  · intro h
    exact h.1
  · intro h
    exact ⟨h, h⟩

/-
## 1.3 析取 (∨) 的性质
-/

-- 析取的交换律：P ∨ Q ↔ Q ∨ P
theorem or_comm (P Q : Prop) : P ∨ Q ↔ Q ∨ P := by
  apply Iff.intro
  · intro h
    cases h with
    | inl hp => exact Or.inr hp
    | inr hq => exact Or.inl hq
  · intro h
    cases h with
    | inl hq => exact Or.inr hq
    | inr hp => exact Or.inl hp

-- 析取的结合律：(P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R)
theorem or_assoc (P Q R : Prop) : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) := by
  apply Iff.intro
  · intro h
    cases h with
    | inl h1 => 
      cases h1 with
      | inl hp => exact Or.inl hp
      | inr hq => exact Or.inr (Or.inl hq)
    | inr hr => exact Or.inr (Or.inr hr)
  · intro h
    cases h with
    | inl hp => exact Or.inl (Or.inl hp)
    | inr h1 => 
      cases h1 with
      | inl hq => exact Or.inl (Or.inr hq)
      | inr hr => exact Or.inr hr

-- 析取的幂等律：P ∨ P ↔ P
theorem or_idempotent (P : Prop) : P ∨ P ↔ P := by
  apply Iff.intro
  · intro h
    cases h with
    | inl hp => exact hp
    | inr hp => exact hp
  · intro h
  exact Or.inl h

/-
## 1.4 分配律
-/

-- 析取对合取的分配律：P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R)
theorem or_and_distrib (P Q R : Prop) : P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  apply Iff.intro
  · intro h
    cases h with
    | inl hp => 
      constructor
      · exact Or.inl hp
      · exact Or.inl hp
    | inr hqr => 
      constructor
      · exact Or.inr hqr.1
      · exact Or.inr hqr.2
  · intro h
    cases h.1 with
    | inl hp => exact Or.inl hp
    | inr hq => 
      cases h.2 with
      | inl hp => exact Or.inl hp
      | inr hr => exact Or.inr ⟨hq, hr⟩

-- 合取对析取的分配律：P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R)
theorem and_or_distrib (P Q R : Prop) : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  apply Iff.intro
  · intro h
    cases h.2 with
    | inl hq => exact Or.inl ⟨h.1, hq⟩
    | inr hr => exact Or.inr ⟨h.1, hr⟩
  · intro h
    cases h with
    | inl hpq => exact ⟨hpq.1, Or.inl hpq.2⟩
    | inr hpr => exact ⟨hpr.1, Or.inr hpr.2⟩

/-
## 1.5 德摩根律 (De Morgan's Laws)
-/

-- 经典德摩根律1：¬(P ∧ Q) ↔ ¬P ∨ ¬Q（需要排中律）
open Classical

theorem de_morgan_and (P Q : Prop) : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  apply Iff.intro
  · intro h
    by_cases hp : P
    · by_cases hq : Q
      · exfalso
        exact h ⟨hp, hq⟩
      · exact Or.inr hq
    · exact Or.inl hp
  · intro h hpq
    cases h with
    | inl hnp => exact hnp hpq.1
    | inr hnq => exact hnq hpq.2

-- 经典德摩根律2：¬(P ∨ Q) ↔ ¬P ∧ ¬Q（无需排中律）
theorem de_morgan_or (P Q : Prop) : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  apply Iff.intro
  · intro h
    constructor
    · intro hp
      exact h (Or.inl hp)
    · intro hq
      exact h (Or.inr hq)
  · intro h hpq
    cases hpq with
    | inl hp => exact h.1 hp
    | inr hq => exact h.2 hq

-- ============================================================
-- 2. 蕴含和等价的性质
-- ============================================================

/-
## 2.1 蕴含的性质
-/

-- 蕴含的自反性：P → P
theorem implies_refl (P : Prop) : P → P := by
  intro hp
  exact hp

-- 蕴含的传递性：(P → Q) → (Q → R) → (P → R)
theorem implies_trans (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) := by
  intro hpq hqr hp
  exact hqr (hpq hp)

-- 假命题蕴含任何命题：False → P
theorem ex_falso (P : Prop) : False → P := by
  intro h
  cases h

/-
## 2.2 等价的性质
-/

-- 等价的自反性：P ↔ P
theorem iff_refl (P : Prop) : P ↔ P := by
  exact Iff.rfl

-- 等价的对称性：(P ↔ Q) → (Q ↔ P)
theorem iff_symm (P Q : Prop) : (P ↔ Q) → (Q ↔ P) := by
  intro h
  exact h.symm

-- 等价的传递性：(P ↔ Q) → (Q ↔ R) → (P ↔ R)
theorem iff_trans (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hpq hqr
  exact hpq.trans hqr

-- ============================================================
-- 3. 谓词逻辑 (Predicate Logic)
-- ============================================================

variable {α : Type*}

/-
## 3.1 全称量词 (∀) 的性质
-/

-- 全称实例化：∀ x, P x → P a
theorem forall_elim {P : α → Prop} (a : α) : (∀ x, P x) → P a := by
  intro h
  exact h a

-- 全称引入：若对任意a可证P a，则可证∀ x, P x
theorem forall_intro {P : α → Prop} : (∀ a, P a) → ∀ x, P x := by
  intro h x
  exact h x

/-
## 3.2 存在量词 (∃) 的性质
-/

-- 存在引入：P a → ∃ x, P x
theorem exists_intro {P : α → Prop} {a : α} : P a → ∃ x, P x := by
  intro h
  exact ⟨a, h⟩

-- 存在消去：∃ x, P x → (∀ a, P a → Q) → Q
theorem exists_elim {P : α → Prop} {Q : Prop} : 
    (∃ x, P x) → (∀ a, P a → Q) → Q := by
  intro hex hall
  cases hex with
  | intro a ha => 
    exact hall a ha

/-
## 3.3 量词否定
-/

-- ¬(∀ x, P x) ↔ ∃ x, ¬P x（经典逻辑）
theorem not_forall (P : α → Prop) : ¬(∀ x, P x) ↔ ∃ x, ¬P x := by
  apply Iff.intro
  · intro h
    by_contra hne
    apply h
    intro x
    by_contra hnx
    exact hne ⟨x, hnx⟩
  · intro hex hall
    cases hex with
    | intro x hnx => 
      exact hnx (hall x)

-- ¬(∃ x, P x) ↔ ∀ x, ¬P x
theorem not_exists (P : α → Prop) : ¬(∃ x, P x) ↔ ∀ x, ¬P x := by
  apply Iff.intro
  · intro h x hpx
    apply h
    exact ⟨x, hpx⟩
  · intro h hex
    cases hex with
    | intro x hpx => 
      exact h x hpx

/-
## 3.4 量词交换
-/

-- ∃∀ → ∀∃（单向）
theorem exists_forall_impl_forall_exists (P : α → α → Prop) :
    (∃ x, ∀ y, P x y) → ∀ y, ∃ x, P x y := by
  intro hex y
  cases hex with
  | intro x hx => 
    exact ⟨x, hx y⟩

-- ∀∀ ↔ ∀∀（显然可交换）
theorem forall_forall_comm (P : α → α → Prop) :
    (∀ x y, P x y) ↔ (∀ y x, P x y) := by
  apply Iff.intro
  · intro h y x
    exact h x y
  · intro h x y
    exact h y x

-- ============================================================
-- 4. 经典逻辑原理
-- ============================================================

/-
## 4.1 排中律 (Law of Excluded Middle)

∀ P, P ∨ ¬P
-/

theorem excluded_middle (P : Prop) : P ∨ ¬P := by
  apply em

/-
## 4.2 双重否定消除

¬¬P → P
-/

theorem double_negation_elim (P : Prop) : ¬¬P → P := by
  intro hnnp
  by_contra hnp
  exact hnnp hnp

/-
## 4.3 反证法

(¬P → False) → P
-/

theorem proof_by_contradiction (P : Prop) : (¬P → False) → P := by
  intro h
  by_contra hnp
  exact h hnp

/-
## 4.4 Peirce定律

((P → Q) → P) → P
-/

theorem peirce (P Q : Prop) : ((P → Q) → P) → P := by
  intro h
  by_contra hnp
  have h1 : P → Q := by
    intro hp
    exfalso
    exact hnp hp
  exact hnp (h h1)

-- ============================================================
-- 5. 一些重要的永真式 (Tautologies)
-- ============================================================

/-
## 5.1 肯定前件式 (Modus Ponens)
(P → Q) → P → Q
-/
theorem modus_ponens (P Q : Prop) : (P → Q) → P → Q := by
  intro hpq hp
  exact hpq hp

/-
## 5.2 三段论
(P → Q) → (Q → R) → (P → R)
-/
theorem hypothetical_syllogism (P Q R : Prop) : 
    (P → Q) → (Q → R) → (P → R) := by
  intro hpq hqr hp
  exact hqr (hpq hp)

/-
## 5.3 构造性二难
(P → Q) → (R → S) → (P ∨ R) → (Q ∨ S)
-/
theorem constructive_dilemma (P Q R S : Prop) :
    (P → Q) → (R → S) → (P ∨ R) → (Q ∨ S) := by
  intro hpq hrs hpr
  cases hpr with
  | inl hp => exact Or.inl (hpq hp)
  | inr hr => exact Or.inr (hrs hr)

end Logic
