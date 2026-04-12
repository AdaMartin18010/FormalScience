/-
# 集合论基本运算的形式化（Lean 4）

本文件包含集合论基本运算的形式化定义和定理证明：
- 并集、交集、补集、幂集
- 基本性质证明
- ZF公理系统的部分形式化

对应文档: FormalRE/01_形式系统详解/01.5_集合论ZF-ZFC.md
-/

-- 引入必要的库
import Mathlib

namespace SetTheory

-- ============================================================
-- 1. 集合基本运算的定义
-- ============================================================

variable {α : Type*} (A B C : Set α)

/-
## 1.1 并集 (Union)

定义: A ∪ B = {x | x ∈ A ∨ x ∈ B}
-/

theorem union_def : A ∪ B = {x | x ∈ A ∨ x ∈ B} := by
  ext x
  simp [Set.mem_union]

/-
## 1.2 交集 (Intersection)

定义: A ∩ B = {x | x ∈ A ∧ x ∈ B}
-/

theorem inter_def : A ∩ B = {x | x ∈ A ∧ x ∈ B} := by
  ext x
  simp [Set.mem_inter]

/-
## 1.3 补集 (Complement)

定义: Aᶜ = {x | x ∉ A}
-/

theorem compl_def : Aᶜ = {x | x ∉ A} := by
  ext x
  simp [Set.mem_compl_iff]

/-
## 1.4 幂集 (Power Set)

定义: 𝒫(A) = {S | S ⊆ A}
-/

theorem powerset_def : 𝒫 A = {S | S ⊆ A} := by
  ext S
  simp [Set.mem_powerset_iff]

-- ============================================================
-- 2. 集合运算的基本性质
-- ============================================================

/-
## 2.1 交换律 (Commutativity)

A ∪ B = B ∪ A
A ∩ B = B ∩ A
-/

theorem union_comm : A ∪ B = B ∪ A := by
  ext x
  simp [or_comm]

theorem inter_comm : A ∩ B = B ∩ A := by
  ext x
  simp [and_comm]

/-
## 2.2 结合律 (Associativity)

(A ∪ B) ∪ C = A ∪ (B ∪ C)
(A ∩ B) ∩ C = A ∩ (B ∩ C)
-/

theorem union_assoc : (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  ext x
  simp [or_assoc]

theorem inter_assoc : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  ext x
  simp [and_assoc]

/-
## 2.3 分配律 (Distributivity)

A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)
A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)
-/

theorem union_inter_distrib : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  simp
  tauto

theorem inter_union_distrib : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  simp
  tauto

/-
## 2.4 德摩根律 (De Morgan's Laws)

(A ∪ B)ᶜ = Aᶜ ∩ Bᶜ
(A ∩ B)ᶜ = Aᶜ ∪ Bᶜ
-/

theorem de_morgan_union : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  simp [not_or]

theorem de_morgan_inter : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ := by
  ext x
  simp [not_and_or]

/-
## 2.5 幂集性质

A ⊆ B ↔ 𝒫(A) ⊆ 𝒫(B)
-/

theorem powerset_mono : A ⊆ B ↔ 𝒫 A ⊆ 𝒫 B := by
  constructor
  · intro h S hS
    simp at hS ⊢
    exact fun x hx => h (hS x hx)
  · intro h x hx
    have : {x} ⊆ A := by simp [hx]
    have : {x} ∈ 𝒫 A := by simpa using this
    have : {x} ∈ 𝒫 B := h this
    simpa using this

-- ============================================================
-- 3. 外延公理 (Axiom of Extensionality)
-- ============================================================

/-
## 3.1 外延公理的形式化

两个集合相等当且仅当它们具有相同的元素：
∀A ∀B (∀x (x ∈ A ↔ x ∈ B) → A = B)
-/

theorem extensionality : (∀ x, x ∈ A ↔ x ∈ B) → A = B := by
  intro h
  ext x
  exact h x

-- ============================================================
-- 4. 集合包含关系的性质
-- ============================================================

/-
## 4.1 自反性

A ⊆ A
-/

theorem subset_refl : A ⊆ A := by
  intro x hx
  exact hx

/-
## 4.2 反对称性

A ⊆ B ∧ B ⊆ A → A = B
-/

theorem subset_antisymm : A ⊆ B → B ⊆ A → A = B := by
  intro h1 h2
  ext x
  constructor
  · intro hx
    exact h1 hx
  · intro hx
    exact h2 hx

/-
## 4.3 传递性

A ⊆ B ∧ B ⊆ C → A ⊆ C
-/

theorem subset_trans : A ⊆ B → B ⊆ C → A ⊆ C := by
  intro h1 h2 x hx
  exact h2 (h1 hx)

-- ============================================================
-- 5. 空集和全集的性质
-- ============================================================

variable [Inhabited α]

/-
## 5.1 空集的性质

空集是所有集合的子集：∅ ⊆ A
-/

theorem empty_subset : ∅ ⊆ A := by
  intro x hx
  simp at hx

/-
## 5.2 全集的性质

每个集合都是全集的子集：A ⊆ Set.univ
-/

theorem subset_univ : A ⊆ Set.univ := by
  intro x hx
  simp

-- ============================================================
-- 6. Cantor定理：|A| < |𝒫(A)|
-- ============================================================

/-
## 6.1 不存在从A到𝒫(A)的满射

这是Cantor定理的核心部分
-/

theorem cantor_surjective : ¬∃ f : α → Set α, Function.Surjective f := by
  intro ⟨f, hf⟩
  let S := {x | x ∉ f x}
  obtain ⟨y, hy⟩ := hf S
  have h : y ∈ S ↔ y ∉ f y := by simp [S]
  rw [hy] at h
  exact h.mpr (h.mp (by rw [hy]))

/-
## 6.2 Cantor定理的推论

对于任何集合A，存在比A更大的集合（幂集）
-/

theorem cantor_theorem : ∀ A : Set α, ∃ B : Set (Set α), 
    Nonempty (A ≃ B) → False := by
  intro A
  use 𝒫 A
  rintro ⟨e⟩
  apply cantor_surjective
  use fun a => e.toFun a
  intro S
  use e.invFun S
  apply e.right_inv

end SetTheory

-- ============================================================
-- 7. 关系与函数的形式化
-- ============================================================

namespace Relations

variable {α β : Type*}

/-
## 7.1 关系的基本性质

一个关系R是传递的：∀x y z, R x y → R y z → R x z
-/

def Transitive (R : α → α → Prop) : Prop :=
  ∀ x y z, R x y → R y z → R x z

def Reflexive (R : α → α → Prop) : Prop :=
  ∀ x, R x x

def Symmetric (R : α → α → Prop) : Prop :=
  ∀ x y, R x y → R y x

/-
## 7.2 等价关系

等价关系 = 自反 + 对称 + 传递
-/

class Equivalence (R : α → α → Prop) where
  refl : Reflexive R
  symm : Symmetric R
  trans : Transitive R

/-
## 7.3 函数作为特殊关系

函数是左全且右单的关系
-/

def IsFunctional (R : α → β → Prop) : Prop :=
  (∀ x, ∃ y, R x y) ∧  -- 左全
  (∀ x y z, R x y → R x z → y = z)  -- 右单

end Relations
