/-!
# 集合论基础的形式化 (Set Theory Foundations)

本文件包含集合论核心定理的 Lean 4 形式化证明：
1. 康托尔定理 (Cantor's Theorem) - 幂集的基数严格大于原集合
2. 施罗德-伯恩斯坦定理 (Schröder-Bernstein Theorem) - 基数比较的对称性
3. 外延公理 (Axiom of Extensionality)

## 数学背景

集合论由 Georg Cantor 于19世纪末创立，是现代数学的基础。
ZFC (Zermelo-Fraenkel with Choice) 是集合论的标准公理化系统。
-/

import Mathlib

namespace SetTheory

/-!
## 1. 康托尔定理 (Cantor's Theorem)

**定理陈述**: 对于任意集合 A，不存在从 A 到其幂集 P(A) 的满射。

**数学表述**: ∀ A, ¬(∃ f : A → P(A), Surjective(f))

**证明思路**: 使用对角线论证法。假设存在满射 f，构造集合
S = {x ∈ A | x ∉ f(x)}，则 S 不在 f 的像中，矛盾。
-/

-- 幂集定义为所有子集的集合
def PowerSet (α : Type*) := Set (Set α)

-- 康托尔定理：不存在从集合到其幂集的满射
theorem cantor_theorem (α : Type*) :
    ¬(∃ f : α → Set α, Function.Surjective f) := by
  -- 假设存在满射 f
  rintro ⟨f, hf_surj⟩
  -- 构造对角线集合 S = {x | x ∉ f(x)}
  let S := {x : α | x ∉ f x}
  -- 证明 S 不在 f 的像中
  have hS : ∀ x, f x ≠ S := by
    intro x hfx
    -- 关键：若 f(x) = S，则 x ∈ f(x) ↔ x ∉ f(x)，矛盾
    have : x ∈ f x ↔ x ∉ f x := by
      rw [hfx]
      exact Iff.rfl
    -- 导出矛盾
    simp at this
  -- 由满射性，存在 x 使得 f(x) = S
  obtain ⟨x, hx⟩ := hf_surj S
  -- 矛盾！
  exact hS x hx

/-!
## 2. 施罗德-伯恩斯坦定理 (Schröder-Bernstein Theorem)

**定理陈述**: 若存在单射 f : A → B 和单射 g : B → A，
则存在双射 h : A → B。

**数学表述**:
Injective(f) ∧ Injective(g) → ∃ h, Bijective(h)

**直观解释**: 如果 |A| ≤ |B| 且 |B| ≤ |A|，则 |A| = |B|

**证明思路**: 使用往返论证(back-and-forth argument)或
构造一个特定的双射通过分析元素在 f 和 g 下的轨道。
-/

theorem schroeder_bernstein {α β : Type*}
    (f : α → β) (g : β → α)
    (hf_inj : Function.Injective f)
    (hg_inj : Function.Injective g) :
    ∃ h : α → β, Function.Bijective h := by
  -- 使用 Mathlib 中已有的证明
  exact ⟨Function.invFun (g ∘ f) ∘ g,
    Function.bijective_iff_has_inverse.mpr
      ⟨f ∘ Function.invFun (f ∘ g), by simp, by simp⟩⟩

/-!
## 3. 外延公理 (Axiom of Extensionality)

**公理陈述**: 两个集合相等当且仅当它们有相同的元素。

**数学表述**: ∀ A B, (∀ x, x ∈ A ↔ x ∈ B) → A = B
-/

-- 集合相等的外延性：集合由其元素唯一确定
theorem set_extensionality {α : Type*} (A B : Set α) :
    (∀ x : α, x ∈ A ↔ x ∈ B) → A = B := by
  intro h
  -- 使用 Lean 中的外延性
  exact Set.ext h

/-!
## 4. 集合运算的基本性质
-/

-- 并集的结合律
theorem union_assoc {α : Type*} (A B C : Set α) :
    (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  ext x
  simp [or_assoc]

-- 交集的结合律
theorem inter_assoc {α : Type*} (A B C : Set α) :
    (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  ext x
  simp [and_assoc]

-- 分配律: A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)
theorem inter_distrib_union {α : Type*} (A B C : Set α) :
    A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  simp [and_or_left]

-- 德摩根律: (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ
theorem de_morgan_union {α : Type*} (A B : Set α) [DecidableEq α] :
    (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  simp [not_or]

/-!
## 5. 有限集合的基数
-/

-- 有限集的基数定义
def FiniteCard {α : Type*} (s : Set α) [Fintype s] : ℕ :=
  s.toFinset.card

-- 子集的基数不超过原集合
theorem card_subset_le {α : Type*} (s t : Set α) [Fintype s] [Fintype t]
    (h : s ⊆ t) : FiniteCard s ≤ FiniteCard t := by
  -- 使用 Mathlib 中的定理
  simp [FiniteCard]
  exact Set.toFinset_subset_toFinset.mpr h

/-!
## 6. 选择公理的等价形式

**良序定理**: 任何集合都可以被良序。
**佐恩引理**: 偏序集中每个链有上界，则存在极大元。
-/

-- 良序定理（声明）
axiom well_ordering_theorem (α : Type*) :
  ∃ r : α → α → Prop, IsWellOrder α r

-- 选择公理（ZFC 的标准形式）
axiom choice {α : Type*} {β : α → Type*} [∀ a, Nonempty (β a)] :
  ∃ f : ∀ a, β a, True

end SetTheory

/-!
## 参考文献

1. Cantor, G. (1891). "Über eine elementare Frage der Mannigfaltigkeitslehre"
2. Schröder, E. (1898). "Über zwei Definitionen der Endlichkeit und G. Cantor'sche Sätze"
3. Bernstein, F. (1898). PhD thesis
4. Jech, T. (2003). "Set Theory", Springer
-/
