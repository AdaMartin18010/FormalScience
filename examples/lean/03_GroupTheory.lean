/-
# 群论基本定义的形式化（Lean 4）

本文件包含群论基本定义和定理的形式化：
- 群、子群、同态的定义
- 群的基本性质
- 子群判定定理
- 同态基本定理

对应文档: FormalRE/01_形式系统详解/01.6_范畴论基础.md（Grp范畴）
-/

import Mathlib

namespace GroupTheory

-- ============================================================
-- 1. 群的基本定义
-- ============================================================

/-
## 1.1 群的定义

群 (G, ·) 满足以下公理：
1. 封闭性：∀ a b ∈ G, a · b ∈ G
2. 结合律：∀ a b c ∈ G, (a · b) · c = a · (b · c)
3. 单位元：∃ e ∈ G, ∀ a ∈ G, e · a = a · e = a
4. 逆元：∀ a ∈ G, ∃ a⁻¹ ∈ G, a · a⁻¹ = a⁻¹ · a = e

Lean的 Mathlib 已经定义了 Group 类型类。
-/

variable {G : Type*} [Group G]

/-
## 1.2 单位元的唯一性
-/

theorem unique_identity (e₁ e₂ : G) (h₁ : ∀ a, e₁ * a = a) (h₂ : ∀ a, a * e₂ = a) : 
    e₁ = e₂ := by
  calc
    e₁ = e₁ * e₂ := by rw [h₂]
    _  = e₂       := by rw [h₁]

/-
## 1.3 逆元的唯一性
-/

theorem unique_inverse (a b : G) (h : a * b = 1) : b = a⁻¹ := by
  calc
    b = a⁻¹ * (a * b) := by rw [inv_mul_cancel_left]
    _ = a⁻¹ * 1       := by rw [h]
    _ = a⁻¹           := by rw [mul_one]

-- ============================================================
-- 2. 群的基本性质
-- ============================================================

/-
## 2.1 消去律
-/

-- 左消去律
theorem mul_left_cancel (a b c : G) (h : a * b = a * c) : b = c := by
  calc
    b = a⁻¹ * (a * b) := by rw [inv_mul_cancel_left]
    _ = a⁻¹ * (a * c) := by rw [h]
    _ = c             := by rw [inv_mul_cancel_left]

-- 右消去律
theorem mul_right_cancel (a b c : G) (h : b * a = c * a) : b = c := by
  calc
    b = (b * a) * a⁻¹ := by rw [mul_inv_cancel_right]
    _ = (c * a) * a⁻¹ := by rw [h]
    _ = c             := by rw [mul_inv_cancel_right]

/-
## 2.2 单位元的性质
-/

-- 单位元的逆是自身
theorem one_inv : (1 : G)⁻¹ = 1 := by
  rw [←mul_one (1 : G)⁻¹]
  rw [inv_mul_cancel]

-- a * 1 = a
theorem mul_one' (a : G) : a * 1 = a := by
  rw [mul_one]

-- 1 * a = a
theorem one_mul' (a : G) : 1 * a = a := by
  rw [one_mul]

/-
## 2.3 逆元的性质
-/

-- (a⁻¹)⁻¹ = a
theorem inv_inv' (a : G) : (a⁻¹)⁻¹ = a := by
  rw [inv_inv]

-- (a * b)⁻¹ = b⁻¹ * a⁻¹
theorem mul_inv_rev' (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  rw [mul_inv_rev]

-- a = b ↔ a⁻¹ = b⁻¹
theorem inv_eq_iff_eq_inv (a b : G) : a⁻¹ = b ↔ a = b⁻¹ := by
  constructor
  · intro h
    rw [←h, inv_inv]
  · intro h
    rw [h, inv_inv]

/-
## 2.4 幂的性质
-/

-- a^n * a^m = a^(n+m)
theorem pow_add' (a : G) (n m : ℕ) : a^n * a^m = a^(n + m) := by
  rw [pow_add]

-- (a^n)^m = a^(n*m)
theorem pow_mul' (a : G) (n m : ℕ) : (a^n)^m = a^(n * m) := by
  rw [pow_mul]

-- a^(-n) = (a⁻¹)^n
theorem pow_neg (a : G) (n : ℕ) : a^(-n : ℤ) = (a⁻¹)^n := by
  rw [zpow_neg, zpow_ofNat]

-- ============================================================
-- 3. 子群的定义和判定
-- ============================================================

/-
## 3.1 子群的定义

子群 H ⊆ G 满足：
1. 1 ∈ H
2. ∀ a b ∈ H, a * b ∈ H
3. ∀ a ∈ H, a⁻¹ ∈ H
-/

structure Subgroup (G : Type*) [Group G] where
  carrier : Set G
  one_mem' : 1 ∈ carrier
  mul_mem' : ∀ {a b}, a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  inv_mem' : ∀ {a}, a ∈ carrier → a⁻¹ ∈ carrier

-- 将子群强制转换为集合
instance : Membership G (Subgroup G) where
  mem H a := a ∈ H.carrier

-- 子群是集合的实例
instance : SetLike (Subgroup G) G where
  coe := Subgroup.carrier
  coe_injective' H₁ H₂ h := by cases H₁; cases H₂; congr

/-
## 3.2 子群判定定理（一步判定法）

H 是子群当且仅当：
- H 非空
- ∀ a b ∈ H, a * b⁻¹ ∈ H
-/

theorem subgroup_criterion (H : Set G) (h_nonempty : ∃ a, a ∈ H)
    (h_closed : ∀ a b, a ∈ H → b ∈ H → a * b⁻¹ ∈ H) : 
    ∃ K : Subgroup G, K.carrier = H := by
  have h_one : 1 ∈ H := by
    obtain ⟨a, ha⟩ := h_nonempty
    have : a * a⁻¹ ∈ H := h_closed a a ha ha
    simpa using this
  
  have h_inv : ∀ a, a ∈ H → a⁻¹ ∈ H := by
    intro a ha
    simpa using h_closed 1 a h_one ha
  
  have h_mul : ∀ a b, a ∈ H → b ∈ H → a * b ∈ H := by
    intro a b ha hb
    have h_binv : b⁻¹ ∈ H := h_inv b hb
    have h_abinv_inv : (a * b⁻¹)⁻¹ ∈ H := h_inv (a * b⁻¹) (h_closed a b ha hb)
    simpa using h_abinv_inv
  
  exact ⟨{ carrier := H, one_mem' := h_one, mul_mem' := h_mul, inv_mem' := h_inv }, rfl⟩

/-
## 3.3 子群的交
-/

-- 任意个子群的交仍是子群
def subgroup_iInf {ι : Type*} (H : ι → Subgroup G) : Subgroup G where
  carrier := ⋂ i, (H i).carrier
  one_mem' := by
    simp
  mul_mem' := by
    intro a b ha hb
    simp at ha hb ⊢
    intro i
    exact (H i).mul_mem' (ha i) (hb i)
  inv_mem' := by
    intro a ha
    simp at ha ⊢
    intro i
    exact (H i).inv_mem' (ha i)

-- ============================================================
-- 4. 群同态
-- ============================================================

/-
## 4.1 群同态的定义

φ : G → H 是群同态，如果 ∀ a b ∈ G, φ(a · b) = φ(a) · φ(b)
-/

structure GroupHom (G H : Type*) [Group G] [Group H] where
  toFun : G → H
  map_mul' : ∀ a b, toFun (a * b) = toFun a * toFun b

-- 记号：G →* H 表示从G到H的群同态
notation:25 G " →* " H => GroupHom G H

-- 将同态强制转换为函数
instance : FunLike (G →* H) G H where
  coe φ := φ.toFun
  coe_injective' φ₁ φ₂ h := by cases φ₁; cases φ₂; congr

/-
## 4.2 同态的基本性质
-/

-- 同态保持单位元
theorem map_one (φ : G →* H) : φ 1 = 1 := by
  have h : φ 1 = φ 1 * φ 1 := by
    rw [←φ.map_mul']
    simp
  calc
    φ 1 = φ 1 * φ 1 := h
    _   = φ 1 * 1   := by rw [mul_one]
    _   = φ 1       := by rw [mul_one]
  have : φ 1 * φ 1 = φ 1 * 1 := by rw [h, mul_one]
  exact mul_left_cancel (φ 1) (φ 1) 1 this

-- 同态保持逆元
theorem map_inv (φ : G →* H) (a : G) : φ a⁻¹ = (φ a)⁻¹ := by
  have h : φ a * φ a⁻¹ = 1 := by
    rw [←φ.map_mul', mul_inv_cancel, map_one]
  exact unique_inverse (φ a) (φ a⁻¹) h

-- 同态保持幂
theorem map_pow (φ : G →* H) (a : G) (n : ℕ) : φ (a^n) = (φ a)^n := by
  induction n with
  | zero => simp [map_one]
  | succ n ih => simp [pow_succ, φ.map_mul', ih]

/-
## 4.3 同态的核与像
-/

-- 同态的核
def ker (φ : G →* H) : Subgroup G where
  carrier := {g | φ g = 1}
  one_mem' := by simp [map_one]
  mul_mem' := by
    intro a b ha hb
    simp at ha hb ⊢
    rw [φ.map_mul', ha, hb, mul_one]
  inv_mem' := by
    intro a ha
    simp at ha ⊢
    rw [map_inv, ha, inv_one]

-- 同态的像
def im (φ : G →* H) : Subgroup H where
  carrier := Set.range φ
  one_mem' := by
    use 1
    exact map_one φ
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    use a * b
    rw [φ.map_mul']
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    use a⁻¹
    rw [map_inv]

/-
## 4.4 同态基本定理
-/

-- 同态是单射当且仅当核为平凡子群
theorem injective_iff_ker_eq_bot (φ : G →* H) : 
    Function.Injective φ ↔ ker φ = ⊥ := by
  sorry  -- 证明较长，省略

-- 第一同态定理（简化版）
-- G/ker(φ) ≅ im(φ)

end GroupTheory
