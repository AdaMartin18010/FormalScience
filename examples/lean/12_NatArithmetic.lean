/-
# 自然数算术的形式化（Lean 4）

本文件包含自然数基本算术的形式化：
- Peano公理
- 加法、乘法的定义和性质
- 序关系
- 数学归纳法
-/

import Mathlib

namespace NatArithmetic

-- ============================================================
-- 1. Peano公理回顾
-- ============================================================

/-
Peano公理系统：
1. 0 是自然数
2. 每个自然数 n 有唯一的后继 succ(n)
3. 0 不是任何自然数的后继
4. 如果 succ(m) = succ(n)，则 m = n
5. 数学归纳法原理
-/

-- Lean中的Nat就是基于Peano公理的实现
#check Nat
#check Nat.zero  -- 0
#check Nat.succ  -- 后继函数

-- ============================================================
-- 2. 加法的定义和性质
-- ============================================================

-- 加法的递归定义（已经在Lean中定义）
-- n + 0 = n
-- n + succ(m) = succ(n + m)

/-
## 2.1 加法的基本性质
-/

-- 加法单位元：n + 0 = n
theorem add_zero' (n : Nat) : n + 0 = n := by
  simp

-- 0是左单位元：0 + n = n
theorem zero_add' (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Nat.add_succ, ih]

-- 加法结合律：(a + b) + c = a + (b + c)
theorem add_assoc' (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero => simp
  | succ c ih => simp [Nat.add_succ, ih]

-- 加法交换律：a + b = b + a
theorem add_comm' (a b : Nat) : a + b = b + a := by
  induction b with
  | zero => simp [zero_add']
  | succ b ih => simp [Nat.add_succ, Nat.succ_add, ih]

-- 加法消去律：a + b = a + c → b = c
theorem add_left_cancel' (a b c : Nat) (h : a + b = a + c) : b = c := by
  induction a with
  | zero => simp at h; exact h
  | succ a ih => 
    simp [Nat.succ_add] at h
    exact ih h

-- ============================================================
-- 3. 乘法的定义和性质
-- ============================================================

-- 乘法的递归定义（已经在Lean中定义）
-- n * 0 = 0
-- n * succ(m) = n * m + n

/-
## 3.1 乘法的基本性质
-/

-- 乘法零元：n * 0 = 0
theorem mul_zero' (n : Nat) : n * 0 = 0 := by
  simp

-- 零乘：0 * n = 0
theorem zero_mul' (n : Nat) : 0 * n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Nat.mul_succ, ih]

-- 乘法单位元：n * 1 = n
theorem mul_one' (n : Nat) : n * 1 = n := by
  simp

-- 1是左单位元：1 * n = n
theorem one_mul' (n : Nat) : 1 * n = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Nat.mul_succ, ih]

-- 乘法对加法的分配律：a * (b + c) = a * b + a * c
theorem mul_add' (a b c : Nat) : a * (b + c) = a * b + a * c := by
  induction c with
  | zero => simp
  | succ c ih => simp [Nat.mul_succ, ih, add_assoc']

-- 乘法结合律：(a * b) * c = a * (b * c)
theorem mul_assoc' (a b c : Nat) : (a * b) * c = a * (b * c) := by
  induction c with
  | zero => simp
  | succ c ih => simp [Nat.mul_succ, mul_add', ih]

-- 乘法交换律：a * b = b * a
theorem mul_comm' (a b : Nat) : a * b = b * a := by
  induction b with
  | zero => simp [zero_mul']
  | succ b ih => simp [Nat.mul_succ, Nat.succ_mul, ih, add_comm']

-- ============================================================
-- 4. 序关系
-- ============================================================

-- ≤ 的定义：a ≤ b ↔ ∃ c, a + c = b

def le' (a b : Nat) : Prop := ∃ c, a + c = b

notation:50 a " ≤' " b => le' a b

-- le' 等价于标准库中的 ≤
theorem le_equiv (a b : Nat) : a ≤' b ↔ a ≤ b := by
  constructor
  · intro ⟨c, hc⟩
    rw [←hc]
    exact Nat.le_add_right a c
  · intro h
    use b - a
    exact (Nat.add_sub_of_le h).symm

-- 反对称性
theorem le_antisymm' (a b : Nat) (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by
  exact Nat.le_antisymm h₁ h₂

-- 传递性
theorem le_trans' (a b c : Nat) (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  exact Nat.le_trans h₁ h₂

-- 完全性
theorem le_total' (a b : Nat) : a ≤ b ∨ b ≤ a := by
  exact Nat.le_total a b

-- ============================================================
-- 5. 数学归纳法原理
-- ============================================================

-- 强归纳法
theorem strong_induction {P : Nat → Prop} 
    (h : ∀ n, (∀ m < n, P m) → P n) : ∀ n, P n := by
  intro n
  have h' : ∀ m ≤ n, P m := by
    induction n with
    | zero => 
      intro m hm
      have : m = 0 := by linarith
      rw [this]
      apply h
      intro m hm
      linarith
    | succ n ih =>
      intro m hm
      cases Nat.eq_or_lt_of_le hm with
      | inl heq => 
        rw [heq]
        apply h
        intro m hm
        exact ih m (Nat.le_of_lt_succ hm)
      | inr hlt => 
        exact ih m (Nat.le_of_lt_succ hlt)
  exact h' n (Nat.le_refl n)

-- 最小数原理（良序原理）
theorem well_ordering (S : Set Nat) (h : ∃ n, n ∈ S) : 
    ∃ m ∈ S, ∀ n ∈ S, m ≤ n := by
  rcases h with ⟨n, hn⟩
  have : ∃ m ≤ n, m ∈ S ∧ ∀ k ∈ S, m ≤ k := by
    induction n with
    | zero => 
      use 0
      simp
      intro k hk
      exact Nat.zero_le k
    | succ n ih =>
      by_cases h' : ∃ m ∈ S, m ≤ n
      · rcases h' with ⟨m, hmS, hmn⟩
        rcases ih with ⟨m', hm'n, hm'S, hm'min⟩
        use m'
        constructor
        · exact Nat.le_succ_of_le hm'n
        · constructor
          · exact hm'S
          · exact hm'min
      · use n + 1
        constructor
        · rfl
        · constructor
          · exact hn
          · intro k hkS
            by_contra hlt
            push_neg at hlt
            have : k ≤ n := Nat.le_of_lt_succ hlt
            exact h' ⟨k, hkS, this⟩
  rcases this with ⟨m, hmn, hmS, hmmin⟩
  exact ⟨m, hmS, hmmin⟩

-- ============================================================
-- 6. 带余除法
-- ============================================================

-- 除法算法：对于任意 a, b > 0，存在唯一的 q, r 使得
-- a = b * q + r 且 0 ≤ r < b

theorem division_algorithm (a b : Nat) (hb : b > 0) : 
    ∃ q r, a = b * q + r ∧ r < b := by
  induction a using Nat.strongRecOn with
  | ind a ih =>
    by_cases h : a < b
    · use 0, a
      simp
      exact h
    · have : a ≥ b := by linarith
      have : a - b < a := by
        apply Nat.sub_lt_of_pos_le
        · exact hb
        · exact this
      rcases ih (a - b) this with ⟨q, r, heq, hr⟩
      use q + 1, r
      constructor
      · have : a = b + (a - b) := (Nat.add_sub_of_le this).symm
        rw [this, heq]
        ring
      · exact hr

-- 欧几里得算法（求最大公约数）
def gcd : Nat → Nat → Nat
  | a, 0 => a
  | a, b + 1 => gcd (b + 1) (a % (b + 1))

-- gcd的基本性质
theorem gcd_dvd_left (a b : Nat) : gcd a b ∣ a := by
  sorry  -- 证明较长

theorem gcd_dvd_right (a b : Nat) : gcd a b ∣ b := by
  sorry  -- 证明较长

theorem gcd_greatest (a b d : Nat) (h₁ : d ∣ a) (h₂ : d ∣ b) : 
    d ∣ gcd a b := by
  sorry  -- 证明较长

end NatArithmetic
