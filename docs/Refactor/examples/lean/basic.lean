/-
# 基础数学定义的 Lean 实现

本文件展示如何在 Lean 4 中形式化基础数学概念，包括：
- 自然数和整数的定义
- 代数结构（群、环、域）
- 序关系和完备性
- 基本数论定理

对应理论文档：数论基础、抽象代数
-/

import Mathlib

-- ============================================================
-- 第一部分：自然数和整数
-- ============================================================

namespace BasicMath

/-
## 1.1 自然数的基本性质

Lean 中的自然数 `ℕ` (Nat) 是基于皮亚诺公理定义的。
这里我们证明一些基本性质。
-/

-- 加法结合律（使用 Lean 内置引理）
example (a b c : ℕ) : (a + b) + c = a + (b + c) := by
  rw [Nat.add_assoc]

-- 乘法分配律
example (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  rw [Nat.mul_add]

-- 数学归纳法示例：证明前 n 个自然数的和公式
theorem sum_of_first_n (n : ℕ) : ∑ i in Finset.range n, (i + 1) = n * (n + 1) / 2 := by
  induction n with
  | zero =>
    -- 基本情况：n = 0，左边为空和等于 0，右边 = 0 * 1 / 2 = 0
    simp
  | succ n ih =>
    -- 归纳步骤：假设对 n 成立，证明对 n+1 成立
    rw [Finset.sum_range_succ, ih]
    -- 代数化简
    simp [Nat.mul_add, Nat.add_mul]
    ring_nf
    omega

/- 输出：
证明展示了数学归纳法的标准结构：
1. 基本情况（n = 0）：验证公式成立
2. 归纳步骤：假设对 n 成立，推导对 n+1 成立
-/

-- ============================================================
-- 1.2 整数和整除性
-- ============================================================

-- 整除关系的定义和基本性质
example (a b c : ℤ) (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
  -- 整除的传递性
  exact Int.dvd_trans h1 h2

-- 最大公约数的存在性（贝祖等式）
example (a b : ℤ) : ∃ x y : ℤ, a * x + b * y = Int.gcd a b := by
  exact Int.gcd_dvd a b

-- ============================================================
-- 第二部分：代数结构
-- ============================================================

/-
## 2.1 群的定义

群是一个集合 G 配备一个二元运算，满足：
- 封闭性
- 结合律
- 单位元存在
- 逆元存在
-/

-- 使用 Lean 的 Group 类型类
example (G : Type*) [Group G] (a b c : G) : 
  (a * b) * c = a * (b * c) := by
  -- 结合律由类型类自动提供
  rw [mul_assoc]

-- 单位元性质
example (G : Type*) [Group G] (a : G) : 
  1 * a = a ∧ a * 1 = a := by
  constructor
  · exact one_mul a
  · exact mul_one a

-- 逆元性质
example (G : Type*) [Group G] (a : G) : 
  a⁻¹ * a = 1 ∧ a * a⁻¹ = 1 := by
  constructor
  · exact inv_mul_cancel a
  · exact mul_inv_cancel a

/-
## 2.2 环和域

环是配备加法和乘法的代数结构。
-/

-- 环中的分配律
example (R : Type*) [Ring R] (a b c : R) : 
  a * (b + c) = a * b + a * c := by
  rw [mul_add]

-- 域中所有非零元都有乘法逆元
example (F : Type*) [Field F] (a : F) (ha : a ≠ 0) : 
  ∃ b : F, a * b = 1 := by
  use a⁻¹
  exact mul_inv_cancel ha

/-
## 2.3 有限域示例：ℤ/pℤ

当 p 是素数时，ℤ/pℤ 构成一个域。
-/

-- 证明 5 是素数
example : Nat.Prime 5 := by
  norm_num

-- 在 ZMod 5 中计算
example : (2 + 3 : ZMod 5) = 0 := by
  -- 2 + 3 = 5 ≡ 0 (mod 5)
  native_decide

example : (2 * 3 : ZMod 5) = 1 := by
  -- 2 * 3 = 6 ≡ 1 (mod 5)
  -- 所以 3 是 2 在 ZMod 5 中的乘法逆元
  native_decide

-- ============================================================
-- 第三部分：序和完备性
-- ============================================================

/-
## 3.1 实数的完备性

实数的一个重要性质是完备性（最小上界性质）。
-/

-- 实数集的非空有上界子集必有上确界
example (S : Set ℝ) (hne : S.Nonempty) (hbdd : BddAbove S) : 
  ∃ x : ℝ, IsLUB S x := by
  exact Real.exists_isLUB hne hbdd

/-
## 3.2 单调收敛定理

有界的单调序列必收敛。
-/

theorem monotone_convergence {f : ℕ → ℝ} 
  (hmono : Monotone f) (hbdd : BddAbove (Set.range f)) : 
  ∃ L : ℝ, Tendsto f atTop (𝓝 L) := by
  exact tendsto_atTop_ciSup hmono hbdd

-- ============================================================
-- 第四部分：数论应用
-- ============================================================

/-
## 4.1 费马小定理

若 p 是素数，a 不被 p 整除，则 a^(p-1) ≡ 1 (mod p)
-/

theorem fermat_little_theorem (p : ℕ) (hp : Nat.Prime p) (a : ℕ) 
  (hndvd : ¬p ∣ a) : 
  a ^ (p - 1) ≡ 1 [MOD p] := by
  have h := Nat.ModEq.pow_totient (show Nat.Coprime a p by 
    exact (Nat.coprime_iff_gcd_eq_one a p).mpr 
      (Nat.gcd_eq_one_of_not_dvd_prime hp hndvd))
  rw [Nat.totient_prime hp] at h
  exact h

/- 输出说明：
费马小定理是公钥密码学（如 RSA）的理论基础。
证明使用了欧拉定理和 φ(p) = p-1（当 p 为素数时）。
-/

/-
## 4.2 算术基本定理

每个大于 1 的自然数都可以唯一地分解为素数的乘积。
-/

-- 素因数分解的存在性和唯一性
example (n : ℕ) (hn : 1 < n) : 
  ∃ (f : ℕ →₀ ℕ), 
    (∀ p ∈ f.support, Nat.Prime p) ∧ 
    n = ∏ p in f.support, p ^ f p := by
  exact Nat.exists_prime_and_prod f n hn

-- ============================================================
-- 第五部分：代码运行示例
-- ============================================================

/-
## 5.1 计算示例

Lean 可以同时用于证明和计算。
-/

-- 计算阶乘
def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

-- 验证计算
example : factorial 5 = 120 := by rfl

-- 计算斐波那契数列
def fibonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fibonacci n + fibonacci (n + 1)

-- 验证斐波那契数
example : fibonacci 10 = 55 := by rfl

-- ============================================================
-- 总结
-- ============================================================

/-
本文件展示了 Lean 4 中形式化数学的基础：

1. **基本数论**：自然数、整数的性质，整除性，GCD
2. **代数结构**：群、环、域的定义和性质
3. **分析基础**：完备性，收敛性
4. **应用**：费马小定理，素因数分解

Lean 的强大之处在于：
- 严格的类型系统保证数学表达的正确性
- 自动化策略（如 `ring_nf`, `omega`, `norm_num`）简化证明
- 与数学库 Mathlib 集成，可直接使用已证明的定理

运行命令：
```bash
lean --run basic.lean
```

或使用 Lean 4 的 VS Code 插件进行交互式证明。
-/

end BasicMath
