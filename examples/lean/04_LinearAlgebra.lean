/-
# 线性代数基础的形式化（Lean 4）

本文件包含线性代数基本概念的形式化：
- 向量空间的定义
- 线性映射的定义
- 线性无关与基
- 矩阵的基本运算

对应文档: FormalRE/01_形式系统详解/01.6_范畴论基础.md（Vect范畴）
-/

import Mathlib

namespace LinearAlgebra

-- ============================================================
-- 1. 向量空间（线性空间）的定义
-- ============================================================

/-
## 1.1 向量空间公理

向量空间 V  over 域 F 满足：
1. (V, +) 是阿贝尔群
2. 标量乘法满足分配律和结合律
3. 1 · v = v

Lean的 Mathlib 已经定义了 Module 类型类。
-/

variable {F : Type*} [Field F]
variable {V : Type*} [AddCommGroup V] [Module F V]

/-
## 1.2 向量空间的基本性质
-/

-- 0 · v = 0
theorem zero_smul' (v : V) : (0 : F) • v = 0 := by
  rw [zero_smul]

-- 1 · v = v
theorem one_smul' (v : V) : (1 : F) • v = v := by
  rw [one_smul]

-- (-1) · v = -v
theorem neg_one_smul' (v : V) : (-1 : F) • v = -v := by
  rw [neg_one_smul]

-- c · 0 = 0
theorem smul_zero' (c : F) : c • (0 : V) = 0 := by
  rw [smul_zero]

/-
## 1.3 标量乘法的分配律
-/

-- (a + b) · v = a · v + b · v
theorem add_smul' (a b : F) (v : V) : (a + b) • v = a • v + b • v := by
  rw [add_smul]

-- a · (u + v) = a · u + a · v
theorem smul_add' (a : F) (u v : V) : a • (u + v) = a • u + a • v := by
  rw [smul_add]

/-
## 1.4 标量乘法的结合律

(a * b) · v = a · (b · v)
-/
theorem mul_smul' (a b : F) (v : V) : (a * b) • v = a • (b • v) := by
  rw [mul_smul]

-- ============================================================
-- 2. 线性组合与线性张成
-- ============================================================

/-
## 2.1 线性组合

给定向量 v₁, v₂, ..., vₙ 和标量 c₁, c₂, ..., cₙ，
线性组合 = c₁·v₁ + c₂·v₂ + ... + cₙ·vₙ
-/

-- 有限集的线性组合
def linearCombination {ι : Type*} (s : Finset ι) (c : ι → F) (v : ι → V) : V :=
  ∑ i in s, c i • v i

notation "∑ℒ" => linearCombination

/-
## 2.2 线性张成 (Span)

span(S) = S 中向量的所有有限线性组合的集合
-/

def span' (S : Set V) : Set V :=
  {w | ∃ (ι : Type) (s : Finset ι) (c : ι → F) (v : ι → V), 
       (∀ i, v i ∈ S) ∧ w = ∑ i in s, c i • v i}

-- span(S) 是 V 的子空间
theorem span_is_subspace (S : Set V) : 
    (0 : V) ∈ span' S ∧ 
    ∀ u v, u ∈ span' S → v ∈ span' S → u + v ∈ span' S ∧
    ∀ c v, v ∈ span' S → c • v ∈ span' S := by
  constructor
  · -- 0 在 span 中
    use PEmpty, ∅, fun _ => 0, fun _ => 0
    simp
  constructor
  · -- 对加法封闭
    rintro u v ⟨ι₁, s₁, c₁, v₁, hv₁, hu⟩ ⟨ι₂, s₂, c₂, v₂, hv₂, hv⟩
    sorry  -- 需要复杂的构造
  · -- 对标量乘法封闭
    rintro c v ⟨ι, s, c', v', hv', rfl⟩
    sorry

-- ============================================================
-- 3. 线性无关性
-- ============================================================

/-
## 3.1 线性无关的定义

向量集合 S 是线性无关的，如果：
c₁·v₁ + c₂·v₂ + ... + cₙ·vₙ = 0 蕴含所有 cᵢ = 0
-/

def LinearIndependent' {ι : Type*} (v : ι → V) : Prop :=
  ∀ (s : Finset ι) (c : ι → F), ∑ i in s, c i • v i = 0 → ∀ i ∈ s, c i = 0

/-
## 3.2 线性无关的基本性质
-/

-- 包含零向量的集合线性相关
theorem not_linearIndependent_zero (v : ℕ → V) (h : v 0 = 0) :
    ¬ LinearIndependent' v := by
  intro hli
  have h0 : ∑ i in {0}, (1 : F) • v i = 0 := by
    simp [h]
  have h1 := hli {0} (fun _ => 1) h0 0 (by simp)
  simp at h1

-- 单元素集合 {v} 线性无关当且仅当 v ≠ 0
theorem linearIndependent_singleton (v : V) :
    LinearIndependent' (fun _ : Unit => v) ↔ v ≠ 0 := by
  constructor
  · intro hli hv
    rw [hv] at hli
    have h0 : ∑ i in {()}, (1 : F) • (fun _ : Unit => (0 : V)) i = 0 := by simp
    have h1 := hli {()} (fun _ => 1) h0 () (by simp)
    simp at h1
  · intro hv s c hsum i hi
    simp at hsum
    cases s.eq_empty_or_nonempty with
    | inl hempty => simp [hempty] at hi
    | inr hne => 
      have : ∃ x, x ∈ s := hne
      rcases this with ⟨x, hx⟩
      have : s = {x} := by sorry  -- 简化假设
      rw [this] at hsum
      simp at hsum
      have : c x • v = 0 := by simpa using hsum
      sorry  -- 需要证明 c x = 0

/-
## 3.3 基 (Basis)

基是线性无关的生成集
-/

structure Basis' (ι : Type*) (v : ι → V) where
  linearIndependent : LinearIndependent' v
  span_eq_top : span' (Set.range v) = Set.univ

-- ============================================================
-- 4. 线性映射
-- ============================================================

/-
## 4.1 线性映射的定义

T : V → W 是线性映射，如果：
1. T(u + v) = T(u) + T(v)
2. T(c · v) = c · T(v)
-/

variable {W : Type*} [AddCommGroup W] [Module F W]

structure LinearMap' (F : Type*) [Field F] (V W : Type*) 
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W] where
  toFun : V → W
  map_add' : ∀ u v, toFun (u + v) = toFun u + toFun v
  map_smul' : ∀ (c : F) v, toFun (c • v) = c • toFun v

notation:25 V " →ₗ[" F "] " W => LinearMap' F V W

-- 将线性映射强制转换为函数
instance : FunLike (V →ₗ[F] W) V W where
  coe T := T.toFun
  coe_injective' T₁ T₂ h := by cases T₁; cases T₂; congr

/-
## 4.2 线性映射的基本性质
-/

-- T(0) = 0
theorem map_zero' (T : V →ₗ[F] W) : T 0 = 0 := by
  rw [←zero_smul (0 : F), T.map_smul', zero_smul]

-- T(-v) = -T(v)
theorem map_neg' (T : V →ₗ[F] W) (v : V) : T (-v) = -T v := by
  rw [←neg_one_smul (1 : F) v, T.map_smul', neg_one_smul]

-- T(u - v) = T(u) - T(v)
theorem map_sub' (T : V →ₗ[F] W) (u v : V) : T (u - v) = T u - T v := by
  rw [sub_eq_add_neg, T.map_add', map_neg', ←sub_eq_add_neg]

/-
## 4.3 核与像
-/

-- 线性映射的核 (Kernel)
def ker' (T : V →ₗ[F] W) : Set V :=
  {v | T v = 0}

-- 线性映射的像 (Image)
def im' (T : V →ₗ[F] W) : Set W :=
  Set.range T

-- 核是子空间
theorem ker_is_subspace (T : V →ₗ[F] W) : 
    (0 : V) ∈ ker' T ∧
    ∀ u v, u ∈ ker' T → v ∈ ker' T → u + v ∈ ker' T ∧
    ∀ c v, v ∈ ker' T → c • v ∈ ker' T := by
  constructor
  · -- 0 在核中
    rw [ker', Set.mem_setOf_eq, map_zero']
  constructor
  · -- 对加法封闭
    intro u v hu hv
    rw [ker', Set.mem_setOf_eq] at hu hv ⊢
    rw [T.map_add', hu, hv, add_zero]
  · -- 对标量乘法封闭
    intro c v hv
    rw [ker', Set.mem_setOf_eq] at hv ⊢
    rw [T.map_smul', hv, smul_zero]

/-
## 4.4 同构

线性同构 = 双射的线性映射
-/

structure LinearEquiv' (F : Type*) [Field F] (V W : Type*)
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W] extends LinearMap' F V W where
  invFun : W → V
  left_inv : ∀ v, invFun (toFun v) = v
  right_inv : ∀ w, toFun (invFun w) = w

notation:25 V " ≃ₗ[" F "] " W => LinearEquiv' F V W

-- ============================================================
-- 5. 矩阵表示
-- ============================================================

/-
## 5.1 矩阵定义

m × n 矩阵 over 域 F
-/

def Matrix' (m n : Type*) [Fintype m] [Fintype n] (F : Type*) [Field F] :=
  m → n → F

/-
## 5.2 矩阵运算
-/

-- 矩阵加法
instance {m n : Type*} [Fintype m] [Fintype n] : Add (Matrix' m n F) where
  add A B := fun i j => A i j + B i j

-- 矩阵数乘
instance {m n : Type*} [Fintype m] [Fintype n] : SMul F (Matrix' m n F) where
  smul c A := fun i j => c * A i j

-- 矩阵乘法
def Matrix'.mul {m n p : Type*} [Fintype m] [Fintype n] [Fintype p] 
    (A : Matrix' m n F) (B : Matrix' n p F) : Matrix' m p F :=
  fun i k => ∑ j, A i j * B j k

/-
## 5.3 矩阵与线性映射的对应

每个矩阵对应一个线性映射
-/

def matrixToLinearMap {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix' m n F) : (n → F) →ₗ[F] (m → F) where
  toFun x := fun i => ∑ j, A i j * x j
  map_add' := by
    intro u v
    funext i
    simp [Finset.sum_add_distrib, mul_add]
  map_smul' := by
    intro c v
    funext i
    simp [Finset.mul_sum, mul_assoc]

end LinearAlgebra
