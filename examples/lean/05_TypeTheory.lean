/-
# 类型论基础的形式化（Lean 4）

本文件包含类型论基本概念的形式化：
- 简单类型λ演算
- 依赖类型 (Π类型和Σ类型)
- Curry-Howard对应
- 归纳类型定义

对应文档: FormalRE/01_形式系统详解/01.7_类型论与依赖类型.md
-/

import Mathlib

namespace TypeTheory

-- ============================================================
-- 1. 简单类型系统
-- ============================================================

/-
## 1.1 基本类型

在Lean中，类型是内建的：
- Type : 普通类型 universe
- Prop : 命题类型 universe
- Sort u : 通用的类型宇宙
-/

-- 基本类型示例
#check Nat      -- 自然数类型
#check Bool     -- 布尔类型
#check String   -- 字符串类型

/-
## 1.2 函数类型

A → B : 从A到B的函数类型
-/

-- 恒等函数
def id' (A : Type*) : A → A :=
  fun x => x

-- 常值函数
def const' (A B : Type*) (a : A) : B → A :=
  fun _ => a

-- 函数复合
def compose' {A B C : Type*} (f : B → C) (g : A → B) : A → C :=
  fun x => f (g x)

-- 函数类型的基本定理
theorem funext {A B : Type*} {f g : A → B} (h : ∀ x, f x = g x) : f = g := by
  funext x
  exact h x

/-
## 1.3 积类型 (Product Type)

A × B : A和B的积类型（有序对）
-/

-- 投影函数
def fst' {A B : Type*} : A × B → A
  | (a, _) => a

def snd' {A B : Type*} : A × B → B
  | (_, b) => b

-- 配对函数
def pair' {A B : Type*} (a : A) (b : B) : A × B :=
  (a, b)

-- 积类型的通用性质 (投影)
theorem prod_eta {A B : Type*} (p : A × B) : (p.1, p.2) = p := by
  cases p
  rfl

/-
## 1.4 和类型 (Sum Type)

A ⊕ B : A和B的和类型（互斥并）
-/

-- 注入函数
def inl' {A B : Type*} : A → A ⊕ B :=
  Sum.inl

def inr' {A B : Type*} : B → A ⊕ B :=
  Sum.inr

-- 和类型的消去（case分析）
def sum_elim {A B C : Type*} (f : A → C) (g : B → C) : A ⊕ B → C
  | Sum.inl a => f a
  | Sum.inr b => g b

-- ============================================================
-- 2. 依赖类型 (Dependent Types)
-- ============================================================

/-
## 2.1 Π类型 (依赖函数类型)

Π(x : A), B x  或  (x : A) → B x

当B不依赖于x时，退化为普通函数类型 A → B
-/

-- 依赖函数示例：向量长度
def Vec (A : Type*) (n : Nat) : Type* :=
  { l : List A // l.length = n }

-- replicate函数的类型体现了依赖类型
def replicate {A : Type*} (n : Nat) (a : A) : Vec A n :=
  ⟨List.replicate n a, by simp⟩

-- 依赖函数：输入n，输出长度为n的向量
def makeVec (n : Nat) : Vec Nat n :=
  replicate n 0

/-
## 2.2 Σ类型 (依赖对类型)

Σ(x : A), B x  或  (x : A) × B x

当B不依赖于x时，退化为积类型 A × B
-/

-- 有长度的列表类型
def DList (A : Type*) : Type* :=
  Σ(n : Nat), Vec A n

-- 构造有长度的列表
def dlist_cons {A : Type*} (a : A) : DList A → DList A
  | ⟨n, ⟨l, h⟩⟩ => ⟨n + 1, ⟨a :: l, by simp [h]⟩⟩

-- ============================================================
-- 3. Curry-Howard 对应
-- ============================================================

/-
## 3.1 命题作为类型

逻辑            | 类型论
----------------|------------------
命题 P          | 类型 P : Prop
证明 p : P      | 项   p : P
真              | True
假              | False
P ∧ Q           | P × Q
P ∨ Q           | P ⊕ Q
P → Q           | P → Q
¬P              | P → False
∀x:A, P(x)      | (x : A) → P x
∃x:A, P(x)      | Σ(x : A), P x
-/

/-
## 3.2 真和假的证明构造
-/

-- True 只有一个证明（构造子 trivial）
theorem true_is_provable : True := by
  trivial

-- False 没有证明（爆炸原理）
theorem false_implies_anything (P : Prop) : False → P := by
  intro h
  cases h

/-
## 3.3 合取和析取的证明构造
-/

-- 合取引入：从P和Q得到P ∧ Q
theorem and_intro {P Q : Prop} (hp : P) (hq : Q) : P ∧ Q := by
  exact ⟨hp, hq⟩

-- 合取消去：从P ∧ Q得到P
theorem and_elim_left {P Q : Prop} (h : P ∧ Q) : P := by
  exact h.1

-- 析取引入1：从P得到P ∨ Q
theorem or_intro_left {P Q : Prop} (hp : P) : P ∨ Q := by
  left
  exact hp

-- 析取引入2：从Q得到P ∨ Q
theorem or_intro_right {P Q : Prop} (hq : Q) : P ∨ Q := by
  right
  exact hq

/-
## 3.4 蕴含和全称量词的证明构造
-/

-- 蕴含消去（肯定前件式）
theorem modus_ponens {P Q : Prop} (hpq : P → Q) (hp : P) : Q := by
  exact hpq hp

-- 全称量词引入
theorem forall_intro {A : Type*} {P : A → Prop} 
    (h : ∀ a, P a) : ∀ x, P x := by
  intro x
  exact h x

-- 全称量词消去
theorem forall_elim {A : Type*} {P : A → Prop} 
    (h : ∀ x, P x) (a : A) : P a := by
  exact h a

/-
## 3.5 存在量词的证明构造
-/

-- 存在引入
theorem exists_intro {A : Type*} {P : A → Prop} {a : A} 
    (ha : P a) : ∃ x, P x := by
  exact ⟨a, ha⟩

-- 存在消去
theorem exists_elim {A : Type*} {P : A → Prop} {Q : Prop}
    (hex : ∃ x, P x) (h : ∀ a, P a → Q) : Q := by
  cases hex with
  | intro a ha => exact h a ha

-- ============================================================
-- 4. 归纳类型 (Inductive Types)
-- ============================================================

/-
## 4.1 自然数的定义

inductive Nat
  | zero : Nat
  | succ : Nat → Nat
-/

-- 自然数归纳原理
theorem nat_induction {P : Nat → Prop} 
    (h0 : P 0) (hstep : ∀ n, P n → P (n + 1)) : ∀ n, P n := by
  intro n
  induction n with
  | zero => exact h0
  | succ n ih => exact hstep n ih

/-
## 4.2 列表类型

inductive List (A : Type*)
  | nil : List A
  | cons : A → List A → List A
-/

-- 列表的长度
def length' {A : Type*} : List A → Nat
  | [] => 0
  | _ :: l => 1 + length' l

-- 列表连接
def append' {A : Type*} : List A → List A → List A
  | [], l => l
  | a :: l₁, l₂ => a :: append' l₁ l₂

-- 列表连接的结合律
theorem append_assoc {A : Type*} (l₁ l₂ l₃ : List A) :
    append' (append' l₁ l₂) l₃ = append' l₁ (append' l₂ l₃) := by
  induction l₁ with
  | nil => simp [append']
  | cons a l₁ ih => simp [append', ih]

-- 列表长度与连接的关系
theorem length_append {A : Type*} (l₁ l₂ : List A) :
    length' (append' l₁ l₂) = length' l₁ + length' l₂ := by
  induction l₁ with
  | nil => simp [append', length']
  | cons a l₁ ih => simp [append', length', ih]

/-
## 4.3 选项类型

inductive Option (A : Type*)
  | none : Option A
  | some : A → Option A
-/

-- 选项类型的应用：偏函数
def safeDiv (n m : Nat) : Option Nat :=
  if m = 0 then none else some (n / m)

/-
## 4.4 等式类型 (Equality Type)

inductive Eq {A : Type*} : A → A → Prop
  | refl : ∀ a, Eq a a
-/

-- 等式的对称性
theorem eq_symm {A : Type*} {a b : A} (h : a = b) : b = a := by
  rw [h]

-- 等式的传递性
theorem eq_trans {A : Type*} {a b c : A} 
    (hab : a = b) (hbc : b = c) : a = c := by
  rw [hab, hbc]

-- 等式替换原理（Leibniz原理）
theorem eq_subst {A : Type*} {P : A → Prop} {a b : A} 
    (h1 : a = b) (h2 : P a) : P b := by
  rw [←h1]
  exact h2

-- ============================================================
-- 5. 递归和高阶函数
-- ============================================================

/-
## 5.1 原始递归

在Lean中，递归函数需要证明终止性
-/

-- 阶乘函数
def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

-- 阶乘性质：factorial n > 0
theorem factorial_pos (n : Nat) : factorial n > 0 := by
  induction n with
  | zero => simp [factorial]
  | succ n ih => simp [factorial, Nat.mul_pos, ih]

/-
## 5.2 高阶函数
-/

-- 映射函数
def map' {A B : Type*} (f : A → B) : List A → List B
  | [] => []
  | a :: l => f a :: map' f l

-- map保持长度
theorem map_preserves_length {A B : Type*} (f : A → B) (l : List A) :
    length' (map' f l) = length' l := by
  induction l with
  | nil => simp [map', length']
  | cons a l ih => simp [map', length', ih]

-- 折叠函数
def foldr' {A B : Type*} (f : A → B → B) (init : B) : List A → B
  | [] => init
  | a :: l => f a (foldr' f init l)

-- 列表求和
def sum' (l : List Nat) : Nat :=
  foldr' (· + ·) 0 l

-- 求和与append的关系
theorem sum_append (l₁ l₂ : List Nat) :
    sum' (append' l₁ l₂) = sum' l₁ + sum' l₂ := by
  induction l₁ with
  | nil => simp [append', sum', foldr']
  | cons a l₁ ih => 
    simp [append', sum', foldr', ih]
    rw [Nat.add_assoc]

end TypeTheory
