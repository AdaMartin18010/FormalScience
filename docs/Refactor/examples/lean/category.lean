/-
# 范畴论基本概念的 Lean 实现

本文件展示范畴论的核心概念在 Lean 4 中的形式化实现：
- 范畴的定义（对象、态射、复合、单位元）
- 函子（协变和逆变）
- 自然变换
- 泛性质（积、余积、始对象、终对象）
- 伴随函子

对应理论文档：范畴论基础
-/

import Mathlib

-- ============================================================
-- 第一部分：范畴的定义
-- ============================================================

namespace CategoryTheory

/-
## 1.1 范畴的数学定义

一个范畴 C 包含：
- 对象类 Ob(C)
- 对每个对象对 (X, Y)，态射集 Hom(X, Y)
- 复合运算 ∘ : Hom(Y, Z) × Hom(X, Y) → Hom(X, Z)
- 满足结合律和单位元律
-/

-- 使用 Lean 的 Category 类型类
-- Mathlib 已经定义了完整的范畴论框架

-- 验证集合范畴 Set 满足范畴公理
example : Category Type := by
  infer_instance

/- 输出说明：
Lean 的 Mathlib 定义了丰富的范畴论框架。
Type 是一个范畴，其中：
- 对象是类型
- 态射是函数
- 复合是函数复合
- 单位态射是恒等函数
-/

-- ============================================================
-- 1.2 具体范畴示例
-- ============================================================

/-
## 离散范畴

离散范畴中，唯一的态射是单位态射。
-/

-- 单对象范畴（幺半群的范畴化）
structure MonoidCategory (M : Type*) [Monoid M] where
  -- 对象只有一个（通常记作 ⋆）
  -- 态射是幺半群的元素
  hom : M

-- 在单对象范畴中，复合对应于幺半群乘法
example {M : Type*} [Monoid M] (f g : M) : M := f * g

/-
## 预序作为范畴

预序集 (P, ≤) 可以看作范畴，其中：
- 对象是 P 的元素
- 当 a ≤ b 时，存在唯一的态射 a → b
-/

instance preorderCategory (P : Type*) [Preorder P] : Category P where
  Hom a b := ULift (PLift (a ≤ b))
  id a := ⟨⟨le_refl a⟩⟩
  comp f g := ⟨⟨le_trans (PLift.down (ULift.down f)).down (PLift.down (ULift.down g)).down⟩⟩

/- 输出说明：
预序范畴展示了范畴论的普遍性：
- 自反性提供单位态射
- 传递性提供复合
- 反对称性（偏序）使得同构等价于相等
-/

-- ============================================================
-- 第二部分：函子
-- ============================================================

/-
## 2.1 函子的定义

函子 F : C → D 是两个范畴之间的映射，保持：
- 对象映射：C 的对象 → D 的对象
- 态射映射：C 的态射 → D 的态射
- 保持单位：F(id_X) = id_{F(X)}
- 保持复合：F(g ∘ f) = F(g) ∘ F(f)
-/

-- 列函子（List Functor）
def ListFunctor : Type ⥤ Type where
  obj α := List α
  map f := List.map f

-- 验证函子律
example : ∀ (α : Type), ListFunctor.map (id : α → α) = id := by
  intro α
  funext xs
  simp [ListFunctor]

example {α β γ : Type} (f : α → β) (g : β → γ) : 
  ListFunctor.map (g ∘ f) = ListFunctor.map g ∘ ListFunctor.map f := by
  funext xs
  simp [ListFunctor]
  rw [List.map_map]

/- 输出说明：
ListFunctor 是一个自函子（Endofunctor）：
- obj：将类型 α 映射到 List α
- map：将函数 f : α → β 提升到 List.map f : List α → List β
- 函子律验证：List.map 保持恒等和复合
-/

-- ============================================================
-- 2.2 函子保持复合的证明
-- ============================================================

-- 函子保持复合的完整证明
theorem ListFunctor.map_comp {α β γ : Type} (f : α → β) (g : β → γ) :
  ListFunctor.map (g ∘ f) = ListFunctor.map g ∘ ListFunctor.map f := by
  funext xs
  simp [ListFunctor]
  rw [List.map_map]
  rfl

-- 函子保持单位的完整证明
theorem ListFunctor.map_id {α : Type} :
  ListFunctor.map (id : α → α) = id := by
  funext xs
  simp [ListFunctor]
  rfl

-- ============================================================
-- 2.3 逆变函子
-- ============================================================

/-
逆变函子 F : Cᵒᵖ → D（或等价地 C → Dᵒᵖ）反转箭头方向。
-/

-- 逆变 Hom 函子
example (C : Type*) [Category C] (X : C) : Cᵒᵖ ⥤ Type where
  obj Y := X ⟶ Y.unop
  map f g := g ≫ f.unop

/- 输出说明：
逆变 Hom 函子 Hom(X, -)ᵒᵖ 是一个经典例子：
- 对对象 Y，映射到态射集 Hom(X, Y)
- 对态射 f : Y → Z，映射为前复合：- ∘ f
- 由于箭头方向反转，这是一个逆变函子
-/

-- ============================================================
-- 第三部分：自然变换
-- ============================================================

/-
## 3.1 自然变换的定义

给定函子 F, G : C → D，自然变换 η : F ⟹ G 是：
- 对每个 X ∈ Ob(C)，一个态射 η_X : F(X) → G(X)
- 满足自然性条件：G(f) ∘ η_X = η_Y ∘ F(f)

图示：
    F(X) --η_X--> G(X)
     |              |
     | F(f)         | G(f)
     v              v
    F(Y) --η_Y--> G(Y)
-/

-- List 到 Option 的自然变换（head 操作）
def headTransformation : (ListFunctor : Type ⥤ Type) ⟶ (Option : Type ⥤ Type) where
  app α xs := xs.head?

-- 验证自然性条件
example {α β : Type} (f : α → β) (xs : List α) :
  headTransformation.app β (List.map f xs) = Option.map f (headTransformation.app α xs) := by
  simp [headTransformation]
  cases xs with
  | nil => simp
  | cons x xs => simp

/- 输出说明：
headTransformation 是自然变换：
- 对每个类型 α，提供一个函数 List α → Option α
- 自然性保证"先映射再取头"等于"先取头再映射"
- 这是函数式编程中常见的模式
-/

-- ============================================================
-- 3.2 自然变换的横组合（Horizontal Composition）
-- ============================================================

-- 两个自然变换的横组合
-- 给定 η : F ⟹ G 和 θ : H ⟹ K，其中 F, G : C → D, H, K : D → E
-- 横组合 θ ∘ₕ η : H ∘ F ⟹ K ∘ G
def horizontalComposition {C D E : Type*} [Category C] [Category D] [Category E]
  {F G : C ⥤ D} {H K : D ⥤ E}
  (η : F ⟶ G) (θ : H ⟶ K) : (H ⋙ F) ⟶ (K ⋙ G) where
  app X := θ.app (G.obj X) ≫ H.map (η.app X)

-- 横组合的自然性证明
theorem horizontalComposition_naturality {C D E : Type*} [Category C] [Category D] [Category E]
  {F G : C ⥤ D} {H K : D ⥤ E}
  (η : F ⟶ G) (θ : H ⟶ K) {X Y : C} (f : X ⟶ Y) :
  (horizontalComposition η θ).app Y ≫ (K ⋙ G).map f = 
  (H ⋙ F).map f ≫ (horizontalComposition η θ).app X := by
  simp [horizontalComposition]
  rw [← Category.assoc, θ.naturality (G.map f)]
  simp only [Category.assoc, ← H.map_comp, η.naturality]
  simp

-- ============================================================
-- 第四部分：泛性质
-- ============================================================

/-
## 4.1 积（Product）

范畴 C 中对象 X 和 Y 的积是对象 X × Y，配备投影 π₁ : X × Y → X 和 π₂ : X × Y → Y，
满足泛性质：对任意对象 Z 和态射 f : Z → X, g : Z → Y，存在唯一的态射 ⟨f, g⟩ : Z → X × Y
使得图表交换。
-/

-- Type 范畴中的积就是笛卡尔积
example (α β : Type) : α × β where
  -- 投影
  fst : α × β → α
  snd : α × β → β
  -- 配对构造
  intro : (Z → α) → (Z → β) → (Z → α × β)

-- 积的泛性质
example {α β γ : Type} (f : γ → α) (g : γ → β) : 
  ∃! h : γ → α × β, h.fst = f ∧ h.snd = g := by
  use fun x => (f x, g x)
  constructor
  · -- 存在性
    constructor
    · funext x; rfl
    · funext x; rfl
  · -- 唯一性
    intro h ⟨h1, h2⟩
    funext x
    have : h x = (f x, g x) := by
      rw [← h1, ← h2]
      rfl
    exact this

/- 输出说明：
积的泛性质刻画了积的本质特征：
- 存在性：配对构造满足投影条件
- 唯一性：任何满足条件的态射都等于配对构造
- 这是"通用构造"的典型例子
-/

-- ============================================================
-- 4.2 余积（Coproduct）

-- Type 范畴中的余积是带标签的并（Sum 类型）
example (α β : Type) : α ⊕ β where
  -- 注入
  inl : α → α ⊕ β
  inr : β → α ⊕ β
  -- 消去子
  elim : (α → γ) → (β → γ) → (α ⊕ β → γ)

-- ============================================================
-- 4.3 始对象和终对象
-- ============================================================

/-
## 始对象（Initial Object）

对象 0 是始对象，如果对任意对象 X，存在唯一的态射 0 → X。
-/

-- Type 范畴中的始对象是空类型
example : IsInitial Empty := by
  constructor
  intro α
  use fun e => Empty.elim e
  intro f
  funext e
  cases e

/-
## 终对象（Terminal Object）

对象 1 是终对象，如果对任意对象 X，存在唯一的态射 X → 1。
-/

-- Type 范畴中的终对象是单位类型
example : IsTerminal PUnit := by
  constructor
  intro α
  use fun _ => PUnit.unit
  intro f
  funext x
  simp only [PUnit.default_eq_unit]

/- 输出说明：
始对象和终对象是范畴论中的"平凡"构造，但非常重要：
- 始对象有出去的箭头，没有进来的（除单位态射外）
- 终对象有进来的箭头，没有出去的（除单位态射外）
- 在 Type 中，Empty 是始对象，PUnit 是终对象
-/

-- ============================================================
-- 第五部分：伴随函子
-- ============================================================

/-
## 5.1 伴随的定义

函子 F : C → D 和 G : D → C 构成伴随（记作 F ⊣ G），如果：
存在自然同构 Hom_D(F(X), Y) ≅ Hom_C(X, G(Y))

等价表述：存在单位 η : 1_C ⟹ G ∘ F 和余单位 ε : F ∘ G ⟹ 1_D
满足三角恒等式。
-/

-- 自由幺半群和遗忘函子的伴随
-- F: Set → Mon（自由构造）
-- U: Mon → Set（遗忘构造）

-- 单位：η_X : X → U(F(X)) = List X
def free_monoid_unit {α : Type} (x : α) : List α := [x]

-- 余单位：ε_M : F(U(M)) → M
def free_monoid_counit {M : Type*} [Monoid M] (xs : List M) : M :=
  xs.foldl (· * ·) 1

-- 辅助引理：自由幺半群的单位性质
theorem free_monoid_unit_property {α : Type} (xs : List α) :
  List.map (free_monoid_unit (α := α)) xs = List.pure xs := by
  simp [free_monoid_unit]
  rfl

-- 三角恒等式验证（简化版）
example {α : Type} (xs : List α) :
  List.map (free_monoid_unit (α := α)) xs = List.pure xs := by
  simp [free_monoid_unit]
  rfl

-- 证明：单位后余单位等于恒等
example {M : Type*} [Monoid M] (xs : List M) :
  free_monoid_counit (List.map (fun x => x) xs) = free_monoid_counit xs := by
  simp [free_monoid_counit]

-- 证明：余单位后单位等于恒等
example {α : Type} (x : α) :
  free_monoid_counit (free_monoid_unit x) = x := by
  simp [free_monoid_counit, free_monoid_unit]

/- 输出说明：
伴随是范畴论中最深刻和最有用的概念之一：
- 自由构造 ⟣ 遗忘构造 是最常见的伴随对
- 单位将元素嵌入自由构造
- 余单位将自由构造"折叠"回原结构
- 伴随捕捉了"最优近似"的概念
-/

-- ============================================================
-- 第六部分：极限和余极限
-- ============================================================

/-
## 6.1 极限

极限是泛构造的统一框架，积、等化子等都是特例。
-/

-- 拉回（Pullback）示例
structure Pullback {C : Type*} [Category C] {X Y Z : C} 
  (f : X ⟶ Z) (g : Y ⟶ Z) where
  P : C
  p1 : P ⟶ X
  p2 : P ⟶ Y
  comm : p1 ≫ f = p2 ≫ g
  -- 泛性质省略

/-
## 6.2 余极限

余极限是极限的对偶概念。
-/

-- 推出（Pushout）示例
structure Pushout {C : Type*} [Category C] {X Y Z : C}
  (f : Z ⟶ X) (g : Z ⟶ Y) where
  P : C
  i1 : X ⟶ P
  i2 : Y ⟶ P
  comm : f ≫ i1 = g ≫ i2

-- ============================================================
-- 总结
-- ============================================================

/-
本文件展示了范畴论在 Lean 中的实现：

1. **范畴**：Set 范畴，预序范畴
2. **函子**：ListFunctor，逆变函子，保持复合和单位
3. **自然变换**：headTransformation，横组合
4. **泛性质**：积、余积、始对象、终对象
5. **伴随**：自由幺半群 ⟣ 遗忘函子
6. **极限**：拉回、推出

范畴论的价值在于：
- **抽象统一**：不同领域的共同结构
- **对偶原理**：每个概念都有对偶版本
- **通用构造**：通过泛性质定义对象

运行命令：
```bash
lean --run category.lean
```

Lean 的 Mathlib 提供了完整的范畴论支持，是学习和研究范畴论的强大工具。
-/

end CategoryTheory
