/-
# 范畴论基础的形式化（Lean 4）

本文件包含范畴论基本概念的形式化：
- 范畴的定义（对象、态射、复合）
- 函子的定义
- 自然变换的定义
- 极限与余极限

对应文档: FormalRE/01_形式系统详解/01.6_范畴论基础.md
-/

import Mathlib

namespace CategoryTheory

-- ============================================================
-- 1. 范畴的定义
-- ============================================================

/-
## 1.1 范畴的公理

一个范畴 C 包含：
1. 对象类 Ob(C)
2. 对任意对象A,B，态射集 Hom(A,B)
3. 复合运算：∘ : Hom(B,C) × Hom(A,B) → Hom(A,C)
4. 恒等态射：id_A ∈ Hom(A,A)

满足：
- 结合律：h ∘ (g ∘ f) = (h ∘ g) ∘ f
- 单位律：f ∘ id_A = f = id_B ∘ f

Lean的 Mathlib 已经定义了 Category 类型类。
-/

-- 使用 Mathlib 的 Category 定义
variable {C : Type*} [Category C]

/-
## 1.2 范畴的基本性质
-/

-- 恒等态射的左单位律
theorem id_comp' {X Y : C} (f : X ⟶ Y) : 𝟙 X ≫ f = f := by
  rw [Category.id_comp]

-- 恒等态射的右单位律
theorem comp_id' {X Y : C} (f : X ⟶ Y) : f ≫ 𝟙 Y = f := by
  rw [Category.comp_id]

-- 复合的结合律
theorem assoc' {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (f ≫ g) ≫ h = f ≫ (g ≫ h) := by
  rw [Category.assoc]

-- ============================================================
-- 2. 具体范畴的例子
-- ============================================================

/-
## 2.1 Set范畴（集合与函数）

对象：集合（在Lean中是Type）
态射：函数
-/

-- Set范畴就是 Type 范畴
example : Category Type := by infer_instance

/-
## 2.2 离散范畴

每个集合可以看作离散范畴（只有恒等态射）
-/

def DiscreteCategory (S : Type*) : Category S where
  Hom := fun _ _ => Unit
  id := fun _ => ()
  comp := fun _ _ => ()
  id_comp := by simp
  comp_id := by simp
  assoc := by simp

/-
## 2.3 偏序范畴 (Poset)

偏序集可以看作范畴：
- 对象：偏序集的元素
- 态射：a ⟶ b 当且仅当 a ≤ b
-/

instance PosetCategory {P : Type*} [PartialOrder P] : Category P where
  Hom := fun a b => PLift (a ≤ b)
  id := fun a => PLift.up (le_refl a)
  comp := fun ⟨h₁⟩ ⟨h₂⟩ => PLift.up (le_trans h₁ h₂)
  id_comp := by simp
  comp_id := by simp
  assoc := by simp

-- ============================================================
-- 3. 同构 (Isomorphism)
-- ============================================================

/-
## 3.1 同构的定义

f : A → B 是同构，如果存在 g : B → A 使得：
g ∘ f = id_A 且 f ∘ g = id_B
-/

structure Iso' {C : Type*} [Category C] (X Y : C) where
  hom : X ⟶ Y
  inv : Y ⟶ X
  hom_inv_id : hom ≫ inv = 𝟙 X
  inv_hom_id : inv ≫ hom = 𝟙 Y

notation:20 X " ≅' " Y => Iso' X Y

/-
## 3.2 同构的性质
-/

-- 同构是自反的
theorem iso_refl {C : Type*} [Category C] (X : C) : X ≅' X where
  hom := 𝟙 X
  inv := 𝟙 X
  hom_inv_id := by simp
  inv_hom_id := by simp

-- 同构是对称的
theorem iso_symm {C : Type*} [Category C] {X Y : C} (h : X ≅' Y) : Y ≅' X where
  hom := h.inv
  inv := h.hom
  hom_inv_id := h.inv_hom_id
  inv_hom_id := h.hom_inv_id

-- 同构是传递的
theorem iso_trans {C : Type*} [Category C] {X Y Z : C} 
    (h₁ : X ≅' Y) (h₂ : Y ≅' Z) : X ≅' Z where
  hom := h₁.hom ≫ h₂.hom
  inv := h₂.inv ≫ h₁.inv
  hom_inv_id := by
    rw [Category.assoc, ←Category.assoc h₂.hom, h₂.hom_inv_id, Category.id_comp, h₁.hom_inv_id]
  inv_hom_id := by
    rw [Category.assoc, ←Category.assoc h₁.inv, h₁.inv_hom_id, Category.id_comp, h₂.inv_hom_id]

-- ============================================================
-- 4. 函子 (Functor)
-- ============================================================

/-
## 4.1 函子的定义

函子 F : C → D 包含：
1. 对象映射：F.ob : Ob(C) → Ob(D)
2. 态射映射：F.map : Hom_C(X,Y) → Hom_D(F.ob X, F.ob Y)

满足：
- F.map(id_X) = id_{F.ob X}
- F.map(f ≫ g) = F.map(f) ≫ F.map(g)
-/

-- 使用 Mathlib 的 Functor
def Functor' (C D : Type*) [Category C] [Category D] :=
  C ⥤ D

notation C " ⥤' " D => Functor' C D

/-
## 4.2 恒等函子
-/

def IdFunctor (C : Type*) [Category C] : C ⥤ C where
  obj := id
  map := id
  map_id := by simp
  map_comp := by simp

/-
## 4.3 函子的复合
-/

def FunctorComp {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) : C ⥤ E where
  obj := fun X => G.obj (F.obj X)
  map := fun f => G.map (F.map f)
  map_id := by simp
  map_comp := by simp

-- 函子复合的结合律
theorem functor_comp_assoc {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (F₁ : C ⥤ D) (F₂ : D ⥤ E) (F₃ : E ⥤ F) :
    FunctorComp (FunctorComp F₁ F₂) F₃ = FunctorComp F₁ (FunctorComp F₂ F₃) := by
  rfl

/-
## 4.4 具体函子的例子

### 列表函子 (List Functor)
List : Type → Type
-/

def ListFunctor : Type ⥤ Type where
  obj := List
  map := fun f => List.map f
  map_id := by
    intro X
    funext l
    induction l with
    | nil => rfl
    | cons a l ih => simp [ih]
  map_comp := by
    intro X Y Z f g
    funext l
    induction l with
    | nil => rfl
    | cons a l ih => simp [ih]

/-
## 4.5 遗忘函子

从有结构的对象到其底层集合的函子
-/

-- 从带结构类型到Type的遗忘函子
def ForgetFunctor (C : Type*) [Category C] (U : C → Type*) : C ⥤ Type where
  obj := U
  map := sorry  -- 需要知道C的具体结构
  map_id := sorry
  map_comp := sorry

-- ============================================================
-- 5. 自然变换 (Natural Transformation)
-- ============================================================

/-
## 5.1 自然变换的定义

自然变换 η : F ⟹ G 包含：
对每个对象X，态射 η_X : F(X) → G(X)

满足自然性：对任意 f : X → Y，
G(f) ∘ η_X = η_Y ∘ F(f)
-/

-- 使用 Mathlib 的 NatTrans
structure NatTrans' {C D : Type*} [Category C] [Category D] 
    (F G : C ⥤ D) where
  app : ∀ X, F.obj X ⟶ G.obj X
  naturality : ∀ {X Y} (f : X ⟶ Y), 
    F.map f ≫ app Y = app X ≫ G.map f

notation:50 F " ⟹' " G => NatTrans' F G

/-
## 5.2 自然变换的垂直复合
-/

def vcomp {C D : Type*} [Category C] [Category D] {F G H : C ⥤ D}
    (α : F ⟹' G) (β : G ⟹' H) : F ⟹' H where
  app := fun X => α.app X ≫ β.app X
  naturality := by
    intro X Y f
    simp
    rw [Category.assoc, β.naturality, ←Category.assoc, α.naturality, Category.assoc]

/-
## 5.3 自然变换的水平复合

Whiskering
-/

def whiskerLeft {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) {G H : D ⥤ E} (α : G ⟹' H) : 
    FunctorComp F G ⟹' FunctorComp F H where
  app := fun X => α.app (F.obj X)
  naturality := by
    intro X Y f
    simp
    apply α.naturality

-- ============================================================
-- 6. 积和余积 (Products and Coproducts)
-- ============================================================

/-
## 6.1 积 (Product)

对象 A × B 带有投影 π₁ : A × B → A 和 π₂ : A × B → B
满足泛性质
-/

structure Product {C : Type*} [Category C] (A B : C) where
  prod : C
  π₁ : prod ⟶ A
  π₂ : prod ⟶ B
  universal : ∀ {X} (f : X ⟶ A) (g : X ⟶ B), ∃! h : X ⟶ prod, 
    h ≫ π₁ = f ∧ h ≫ π₂ = g

/-
## 6.2 余积 (Coproduct)

对象 A + B 带有内射 ι₁ : A → A + B 和 ι₂ : B → A + B
-/

structure Coproduct {C : Type*} [Category C] (A B : C) where
  coprod : C
  ι₁ : A ⟶ coprod
  ι₂ : B ⟶ coprod
  universal : ∀ {X} (f : A ⟶ X) (g : B ⟶ X), ∃! h : coprod ⟶ X,
    ι₁ ≫ h = f ∧ ι₂ ≫ h = g

/-
## 6.3 笛卡尔闭范畴 (CCC)

范畴有：
- 终对象
- 积
- 指数对象（函数对象）
-/

structure CartesianClosed {C : Type*} [Category C] where
  terminal : C  -- 终对象
  terminal_is_terminal : ∀ X, ∃! f : X ⟶ terminal, True
  
  prod : ∀ A B, Product A B  -- 积
  
  exp : ∀ A B, C  -- 指数对象 B^A
  eval : ∀ A B, prod.prod (exp A B) A ⟶ B  -- 求值映射
  curry : ∀ {A B X} (f : (prod.prod X A).prod ⟶ B), 
    X ⟶ exp A B  -- 柯里化
  -- 需要添加更多的条件来表示笛卡尔闭性

-- ============================================================
-- 7. 与类型论的对应 (Curry-Howard-Lambek)
-- ============================================================

/-
## 7.1 对应关系

逻辑      | 类型论    | 范畴论
----------|-----------|------------------
命题 P    | 类型 P    | 对象 P
证明 p:P  | 项 p:P    | 态射 p:𝟙→P
P → Q     | 函数类型  | 指数对象 Q^P
P ∧ Q     | 积类型    | 积 P×Q
P ∨ Q     | 和类型    | 余积 P+Q
真        | Unit      | 终对象 𝟙
假        | Empty     | 始对象 ∅
∀x.P(x)   | 依赖积    | 局部积
∃x.P(x)   | 依赖和    | 局部余积
-/

-- 类型范畴是笛卡尔闭的
def TypeCCC : CartesianClosed where
  terminal := PUnit
  terminal_is_terminal := fun X => 
    ⟨(fun _ => PUnit.unit), by intro f; funext _; simp⟩
  
  prod := fun A B => {
    prod := A × B
    π₁ := fun p => p.1
    π₂ := fun p => p.2
    universal := fun f g => 
      ⟨fun x => (f x, g x), by simp, fun h hh => by funext x; simp [hh]⟩
  }
  
  exp := fun A B => A → B
  eval := fun A B p => p.1 p.2
  curry := fun f => fun x y => f (x, y)

end CategoryTheory
