# 7. 范畴论基础 (Category Theory Foundations)

## 7.1 概述

范畴论是研究数学结构及其关系的抽象理论，为现代数学、计算机科学和形式化方法提供了统一的语言。

## 7.2 基本概念

### 7.2.1 范畴定义

**定义 7.1** (范畴)
范畴 $\mathcal{C}$ 包含：
1. **对象类** $\text{Ob}(\mathcal{C})$
2. **态射类** $\text{Mor}(\mathcal{C})$
3. **复合运算** $\circ$
4. **单位态射** $1_A: A \to A$

满足：
- 结合律：$(f \circ g) \circ h = f \circ (g \circ h)$
- 单位律：$f \circ 1_A = f = 1_B \circ f$

### 7.2.2 函子

**定义 7.2** (函子)
函子 $F: \mathcal{C} \to \mathcal{D}$ 包含：
1. 对象映射：$F: \text{Ob}(\mathcal{C}) \to \text{Ob}(\mathcal{D})$
2. 态射映射：$F: \text{Mor}(\mathcal{C}) \to \text{Mor}(\mathcal{D})$

满足：
- $F(f \circ g) = F(f) \circ F(g)$
- $F(1_A) = 1_{F(A)}$

### 7.2.3 自然变换

**定义 7.3** (自然变换)
自然变换 $\eta: F \Rightarrow G$ 是态射族 $\{\eta_A: F(A) \to G(A)\}$，满足：
$$G(f) \circ \eta_A = \eta_B \circ F(f)$$

## 7.3 极限与余极限

### 7.3.1 积与余积

**定义 7.4** (积)
对象 $A \times B$ 是 $A, B$ 的积，若存在投影态射 $\pi_1, \pi_2$ 满足泛性质。

**定义 7.5** (余积)
对象 $A + B$ 是 $A, B$ 的余积，若存在包含态射 $\iota_1, \iota_2$ 满足泛性质。

### 7.3.2 等化子与余等化子

**定义 7.6** (等化子)
$\text{Eq}(f, g)$ 是 $f, g: A \to B$ 的等化子，若 $f \circ e = g \circ e$ 且满足泛性质。

## 7.4 伴随函子

### 7.4.1 伴随定义

**定义 7.7** (伴随函子)
$F \dashv G$ 当且仅当存在自然同构：
$$\text{Hom}_{\mathcal{D}}(F(A), B) \cong \text{Hom}_{\mathcal{C}}(A, G(B))$$

### 7.4.2 伴随性质

**定理 7.1** (伴随函子性质)
1. 左伴随保持余极限
2. 右伴随保持极限

## 7.5 单子与余单子

### 7.5.1 单子

**定义 7.8** (单子)
单子 $(T, \eta, \mu)$ 包含：
- 函子 $T: \mathcal{C} \to \mathcal{C}$
- 单位自然变换 $\eta: 1 \Rightarrow T$
- 乘法自然变换 $\mu: T^2 \Rightarrow T$

满足：
- $\mu \circ T\mu = \mu \circ \mu T$
- $\mu \circ T\eta = \mu \circ \eta T = 1$

### 7.5.2 余单子

**定义 7.9** (余单子)
余单子是单子的对偶概念。

## 7.6 范畴论在计算机科学中的应用

### 7.6.1 函数式编程

```haskell
-- Haskell 中的函子
class Functor f where
  fmap :: (a -> b) -> f a -> f b

-- 单子
class Monad m where
  return :: a -> m a
  (>>=) :: m a -> (a -> m b) -> m b

-- 自然变换
type Nat f g = forall a. f a -> g a
```

### 7.6.2 类型理论

```rust
// Rust 中的函子概念
trait Functor<A, B> {
    type Output;
    fn map<F>(self, f: F) -> Self::Output
    where F: Fn(A) -> B;
}

// 单子概念
trait Monad<A, B> {
    type Output;
    fn bind<F>(self, f: F) -> Self::Output
    where F: Fn(A) -> Self::Output;
}
```

### 7.6.3 形式化证明

```lean
-- Lean 中的范畴论
import category_theory.basic

-- 范畴定义
structure category (obj : Type*) (hom : obj → obj → Type*) :=
  (id : Π X : obj, hom X X)
  (comp : Π {X Y Z : obj}, hom X Y → hom Y Z → hom X Z)
  (id_comp' : ∀ {X Y : obj} (f : hom X Y), comp (id X) f = f)
  (comp_id' : ∀ {X Y : obj} (f : hom X Y), comp f (id Y) = f)
  (assoc' : ∀ {W X Y Z : obj} (f : hom W X) (g : hom X Y) (h : hom Y Z),
    comp (comp f g) h = comp f (comp g h))

-- 函子定义
structure functor (C D : Type*) [category C] [category D] :=
  (obj : C → D)
  (map : Π {X Y : C}, (X ⟶ Y) → (obj X ⟶ obj D))
  (map_id' : ∀ (X : C), map (𝟙 X) = 𝟙 (obj X))
  (map_comp' : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    map (f ≫ g) = (map f) ≫ (map g))
```

## 7.7 总结

范畴论为现代数学和计算机科学提供了统一的抽象框架，在类型理论、函数式编程、代数几何等领域有重要应用。

## 参考文献

1. Mac Lane, S. (1998). *Categories for the working mathematician*. Springer.
2. Awodey, S. (2010). *Category theory*. Oxford University Press.
3. Barr, M., & Wells, C. (1995). *Category theory for computing science*. Prentice Hall.
4. Pierce, B. C. (1991). *Basic category theory for computer scientists*. MIT Press.

---

**更新时间**: 2024-12-21  
**版本**: 1.0  
**作者**: FormalScience Team 