# 3. 代数基础 (Algebra Foundations)

## 3.1 概述

代数是研究代数结构（如群、环、域等）及其性质的数学分支。代数为形式科学、计算机科学、密码学等领域提供了理论基础。

## 3.2 群论

### 3.2.1 群的定义

**定义 3.1** (群)
群是一个二元运算的集合 $(G, \ast)$，满足：
1. **封闭性**: $\forall a, b \in G, a \ast b \in G$
2. **结合律**: $\forall a, b, c \in G, (a \ast b) \ast c = a \ast (b \ast c)$
3. **单位元**: $\exists e \in G, \forall a \in G, e \ast a = a \ast e = a$
4. **逆元**: $\forall a \in G, \exists b \in G, a \ast b = b \ast a = e$

如果还满足 $a \ast b = b \ast a$，则称为**阿贝尔群**。

### 3.2.2 群的例子
- $(\mathbb{Z}, +)$
- $(\mathbb{R}^*, \cdot)$
- 对称群 $S_n$

### 3.2.3 子群与陪集

**定义 3.2** (子群)
$H \leq G$ 当且仅当 $H \subseteq G$ 且 $H$ 本身是群。

**定理 3.1** (拉格朗日定理)
有限群 $G$ 的任意子群 $H$ 的阶整除 $G$ 的阶。

**证明**: $G$ 可分解为 $H$ 的陪集，陪集等势。

### 3.2.4 同态与同构

**定义 3.3** (群同态)
$f: G \to H$ 是群同态当且仅当 $f(a \ast b) = f(a) \ast' f(b)$。

**定义 3.4** (群同构)
$f$ 是双射的群同态。

## 3.3 环论

### 3.3.1 环的定义

**定义 3.5** (环)
环 $(R, +, \cdot)$ 满足：
1. $(R, +)$ 是阿贝尔群
2. $\cdot$ 封闭且结合
3. $\cdot$ 对 $+$ 分配

若 $\cdot$ 有单位元，称为含幺环；若 $\cdot$ 交换，称为交换环。

### 3.3.2 理想与商环

**定义 3.6** (理想)
$A \subseteq R$ 是理想当且仅当：
1. $A$ 对 $+$ 封闭
2. $\forall r \in R, a \in A, ra, ar \in A$

**定义 3.7** (商环)
$R/A$ 是 $R$ 关于理想 $A$ 的商结构。

## 3.4 域论

### 3.4.1 域的定义

**定义 3.8** (域)
域 $(F, +, \cdot)$ 是交换环，$F \setminus \{0\}$ 关于 $\cdot$ 构成阿贝尔群。

### 3.4.2 有限域

**定理 3.2** (有限域存在性)
对任意素数 $p$ 和正整数 $n$，存在唯一（同构意义下）有限域 $\mathbb{F}_{p^n}$。

## 3.5 代数结构在计算机科学中的应用

### 3.5.1 群与密码学

```rust
// 椭圆曲线群上的点加法
struct Point {
    x: i64,
    y: i64,
}

fn point_add(p: &Point, q: &Point, a: i64, p_mod: i64) -> Point {
    // 省略具体实现
    Point { x: 0, y: 0 }
}
```

### 3.5.2 环与多项式运算

```rust
// 多项式加法
fn poly_add(a: &[i64], b: &[i64]) -> Vec<i64> {
    let n = a.len().max(b.len());
    let mut res = vec![0; n];
    for i in 0..n {
        res[i] = a.get(i).unwrap_or(&0) + b.get(i).unwrap_or(&0);
    }
    res
}
```

### 3.5.3 域与有限域运算

```rust
// 有限域上的加法和乘法
fn gf_add(a: u8, b: u8, p: u8) -> u8 {
    (a + b) % p
}
fn gf_mul(a: u8, b: u8, p: u8) -> u8 {
    (a * b) % p
}
```

### 3.5.4 形式化证明

```lean
-- Lean 中的群定义
structure group (G : Type*) extends has_mul G, has_one G, has_inv G :=
  (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
  (one_mul : ∀ a : G, 1 * a = a)
  (mul_left_inv : ∀ a : G, a⁻¹ * a = 1)

-- 拉格朗日定理
lemma lagrange_theorem {G : Type*} [fintype G] [group G] (H : set G) [is_subgroup H] :
  fintype.card H ∣ fintype.card G :=
begin
  -- 证明实现
  sorry
end
```

## 3.6 总结

代数为形式科学和计算机科学提供了结构化的理论基础，群、环、域等结构广泛应用于密码学、编码理论、算法设计等领域。

## 参考文献

1. Herstein, I. N. (1975). *Topics in algebra*. Wiley.
2. Dummit, D. S., & Foote, R. M. (2004). *Abstract algebra*. Wiley.
3. Artin, M. (2011). *Algebra*. Pearson.
4. Lidl, R., & Niederreiter, H. (1997). *Finite fields*. Cambridge University Press.

---

**更新时间**: 2024-12-21  
**版本**: 1.0  
**作者**: FormalScience Team 