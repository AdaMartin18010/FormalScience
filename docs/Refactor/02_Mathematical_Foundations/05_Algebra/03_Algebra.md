# 03. 代数基础 (Algebra)

## 目录

1. [群论基础](#1-群论基础)
2. [环论基础](#2-环论基础)
3. [域论基础](#3-域论基础)
4. [模论基础](#4-模论基础)
5. [线性代数](#5-线性代数)
6. [多项式理论](#6-多项式理论)
7. [伽罗瓦理论](#7-伽罗瓦理论)
8. [表示论](#8-表示论)
9. [同调代数](#9-同调代数)
10. [应用与算法](#10-应用与算法)

## 1. 群论基础

### 1.1 群的定义

**定义 1.1.1** (群)
群是一个集合 $G$ 连同二元运算 $\cdot: G \times G \to G$，满足以下公理：

1. **结合律**：$(a \cdot b) \cdot c = a \cdot (b \cdot c)$ 对所有 $a, b, c \in G$
2. **单位元**：存在 $e \in G$ 使得 $e \cdot a = a \cdot e = a$ 对所有 $a \in G$
3. **逆元**：对每个 $a \in G$，存在 $a^{-1} \in G$ 使得 $a \cdot a^{-1} = a^{-1} \cdot a = e$

**定义 1.1.2** (阿贝尔群)
如果群 $G$ 还满足交换律 $a \cdot b = b \cdot a$ 对所有 $a, b \in G$，则称 $G$ 为阿贝尔群。

### 1.2 群的基本性质

**定理 1.2.1** (群的唯一性)

1. 群的单位元是唯一的
2. 每个元素的逆元是唯一的

**证明**：

1. 假设 $e_1, e_2$ 都是单位元，则 $e_1 = e_1 \cdot e_2 = e_2$
2. 假设 $a^{-1}, a'$ 都是 $a$ 的逆元，则 $a^{-1} = a^{-1} \cdot e = a^{-1} \cdot (a \cdot a') = (a^{-1} \cdot a) \cdot a' = e \cdot a' = a'$

**定理 1.2.2** (消去律)
在群 $G$ 中，如果 $a \cdot b = a \cdot c$，则 $b = c$；如果 $b \cdot a = c \cdot a$，则 $b = c$。

### 1.3 子群

**定义 1.3.1** (子群)
群 $G$ 的子集 $H$ 是子群，如果：

1. $H$ 非空
2. 如果 $a, b \in H$，则 $a \cdot b \in H$
3. 如果 $a \in H$，则 $a^{-1} \in H$

**定理 1.3.1** (子群判定)
群 $G$ 的非空子集 $H$ 是子群当且仅当对任意 $a, b \in H$，有 $a \cdot b^{-1} \in H$。

### 1.4 陪集与拉格朗日定理

**定义 1.4.1** (左陪集)
群 $G$ 的子群 $H$ 的左陪集定义为：
$$aH = \{a \cdot h \mid h \in H\}$$

**定义 1.4.2** (右陪集)
群 $G$ 的子群 $H$ 的右陪集定义为：
$$Ha = \{h \cdot a \mid h \in H\}$$

**定理 1.4.1** (拉格朗日定理)
有限群 $G$ 的子群 $H$ 的阶整除 $G$ 的阶：
$$|H| \mid |G|$$

**证明**：

1. 所有左陪集的大小相等且等于 $|H|$
2. 不同的左陪集不相交
3. $G$ 是所有左陪集的并集
4. 因此 $|G| = [G:H] \cdot |H|$，其中 $[G:H]$ 是 $H$ 在 $G$ 中的指数

### 1.5 正规子群与商群

**定义 1.5.1** (正规子群)
群 $G$ 的子群 $N$ 是正规子群，如果对任意 $g \in G$，有 $gNg^{-1} = N$。

**定义 1.5.2** (商群)
群 $G$ 关于正规子群 $N$ 的商群定义为：
$$G/N = \{gN \mid g \in G\}$$
运算为 $(g_1N) \cdot (g_2N) = (g_1g_2)N$。

**定理 1.5.1** (第一同构定理)
如果 $\phi: G \to H$ 是群同态，则：
$$G/\ker(\phi) \cong \text{im}(\phi)$$

### 1.6 循环群

**定义 1.6.1** (循环群)
群 $G$ 是循环群，如果存在 $g \in G$ 使得 $G = \langle g \rangle = \{g^n \mid n \in \mathbb{Z}\}$。

**定理 1.6.1** (循环群的结构)

1. 无限循环群同构于 $(\mathbb{Z}, +)$
2. 有限循环群同构于 $(\mathbb{Z}_n, +)$

```lean
-- Lean 4 证明示例：循环群的结构
theorem cyclic_group_structure (G : Type*) [group G] (g : G) (h : G = subgroup.closure {g}) :
  (G ≃* ℤ) ∨ (∃ n : ℕ, G ≃* zmod n) :=
begin
  -- 根据 g 的阶进行分类讨论
  cases (order_of g).eq_zero_or_pos with h1 h2,
  { -- 无限阶情况
    left,
    -- 构造同构
    sorry
  },
  { -- 有限阶情况
    right,
    -- 构造同构
    sorry
  }
end
```

## 2. 环论基础

### 2.1 环的定义

**定义 2.1.1** (环)
环是一个集合 $R$ 连同两个二元运算 $+$ 和 $\cdot$，满足：

1. $(R, +)$ 是阿贝尔群
2. $(R, \cdot)$ 是半群（满足结合律）
3. 分配律：$a \cdot (b + c) = a \cdot b + a \cdot c$ 和 $(a + b) \cdot c = a \cdot c + b \cdot c$

**定义 2.1.2** (交换环)
如果环 $R$ 的乘法满足交换律，则称 $R$ 为交换环。

**定义 2.1.3** (单位环)
如果环 $R$ 有乘法单位元，则称 $R$ 为单位环。

### 2.2 环的基本性质

**定理 2.2.1** (环的基本性质)
在环 $R$ 中：

1. $0 \cdot a = a \cdot 0 = 0$ 对所有 $a \in R$
2. $(-a) \cdot b = a \cdot (-b) = -(a \cdot b)$
3. $(-a) \cdot (-b) = a \cdot b$

### 2.3 理想

**定义 2.3.1** (左理想)
环 $R$ 的子集 $I$ 是左理想，如果：

1. $(I, +)$ 是 $(R, +)$ 的子群
2. 对任意 $r \in R$ 和 $a \in I$，有 $r \cdot a \in I$

**定义 2.3.2** (右理想)
环 $R$ 的子集 $I$ 是右理想，如果：

1. $(I, +)$ 是 $(R, +)$ 的子群
2. 对任意 $r \in R$ 和 $a \in I$，有 $a \cdot r \in I$

**定义 2.3.3** (理想)
既是左理想又是右理想的子集称为理想。

### 2.4 商环

**定义 2.4.1** (商环)
环 $R$ 关于理想 $I$ 的商环定义为：
$$R/I = \{r + I \mid r \in R\}$$
运算为 $(r_1 + I) + (r_2 + I) = (r_1 + r_2) + I$ 和 $(r_1 + I) \cdot (r_2 + I) = (r_1 \cdot r_2) + I$。

**定理 2.4.1** (环的第一同构定理)
如果 $\phi: R \to S$ 是环同态，则：
$$R/\ker(\phi) \cong \text{im}(\phi)$$

### 2.5 整环与域

**定义 2.5.1** (整环)
交换单位环 $R$ 是整环，如果 $R$ 没有零因子（即 $a \cdot b = 0$ 蕴含 $a = 0$ 或 $b = 0$）。

**定义 2.5.2** (域)
交换单位环 $F$ 是域，如果 $F \setminus \{0\}$ 在乘法下构成群。

**定理 2.5.1** (域的性质)
域是整环，且每个非零元素都有乘法逆元。

## 3. 域论基础

### 3.1 域扩张

**定义 3.1.1** (域扩张)
如果 $F$ 是 $K$ 的子域，则称 $F$ 是 $K$ 的域扩张，记作 $K/F$。

**定义 3.1.2** (扩张次数)
域扩张 $K/F$ 的次数定义为 $K$ 作为 $F$ 向量空间的维数，记作 $[K:F]$。

### 3.2 代数扩张

**定义 3.2.1** (代数元素)
元素 $\alpha \in K$ 在 $F$ 上是代数的，如果存在非零多项式 $f(x) \in F[x]$ 使得 $f(\alpha) = 0$。

**定义 3.2.2** (代数扩张)
域扩张 $K/F$ 是代数扩张，如果 $K$ 的每个元素在 $F$ 上都是代数的。

**定理 3.2.1** (有限扩张是代数扩张)
如果 $[K:F] < \infty$，则 $K/F$ 是代数扩张。

### 3.3 分裂域

**定义 3.3.1** (分裂域)
多项式 $f(x) \in F[x]$ 的分裂域是包含 $F$ 和 $f(x)$ 所有根的最小域。

**定理 3.3.1** (分裂域的存在性)
每个多项式都有分裂域，且在 $F$ 同构意义下唯一。

## 4. 模论基础

### 4.1 模的定义

**定义 4.1.1** (左模)
环 $R$ 上的左模是一个阿贝尔群 $M$ 连同标量乘法 $R \times M \to M$，满足：

1. $(r + s) \cdot m = r \cdot m + s \cdot m$
2. $r \cdot (m + n) = r \cdot m + r \cdot n$
3. $(rs) \cdot m = r \cdot (s \cdot m)$
4. $1 \cdot m = m$（如果 $R$ 有单位元）

### 4.2 自由模

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
