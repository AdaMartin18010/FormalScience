# 02. 数论基础 (Number Theory)

## 目录

1. [基本概念](#1-基本概念)
2. [整除理论](#2-整除理论)
3. [素数理论](#3-素数理论)
4. [同余理论](#4-同余理论)
5. [二次剩余](#5-二次剩余)
6. [原根理论](#6-原根理论)
7. [连分数](#7-连分数)
8. [代数数论](#8-代数数论)
9. [解析数论](#9-解析数论)
10. [应用与算法](#10-应用与算法)

## 1. 基本概念

### 1.1 自然数与整数

**定义 1.1.1** (自然数集)
自然数集 $\mathbb{N}$ 是满足以下公理的集合：
- $0 \in \mathbb{N}$
- 如果 $n \in \mathbb{N}$，则 $n + 1 \in \mathbb{N}$
- 数学归纳原理

**定义 1.1.2** (整数集)
整数集 $\mathbb{Z}$ 定义为：
$$\mathbb{Z} = \{..., -2, -1, 0, 1, 2, ...\}$$

### 1.2 整除关系

**定义 1.2.1** (整除)
对于整数 $a, b$，如果存在整数 $k$ 使得 $a = kb$，则称 $b$ 整除 $a$，记作 $b \mid a$。

**性质 1.2.1** (整除的基本性质)
1. 如果 $a \mid b$ 且 $b \mid c$，则 $a \mid c$
2. 如果 $a \mid b$ 且 $a \mid c$，则 $a \mid (bx + cy)$ 对所有整数 $x, y$
3. 如果 $a \mid b$ 且 $b \mid a$，则 $a = \pm b$

### 1.3 最大公约数

**定义 1.3.1** (最大公约数)
整数 $a, b$ 的最大公约数 $\gcd(a, b)$ 是满足以下条件的最大正整数 $d$：
- $d \mid a$ 且 $d \mid b$
- 如果 $c \mid a$ 且 $c \mid b$，则 $c \mid d$

**定理 1.3.1** (贝祖定理)
对于任意整数 $a, b$，存在整数 $x, y$ 使得：
$$\gcd(a, b) = ax + by$$

**证明**：
使用扩展欧几里得算法构造性证明。

```lean
-- Lean 4 证明示例
theorem bezout_identity (a b : ℤ) : ∃ x y : ℤ, a * x + b * y = gcd a b :=
begin
  -- 使用扩展欧几里得算法
  induction' b with b' ih,
  { use [1, 0], simp },
  { 
    -- 递归构造解
    cases ih with x y h,
    use [y, x - (a / b) * y],
    -- 验证等式成立
    ring,
    exact h
  }
end
```

## 2. 整除理论

### 2.1 带余除法

**定理 2.1.1** (带余除法)
对于任意整数 $a$ 和正整数 $b$，存在唯一的整数 $q$ 和 $r$ 使得：
$$a = bq + r, \quad 0 \leq r < b$$

**证明**：
1. **存在性**：构造性证明
2. **唯一性**：反证法

### 2.2 欧几里得算法

**算法 2.2.1** (欧几里得算法)
```rust
// Rust 实现
pub fn gcd(mut a: i64, mut b: i64) -> i64 {
    while b != 0 {
        let temp = b;
        b = a % b;
        a = temp;
    }
    a
}

// 扩展欧几里得算法
pub fn extended_gcd(a: i64, b: i64) -> (i64, i64, i64) {
    if b == 0 {
        (a, 1, 0)
    } else {
        let (gcd, x, y) = extended_gcd(b, a % b);
        (gcd, y, x - (a / b) * y)
    }
}
```

### 2.3 最小公倍数

**定义 2.3.1** (最小公倍数)
整数 $a, b$ 的最小公倍数 $\text{lcm}(a, b)$ 是满足以下条件的最小正整数 $m$：
- $a \mid m$ 且 $b \mid m$
- 如果 $a \mid c$ 且 $b \mid c$，则 $m \mid c$

**定理 2.3.1** (GCD-LCM 关系)
$$\gcd(a, b) \cdot \text{lcm}(a, b) = |ab|$$

## 3. 素数理论

### 3.1 素数定义

**定义 3.1.1** (素数)
大于1的整数 $p$ 是素数，当且仅当 $p$ 的正因子只有1和 $p$ 本身。

**定义 3.1.2** (合数)
大于1的非素数整数称为合数。

### 3.2 算术基本定理

**定理 3.2.1** (算术基本定理)
每个大于1的整数都可以唯一地表示为素数的乘积（不计顺序）。

**形式化表述**：
对于任意整数 $n > 1$，存在唯一的素数序列 $p_1 \leq p_2 \leq ... \leq p_k$ 和正整数序列 $e_1, e_2, ..., e_k$ 使得：
$$n = p_1^{e_1} p_2^{e_2} \cdots p_k^{e_k}$$

**证明**：
1. **存在性**：数学归纳法
2. **唯一性**：使用素数性质

```lean
-- Lean 4 证明框架
theorem fundamental_theorem_arithmetic (n : ℕ) (h : n > 1) :
  ∃ (primes : list ℕ) (exponents : list ℕ),
    (∀ p ∈ primes, prime p) ∧
    n = list.prod (list.zip_with (^) primes exponents) :=
begin
  -- 构造性证明
  induction' n using nat.strong_induction_on with n ih,
  -- 如果 n 是素数，直接返回
  -- 否则，找到 n 的一个素因子 p，递归处理 n/p
end
```

### 3.3 素数分布

**定理 3.3.1** (欧几里得)
素数有无穷多个。

**证明**：
反证法。假设素数只有有限个：$p_1, p_2, ..., p_k$。
考虑数 $N = p_1 p_2 \cdots p_k + 1$。
$N$ 不能被任何 $p_i$ 整除，因此 $N$ 是素数或包含新的素因子，矛盾。

**定理 3.3.2** (素数定理)
设 $\pi(x)$ 表示不超过 $x$ 的素数个数，则：
$$\lim_{x \to \infty} \frac{\pi(x)}{x/\ln x} = 1$$

## 4. 同余理论

### 4.1 同余定义

**定义 4.1.1** (同余)
对于整数 $a, b$ 和正整数 $m$，如果 $m \mid (a - b)$，则称 $a$ 与 $b$ 模 $m$ 同余，记作：
$$a \equiv b \pmod{m}$$

### 4.2 同余性质

**性质 4.2.1** (同余的基本性质)
1. 自反性：$a \equiv a \pmod{m}$
2. 对称性：如果 $a \equiv b \pmod{m}$，则 $b \equiv a \pmod{m}$
3. 传递性：如果 $a \equiv b \pmod{m}$ 且 $b \equiv c \pmod{m}$，则 $a \equiv c \pmod{m}$
4. 运算保持：如果 $a \equiv b \pmod{m}$ 且 $c \equiv d \pmod{m}$，则：
   - $a + c \equiv b + d \pmod{m}$
   - $ac \equiv bd \pmod{m}$

### 4.3 线性同余方程

**定义 4.3.1** (线性同余方程)
形如 $ax \equiv b \pmod{m}$ 的方程称为线性同余方程。

**定理 4.3.1** (线性同余方程解的存在性)
线性同余方程 $ax \equiv b \pmod{m}$ 有解当且仅当 $\gcd(a, m) \mid b$。

**证明**：
使用贝祖定理和同余性质。

```rust
// Rust 实现：求解线性同余方程
pub fn solve_linear_congruence(a: i64, b: i64, m: i64) -> Option<Vec<i64>> {
    let (gcd, x, _) = extended_gcd(a, m);
    
    if b % gcd != 0 {
        None
    } else {
        let x0 = (x * (b / gcd)) % m;
        let solutions: Vec<i64> = (0..gcd)
            .map(|i| (x0 + i * (m / gcd)) % m)
            .collect();
        Some(solutions)
    }
}
```

### 4.4 中国剩余定理

**定理 4.4.1** (中国剩余定理)
设 $m_1, m_2, ..., m_k$ 是两两互素的正整数，$a_1, a_2, ..., a_k$ 是任意整数，则同余方程组：
$$\begin{cases}
x \equiv a_1 \pmod{m_1} \\
x \equiv a_2 \pmod{m_2} \\
\vdots \\
x \equiv a_k \pmod{m_k}
\end{cases}$$
有唯一解模 $M = m_1 m_2 \cdots m_k$。

**证明**：
构造性证明，使用扩展欧几里得算法。

```rust
// Rust 实现：中国剩余定理
pub fn chinese_remainder_theorem(
    remainders: &[i64],
    moduli: &[i64]
) -> Option<i64> {
    if remainders.len() != moduli.len() {
        return None;
    }
    
    let mut result = 0;
    let mut product = 1;
    
    // 计算所有模数的乘积
    for &m in moduli {
        product *= m;
    }
    
    for i in 0..remainders.len() {
        let pi = product / moduli[i];
        let (_, inv, _) = extended_gcd(pi, moduli[i]);
        result = (result + remainders[i] * pi * inv) % product;
    }
    
    Some((result + product) % product)
}
```

## 5. 二次剩余

### 5.1 二次剩余定义

**定义 5.1.1** (二次剩余)
对于素数 $p$ 和整数 $a$，如果存在整数 $x$ 使得 $x^2 \equiv a \pmod{p}$，则称 $a$ 是模 $p$ 的二次剩余。

### 5.2 勒让德符号

**定义 5.2.1** (勒让德符号)
对于素数 $p$ 和整数 $a$，勒让德符号定义为：
$$\left(\frac{a}{p}\right) = \begin{cases}
1 & \text{如果 } a \text{ 是模 } p \text{ 的二次剩余} \\
-1 & \text{如果 } a \text{ 不是模 } p \text{ 的二次剩余} \\
0 & \text{如果 } p \mid a
\end{cases}$$

### 5.3 二次互反律

**定理 5.3.1** (二次互反律)
对于不同的奇素数 $p, q$：
$$\left(\frac{p}{q}\right) \left(\frac{q}{p}\right) = (-1)^{\frac{p-1}{2} \cdot \frac{q-1}{2}}$$

## 6. 原根理论

### 6.1 原根定义

**定义 6.1.1** (原根)
对于素数 $p$，如果整数 $g$ 的阶等于 $p-1$，则称 $g$ 是模 $p$ 的原根。

**定义 6.1.2** (阶)
对于整数 $a$ 和正整数 $m$，如果 $\gcd(a, m) = 1$，则 $a$ 模 $m$ 的阶是最小的正整数 $k$ 使得 $a^k \equiv 1 \pmod{m}$。

### 6.2 原根存在性

**定理 6.2.1** (原根存在性)
每个素数都有原根。

**证明**：
使用群论和有限域理论。

## 7. 连分数

### 7.1 连分数定义

**定义 7.1.1** (简单连分数)
形如 $[a_0; a_1, a_2, ...]$ 的表达式称为简单连分数，其中 $a_0$ 是整数，$a_1, a_2, ...$ 是正整数。

### 7.2 连分数展开

**算法 7.2.1** (实数连分数展开)
```rust
// Rust 实现：实数连分数展开
pub fn continued_fraction_expansion(x: f64, max_terms: usize) -> Vec<i64> {
    let mut result = Vec::new();
    let mut current = x;
    
    for _ in 0..max_terms {
        let integer_part = current.floor() as i64;
        result.push(integer_part);
        
        let fractional_part = current - integer_part as f64;
        if fractional_part.abs() < 1e-10 {
            break;
        }
        current = 1.0 / fractional_part;
    }
    
    result
}
```

## 8. 代数数论

### 8.1 代数数

**定义 8.1.1** (代数数)
复数 $\alpha$ 是代数数，如果存在非零多项式 $f(x) \in \mathbb{Q}[x]$ 使得 $f(\alpha) = 0$。

### 8.2 代数整数

**定义 8.2.1** (代数整数)
代数数 $\alpha$ 是代数整数，如果存在首一多项式 $f(x) \in \mathbb{Z}[x]$ 使得 $f(\alpha) = 0$。

## 9. 解析数论

### 9.1 黎曼ζ函数

**定义 9.1.1** (黎曼ζ函数)
对于复数 $s$，$\Re(s) > 1$，黎曼ζ函数定义为：
$$\zeta(s) = \sum_{n=1}^{\infty} \frac{1}{n^s}$$

### 9.2 素数分布函数

**定义 9.2.1** (素数计数函数)
$$\pi(x) = \sum_{p \leq x, p \text{ 素数}} 1$$

## 10. 应用与算法

### 10.1 密码学应用

#### 10.1.1 RSA 加密
基于大整数分解困难性的公钥加密系统。

```rust
// Rust 实现：RSA 密钥生成
pub struct RSAKey {
    pub n: i64,
    pub e: i64,
    pub d: i64,
}

pub fn generate_rsa_keys(bit_length: usize) -> RSAKey {
    // 生成大素数
    let p = generate_large_prime(bit_length / 2);
    let q = generate_large_prime(bit_length / 2);
    
    let n = p * q;
    let phi = (p - 1) * (q - 1);
    
    // 选择公钥指数
    let e = 65537; // 常用选择
    
    // 计算私钥
    let (_, d, _) = extended_gcd(e, phi);
    let d = (d % phi + phi) % phi;
    
    RSAKey { n, e, d }
}
```

#### 10.1.2 椭圆曲线密码学
基于椭圆曲线离散对数问题的密码系统。

### 10.2 算法复杂度

#### 10.2.1 素数测试
- **试除法**：$O(\sqrt{n})$
- **Miller-Rabin 测试**：$O(k \log^3 n)$（概率性）
- **AKS 测试**：$O(\log^{12} n)$（确定性）

```rust
// Rust 实现：Miller-Rabin 素数测试
pub fn miller_rabin(n: u64, k: u32) -> bool {
    if n <= 1 || n == 4 {
        return false;
    }
    if n <= 3 {
        return true;
    }
    
    // 将 n-1 写成 d * 2^r 的形式
    let mut d = n - 1;
    let mut r = 0;
    while d % 2 == 0 {
        d /= 2;
        r += 1;
    }
    
    // 进行 k 次测试
    for _ in 0..k {
        let a = 2 + (rand::random::<u64>() % (n - 4));
        let mut x = mod_pow(a, d, n);
        
        if x == 1 || x == n - 1 {
            continue;
        }
        
        for _ in 1..r {
            x = (x * x) % n;
            if x == n - 1 {
                break;
            }
            if x == 1 {
                return false;
            }
        }
        
        if x != n - 1 {
            return false;
        }
    }
    
    true
}
```

#### 10.2.2 整数分解
- **试除法**：$O(\sqrt{n})$
- **Pollard's rho 算法**：$O(\sqrt{p})$（$p$ 是最小素因子）
- **二次筛法**：$O(e^{\sqrt{\ln n \ln \ln n}})$

### 10.3 数论函数

#### 10.3.1 欧拉函数
**定义 10.3.1** (欧拉函数)
$\phi(n)$ 表示不超过 $n$ 且与 $n$ 互素的正整数个数。

**性质 10.3.1**
- 如果 $p$ 是素数，则 $\phi(p) = p - 1$
- 如果 $\gcd(m, n) = 1$，则 $\phi(mn) = \phi(m)\phi(n)$
- $\phi(n) = n \prod_{p \mid n} (1 - \frac{1}{p})$

```rust
// Rust 实现：欧拉函数
pub fn euler_totient(n: u64) -> u64 {
    let mut result = n;
    let mut n_mut = n;
    
    for i in 2..=((n as f64).sqrt() as u64) {
        if n_mut % i == 0 {
            while n_mut % i == 0 {
                n_mut /= i;
            }
            result = result / i * (i - 1);
        }
    }
    
    if n_mut > 1 {
        result = result / n_mut * (n_mut - 1);
    }
    
    result
}
```

#### 10.3.2 莫比乌斯函数
**定义 10.3.2** (莫比乌斯函数)
$$\mu(n) = \begin{cases}
1 & \text{如果 } n = 1 \\
(-1)^k & \text{如果 } n \text{ 是 } k \text{ 个不同素数的乘积} \\
0 & \text{如果 } n \text{ 包含平方因子}
\end{cases}$$

## 参考文献

1. Hardy, G. H., & Wright, E. M. (2008). *An Introduction to the Theory of Numbers*. Oxford University Press.
2. Ireland, K., & Rosen, M. (1990). *A Classical Introduction to Modern Number Theory*. Springer.
3. Niven, I., Zuckerman, H. S., & Montgomery, H. L. (1991). *An Introduction to the Theory of Numbers*. Wiley.
4. Rosen, K. H. (2011). *Elementary Number Theory and Its Applications*. Pearson.
5. Silverman, J. H. (2006). *A Friendly Introduction to Number Theory*. Pearson.

## 交叉引用

- [01_Philosophical_Foundations/01_Epistemological_Foundations.md](../01_Philosophical_Foundations/01_Epistemological_Foundations.md) - 数学知识的认识论基础
- [02_Mathematical_Foundations/01_Set_Theory.md](01_Set_Theory.md) - 集合论基础
- [03_Logic_Theory/01_Propositional_Logic.md](../03_Logic_Theory/01_Propositional_Logic.md) - 逻辑推理基础
- [04_Formal_Language_Theory/01_Formal_Grammars.md](../04_Formal_Language_Theory/01_Formal_Grammars.md) - 形式语言理论
- [15_Information_Theory/01_Information_Theory_Foundations.md](../15_Information_Theory/01_Information_Theory_Foundations.md) - 信息论基础 