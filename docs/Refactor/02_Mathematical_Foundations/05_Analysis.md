# 5. 数学分析基础 (Analysis Foundations)

## 5.1 概述

数学分析研究极限、连续、微分、积分等概念，是现代数学和科学建模的基础。

## 5.2 实数与极限

### 5.2.1 实数系

**定义 5.1** (实数)
实数 $\mathbb{R}$ 是有理数的完备有序域。

### 5.2.2 数列极限

**定义 5.2** (数列极限)
数列 $\{a_n\}$ 收敛于 $A$，记作 $\lim_{n\to\infty} a_n = A$，当且仅当：
$$\forall \varepsilon > 0, \exists N, \forall n > N, |a_n - A| < \varepsilon$$

### 5.2.3 函数极限

**定义 5.3** (函数极限)
$\lim_{x\to a} f(x) = L$ 当且仅当：
$$\forall \varepsilon > 0, \exists \delta > 0, \forall x, 0 < |x - a| < \delta \implies |f(x) - L| < \varepsilon$$

## 5.3 连续与可微

### 5.3.1 连续性

**定义 5.4** (连续函数)
$f$ 在 $a$ 连续当且仅当：
$$\lim_{x\to a} f(x) = f(a)$$

### 5.3.2 可微性

**定义 5.5** (可微函数)
$f$ 在 $a$ 可微当且仅当极限
$$f'(a) = \lim_{h\to 0} \frac{f(a+h) - f(a)}{h}$$
存在。

## 5.4 积分

### 5.4.1 不定积分

**定义 5.6** (不定积分)
$F(x)$ 是 $f(x)$ 的一个原函数，则
$$\int f(x) dx = F(x) + C$$

### 5.4.2 定积分

**定义 5.7** (定积分)
$$\int_a^b f(x) dx = \lim_{n\to\infty} \sum_{i=1}^n f(x_i^*) \Delta x$$

### 5.4.3 基本定理

**定理 5.1** (微积分基本定理)
若 $F'(x) = f(x)$，则
$$\int_a^b f(x) dx = F(b) - F(a)$$

## 5.5 级数

### 5.5.1 收敛级数

**定义 5.8** (级数收敛)
$\sum_{n=1}^\infty a_n$ 收敛当且仅当部分和极限存在。

### 5.5.2 泰勒级数

**定义 5.9** (泰勒级数)
$$f(x) = \sum_{n=0}^\infty \frac{f^{(n)}(a)}{n!}(x-a)^n$$

## 5.6 分析在计算机科学中的应用

### 5.6.1 数值分析

```rust
// 牛顿迭代法求方程根
fn newton_method<F: Fn(f64) -> f64, G: Fn(f64) -> f64>(f: F, df: G, x0: f64, tol: f64) -> f64 {
    let mut x = x0;
    loop {
        let x1 = x - f(x) / df(x);
        if (x1 - x).abs() < tol {
            break x1;
        }
        x = x1;
    }
}
```

### 5.6.2 信号处理与微分方程
- 傅里叶分析
- 拉普拉斯变换
- 常微分方程数值解法

### 5.6.3 形式化证明

```lean
-- Lean 中的极限定义
import analysis.special_functions.exp_log

def my_limit (a : ℕ → ℝ) (A : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n > N, |a n - A| < ε

-- 微积分基本定理
lemma fundamental_theorem_of_calculus (f F : ℝ → ℝ) (a b : ℝ)
  (hF : ∀ x, has_deriv_at F (f x) x) :
  ∫ x in a..b, f x = F b - F a :=
begin
  -- 证明实现
  sorry
end
```

## 5.7 总结

数学分析为科学建模、工程计算、信号处理等领域提供了理论基础。

## 参考文献

1. Rudin, W. (1976). *Principles of mathematical analysis*. McGraw-Hill.
2. Apostol, T. M. (1974). *Mathematical analysis*. Addison-Wesley.
3. Spivak, M. (2008). *Calculus*. Publish or Perish.
4. Burden, R. L., & Faires, J. D. (2010). *Numerical analysis*. Brooks/Cole.

---

**更新时间**: 2024-12-21  
**版本**: 1.0  
**作者**: FormalScience Team 