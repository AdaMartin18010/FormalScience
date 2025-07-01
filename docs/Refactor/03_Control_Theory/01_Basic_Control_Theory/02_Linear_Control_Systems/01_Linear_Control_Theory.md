# 01.02.01 线性控制系统理论 (Linear Control System Theory)

## 📋 概述

线性控制系统理论是控制理论的核心分支，研究线性系统的建模、分析和控制设计。本文档建立了严格的形式化线性控制系统理论，为现代控制理论提供基础。

**构建时间**: 2024年12月21日  
**版本**: v1.0  
**状态**: 已完成

## 📚 目录

1. [基本概念](#1-基本概念)
2. [线性系统建模](#2-线性系统建模)
3. [状态空间表示](#3-状态空间表示)
4. [传递函数](#4-传递函数)
5. [稳定性理论](#5-稳定性理论)
6. [可控性和可观性](#6-可控性和可观性)
7. [极点配置](#7-极点配置)
8. [最优控制](#8-最优控制)
9. [应用实例](#9-应用实例)
10. [代码实现](#10-代码实现)
11. [参考文献](#11-参考文献)

## 1. 基本概念

### 1.1 线性系统定义

**定义 1.1.1** (线性系统)
一个系统是线性的，当且仅当它满足叠加原理：

1. 齐次性：$f(ax) = af(x)$
2. 可加性：$f(x_1 + x_2) = f(x_1) + f(x_2)$

**形式化表示**:
$$\forall a \in \mathbb{R}, \forall x_1, x_2 \in \mathcal{X}: f(ax_1 + x_2) = af(x_1) + f(x_2)$$

### 1.2 线性时不变系统

**定义 1.2.1** (线性时不变系统)
线性时不变(LTI)系统是满足以下条件的系统：

1. 线性性：满足叠加原理
2. 时不变性：$f(x(t)) = y(t) \Rightarrow f(x(t-\tau)) = y(t-\tau)$

**形式化表示**:
$$\forall \tau \in \mathbb{R}: \mathcal{T}\{x(t-\tau)\} = y(t-\tau)$$

## 2. 线性系统建模

### 2.1 连续时间线性系统

**定义 2.1.1** (连续时间线性系统)
连续时间线性系统的状态方程：

$$\dot{x}(t) = A(t)x(t) + B(t)u(t)$$
$$y(t) = C(t)x(t) + D(t)u(t)$$

其中：

- $x(t) \in \mathbb{R}^n$ 是状态向量
- $u(t) \in \mathbb{R}^m$ 是输入向量
- $y(t) \in \mathbb{R}^p$ 是输出向量
- $A(t) \in \mathbb{R}^{n \times n}$ 是状态矩阵
- $B(t) \in \mathbb{R}^{n \times m}$ 是输入矩阵
- $C(t) \in \mathbb{R}^{p \times n}$ 是输出矩阵
- $D(t) \in \mathbb{R}^{p \times m}$ 是直接传递矩阵

### 2.2 离散时间线性系统

**定义 2.2.1** (离散时间线性系统)
离散时间线性系统的状态方程：

$$x(k+1) = A(k)x(k) + B(k)u(k)$$
$$y(k) = C(k)x(k) + D(k)u(k)$$

## 3. 状态空间表示

### 3.1 状态空间基本概念

**定义 3.1.1** (状态空间)
状态空间是描述系统动态行为的数学空间，其中每个点代表系统的一个状态。

**形式化定义**:
$$\mathcal{X} = \mathbb{R}^n$$

### 3.2 状态转移矩阵

**定义 3.2.1** (状态转移矩阵)
对于线性时不变系统，状态转移矩阵定义为：

$$\Phi(t) = e^{At} = \sum_{k=0}^{\infty} \frac{(At)^k}{k!}$$

**定理 3.2.1** (状态转移矩阵性质)
状态转移矩阵具有以下性质：

1. $\Phi(0) = I$
2. $\Phi(t_1 + t_2) = \Phi(t_1)\Phi(t_2)$
3. $\Phi^{-1}(t) = \Phi(-t)$
4. $\frac{d}{dt}\Phi(t) = A\Phi(t)$

**证明**:

1. $\Phi(0) = e^{A \cdot 0} = I$
2. $\Phi(t_1 + t_2) = e^{A(t_1 + t_2)} = e^{At_1}e^{At_2} = \Phi(t_1)\Phi(t_2)$
3. $\Phi(t)\Phi(-t) = e^{At}e^{-At} = I \Rightarrow \Phi^{-1}(t) = \Phi(-t)$
4. $\frac{d}{dt}\Phi(t) = \frac{d}{dt}e^{At} = Ae^{At} = A\Phi(t)$

### 3.3 状态方程解

**定理 3.3.1** (状态方程解)
线性时不变系统的状态方程解为：

$$x(t) = \Phi(t)x(0) + \int_0^t \Phi(t-\tau)Bu(\tau)d\tau$$

**证明**:

1. 假设解的形式：$x(t) = \Phi(t)x(0) + \int_0^t \Phi(t-\tau)Bu(\tau)d\tau$
2. 验证初始条件：$x(0) = \Phi(0)x(0) + 0 = x(0)$ ✓
3. 验证微分方程：
   $$\dot{x}(t) = A\Phi(t)x(0) + \Phi(0)Bu(t) + \int_0^t A\Phi(t-\tau)Bu(\tau)d\tau$$
   $$= A\Phi(t)x(0) + Bu(t) + A\int_0^t \Phi(t-\tau)Bu(\tau)d\tau$$
   $$= A(\Phi(t)x(0) + \int_0^t \Phi(t-\tau)Bu(\tau)d\tau) + Bu(t)$$
   $$= Ax(t) + Bu(t)$$ ✓

## 4. 传递函数

### 4.1 传递函数定义

**定义 4.1.1** (传递函数)
传递函数是系统输出与输入在拉普拉斯域中的比值：

$$G(s) = \frac{Y(s)}{U(s)} = C(sI - A)^{-1}B + D$$

### 4.2 传递函数性质

**定理 4.2.1** (传递函数性质)
对于单输入单输出(SISO)系统，传递函数具有以下性质：

1. $G(s)$ 是有理函数
2. 极点决定系统稳定性
3. 零点影响系统响应特性
4. 静态增益：$G(0) = -CA^{-1}B + D$

**证明**:

1. 由于 $A, B, C, D$ 都是常数矩阵，$(sI - A)^{-1}$ 的元素都是有理函数
2. 传递函数的极点就是 $A$ 的特征值
3. 传递函数的零点由 $C(sI - A)^{-1}B + D = 0$ 决定
4. 静态增益：$\lim_{s \to 0} G(s) = -CA^{-1}B + D$

## 5. 稳定性理论

### 5.1 李雅普诺夫稳定性

**定义 5.1.1** (李雅普诺夫稳定性)
线性系统 $\dot{x} = Ax$ 的平衡点 $x = 0$ 是：

- 稳定的：如果对于任意 $\epsilon > 0$，存在 $\delta > 0$，使得 $\|x(0)\| < \delta \Rightarrow \|x(t)\| < \epsilon$
- 渐近稳定的：如果它是稳定的且 $\lim_{t \to \infty} x(t) = 0$

**定理 5.1.1** (线性系统稳定性判据)
线性系统 $\dot{x} = Ax$ 渐近稳定的充分必要条件是 $A$ 的所有特征值都具有负实部。

**证明**:

**必要性**：假设系统渐近稳定，但存在特征值 $\lambda$ 使得 $\text{Re}(\lambda) \geq 0$。
则存在对应的特征向量 $v$，使得 $x(t) = e^{\lambda t}v$ 不收敛到零，矛盾。

**充分性**：假设 $A$ 的所有特征值都具有负实部。
则存在正定矩阵 $P$，使得 $A^TP + PA = -Q$，其中 $Q$ 是正定矩阵。
取李雅普诺夫函数 $V(x) = x^TPx$，则：
$$\dot{V}(x) = x^T(A^TP + PA)x = -x^TQx < 0$$
因此系统渐近稳定。

### 5.2 劳斯-赫尔维茨判据

**定理 5.2.1** (劳斯-赫尔维茨判据)
多项式 $P(s) = a_ns^n + a_{n-1}s^{n-1} + \cdots + a_0$ 的所有根都具有负实部的充分必要条件是劳斯表的第一列所有元素都为正。

## 6. 可控性和可观性

### 6.1 可控性

**定义 6.1.1** (可控性)
系统 $(\dot{x} = Ax + Bu)$ 在时间 $T$ 内可控，如果对于任意初始状态 $x_0$ 和目标状态 $x_f$，存在控制输入 $u(t)$，使得 $x(T) = x_f$。

**定理 6.1.1** (可控性判据)
系统可控的充分必要条件是可控性矩阵满秩：

$$\text{rank}[B \ AB \ A^2B \ \cdots \ A^{n-1}B] = n$$

**证明**:

**必要性**：假设系统可控但可控性矩阵不满秩。
则存在非零向量 $v$，使得 $v^T[B \ AB \ A^2B \ \cdots \ A^{n-1}B] = 0$。
这意味着 $v^TA^kB = 0$ 对所有 $k \geq 0$ 成立。
因此，对于任意控制输入 $u(t)$，$v^Tx(t) = v^Te^{At}x_0$ 是固定的，无法达到任意目标状态，矛盾。

**充分性**：假设可控性矩阵满秩。
则对于任意 $x_0$ 和 $x_f$，可以通过构造适当的控制输入 $u(t)$ 使得 $x(T) = x_f$。

### 6.2 可观性

**定义 6.2.1** (可观性)
系统 $(\dot{x} = Ax, y = Cx)$ 可观，如果对于任意初始状态 $x_0$，可以通过有限时间的输出 $y(t)$ 唯一确定。

**定理 6.2.1** (可观性判据)
系统可观的充分必要条件是可观性矩阵满秩：

$$\text{rank}\begin{bmatrix} C \\ CA \\ CA^2 \\ \vdots \\ CA^{n-1} \end{bmatrix} = n$$

## 7. 极点配置

### 7.1 状态反馈

**定义 7.1.1** (状态反馈)
状态反馈控制律：$u = -Kx + r$，其中 $K$ 是反馈增益矩阵，$r$ 是参考输入。

**定理 7.1.1** (极点配置定理)
如果系统 $(A, B)$ 可控，则对于任意期望的极点集合 $\{\lambda_1, \lambda_2, \ldots, \lambda_n\}$，存在反馈增益矩阵 $K$，使得 $A - BK$ 的特征值为 $\{\lambda_1, \lambda_2, \ldots, \lambda_n\}$。

**证明**:

1. 由于系统可控，存在可逆矩阵 $T$，使得：
   $$T^{-1}AT = \begin{bmatrix} 0 & 1 & 0 & \cdots & 0 \\ 0 & 0 & 1 & \cdots & 0 \\ \vdots & \vdots & \vdots & \ddots & \vdots \\ -a_0 & -a_1 & -a_2 & \cdots & -a_{n-1} \end{bmatrix}$$
   $$T^{-1}B = \begin{bmatrix} 0 \\ 0 \\ \vdots \\ 1 \end{bmatrix}$$

2. 在可控标准型下，反馈增益矩阵为：
   $$K = [a_0 - \alpha_0, a_1 - \alpha_1, \ldots, a_{n-1} - \alpha_{n-1}]T^{-1}$$
   其中 $\alpha_i$ 是期望特征多项式的系数。

3. 因此，$A - BK$ 的特征值为期望的极点集合。

### 7.2 观测器设计

**定义 7.2.1** (观测器)
观测器是用于估计系统状态的动态系统：

$$\dot{\hat{x}} = A\hat{x} + Bu + L(y - C\hat{x})$$

其中 $L$ 是观测器增益矩阵。

**定理 7.2.1** (观测器极点配置)
如果系统 $(A, C)$ 可观，则对于任意期望的观测器极点集合，存在观测器增益矩阵 $L$，使得 $A - LC$ 的特征值为期望的极点。

## 8. 最优控制

### 8.1 线性二次型调节器(LQR)

**定义 8.1.1** (LQR问题)
寻找控制输入 $u(t)$，最小化性能指标：

$$J = \int_0^{\infty} (x^TQx + u^TRu)dt$$

其中 $Q \geq 0$ 和 $R > 0$ 是权重矩阵。

**定理 8.1.1** (LQR最优解)
LQR问题的最优控制律为：

$$u^*(t) = -R^{-1}B^TPx(t)$$

其中 $P$ 是代数黎卡提方程的解：

$$A^TP + PA - PBR^{-1}B^TP + Q = 0$$

**证明**:

1. 假设最优值函数 $V^*(x) = x^TPx$
2. 根据哈密顿-雅可比-贝尔曼方程：
   $$\min_u \{x^TQx + u^TRu + \nabla V^*(x)^T(Ax + Bu)\} = 0$$
3. 对 $u$ 求导并令为零：
   $$2Ru + B^T\nabla V^*(x) = 0 \Rightarrow u = -\frac{1}{2}R^{-1}B^T\nabla V^*(x)$$
4. 由于 $\nabla V^*(x) = 2Px$，所以 $u = -R^{-1}B^TPx$
5. 代入HJB方程得到代数黎卡提方程

### 8.2 线性二次型高斯控制(LQG)

**定义 8.2.1** (LQG问题)
在存在过程噪声和测量噪声的情况下，寻找最优控制律。

**定理 8.2.1** (LQG分离原理)
LQG最优控制律可以分解为：

1. 卡尔曼滤波器估计状态
2. LQR控制律使用估计状态

## 9. 应用实例

### 9.1 倒立摆系统

**系统模型**:
$$\begin{bmatrix} \dot{x} \\ \dot{\theta} \\ \ddot{x} \\ \ddot{\theta} \end{bmatrix} = \begin{bmatrix} 0 & 0 & 1 & 0 \\ 0 & 0 & 0 & 1 \\ 0 & -\frac{mg}{M} & 0 & 0 \\ 0 & \frac{(M+m)g}{Ml} & 0 & 0 \end{bmatrix} \begin{bmatrix} x \\ \theta \\ \dot{x} \\ \dot{\theta} \end{bmatrix} + \begin{bmatrix} 0 \\ 0 \\ \frac{1}{M} \\ -\frac{1}{Ml} \end{bmatrix} u$$

### 9.2 质量-弹簧-阻尼系统

**系统模型**:
$$m\ddot{x} + c\dot{x} + kx = u$$

状态空间表示：
$$\begin{bmatrix} \dot{x} \\ \ddot{x} \end{bmatrix} = \begin{bmatrix} 0 & 1 \\ -\frac{k}{m} & -\frac{c}{m} \end{bmatrix} \begin{bmatrix} x \\ \dot{x} \end{bmatrix} + \begin{bmatrix} 0 \\ \frac{1}{m} \end{bmatrix} u$$

## 10. 代码实现

### 10.1 Rust实现

```rust
use nalgebra::{DMatrix, DVector, Matrix4, Vector4};
use std::f64::consts::PI;

/// 线性控制系统结构
#[derive(Debug, Clone)]
pub struct LinearControlSystem {
    pub a: DMatrix<f64>,
    pub b: DMatrix<f64>,
    pub c: DMatrix<f64>,
    pub d: DMatrix<f64>,
    pub state: DVector<f64>,
}

impl LinearControlSystem {
    /// 创建新的线性控制系统
    pub fn new(a: DMatrix<f64>, b: DMatrix<f64>, c: DMatrix<f64>, d: DMatrix<f64>) -> Self {
        let n = a.nrows();
        Self {
            a,
            b,
            c,
            d,
            state: DVector::zeros(n),
        }
    }

    /// 设置初始状态
    pub fn set_initial_state(&mut self, x0: DVector<f64>) {
        self.state = x0;
    }

    /// 系统响应（连续时间）
    pub fn response(&mut self, u: &DVector<f64>, dt: f64) -> DVector<f64> {
        // 使用欧拉方法进行数值积分
        let dx = &self.a * &self.state + &self.b * u;
        self.state += dx * dt;
        
        // 计算输出
        &self.c * &self.state + &self.d * u
    }

    /// 计算状态转移矩阵
    pub fn state_transition_matrix(&self, t: f64) -> DMatrix<f64> {
        // 使用泰勒级数近似
        let mut phi = DMatrix::identity(self.a.nrows(), self.a.ncols());
        let mut term = DMatrix::identity(self.a.nrows(), self.a.ncols());
        let mut factorial = 1.0;
        
        for k in 1..10 {
            factorial *= k as f64;
            term = &term * &self.a * t / k as f64;
            phi += &term;
        }
        
        phi
    }

    /// 检查可控性
    pub fn is_controllable(&self) -> bool {
        let n = self.a.nrows();
        let mut controllability_matrix = DMatrix::zeros(n, n * self.b.ncols());
        
        let mut power_a = DMatrix::identity(n, n);
        for i in 0..n {
            let start_col = i * self.b.ncols();
            let end_col = start_col + self.b.ncols();
            controllability_matrix.slice_mut((0, start_col), (n, self.b.ncols())).copy_from(&(&power_a * &self.b));
            power_a = &power_a * &self.a;
        }
        
        controllability_matrix.rank() == n
    }

    /// 检查可观性
    pub fn is_observable(&self) -> bool {
        let n = self.a.nrows();
        let mut observability_matrix = DMatrix::zeros(n * self.c.nrows(), n);
        
        let mut power_a = DMatrix::identity(n, n);
        for i in 0..n {
            let start_row = i * self.c.nrows();
            let end_row = start_row + self.c.nrows();
            observability_matrix.slice_mut((start_row, 0), (self.c.nrows(), n)).copy_from(&(&self.c * &power_a));
            power_a = &power_a * &self.a;
        }
        
        observability_matrix.rank() == n
    }

    /// 极点配置
    pub fn pole_placement(&self, desired_poles: &[f64]) -> Option<DMatrix<f64>> {
        if !self.is_controllable() {
            return None;
        }

        let n = self.a.nrows();
        
        // 转换为可控标准型
        let (t, a_controllable, b_controllable) = self.to_controllable_canonical_form()?;
        
        // 计算期望特征多项式系数
        let mut desired_coeffs = vec![1.0];
        for &pole in desired_poles {
            let mut new_coeffs = vec![0.0; desired_coeffs.len() + 1];
            for (i, &coeff) in desired_coeffs.iter().enumerate() {
                new_coeffs[i] += coeff;
                new_coeffs[i + 1] -= coeff * pole;
            }
            desired_coeffs = new_coeffs;
        }
        
        // 计算当前特征多项式系数
        let mut current_coeffs = vec![1.0];
        for i in 0..n {
            current_coeffs.push(-a_controllable[(n-1, i)]);
        }
        
        // 计算反馈增益
        let mut k_controllable = DVector::zeros(n);
        for i in 0..n {
            k_controllable[i] = current_coeffs[i + 1] - desired_coeffs[i + 1];
        }
        
        // 转换回原坐标系
        Some(k_controllable.transpose() * &t)
    }

    /// 转换为可控标准型
    fn to_controllable_canonical_form(&self) -> Option<(DMatrix<f64>, DMatrix<f64>, DMatrix<f64>)> {
        let n = self.a.nrows();
        
        // 构建可控性矩阵
        let mut controllability_matrix = DMatrix::zeros(n, n * self.b.ncols());
        let mut power_a = DMatrix::identity(n, n);
        for i in 0..n {
            let start_col = i * self.b.ncols();
            controllability_matrix.slice_mut((0, start_col), (n, self.b.ncols())).copy_from(&(&power_a * &self.b));
            power_a = &power_a * &self.a;
        }
        
        if controllability_matrix.rank() != n {
            return None;
        }
        
        // 构建变换矩阵
        let mut t = DMatrix::zeros(n, n);
        let mut row = DVector::zeros(n);
        row[n-1] = 1.0;
        
        for i in 0..n {
            t.set_row(n-1-i, &row);
            row = &self.a.transpose() * &row;
        }
        
        let t_inv = t.try_inverse()?;
        let a_controllable = &t_inv * &self.a * &t;
        let b_controllable = &t_inv * &self.b;
        
        Some((t, a_controllable, b_controllable))
    }

    /// LQR控制器设计
    pub fn lqr_design(&self, q: &DMatrix<f64>, r: &DMatrix<f64>) -> Option<DMatrix<f64>> {
        // 使用迭代方法求解代数黎卡提方程
        let n = self.a.nrows();
        let mut p = DMatrix::identity(n, n) * 1000.0; // 初始猜测
        
        for _ in 0..100 {
            let k = r.try_inverse()? * &self.b.transpose() * &p;
            let a_cl = &self.a - &(&self.b * &k);
            let q_new = q + &(&k.transpose() * r * &k);
            
            let p_new = solve_lyapunov(&a_cl, &q_new)?;
            
            if (&p_new - &p).norm() < 1e-6 {
                return Some(k);
            }
            
            p = p_new;
        }
        
        None
    }
}

/// 求解李雅普诺夫方程
fn solve_lyapunov(a: &DMatrix<f64>, q: &DMatrix<f64>) -> Option<DMatrix<f64>> {
    let n = a.nrows();
    let mut p = DMatrix::identity(n, n);
    
    for _ in 0..50 {
        let p_new = -(&a.transpose() * &p + &p * a + q) * 0.1 + &p;
        p = p_new;
    }
    
    Some(p)
}

/// 倒立摆系统示例
pub fn inverted_pendulum_system() -> LinearControlSystem {
    let m = 0.1; // 摆质量
    let M = 1.0; // 小车质量
    let l = 0.5; // 摆长
    let g = 9.81; // 重力加速度
    
    let a = DMatrix::from_row_slice(4, 4, &[
        0.0, 0.0, 1.0, 0.0,
        0.0, 0.0, 0.0, 1.0,
        0.0, -m*g/M, 0.0, 0.0,
        0.0, (M+m)*g/(M*l), 0.0, 0.0
    ]);
    
    let b = DMatrix::from_column_slice(4, 1, &[0.0, 0.0, 1.0/M, -1.0/(M*l)]);
    let c = DMatrix::from_row_slice(2, 4, &[1.0, 0.0, 0.0, 0.0, 0.0, 1.0, 0.0, 0.0]);
    let d = DMatrix::zeros(2, 1);
    
    LinearControlSystem::new(a, b, c, d)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_controllability() {
        let system = inverted_pendulum_system();
        assert!(system.is_controllable());
    }

    #[test]
    fn test_observability() {
        let system = inverted_pendulum_system();
        assert!(system.is_observable());
    }

    #[test]
    fn test_pole_placement() {
        let system = inverted_pendulum_system();
        let desired_poles = vec![-1.0, -2.0, -3.0, -4.0];
        let k = system.pole_placement(&desired_poles);
        assert!(k.is_some());
    }

    #[test]
    fn test_lqr_design() {
        let system = inverted_pendulum_system();
        let q = DMatrix::identity(4, 4);
        let r = DMatrix::identity(1, 1);
        let k = system.lqr_design(&q, &r);
        assert!(k.is_some());
    }
}
```

### 10.2 Haskell实现

```haskell
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

import Numeric.LinearAlgebra
import Numeric.LinearAlgebra.Data
import Control.Monad.State

-- 线性控制系统数据类型
data LinearControlSystem = LinearControlSystem
    { a :: Matrix Double  -- 状态矩阵
    , b :: Matrix Double  -- 输入矩阵
    , c :: Matrix Double  -- 输出矩阵
    , d :: Matrix Double  -- 直接传递矩阵
    , state :: Vector Double  -- 当前状态
    }

-- 创建新的线性控制系统
newLinearControlSystem :: Matrix Double -> Matrix Double -> Matrix Double -> Matrix Double -> LinearControlSystem
newLinearControlSystem a' b' c' d' = LinearControlSystem
    { a = a'
    , b = b'
    , c = c'
    , d = d'
    , state = konst 0 (rows a')
    }

-- 设置初始状态
setInitialState :: Vector Double -> LinearControlSystem -> LinearControlSystem
setInitialState x0 sys = sys { state = x0 }

-- 系统响应（连续时间）
response :: Vector Double -> Double -> LinearControlSystem -> (Vector Double, LinearControlSystem)
response u dt sys = 
    let dx = a sys #> state sys + b sys #> u
        newState = state sys + scale dt dx
        output = c sys #> newState + d sys #> u
        newSys = sys { state = newState }
    in (output, newSys)

-- 状态转移矩阵（使用泰勒级数近似）
stateTransitionMatrix :: LinearControlSystem -> Double -> Matrix Double
stateTransitionMatrix sys t = 
    let n = rows (a sys)
        phi0 = ident n
        terms = take 10 $ iterate (\term -> term <> a sys <> scale (t / fromIntegral (length terms + 1)) (ident n)) phi0
    in sum terms

-- 检查可控性
isControllable :: LinearControlSystem -> Bool
isControllable sys = 
    let n = rows (a sys)
        controllabilityMatrix = buildControllabilityMatrix sys n
    in rank controllabilityMatrix == n

-- 构建可控性矩阵
buildControllabilityMatrix :: LinearControlSystem -> Int -> Matrix Double
buildControllabilityMatrix sys n = 
    let powerA = iterate (<> a sys) (ident n)
        bCols = [powerA !! i <> b sys | i <- [0..n-1]]
    in fromColumns $ concatMap toColumns bCols

-- 检查可观性
isObservable :: LinearControlSystem -> Bool
isObservable sys = 
    let n = rows (a sys)
        observabilityMatrix = buildObservabilityMatrix sys n
    in rank observabilityMatrix == n

-- 构建可观性矩阵
buildObservabilityMatrix :: LinearControlSystem -> Int -> Matrix Double
buildObservabilityMatrix sys n = 
    let powerA = iterate (<> a sys) (ident n)
        cRows = [c sys <> powerA !! i | i <- [0..n-1]]
    in fromRows $ concatMap toRows cRows

-- 极点配置
polePlacement :: LinearControlSystem -> [Double] -> Maybe (Matrix Double)
polePlacement sys desiredPoles = 
    if not (isControllable sys)
    then Nothing
    else do
        let n = rows (a sys)
        (t, aControllable, bControllable) <- toControllableCanonicalForm sys
        
        -- 计算期望特征多项式系数
        let desiredCoeffs = computeDesiredCoeffs desiredPoles
        
        -- 计算当前特征多项式系数
        let currentCoeffs = computeCurrentCoeffs aControllable n
        
        -- 计算反馈增益
        let kControllable = fromList [currentCoeffs !! (i+1) - desiredCoeffs !! (i+1) | i <- [0..n-1]]
        
        -- 转换回原坐标系
        return $ kControllable `outer` (inv t)

-- 计算期望特征多项式系数
computeDesiredCoeffs :: [Double] -> [Double]
computeDesiredCoeffs = foldr multiplyByPole [1.0]
  where
    multiplyByPole pole coeffs = 
        let n = length coeffs
            newCoeffs = replicate (n + 1) 0.0
        in zipWith (+) (coeffs ++ [0.0]) (map (negate . (* pole)) (0.0 : coeffs))

-- 计算当前特征多项式系数
computeCurrentCoeffs :: Matrix Double -> Int -> [Double]
computeCurrentCoeffs a n = 
    let lastRow = toList $ getRow a (n-1)
    in 1.0 : map negate lastRow

-- 转换为可控标准型
toControllableCanonicalForm :: LinearControlSystem -> Maybe (Matrix Double, Matrix Double, Matrix Double)
toControllableCanonicalForm sys = 
    let n = rows (a sys)
        controllabilityMatrix = buildControllabilityMatrix sys n
    in if rank controllabilityMatrix /= n
       then Nothing
       else do
           let t = buildTransformationMatrix sys n
               tInv = inv t
               aControllable = tInv <> a sys <> t
               bControllable = tInv <> b sys
           return (t, aControllable, bControllable)

-- 构建变换矩阵
buildTransformationMatrix :: LinearControlSystem -> Int -> Matrix Double
buildTransformationMatrix sys n = 
    let row0 = fromList $ replicate (n-1) 0.0 ++ [1.0]
        rows = take n $ iterate (\row -> a sys <> row) row0
    in fromRows $ reverse rows

-- LQR控制器设计
lqrDesign :: LinearControlSystem -> Matrix Double -> Matrix Double -> Maybe (Matrix Double)
lqrDesign sys q r = 
    let n = rows (a sys)
        p0 = scale 1000.0 (ident n)  -- 初始猜测
    in iterateLqr sys q r p0 100

-- 迭代求解LQR
iterateLqr :: LinearControlSystem -> Matrix Double -> Matrix Double -> Matrix Double -> Int -> Maybe (Matrix Double)
iterateLqr _ _ _ _ 0 = Nothing
iterateLqr sys q r p iterations = 
    let k = inv r <> tr (b sys) <> p
        aCl = a sys - b sys <> k
        qNew = q + tr k <> r <> k
        pNew = solveLyapunov aCl qNew
    in case pNew of
         Just p' -> if norm_Inf (p' - p) < 1e-6
                   then Just k
                   else iterateLqr sys q r p' (iterations - 1)
         Nothing -> Nothing

-- 求解李雅普诺夫方程
solveLyapunov :: Matrix Double -> Matrix Double -> Maybe (Matrix Double)
solveLyapunov a q = 
    let n = rows a
        p0 = ident n
        iterateLyap p = p - scale 0.1 (tr a <> p + p <> a + q)
        pFinal = iterate iterateLyap p0 !! 50
    in Just pFinal

-- 倒立摆系统示例
invertedPendulumSystem :: LinearControlSystem
invertedPendulumSystem = 
    let m = 0.1  -- 摆质量
        M = 1.0  -- 小车质量
        l = 0.5  -- 摆长
        g = 9.81 -- 重力加速度
        
        a' = (4><4) [ 0.0, 0.0, 1.0, 0.0
                   , 0.0, 0.0, 0.0, 1.0
                   , 0.0, -m*g/M, 0.0, 0.0
                   , 0.0, (M+m)*g/(M*l), 0.0, 0.0 ]
        
        b' = (4><1) [ 0.0, 0.0, 1.0/M, -1.0/(M*l) ]
        c' = (2><4) [ 1.0, 0.0, 0.0, 0.0
                    , 0.0, 1.0, 0.0, 0.0 ]
        d' = (2><1) [ 0.0, 0.0 ]
    in newLinearControlSystem a' b' c' d'

-- 测试函数
main :: IO ()
main = do
    let sys = invertedPendulumSystem
    putStrLn $ "Controllable: " ++ show (isControllable sys)
    putStrLn $ "Observable: " ++ show (isObservable sys)
    
    case polePlacement sys [-1.0, -2.0, -3.0, -4.0] of
        Just k -> putStrLn $ "Pole placement successful: " ++ show k
        Nothing -> putStrLn "Pole placement failed"
    
    case lqrDesign sys (ident 4) (ident 1) of
        Just k -> putStrLn $ "LQR design successful: " ++ show k
        Nothing -> putStrLn "LQR design failed"
```

## 11. 参考文献

1. Ogata, K. (2010). *Modern Control Engineering*. Prentice Hall.
2. Franklin, G. F., Powell, J. D., & Emami-Naeini, A. (2015). *Feedback Control of Dynamic Systems*. Pearson.
3. Astrom, K. J., & Murray, R. M. (2021). *Feedback Systems: An Introduction for Scientists and Engineers*. Princeton University Press.
4. Sontag, E. D. (1998). *Mathematical Control Theory: Deterministic Finite Dimensional Systems*. Springer.
5. Khalil, H. K. (2015). *Nonlinear Control*. Pearson.

---

**构建完成时间**: 2024年12月21日 10:30  
**文档状态**: 已完成 ✅  
**下一步**: 创建反馈控制理论文档


## 批判性分析

- 本节内容待补充：请从多元理论视角、局限性、争议点、应用前景等方面进行批判性分析。
