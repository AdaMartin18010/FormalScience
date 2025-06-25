# 01.03.01 反馈控制理论基础 (Feedback Control Theory Basics)

## 📋 概述

反馈控制理论是控制理论的核心，研究如何利用系统输出信息来调节系统行为。本文档建立了严格的形式化反馈控制理论，为现代控制系统的设计和分析提供基础。

**构建时间**: 2024年12月21日  
**版本**: v1.0  
**状态**: 已完成

## 📚 目录

1. [基本概念](#1-基本概念)
2. [反馈控制结构](#2-反馈控制结构)
3. [闭环系统分析](#3-闭环系统分析)
4. [稳定性分析](#4-稳定性分析)
5. [性能分析](#5-性能分析)
6. [鲁棒性分析](#6-鲁棒性分析)
7. [控制器设计](#7-控制器设计)
8. [应用实例](#8-应用实例)
9. [代码实现](#9-代码实现)
10. [参考文献](#10-参考文献)

## 1. 基本概念

### 1.1 反馈控制定义

**定义 1.1.1** (反馈控制)
反馈控制是一种控制策略，通过测量系统输出并将其与期望值比较，产生控制信号来调节系统行为。

**形式化表示**:
$$u(t) = K(e(t)) = K(r(t) - y(t))$$

其中：

- $u(t)$ 是控制输入
- $e(t) = r(t) - y(t)$ 是误差信号
- $r(t)$ 是参考输入
- $y(t)$ 是系统输出
- $K(\cdot)$ 是控制器

### 1.2 反馈控制类型

**定义 1.2.1** (反馈控制类型)
根据反馈信号的不同，反馈控制可分为：

1. **负反馈**: $u(t) = -K(y(t))$
2. **正反馈**: $u(t) = +K(y(t))$
3. **比例反馈**: $u(t) = K_p e(t)$
4. **积分反馈**: $u(t) = K_i \int_0^t e(\tau)d\tau$
5. **微分反馈**: $u(t) = K_d \frac{d}{dt}e(t)$

## 2. 反馈控制结构

### 2.1 基本反馈结构

**定义 2.1.1** (基本反馈结构)
基本反馈控制系统由以下部分组成：

1. **被控对象**: $G(s)$ - 系统传递函数
2. **控制器**: $C(s)$ - 控制器传递函数
3. **传感器**: $H(s)$ - 传感器传递函数
4. **比较器**: 计算误差 $e(t) = r(t) - y(t)$

**系统框图**:

```text
r(t) → [比较器] → e(t) → [C(s)] → u(t) → [G(s)] → y(t)
                    ↑                                    ↓
                    └────────── [H(s)] ←────────────────┘
```

### 2.2 闭环传递函数

**定义 2.2.1** (闭环传递函数)
闭环系统的传递函数定义为：

$$T(s) = \frac{Y(s)}{R(s)} = \frac{G(s)C(s)}{1 + G(s)C(s)H(s)}$$

**定理 2.2.1** (闭环传递函数性质)
闭环传递函数具有以下性质：

1. 如果 $H(s) = 1$，则 $T(s) = \frac{G(s)C(s)}{1 + G(s)C(s)}$
2. 如果 $|G(s)C(s)H(s)| \gg 1$，则 $T(s) \approx \frac{1}{H(s)}$
3. 如果 $|G(s)C(s)H(s)| \ll 1$，则 $T(s) \approx G(s)C(s)$

**证明**:

1. 直接代入 $H(s) = 1$ 得到结果
2. 当 $|G(s)C(s)H(s)| \gg 1$ 时：
   $$T(s) = \frac{G(s)C(s)}{1 + G(s)C(s)H(s)} \approx \frac{G(s)C(s)}{G(s)C(s)H(s)} = \frac{1}{H(s)}$$
3. 当 $|G(s)C(s)H(s)| \ll 1$ 时：
   $$T(s) = \frac{G(s)C(s)}{1 + G(s)C(s)H(s)} \approx \frac{G(s)C(s)}{1} = G(s)C(s)$$

## 3. 闭环系统分析

### 3.1 闭环系统稳定性

**定义 3.1.1** (闭环系统稳定性)
闭环系统稳定，当且仅当闭环传递函数的所有极点都具有负实部。

**定理 3.1.1** (奈奎斯特稳定性判据)
闭环系统稳定的充分必要条件是奈奎斯特图不包围点 $(-1, 0)$。

**证明**:

1. 闭环特征方程为：$1 + G(s)C(s)H(s) = 0$
2. 根据幅角原理，奈奎斯特图包围 $(-1, 0)$ 的次数等于右半平面极点数
3. 系统稳定当且仅当右半平面极点数为零
4. 因此，奈奎斯特图不包围 $(-1, 0)$

### 3.2 闭环系统性能

**定义 3.2.1** (闭环系统性能指标)
闭环系统的性能指标包括：

1. **稳态误差**: $e_{ss} = \lim_{t \to \infty} e(t)$
2. **上升时间**: $t_r$ - 响应从10%到90%的时间
3. **峰值时间**: $t_p$ - 响应达到第一个峰值的时间
4. **超调量**: $M_p = \frac{y_{max} - y_{ss}}{y_{ss}} \times 100\%$
5. **调节时间**: $t_s$ - 响应进入并保持在±5%误差带的时间

**定理 3.2.1** (稳态误差计算)
对于单位阶跃输入，稳态误差为：

$$e_{ss} = \lim_{s \to 0} \frac{1}{1 + G(s)C(s)H(s)}$$

**证明**:

1. 单位阶跃输入的拉普拉斯变换：$R(s) = \frac{1}{s}$
2. 误差传递函数：$E(s) = \frac{1}{1 + G(s)C(s)H(s)}R(s)$
3. 根据终值定理：
   $$e_{ss} = \lim_{s \to 0} sE(s) = \lim_{s \to 0} \frac{1}{1 + G(s)C(s)H(s)}$$

## 4. 稳定性分析

### 4.1 劳斯-赫尔维茨判据

**定理 4.1.1** (劳斯-赫尔维茨判据)
闭环特征方程 $1 + G(s)C(s)H(s) = 0$ 的所有根都具有负实部的充分必要条件是劳斯表的第一列所有元素都为正。

### 4.2 根轨迹分析

**定义 4.2.1** (根轨迹)
根轨迹是系统参数（通常是增益）变化时，闭环极点在复平面上的轨迹。

**根轨迹规则**:

1. **起点**: 根轨迹从开环极点开始
2. **终点**: 根轨迹终止于开环零点或无穷远
3. **分支数**: 根轨迹分支数等于开环极点数
4. **对称性**: 根轨迹关于实轴对称
5. **渐近线**: 当 $K \to \infty$ 时，根轨迹趋于渐近线

**定理 4.2.1** (根轨迹方程)
根轨迹上的点满足：

$$|G(s)C(s)H(s)| = 1$$
$$\angle G(s)C(s)H(s) = (2k + 1)\pi, k = 0, \pm1, \pm2, \ldots$$

## 5. 性能分析

### 5.1 频域性能

**定义 5.1.1** (频域性能指标)
频域性能指标包括：

1. **带宽**: $\omega_b$ - 幅值下降到-3dB的频率
2. **谐振峰值**: $M_r$ - 闭环幅频特性的最大值
3. **谐振频率**: $\omega_r$ - 谐振峰值对应的频率
4. **相位裕度**: $\phi_m$ - 在增益穿越频率处的相位裕度
5. **增益裕度**: $G_m$ - 在相位穿越频率处的增益裕度

**定理 5.1.1** (性能指标关系)
对于二阶系统，性能指标之间的关系为：

$$M_r = \frac{1}{2\zeta\sqrt{1-\zeta^2}}, \quad \zeta < \frac{1}{\sqrt{2}}$$
$$\omega_r = \omega_n\sqrt{1-2\zeta^2}, \quad \zeta < \frac{1}{\sqrt{2}}$$

其中 $\zeta$ 是阻尼比，$\omega_n$ 是自然频率。

### 5.2 时域性能

**定理 5.2.1** (二阶系统时域性能)
对于标准二阶系统 $\frac{\omega_n^2}{s^2 + 2\zeta\omega_n s + \omega_n^2}$：

1. **上升时间**: $t_r = \frac{\pi - \cos^{-1}\zeta}{\omega_n\sqrt{1-\zeta^2}}$
2. **峰值时间**: $t_p = \frac{\pi}{\omega_n\sqrt{1-\zeta^2}}$
3. **超调量**: $M_p = e^{-\frac{\zeta\pi}{\sqrt{1-\zeta^2}}} \times 100\%$
4. **调节时间**: $t_s = \frac{4}{\zeta\omega_n}$ (2%误差带)

## 6. 鲁棒性分析

### 6.1 鲁棒稳定性

**定义 6.1.1** (鲁棒稳定性)
系统在参数摄动下保持稳定的能力称为鲁棒稳定性。

**定理 6.1.1** (小增益定理)
如果 $\|G(s)\|_{\infty} < 1$ 且 $\|\Delta(s)\|_{\infty} < 1$，则闭环系统稳定。

**证明**:

1. 闭环系统特征方程为：$1 + G(s)(1 + \Delta(s)) = 0$
2. 如果 $|G(s)(1 + \Delta(s))| < 1$，则系统稳定
3. 由于 $|\Delta(s)| < 1$，所以 $|1 + \Delta(s)| < 2$
4. 因此，如果 $|G(s)| < \frac{1}{2}$，则系统稳定

### 6.2 鲁棒性能

**定义 6.2.1** (鲁棒性能)
系统在参数摄动下保持期望性能的能力称为鲁棒性能。

**定理 6.2.1** (鲁棒性能条件)
对于性能指标 $J$，鲁棒性能条件为：

$$\|W(s)S(s)\|_{\infty} < 1$$

其中 $W(s)$ 是性能权重函数，$S(s) = \frac{1}{1 + G(s)C(s)}$ 是灵敏度函数。

## 7. 控制器设计

### 7.1 PID控制器

**定义 7.1.1** (PID控制器)
PID控制器的传递函数为：

$$C(s) = K_p + \frac{K_i}{s} + K_d s$$

其中：

- $K_p$ 是比例增益
- $K_i$ 是积分增益
- $K_d$ 是微分增益

**定理 7.1.1** (PID控制器设计)
对于一阶系统 $G(s) = \frac{K}{\tau s + 1}$，PID控制器参数为：

$$K_p = \frac{2\zeta\omega_n\tau - 1}{K}$$
$$K_i = \frac{\omega_n^2\tau}{K}$$
$$K_d = \frac{\tau}{K}$$

其中 $\zeta$ 和 $\omega_n$ 是期望的阻尼比和自然频率。

### 7.2 状态反馈控制器

**定义 7.2.1** (状态反馈控制器)
状态反馈控制律为：

$$u(t) = -Kx(t) + r(t)$$

其中 $K$ 是反馈增益矩阵。

**定理 7.2.1** (状态反馈设计)
如果系统 $(A, B)$ 可控，则可以通过极点配置设计状态反馈控制器。

### 7.3 观测器设计

**定义 7.3.1** (观测器)
观测器用于估计系统状态：

$$\dot{\hat{x}}(t) = A\hat{x}(t) + Bu(t) + L(y(t) - C\hat{x}(t))$$

其中 $L$ 是观测器增益矩阵。

**定理 7.3.1** (观测器设计)
如果系统 $(A, C)$ 可观，则可以通过极点配置设计观测器。

## 8. 应用实例

### 8.1 温度控制系统

**系统模型**:
$$\frac{dT}{dt} = \frac{1}{RC}(T_{in} - T) + \frac{1}{C}u$$

其中：

- $T$ 是温度
- $T_{in}$ 是环境温度
- $u$ 是加热功率
- $R$ 是热阻
- $C$ 是热容

**PID控制器设计**:
$$u(t) = K_p(T_{ref} - T) + K_i\int_0^t(T_{ref} - T)d\tau + K_d\frac{d}{dt}(T_{ref} - T)$$

### 8.2 倒立摆控制系统

**系统模型**:
$$\begin{bmatrix} \dot{x} \\ \dot{\theta} \\ \ddot{x} \\ \ddot{\theta} \end{bmatrix} = \begin{bmatrix} 0 & 0 & 1 & 0 \\ 0 & 0 & 0 & 1 \\ 0 & -\frac{mg}{M} & 0 & 0 \\ 0 & \frac{(M+m)g}{Ml} & 0 & 0 \end{bmatrix} \begin{bmatrix} x \\ \theta \\ \dot{x} \\ \dot{\theta} \end{bmatrix} + \begin{bmatrix} 0 \\ 0 \\ \frac{1}{M} \\ -\frac{1}{Ml} \end{bmatrix} u$$

**状态反馈控制器**:
$$u = -K_1x - K_2\theta - K_3\dot{x} - K_4\dot{\theta}$$

## 9. 代码实现

### 9.1 Rust实现

```rust
use nalgebra::{DMatrix, DVector};
use std::f64::consts::PI;

/// 反馈控制系统结构
#[derive(Debug, Clone)]
pub struct FeedbackControlSystem {
    pub plant: DMatrix<f64>,      // 被控对象传递函数系数
    pub controller: DMatrix<f64>, // 控制器传递函数系数
    pub sensor: DMatrix<f64>,     // 传感器传递函数系数
    pub state: DVector<f64>,      // 系统状态
    pub error: f64,               // 误差信号
    pub output: f64,              // 系统输出
}

impl FeedbackControlSystem {
    /// 创建新的反馈控制系统
    pub fn new(plant: DMatrix<f64>, controller: DMatrix<f64>, sensor: DMatrix<f64>) -> Self {
        let n = plant.nrows();
        Self {
            plant,
            controller,
            sensor,
            state: DVector::zeros(n),
            error: 0.0,
            output: 0.0,
        }
    }

    /// 设置初始状态
    pub fn set_initial_state(&mut self, x0: DVector<f64>) {
        self.state = x0;
    }

    /// 计算闭环传递函数
    pub fn closed_loop_transfer_function(&self) -> DMatrix<f64> {
        let g = &self.plant;
        let c = &self.controller;
        let h = &self.sensor;
        
        // T(s) = G(s)C(s) / (1 + G(s)C(s)H(s))
        let gc = g * c;
        let gch = gc * h;
        let denominator = DMatrix::identity(gch.nrows(), gch.ncols()) + gch;
        
        gc * denominator.try_inverse().unwrap_or_else(|| DMatrix::identity(gc.nrows(), gc.ncols()))
    }

    /// 检查闭环稳定性
    pub fn is_stable(&self) -> bool {
        let closed_loop = self.closed_loop_transfer_function();
        let eigenvalues = closed_loop.eigenvalues();
        
        eigenvalues.iter().all(|&e| e.real < 0.0)
    }

    /// 计算稳态误差
    pub fn steady_state_error(&self, reference: f64) -> f64 {
        let closed_loop = self.closed_loop_transfer_function();
        let dc_gain = closed_loop[(0, 0)]; // 假设SISO系统
        
        reference * (1.0 - dc_gain)
    }

    /// 系统响应
    pub fn response(&mut self, reference: f64, dt: f64) -> f64 {
        // 计算误差
        self.error = reference - self.output;
        
        // 计算控制输入
        let control_input = self.compute_control_input();
        
        // 更新系统状态
        self.update_system_state(control_input, dt);
        
        // 更新输出
        self.output = self.compute_output();
        
        self.output
    }

    /// 计算控制输入
    fn compute_control_input(&self) -> f64 {
        // 简单的比例控制
        let kp = 1.0;
        kp * self.error
    }

    /// 更新系统状态
    fn update_system_state(&mut self, control_input: f64, dt: f64) {
        // 使用欧拉方法进行数值积分
        let dx = &self.plant * &self.state + DVector::from_column_slice(&[control_input]);
        self.state += dx * dt;
    }

    /// 计算输出
    fn compute_output(&self) -> f64 {
        // 假设输出是状态的线性组合
        let c = DVector::from_column_slice(&[1.0, 0.0, 0.0, 0.0]); // 输出矩阵
        c.dot(&self.state)
    }

    /// PID控制器
    pub fn pid_controller(&mut self, reference: f64, dt: f64) -> f64 {
        let kp = 1.0;
        let ki = 0.1;
        let kd = 0.01;
        
        // 计算误差
        let error = reference - self.output;
        
        // 积分项
        static mut INTEGRAL: f64 = 0.0;
        unsafe {
            INTEGRAL += error * dt;
        }
        
        // 微分项
        static mut PREV_ERROR: f64 = 0.0;
        let derivative = unsafe {
            let deriv = (error - PREV_ERROR) / dt;
            PREV_ERROR = error;
            deriv
        };
        
        // PID控制律
        let control_input = kp * error + ki * unsafe { INTEGRAL } + kd * derivative;
        
        control_input
    }

    /// 状态反馈控制器
    pub fn state_feedback_controller(&self, reference: f64) -> f64 {
        let k = DVector::from_column_slice(&[1.0, 2.0, 0.5, 1.0]); // 反馈增益
        let reference_state = DVector::from_column_slice(&[reference, 0.0, 0.0, 0.0]);
        
        k.dot(&(reference_state - &self.state))
    }

    /// 观测器
    pub fn observer(&mut self, measurement: f64, dt: f64) -> DVector<f64> {
        let l = DVector::from_column_slice(&[1.0, 1.0, 1.0, 1.0]); // 观测器增益
        let c = DVector::from_column_slice(&[1.0, 0.0, 0.0, 0.0]); // 输出矩阵
        
        // 观测器方程
        let innovation = measurement - c.dot(&self.state);
        let dx = &self.plant * &self.state + &l * innovation;
        self.state += dx * dt;
        
        self.state.clone()
    }

    /// 根轨迹分析
    pub fn root_locus(&self, k_range: &[f64]) -> Vec<(f64, f64)> {
        let mut roots = Vec::new();
        
        for &k in k_range {
            let closed_loop = self.closed_loop_with_gain(k);
            let eigenvalues = closed_loop.eigenvalues();
            
            for &eigenvalue in eigenvalues.iter() {
                roots.push((eigenvalue.real, eigenvalue.imaginary));
            }
        }
        
        roots
    }

    /// 带增益的闭环系统
    fn closed_loop_with_gain(&self, k: f64) -> DMatrix<f64> {
        let g = &self.plant;
        let c = &self.controller;
        let h = &self.sensor;
        
        let gc = g * c * k;
        let gch = gc * h;
        let denominator = DMatrix::identity(gch.nrows(), gch.ncols()) + gch;
        
        gc * denominator.try_inverse().unwrap_or_else(|| DMatrix::identity(gc.nrows(), gc.ncols()))
    }

    /// 频域分析
    pub fn frequency_response(&self, frequencies: &[f64]) -> Vec<(f64, f64, f64)> {
        let mut response = Vec::new();
        
        for &freq in frequencies {
            let s = complex::Complex::new(0.0, 2.0 * PI * freq);
            let transfer_function = self.evaluate_transfer_function(s);
            
            response.push((
                freq,
                transfer_function.norm(),
                transfer_function.arg()
            ));
        }
        
        response
    }

    /// 评估传递函数
    fn evaluate_transfer_function(&self, s: complex::Complex<f64>) -> complex::Complex<f64> {
        // 简化的传递函数评估
        let g = complex::Complex::new(1.0, 0.0) / (s + complex::Complex::new(1.0, 0.0));
        let c = complex::Complex::new(1.0, 0.0);
        let h = complex::Complex::new(1.0, 0.0);
        
        g * c / (complex::Complex::new(1.0, 0.0) + g * c * h)
    }
}

/// 温度控制系统示例
pub fn temperature_control_system() -> FeedbackControlSystem {
    let plant = DMatrix::from_row_slice(2, 2, &[
        -0.1, 1.0,
        0.0, 0.0
    ]);
    
    let controller = DMatrix::from_row_slice(2, 2, &[
        1.0, 0.0,
        0.0, 1.0
    ]);
    
    let sensor = DMatrix::from_row_slice(1, 1, &[1.0]);
    
    FeedbackControlSystem::new(plant, controller, sensor)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_stability() {
        let system = temperature_control_system();
        assert!(system.is_stable());
    }

    #[test]
    fn test_steady_state_error() {
        let mut system = temperature_control_system();
        let error = system.steady_state_error(100.0);
        assert!(error.abs() < 1e-6);
    }

    #[test]
    fn test_root_locus() {
        let system = temperature_control_system();
        let k_range = vec![0.1, 0.5, 1.0, 2.0, 5.0];
        let roots = system.root_locus(&k_range);
        assert!(!roots.is_empty());
    }
}
```

### 9.2 Haskell实现

```haskell
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

import Numeric.LinearAlgebra
import Numeric.LinearAlgebra.Data
import Control.Monad.State
import Data.Complex

-- 反馈控制系统数据类型
data FeedbackControlSystem = FeedbackControlSystem
    { plant :: Matrix Double      -- 被控对象传递函数系数
    , controller :: Matrix Double -- 控制器传递函数系数
    , sensor :: Matrix Double     -- 传感器传递函数系数
    , state :: Vector Double      -- 系统状态
    , error :: Double             -- 误差信号
    , output :: Double            -- 系统输出
    , integral :: Double          -- 积分项
    , prevError :: Double         -- 前一次误差
    }

-- 创建新的反馈控制系统
newFeedbackControlSystem :: Matrix Double -> Matrix Double -> Matrix Double -> FeedbackControlSystem
newFeedbackControlSystem plant' controller' sensor' = FeedbackControlSystem
    { plant = plant'
    , controller = controller'
    , sensor = sensor'
    , state = konst 0 (rows plant')
    , error = 0.0
    , output = 0.0
    , integral = 0.0
    , prevError = 0.0
    }

-- 设置初始状态
setInitialState :: Vector Double -> FeedbackControlSystem -> FeedbackControlSystem
setInitialState x0 sys = sys { state = x0 }

-- 计算闭环传递函数
closedLoopTransferFunction :: FeedbackControlSystem -> Matrix Double
closedLoopTransferFunction sys = 
    let g = plant sys
        c = controller sys
        h = sensor sys
        gc = g <> c
        gch = gc <> h
        denominator = ident (rows gch) + gch
    in gc <> inv denominator

-- 检查闭环稳定性
isStable :: FeedbackControlSystem -> Bool
isStable sys = 
    let closedLoop = closedLoopTransferFunction sys
        eigenvalues = eigSH closedLoop
    in all (< 0) eigenvalues

-- 计算稳态误差
steadyStateError :: FeedbackControlSystem -> Double -> Double
steadyStateError sys reference = 
    let closedLoop = closedLoopTransferFunction sys
        dcGain = closedLoop @@> (0, 0)  -- 假设SISO系统
    in reference * (1.0 - dcGain)

-- 系统响应
response :: Double -> Double -> FeedbackControlSystem -> (Double, FeedbackControlSystem)
response reference dt sys = 
    let error' = reference - output sys
        controlInput = computeControlInput sys error'
        newState = updateSystemState sys controlInput dt
        newOutput = computeOutput newState
        newSys = sys { state = newState, error = error', output = newOutput }
    in (newOutput, newSys)

-- 计算控制输入
computeControlInput :: FeedbackControlSystem -> Double -> Double
computeControlInput sys error' = 
    let kp = 1.0  -- 比例增益
    in kp * error'

-- 更新系统状态
updateSystemState :: FeedbackControlSystem -> Double -> Double -> Vector Double
updateSystemState sys controlInput dt = 
    let dx = plant sys #> state sys + fromList [controlInput]
    in state sys + scale dt dx

-- 计算输出
computeOutput :: Vector Double -> Double
computeOutput state' = 
    let c = fromList [1.0, 0.0, 0.0, 0.0]  -- 输出矩阵
    in c `dot` state'

-- PID控制器
pidController :: Double -> Double -> FeedbackControlSystem -> (Double, FeedbackControlSystem)
pidController reference dt sys = 
    let kp = 1.0
        ki = 0.1
        kd = 0.01
        error' = reference - output sys
        newIntegral = integral sys + error' * dt
        derivative = (error' - prevError sys) / dt
        controlInput = kp * error' + ki * newIntegral + kd * derivative
        newSys = sys { integral = newIntegral, prevError = error' }
    in (controlInput, newSys)

-- 状态反馈控制器
stateFeedbackController :: Double -> FeedbackControlSystem -> Double
stateFeedbackController reference sys = 
    let k = fromList [1.0, 2.0, 0.5, 1.0]  -- 反馈增益
        referenceState = fromList [reference, 0.0, 0.0, 0.0]
    in k `dot` (referenceState - state sys)

-- 观测器
observer :: Double -> Double -> FeedbackControlSystem -> (Vector Double, FeedbackControlSystem)
observer measurement dt sys = 
    let l = fromList [1.0, 1.0, 1.0, 1.0]  -- 观测器增益
        c = fromList [1.0, 0.0, 0.0, 0.0]  -- 输出矩阵
        innovation = measurement - c `dot` state sys
        dx = plant sys #> state sys + scale innovation l
        newState = state sys + scale dt dx
        newSys = sys { state = newState }
    in (newState, newSys)

-- 根轨迹分析
rootLocus :: FeedbackControlSystem -> [Double] -> [(Double, Double)]
rootLocus sys kRange = 
    concatMap (\k -> 
        let closedLoop = closedLoopWithGain sys k
            eigenvalues = eigSH closedLoop
        in map (\eigenvalue -> (eigenvalue, 0.0)) eigenvalues
    ) kRange

-- 带增益的闭环系统
closedLoopWithGain :: FeedbackControlSystem -> Double -> Matrix Double
closedLoopWithGain sys k = 
    let g = plant sys
        c = controller sys
        h = sensor sys
        gc = g <> c <> scale k (ident (rows g))
        gch = gc <> h
        denominator = ident (rows gch) + gch
    in gc <> inv denominator

-- 频域分析
frequencyResponse :: FeedbackControlSystem -> [Double] -> [(Double, Double, Double)]
frequencyResponse sys frequencies = 
    map (\freq -> 
        let s = 0.0 :+ (2.0 * pi * freq)
            transferFunction = evaluateTransferFunction s
        in (freq, magnitude transferFunction, phase transferFunction)
    ) frequencies

-- 评估传递函数
evaluateTransferFunction :: Complex Double -> Complex Double
evaluateTransferFunction s = 
    let g = 1.0 / (s + 1.0)
        c = 1.0
        h = 1.0
    in g * c / (1.0 + g * c * h)

-- 温度控制系统示例
temperatureControlSystem :: FeedbackControlSystem
temperatureControlSystem = 
    let plant' = (2><2) [ -0.1, 1.0
                        , 0.0, 0.0 ]
        controller' = (2><2) [ 1.0, 0.0
                             , 0.0, 1.0 ]
        sensor' = (1><1) [ 1.0 ]
    in newFeedbackControlSystem plant' controller' sensor'

-- 测试函数
main :: IO ()
main = do
    let sys = temperatureControlSystem
    putStrLn $ "Stable: " ++ show (isStable sys)
    
    let error = steadyStateError sys 100.0
    putStrLn $ "Steady state error: " ++ show error
    
    let kRange = [0.1, 0.5, 1.0, 2.0, 5.0]
    let roots = rootLocus sys kRange
    putStrLn $ "Root locus points: " ++ show (length roots)
    
    let frequencies = [0.1, 0.5, 1.0, 2.0, 5.0]
    let response = frequencyResponse sys frequencies
    putStrLn $ "Frequency response points: " ++ show (length response)
```

## 10. 参考文献

1. Franklin, G. F., Powell, J. D., & Emami-Naeini, A. (2015). *Feedback Control of Dynamic Systems*. Pearson.
2. Ogata, K. (2010). *Modern Control Engineering*. Prentice Hall.
3. Astrom, K. J., & Murray, R. M. (2021). *Feedback Systems: An Introduction for Scientists and Engineers*. Princeton University Press.
4. Skogestad, S., & Postlethwaite, I. (2005). *Multivariable Feedback Control: Analysis and Design*. Wiley.
5. Doyle, J. C., Francis, B. A., & Tannenbaum, A. R. (2013). *Feedback Control Theory*. Dover Publications.

---

**构建完成时间**: 2024年12月21日 11:00  
**文档状态**: 已完成 ✅  
**下一步**: 创建状态空间方法文档
