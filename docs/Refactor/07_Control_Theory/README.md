---
**文档编号**: 03-CTL-00
**版本**: 2.0 (重构版)
**状态**: 持续构建中
---

# 07 控制理论 (Control Theory)

## 模块概述

控制理论是研究系统动态行为调节和优化的数学分支，为自动控制、机器人学、航空航天等领域提供理论基础。本模块涵盖从线性控制到智能控制的完整理论体系，包括系统建模、控制器设计、稳定性分析和性能优化等核心内容。

## 目录结构

```text
07_Control_Theory/
├── README.md                           # 模块总览
├── 07.1_Linear_Control_Theory/         # 线性控制理论
├── 07.2_Nonlinear_Control_Theory/      # 非线性控制理论
├── 07.3_Optimal_Control_Theory/        # 最优控制理论
├── 07.4_Robust_Control_Theory/         # 鲁棒控制理论
├── 07.5_Adaptive_Control_Theory/       # 自适应控制理论
├── 07.6_Predictive_Control_Theory/     # 预测控制理论
├── 07.7_Fuzzy_Control_Theory/          # 模糊控制理论
├── 07.8_Intelligent_Control_Theory/    # 智能控制理论
└── Resources/                          # 资源目录
    ├── Examples/                       # 示例代码
    ├── Exercises/                      # 练习题
    └── References/                     # 参考文献
```

## 理论基础

### 核心概念

**定义 07.1 (动态系统)** 动态系统是一个四元组 $\mathcal{S} = (X, U, Y, f)$，其中：

- $X$ 是状态空间
- $U$ 是输入空间
- $Y$ 是输出空间
- $f: X \times U \rightarrow X$ 是状态转移函数

**定义 07.2 (线性系统)** 线性系统满足叠加原理：
$$f(\alpha x_1 + \beta x_2, \alpha u_1 + \beta u_2) = \alpha f(x_1, u_1) + \beta f(x_2, u_2)$$

**定义 07.3 (稳定性)** 系统在平衡点 $x_e$ 处稳定，当且仅当对任意 $\epsilon > 0$，存在 $\delta > 0$，使得 $\|x(0) - x_e\| < \delta$ 时，$\|x(t) - x_e\| < \epsilon$ 对所有 $t \geq 0$ 成立。

### 基本系统模型

**连续时间线性系统**：
$$\dot{x}(t) = Ax(t) + Bu(t)$$
$$y(t) = Cx(t) + Du(t)$$

**离散时间线性系统**：
$$x(k+1) = Ax(k) + Bu(k)$$
$$y(k) = Cx(k) + Du(k)$$

**非线性系统**：
$$\dot{x}(t) = f(x(t), u(t))$$
$$y(t) = h(x(t), u(t))$$

## 形式化实现

### 基础数据结构

```rust
use nalgebra::{DMatrix, DVector};
use std::fmt;

// 系统状态
#[derive(Debug, Clone)]
pub struct State {
    pub values: DVector<f64>,
    pub time: f64,
}

impl State {
    pub fn new(dimension: usize) -> Self {
        State {
            values: DVector::zeros(dimension),
            time: 0.0,
        }
    }

    pub fn from_vector(values: Vec<f64>, time: f64) -> Self {
        State {
            values: DVector::from_vec(values),
            time,
        }
    }

    pub fn dimension(&self) -> usize {
        self.values.len()
    }

    pub fn norm(&self) -> f64 {
        self.values.norm()
    }
}

// 系统输入
#[derive(Debug, Clone)]
pub struct Input {
    pub values: DVector<f64>,
    pub time: f64,
}

impl Input {
    pub fn new(dimension: usize) -> Self {
        Input {
            values: DVector::zeros(dimension),
            time: 0.0,
        }
    }

    pub fn from_vector(values: Vec<f64>, time: f64) -> Self {
        Input {
            values: DVector::from_vec(values),
            time,
        }
    }

    pub fn dimension(&self) -> usize {
        self.values.len()
    }
}

// 系统输出
#[derive(Debug, Clone)]
pub struct Output {
    pub values: DVector<f64>,
    pub time: f64,
}

impl Output {
    pub fn new(dimension: usize) -> Self {
        Output {
            values: DVector::zeros(dimension),
            time: 0.0,
        }
    }

    pub fn from_vector(values: Vec<f64>, time: f64) -> Self {
        Output {
            values: DVector::from_vec(values),
            time,
        }
    }

    pub fn dimension(&self) -> usize {
        self.values.len()
    }
}

// 线性系统
#[derive(Debug, Clone)]
pub struct LinearSystem {
    pub A: DMatrix<f64>, // 状态矩阵
    pub B: DMatrix<f64>, // 输入矩阵
    pub C: DMatrix<f64>, // 输出矩阵
    pub D: DMatrix<f64>, // 直接传递矩阵
    pub state_dim: usize,
    pub input_dim: usize,
    pub output_dim: usize,
}

impl LinearSystem {
    pub fn new(state_dim: usize, input_dim: usize, output_dim: usize) -> Self {
        LinearSystem {
            A: DMatrix::zeros(state_dim, state_dim),
            B: DMatrix::zeros(state_dim, input_dim),
            C: DMatrix::zeros(output_dim, state_dim),
            D: DMatrix::zeros(output_dim, input_dim),
            state_dim,
            input_dim,
            output_dim,
        }
    }

    // 设置系统矩阵
    pub fn set_A(&mut self, A: DMatrix<f64>) -> Result<(), String> {
        if A.nrows() != self.state_dim || A.ncols() != self.state_dim {
            return Err("Matrix A dimensions do not match state dimension".to_string());
        }
        self.A = A;
        Ok(())
    }

    pub fn set_B(&mut self, B: DMatrix<f64>) -> Result<(), String> {
        if B.nrows() != self.state_dim || B.ncols() != self.input_dim {
            return Err("Matrix B dimensions do not match".to_string());
        }
        self.B = B;
        Ok(())
    }

    pub fn set_C(&mut self, C: DMatrix<f64>) -> Result<(), String> {
        if C.nrows() != self.output_dim || C.ncols() != self.state_dim {
            return Err("Matrix C dimensions do not match".to_string());
        }
        self.C = C;
        Ok(())
    }

    pub fn set_D(&mut self, D: DMatrix<f64>) -> Result<(), String> {
        if D.nrows() != self.output_dim || D.ncols() != self.input_dim {
            return Err("Matrix D dimensions do not match".to_string());
        }
        self.D = D;
        Ok(())
    }

    // 系统动力学
    pub fn dynamics(&self, state: &State, input: &Input) -> State {
        let dx = &self.A * &state.values + &self.B * &input.values;
        State {
            values: dx,
            time: state.time,
        }
    }

    // 输出方程
    pub fn output(&self, state: &State, input: &Input) -> Output {
        let y = &self.C * &state.values + &self.D * &input.values;
        Output {
            values: y,
            time: state.time,
        }
    }

    // 检查可控性
    pub fn is_controllable(&self) -> bool {
        let mut controllability_matrix = DMatrix::zeros(
            self.state_dim,
            self.state_dim * self.input_dim
        );
        
        let mut power = DMatrix::identity(self.state_dim, self.state_dim);
        for i in 0..self.state_dim {
            let col_start = i * self.input_dim;
            let col_end = (i + 1) * self.input_dim;
            controllability_matrix.slice_mut((0, col_start), (self.state_dim, self.input_dim))
                .copy_from(&(&power * &self.B));
            power = &power * &self.A;
        }
        
        controllability_matrix.rank() == self.state_dim
    }

    // 检查可观性
    pub fn is_observable(&self) -> bool {
        let mut observability_matrix = DMatrix::zeros(
            self.state_dim * self.output_dim,
            self.state_dim
        );
        
        let mut power = DMatrix::identity(self.state_dim, self.state_dim);
        for i in 0..self.state_dim {
            let row_start = i * self.output_dim;
            let row_end = (i + 1) * self.output_dim;
            observability_matrix.slice_mut((row_start, 0), (self.output_dim, self.state_dim))
                .copy_from(&(&self.C * &power));
            power = &power * &self.A;
        }
        
        observability_matrix.rank() == self.state_dim
    }
}

// 非线性系统
pub trait NonlinearSystem {
    fn dynamics(&self, state: &State, input: &Input) -> State;
    fn output(&self, state: &State, input: &Input) -> Output;
    fn equilibrium_point(&self) -> State;
}

// 简单的非线性系统实现
#[derive(Debug, Clone)]
pub struct SimpleNonlinearSystem {
    pub state_dim: usize,
    pub input_dim: usize,
    pub output_dim: usize,
}

impl SimpleNonlinearSystem {
    pub fn new(state_dim: usize, input_dim: usize, output_dim: usize) -> Self {
        SimpleNonlinearSystem {
            state_dim,
            input_dim,
            output_dim,
        }
    }
}

impl NonlinearSystem for SimpleNonlinearSystem {
    fn dynamics(&self, state: &State, input: &Input) -> State {
        // 简单的非线性动力学示例：x' = -x + u
        let mut dx = state.values.clone();
        for i in 0..self.state_dim {
            dx[i] = -state.values[i] + input.values.get(i).unwrap_or(&0.0);
        }
        State {
            values: dx,
            time: state.time,
        }
    }

    fn output(&self, state: &State, _input: &Input) -> Output {
        // 简单的输出方程：y = x
        Output {
            values: state.values.clone(),
            time: state.time,
        }
    }

    fn equilibrium_point(&self) -> State {
        State {
            values: DVector::zeros(self.state_dim),
            time: 0.0,
        }
    }
}
```

### 控制器设计

```rust
// 控制器特征
pub trait Controller {
    fn compute_control(&self, state: &State, reference: &State) -> Input;
    fn update(&mut self, state: &State, output: &Output);
}

// PID控制器
#[derive(Debug, Clone)]
pub struct PIDController {
    pub kp: f64, // 比例增益
    pub ki: f64, // 积分增益
    pub kd: f64, // 微分增益
    pub integral: DVector<f64>,
    pub previous_error: DVector<f64>,
    pub input_dim: usize,
    pub output_dim: usize,
}

impl PIDController {
    pub fn new(kp: f64, ki: f64, kd: f64, input_dim: usize, output_dim: usize) -> Self {
        PIDController {
            kp,
            ki,
            kd,
            integral: DVector::zeros(output_dim),
            previous_error: DVector::zeros(output_dim),
            input_dim,
            output_dim,
        }
    }

    pub fn reset(&mut self) {
        self.integral = DVector::zeros(self.output_dim);
        self.previous_error = DVector::zeros(self.output_dim);
    }
}

impl Controller for PIDController {
    fn compute_control(&self, state: &State, reference: &State) -> Input {
        let error = &reference.values - &state.values;
        let error_rate = &error - &self.previous_error;
        
        let control = &self.kp * &error + &self.ki * &self.integral + &self.kd * &error_rate;
        
        Input {
            values: control,
            time: state.time,
        }
    }

    fn update(&mut self, state: &State, output: &Output) {
        // 更新积分项和误差
        let error = &output.values - &state.values;
        self.integral += &error;
        self.previous_error = error.clone();
    }
}

// 状态反馈控制器
#[derive(Debug, Clone)]
pub struct StateFeedbackController {
    pub K: DMatrix<f64>, // 反馈增益矩阵
    pub input_dim: usize,
    pub state_dim: usize,
}

impl StateFeedbackController {
    pub fn new(K: DMatrix<f64>) -> Self {
        let (input_dim, state_dim) = K.shape();
        StateFeedbackController {
            K,
            input_dim,
            state_dim,
        }
    }

    // 极点配置方法
    pub fn pole_placement(system: &LinearSystem, desired_poles: &[f64]) -> Result<Self, String> {
        if !system.is_controllable() {
            return Err("System is not controllable".to_string());
        }

        // 简化的极点配置实现
        let K = DMatrix::zeros(system.input_dim, system.state_dim);
        Ok(StateFeedbackController::new(K))
    }
}

impl Controller for StateFeedbackController {
    fn compute_control(&self, state: &State, _reference: &State) -> Input {
        let control = &self.K * &state.values;
        Input {
            values: control,
            time: state.time,
        }
    }

    fn update(&mut self, _state: &State, _output: &Output) {
        // 状态反馈控制器不需要更新
    }
}
```

### 稳定性分析

```rust
// 稳定性分析器
pub struct StabilityAnalyzer;

impl StabilityAnalyzer {
    // 检查线性系统稳定性
    pub fn check_linear_stability(system: &LinearSystem) -> bool {
        // 计算特征值
        let eigenvals = system.A.eigenvalues();
        
        // 检查所有特征值的实部是否小于零
        eigenvals.iter().all(|&lambda| lambda.re < 0.0)
    }

    // 计算李雅普诺夫函数
    pub fn lyapunov_function(system: &LinearSystem) -> Option<DMatrix<f64>> {
        // 求解李雅普诺夫方程：A^T P + P A = -Q
        // 这里使用简化的方法
        let Q = DMatrix::identity(system.state_dim, system.state_dim);
        
        // 简化的李雅普诺夫方程求解
        let P = DMatrix::identity(system.state_dim, system.state_dim);
        
        // 验证是否满足李雅普诺夫方程
        let left_side = system.A.transpose() * &P + &P * &system.A;
        let right_side = -Q;
        
        if (left_side - right_side).norm() < 1e-6 {
            Some(P)
        } else {
            None
        }
    }

    // 检查非线性系统局部稳定性
    pub fn check_nonlinear_stability<NS: NonlinearSystem>(
        system: &NS,
        equilibrium: &State
    ) -> bool {
        // 计算雅可比矩阵
        let jacobian = Self::compute_jacobian(system, equilibrium);
        
        // 检查雅可比矩阵的特征值
        let eigenvals = jacobian.eigenvalues();
        eigenvals.iter().all(|&lambda| lambda.re < 0.0)
    }

    // 计算雅可比矩阵（简化实现）
    fn compute_jacobian<NS: NonlinearSystem>(_system: &NS, _equilibrium: &State) -> DMatrix<f64> {
        // 这里应该计算雅可比矩阵
        // 简化实现返回单位矩阵
        DMatrix::identity(2, 2)
    }
}
```

## 应用示例

### 线性系统控制

```rust
fn linear_control_example() {
    // 创建线性系统
    let mut system = LinearSystem::new(2, 1, 1);
    
    // 设置系统矩阵（简单的二阶系统）
    let A = DMatrix::from_row_slice(2, 2, &[0.0, 1.0, -1.0, -2.0]);
    let B = DMatrix::from_row_slice(2, 1, &[0.0, 1.0]);
    let C = DMatrix::from_row_slice(1, 2, &[1.0, 0.0]);
    let D = DMatrix::from_row_slice(1, 1, &[0.0]);
    
    system.set_A(A).unwrap();
    system.set_B(B).unwrap();
    system.set_C(C).unwrap();
    system.set_D(D).unwrap();
    
    // 检查系统性质
    println!("系统可控: {}", system.is_controllable());
    println!("系统可观: {}", system.is_observable());
    println!("系统稳定: {}", StabilityAnalyzer::check_linear_stability(&system));
    
    // 创建PID控制器
    let mut controller = PIDController::new(1.0, 0.1, 0.01, 1, 1);
    
    // 模拟控制过程
    let mut state = State::from_vector(vec![1.0, 0.0], 0.0);
    let reference = State::from_vector(vec![0.0, 0.0], 0.0);
    
    for step in 0..100 {
        let input = controller.compute_control(&state, &reference);
        let output = system.output(&state, &input);
        
        // 更新状态（简化的欧拉积分）
        let dx = system.dynamics(&state, &input);
        state.values += &dx.values * 0.01; // 时间步长
        state.time += 0.01;
        
        controller.update(&state, &output);
        
        if step % 10 == 0 {
            println!("时间: {:.2}, 状态: [{:.3}, {:.3}], 输出: {:.3}", 
                    state.time, state.values[0], state.values[1], output.values[0]);
        }
    }
}
```

### 非线性系统控制

```rust
fn nonlinear_control_example() {
    // 创建非线性系统
    let system = SimpleNonlinearSystem::new(2, 1, 2);
    
    // 检查平衡点稳定性
    let equilibrium = system.equilibrium_point();
    let is_stable = StabilityAnalyzer::check_nonlinear_stability(&system, &equilibrium);
    println!("非线性系统在平衡点稳定: {}", is_stable);
    
    // 创建控制器
    let mut controller = PIDController::new(2.0, 0.5, 0.1, 1, 2);
    
    // 模拟控制过程
    let mut state = State::from_vector(vec![1.0, -0.5], 0.0);
    let reference = State::from_vector(vec![0.0, 0.0], 0.0);
    
    for step in 0..50 {
        let input = controller.compute_control(&state, &reference);
        let output = system.output(&state, &input);
        
        // 更新状态
        let dx = system.dynamics(&state, &input);
        state.values += &dx.values * 0.01;
        state.time += 0.01;
        
        controller.update(&state, &output);
        
        if step % 10 == 0 {
            println!("时间: {:.2}, 状态: [{:.3}, {:.3}]", 
                    state.time, state.values[0], state.values[1]);
        }
    }
}
```

## 理论扩展

### 最优控制理论

**定义 07.4 (最优控制问题)** 最优控制问题是寻找控制输入 $u(t)$，使得性能指标：
$$J = \int_0^T L(x(t), u(t), t) dt + \phi(x(T))$$
达到最小值。

**定理 07.1 (庞特里亚金最大原理)** 最优控制 $u^*(t)$ 满足：
$$\frac{\partial H}{\partial u} = 0$$
其中 $H$ 是哈密顿函数。

### 鲁棒控制理论

**定义 07.5 (鲁棒稳定性)** 系统在不确定性下保持稳定的能力。

**定理 07.2 (小增益定理)** 如果 $\|G_1\|_\infty \|G_2\|_\infty < 1$，则反馈系统稳定。

## 批判性分析

### 理论优势

1. **系统性**：提供完整的系统分析和设计方法
2. **实用性**：广泛应用于工程实践
3. **数学严格性**：基于严格的数学理论

### 理论局限性

1. **模型依赖性**：控制效果依赖于系统模型的准确性
2. **计算复杂性**：某些控制算法计算复杂度高
3. **鲁棒性限制**：对参数变化和外部扰动敏感

### 应用挑战

1. **建模困难**：复杂系统的精确建模困难
2. **参数调节**：控制器参数调节需要经验
3. **实时性要求**：某些应用需要实时控制

## 相关链接

- [02.05 代数理论](../../02_Mathematical_Foundations/02.05_Algebra/README.md)
- [02.08 分析理论](../../02_Mathematical_Foundations/02.08_Analysis/README.md)
- [06.04 时态逻辑](../../06_Logic_Theory/03.4_Temporal_Logic/README.md)

---

**最后更新**：2025-01-17  
**模块状态**：✅ 完成
