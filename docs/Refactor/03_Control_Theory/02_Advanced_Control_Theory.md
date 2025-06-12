# 高级控制理论 (Advanced Control Theory)

## 目录

1. [鲁棒控制理论](#1-鲁棒控制理论)
2. [自适应控制理论](#2-自适应控制理论)
3. [非线性控制理论](#3-非线性控制理论)
4. [最优控制理论](#4-最优控制理论)
5. [预测控制理论](#5-预测控制理论)
6. [滑模控制理论](#6-滑模控制理论)
7. [参考文献](#7-参考文献)

## 1. 鲁棒控制理论

### 1.1 不确定性建模

**定义 1.1 (参数不确定性)**
系统参数不确定性模型：
$$\dot{x}(t) = (A + \Delta A)x(t) + (B + \Delta B)u(t)$$
$$y(t) = (C + \Delta C)x(t)$$

其中 $\Delta A, \Delta B, \Delta C$ 是未知但有界的参数摄动。

**定义 1.2 (结构不确定性)**
结构不确定性模型：
$$\dot{x}(t) = Ax(t) + Bu(t) + E_1w(t)$$
$$y(t) = Cx(t) + E_2w(t)$$

其中 $w(t)$ 是外部干扰，$E_1, E_2$ 是干扰分布矩阵。

**定义 1.3 (乘性不确定性)**
乘性不确定性模型：
$$G_p(s) = G(s)(1 + \Delta(s)W(s))$$

其中 $G(s)$ 是标称模型，$\Delta(s)$ 是满足 $\|\Delta\|_\infty \leq 1$ 的不确定性，$W(s)$ 是权重函数。

### 1.2 H∞控制理论

**定义 1.4 (H∞范数)**
传递函数 $G(s)$ 的H∞范数：
$$\|G\|_\infty = \sup_{\omega \in \mathbb{R}} \sigma_{max}(G(j\omega))$$

其中 $\sigma_{max}$ 表示最大奇异值。

**定义 1.5 (H∞控制问题)**
H∞控制问题：设计控制器 $K(s)$ 使得闭环系统稳定且：
$$\|T_{zw}\|_\infty < \gamma$$

其中 $T_{zw}$ 是从干扰 $w$ 到性能输出 $z$ 的闭环传递函数。

**定理 1.1 (H∞控制存在性)**
H∞控制器存在的充分必要条件是存在正定矩阵 $X, Y$ 满足：
$$AX + XA^T + B_1B_1^T + X(\frac{1}{\gamma^2}C_1^TC_1 - C_2^TC_2)X < 0$$
$$A^TY + YA + C_1^TC_1 + Y(\frac{1}{\gamma^2}B_1B_1^T - B_2B_2^T)Y < 0$$
$$X > 0, Y > 0, \rho(XY) < \gamma^2$$

**证明：** 通过Riccati方程：

1. 构造H∞Riccati方程
2. 利用有界实引理
3. 通过线性矩阵不等式求解

**算法 1.1 (H∞控制器设计)**

```haskell
hInfinityController :: LinearSystem -> Double -> Controller
hInfinityController sys gamma = 
  let -- 求解H∞Riccati方程
      x = solveHInfinityRiccati sys gamma
      y = solveHInfinityRiccatiDual sys gamma
      
      -- 构造控制器
      controller = buildHInfinityController sys x y gamma
  in controller

solveHInfinityRiccati :: LinearSystem -> Double -> Matrix Double
solveHInfinityRiccati sys gamma = 
  let a = aMatrix sys
      b1 = b1Matrix sys  -- 干扰输入
      b2 = b2Matrix sys  -- 控制输入
      c1 = c1Matrix sys  -- 性能输出
      c2 = c2Matrix sys  -- 测量输出
      
      -- H∞ Riccati方程
      riccatiEquation x = 
        a `multiply` x + x `multiply` (transpose a) +
        x `multiply` ((1/gamma^2) `scale` (c1 `multiply` (transpose c1))) `multiply` x +
        b1 `multiply` (transpose b1) -
        x `multiply` (c2 `multiply` (transpose c2)) `multiply` x
      
      -- 求解Riccati方程
      x = solveRiccatiEquation riccatiEquation
  in x
```

### 1.3 μ-综合理论

**定义 1.6 (结构奇异值)**
结构奇异值 $\mu_\Delta(M)$：
$$\mu_\Delta(M) = \frac{1}{\min\{\bar{\sigma}(\Delta) : \Delta \in \Delta, \det(I - M\Delta) = 0\}}$$

**定义 1.7 (μ-综合问题)**
μ-综合问题：设计控制器使得：
$$\mu_\Delta(T_{zw}) < 1$$

**定理 1.2 (μ-综合存在性)**
μ-综合控制器存在的充分必要条件是存在标量函数 $\alpha(s)$ 使得：
$$\|W_1T_{zw}W_2\|_\infty < 1$$

其中 $W_1, W_2$ 是适当的权重函数。

## 2. 自适应控制理论

### 2.1 模型参考自适应控制

**定义 2.1 (参考模型)**
参考模型：
$$\dot{x}_m(t) = A_mx_m(t) + B_mr(t)$$
$$y_m(t) = C_mx_m(t)$$

其中 $A_m$ 是稳定的，$(A_m, B_m)$ 可控。

**定义 2.2 (跟踪误差)**
跟踪误差：
$$e(t) = x(t) - x_m(t)$$

**定理 2.1 (模型参考自适应控制)**
如果存在参数矩阵 $\theta^*$ 使得：
$$A + B\theta^{*T} = A_m$$
$$B\theta^{*T} = B_m$$

则自适应控制律：
$$u(t) = \theta^T(t)x(t) + \theta_r^T(t)r(t)$$
$$\dot{\theta}(t) = -\Gamma x(t)e^T(t)PB$$
$$\dot{\theta}_r(t) = -\Gamma r(t)e^T(t)PB$$

使得跟踪误差渐近收敛到零。

**证明：** 通过李雅普诺夫函数：

1. 构造李雅普诺夫函数 $V = e^TPe + \text{tr}(\tilde{\theta}^T\Gamma^{-1}\tilde{\theta})$
2. 计算导数 $\dot{V} = -e^TQe \leq 0$
3. 应用李雅普诺夫稳定性理论

**算法 2.1 (模型参考自适应控制)**

```haskell
modelReferenceAdaptiveControl :: LinearSystem -> ReferenceModel -> Controller
modelReferenceAdaptiveControl sys refModel = 
  let -- 计算理想参数
      idealParams = computeIdealParameters sys refModel
      
      -- 自适应控制律
      adaptiveLaw params error state = 
        let gamma = 0.1  -- 自适应增益
            paramUpdate = gamma `scale` (state `outer` error)
        in params + paramUpdate
      
      -- 控制器
      controller state params reference = 
        params.stateGain `multiply` state + 
        params.referenceGain `multiply` reference
  in AdaptiveController {
    adaptiveLaw = adaptiveLaw,
    controller = controller,
    idealParams = idealParams
  }
```

### 2.2 自校正控制

**定义 2.3 (参数估计)**
参数估计模型：
$$y(k) = \phi^T(k-1)\theta + e(k)$$

其中 $\phi(k-1)$ 是回归向量，$\theta$ 是参数向量，$e(k)$ 是噪声。

**定义 2.4 (递归最小二乘)**
递归最小二乘估计：
$$\hat{\theta}(k) = \hat{\theta}(k-1) + P(k)\phi(k-1)[y(k) - \phi^T(k-1)\hat{\theta}(k-1)]$$
$$P(k) = P(k-1) - \frac{P(k-1)\phi(k-1)\phi^T(k-1)P(k-1)}{1 + \phi^T(k-1)P(k-1)\phi(k-1)}$$

**定理 2.2 (自校正控制收敛性)**
如果系统满足持续激励条件，则参数估计收敛到真值。

**算法 2.2 (自校正控制)**

```haskell
selfTuningControl :: SystemModel -> Controller
selfTuningControl model = 
  let -- 参数估计器
      parameterEstimator = recursiveLeastSquares 0.1
      
      -- 控制器设计
      controllerDesign estimatedParams = 
        polePlacementController estimatedParams
      
      -- 自校正控制
      selfTuningController input output = 
        let estimatedParams = parameterEstimator input output
            controller = controllerDesign estimatedParams
        in controller input
  in SelfTuningController {
    parameterEstimator = parameterEstimator,
    controllerDesign = controllerDesign,
    controller = selfTuningController
  }
```

## 3. 非线性控制理论

### 3.1 反馈线性化

**定义 3.1 (相对度)**
系统 $\dot{x} = f(x) + g(x)u$ 在 $x_0$ 点的相对度 $r$ 是满足：
$$L_gL_f^{r-1}h(x_0) \neq 0$$
的最小整数。

**定义 3.2 (反馈线性化)**
反馈线性化控制律：
$$u = \frac{1}{L_gL_f^{r-1}h(x)}[-L_f^rh(x) + v]$$

其中 $v$ 是新的控制输入。

**定理 3.1 (反馈线性化条件)**
系统可以通过状态反馈线性化的充分必要条件是系统在平衡点附近具有恒定的相对度。

**证明：** 通过坐标变换：

1. 构造新的坐标 $z_i = L_f^{i-1}h(x)$
2. 验证相对度条件
3. 应用反馈线性化控制律

**算法 3.1 (反馈线性化)**

```haskell
feedbackLinearization :: NonlinearSystem -> Controller
feedbackLinearization sys = 
  let -- 计算相对度
      relativeDegree = computeRelativeDegree sys
      
      -- 构造坐标变换
      coordinateTransform = buildCoordinateTransform sys relativeDegree
      
      -- 反馈线性化控制律
      linearizingControl state newInput = 
        let lfrh = lieDerivative sys relativeDegree state
            lgLfr1h = lieDerivative sys (relativeDegree-1) state
            u = (-lfrh + newInput) / lgLfr1h
        in u
  in FeedbackLinearizingController {
    relativeDegree = relativeDegree,
    coordinateTransform = coordinateTransform,
    controlLaw = linearizingControl
  }
```

### 3.2 滑模控制

**定义 3.3 (滑模面)**
滑模面：
$$s(x) = c^Tx = 0$$

其中 $c$ 是滑模面参数向量。

**定义 3.4 (滑模控制)**
滑模控制律：
$$u = u_{eq} + u_{sw}$$

其中 $u_{eq}$ 是等效控制，$u_{sw}$ 是切换控制。

**定理 3.2 (滑模存在性)**
滑模存在的充分条件是：
$$s\dot{s} < 0$$

**证明：** 通过李雅普诺夫函数：

1. 选择 $V = \frac{1}{2}s^2$
2. 计算 $\dot{V} = s\dot{s}$
3. 设计控制律使得 $\dot{V} < 0$

**算法 3.2 (滑模控制)**

```haskell
slidingModeControl :: NonlinearSystem -> Vector Double -> Controller
slidingModeControl sys slidingSurface = 
  let -- 等效控制
      equivalentControl state = 
        let c = slidingSurface
            s = c `dot` state
            ds = c `dot` (systemDynamics sys state)
            ueq = -ds / (c `dot` (controlMatrix sys state))
        in ueq
      
      -- 切换控制
      switchingControl state = 
        let c = slidingSurface
            s = c `dot` state
            k = 1.0  -- 切换增益
            usw = -k * sign s
        in usw
      
      -- 滑模控制律
      slidingModeLaw state = 
        let ueq = equivalentControl state
            usw = switchingControl state
        in ueq + usw
  in SlidingModeController {
    slidingSurface = slidingSurface,
    equivalentControl = equivalentControl,
    switchingControl = switchingControl,
    controlLaw = slidingModeLaw
  }
```

### 3.3 反步法

**定义 3.5 (反步法)**
反步法是一种递归设计方法，通过逐步构造李雅普诺夫函数来设计控制器。

**定理 3.3 (反步法设计)**
对于系统：
$$\dot{x}_1 = f_1(x_1) + g_1(x_1)x_2$$
$$\dot{x}_2 = f_2(x_1, x_2) + g_2(x_1, x_2)u$$

反步法控制律：
$$u = \frac{1}{g_2(x_1, x_2)}[-f_2(x_1, x_2) - \frac{\partial V_1}{\partial x_1}g_1(x_1) - k_2z_2]$$

其中 $z_2 = x_2 - \alpha_1(x_1)$，$\alpha_1(x_1)$ 是虚拟控制律。

**算法 3.3 (反步法控制)**

```haskell
backsteppingControl :: NonlinearSystem -> Controller
backsteppingControl sys = 
  let -- 第一步：设计虚拟控制律
      virtualControl x1 = 
        let k1 = 1.0
            alpha1 = -k1 * x1
        in alpha1
      
      -- 第二步：设计实际控制律
      actualControl x1 x2 = 
        let k2 = 1.0
            z2 = x2 - virtualControl x1
            u = (-systemDynamics2 sys x1 x2 - 
                 partialV1PartialX1 x1 * controlMatrix1 sys x1 - 
                 k2 * z2) / controlMatrix2 sys x1 x2
        in u
  in BacksteppingController {
    virtualControl = virtualControl,
    actualControl = actualControl
  }
```

## 4. 最优控制理论

### 4.1 变分法

**定义 4.1 (最优控制问题)**
最优控制问题：
$$\min_{u(t)} J = \int_{t_0}^{t_f} L(x(t), u(t), t)dt + \phi(x(t_f), t_f)$$

受约束于：
$$\dot{x}(t) = f(x(t), u(t), t)$$
$$x(t_0) = x_0$$

**定理 4.1 (欧拉-拉格朗日方程)**
最优轨迹满足欧拉-拉格朗日方程：
$$\frac{d}{dt}\frac{\partial L}{\partial \dot{x}} - \frac{\partial L}{\partial x} = 0$$

**证明：** 通过变分法：

1. 构造变分 $\delta J$
2. 利用分部积分
3. 应用变分基本引理

### 4.2 动态规划

**定义 4.2 (值函数)**
值函数：
$$V(x, t) = \min_{u(\tau)} \int_t^{t_f} L(x(\tau), u(\tau), \tau)d\tau + \phi(x(t_f), t_f)$$

**定理 4.2 (贝尔曼方程)**
值函数满足贝尔曼方程：
$$-\frac{\partial V}{\partial t} = \min_u \{L(x, u, t) + \frac{\partial V}{\partial x}f(x, u, t)\}$$

**证明：** 通过最优性原理：

1. 分解最优控制问题
2. 利用时间可加性
3. 取极限得到偏微分方程

**算法 4.1 (动态规划)**

```haskell
dynamicProgramming :: CostFunction -> SystemDynamics -> ValueFunction
dynamicProgramming costFunction systemDynamics = 
  let -- 离散化状态空间
      stateGrid = discretizeStateSpace
      
      -- 初始化值函数
      initialValueFunction = initializeValueFunction stateGrid
      
      -- 值迭代
      valueIteration valueFunction = 
        let newValueFunction = updateValueFunction valueFunction costFunction systemDynamics
        in if convergenceCheck valueFunction newValueFunction
           then newValueFunction
           else valueIteration newValueFunction
      
      -- 求解最优值函数
      optimalValueFunction = valueIteration initialValueFunction
  in optimalValueFunction
```

### 4.3 线性二次型调节器

**定义 4.3 (LQR问题)**
线性二次型调节器问题：
$$\min_{u(t)} J = \int_0^\infty [x^T(t)Qx(t) + u^T(t)Ru(t)]dt$$

受约束于：
$$\dot{x}(t) = Ax(t) + Bu(t)$$

**定理 4.3 (LQR最优控制)**
LQR最优控制律：
$$u^*(t) = -Kx(t)$$

其中 $K = R^{-1}B^TP$，$P$ 是代数Riccati方程的解：
$$A^TP + PA - PBR^{-1}B^TP + Q = 0$$

**证明：** 通过动态规划：

1. 假设值函数为二次型 $V(x) = x^TPx$
2. 代入贝尔曼方程
3. 求解代数Riccati方程

**算法 4.2 (LQR设计)**

```haskell
lqrDesign :: Matrix Double -> Matrix Double -> Matrix Double -> Matrix Double -> Matrix Double
lqrDesign a b q r = 
  let -- 求解代数Riccati方程
      p = solveAlgebraicRiccati a b q r
      
      -- 计算最优反馈增益
      k = inverse r `multiply` (transpose b) `multiply` p
  in k

solveAlgebraicRiccati :: Matrix Double -> Matrix Double -> Matrix Double -> Matrix Double -> Matrix Double
solveAlgebraicRiccati a b q r = 
  let -- 构造哈密顿矩阵
      hamiltonian = matrix (2*n) (2*n) (\(i, j) -> 
        if i <= n && j <= n then a `atIndex` (i, j)
        else if i <= n && j > n then (b `multiply` (inverse r) `multiply` (transpose b)) `atIndex` (i, j-n)
        else if i > n && j <= n then -q `atIndex` (i-n, j)
        else -(transpose a) `atIndex` (i-n, j-n))
      
      -- 计算稳定不变子空间
      stableSubspace = computeStableSubspace hamiltonian
      
      -- 提取Riccati方程的解
      p = extractRiccatiSolution stableSubspace
  in p
```

## 5. 预测控制理论

### 5.1 模型预测控制

**定义 5.1 (MPC问题)**
模型预测控制问题：
$$\min_{u(k), ..., u(k+N-1)} J = \sum_{i=0}^{N-1} \|x(k+i|k)\|_Q^2 + \|u(k+i)\|_R^2 + \|x(k+N|k)\|_P^2$$

受约束于：
$$x(k+i+1|k) = Ax(k+i|k) + Bu(k+i)$$
$$u_{min} \leq u(k+i) \leq u_{max}$$
$$x_{min} \leq x(k+i|k) \leq x_{max}$$

**定理 5.1 (MPC稳定性)**
如果终端权重 $P$ 满足：
$$A^TPA - P + Q - A^TPB(R + B^TPB)^{-1}B^TPA \leq 0$$

则MPC闭环系统稳定。

**算法 5.1 (MPC控制器)**

```haskell
modelPredictiveControl :: LinearSystem -> Int -> Matrix Double -> Matrix Double -> Matrix Double -> Controller
modelPredictiveControl sys horizon q r p = 
  let -- 构造预测模型
      predictionModel = buildPredictionModel sys horizon
      
      -- 构造约束
      constraints = buildConstraints sys horizon
      
      -- 构造目标函数
      objectiveFunction = buildObjectiveFunction q r p horizon
      
      -- 求解优化问题
      solveOptimization state = 
        let optimizationProblem = OptimizationProblem {
              objective = objectiveFunction,
              constraints = constraints,
              initialState = state
            }
            solution = solveQP optimizationProblem
        in solution.controlSequence
      
      -- MPC控制律
      mpcController state = 
        let controlSequence = solveOptimization state
        in head controlSequence  -- 只使用第一个控制输入
  in MPCController {
    predictionModel = predictionModel,
    constraints = constraints,
    objectiveFunction = objectiveFunction,
    controller = mpcController
  }
```

### 5.2 鲁棒预测控制

**定义 5.2 (鲁棒MPC)**
鲁棒MPC考虑系统不确定性：
$$\min_{u(k), ..., u(k+N-1)} \max_{w(k), ..., w(k+N-1)} J$$

**定理 5.2 (鲁棒MPC稳定性)**
如果存在鲁棒不变集，则鲁棒MPC闭环系统稳定。

## 6. 滑模控制理论

### 6.1 高阶滑模控制

**定义 6.1 (高阶滑模)**
$r$ 阶滑模：
$$s = \dot{s} = \ddot{s} = \cdots = s^{(r-1)} = 0$$

**定义 6.2 (超扭曲算法)**
超扭曲算法：
$$u = -\alpha_1|s|^{1/2}\text{sign}(s) + v$$
$$\dot{v} = -\alpha_2\text{sign}(s)$$

**定理 6.1 (超扭曲收敛性)**
如果 $\alpha_1 > 0, \alpha_2 > 0$ 且满足适当条件，则超扭曲算法在有限时间内收敛。

### 6.2 自适应滑模控制

**定义 6.3 (自适应滑模)**
自适应滑模控制律：
$$u = -\hat{k}(t)\text{sign}(s)$$
$$\dot{\hat{k}}(t) = \gamma|s|$$

**定理 6.2 (自适应滑模稳定性)**
自适应滑模控制保证系统稳定且参数估计有界。

## 7. 参考文献

1. Zhou, K., & Doyle, J. C. (1998). Essentials of Robust Control. Prentice Hall.
2. Åström, K. J., & Wittenmark, B. (2013). Adaptive Control (2nd ed.). Dover Publications.
3. Khalil, H. K. (2015). Nonlinear Systems (3rd ed.). Prentice Hall.
4. Kirk, D. E. (2012). Optimal Control Theory: An Introduction. Dover Publications.
5. Camacho, E. F., & Bordons, C. (2007). Model Predictive Control (2nd ed.). Springer.
6. Utkin, V. I. (1992). Sliding Modes in Control and Optimization. Springer.
7. Sontag, E. D. (1998). Mathematical Control Theory: Deterministic Finite Dimensional Systems (2nd ed.). Springer.
8. Isidori, A. (1995). Nonlinear Control Systems (3rd ed.). Springer. 