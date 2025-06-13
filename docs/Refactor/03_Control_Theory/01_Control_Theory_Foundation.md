# 控制理论基础 - 形式化数学体系

## 目录

1. [控制系统基础](#1-控制系统基础)
2. [线性系统理论](#2-线性系统理论)
3. [稳定性分析](#3-稳定性分析)
4. [可控性与可观性](#4-可控性与可观性)
5. [反馈控制理论](#5-反馈控制理论)
6. [最优控制理论](#6-最优控制理论)
7. [鲁棒控制理论](#7-鲁棒控制理论)
8. [非线性控制理论](#8-非线性控制理论)

## 1. 控制系统基础

### 1.1 动态系统定义

**定义 1.1.1 (动态系统)**
动态系统是一个五元组 $\Sigma = (X, U, Y, f, h)$，其中：

- $X \subseteq \mathbb{R}^n$ 是状态空间
- $U \subseteq \mathbb{R}^m$ 是输入空间  
- $Y \subseteq \mathbb{R}^p$ 是输出空间
- $f : X \times U \rightarrow X$ 是状态转移函数
- $h : X \rightarrow Y$ 是输出函数

**定义 1.1.2 (连续时间系统)**
连续时间系统的状态方程：
$$\dot{x}(t) = f(x(t), u(t))$$
$$y(t) = h(x(t))$$

其中 $t \in \mathbb{R}^+$ 是连续时间变量。

**定义 1.1.3 (离散时间系统)**
离散时间系统的状态方程：
$$x(k+1) = f(x(k), u(k))$$
$$y(k) = h(x(k))$$

其中 $k \in \mathbb{N}$ 是离散时间变量。

### 1.2 系统分类

**定义 1.2.1 (线性系统)**
系统 $\Sigma$ 是线性的，如果对于任意 $\alpha, \beta \in \mathbb{R}$ 和 $(x_1, u_1), (x_2, u_2) \in X \times U$：
$$f(\alpha x_1 + \beta x_2, \alpha u_1 + \beta u_2) = \alpha f(x_1, u_1) + \beta f(x_2, u_2)$$
$$h(\alpha x_1 + \beta x_2) = \alpha h(x_1) + \beta h(x_2)$$

**定义 1.2.2 (时不变系统)**
系统 $\Sigma$ 是时不变的，如果对于任意时间平移 $\tau$：
$$f(x(t), u(t)) = f(x(t-\tau), u(t-\tau))$$
$$h(x(t)) = h(x(t-\tau))$$

**定义 1.2.3 (线性时不变系统)**
线性时不变(LTI)系统的状态空间表示：
$$\dot{x}(t) = Ax(t) + Bu(t)$$
$$y(t) = Cx(t) + Du(t)$$

其中：

- $A \in \mathbb{R}^{n \times n}$ 是系统矩阵
- $B \in \mathbb{R}^{n \times m}$ 是输入矩阵
- $C \in \mathbb{R}^{p \times n}$ 是输出矩阵
- $D \in \mathbb{R}^{p \times m}$ 是直接传递矩阵

### 1.3 系统解

**定理 1.3.1 (线性系统解)**
线性时不变系统 $\dot{x}(t) = Ax(t) + Bu(t)$ 的解为：
$$x(t) = e^{At}x(0) + \int_0^t e^{A(t-\tau)}Bu(\tau)d\tau$$

**证明：** 通过状态方程的积分：

1. **齐次方程解**: $\dot{x} = Ax$ 的解为 $x(t) = e^{At}x(0)$
2. **非齐次方程**: 通过变分常数法求解
3. **完整解**: 利用卷积积分得到 $x(t) = e^{At}x(0) + \int_0^t e^{A(t-\tau)}Bu(\tau)d\tau$

**定义 1.3.1 (状态转移矩阵)**
状态转移矩阵 $\Phi(t) = e^{At}$ 满足：
$$\Phi(0) = I$$
$$\dot{\Phi}(t) = A\Phi(t)$$
$$\Phi(t_1 + t_2) = \Phi(t_1)\Phi(t_2)$$

## 2. 线性系统理论

### 2.1 传递函数

**定义 2.1.1 (传递函数)**
线性时不变系统的传递函数定义为：
$$G(s) = C(sI - A)^{-1}B + D$$

其中 $s \in \mathbb{C}$ 是拉普拉斯变量。

**定理 2.1.1 (传递函数性质)**
传递函数 $G(s)$ 是 $s$ 的有理函数，且：

1. 极点由 $A$ 的特征值决定
2. 零点由系统零点决定
3. 相对阶为 $n - \text{deg}(G(s))$

**证明：** 通过矩阵求逆和特征值分解：

1. $(sI - A)^{-1} = \frac{\text{adj}(sI - A)}{\det(sI - A)}$
2. $\det(sI - A)$ 的根是 $A$ 的特征值
3. 传递函数分子分母都是多项式

### 2.2 系统实现

**定义 2.2.1 (最小实现)**
传递函数 $G(s)$ 的最小实现是状态空间表示 $(A, B, C, D)$，其中 $A$ 的维数最小。

**定理 2.2.1 (最小实现判据)**
状态空间表示 $(A, B, C, D)$ 是最小实现当且仅当 $(A, B)$ 可控且 $(A, C)$ 可观。

**证明：** 通过可控性和可观性分解：

1. 如果系统不可控或不可观，可以降维
2. 可控且可观的系统不能进一步降维
3. 因此最小实现必须可控且可观

### 2.3 系统连接

**定义 2.3.1 (串联连接)**
两个系统 $G_1(s)$ 和 $G_2(s)$ 的串联连接：
$$G(s) = G_2(s)G_1(s)$$

**定义 2.3.2 (并联连接)**
两个系统 $G_1(s)$ 和 $G_2(s)$ 的并联连接：
$$G(s) = G_1(s) + G_2(s)$$

**定义 2.3.3 (反馈连接)**
系统 $G(s)$ 和控制器 $K(s)$ 的反馈连接：
$$G_{cl}(s) = \frac{G(s)K(s)}{1 + G(s)K(s)}$$

## 3. 稳定性分析

### 3.1 李雅普诺夫稳定性

**定义 3.1.1 (平衡点)**
状态 $x_e \in X$ 是平衡点，如果 $f(x_e, 0) = 0$。

**定义 3.1.2 (李雅普诺夫稳定性)**
平衡点 $x_e$ 是李雅普诺夫稳定的，如果对于任意 $\epsilon > 0$，存在 $\delta > 0$ 使得：
$$\|x(0) - x_e\| < \delta \Rightarrow \|x(t) - x_e\| < \epsilon \text{ for all } t \geq 0$$

**定义 3.1.3 (渐近稳定性)**
平衡点 $x_e$ 是渐近稳定的，如果它是李雅普诺夫稳定的且：
$$\lim_{t \rightarrow \infty} x(t) = x_e$$

**定义 3.1.4 (指数稳定性)**
平衡点 $x_e$ 是指数稳定的，如果存在常数 $M, \alpha > 0$ 使得：
$$\|x(t) - x_e\| \leq M\|x(0) - x_e\|e^{-\alpha t}$$

**定理 3.1.1 (李雅普诺夫直接法)**
如果存在连续可微函数 $V : X \rightarrow \mathbb{R}$ 满足：

1. $V(x_e) = 0$
2. $V(x) > 0$ 对于 $x \neq x_e$
3. $\dot{V}(x) \leq 0$ 对于 $x \neq x_e$

则平衡点 $x_e$ 是李雅普诺夫稳定的。

**证明：** 通过李雅普诺夫函数的单调性：

1. $V(x)$ 在平衡点附近有下界
2. $\dot{V}(x) \leq 0$ 确保 $V(x)$ 不增加
3. 因此状态轨迹保持在平衡点附近

**定理 3.1.2 (李雅普诺夫渐近稳定性)**
如果存在连续可微函数 $V : X \rightarrow \mathbb{R}$ 满足：

1. $V(x_e) = 0$
2. $V(x) > 0$ 对于 $x \neq x_e$
3. $\dot{V}(x) < 0$ 对于 $x \neq x_e$

则平衡点 $x_e$ 是渐近稳定的。

**证明：** 通过李雅普诺夫函数的严格单调性：

1. $\dot{V}(x) < 0$ 确保 $V(x)$ 严格递减
2. $V(x)$ 有下界，因此收敛到某个值
3. 唯一可能的收敛点是 $x_e$

### 3.2 线性系统稳定性

**定理 3.2.1 (线性系统稳定性)**
线性系统 $\dot{x} = Ax$ 的零平衡点是渐近稳定的当且仅当 $A$ 的所有特征值都有负实部。

**证明：** 通过特征值分解：

1. $A$ 的特征值决定系统动态
2. 负实部特征值对应衰减模态
3. 正实部特征值对应增长模态

**定义 3.2.1 (赫尔维茨判据)**
多项式 $p(s) = a_n s^n + a_{n-1} s^{n-1} + \cdots + a_0$ 是赫尔维茨的，如果所有根都有负实部。

-**算法 3.2.1 (赫尔维茨判据)**

```haskell
hurwitzCriterion :: [Double] -> Bool
hurwitzCriterion coeffs = 
  let n = length coeffs - 1
      hurwitzMatrix = buildHurwitzMatrix coeffs
      minors = [determinant (submatrix hurwitzMatrix i) | i <- [1..n]]
  in all (> 0) minors

buildHurwitzMatrix :: [Double] -> Matrix
buildHurwitzMatrix coeffs = 
  let n = length coeffs - 1
      rows = [buildRow coeffs i | i <- [0..n-1]]
  in matrixFromRows rows

buildRow :: [Double] -> Int -> [Double]
buildRow coeffs i = 
  let n = length coeffs - 1
      row = replicate (2*n) 0
  in zipWith (\j c -> if j >= 0 && j < n then coeffs !! j else 0) 
             [i, i+2, i+4..] row
```

### 3.3 频域稳定性

**定义 3.3.1 (奈奎斯特判据)**
闭环系统稳定的奈奎斯特判据：
$$N = P - Z$$

其中：

- $N$ 是奈奎斯特图绕 $(-1, 0)$ 的圈数
- $P$ 是开环系统在右半平面的极点数
- $Z$ 是闭环系统在右半平面的极点数

**定理 3.3.1 (奈奎斯特稳定性)**
闭环系统稳定当且仅当 $Z = 0$，即 $N = P$。

## 4. 可控性与可观性

### 4.1 可控性

**定义 4.1.1 (可控性)**
系统 $\Sigma$ 在时间 $T$ 内可控，如果对于任意初始状态 $x_0$ 和目标状态 $x_f$，存在输入 $u(t)$ 使得 $x(T) = x_f$。

**定义 4.1.2 (可控性矩阵)**
线性系统的可控性矩阵：
$$\mathcal{C} = [B \quad AB \quad A^2B \quad \cdots \quad A^{n-1}B]$$

**定理 4.1.1 (可控性判据)**
线性系统完全可控当且仅当可控性矩阵 $\mathcal{C}$ 满秩。

**证明：** 通过凯莱-哈密顿定理：

1. 可控性矩阵的列空间包含可达状态空间
2. 满秩确保可达整个状态空间
3. 凯莱-哈密顿定理限制矩阵幂的线性相关性

-**算法 4.1.1 (可控性检验)**

```haskell
controllability :: Matrix -> Matrix -> Bool
controllability a b = 
  let n = rows a
      controllabilityMatrix = buildControllabilityMatrix a b n
  in rank controllabilityMatrix == n

buildControllabilityMatrix :: Matrix -> Matrix -> Int -> Matrix
buildControllabilityMatrix a b n = 
  let powers = [a^i | i <- [0..n-1]]
      terms = [powers !! i * b | i <- [0..n-1]]
  in hconcat terms
```

### 4.2 可观性

**定义 4.2.1 (可观性)**
系统 $\Sigma$ 可观，如果任意初始状态 $x_0$ 都可以通过输出 $y(t)$ 唯一确定。

**定义 4.2.2 (可观性矩阵)**
线性系统的可观性矩阵：
$$\mathcal{O} = \begin{bmatrix} C \\ CA \\ CA^2 \\ \vdots \\ CA^{n-1} \end{bmatrix}$$

**定理 4.2.1 (可观性判据)**
线性系统完全可观当且仅当可观性矩阵 $\mathcal{O}$ 满秩。

**证明：** 通过输出方程：

1. 可观性矩阵的行空间包含可观测状态空间
2. 满秩确保状态唯一确定
3. 输出序列包含足够信息重构状态

-**算法 4.2.1 (可观性检验)**

```haskell
observability :: Matrix -> Matrix -> Bool
observability a c = 
  let n = rows a
      observabilityMatrix = buildObservabilityMatrix a c n
  in rank observabilityMatrix == n

buildObservabilityMatrix :: Matrix -> Matrix -> Int -> Matrix
buildObservabilityMatrix a c n = 
  let powers = [a^i | i <- [0..n-1]]
      terms = [c * (powers !! i) | i <- [0..n-1]]
  in vconcat terms
```

### 4.3 对偶性

**定理 4.3.1 (可控可观对偶性)**
系统 $(A, B, C)$ 可控当且仅当系统 $(A^T, C^T, B^T)$ 可观。

**证明：** 通过矩阵转置性质：

1. $(A, B)$ 的可控性矩阵为 $[B \quad AB \quad \cdots \quad A^{n-1}B]$
2. $(A^T, C^T)$ 的可观性矩阵为 $\begin{bmatrix} C^T \\ C^TA^T \\ \vdots \\ C^T(A^T)^{n-1} \end{bmatrix}$
3. 这两个矩阵互为转置，因此秩相同

## 5. 反馈控制理论

### 5.1 状态反馈

**定义 5.1.1 (状态反馈)**
状态反馈控制律：
$$u(t) = -Kx(t) + r(t)$$

其中 $K \in \mathbb{R}^{m \times n}$ 是反馈增益矩阵，$r(t)$ 是参考输入。

**定理 5.1.1 (极点配置)**
如果系统 $(A, B)$ 可控，则可以通过状态反馈任意配置闭环极点。

**证明：** 通过可控性标准形：

1. 可控系统可以变换为标准形
2. 标准形下极点配置直接可得
3. 变换回原坐标系得到反馈增益

-**算法 5.1.1 (极点配置)**

```haskell
polePlacement :: Matrix -> Matrix -> [Complex Double] -> Matrix
polePlacement a b desiredPoles = 
  let controllableForm = toControllableForm a b
      kStandard = placePoles controllableForm desiredPoles
      transformation = getTransformation a b
  in kStandard * transformation

toControllableForm :: Matrix -> Matrix -> (Matrix, Matrix)
toControllableForm a b = 
  let n = rows a
      controllabilityMatrix = buildControllabilityMatrix a b n
      transformation = inverse controllabilityMatrix
      aStandard = transformation * a * inverse transformation
      bStandard = transformation * b
  in (aStandard, bStandard)
```

### 5.2 输出反馈

**定义 5.2.1 (输出反馈)**
输出反馈控制律：
$$u(t) = -Ky(t) + r(t)$$

**定理 5.2.1 (输出反馈限制)**
输出反馈不能任意配置极点，只能配置可观部分的极点。

**证明：** 通过可观性分解：

1. 系统可以分解为可观和不可观部分
2. 输出反馈只能影响可观部分
3. 不可观部分的极点无法通过输出反馈改变

### 5.3 观测器设计

**定义 5.3.1 (全维观测器)**
全维观测器：
$$\dot{\hat{x}}(t) = A\hat{x}(t) + Bu(t) + L(y(t) - C\hat{x}(t))$$

其中 $L \in \mathbb{R}^{n \times p}$ 是观测器增益矩阵。

**定理 5.3.1 (观测器极点配置)**
如果系统 $(A, C)$ 可观，则可以通过选择 $L$ 任意配置观测器极点。

**证明：** 通过可观性对偶性：

1. $(A, C)$ 可观等价于 $(A^T, C^T)$ 可控
2. 观测器极点配置等价于状态反馈极点配置
3. 对偶系统可控，因此可以任意配置极点

-**算法 5.3.1 (观测器设计)**

```haskell
observerDesign :: Matrix -> Matrix -> [Complex Double] -> Matrix
observerDesign a c desiredPoles = 
  let dualA = transpose a
      dualB = transpose c
      dualK = polePlacement dualA dualB desiredPoles
  in transpose dualK
```

### 5.4 分离原理

**定理 5.4.1 (分离原理)**
如果状态反馈控制器和观测器分别设计，则闭环系统的极点等于控制器极点和观测器极点的并集。

**证明：** 通过闭环系统分析：

1. 闭环系统状态为 $[x^T \quad \tilde{x}^T]^T$
2. 闭环系统矩阵为块对角矩阵
3. 特征值等于各块特征值的并集

## 6. 最优控制理论

### 6.1 线性二次型调节器

**定义 6.1.1 (LQR问题)**
线性二次型调节器问题：
$$\min_{u(t)} J = \int_0^\infty [x^T(t)Qx(t) + u^T(t)Ru(t)]dt$$

约束条件：$\dot{x}(t) = Ax(t) + Bu(t)$

其中 $Q \geq 0$ 和 $R > 0$ 是权重矩阵。

**定理 6.1.1 (LQR解)**
LQR问题的最优控制律为：
$$u^*(t) = -R^{-1}B^TPx(t)$$

其中 $P$ 是代数黎卡提方程的解：
$$A^TP + PA - PBR^{-1}B^TP + Q = 0$$

**证明：** 通过变分法和哈密顿-雅可比-贝尔曼方程：

1. 最优性必要条件
2. 代数黎卡提方程
3. 最优控制律形式

-**算法 6.1.1 (LQR设计)**

```haskell
lqrDesign :: Matrix -> Matrix -> Matrix -> Matrix -> Matrix
lqrDesign a b q r = 
  let p = solveAlgebraicRiccati a b q r
      k = inverse r * transpose b * p
  in k

solveAlgebraicRiccati :: Matrix -> Matrix -> Matrix -> Matrix -> Matrix
solveAlgebraicRiccati a b q r = 
  let n = rows a
      h = buildHamiltonianMatrix a b q r
      eigenvals = eigenvalues h
      stableEigenvals = filter (\lambda -> realPart lambda < 0) eigenvals
      eigenvectors = eigenvectors h
      stableEigenvectors = selectEigenvectors eigenvectors stableEigenvals
      p = solve pEquation stableEigenvectors
  in p
```

### 6.2 线性二次型高斯控制

**定义 6.2.1 (LQG问题)**
线性二次型高斯控制问题：
$$\min_{u(t)} E[J] = E\left[\int_0^\infty [x^T(t)Qx(t) + u^T(t)Ru(t)]dt\right]$$

约束条件：
$$\dot{x}(t) = Ax(t) + Bu(t) + w(t)$$
$$y(t) = Cx(t) + v(t)$$

其中 $w(t)$ 和 $v(t)$ 是白噪声。

**定理 6.2.1 (LQG解)**
LQG问题的最优控制律为：
$$u^*(t) = -K\hat{x}(t)$$

其中：

- $K$ 是LQR最优增益
- $\hat{x}(t)$ 是卡尔曼滤波器估计

**证明：** 通过分离原理：

1. LQR设计最优控制律
2. 卡尔曼滤波器设计最优估计
3. 分离原理确保整体最优性

## 7. 鲁棒控制理论

### 7.1 H∞控制

**定义 7.1.1 (H∞范数)**
传递函数 $G(s)$ 的H∞范数：
$$\|G\|_\infty = \sup_{\omega \in \mathbb{R}} \sigma_{\max}(G(j\omega))$$

其中 $\sigma_{\max}$ 是最大奇异值。

**定义 7.1.2 (H∞控制问题)**
H∞控制问题：设计控制器 $K(s)$ 使得：
$$\|T_{zw}\|_\infty < \gamma$$

其中 $T_{zw}$ 是从干扰 $w$ 到性能输出 $z$ 的闭环传递函数。

**定理 7.1.1 (H∞控制解)**
H∞控制问题的解通过求解两个代数黎卡提方程得到。

-**算法 7.1.1 (H∞控制器设计)**

```haskell
hinfController :: System -> Double -> Controller
hinfController plant gamma = 
  let (a, b1, b2, c1, c2, d11, d12, d21, d22) = extractMatrices plant
      (x, y) = solveHinfRiccati a b1 b2 c1 c2 d11 d12 d21 d22 gamma
      f = computeStateFeedback x
      l = computeObserverGain y
  in buildController f l
```

### 7.2 μ综合

**定义 7.2.1 (结构奇异值)**
结构奇异值 $\mu_\Delta(M)$：
$$\mu_\Delta(M) = \frac{1}{\min\{\bar{\sigma}(\Delta) : \Delta \in \Delta, \det(I - M\Delta) = 0\}}$$

**定义 7.2.2 (μ综合问题)**
μ综合问题：设计控制器使得：
$$\mu_\Delta(T_{zw}) < 1$$

-**算法 7.2.1 (μ综合)**

```haskell
muSynthesis :: UncertainSystem -> Controller
muSynthesis uncertainPlant = 
  let initialController = designInitialController uncertainPlant
      controller = iterateMuSynthesis uncertainPlant initialController
  in controller

iterateMuSynthesis :: UncertainSystem -> Controller -> Controller
iterateMuSynthesis plant controller = 
  let mu = computeMu plant controller
      scaling = computeOptimalScaling mu
      newController = redesignController plant scaling
  in if convergenceTest mu then newController
     else iterateMuSynthesis plant newController
```

## 8. 非线性控制理论

### 8.1 反馈线性化

**定义 8.1.1 (相对阶)**
系统 $\dot{x} = f(x) + g(x)u$ 的相对阶为 $r$，如果：
$$L_g L_f^{k-1} h(x) = 0, \quad k = 1, 2, \ldots, r-1$$
$$L_g L_f^{r-1} h(x) \neq 0$$

其中 $L_f h$ 是李导数。

**定理 8.1.1 (反馈线性化)**
如果系统相对阶为 $n$，则可以通过状态反馈和坐标变换将系统线性化。

**证明：** 通过坐标变换和反馈控制：

1. 定义新的坐标 $z_i = L_f^{i-1} h(x)$
2. 设计反馈控制律 $u = \frac{v - L_f^n h(x)}{L_g L_f^{n-1} h(x)}$
3. 得到线性系统 $\dot{z} = Az + Bv$

### 8.2 滑模控制

**定义 8.2.1 (滑模面)**
滑模面定义为：
$$s(x) = c^T x = 0$$

其中 $c$ 是设计参数。

**定义 8.2.2 (滑模控制律)**
滑模控制律：
$$u = u_{eq} + u_{sw}$$

其中：

- $u_{eq}$ 是等效控制
- $u_{sw}$ 是开关控制

**定理 8.2.1 (滑模稳定性)**
如果滑模面设计满足 $c^T b \neq 0$，则系统在有限时间内到达滑模面。

**证明：** 通过李雅普诺夫函数：

1. 选择 $V = \frac{1}{2}s^2$
2. 设计控制律使得 $\dot{V} < 0$
3. 确保有限时间收敛

## 结论

控制理论为动态系统的分析和设计提供了完整的数学框架，从基础的线性系统理论到高级的非线性控制方法，涵盖了：

1. **系统建模**: 状态空间表示和传递函数
2. **稳定性分析**: 李雅普诺夫方法和频域方法
3. **系统性质**: 可控性、可观性、对偶性
4. **控制设计**: 状态反馈、输出反馈、观测器
5. **最优控制**: LQR、LQG、H∞控制
6. **鲁棒控制**: 不确定性处理和性能保证
7. **非线性控制**: 反馈线性化、滑模控制

这些理论为实际工程应用提供了坚实的理论基础和设计方法。

## 参考文献

1. Khalil, H. K. (2002). *Nonlinear systems*. Prentice Hall.
2. Ogata, K. (2010). *Modern control engineering*. Prentice Hall.
3. Skogestad, S., & Postlethwaite, I. (2007). *Multivariable feedback control: analysis and design*. John Wiley & Sons.
4. Zhou, K., & Doyle, J. C. (1998). *Essentials of robust control*. Prentice Hall.
5. Slotine, J. J. E., & Li, W. (1991). *Applied nonlinear control*. Prentice Hall.
6. Anderson, B. D., & Moore, J. B. (2012). *Optimal control: linear quadratic methods*. Courier Corporation.
7. Doyle, J. C., Francis, B. A., & Tannenbaum, A. R. (2013). *Feedback control theory*. Courier Corporation.

---

**最后更新**: 2024年12月19日  
**版本**: v1.0  
**状态**: 完成控制理论基础重构
