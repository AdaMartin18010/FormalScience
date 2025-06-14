# 经典控制理论 (Classical Control Theory)

## 目录

1. [引言](#引言)
2. [控制系统基础](#控制系统基础)
3. [线性系统理论](#线性系统理论)
4. [稳定性分析](#稳定性分析)
5. [可控性与可观性](#可控性与可观性)
6. [反馈控制设计](#反馈控制设计)
7. [频率域方法](#频率域方法)
8. [根轨迹方法](#根轨迹方法)
9. [应用实例](#应用实例)
10. [总结](#总结)
11. [参考文献](#参考文献)

## 交叉引用与关联

### 相关理论领域

- **[现代控制理论](02_Modern_Control_Theory.md)**：状态空间方法的扩展
- **[自适应控制理论](03_Adaptive_Control_Theory.md)**：参数自适应控制
- **[鲁棒控制理论](04_Robust_Control_Theory.md)**：不确定性处理
- **[最优控制理论](05_Optimal_Control_Theory.md)**：性能优化控制
- **[智能控制理论](06_Intelligent_Control_Theory.md)**：智能算法控制
- **[时态逻辑](../06_Temporal_Logic/01_Temporal_Logic_Foundation.md)**：控制系统的时间性质验证
- **[分布式系统](../04_Distributed_Systems/01_Consensus_Theory.md)**：分布式控制系统

### 基础依赖关系

- **[数学基础](../01_Foundational_Theory/05_Number_System_Theory.md)**：线性代数和微分方程
- **[逻辑基础](../01_Foundational_Theory/01_Logic_Foundation.md)**：系统性质的逻辑验证
- **[形式语言](../07_Formal_Language/01_Automata_Theory.md)**：控制系统的形式化建模

### 应用领域

- **[软件工程](../10_Software_Engineering/01_Software_Engineering_Theory.md)**：软件控制系统设计
- **[人工智能](../11_AI_Computing/01_Artificial_Intelligence_Theory.md)**：智能控制系统
- **[系统设计](../10_Software_Engineering/03_System_Design_Theory.md)**：系统架构设计

## 引言

经典控制理论是控制工程的基础，主要研究线性时不变系统的分析和设计方法。本章节建立经典控制理论的完整框架，包括系统建模、稳定性分析、控制器设计等核心内容。

### 1.1 研究背景

经典控制理论起源于20世纪初的工程应用需求，经过Nyquist、Bode、Evans等人的发展，形成了完整的理论体系。经典控制理论主要处理单输入单输出(SISO)系统，为现代控制理论奠定了基础。

**关联**：经典控制理论与[现代控制理论](02_Modern_Control_Theory.md)形成互补，前者关注频率域方法，后者关注状态空间方法。

### 1.2 本章目标

- 建立完整的控制系统数学模型
- 提供系统稳定性的分析方法
- 设计有效的反馈控制器
- 建立频率域和时域的设计方法

## 控制系统基础

### 2.1 系统定义

**定义 2.1 (动态系统)**
动态系统是一个五元组 $\Sigma = (X, U, Y, f, h)$，其中：

- $X \subseteq \mathbb{R}^n$ 是状态空间
- $U \subseteq \mathbb{R}^m$ 是输入空间  
- $Y \subseteq \mathbb{R}^p$ 是输出空间
- $f : X \times U \rightarrow X$ 是状态转移函数
- $h : X \rightarrow Y$ 是输出函数

**定义 2.2 (连续时间系统)**
连续时间系统的状态方程：
$$\dot{x}(t) = f(x(t), u(t))$$
$$y(t) = h(x(t))$$

**定义 2.3 (离散时间系统)**
离散时间系统的状态方程：
$$x(k+1) = f(x(k), u(k))$$
$$y(k) = h(x(k))$$

### 2.2 系统分类

**定义 2.4 (线性系统)**
系统 $\Sigma$ 是线性的，如果满足叠加原理：
$$f(\alpha x_1 + \beta x_2, \alpha u_1 + \beta u_2) = \alpha f(x_1, u_1) + \beta f(x_2, u_2)$$
$$h(\alpha x_1 + \beta x_2) = \alpha h(x_1) + \beta h(x_2)$$

**定义 2.5 (时不变系统)**
系统 $\Sigma$ 是时不变的，如果对于任意时间平移 $\tau$：
$$f(x(t), u(t)) = f(x(t-\tau), u(t-\tau))$$
$$h(x(t)) = h(x(t-\tau))$$

**定义 2.6 (线性时不变系统)**
线性时不变(LTI)系统的状态空间表示：
$$\dot{x}(t) = Ax(t) + Bu(t)$$
$$y(t) = Cx(t) + Du(t)$$

其中：

- $A \in \mathbb{R}^{n \times n}$ 是系统矩阵
- $B \in \mathbb{R}^{n \times m}$ 是输入矩阵
- $C \in \mathbb{R}^{p \times n}$ 是输出矩阵
- $D \in \mathbb{R}^{p \times m}$ 是直接传递矩阵

### 2.3 传递函数

**定义 2.7 (传递函数)**
LTI系统的传递函数定义为：
$$G(s) = C(sI - A)^{-1}B + D$$

**定理 2.1 (传递函数性质)**
传递函数 $G(s)$ 是有理函数，分子分母多项式的次数满足：
$$\deg(\text{num}) \leq \deg(\text{den})$$

**证明：**

1. $(sI - A)^{-1}$ 的每个元素都是有理函数
2. 矩阵乘法和加法保持有理性
3. 传递函数是有理函数的线性组合

## 线性系统理论

### 3.1 系统解

**定理 3.1 (线性系统解)**
LTI系统 $\dot{x}(t) = Ax(t) + Bu(t)$ 的解为：
$$x(t) = e^{At}x(0) + \int_0^t e^{A(t-\tau)}Bu(\tau)d\tau$$

**证明：**
通过状态方程的积分：

1. **齐次方程解**：$\dot{x} = Ax$ 的解为 $x(t) = e^{At}x(0)$
2. **非齐次方程解**：通过变分常数法求解
3. **完整解**：利用卷积积分得到

**定义 3.1 (状态转移矩阵)**
状态转移矩阵定义为：
$$\Phi(t) = e^{At}$$

-**性质 3.1 (状态转移矩阵性质)**

1. $\Phi(0) = I$
2. $\Phi(t_1 + t_2) = \Phi(t_1)\Phi(t_2)$
3. $\Phi^{-1}(t) = \Phi(-t)$
4. $\frac{d}{dt}\Phi(t) = A\Phi(t)$

### 3.2 系统响应

**定义 3.2 (脉冲响应)**
系统的脉冲响应定义为：
$$g(t) = \mathcal{L}^{-1}\{G(s)\}$$

**定义 3.3 (阶跃响应)**
系统的阶跃响应定义为：
$$h(t) = \mathcal{L}^{-1}\left\{\frac{G(s)}{s}\right\}$$

**定理 3.2 (卷积积分)**
系统输出可以通过卷积积分计算：
$$y(t) = \int_0^t g(t-\tau)u(\tau)d\tau$$

## 稳定性分析

### 4.1 李雅普诺夫稳定性

**定义 4.1 (平衡点)**
状态 $x_e \in X$ 是平衡点，如果 $f(x_e, 0) = 0$。

**定义 4.2 (李雅普诺夫稳定性)**
平衡点 $x_e$ 是李雅普诺夫稳定的，如果对于任意 $\epsilon > 0$，存在 $\delta > 0$ 使得：
$$\|x(0) - x_e\| < \delta \Rightarrow \|x(t) - x_e\| < \epsilon \text{ for all } t \geq 0$$

**定义 4.3 (渐近稳定性)**
平衡点 $x_e$ 是渐近稳定的，如果它是李雅普诺夫稳定的且：
$$\lim_{t \rightarrow \infty} x(t) = x_e$$

**定理 4.1 (李雅普诺夫直接法)**
如果存在连续可微函数 $V : X \rightarrow \mathbb{R}$ 满足：

1. $V(x_e) = 0$
2. $V(x) > 0$ 对于 $x \neq x_e$
3. $\dot{V}(x) \leq 0$ 对于 $x \neq x_e$

则平衡点 $x_e$ 是李雅普诺夫稳定的。

**证明：**
通过李雅普诺夫函数的单调性：

1. $V(x)$ 在平衡点附近有下界
2. $\dot{V}(x) \leq 0$ 确保 $V(x)$ 不增加
3. 因此状态轨迹保持在平衡点附近

### 4.2 线性系统稳定性

**定理 4.2 (线性系统稳定性)**
线性系统 $\dot{x} = Ax$ 的零平衡点是渐近稳定的当且仅当 $A$ 的所有特征值都有负实部。

**证明：**
通过特征值分解：

1. $A$ 的特征值决定系统动态
2. 负实部特征值对应衰减模态
3. 正实部特征值对应增长模态

**定义 4.4 (赫尔维茨判据)**
多项式 $p(s) = a_n s^n + a_{n-1} s^{n-1} + \cdots + a_0$ 是赫尔维茨的，如果所有根都有负实部。

-**算法 4.1 (赫尔维茨判据)**

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
      matrix = zeroMatrix n n
  in foldl (\m (i, j, val) -> setElement m i j val) matrix
       [(i, j, coeffs !! (n - i + 2*j)) | i <- [0..n-1], j <- [0..n-1], n - i + 2*j >= 0, n - i + 2*j < length coeffs]
```

### 4.3 Routh-Hurwitz判据

-**算法 4.2 (Routh表)**

```haskell
routhTable :: [Double] -> [[Double]]
routhTable coeffs = 
  let n = length coeffs - 1
      firstRow = coeffs
      secondRow = [coeffs !! i | i <- [1,3..n], i < length coeffs]
      buildRow prev1 prev2 = 
        let k = head prev1
            newRow = [k * (prev2 !! i) - (prev1 !! (i+1)) * (prev2 !! 0) | i <- [0..length prev2-2]]
        in newRow
  in iterate (\rows -> buildRow (head rows) (rows !! 1)) [firstRow, secondRow]
```

## 可控性与可观性

### 5.1 可控性

**定义 5.1 (可控性)**
系统 $\Sigma$ 在时间 $T$ 内可控，如果对于任意初始状态 $x_0$ 和目标状态 $x_f$，存在输入 $u(t)$ 使得 $x(T) = x_f$。

**定义 5.2 (可控性矩阵)**
线性系统的可控性矩阵：
$$\mathcal{C} = [B \quad AB \quad A^2B \quad \cdots \quad A^{n-1}B]$$

**定理 5.1 (可控性判据)**
线性系统完全可控当且仅当可控性矩阵 $\mathcal{C}$ 满秩。

**证明：**
通过凯莱-哈密顿定理：

1. 可控性矩阵的列空间包含可达状态空间
2. 满秩确保可达整个状态空间
3. 凯莱-哈密顿定理限制矩阵幂的线性相关性

-**算法 5.1 (可控性检查)**

```haskell
controllability :: Matrix -> Matrix -> Bool
controllability a b = 
  let n = rows a
      controllabilityMatrix = buildControllabilityMatrix a b n
  in rank controllabilityMatrix == n

buildControllabilityMatrix :: Matrix -> Matrix -> Int -> Matrix
buildControllabilityMatrix a b n = 
  let powers = take n $ iterate (\m -> a * m) b
  in horizontalConcat powers
```

### 5.2 可观性

**定义 5.3 (可观性)**
系统 $\Sigma$ 可观，如果任意初始状态 $x_0$ 都可以通过输出 $y(t)$ 唯一确定。

**定义 5.4 (可观性矩阵)**
线性系统的可观性矩阵：
$$\mathcal{O} = \begin{bmatrix} C \\ CA \\ CA^2 \\ \vdots \\ CA^{n-1} \end{bmatrix}$$

**定理 5.2 (可观性判据)**
线性系统完全可观当且仅当可观性矩阵 $\mathcal{O}$ 满秩。

**证明：**
通过输出方程：

1. 可观性矩阵的行空间包含可观测状态空间
2. 满秩确保状态唯一确定
3. 输出序列包含足够信息重构状态

-**算法 5.2 (可观性检查)**

```haskell
observability :: Matrix -> Matrix -> Bool
observability a c = 
  let n = rows a
      observabilityMatrix = buildObservabilityMatrix a c n
  in rank observabilityMatrix == n

buildObservabilityMatrix :: Matrix -> Matrix -> Int -> Matrix
buildObservabilityMatrix a c n = 
  let powers = take n $ iterate (\m -> m * a) c
  in verticalConcat powers
```

## 反馈控制设计

### 6.1 状态反馈

**定义 6.1 (状态反馈)**
状态反馈控制律：
$$u(t) = -Kx(t) + r(t)$$

其中 $K \in \mathbb{R}^{m \times n}$ 是反馈增益矩阵，$r(t)$ 是参考输入。

**定理 6.1 (极点配置)**
如果系统 $(A, B)$ 可控，则可以通过状态反馈任意配置闭环极点。

**证明：**
通过可控性标准形：

1. 可控系统可以变换为标准形
2. 标准形下极点配置直接可得
3. 变换回原坐标系得到反馈增益

-**算法 6.1 (极点配置)**

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
      aBar = transformation * a * inverse transformation
      bBar = transformation * b
  in (aBar, bBar)

placePoles :: Matrix -> Matrix -> [Complex Double] -> Matrix
placePoles aBar bBar desiredPoles = 
  let characteristicPoly = product [s - pole | pole <- desiredPoles]
      coeffs = polynomialCoefficients characteristicPoly
      kStandard = [-coeffs !! i | i <- [1..length coeffs-1]]
  in matrixFromList [kStandard]
```

### 6.2 输出反馈

**定义 6.2 (输出反馈)**
输出反馈控制律：
$$u(t) = -Ky(t) + r(t)$$

**定理 6.2 (输出反馈限制)**
输出反馈不能任意配置极点，只能配置可观部分的极点。

**证明：**
通过可观性分解：

1. 系统可以分解为可观和不可观部分
2. 输出反馈只能影响可观部分
3. 不可观部分的极点无法通过输出反馈改变

### 6.3 观测器设计

**定义 6.3 (全维观测器)**
全维观测器：
$$\dot{\hat{x}}(t) = A\hat{x}(t) + Bu(t) + L(y(t) - C\hat{x}(t))$$

其中 $L \in \mathbb{R}^{n \times p}$ 是观测器增益矩阵。

**定理 6.3 (观测器极点配置)**
如果系统 $(A, C)$ 可观，则可以通过选择 $L$ 任意配置观测器极点。

**证明：**
通过可观性对偶性：

1. $(A, C)$ 可观等价于 $(A^T, C^T)$ 可控
2. 观测器极点配置等价于状态反馈极点配置
3. 对偶系统使用相同的极点配置算法

-**算法 6.2 (观测器设计)**

```haskell
observerDesign :: Matrix -> Matrix -> [Complex Double] -> Matrix
observerDesign a c desiredPoles = 
  let -- 对偶系统
      aDual = transpose a
      bDual = transpose c
      -- 极点配置
      kDual = polePlacement aDual bDual desiredPoles
      -- 观测器增益
      l = transpose kDual
  in l
```

## 频率域方法

### 7.1 频率响应

**定义 7.1 (频率响应)**
系统的频率响应定义为：
$$G(j\omega) = G(s)|_{s=j\omega}$$

**定义 7.2 (幅频特性)**
幅频特性定义为：
$$|G(j\omega)| = \sqrt{\text{Re}^2\{G(j\omega)\} + \text{Im}^2\{G(j\omega)\}}$$

**定义 7.3 (相频特性)**
相频特性定义为：
$$\angle G(j\omega) = \tan^{-1}\left(\frac{\text{Im}\{G(j\omega)\}}{\text{Re}\{G(j\omega)\}}\right)$$

### 7.2 Bode图

-**算法 7.1 (Bode图绘制)**

```haskell
bodePlot :: TransferFunction -> [Double] -> (Plot, Plot)
bodePlot g frequencies = 
  let magnitudeData = [(f, 20 * log10 (magnitude (g (0 :+ f)))) | f <- frequencies]
      phaseData = [(f, phase (g (0 :+ f)) * 180 / pi) | f <- frequencies]
  in (plot magnitudeData, plot phaseData)

magnitude :: Complex Double -> Double
magnitude z = sqrt ((realPart z)^2 + (imagPart z)^2)

phase :: Complex Double -> Double
phase z = atan2 (imagPart z) (realPart z)
```

### 7.3 Nyquist判据

**定理 7.1 (Nyquist稳定性判据)**
闭环系统稳定的充分必要条件是：
$$N = P - Z$$

其中：

- $N$ 是 $G(s)H(s)$ 的 Nyquist 图绕 $(-1, 0)$ 点的圈数
- $P$ 是开环系统在右半平面的极点数
- $Z$ 是闭环系统在右半平面的极点数

-**算法 7.2 (Nyquist图)**

```haskell
nyquistPlot :: TransferFunction -> [Double] -> Plot
nyquistPlot g frequencies = 
  let points = [g (0 :+ f) | f <- frequencies]
      realParts = [realPart p | p <- points]
      imagParts = [imagPart p | p <- points]
  in plot (zip realParts imagParts)
```

## 根轨迹方法

### 8.1 根轨迹定义

**定义 8.1 (根轨迹)**
根轨迹是系统特征方程：
$$1 + KG(s)H(s) = 0$$

当增益 $K$ 从 $0$ 变化到 $\infty$ 时，闭环极点在复平面上的轨迹。

### 8.2 根轨迹规则

-**规则 8.1 (根轨迹起点和终点)**

- 起点：$K = 0$ 时，根轨迹从开环极点开始
- 终点：$K = \infty$ 时，根轨迹趋向开环零点或无穷远

-**规则 8.2 (根轨迹分支数)**
根轨迹的分支数等于开环极点数。

-**规则 8.3 (实轴上的根轨迹)**
实轴上的根轨迹段满足：其右侧的开环极点和零点个数之和为奇数。

-**算法 8.1 (根轨迹绘制)**

```haskell
rootLocus :: TransferFunction -> [Double] -> Plot
rootLocus g gains = 
  let poles = [findRoots (1 + k * g) | k <- gains]
      realParts = [realPart p | ps <- poles, p <- ps]
      imagParts = [imagPart p | ps <- poles, p <- ps]
  in plot (zip realParts imagParts)

findRoots :: Polynomial -> [Complex Double]
findRoots poly = 
  let coeffs = polynomialCoefficients poly
      n = length coeffs - 1
      companionMatrix = buildCompanionMatrix coeffs
      eigenvalues = eigenValues companionMatrix
  in eigenvalues
```

## 应用实例

### 9.1 倒立摆控制

**系统建模：**
倒立摆系统的线性化模型：

```latex
$$\begin{bmatrix} \dot{x} \\ \dot{\theta} \\ \ddot{x} \\ \ddot{\theta} \end{bmatrix} =
\begin{bmatrix}
0 & 0 & 1 & 0 \\
0 & 0 & 0 & 1 \\
0 & -\frac{mg}{M} & 0 & 0 \\
0 & \frac{(M+m)g}{Ml} & 0 & 0
\end{bmatrix}
\begin{bmatrix} x \\ \theta \\ \dot{x} \\ \dot{\theta} \end{bmatrix} +
\begin{bmatrix} 0 \\ 0 \\ \frac{1}{M} \\ -\frac{1}{Ml} \end{bmatrix} u$$
```

**控制器设计：**

```haskell
invertedPendulumControl :: IO ()
invertedPendulumControl = do
  let -- 系统参数
      m = 0.1  -- 摆质量
      M = 1.0  -- 小车质量
      l = 0.5  -- 摆长
      g = 9.81 -- 重力加速度

      -- 系统矩阵
      a = matrixFromList [
        [0, 0, 1, 0],
        [0, 0, 0, 1],
        [0, -m*g/M, 0, 0],
        [0, (M+m)*g/(M*l), 0, 0]
      ]
      b = matrixFromList [[0], [0], [1/M], [-1/(M*l)]]
      c = matrixFromList [[1, 0, 0, 0], [0, 1, 0, 0]]

      -- 期望极点
      desiredPoles = [-2, -3, -4, -5]

      -- 状态反馈设计
      k = polePlacement a b desiredPoles

      -- 观测器设计
      observerPoles = [-6, -7, -8, -9]
      l = observerDesign a c observerPoles

  putStrLn "倒立摆控制系统设计完成"
  putStrLn $ "状态反馈增益: " ++ show k
  putStrLn $ "观测器增益: " ++ show l
```

### 9.2 直流电机控制

**系统建模：**

```latex
直流电机的传递函数：
$$G(s) = \frac{K_m}{s(Js + b)(Ls + R)}$$

其中：

- $K_m$ 是电机常数
- $J$ 是转动惯量
- $b$ 是阻尼系数
- $L$ 是电感
- $R$ 是电阻
```

**PID控制器设计：**

```haskell
dcMotorControl :: IO ()
dcMotorControl = do
  let -- 系统参数
      km = 0.1  -- 电机常数
      j = 0.01  -- 转动惯量
      b = 0.1   -- 阻尼系数
      l = 0.001 -- 电感
      r = 1.0   -- 电阻

      -- 传递函数
      g s = km / (s * (j*s + b) * (l*s + r))

      -- PID控制器
      kp = 100.0  -- 比例增益
      ki = 50.0   -- 积分增益
      kd = 10.0   -- 微分增益

      -- PID传递函数
      pid s = kp + ki/s + kd*s

      -- 闭环传递函数
      closedLoop s = (pid s * g s) / (1 + pid s * g s)

  putStrLn "直流电机PID控制系统设计完成"
  putStrLn $ "闭环传递函数: " ++ show (closedLoop (0 :+ 1))
```

### 9.3 温度控制系统

**系统建模：**
温度控制系统的传递函数：

```latex
$$G(s) = \frac{K}{Ts + 1} e^{-\tau s}$$

其中：

- $K$ 是系统增益
- $T$ 是时间常数
- $\tau$ 是时间延迟
```

**Smith预测器设计：**

```haskell
temperatureControl :: IO ()
temperatureControl = do
  let -- 系统参数
      k = 2.0   -- 系统增益
      t = 10.0  -- 时间常数
      tau = 2.0 -- 时间延迟

      -- 系统传递函数
      g s = k / (t*s + 1) * exp (-tau*s)

      -- Smith预测器
      g0 s = k / (t*s + 1)  -- 无延迟部分
      delay s = exp (-tau*s) -- 延迟部分

      -- 预测器控制器
      c s = 1.0 / g0 s  -- 理想控制器

      -- 闭环传递函数
      closedLoop s = (c s * g s) / (1 + c s * g s)

  putStrLn "温度控制系统Smith预测器设计完成"
  putStrLn $ "闭环传递函数: " ++ show (closedLoop (0 :+ 0.1))
```

### 9.4 飞行器姿态控制

**系统建模：**

```latex
飞行器姿态控制系统的状态空间模型：
$$\begin{bmatrix} \dot{\phi} \\ \dot{\theta} \\ \dot{\psi} \\ \dot{p} \\ \dot{q} \\ \dot{r} \end{bmatrix} =
\begin{bmatrix}
0 & 0 & 0 & 1 & 0 & 0 \\
0 & 0 & 0 & 0 & 1 & 0 \\
0 & 0 & 0 & 0 & 0 & 1 \\
0 & 0 & 0 & L_p & 0 & 0 \\
0 & 0 & 0 & 0 & M_q & 0 \\
0 & 0 & 0 & 0 & 0 & N_r
\end{bmatrix}
\begin{bmatrix} \phi \\ \theta \\ \psi \\ p \\ q \\ r \end{bmatrix} +
\begin{bmatrix}
0 & 0 & 0 \\
0 & 0 & 0 \\
0 & 0 & 0 \\
L_{\delta_a} & 0 & 0 \\
0 & M_{\delta_e} & 0 \\
0 & 0 & N_{\delta_r}
\end{bmatrix}
\begin{bmatrix} \delta_a \\ \delta_e \\ \delta_r \end{bmatrix}$$
```

**LQR控制器设计：**

```haskell
aircraftControl :: IO ()
aircraftControl = do
  let -- 系统参数
      lp = -0.5   -- 滚转阻尼
      mq = -0.8   -- 俯仰阻尼
      nr = -0.3   -- 偏航阻尼
      lda = 0.1   -- 副翼效率
      mde = -0.2  -- 升降舵效率
      ndr = 0.05  -- 方向舵效率

      -- 系统矩阵
      a = matrixFromList [
        [0, 0, 0, 1, 0, 0],
        [0, 0, 0, 0, 1, 0],
        [0, 0, 0, 0, 0, 1],
        [0, 0, 0, lp, 0, 0],
        [0, 0, 0, 0, mq, 0],
        [0, 0, 0, 0, 0, nr]
      ]
      b = matrixFromList [
        [0, 0, 0],
        [0, 0, 0],
        [0, 0, 0],
        [lda, 0, 0],
        [0, mde, 0],
        [0, 0, ndr]
      ]

      -- 权重矩阵
      q = diagonal [1.0, 1.0, 1.0, 0.1, 0.1, 0.1]  -- 状态权重
      r = diagonal [0.1, 0.1, 0.1]                  -- 控制权重

      -- LQR控制器设计
      k = lqr a b q r

  putStrLn "飞行器姿态控制系统LQR设计完成"
  putStrLn $ "LQR增益矩阵: " ++ show k
```

### 9.5 机器人路径跟踪控制

**系统建模：**

```latex
移动机器人的运动学模型：
$$\begin{bmatrix} \dot{x} \\ \dot{y} \\ \dot{\theta} \end{bmatrix} =
\begin{bmatrix}
\cos \theta & 0 \\
\sin \theta & 0 \\
0 & 1
\end{bmatrix}
\begin{bmatrix} v \\ \omega \end{bmatrix}$$
```

**非线性控制器设计：**

```haskell
robotPathTracking :: IO ()
robotPathTracking = do
  let -- 期望路径
      desiredPath t = (t, sin t)  -- 正弦路径

      -- 路径跟踪控制器
      pathTrackingController :: (Double, Double, Double) -> (Double, Double) -> (Double, Double)
      pathTrackingController (x, y, theta) (xd, yd) =
        let -- 位置误差
            ex = xd - x
            ey = yd - y

            -- 期望角度
            theta_d = atan2 (yd - y) (xd - x)

            -- 角度误差
            e_theta = theta_d - theta

            -- 控制律
            k1 = 2.0  -- 位置增益
            k2 = 3.0  -- 角度增益

            v = k1 * sqrt (ex^2 + ey^2)  -- 线速度
            omega = k2 * e_theta         -- 角速度
        in (v, omega)

      -- 仿真
      simulateRobot :: Double -> (Double, Double, Double) -> [(Double, Double, Double)]
      simulateRobot dt (x0, y0, theta0) =
        let timeSteps = [0, dt..10]  -- 10秒仿真
            initialState = (x0, y0, theta0)
        in scanl (\state t ->
               let (x, y, theta) = state
                   (xd, yd) = desiredPath t
                   (v, omega) = pathTrackingController state (xd, yd)
                   -- 欧拉积分
                   x' = x + v * cos theta * dt
                   y' = y + v * sin theta * dt
                   theta' = theta + omega * dt
               in (x', y', theta')) initialState timeSteps

  putStrLn "机器人路径跟踪控制系统设计完成"
  let trajectory = simulateRobot 0.01 (0, 0, 0)
  putStrLn $ "轨迹点数: " ++ show (length trajectory)
```

### 9.6 电力系统频率控制

**系统建模：**
电力系统的频率控制模型：
$$G(s) = \frac{1}{Ms + D}$$

其中：

- $M$ 是系统惯性常数
- $D$ 是阻尼系数

**自适应控制器设计：**

```haskell
powerSystemControl :: IO ()
powerSystemControl = do
  let -- 系统参数
      m = 10.0  -- 惯性常数
      d = 1.0   -- 阻尼系数

      -- 系统传递函数
      g s = 1 / (m*s + d)

      -- 自适应PID控制器
      adaptivePID :: Double -> Double -> Double -> Double -> Double -> Double
      adaptivePID error integral derivative kp ki kd =
        let -- 自适应增益调整
            kp' = kp * (1 + 0.1 * abs error)
            ki' = ki * (1 + 0.05 * abs integral)
            kd' = kd * (1 + 0.02 * abs derivative)

            -- PID控制律
            control = kp' * error + ki' * integral + kd' * derivative
        in control

      -- 频率控制仿真
      frequencyControl :: Double -> [Double]
      frequencyControl dt =
        let timeSteps = [0, dt..20]  -- 20秒仿真
            initialFrequency = 50.0  -- 初始频率50Hz
            desiredFrequency = 50.0  -- 期望频率50Hz

            -- 仿真循环
            simulate :: Double -> Double -> Double -> [Double]
            simulate t freq integral =
              let error = desiredFrequency - freq
                  derivative = 0  -- 简化处理
                  control = adaptivePID error integral derivative 1.0 0.5 0.1

                  -- 系统响应
                  freq' = freq + (control - d * freq) / m * dt
                  integral' = integral + error * dt
              in freq : simulate (t + dt) freq' integral'
        in simulate 0 initialFrequency 0

  putStrLn "电力系统频率控制系统设计完成"
  let frequencies = frequencyControl 0.01
  putStrLn $ "频率响应点数: " ++ show (length frequencies)
```

## 总结

经典控制理论为控制系统分析和设计提供了完整的理论框架，主要包括：

1. **系统建模**：建立动态系统的数学模型，包括状态空间和传递函数表示
2. **稳定性分析**：通过李雅普诺夫方法和特征值分析判断系统稳定性
3. **可控可观性**：分析系统的控制能力和观测能力
4. **控制器设计**：通过极点配置、观测器设计等方法设计反馈控制器
5. **频率域方法**：利用Bode图、Nyquist判据等频率域工具进行系统分析
6. **根轨迹方法**：通过根轨迹分析系统参数变化对性能的影响

经典控制理论为现代控制理论的发展奠定了基础，在工程实践中具有重要的应用价值。

## 参考文献

1. Ogata, K. (2010). *Modern control engineering*. Pearson.
2. Franklin, G. F., Powell, J. D., & Emami-Naeini, A. (2015). *Feedback control of dynamic systems*. Pearson.
3. Kuo, B. C., & Golnaraghi, F. (2003). *Automatic control systems*. John Wiley & Sons.
4. Dorf, R. C., Bishop, R. H. (2011). *Modern control systems*. Pearson.
5. Nise, N. S. (2015). *Control systems engineering*. John Wiley & Sons.
6. Åström, K. J., & Murray, R. M. (2021). *Feedback systems: an introduction for scientists and engineers*. Princeton University Press.
7. Skogestad, S., & Postlethwaite, I. (2005). *Multivariable feedback control: analysis and design*. John Wiley & Sons.
8. Doyle, J. C., Francis, B. A., & Tannenbaum, A. R. (2013). *Feedback control theory*. Courier Corporation.

---

**最后更新**：2024年12月19日  
**版本**：v1.0  
**维护者**：形式科学理论体系重构团队
