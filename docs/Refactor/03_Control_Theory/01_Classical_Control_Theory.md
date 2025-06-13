# 经典控制理论

(Classical Control Theory)

## 目录

- [经典控制理论](#经典控制理论)
  - [目录](#目录)
  - [1. 系统建模基础 (System Modeling Foundation)](#1-系统建模基础-system-modeling-foundation)
    - [1.1 线性时不变系统](#11-线性时不变系统)
    - [1.2 传递函数模型](#12-传递函数模型)
  - [2. 传递函数分析 (Transfer Function Analysis)](#2-传递函数分析-transfer-function-analysis)
    - [2.1 系统特性分析](#21-系统特性分析)
    - [2.2 频率响应分析](#22-频率响应分析)
  - [3. 稳定性分析 (Stability Analysis)](#3-稳定性分析-stability-analysis)
    - [3.1 稳定性定义](#31-稳定性定义)
    - [3.2 劳斯-赫尔维茨判据](#32-劳斯-赫尔维茨判据)
  - [4. 根轨迹法 (Root Locus Method)](#4-根轨迹法-root-locus-method)
    - [4.1 根轨迹定义](#41-根轨迹定义)
    - [4.2 根轨迹绘制规则](#42-根轨迹绘制规则)
  - [5. 频域分析 (Frequency Domain Analysis)](#5-频域分析-frequency-domain-analysis)
    - [5.1 奈奎斯特判据](#51-奈奎斯特判据)
    - [5.2 增益裕度和相位裕度](#52-增益裕度和相位裕度)
  - [6. 控制器设计 (Controller Design)](#6-控制器设计-controller-design)
    - [6.1 PID控制器](#61-pid控制器)
    - [6.2 超前-滞后补偿器](#62-超前-滞后补偿器)
  - [7. 应用领域](#7-应用领域)
    - [7.1 工业控制](#71-工业控制)
    - [7.2 航空航天](#72-航空航天)
    - [7.3 汽车工业](#73-汽车工业)
    - [7.4 电子系统](#74-电子系统)
  - [8. 批判分析](#8-批判分析)
    - [8.1 理论局限性](#81-理论局限性)
      - [8.1.1 线性假设](#811-线性假设)
      - [8.1.2 单输入单输出](#812-单输入单输出)
    - [8.2 设计挑战](#82-设计挑战)
      - [8.2.1 参数整定](#821-参数整定)
      - [8.2.2 模型不确定性](#822-模型不确定性)
    - [8.3 哲学问题](#83-哲学问题)
      - [8.3.1 因果性](#831-因果性)
      - [8.3.2 最优性](#832-最优性)
  - [9. 参考文献](#9-参考文献)

## 1. 系统建模基础 (System Modeling Foundation)

### 1.1 线性时不变系统

**定义 1.1.1 (线性时不变系统)**
线性时不变(LTI)系统是满足线性性和时不变性的动态系统：
$$\mathcal{S}: \mathbb{R}^n \times \mathbb{R}^m \rightarrow \mathbb{R}^p$$

满足：

1. **线性性**：$\mathcal{S}(\alpha x_1 + \beta x_2, u) = \alpha \mathcal{S}(x_1, u) + \beta \mathcal{S}(x_2, u)$
2. **时不变性**：$\mathcal{S}(x(t), u(t)) = \mathcal{S}(x(t-\tau), u(t-\tau))$

**定义 1.1.2 (状态空间模型)**
LTI系统的状态空间表示：
$$\dot{x}(t) = Ax(t) + Bu(t)$$
$$y(t) = Cx(t) + Du(t)$$

其中：

- $x(t) \in \mathbb{R}^n$ 是状态向量
- $u(t) \in \mathbb{R}^m$ 是输入向量
- $y(t) \in \mathbb{R}^p$ 是输出向量
- $A \in \mathbb{R}^{n \times n}$ 是系统矩阵
- $B \in \mathbb{R}^{n \times m}$ 是输入矩阵
- $C \in \mathbb{R}^{p \times n}$ 是输出矩阵
- $D \in \mathbb{R}^{p \times m}$ 是直接传递矩阵

**定理 1.1.1 (状态空间解)**
LTI系统的状态解为：
$$x(t) = e^{At}x(0) + \int_0^t e^{A(t-\tau)}Bu(\tau)d\tau$$

**证明：** 通过拉普拉斯变换：

```haskell
-- 线性时不变系统
data LTISystem = LTISystem
  { systemMatrix :: Matrix Double
  , inputMatrix :: Matrix Double
  , outputMatrix :: Matrix Double
  , directMatrix :: Matrix Double
  }

-- 状态空间模型
data StateSpace = StateSpace
  { state :: Vector Double
  , input :: Vector Double
  , output :: Vector Double
  }

-- 系统响应计算
systemResponse :: LTISystem -> StateSpace -> Double -> StateSpace
systemResponse system initialState t = 
  let A = systemMatrix system
      B = inputMatrix system
      C = outputMatrix system
      D = directMatrix system
      
      -- 状态转移矩阵
      stateTransition = matrixExp (A `multiply` t)
      
      -- 状态响应
      stateResponse = stateTransition `multiply` (state initialState)
      
      -- 输入响应
      inputResponse = convolution (matrixExp A) B (input initialState) t
      
      -- 总状态
      totalState = stateResponse + inputResponse
      
      -- 输出
      output = C `multiply` totalState + D `multiply` (input initialState)
  in StateSpace { state = totalState, input = input initialState, output = output }

-- 矩阵指数计算
matrixExp :: Matrix Double -> Matrix Double
matrixExp A = 
  let eigenvalues = eigenValues A
      eigenvectors = eigenVectors A
      expEigenvalues = map exp eigenvalues
      expMatrix = diagonalMatrix expEigenvalues
  in eigenvectors `multiply` expMatrix `multiply` (inverse eigenvectors)
```

### 1.2 传递函数模型

**定义 1.2.1 (传递函数)**
传递函数是系统输出与输入的拉普拉斯变换比：
$$G(s) = \frac{Y(s)}{U(s)} = \frac{b_n s^n + b_{n-1} s^{n-1} + \cdots + b_0}{a_n s^n + a_{n-1} s^{n-1} + \cdots + a_0}$$

**定义 1.2.2 (零极点形式)**
传递函数的零极点表示：
$$G(s) = K \frac{(s - z_1)(s - z_2) \cdots (s - z_m)}{(s - p_1)(s - p_2) \cdots (s - p_n)}$$

其中：

- $z_i$ 是零点
- $p_i$ 是极点
- $K$ 是增益

**定理 1.2.1 (状态空间到传递函数)**
状态空间模型到传递函数的转换：
$$G(s) = C(sI - A)^{-1}B + D$$

**证明：** 通过拉普拉斯变换：

```haskell
-- 传递函数
data TransferFunction = TransferFunction
  { numerator :: [Double]
  , denominator :: [Double]
  , zeros :: [Complex Double]
  , poles :: [Complex Double]
  , gain :: Double
  }

-- 状态空间到传递函数转换
stateSpaceToTransferFunction :: LTISystem -> TransferFunction
stateSpaceToTransferFunction system = 
  let A = systemMatrix system
      B = inputMatrix system
      C = outputMatrix system
      D = directMatrix system
      
      -- 特征多项式
      characteristicPoly = characteristicPolynomial A
      
      -- 传递函数分子
      numerator = transferFunctionNumerator A B C D
      
      -- 传递函数分母
      denominator = characteristicPoly
      
      -- 零极点
      zeros = findZeros numerator
      poles = findPoles denominator
      
      -- 增益
      gain = calculateGain numerator denominator
  in TransferFunction numerator denominator zeros poles gain

-- 特征多项式
characteristicPolynomial :: Matrix Double -> [Double]
characteristicPolynomial A = 
  let eigenvalues = eigenValues A
      n = size A
      poly = [1.0] ++ map (\i -> (-1)^i * elementarySymmetric i eigenvalues) [1..n]
  in reverse poly
```

## 2. 传递函数分析 (Transfer Function Analysis)

### 2.1 系统特性分析

**定义 2.1.1 (系统阶数)**
系统阶数是传递函数分母多项式的最高次数：
$$\text{Order}(G) = \deg(\text{denominator}(G))$$

**定义 2.1.2 (系统类型)**
系统类型是传递函数在原点的极点个数：
$$\text{Type}(G) = \text{number of poles at } s = 0$$

**定理 2.1.1 (稳态误差)**
对于单位阶跃输入，稳态误差为：
$$e_{ss} = \frac{1}{1 + K_p}$$

其中 $K_p$ 是位置误差常数。

**证明：** 通过终值定理：

```haskell
-- 系统特性分析
data SystemCharacteristics = SystemCharacteristics
  { order :: Int
  , systemType :: Int
  , steadyStateError :: Double
  , settlingTime :: Double
  , riseTime :: Double
  }

-- 系统特性计算
calculateSystemCharacteristics :: TransferFunction -> SystemCharacteristics
calculateSystemCharacteristics tf = 
  let order = length (denominator tf) - 1
      systemType = countPolesAtOrigin tf
      steadyStateError = calculateSteadyStateError tf
      settlingTime = calculateSettlingTime tf
      riseTime = calculateRiseTime tf
  in SystemCharacteristics order systemType steadyStateError settlingTime riseTime

-- 稳态误差计算
calculateSteadyStateError :: TransferFunction -> Double
calculateSteadyStateError tf = 
  let kp = positionErrorConstant tf
      ess = 1 / (1 + kp)
  in ess

-- 位置误差常数
positionErrorConstant :: TransferFunction -> Double
positionErrorConstant tf = 
  let s = 0
      gs = evaluateTransferFunction tf s
  in realPart gs
```

### 2.2 频率响应分析

**定义 2.2.1 (频率响应)**
频率响应是传递函数在虚轴上的值：
$$G(j\omega) = |G(j\omega)|e^{j\angle G(j\omega)}$$

**定义 2.2.2 (伯德图)**
伯德图是频率响应的对数幅频和相频特性：

- **幅频特性**：$20\log_{10}|G(j\omega)|$ vs $\log_{10}\omega$
- **相频特性**：$\angle G(j\omega)$ vs $\log_{10}\omega$

**定理 2.2.1 (频率响应特性)**
频率响应满足：
$$|G(j\omega)| = \sqrt{\text{Re}^2[G(j\omega)] + \text{Im}^2[G(j\omega)]}$$
$$\angle G(j\omega) = \tan^{-1}\left(\frac{\text{Im}[G(j\omega)]}{\text{Re}[G(j\omega)]}\right)$$

**证明：** 通过复数运算：

```haskell
-- 频率响应
data FrequencyResponse = FrequencyResponse
  { frequency :: Double
  , magnitude :: Double
  , phase :: Double
  , realPart :: Double
  , imaginaryPart :: Double
  }

-- 频率响应计算
calculateFrequencyResponse :: TransferFunction -> Double -> FrequencyResponse
calculateFrequencyResponse tf omega = 
  let s = 0 :+ omega
      gs = evaluateTransferFunction tf s
      magnitude = magnitude gs
      phase = phase gs
      realPart = realPart gs
      imaginaryPart = imagPart gs
  in FrequencyResponse omega magnitude phase realPart imaginaryPart

-- 伯德图生成
generateBodePlot :: TransferFunction -> [Double] -> [FrequencyResponse]
generateBodePlot tf frequencies = 
  map (calculateFrequencyResponse tf) frequencies

-- 伯德图绘制
plotBode :: TransferFunction -> IO ()
plotBode tf = do
  let frequencies = logspace (-2) 2 1000
      responses = generateBodePlot tf frequencies
      magnitudes = map (\r -> 20 * log10 (magnitude r)) responses
      phases = map (\r -> phase r * 180 / pi) responses
  plotMagnitude frequencies magnitudes
  plotPhase frequencies phases
```

## 3. 稳定性分析 (Stability Analysis)

### 3.1 稳定性定义

**定义 3.1.1 (渐近稳定性)**
系统是渐近稳定的，如果对于任意初始状态 $x(0)$，都有：
$$\lim_{t \rightarrow \infty} x(t) = 0$$

**定义 3.1.2 (有界输入有界输出稳定性)**
系统是BIBO稳定的，如果对于任意有界输入 $u(t)$，输出 $y(t)$ 都是有界的。

**定理 3.1.1 (稳定性判据)**
LTI系统渐近稳定的充分必要条件是所有特征值的实部都小于零：
$$\text{Re}(\lambda_i) < 0, \quad \forall i = 1, 2, \ldots, n$$

**证明：** 通过状态解分析：

```haskell
-- 稳定性分析
data StabilityAnalysis = StabilityAnalysis
  { isAsymptoticallyStable :: Bool
  , isBIBOStable :: Bool
  , eigenvalues :: [Complex Double]
  , stabilityMargin :: Double
  }

-- 稳定性检查
checkStability :: LTISystem -> StabilityAnalysis
checkStability system = 
  let A = systemMatrix system
      eigenvalues = eigenValues A
      isAsymptoticallyStable = all (\lambda -> realPart lambda < 0) eigenvalues
      isBIBOStable = checkBIBOStability system
      stabilityMargin = calculateStabilityMargin eigenvalues
  in StabilityAnalysis isAsymptoticallyStable isBIBOStable eigenvalues stabilityMargin

-- BIBO稳定性检查
checkBIBOStability :: LTISystem -> Bool
checkBIBOStability system = 
  let tf = stateSpaceToTransferFunction system
      poles = poles tf
      isBIBOStable = all (\pole -> realPart pole < 0) poles
  in isBIBOStable

-- 稳定性裕度计算
calculateStabilityMargin :: [Complex Double] -> Double
calculateStabilityMargin eigenvalues = 
  let realParts = map realPart eigenvalues
      minRealPart = minimum realParts
      stabilityMargin = abs minRealPart
  in stabilityMargin
```

### 3.2 劳斯-赫尔维茨判据

**定义 3.2.1 (劳斯表)**
劳斯表是判断多项式根分布的方法：

对于多项式 $P(s) = a_n s^n + a_{n-1} s^{n-1} + \cdots + a_0$，劳斯表为：

```text
$$\begin{array}{c|cccc}
s^n & a_n & a_{n-2} & a_{n-4} & \cdots \\
s^{n-1} & a_{n-1} & a_{n-3} & a_{n-5} & \cdots \\
s^{n-2} & b_1 & b_2 & b_3 & \cdots \\
s^{n-3} & c_1 & c_2 & c_3 & \cdots \\
\vdots & \vdots & \vdots & \vdots & \ddots
\end{array}$$
```

其中：
$$b_1 = \frac{a_{n-1}a_{n-2} - a_n a_{n-3}}{a_{n-1}}$$
$$c_1 = \frac{b_1 a_{n-3} - a_{n-1} b_2}{b_1}$$

**定理 3.2.1 (劳斯判据)**
多项式 $P(s)$ 的所有根都在左半平面的充分必要条件是劳斯表第一列的所有元素都同号。

**证明：** 通过劳斯表构造：

```haskell
-- 劳斯表
data RouthTable = RouthTable
  { coefficients :: [[Double]]
  , firstColumn :: [Double]
  }

-- 劳斯表构造
constructRouthTable :: [Double] -> RouthTable
constructRouthTable poly =
  let n = length poly - 1
      coefficients = buildRouthCoefficients poly n
      firstColumn = map head coefficients
  in RouthTable coefficients firstColumn

-- 劳斯系数计算
buildRouthCoefficients :: [Double] -> Int -> [[Double]]
buildRouthCoefficients poly n =
  let row1 = take (n + 1) poly
      row2 = take n (drop 1 poly)
      rows = [row1, row2] ++ buildRemainingRows row1 row2 n
  in rows

-- 劳斯判据
routhCriterion :: [Double] -> Bool
routhCriterion poly =
  let routhTable = constructRouthTable poly
      firstColumn = firstColumn routhTable
      allSameSign = allSameSign firstColumn
  in allSameSign

-- 同号检查
allSameSign :: [Double] -> Bool
allSameSign [] = True
allSameSign (x:xs) =
  let sign = signum x
  in all (\y -> signum y == sign) xs
```

## 4. 根轨迹法 (Root Locus Method)

### 4.1 根轨迹定义

**定义 4.1.1 (根轨迹)**
根轨迹是系统闭环极点随增益 $K$ 变化的轨迹：
$$1 + KG(s)H(s) = 0$$

**定义 4.1.2 (根轨迹方程)**
根轨迹满足的方程：
$$G(s)H(s) = -\frac{1}{K}$$

**定理 4.1.1 (根轨迹性质)**
根轨迹具有以下性质：

1. 起点：$K = 0$ 时，根轨迹从开环极点开始
2. 终点：$K = \infty$ 时，根轨迹趋向开环零点或无穷远
3. 分支数：等于开环极点数

**证明：** 通过根轨迹方程分析：

```haskell
-- 根轨迹
data RootLocus = RootLocus
  { openLoopPoles :: [Complex Double]
  , openLoopZeros :: [Complex Double]
  , gainValues :: [Double]
  , closedLoopPoles :: [[Complex Double]]
  }

-- 根轨迹计算
calculateRootLocus :: TransferFunction -> TransferFunction -> [Double] -> RootLocus
calculateRootLocus g h gains =
  let openLoopPoles = poles g
      openLoopZeros = zeros g
      closedLoopPoles = map (\k -> findClosedLoopPoles g h k) gains
  in RootLocus openLoopPoles openLoopZeros gains closedLoopPoles

-- 闭环极点计算
findClosedLoopPoles :: TransferFunction -> TransferFunction -> Double -> [Complex Double]
findClosedLoopPoles g h k =
  let characteristicEq = characteristicEquation g h k
      roots = findRoots characteristicEq
  in roots

-- 特征方程
characteristicEquation :: TransferFunction -> TransferFunction -> Double -> [Double]
characteristicEquation g h k =
  let numG = numerator g
      denG = denominator g
      numH = numerator h
      denH = denominator h

      -- 闭环特征多项式
      closedLoopNum = polynomialAdd (polynomialMultiply numG numH) (polynomialMultiply denG denH)
      closedLoopDen = polynomialMultiply denG denH

      -- 特征方程
      characteristicPoly = polynomialAdd closedLoopDen (polynomialScale k closedLoopNum)
  in characteristicPoly
```

### 4.2 根轨迹绘制规则

**定义 4.2.1 (根轨迹绘制规则)**
根轨迹绘制遵循以下规则：

1. **起点和终点**：从开环极点开始，趋向开环零点或无穷远
2. **分支数**：等于开环极点数
3. **实轴上的根轨迹**：实轴上根轨迹段右侧的实零极点个数为奇数
4. **渐近线**：$n - m$ 条渐近线，角度为 $\frac{(2k+1)\pi}{n-m}$
5. **分离点**：满足 $\frac{dK}{ds} = 0$

**定理 4.2.1 (根轨迹渐近线)**
根轨迹渐近线的中心点和角度为：
$$\sigma_a = \frac{\sum p_i - \sum z_i}{n - m}$$
$$\theta_a = \frac{(2k+1)\pi}{n-m}, \quad k = 0, 1, \ldots, n-m-1$$

**证明：** 通过根轨迹方程分析：

```haskell
-- 根轨迹绘制
data RootLocusPlot = RootLocusPlot
  { asymptotes :: [Asymptote]
  , breakawayPoints :: [Complex Double]
  , intersectionPoints :: [Complex Double]
  }

-- 渐近线计算
calculateAsymptotes :: RootLocus -> [Asymptote]
calculateAsymptotes rootLocus =
  let poles = openLoopPoles rootLocus
      zeros = openLoopZeros rootLocus
      n = length poles
      m = length zeros

      -- 渐近线中心
      center = (sum poles - sum zeros) / fromIntegral (n - m)

      -- 渐近线角度
      angles = map (\k -> (2 * k + 1) * pi / fromIntegral (n - m)) [0..(n-m-1)]

      asymptotes = map (\angle -> Asymptote center angle) angles
  in asymptotes

-- 分离点计算
calculateBreakawayPoints :: RootLocus -> [Complex Double]
calculateBreakawayPoints rootLocus =
  let g = transferFunctionFromRootLocus rootLocus
      h = unityFeedback
      dKds = derivativeK g h
      breakawayPoints = findRoots dKds
  in breakawayPoints

-- 根轨迹绘制
plotRootLocus :: RootLocus -> IO ()
plotRootLocus rootLocus = do
  let gains = gainValues rootLocus
      poles = closedLoopPoles rootLocus

      -- 绘制根轨迹
      plotTrajectories poles

      -- 绘制渐近线
      asymptotes = calculateAsymptotes rootLocus
      plotAsymptotes asymptotes

      -- 绘制分离点
      breakawayPoints = calculateBreakawayPoints rootLocus
      plotBreakawayPoints breakawayPoints
```

## 5. 频域分析 (Frequency Domain Analysis)

### 5.1 奈奎斯特判据

**定义 5.1.1 (奈奎斯特判据)**
奈奎斯特判据通过开环频率响应判断闭环稳定性：
$$N = P - Z$$

其中：

- $N$ 是奈奎斯特图包围 $(-1, 0)$ 点的圈数
- $P$ 是开环不稳定极点数
- $Z$ 是闭环不稳定极点数

**定义 5.1.2 (奈奎斯特图)**
奈奎斯特图是开环频率响应 $G(j\omega)H(j\omega)$ 的极坐标图。

**定理 5.1.1 (奈奎斯特稳定性判据)**
闭环系统稳定的充分必要条件是：
$$Z = P - N = 0$$

**证明：** 通过幅角原理：

```haskell
-- 奈奎斯特分析
data NyquistAnalysis = NyquistAnalysis
  { openLoopResponse :: [Complex Double]
  , encirclements :: Int
  , openLoopUnstablePoles :: Int
  , closedLoopStability :: Bool
  }

-- 奈奎斯特分析
performNyquistAnalysis :: TransferFunction -> TransferFunction -> NyquistAnalysis
performNyquistAnalysis g h =
  let frequencies = logspace (-3) 3 1000
      openLoopResponse = map (\omega -> evaluateOpenLoop g h omega) frequencies
      encirclements = countEncirclements openLoopResponse
      openLoopUnstablePoles = countUnstablePoles g
      closedLoopStability = encirclements == openLoopUnstablePoles
  in NyquistAnalysis openLoopResponse encirclements openLoopUnstablePoles closedLoopStability

-- 包围圈数计算
countEncirclements :: [Complex Double] -> Int
countEncirclements response =
  let criticalPoint = (-1) :+ 0
      encirclements = countWindingNumber response criticalPoint
  in encirclements

-- 开环频率响应
evaluateOpenLoop :: TransferFunction -> TransferFunction -> Double -> Complex Double
evaluateOpenLoop g h omega =
  let s = 0 :+ omega
      gs = evaluateTransferFunction g s
      hs = evaluateTransferFunction h s
  in gs * hs
```

### 5.2 增益裕度和相位裕度

**定义 5.2.1 (增益裕度)**
增益裕度是系统稳定性的度量：
$$GM = \frac{1}{|G(j\omega_{pc})H(j\omega_{pc})|}$$

其中 $\omega_{pc}$ 是相位穿越频率。

**定义 5.2.2 (相位裕度)**
相位裕度是系统稳定性的度量：
$$PM = 180^\circ + \angle G(j\omega_{gc})H(j\omega_{gc})$$

其中 $\omega_{gc}$ 是增益穿越频率。

**定理 5.2.1 (稳定性裕度)**
系统稳定的充分条件是：
$$GM > 1 \quad \text{and} \quad PM > 0$$

**证明：** 通过奈奎斯特判据：

```haskell
-- 稳定性裕度
data StabilityMargins = StabilityMargins
  { gainMargin :: Double
  , phaseMargin :: Double
  , gainCrossoverFreq :: Double
  , phaseCrossoverFreq :: Double
  }

-- 稳定性裕度计算
calculateStabilityMargins :: TransferFunction -> TransferFunction -> StabilityMargins
calculateStabilityMargins g h =
  let gainCrossoverFreq = findGainCrossoverFrequency g h
      phaseCrossoverFreq = findPhaseCrossoverFrequency g h

      gainMargin = calculateGainMargin g h phaseCrossoverFreq
      phaseMargin = calculatePhaseMargin g h gainCrossoverFreq
  in StabilityMargins gainMargin phaseMargin gainCrossoverFreq phaseCrossoverFreq

-- 增益裕度计算
calculateGainMargin :: TransferFunction -> TransferFunction -> Double -> Double
calculateGainMargin g h omega =
  let s = 0 :+ omega
      gh = evaluateOpenLoop g h omega
      magnitude = magnitude gh
      gainMargin = 1 / magnitude
  in gainMargin

-- 相位裕度计算
calculatePhaseMargin :: TransferFunction -> TransferFunction -> Double -> Double
calculatePhaseMargin g h omega =
  let s = 0 :+ omega
      gh = evaluateOpenLoop g h omega
      phase = phase gh
      phaseMargin = 180 + phase * 180 / pi
  in phaseMargin
```

## 6. 控制器设计 (Controller Design)

### 6.1 PID控制器

**定义 6.1.1 (PID控制器)**
PID控制器的传递函数：
$$G_c(s) = K_p + \frac{K_i}{s} + K_d s$$

其中：

- $K_p$ 是比例增益
- $K_i$ 是积分增益
- $K_d$ 是微分增益

**定义 6.1.2 (PID参数整定)**
PID参数整定方法包括：

1. **齐格勒-尼科尔斯方法**
2. **科恩-库恩方法**
3. **内模控制方法**

**定理 6.1.1 (PID稳定性)**
PID控制器能够改善系统稳定性，但需要合理选择参数。

**证明：** 通过根轨迹分析：

```haskell
-- PID控制器
data PIDController = PIDController
  { proportionalGain :: Double
  , integralGain :: Double
  , derivativeGain :: Double
  }

-- PID控制器传递函数
pidTransferFunction :: PIDController -> TransferFunction
pidTransferFunction pid =
  let kp = proportionalGain pid
      ki = integralGain pid
      kd = derivativeGain pid

      -- PID传递函数
      numerator = [kd, kp, ki]
      denominator = [1, 0]
  in TransferFunction numerator denominator [] [] 1.0

-- 齐格勒-尼科尔斯整定
zieglerNicholsTuning :: TransferFunction -> PIDController
zieglerNicholsTuning plant =
  let (ku, tu) = findUltimateGainAndPeriod plant
      kp = 0.6 * ku
      ki = 1.2 * ku / tu
      kd = 0.075 * ku * tu
  in PIDController kp ki kd

-- 极限增益和周期
findUltimateGainAndPeriod :: TransferFunction -> (Double, Double)
findUltimateGainAndPeriod plant =
  let -- 寻找使系统产生持续振荡的增益
      ku = findUltimateGain plant
      tu = findUltimatePeriod plant
  in (ku, tu)
```

### 6.2 超前-滞后补偿器

**定义 6.2.1 (超前补偿器)**
超前补偿器的传递函数：
$$G_c(s) = K \frac{s + z}{s + p}, \quad z < p$$

**定义 6.2.2 (滞后补偿器)**
滞后补偿器的传递函数：
$$G_c(s) = K \frac{s + z}{s + p}, \quad z > p$$

**定理 6.2.1 (补偿器设计)**
超前补偿器提高相位裕度，滞后补偿器改善稳态误差。

**证明：** 通过频率响应分析：

```haskell
-- 补偿器
data Compensator =
  LeadCompensator Double Double Double
  | LagCompensator Double Double Double

-- 超前补偿器
leadCompensator :: Double -> Double -> Double -> TransferFunction
leadCompensator k z p =
  let numerator = [k, k * z]
      denominator = [1, p]
  in TransferFunction numerator denominator [] [] 1.0

-- 滞后补偿器
lagCompensator :: Double -> Double -> Double -> TransferFunction
lagCompensator k z p =
  let numerator = [k, k * z]
      denominator = [1, p]
  in TransferFunction numerator denominator [] [] 1.0

-- 补偿器设计
designCompensator :: TransferFunction -> Compensator
designCompensator plant =
  let stabilityMargins = calculateStabilityMargins plant unityFeedback
      phaseMargin = phaseMargin stabilityMargins

      if phaseMargin < 45
      then -- 需要超前补偿
        let requiredPhase = 45 - phaseMargin
            (k, z, p) = designLeadCompensator plant requiredPhase
        in LeadCompensator k z p
      else -- 需要滞后补偿
        let (k, z, p) = designLagCompensator plant
        in LagCompensator k z p

-- 超前补偿器设计
designLeadCompensator :: TransferFunction -> Double -> (Double, Double, Double)
designLeadCompensator plant requiredPhase =
  let -- 根据所需相位设计参数
      alpha = (1 - sin (requiredPhase * pi / 180)) / (1 + sin (requiredPhase * pi / 180))
      omega = findCrossoverFrequency plant
      z = omega / sqrt alpha
      p = omega * sqrt alpha
      k = 1 / sqrt alpha
  in (k, z, p)
```

## 7. 应用领域

### 7.1 工业控制

- **过程控制**: 化工、石油、电力等工业过程
- **运动控制**: 机器人、数控机床、伺服系统
- **温度控制**: 加热、制冷、恒温系统
- **流量控制**: 液体、气体流量控制

### 7.2 航空航天

- **飞行控制**: 飞机、导弹、卫星的姿态控制
- **导航系统**: 惯性导航、GPS导航
- **推进系统**: 发动机控制、推力控制
- **制导系统**: 目标跟踪、路径规划

### 7.3 汽车工业

- **发动机控制**: 燃油喷射、点火控制
- **制动系统**: 防抱死制动、电子稳定控制
- **转向系统**: 电动助力转向、四轮转向
- **悬架系统**: 主动悬架、自适应悬架

### 7.4 电子系统

- **电源控制**: 开关电源、线性稳压器
- **通信系统**: 调制解调、同步控制
- **音频系统**: 音量控制、均衡器
- **显示系统**: 亮度控制、对比度控制

## 8. 批判分析

### 8.1 理论局限性

#### 8.1.1 线性假设

**批判 8.1.1** (线性假设) 经典控制理论基于线性系统假设，无法处理强非线性系统。

**分析** 线性假设的限制：

- 无法处理饱和、死区等非线性特性
- 无法处理时变系统
- 无法处理多模态系统
- 实际系统往往具有非线性特性

#### 8.1.2 单输入单输出

**批判 8.1.2** (SISO限制) 经典控制理论主要针对单输入单输出系统。

**分析** SISO限制的问题：

- 无法处理多变量系统
- 无法处理耦合效应
- 无法处理分布式系统
- 现代系统往往具有多变量特性

### 8.2 设计挑战

#### 8.2.1 参数整定

**批判 8.2.1** (参数整定) 控制器参数整定需要经验和试错。

**分析** 参数整定的挑战：

- 缺乏系统化的整定方法
- 参数之间相互影响
- 性能指标难以量化
- 鲁棒性要求难以满足

#### 8.2.2 模型不确定性

**批判 8.2.2** (模型不确定性) 实际系统模型往往存在不确定性。

**分析** 模型不确定性的影响：

- 参数变化影响控制性能
- 未建模动态导致不稳定
- 外部扰动影响控制效果
- 传感器噪声影响测量精度

### 8.3 哲学问题

#### 8.3.1 因果性

**问题 8.3.1** (因果性) 控制理论中的因果关系是什么？

**分析** 因果性的哲学问题：

- **决定论**: 系统行为是否完全由输入决定？
- **自由意志**: 控制器是否具有自主性？
- **目的论**: 控制目标是否具有目的性？

#### 8.3.2 最优性

**问题 8.3.2** (最优性) 什么是最优控制？

**分析** 最优性的哲学问题：

- **目标函数**: 如何定义最优性？
- **约束条件**: 如何处理约束？
- **多目标**: 如何处理多个目标？

## 9. 参考文献

1. **基础理论**: Ogata, K. (2010). Modern Control Engineering
2. **稳定性分析**: Khalil, H.K. (2002). Nonlinear Systems
3. **控制器设计**: Franklin, G.F. et al. (2015). Feedback Control of Dynamic Systems
4. **频域方法**: Bode, H.W. (1945). Network Analysis and Feedback Amplifier Design
5. **根轨迹法**: Evans, W.R. (1948). Graphical Analysis of Control Systems

---

*本文档将持续更新和完善*
