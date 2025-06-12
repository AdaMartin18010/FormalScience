# 控制理论基础 (Control Theory Foundation)

## 目录

1. [系统基础定义](#1-系统基础定义)
2. [线性系统理论](#2-线性系统理论)
3. [稳定性理论](#3-稳定性理论)
4. [可控性与可观性](#4-可控性与可观性)
5. [基本控制方法](#5-基本控制方法)
6. [系统分析与设计](#6-系统分析与设计)
7. [参考文献](#7-参考文献)

## 1. 系统基础定义

### 1.1 动态系统

**定义 1.1 (动态系统)**
动态系统是一个五元组 $\Sigma = (X, U, Y, f, h)$，其中：

- $X \subseteq \mathbb{R}^n$ 是状态空间
- $U \subseteq \mathbb{R}^m$ 是输入空间  
- $Y \subseteq \mathbb{R}^p$ 是输出空间
- $f : X \times U \times \mathbb{R} \rightarrow X$ 是状态转移函数
- $h : X \times U \times \mathbb{R} \rightarrow Y$ 是输出函数

**定义 1.2 (连续时间系统)**
连续时间系统的状态方程：
$$\dot{x}(t) = f(x(t), u(t), t)$$
$$y(t) = h(x(t), u(t), t)$$

**定义 1.3 (离散时间系统)**
离散时间系统的状态方程：
$$x(k+1) = f(x(k), u(k), k)$$
$$y(k) = h(x(k), u(k), k)$$

**定义 1.4 (自治系统)**
自治系统是不依赖外部输入的系统：
$$\dot{x}(t) = f(x(t))$$

### 1.2 系统分类

**定义 1.5 (线性系统)**
系统是线性的，如果满足叠加原理：
$$f(\alpha x_1 + \beta x_2, \alpha u_1 + \beta u_2, t) = \alpha f(x_1, u_1, t) + \beta f(x_2, u_2, t)$$

**定义 1.6 (时不变系统)**
系统是时不变的，如果：
$$f(x, u, t) = f(x, u, 0) \text{ for all } t$$

**定义 1.7 (线性时不变系统)**
线性时不变(LTI)系统的状态空间表示：
$$\dot{x}(t) = Ax(t) + Bu(t)$$
$$y(t) = Cx(t) + Du(t)$$

其中 $A \in \mathbb{R}^{n \times n}$, $B \in \mathbb{R}^{n \times m}$, $C \in \mathbb{R}^{p \times n}$, $D \in \mathbb{R}^{p \times m}$。

### 1.3 系统解

**定理 1.1 (线性系统解)**
线性时不变系统的解为：
$$x(t) = e^{At}x(0) + \int_0^t e^{A(t-\tau)}Bu(\tau)d\tau$$

**证明：** 通过状态方程的积分：

1. 齐次方程 $\dot{x} = Ax$ 的解为 $x(t) = e^{At}x(0)$
2. 非齐次方程通过变分常数法求解
3. 利用卷积积分得到完整解

**定义 1.8 (状态转移矩阵)**
状态转移矩阵 $\Phi(t, t_0)$ 定义为：
$$\Phi(t, t_0) = e^{A(t-t_0)}$$

满足：
$$\frac{d}{dt}\Phi(t, t_0) = A\Phi(t, t_0), \quad \Phi(t_0, t_0) = I$$

## 2. 线性系统理论

### 2.1 传递函数

**定义 2.1 (传递函数)**
线性时不变系统的传递函数：
$$G(s) = C(sI - A)^{-1}B + D$$

**定理 2.1 (传递函数性质)**
传递函数 $G(s)$ 是 $s$ 的有理函数，其极点等于矩阵 $A$ 的特征值。

**证明：** 通过拉普拉斯变换：

1. 对状态方程进行拉普拉斯变换
2. 求解状态变量的拉普拉斯变换
3. 代入输出方程得到传递函数

**定义 2.2 (极点与零点)**
传递函数 $G(s) = \frac{N(s)}{D(s)}$ 的：
- 极点是 $D(s) = 0$ 的根
- 零点是 $N(s) = 0$ 的根

### 2.2 系统响应

**定义 2.3 (脉冲响应)**
系统的脉冲响应：
$$g(t) = \mathcal{L}^{-1}\{G(s)\} = Ce^{At}B + D\delta(t)$$

**定义 2.4 (阶跃响应)**
系统的阶跃响应：
$$y(t) = \int_0^t g(\tau)d\tau$$

**定理 2.2 (终值定理)**
如果 $\lim_{s \rightarrow 0} sG(s)$ 存在，则：
$$\lim_{t \rightarrow \infty} y(t) = \lim_{s \rightarrow 0} sG(s)$$

### 2.3 系统连接

**定义 2.5 (串联连接)**
两个系统 $G_1(s)$ 和 $G_2(s)$ 的串联：
$$G_{series}(s) = G_2(s)G_1(s)$$

**定义 2.6 (并联连接)**
两个系统 $G_1(s)$ 和 $G_2(s)$ 的并联：
$$G_{parallel}(s) = G_1(s) + G_2(s)$$

**定义 2.7 (反馈连接)**
系统 $G(s)$ 和 $H(s)$ 的反馈连接：
$$G_{feedback}(s) = \frac{G(s)}{1 + G(s)H(s)}$$

## 3. 稳定性理论

### 3.1 李雅普诺夫稳定性

**定义 3.1 (平衡点)**
状态 $x_e \in X$ 是平衡点，如果 $f(x_e, 0, t) = 0$ 对于所有 $t$。

**定义 3.2 (李雅普诺夫稳定性)**
平衡点 $x_e$ 是李雅普诺夫稳定的，如果对于任意 $\epsilon > 0$，存在 $\delta > 0$ 使得：
$$\|x(0) - x_e\| < \delta \Rightarrow \|x(t) - x_e\| < \epsilon \text{ for all } t \geq 0$$

**定义 3.3 (渐近稳定性)**
平衡点 $x_e$ 是渐近稳定的，如果它是李雅普诺夫稳定的且：
$$\lim_{t \rightarrow \infty} x(t) = x_e$$

**定义 3.4 (指数稳定性)**
平衡点 $x_e$ 是指数稳定的，如果存在常数 $M, \alpha > 0$ 使得：
$$\|x(t) - x_e\| \leq M\|x(0) - x_e\|e^{-\alpha t}$$

**定理 3.1 (李雅普诺夫直接法)**
如果存在连续可微函数 $V : X \rightarrow \mathbb{R}$ 满足：

1. $V(x_e) = 0$
2. $V(x) > 0$ 对于 $x \neq x_e$
3. $\dot{V}(x) \leq 0$ 对于 $x \neq x_e$

则平衡点 $x_e$ 是李雅普诺夫稳定的。

**证明：** 通过李雅普诺夫函数的单调性：

1. $V(x)$ 在平衡点附近有下界
2. $\dot{V}(x) \leq 0$ 确保 $V(x)$ 不增加
3. 因此状态轨迹保持在平衡点附近

**定理 3.2 (李雅普诺夫渐近稳定性)**
如果存在连续可微函数 $V : X \rightarrow \mathbb{R}$ 满足：

1. $V(x_e) = 0$
2. $V(x) > 0$ 对于 $x \neq x_e$
3. $\dot{V}(x) < 0$ 对于 $x \neq x_e$

则平衡点 $x_e$ 是渐近稳定的。

### 3.2 线性系统稳定性

**定理 3.3 (线性系统稳定性)**
线性系统 $\dot{x} = Ax$ 的零平衡点是渐近稳定的当且仅当 $A$ 的所有特征值都有负实部。

**证明：** 通过特征值分解：

1. $A$ 的特征值决定系统动态
2. 负实部特征值对应衰减模态
3. 正实部特征值对应增长模态

**定义 3.5 (赫尔维茨判据)**
多项式 $p(s) = a_n s^n + a_{n-1} s^{n-1} + \cdots + a_0$ 是赫尔维茨的，如果所有根都有负实部。

**算法 3.1 (赫尔维茨判据)**

```haskell
hurwitzCriterion :: [Double] -> Bool
hurwitzCriterion coeffs = 
  let n = length coeffs - 1
      hurwitzMatrix = buildHurwitzMatrix coeffs
      minors = [determinant (submatrix hurwitzMatrix i) | i <- [1..n]]
  in all (> 0) minors

buildHurwitzMatrix :: [Double] -> Matrix Double
buildHurwitzMatrix coeffs = 
  let n = length coeffs - 1
      matrix = matrix n n (\(i, j) -> 
        if j <= i && i - j < length coeffs 
        then coeffs !! (i - j) 
        else 0.0)
  in matrix
```

**定义 3.6 (劳斯判据)**
劳斯表的第一列符号变化次数等于右半平面根的个数。

## 4. 可控性与可观性

### 4.1 可控性

**定义 4.1 (可控性)**
系统 $\Sigma$ 在时间 $T$ 内可控，如果对于任意初始状态 $x_0$ 和目标状态 $x_f$，存在输入 $u(t)$ 使得 $x(T) = x_f$。

**定义 4.2 (可控性矩阵)**
线性系统的可控性矩阵：
$$\mathcal{C} = [B \quad AB \quad A^2B \quad \cdots \quad A^{n-1}B]$$

**定理 4.1 (可控性判据)**
线性系统完全可控当且仅当可控性矩阵 $\mathcal{C}$ 满秩。

**证明：** 通过凯莱-哈密顿定理：

1. 可控性矩阵的列空间包含可达状态空间
2. 满秩确保可达整个状态空间
3. 凯莱-哈密顿定理限制矩阵幂的线性相关性

**定义 4.3 (可控性标准形)**
可控系统可以变换为标准形：
$$\dot{z} = \begin{bmatrix} 
0 & 1 & 0 & \cdots & 0 \\
0 & 0 & 1 & \cdots & 0 \\
\vdots & \vdots & \vdots & \ddots & \vdots \\
0 & 0 & 0 & \cdots & 1 \\
-a_0 & -a_1 & -a_2 & \cdots & -a_{n-1}
\end{bmatrix} z + \begin{bmatrix} 0 \\ 0 \\ \vdots \\ 0 \\ 1 \end{bmatrix} u$$

### 4.2 可观性

**定义 4.4 (可观性)**
系统 $\Sigma$ 可观，如果任意初始状态 $x_0$ 都可以通过输出 $y(t)$ 唯一确定。

**定义 4.5 (可观性矩阵)**
线性系统的可观性矩阵：
$$\mathcal{O} = \begin{bmatrix} C \\ CA \\ CA^2 \\ \vdots \\ CA^{n-1} \end{bmatrix}$$

**定理 4.2 (可观性判据)**
线性系统完全可观当且仅当可观性矩阵 $\mathcal{O}$ 满秩。

**证明：** 通过输出方程：

1. 可观性矩阵的行空间包含可观测状态空间
2. 满秩确保状态唯一确定
3. 输出序列包含足够信息重构状态

**定义 4.6 (可观性标准形)**
可观系统可以变换为标准形：
$$\dot{z} = \begin{bmatrix} 
0 & 0 & \cdots & 0 & -a_0 \\
1 & 0 & \cdots & 0 & -a_1 \\
0 & 1 & \cdots & 0 & -a_2 \\
\vdots & \vdots & \ddots & \vdots & \vdots \\
0 & 0 & \cdots & 1 & -a_{n-1}
\end{bmatrix} z + \begin{bmatrix} b_0 \\ b_1 \\ b_2 \\ \vdots \\ b_{n-1} \end{bmatrix} u$$
$$y = [0 \quad 0 \quad \cdots \quad 0 \quad 1] z$$

### 4.3 卡尔曼分解

**定理 4.3 (卡尔曼分解)**
任何线性系统都可以分解为四个子系统：

1. **可控可观**：$(A_{co}, B_{co}, C_{co})$
2. **可控不可观**：$(A_{c\bar{o}}, B_{c\bar{o}}, C_{c\bar{o}})$
3. **不可控可观**：$(A_{\bar{c}o}, B_{\bar{c}o}, C_{\bar{c}o})$
4. **不可控不可观**：$(A_{\bar{c}\bar{o}}, B_{\bar{c}\bar{o}}, C_{\bar{c}\bar{o}})$

**证明：** 通过相似变换：

1. 构造可控性和可观性子空间
2. 利用子空间的正交性
3. 通过相似变换得到标准分解

## 5. 基本控制方法

### 5.1 状态反馈

**定义 5.1 (状态反馈)**
状态反馈控制律：
$$u(t) = -Kx(t) + r(t)$$

其中 $K \in \mathbb{R}^{m \times n}$ 是反馈增益矩阵，$r(t)$ 是参考输入。

**定理 5.1 (极点配置)**
如果系统 $(A, B)$ 可控，则可以通过状态反馈任意配置闭环极点。

**证明：** 通过可控性标准形：

1. 可控系统可以变换为标准形
2. 标准形下极点配置直接可得
3. 变换回原坐标系得到反馈增益

**算法 5.1 (极点配置)**

```haskell
polePlacement :: Matrix Double -> Matrix Double -> [Complex Double] -> Matrix Double
polePlacement a b desiredPoles = 
  let controllableForm = toControllableForm a b
      kStandard = placePoles controllableForm desiredPoles
      transformation = getTransformation a b
  in kStandard * transformation

toControllableForm :: Matrix Double -> Matrix Double -> (Matrix Double, Matrix Double, Matrix Double)
toControllableForm a b = 
  let controllabilityMatrix = buildControllabilityMatrix a b
      transformation = controllabilityMatrix
      aNew = inverse transformation `multiply` a `multiply` transformation
      bNew = inverse transformation `multiply` b
  in (aNew, bNew, transformation)
```

### 5.2 输出反馈

**定义 5.2 (输出反馈)**
输出反馈控制律：
$$u(t) = -Ky(t) + r(t)$$

**定理 5.2 (输出反馈限制)**
输出反馈不能任意配置极点，只能配置可观部分的极点。

**证明：** 通过可观性分解：

1. 系统可以分解为可观和不可观部分
2. 输出反馈只能影响可观部分
3. 不可观部分的极点无法通过输出反馈改变

### 5.3 观测器设计

**定义 5.3 (全维观测器)**
全维观测器：
$$\dot{\hat{x}}(t) = A\hat{x}(t) + Bu(t) + L(y(t) - C\hat{x}(t))$$

其中 $L \in \mathbb{R}^{n \times p}$ 是观测器增益矩阵。

**定理 5.3 (观测器极点配置)**
如果系统 $(A, C)$ 可观，则可以通过选择 $L$ 任意配置观测器极点。

**证明：** 通过可观性对偶性：

1. $(A, C)$ 可观等价于 $(A^T, C^T)$ 可控
2. 观测器极点配置等价于状态反馈极点配置
3. 通过对偶性得到观测器增益

**定义 5.4 (观测误差)**
观测误差：
$$e(t) = x(t) - \hat{x}(t)$$

观测误差动态：
$$\dot{e}(t) = (A - LC)e(t)$$

### 5.4 分离原理

**定理 5.4 (分离原理)**
对于线性系统，状态反馈控制器和观测器可以独立设计，然后组合使用。

**证明：** 通过闭环系统分析：

1. 闭环系统可以分解为状态反馈部分和观测器部分
2. 两部分独立设计不影响整体性能
3. 闭环极点等于状态反馈极点和观测器极点的并集

## 6. 系统分析与设计

### 6.1 性能指标

**定义 6.1 (稳态误差)**
稳态误差：
$$e_{ss} = \lim_{t \rightarrow \infty} e(t)$$

**定义 6.2 (超调量)**
超调量：
$$M_p = \frac{y_{max} - y_{ss}}{y_{ss}} \times 100\%$$

**定义 6.3 (调节时间)**
调节时间：输出进入稳态值±2%范围内的时间。

**定义 6.4 (上升时间)**
上升时间：输出从10%到90%稳态值的时间。

### 6.2 根轨迹法

**定义 6.5 (根轨迹)**
根轨迹是闭环极点随增益变化的轨迹。

**根轨迹规则：**

1. **起点**：$K = 0$ 时，根轨迹从开环极点开始
2. **终点**：$K = \infty$ 时，根轨迹趋向开环零点或无穷远
3. **分支数**：等于开环极点数
4. **对称性**：关于实轴对称
5. **渐近线**：$n - m$ 条渐近线，角度为 $\frac{(2k+1)\pi}{n-m}$

**算法 6.1 (根轨迹绘制)**

```haskell
rootLocus :: TransferFunction -> [Double] -> [(Complex Double, Double)]
rootLocus tf gains = 
  let openLoopPoles = poles tf
      openLoopZeros = zeros tf
      rootLocusPoints = [findClosedLoopPoles tf k | k <- gains]
  in zip rootLocusPoints gains
```

### 6.3 频域分析

**定义 6.6 (频率响应)**
系统的频率响应：
$$G(j\omega) = |G(j\omega)|e^{j\angle G(j\omega)}$$

**定义 6.7 (伯德图)**
伯德图是幅频特性和相频特性的对数坐标图。

**定义 6.8 (奈奎斯特判据)**
闭环系统稳定的充分必要条件是奈奎斯特图不包围点 $(-1, 0)$。

**定理 6.1 (奈奎斯特稳定性判据)**
对于开环稳定的系统，闭环系统稳定的充分必要条件是：
$$N = P$$

其中 $N$ 是奈奎斯特图包围 $(-1, 0)$ 的次数，$P$ 是开环不稳定极点数。

## 7. 参考文献

1. Ogata, K. (2010). Modern Control Engineering (5th ed.). Prentice Hall.
2. Franklin, G. F., Powell, J. D., & Emami-Naeini, A. (2015). Feedback Control of Dynamic Systems (7th ed.). Pearson.
3. Doyle, J. C., Francis, B. A., & Tannenbaum, A. R. (2013). Feedback Control Theory. Dover Publications.
4. Kailath, T. (1980). Linear Systems. Prentice Hall.
5. Chen, C. T. (1999). Linear System Theory and Design (3rd ed.). Oxford University Press.
6. Åström, K. J., & Murray, R. M. (2021). Feedback Systems: An Introduction for Scientists and Engineers (2nd ed.). Princeton University Press.
