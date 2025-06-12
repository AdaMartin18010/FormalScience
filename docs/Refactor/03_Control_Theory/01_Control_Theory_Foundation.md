# 控制理论基础 (Control Theory Foundation)

## 目录

1. [引言](#1-引言)
2. [系统理论基础](#2-系统理论基础)
3. [线性系统理论](#3-线性系统理论)
4. [稳定性理论](#4-稳定性理论)
5. [可控性与可观性](#5-可控性与可观性)
6. [状态反馈控制](#6-状态反馈控制)
7. [最优控制理论](#7-最优控制理论)
8. [鲁棒控制理论](#8-鲁棒控制理论)
9. [参考文献](#9-参考文献)

## 1. 引言

### 1.1 控制理论概述

控制理论是研究动态系统行为调节的数学理论，为工程系统设计提供了严格的理论基础。控制理论通过数学模型描述系统动态，通过控制算法实现期望的系统行为。

**定义 1.1.1** (控制系统)
控制系统是一个五元组 $\mathcal{S} = (X, U, Y, f, g)$，其中：

- $X \subseteq \mathbb{R}^n$ 是状态空间
- $U \subseteq \mathbb{R}^m$ 是控制输入空间
- $Y \subseteq \mathbb{R}^p$ 是输出空间
- $f: X \times U \times \mathbb{R} \rightarrow X$ 是状态转移函数
- $g: X \times U \times \mathbb{R} \rightarrow Y$ 是输出函数

**定义 1.1.2** (系统分类)
控制系统按特性分类：

1. **线性系统**：满足叠加原理 $f(\alpha x_1 + \beta x_2, \alpha u_1 + \beta u_2, t) = \alpha f(x_1, u_1, t) + \beta f(x_2, u_2, t)$
2. **时不变系统**：$f(x, u, t) = f(x, u, t + \tau)$ 对于所有 $\tau$
3. **连续时间系统**：状态连续变化
4. **离散时间系统**：状态在离散时间点变化

### 1.2 控制理论的重要性

控制理论在以下领域具有重要作用：

- **工程系统**：机械、电气、化工系统控制
- **航空航天**：飞行器姿态控制、轨道控制
- **机器人学**：机器人运动控制、力控制
- **经济系统**：宏观经济调控、金融风险控制

## 2. 系统理论基础

### 2.1 状态空间表示

**定义 2.1.1** (连续时间状态空间)
连续时间系统的状态空间表示：

$$\dot{x}(t) = f(x(t), u(t), t)$$
$$y(t) = g(x(t), u(t), t)$$

其中 $x(t) \in \mathbb{R}^n$, $u(t) \in \mathbb{R}^m$, $y(t) \in \mathbb{R}^p$。

**定义 2.1.2** (离散时间状态空间)
离散时间系统的状态空间表示：

$$x(k+1) = f(x(k), u(k), k)$$
$$y(k) = g(x(k), u(k), k)$$

其中 $x(k) \in \mathbb{R}^n$, $u(k) \in \mathbb{R}^m$, $y(k) \in \mathbb{R}^p$。

**定理 2.1.1** (解的存在唯一性)
如果 $f$ 是利普希茨连续的，则状态方程存在唯一解。

**证明**：通过皮卡-林德洛夫定理：

1. 利普希茨连续性确保局部存在性
2. 全局存在性通过延拓得到
3. 唯一性通过利普希茨条件保证

### 2.2 系统线性化

**定义 2.2.1** (线性化)
非线性系统在平衡点 $(x_e, u_e)$ 附近的线性化：

$$\delta \dot{x}(t) = A \delta x(t) + B \delta u(t)$$
$$\delta y(t) = C \delta x(t) + D \delta u(t)$$

其中：
$$A = \frac{\partial f}{\partial x}\bigg|_{(x_e, u_e)}, \quad B = \frac{\partial f}{\partial u}\bigg|_{(x_e, u_e)}$$
$$C = \frac{\partial g}{\partial x}\bigg|_{(x_e, u_e)}, \quad D = \frac{\partial g}{\partial u}\bigg|_{(x_e, u_e)}$$

**算法 2.2.1** (系统线性化算法)

```haskell
data NonlinearSystem = NonlinearSystem {
  stateDimension :: Int,
  inputDimension :: Int,
  outputDimension :: Int,
  stateFunction :: Vector Double -> Vector Double -> Double -> Vector Double,
  outputFunction :: Vector Double -> Vector Double -> Double -> Vector Double
}

data LinearSystem = LinearSystem {
  aMatrix :: Matrix Double,
  bMatrix :: Matrix Double,
  cMatrix :: Matrix Double,
  dMatrix :: Matrix Double
}

linearizeSystem :: NonlinearSystem -> Vector Double -> Vector Double -> LinearSystem
linearizeSystem sys xEquilibrium uEquilibrium = 
  let -- 计算雅可比矩阵
      aMatrix = computeJacobian (stateFunction sys) xEquilibrium uEquilibrium 0.0
      bMatrix = computeJacobian (stateFunction sys) xEquilibrium uEquilibrium 0.0
      cMatrix = computeJacobian (outputFunction sys) xEquilibrium uEquilibrium 0.0
      dMatrix = computeJacobian (outputFunction sys) xEquilibrium uEquilibrium 0.0
  in LinearSystem {
    aMatrix = aMatrix,
    bMatrix = bMatrix,
    cMatrix = cMatrix,
    dMatrix = dMatrix
  }

computeJacobian :: (Vector Double -> Vector Double -> Double -> Vector Double) 
                -> Vector Double -> Vector Double -> Double -> Matrix Double
computeJacobian f x u t = 
  let n = length x
      epsilon = 1e-8
      jacobian = matrix n n (\(i, j) -> 
        let xPlus = x + (unitVector n j * epsilon)
            xMinus = x - (unitVector n j * epsilon)
            derivative = (f xPlus u t - f xMinus u t) / (2 * epsilon)
        in derivative `atIndex` i)
  in jacobian
```

## 3. 线性系统理论

### 3.1 线性系统基础

**定义 3.1.1** (线性时不变系统)
线性时不变系统的状态空间表示：

$$\dot{x}(t) = Ax(t) + Bu(t)$$
$$y(t) = Cx(t) + Du(t)$$

其中 $A \in \mathbb{R}^{n \times n}$, $B \in \mathbb{R}^{n \times m}$, $C \in \mathbb{R}^{p \times n}$, $D \in \mathbb{R}^{p \times m}$。

**定义 3.1.2** (状态转移矩阵)
状态转移矩阵 $\Phi(t, t_0)$ 满足：

$$\dot{\Phi}(t, t_0) = A\Phi(t, t_0), \quad \Phi(t_0, t_0) = I$$

**定理 3.1.1** (状态转移矩阵性质)
状态转移矩阵具有以下性质：

1. **半群性质**：$\Phi(t_2, t_0) = \Phi(t_2, t_1)\Phi(t_1, t_0)$
2. **可逆性**：$\Phi(t, t_0)^{-1} = \Phi(t_0, t)$
3. **解的表达**：$x(t) = \Phi(t, t_0)x(t_0) + \int_{t_0}^t \Phi(t, \tau)Bu(\tau)d\tau$

**证明**：通过矩阵微分方程理论：

1. 半群性质通过解的唯一性得到
2. 可逆性通过行列式非零得到
3. 解的表达通过变分常数法得到

### 3.2 传递函数

**定义 3.2.1** (传递函数)
传递函数是系统输入输出关系的拉普拉斯变换：

$$G(s) = C(sI - A)^{-1}B + D$$

**定义 3.2.2** (极点与零点)
传递函数的极点和零点：

1. **极点**：$s$ 使得 $\det(sI - A) = 0$
2. **零点**：$s$ 使得 $\text{rank}\begin{bmatrix} sI-A & B \\ C & D \end{bmatrix} < n + p$

**定理 3.2.1** (极点配置)
通过状态反馈可以任意配置闭环系统极点。

**证明**：通过可控性：

1. 如果系统可控，则存在反馈矩阵 $K$ 使得 $A - BK$ 的特征值任意
2. 闭环系统矩阵为 $A - BK$
3. 因此可以任意配置极点

## 4. 稳定性理论

### 4.1 李雅普诺夫稳定性

**定义 4.1.1** (李雅普诺夫函数)
函数 $V : \mathbb{R}^n \rightarrow \mathbb{R}$ 是系统 $\dot{x} = f(x)$ 的李雅普诺夫函数，如果：

1. $V(0) = 0$
2. $V(x) > 0$ 对于 $x \neq 0$
3. $\dot{V}(x) = \nabla V(x)^T f(x) \leq 0$ 对于 $x \neq 0$

**定义 4.1.2** (渐近稳定性)
平衡点 $x_e = 0$ 是渐近稳定的，如果：

1. 它是李雅普诺夫稳定的
2. $\lim_{t \rightarrow \infty} x(t) = 0$ 对于所有初始条件

**定理 4.1.1** (李雅普诺夫稳定性定理)
如果存在李雅普诺夫函数 $V(x)$ 使得 $\dot{V}(x) < 0$ 对于 $x \neq 0$，则平衡点是渐近稳定的。

**证明**：通过李雅普诺夫直接法：

1. 李雅普诺夫函数确保轨迹有界
2. $\dot{V}(x) < 0$ 确保 $V(x)$ 严格递减
3. 结合李雅普诺夫稳定性得到渐近稳定性

**算法 4.1.1** (李雅普诺夫函数构造)

```haskell
data LyapunovFunction = LyapunovFunction {
  function :: Vector Double -> Double,
  gradient :: Vector Double -> Vector Double
}

constructLyapunovFunction :: Matrix Double -> LyapunovFunction
constructLyapunovFunction aMatrix = 
  let -- 求解李雅普诺夫方程 A^T P + P A = -Q
      qMatrix = identity (rows aMatrix)
      pMatrix = solveLyapunovEquation aMatrix qMatrix
      
      -- 构造二次型李雅普诺夫函数
      lyapunovFunc x = x `dot` (pMatrix `multiply` x)
      lyapunovGrad x = 2 * (pMatrix `multiply` x)
  in LyapunovFunction {
    function = lyapunovFunc,
    gradient = lyapunovGrad
  }

solveLyapunovEquation :: Matrix Double -> Matrix Double -> Matrix Double
solveLyapunovEquation a q = 
  let n = rows a
      -- 将李雅普诺夫方程转换为线性系统
      vecP = solve (kroneckerProduct (transpose a) (identity n) + 
                   kroneckerProduct (identity n) a) (vectorize q)
  in reshape n n vecP
```

### 4.2 输入输出稳定性

**定义 4.2.1** (L2稳定性)
系统是L2稳定的，如果存在常数 $\gamma > 0$ 使得：

$$\|y\|_2 \leq \gamma \|u\|_2$$

对于所有 $u \in L_2$。

**定义 4.2.2** (L∞稳定性)
系统是L∞稳定的，如果存在常数 $\gamma > 0$ 使得：

$$\|y\|_\infty \leq \gamma \|u\|_\infty$$

对于所有 $u \in L_\infty$。

**定理 4.2.1** (小增益定理)
如果两个L2稳定系统 $G_1$ 和 $G_2$ 的增益分别为 $\gamma_1$ 和 $\gamma_2$，且 $\gamma_1 \gamma_2 < 1$，则反馈连接系统是L2稳定的。

**证明**：通过增益分析：

1. 反馈系统的输入输出关系
2. 利用三角不等式
3. 应用小增益条件

## 5. 可控性与可观性

### 5.1 可控性

**定义 5.1.1** (可控性)
系统 $(A, B)$ 是可控的，如果对于任意初始状态 $x_0$ 和目标状态 $x_f$，存在控制输入 $u(t)$ 使得 $x(T) = x_f$。

**定义 5.1.2** (可控性矩阵)
可控性矩阵定义为：

$$\mathcal{C} = [B \quad AB \quad A^2B \quad \cdots \quad A^{n-1}B]$$

**定理 5.1.1** (可控性判据)
系统 $(A, B)$ 可控当且仅当 $\text{rank}(\mathcal{C}) = n$。

**证明**：通过凯莱-哈密顿定理：

1. 如果可控，则 $\text{span}\{B, AB, \ldots, A^{n-1}B\} = \mathbb{R}^n$
2. 因此 $\text{rank}(\mathcal{C}) = n$
3. 反之，如果 $\text{rank}(\mathcal{C}) = n$，则系统可控

**算法 5.1.1** (可控性检查)

```haskell
checkControllability :: Matrix Double -> Matrix Double -> Bool
checkControllability a b = 
  let n = rows a
      -- 构造可控性矩阵
      controllabilityMatrix = constructControllabilityMatrix a b n
      -- 检查秩
      rank = matrixRank controllabilityMatrix
  in rank == n

constructControllabilityMatrix :: Matrix Double -> Matrix Double -> Int -> Matrix Double
constructControllabilityMatrix a b n = 
  let -- 计算 A^i * B for i = 0, 1, ..., n-1
      powers = scanl (\acc _ -> a `multiply` acc) b [1..n-1]
      -- 水平拼接
      controllabilityMatrix = hconcat (b:init powers)
  in controllabilityMatrix
```

### 5.2 可观性

**定义 5.2.1** (可观性)
系统 $(A, C)$ 是可观的，如果任意初始状态 $x_0$ 都可以通过输出 $y(t)$ 唯一确定。

**定义 5.2.2** (可观性矩阵)
可观性矩阵定义为：

$$\mathcal{O} = \begin{bmatrix} C \\ CA \\ CA^2 \\ \vdots \\ CA^{n-1} \end{bmatrix}$$

**定理 5.2.1** (可观性判据)
系统 $(A, C)$ 可观当且仅当 $\text{rank}(\mathcal{O}) = n$。

**证明**：通过对偶性：

1. 可观性等价于对偶系统的可控性
2. 对偶系统的可控性矩阵是 $\mathcal{O}^T$
3. 因此 $\text{rank}(\mathcal{O}) = n$ 等价于可观性

## 6. 状态反馈控制

### 6.1 状态反馈设计

**定义 6.1.1** (状态反馈)
状态反馈控制律：

$$u(t) = -Kx(t) + r(t)$$

其中 $K \in \mathbb{R}^{m \times n}$ 是反馈增益矩阵，$r(t)$ 是参考输入。

**定义 6.1.2** (闭环系统)
闭环系统动态：

$$\dot{x}(t) = (A - BK)x(t) + Br(t)$$
$$y(t) = Cx(t) + Du(t)$$

**定理 6.1.1** (极点配置定理)
如果系统 $(A, B)$ 可控，则对于任意期望极点集合 $\{\lambda_1, \lambda_2, \ldots, \lambda_n\}$，存在反馈增益矩阵 $K$ 使得 $A - BK$ 的特征值为 $\lambda_i$。

**证明**：通过阿克曼公式：

1. 可控性确保极点配置可行
2. 阿克曼公式给出具体的 $K$ 构造
3. 验证 $A - BK$ 的特征值

**算法 6.1.1** (极点配置算法)

```haskell
polePlacement :: Matrix Double -> Matrix Double -> [Complex Double] -> Matrix Double
polePlacement a b desiredPoles = 
  let n = rows a
      -- 构造期望特征多项式
      desiredPoly = polyFromRoots desiredPoles
      -- 计算阿克曼公式
      kMatrix = ackermannFormula a b desiredPoly
  in kMatrix

ackermannFormula :: Matrix Double -> Matrix Double -> [Double] -> Matrix Double
ackermannFormula a b desiredPoly = 
  let n = rows a
      -- 计算可控性矩阵
      controllabilityMatrix = constructControllabilityMatrix a b n
      -- 计算特征多项式系数
      characteristicPoly = characteristicPolynomial a
      -- 计算阿克曼公式
      kMatrix = computeAckermann controllabilityMatrix characteristicPoly desiredPoly
  in kMatrix

computeAckermann :: Matrix Double -> [Double] -> [Double] -> Matrix Double
computeAckermann controllabilityMatrix charPoly desiredPoly = 
  let -- 计算多项式差值
      diffPoly = zipWith (-) desiredPoly charPoly
      -- 计算阿克曼公式
      kMatrix = sum (zipWith (*) diffPoly (map (matrixPower controllabilityMatrix) [0..]))
  in kMatrix
```

### 6.2 最优状态反馈

**定义 6.2.1** (线性二次型调节器)
线性二次型调节器(LQR)问题：

$$\min_{u(t)} \int_0^\infty [x^T(t)Qx(t) + u^T(t)Ru(t)]dt$$

受约束于 $\dot{x}(t) = Ax(t) + Bu(t)$。

**定义 6.2.2** (代数黎卡提方程)
最优反馈增益通过代数黎卡提方程求解：

$$A^TP + PA - PBR^{-1}B^TP + Q = 0$$

**定理 6.2.1** (LQR最优性)
如果 $(A, B)$ 可控且 $(A, Q^{1/2})$ 可观，则LQR问题存在唯一最优解。

**证明**：通过最优控制理论：

1. 可控性确保问题有解
2. 可观性确保解唯一
3. 代数黎卡提方程给出最优解

**算法 6.2.1** (LQR设计算法)

```haskell
designLQR :: Matrix Double -> Matrix Double -> Matrix Double -> Matrix Double -> Matrix Double
designLQR a b q r = 
  let -- 求解代数黎卡提方程
      pMatrix = solveAlgebraicRiccati a b q r
      -- 计算最优反馈增益
      kMatrix = r `inverse` (transpose b `multiply` pMatrix)
  in kMatrix

solveAlgebraicRiccati :: Matrix Double -> Matrix Double -> Matrix Double -> Matrix Double -> Matrix Double
solveAlgebraicRiccati a b q r = 
  let -- 构造哈密顿矩阵
      hamiltonianMatrix = constructHamiltonian a b q r
      -- 计算稳定不变子空间
      stableSubspace = stableInvariantSubspace hamiltonianMatrix
      -- 提取黎卡提方程的解
      pMatrix = extractRiccatiSolution stableSubspace
  in pMatrix

constructHamiltonian :: Matrix Double -> Matrix Double -> Matrix Double -> Matrix Double -> Matrix Double
constructHamiltonian a b q r = 
  let n = rows a
      -- 构造哈密顿矩阵
      h11 = a
      h12 = b `multiply` (r `inverse`) `multiply` (transpose b)
      h21 = q
      h22 = -transpose a
      -- 垂直和水平拼接
      hamiltonian = vconcat [hconcat [h11, h12], hconcat [h21, h22]]
  in hamiltonian
```

## 7. 最优控制理论

### 7.1 变分法

**定义 7.1.1** (最优控制问题)
最优控制问题：

$$\min_{u(t)} J = \int_{t_0}^{t_f} L(x(t), u(t), t)dt + \phi(x(t_f))$$

受约束于 $\dot{x}(t) = f(x(t), u(t), t)$。

**定义 7.1.2** (哈密顿函数)
哈密顿函数：

$$H(x, u, \lambda, t) = L(x, u, t) + \lambda^T f(x, u, t)$$

**定理 7.1.1** (最优性必要条件)
如果 $u^*(t)$ 是最优控制，则满足：

1. **状态方程**：$\dot{x} = \frac{\partial H}{\partial \lambda}$
2. **协态方程**：$\dot{\lambda} = -\frac{\partial H}{\partial x}$
3. **控制方程**：$\frac{\partial H}{\partial u} = 0$

**证明**：通过变分法：

1. 构造变分问题
2. 应用欧拉-拉格朗日方程
3. 得到最优性必要条件

### 7.2 动态规划

**定义 7.2.1** (值函数)
值函数 $V(x, t)$ 定义为从状态 $x$ 和时间 $t$ 开始的最优代价。

**定义 7.2.2** (贝尔曼方程)
贝尔曼方程：

$$V(x, t) = \min_{u} \{L(x, u, t) + V(f(x, u, t), t + \Delta t)\}$$

**定理 7.2.1** (动态规划原理)
最优控制满足动态规划原理。

**证明**：通过最优性原理：

1. 最优轨迹的任何子轨迹都是最优的
2. 因此值函数满足贝尔曼方程
3. 动态规划给出最优解

## 8. 鲁棒控制理论

### 8.1 不确定性建模

**定义 8.1.1** (不确定性模型)
系统不确定性模型：

$$\dot{x}(t) = (A + \Delta A)x(t) + (B + \Delta B)u(t)$$

其中 $\Delta A$ 和 $\Delta B$ 是不确定性矩阵。

**定义 8.1.2** (H∞控制)
H∞控制问题：

$$\min_{K} \|T_{zw}\|_\infty$$

其中 $T_{zw}$ 是从干扰 $w$ 到性能输出 $z$ 的闭环传递函数。

**定理 8.1.1** (H∞控制存在性)
H∞控制问题有解当且仅当存在正定矩阵 $P$ 满足H∞黎卡提不等式。

**证明**：通过有界实引理：

1. H∞范数有界等价于有界实引理
2. 有界实引理给出矩阵不等式
3. 求解不等式得到控制器

### 8.2 μ-综合

**定义 8.2.1** (μ-分析)
μ-分析用于分析系统在结构不确定性下的鲁棒性。

**定义 8.2.2** (μ-综合)
μ-综合设计控制器使得闭环系统的μ值小于1。

**定理 8.2.1** (μ-综合定理)
μ-综合问题可以通过D-K迭代求解。

**证明**：通过μ-综合理论：

1. μ-综合等价于D-K迭代
2. D-K迭代收敛到局部最优解
3. 因此μ-综合问题可解

## 9. 参考文献

1. **Ogata, K.** (2010). *Modern Control Engineering*. Prentice Hall.

2. **Franklin, G. F., Powell, J. D., & Emami-Naeini, A.** (2015). *Feedback Control of Dynamic Systems*. Pearson.

3. **Doyle, J. C., Francis, B. A., & Tannenbaum, A. R.** (2013). *Feedback Control Theory*. Dover Publications.

4. **Khalil, H. K.** (2002). *Nonlinear Systems*. Prentice Hall.

5. **Sontag, E. D.** (1998). *Mathematical Control Theory: Deterministic Finite Dimensional Systems*. Springer.

6. **Zhou, K., & Doyle, J. C.** (1998). *Essentials of Robust Control*. Prentice Hall.

7. **Anderson, B. D., & Moore, J. B.** (2007). *Optimal Control: Linear Quadratic Methods*. Dover Publications.

8. **Lewis, F. L., Vrabie, D., & Syrmos, V. L.** (2012). *Optimal Control*. John Wiley & Sons.

---

**文档版本**：1.0  
**最后更新**：2024-12-19  
**作者**：形式科学理论体系重构项目  
**状态**：已完成控制理论基础重构
