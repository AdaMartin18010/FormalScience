# 01. 线性控制理论 (Linear Control Theory)

## 目录

1. [基本概念](#基本概念)
2. [状态空间表示](#状态空间表示)
3. [传递函数](#传递函数)
4. [稳定性分析](#稳定性分析)
5. [可控性与可观性](#可控性与可观性)
6. [形式化表示](#形式化表示)
7. [证明系统](#证明系统)
8. [与其他学科的关联](#与其他学科的关联)

## 基本概念

### 1.1 线性系统

**定义 1.1.1 (线性系统)**
线性系统是满足叠加原理的动态系统：

```
如果 y₁(t) = T[u₁(t)] 且 y₂(t) = T[u₂(t)]
则 T[αu₁(t) + βu₂(t)] = αy₁(t) + βy₂(t)
```

**定义 1.1.2 (时不变系统)**
时不变系统是满足时间平移不变性的系统：

```
如果 y(t) = T[u(t)]
则 y(t - τ) = T[u(t - τ)]
```

### 1.2 系统表示

**定义 1.1.3 (连续时间线性系统)**
连续时间线性时不变系统可以表示为：

```
ẋ(t) = Ax(t) + Bu(t)
y(t) = Cx(t) + Du(t)
```

其中：

- x(t) ∈ ℝⁿ 是状态向量
- u(t) ∈ ℝᵐ 是输入向量
- y(t) ∈ ℝᵖ 是输出向量
- A ∈ ℝⁿˣⁿ 是系统矩阵
- B ∈ ℝⁿˣᵐ 是输入矩阵
- C ∈ ℝᵖˣⁿ 是输出矩阵
- D ∈ ℝᵖˣᵐ 是直接传递矩阵

## 状态空间表示

### 2.1 状态空间模型

**定义 2.1.1 (状态空间)**
状态空间是描述系统动态行为的数学空间，其中每个点表示系统的一个状态。

**定理 2.1.1 (状态方程的解)**
对于线性系统 ẋ(t) = Ax(t) + Bu(t)，其解为：

```
x(t) = eᴬᵗx(0) + ∫₀ᵗ eᴬ⁽ᵗ⁻ᵗ⁾Bu(τ)dτ
```

**证明：**

1. 设 x(t) = eᴬᵗv(t)，其中 v(t) 是待定函数
2. 代入状态方程：Aeᴬᵗv(t) + eᴬᵗv̇(t) = Aeᴬᵗv(t) + Bu(t)
3. 因此 v̇(t) = e⁻ᴬᵗBu(t)
4. 积分得到：v(t) = v(0) + ∫₀ᵗ e⁻ᴬᵗBu(τ)dτ
5. 所以 x(t) = eᴬᵗx(0) + ∫₀ᵗ eᴬ⁽ᵗ⁻ᵗ⁾Bu(τ)dτ

### 2.2 状态转移矩阵

**定义 2.1.2 (状态转移矩阵)**
状态转移矩阵 Φ(t) = eᴬᵗ 满足：

```
Φ̇(t) = AΦ(t), Φ(0) = I
```

**定理 2.1.2 (状态转移矩阵的性质)**

```
1. Φ(0) = I
2. Φ(t₁ + t₂) = Φ(t₁)Φ(t₂)
3. Φ⁻¹(t) = Φ(-t)
4. Φ(t) = L⁻¹[(sI - A)⁻¹]
```

**证明：**

1. Φ(0) = eᴬ⁰ = I
2. Φ(t₁ + t₂) = eᴬ⁽ᵗ¹⁺ᵗ²⁾ = eᴬᵗ¹eᴬᵗ² = Φ(t₁)Φ(t₂)
3. Φ(t)Φ(-t) = eᴬᵗe⁻ᴬᵗ = I，因此 Φ⁻¹(t) = Φ(-t)
4. 根据拉普拉斯变换的性质

## 传递函数

### 3.1 传递函数定义

**定义 3.1.1 (传递函数)**
传递函数是系统输出与输入的拉普拉斯变换之比：

```
G(s) = Y(s)/U(s) = C(sI - A)⁻¹B + D
```

**定理 3.1.1 (传递函数的性质)**

```
1. G(s) 是有理函数
2. G(s) 的极点等于 A 的特征值
3. G(s) 的零点由 A, B, C 共同决定
```

**证明：**

1. 由于 (sI - A)⁻¹ = adj(sI - A)/det(sI - A)，G(s) 是有理函数
2. G(s) 的极点满足 det(sI - A) = 0，即 A 的特征值
3. G(s) 的零点满足 det([sI - A, -B; C, D]) = 0

### 3.2 传递函数的实现

**定义 3.1.2 (最小实现)**
最小实现是传递函数的最小阶状态空间实现。

**定理 3.1.2 (最小实现的阶数)**
最小实现的阶数等于传递函数的分母多项式次数。

**证明：**

1. 设传递函数 G(s) = N(s)/D(s)，其中 deg(D(s)) = n
2. 最小实现的阶数不能小于 n，否则无法实现所有极点
3. 阶数为 n 的实现可以构造，因此最小阶数为 n

## 稳定性分析

### 4.1 稳定性定义

**定义 4.1.1 (渐近稳定性)**
系统 ẋ(t) = Ax(t) 是渐近稳定的，如果对于任意初始状态 x(0)，都有：

```
lim_{t→∞} x(t) = 0
```

**定义 4.1.2 (李雅普诺夫稳定性)**
系统是李雅普诺夫稳定的，如果对于任意 ε > 0，存在 δ > 0，使得：

```
||x(0)|| < δ → ||x(t)|| < ε, ∀t ≥ 0
```

### 4.2 稳定性判据

**定理 4.1.1 (特征值判据)**
线性系统 ẋ(t) = Ax(t) 渐近稳定当且仅当 A 的所有特征值都具有负实部。

**证明：**

1. 充分性：如果所有特征值都有负实部，则 eᴬᵗ → 0 (t → ∞)
2. 必要性：如果存在特征值 λ 使得 Re(λ) ≥ 0，则 eᴬᵗ 不收敛到零

**定理 4.1.2 (李雅普诺夫判据)**
系统 ẋ(t) = Ax(t) 渐近稳定当且仅当存在正定矩阵 P 使得：

```
AᵀP + PA = -Q
```

其中 Q 是正定矩阵。

**证明：**

1. 设 V(x) = xᵀPx 是李雅普诺夫函数
2. V̇(x) = xᵀ(AᵀP + PA)x = -xᵀQx < 0
3. 因此系统渐近稳定

### 4.3 劳斯-赫尔维茨判据

**定理 4.1.3 (劳斯判据)**
多项式 P(s) = aₙsⁿ + aₙ₋₁sⁿ⁻¹ + ... + a₁s + a₀ 的所有根都具有负实部当且仅当劳斯表的第一列所有元素都为正。

**劳斯表构造：**

```
sⁿ    aₙ    aₙ₋₂    aₙ₋₄    ...
sⁿ⁻¹  aₙ₋₁  aₙ₋₃    aₙ₋₅    ...
sⁿ⁻²  b₁    b₂      b₃      ...
...
s⁰    c₁
```

其中：

```
b₁ = (aₙ₋₁aₙ₋₂ - aₙaₙ₋₃)/aₙ₋₁
b₂ = (aₙ₋₁aₙ₋₄ - aₙaₙ₋₅)/aₙ₋₁
...
```

## 可控性与可观性

### 5.1 可控性

**定义 5.1.1 (可控性)**
系统 (A, B) 是可控的，如果对于任意初始状态 x₀ 和目标状态 x₁，存在有限时间 T 和控制输入 u(t)，使得：

```
x(T) = x₁
```

**定理 5.1.1 (可控性判据)**
系统 (A, B) 可控当且仅当可控性矩阵：

```
Wc = [B, AB, A²B, ..., Aⁿ⁻¹B]
```

满秩，即 rank(Wc) = n。

**证明：**

1. 充分性：如果 Wc 满秩，则存在控制输入使得 x(T) = x₁
2. 必要性：如果 Wc 不满秩，则存在不可达状态

### 5.2 可观性

**定义 5.1.2 (可观性)**
系统 (A, C) 是可观的，如果对于任意初始状态 x₀，可以通过输出 y(t) 在有限时间内确定。

**定理 5.1.2 (可观性判据)**
系统 (A, C) 可观当且仅当可观性矩阵：

```
Wo = [C; CA; CA²; ...; CAⁿ⁻¹]
```

满秩，即 rank(Wo) = n。

**证明：**

1. 充分性：如果 Wo 满秩，则可以通过输出确定初始状态
2. 必要性：如果 Wo 不满秩，则存在不可观测状态

### 5.3 标准形

**定理 5.1.3 (可控标准形)**
如果系统 (A, B) 可控，则存在非奇异变换 T 使得：

```
Ā = T⁻¹AT = [0 1 0 ... 0; 0 0 1 ... 0; ...; -a₀ -a₁ ... -aₙ₋₁]
Ḃ = T⁻¹B = [0; 0; ...; 1]
```

**定理 5.1.4 (可观标准形)**
如果系统 (A, C) 可观，则存在非奇异变换 T 使得：

```
Ā = T⁻¹AT = [0 0 ... 0 -a₀; 1 0 ... 0 -a₁; ...; 0 0 ... 1 -aₙ₋₁]
Ĉ = CT = [0 0 ... 0 1]
```

## 形式化表示

### 6.1 一阶逻辑表示

**语言 L：**

- 个体变元：x, y, z, u, v, w, t, s, ...
- 矩阵变元：A, B, C, D, P, Q, ...
- 函数符号：eᴬᵗ (矩阵指数), L (拉普拉斯变换), det (行列式), rank (秩)
- 谓词符号：∈ (属于), = (等于), < (小于), > (大于), stable (稳定), controllable (可控), observable (可观)
- 逻辑连接词：¬, ∧, ∨, →, ↔
- 量词：∀, ∃

**公理系统：**

```
A1: ∀x∀t(ẋ(t) = Ax(t) + Bu(t) → x(t) = eᴬᵗx(0) + ∫₀ᵗ eᴬ⁽ᵗ⁻ᵗ⁾Bu(τ)dτ)  // 状态方程解
A2: ∀A∀t(eᴬ⁽ᵗ¹⁺ᵗ²⁾ = eᴬᵗ¹eᴬᵗ²)  // 矩阵指数性质
A3: ∀A∀P∀Q(AᵀP + PA = -Q ∧ P > 0 ∧ Q > 0 → stable(A))  // 李雅普诺夫判据
A4: ∀A∀B(controllable(A, B) ↔ rank([B, AB, ..., Aⁿ⁻¹B]) = n)  // 可控性判据
A5: ∀A∀C(observable(A, C) ↔ rank([C; CA; ...; CAⁿ⁻¹]) = n)  // 可观性判据
```

### 6.2 类型论表示

**类型定义：**

```rust
// 向量类型
#[derive(Debug, Clone)]
struct Vector {
    data: Vec<f64>,
    size: usize,
}

impl Vector {
    fn new(size: usize) -> Self {
        Vector {
            data: vec![0.0; size],
            size,
        }
    }
    
    fn from_vec(data: Vec<f64>) -> Self {
        let size = data.len();
        Vector { data, size }
    }
    
    fn norm(&self) -> f64 {
        self.data.iter().map(|x| x * x).sum::<f64>().sqrt()
    }
    
    fn dot(&self, other: &Vector) -> Option<f64> {
        if self.size != other.size {
            return None;
        }
        Some(self.data.iter().zip(&other.data).map(|(a, b)| a * b).sum())
    }
}

// 矩阵类型
#[derive(Debug, Clone)]
struct Matrix {
    data: Vec<Vec<f64>>,
    rows: usize,
    cols: usize,
}

impl Matrix {
    fn new(rows: usize, cols: usize) -> Self {
        Matrix {
            data: vec![vec![0.0; cols]; rows],
            rows,
            cols,
        }
    }
    
    fn identity(size: usize) -> Self {
        let mut matrix = Matrix::new(size, size);
        for i in 0..size {
            matrix.data[i][i] = 1.0;
        }
        matrix
    }
    
    fn multiply(&self, other: &Matrix) -> Option<Matrix> {
        if self.cols != other.rows {
            return None;
        }
        
        let mut result = Matrix::new(self.rows, other.cols);
        for i in 0..self.rows {
            for j in 0..other.cols {
                for k in 0..self.cols {
                    result.data[i][j] += self.data[i][k] * other.data[k][j];
                }
            }
        }
        Some(result)
    }
    
    fn transpose(&self) -> Matrix {
        let mut result = Matrix::new(self.cols, self.rows);
        for i in 0..self.rows {
            for j in 0..self.cols {
                result.data[j][i] = self.data[i][j];
            }
        }
        result
    }
    
    fn determinant(&self) -> Option<f64> {
        if self.rows != self.cols {
            return None;
        }
        
        if self.rows == 1 {
            return Some(self.data[0][0]);
        }
        
        if self.rows == 2 {
            return Some(self.data[0][0] * self.data[1][1] - self.data[0][1] * self.data[1][0]);
        }
        
        // 递归计算行列式
        let mut det = 0.0;
        for j in 0..self.cols {
            let minor = self.minor(0, j);
            det += (-1.0_f64).powi(j as i32) * self.data[0][j] * minor.determinant().unwrap_or(0.0);
        }
        Some(det)
    }
    
    fn minor(&self, row: usize, col: usize) -> Matrix {
        let mut result = Matrix::new(self.rows - 1, self.cols - 1);
        let mut r = 0;
        for i in 0..self.rows {
            if i == row {
                continue;
            }
            let mut c = 0;
            for j in 0..self.cols {
                if j == col {
                    continue;
                }
                result.data[r][c] = self.data[i][j];
                c += 1;
            }
            r += 1;
        }
        result
    }
    
    fn eigenvalues(&self) -> Vec<Complex<f64>> {
        // 简化版本的特征值计算
        if self.rows == 2 {
            let a = self.data[0][0];
            let b = self.data[0][1];
            let c = self.data[1][0];
            let d = self.data[1][1];
            
            let trace = a + d;
            let det = a * d - b * c;
            let discriminant = trace * trace - 4.0 * det;
            
            if discriminant >= 0.0 {
                let sqrt_disc = discriminant.sqrt();
                vec![
                    Complex::new((trace + sqrt_disc) / 2.0, 0.0),
                    Complex::new((trace - sqrt_disc) / 2.0, 0.0),
                ]
            } else {
                let sqrt_disc = (-discriminant).sqrt();
                vec![
                    Complex::new(trace / 2.0, sqrt_disc / 2.0),
                    Complex::new(trace / 2.0, -sqrt_disc / 2.0),
                ]
            }
        } else {
            // 对于高阶矩阵，使用数值方法
            vec![]
        }
    }
}

// 线性系统类型
#[derive(Debug, Clone)]
struct LinearSystem {
    A: Matrix,
    B: Matrix,
    C: Matrix,
    D: Matrix,
    state_dim: usize,
    input_dim: usize,
    output_dim: usize,
}

impl LinearSystem {
    fn new(A: Matrix, B: Matrix, C: Matrix, D: Matrix) -> Self {
        let state_dim = A.rows;
        let input_dim = B.cols;
        let output_dim = C.rows;
        
        LinearSystem {
            A,
            B,
            C,
            D,
            state_dim,
            input_dim,
            output_dim,
        }
    }
    
    fn is_stable(&self) -> bool {
        let eigenvalues = self.A.eigenvalues();
        eigenvalues.iter().all(|λ| λ.re < 0.0)
    }
    
    fn is_controllable(&self) -> bool {
        let controllability_matrix = self.build_controllability_matrix();
        controllability_matrix.rank() == self.state_dim
    }
    
    fn is_observable(&self) -> bool {
        let observability_matrix = self.build_observability_matrix();
        observability_matrix.rank() == self.state_dim
    }
    
    fn build_controllability_matrix(&self) -> Matrix {
        let mut result = Matrix::new(self.state_dim, self.state_dim * self.input_dim);
        let mut current_power = Matrix::identity(self.state_dim);
        
        for i in 0..self.state_dim {
            let term = current_power.multiply(&self.B).unwrap();
            for j in 0..self.input_dim {
                for k in 0..self.state_dim {
                    result.data[k][i * self.input_dim + j] = term.data[k][j];
                }
            }
            current_power = current_power.multiply(&self.A).unwrap();
        }
        
        result
    }
    
    fn build_observability_matrix(&self) -> Matrix {
        let mut result = Matrix::new(self.state_dim * self.output_dim, self.state_dim);
        let mut current_power = Matrix::identity(self.state_dim);
        
        for i in 0..self.state_dim {
            let term = self.C.multiply(&current_power).unwrap();
            for j in 0..self.output_dim {
                for k in 0..self.state_dim {
                    result.data[i * self.output_dim + j][k] = term.data[j][k];
                }
            }
            current_power = self.A.multiply(&current_power).unwrap();
        }
        
        result
    }
    
    fn rank(&self) -> usize {
        // 简化版本的秩计算
        let mut matrix = self.clone();
        let mut rank = 0;
        
        for col in 0..matrix.cols.min(matrix.rows) {
            // 寻找主元
            let mut pivot_row = rank;
            for row in rank..matrix.rows {
                if matrix.data[row][col].abs() > matrix.data[pivot_row][col].abs() {
                    pivot_row = row;
                }
            }
            
            if matrix.data[pivot_row][col].abs() > 1e-10 {
                // 交换行
                if pivot_row != rank {
                    matrix.data.swap(rank, pivot_row);
                }
                
                // 消元
                for row in (rank + 1)..matrix.rows {
                    let factor = matrix.data[row][col] / matrix.data[rank][col];
                    for c in col..matrix.cols {
                        matrix.data[row][c] -= factor * matrix.data[rank][c];
                    }
                }
                
                rank += 1;
            }
        }
        
        rank
    }
    
    fn solve_lyapunov_equation(&self, Q: &Matrix) -> Option<Matrix> {
        // 求解李雅普诺夫方程 AᵀP + PA = -Q
        // 简化版本，实际需要更复杂的算法
        if self.A.rows != Q.rows || self.A.rows != Q.cols {
            return None;
        }
        
        let n = self.A.rows;
        let mut P = Matrix::new(n, n);
        
        // 使用迭代方法求解
        for _ in 0..100 {
            let A_T = self.A.transpose();
            let AP = self.A.multiply(&P).unwrap();
            let A_T_P = A_T.multiply(&P).unwrap();
            let sum = AP.add(&A_T_P).unwrap();
            let residual = sum.add(Q).unwrap();
            
            if residual.norm() < 1e-6 {
                return Some(P);
            }
            
            // 更新P
            for i in 0..n {
                for j in 0..n {
                    P.data[i][j] -= 0.1 * residual.data[i][j];
                }
            }
        }
        
        None
    }
}

// 传递函数类型
#[derive(Debug, Clone)]
struct TransferFunction {
    numerator: Vec<f64>,
    denominator: Vec<f64>,
}

impl TransferFunction {
    fn new(numerator: Vec<f64>, denominator: Vec<f64>) -> Self {
        TransferFunction {
            numerator,
            denominator,
        }
    }
    
    fn from_system(system: &LinearSystem) -> Self {
        // 从状态空间模型计算传递函数
        // 简化版本，实际需要更复杂的计算
        let n = system.state_dim;
        let mut numerator = vec![0.0; n];
        let mut denominator = vec![0.0; n + 1];
        
        // 计算特征多项式
        let char_poly = system.A.characteristic_polynomial();
        denominator = char_poly;
        
        // 计算传递函数分子
        numerator[0] = 1.0;
        
        TransferFunction {
            numerator,
            denominator,
        }
    }
    
    fn poles(&self) -> Vec<Complex<f64>> {
        // 计算极点（分母多项式的根）
        self.denominator_roots()
    }
    
    fn zeros(&self) -> Vec<Complex<f64>> {
        // 计算零点（分子多项式的根）
        self.numerator_roots()
    }
    
    fn is_stable(&self) -> bool {
        let poles = self.poles();
        poles.iter().all(|p| p.re < 0.0)
    }
    
    fn denominator_roots(&self) -> Vec<Complex<f64>> {
        // 简化版本的多项式求根
        if self.denominator.len() == 2 {
            // 一次多项式
            let root = -self.denominator[0] / self.denominator[1];
            vec![Complex::new(root, 0.0)]
        } else if self.denominator.len() == 3 {
            // 二次多项式
            let a = self.denominator[2];
            let b = self.denominator[1];
            let c = self.denominator[0];
            
            let discriminant = b * b - 4.0 * a * c;
            if discriminant >= 0.0 {
                let sqrt_disc = discriminant.sqrt();
                vec![
                    Complex::new((-b + sqrt_disc) / (2.0 * a), 0.0),
                    Complex::new((-b - sqrt_disc) / (2.0 * a), 0.0),
                ]
            } else {
                let sqrt_disc = (-discriminant).sqrt();
                vec![
                    Complex::new(-b / (2.0 * a), sqrt_disc / (2.0 * a)),
                    Complex::new(-b / (2.0 * a), -sqrt_disc / (2.0 * a)),
                ]
            }
        } else {
            // 高阶多项式需要数值方法
            vec![]
        }
    }
    
    fn numerator_roots(&self) -> Vec<Complex<f64>> {
        // 类似分母求根
        vec![]
    }
}
```

## 证明系统

### 7.1 稳定性证明

**定理 7.1.1 (李雅普诺夫稳定性定理)**
如果存在正定矩阵 P 使得 AᵀP + PA = -Q，其中 Q 是正定矩阵，则系统 ẋ(t) = Ax(t) 渐近稳定。

**证明：**

1. 设 V(x) = xᵀPx 是李雅普诺夫函数
2. V(x) > 0 对所有 x ≠ 0（因为 P 正定）
3. V̇(x) = xᵀ(AᵀP + PA)x = -xᵀQx < 0 对所有 x ≠ 0（因为 Q 正定）
4. 因此系统渐近稳定

### 7.2 可控性证明

**定理 7.1.2 (可控性判据)**
系统 (A, B) 可控当且仅当可控性矩阵 Wc = [B, AB, A²B, ..., Aⁿ⁻¹B] 满秩。

**证明：**

1. 充分性：如果 Wc 满秩，则对于任意目标状态，存在控制输入
2. 必要性：如果 Wc 不满秩，则存在不可达状态

## 与其他学科的关联

### 8.1 与哲学的关联

**认识论：**

- 系统建模与知识表示
- 稳定性与确定性
- 控制与自由意志

**本体论：**

- 系统与实体
- 状态与存在
- 动态与静态

### 8.2 与数学的关联

**线性代数：**

- 矩阵运算
- 特征值与特征向量
- 向量空间

**微分方程：**

- 状态方程
- 解的存在唯一性
- 稳定性理论

### 8.3 与工程学的关联

**自动控制：**

- 反馈控制
- 系统设计
- 性能优化

**信号处理：**

- 传递函数
- 频率响应
- 滤波器设计

## 应用示例

### 9.1 倒立摆控制

```rust
// 倒立摆系统的线性化模型
struct InvertedPendulum {
    system: LinearSystem,
    controller: LinearController,
}

impl InvertedPendulum {
    fn new() -> Self {
        // 倒立摆的线性化模型
        let g = 9.81; // 重力加速度
        let l = 1.0;  // 摆长
        let m = 1.0;  // 质量
        
        let A = Matrix::from_vec(vec![
            vec![0.0, 1.0, 0.0, 0.0],
            vec![g/l, 0.0, 0.0, 0.0],
            vec![0.0, 0.0, 0.0, 1.0],
            vec![0.0, 0.0, 0.0, 0.0],
        ]);
        
        let B = Matrix::from_vec(vec![
            vec![0.0],
            vec![0.0],
            vec![0.0],
            vec![1.0],
        ]);
        
        let C = Matrix::from_vec(vec![
            vec![1.0, 0.0, 0.0, 0.0],
            vec![0.0, 0.0, 1.0, 0.0],
        ]);
        
        let D = Matrix::new(2, 1);
        
        let system = LinearSystem::new(A, B, C, D);
        let controller = LinearController::new(&system);
        
        InvertedPendulum { system, controller }
    }
    
    fn design_controller(&mut self) {
        // 设计线性二次型调节器
        let Q = Matrix::from_vec(vec![
            vec![10.0, 0.0, 0.0, 0.0],
            vec![0.0, 1.0, 0.0, 0.0],
            vec![0.0, 0.0, 10.0, 0.0],
            vec![0.0, 0.0, 0.0, 1.0],
        ]);
        
        let R = Matrix::from_vec(vec![vec![1.0]]);
        
        self.controller = LinearController::lqr(&self.system, &Q, &R);
    }
    
    fn simulate(&self, initial_state: Vector, duration: f64, dt: f64) -> Vec<Vector> {
        let mut states = Vec::new();
        let mut current_state = initial_state;
        
        let steps = (duration / dt) as usize;
        for _ in 0..steps {
            states.push(current_state.clone());
            
            // 计算控制输入
            let control = self.controller.compute_control(&current_state);
            
            // 更新状态
            current_state = self.system.simulate_step(&current_state, &control, dt);
        }
        
        states
    }
}

struct LinearController {
    K: Matrix,
}

impl LinearController {
    fn new(system: &LinearSystem) -> Self {
        // 简单的比例控制器
        let K = Matrix::from_vec(vec![
            vec![-1.0, -2.0, -1.0, -2.0],
        ]);
        
        LinearController { K }
    }
    
    fn lqr(system: &LinearSystem, Q: &Matrix, R: &Matrix) -> Self {
        // 线性二次型调节器设计
        // 简化版本，实际需要求解代数黎卡提方程
        let K = Matrix::from_vec(vec![
            vec![-3.16, -4.47, -3.16, -4.47],
        ]);
        
        LinearController { K }
    }
    
    fn compute_control(&self, state: &Vector) -> Vector {
        // 计算控制输入 u = -Kx
        let state_matrix = Matrix::from_vec(vec![state.data.clone()]).transpose();
        let control_matrix = self.K.multiply(&state_matrix).unwrap();
        
        Vector::from_vec(control_matrix.data[0].clone())
    }
}
```

### 9.2 稳定性分析工具

```rust
// 稳定性分析工具
struct StabilityAnalyzer;

impl StabilityAnalyzer {
    fn analyze_system(system: &LinearSystem) -> StabilityReport {
        let eigenvalues = system.A.eigenvalues();
        let is_stable = system.is_stable();
        let is_controllable = system.is_controllable();
        let is_observable = system.is_observable();
        
        let lyapunov_solution = system.solve_lyapunov_equation(&Matrix::identity(system.state_dim));
        let has_lyapunov_function = lyapunov_solution.is_some();
        
        StabilityReport {
            eigenvalues,
            is_stable,
            is_controllable,
            is_observable,
            has_lyapunov_function,
        }
    }
    
    fn routh_hurwitz_criterion(denominator: &[f64]) -> bool {
        // 劳斯-赫尔维茨判据
        let n = denominator.len() - 1;
        let mut routh_table = vec![vec![0.0; n + 1]; n + 1];
        
        // 填充前两行
        for i in 0..=n {
            routh_table[0][i] = denominator[n - i];
        }
        
        for i in 0..n {
            routh_table[1][i] = if i % 2 == 0 && i + 1 < denominator.len() {
                denominator[n - i - 1]
            } else {
                0.0
            };
        }
        
        // 计算其余行
        for i in 2..=n {
            for j in 0..n {
                if routh_table[i-1][0] != 0.0 {
                    routh_table[i][j] = (routh_table[i-2][0] * routh_table[i-1][j+1] 
                        - routh_table[i-2][j+1] * routh_table[i-1][0]) / routh_table[i-1][0];
                }
            }
        }
        
        // 检查第一列符号变化
        let mut sign_changes = 0;
        let mut prev_sign = routh_table[0][0].signum();
        
        for i in 1..=n {
            let current_sign = routh_table[i][0].signum();
            if current_sign != 0.0 && current_sign != prev_sign {
                sign_changes += 1;
                prev_sign = current_sign;
            }
        }
        
        sign_changes == 0
    }
}

#[derive(Debug)]
struct StabilityReport {
    eigenvalues: Vec<Complex<f64>>,
    is_stable: bool,
    is_controllable: bool,
    is_observable: bool,
    has_lyapunov_function: bool,
}
```

## 总结

线性控制理论为动态系统的分析和设计提供了强大的数学工具，通过形式化表示和严格的证明系统，我们可以：

1. 建立线性系统的基本理论
2. 分析系统的稳定性和性能
3. 设计控制器和观测器
4. 验证系统的可控性和可观性

这些理论为后续的非线性控制、鲁棒控制、最优控制等提供了重要的理论基础。


## 批判性分析

- 本节内容待补充：请从多元理论视角、局限性、争议点、应用前景等方面进行批判性分析。
