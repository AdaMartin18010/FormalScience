# 形式科学理论体系 - 快速参考

> **文档版本**: v2.1.0
> **最后更新**: 2025-10-29
> **用途**: 公式、定理、常数速查表
> **建议**: 打印或作为第二屏参考
> **新增**: ✨ 31个核心公式统一编号系统（新增编程算法视角 5个公式）

---

## 1 📌 公式编号系统

本文档为核心公式建立了统一的编号系统，方便跨文档引用：

| 分类 | 编号范围 | 数量 | 说明 |
|------|---------|------|------|
| **信息论** | [INFO-01] ~ [INFO-08] | 8个 | Shannon熵、互信息、信道容量等 |
| **物理** | [PHYS-01] | 1个 | Landauer极限 |
| **学习理论** | [LEARN-01] ~ [LEARN-05] | 5个 | VC维、PAC、Rademacher等 |
| **控制论** | [CTRL-01] ~ [CTRL-05] | 5个 | Ashby定律、Data Rate、Lyapunov等 |
| **计算复杂性** | [COMP-01] ~ [COMP-04] | 4个 | P/NP、空间复杂性、Savitch等 |
| **分布式** | [DIST-01] ~ [DIST-03] | 3个 | BFT阈值、最终一致性、CAP等 |
| **编程算法** ✨ **NEW!** | [PROG-01] ~ [PROG-05] | 5个 | UH-Cost模型、形式语义、复杂度理论等 |
| **总计** | - | **31个** | 覆盖七大核心领域 |

**使用示例**:

```markdown
简洁引用: Shannon熵 [INFO-01] 定义了...
完整引用: 根据Shannon熵 [INFO-01]: H(X) = -Σ p(x) log p(x)，...
```

---

## 📋 目录

- [形式科学理论体系 - 快速参考](#形式科学理论体系---快速参考)
  - [1 📌 公式编号系统](#1--公式编号系统)
  - [📋 目录](#-目录)
  - [2 核心公式](#2-核心公式)
    - [2.1 信息论](#21-信息论)
    - [2.2 学习理论](#22-学习理论)
    - [2.3 控制论](#23-控制论)
    - [2.4 计算复杂性](#24-计算复杂性)
    - [2.5 分布式系统](#25-分布式系统)
    - [2.6 编程算法设计 ✨ **NEW!**](#26-编程算法设计--new)
  - [3 重要定理](#3-重要定理)
    - [3.1 不可判定性/不可能性](#31-不可判定性不可能性)
    - [3.2 可学习性](#32-可学习性)
    - [3.3 系统与控制](#33-系统与控制)
  - [4 关键常数](#4-关键常数)
    - [4.1 物理常数](#41-物理常数)
    - [4.2 信息理论界限](#42-信息理论界限)
    - [4.3 生物极限](#43-生物极限)
    - [4.4 计算极限](#44-计算极限)
  - [5 复杂性类](#5-复杂性类)
    - [5.1 时间复杂性层级](#51-时间复杂性层级)
    - [5.2 概率复杂性](#52-概率复杂性)
    - [5.3 量子复杂性](#53-量子复杂性)
  - [6 不可能三角](#6-不可能三角)
    - [6.1 CAP三角](#61-cap三角)
    - [6.2 虚拟化三角 (冯·诺依曼)](#62-虚拟化三角-冯诺依曼)
    - [6.3 三票不可能三角](#63-三票不可能三角)
  - [7 等价关系](#7-等价关系)
    - [7.1 跨视角等价](#71-跨视角等价)
    - [7.2 学习理论等价](#72-学习理论等价)
  - [8 快速决策树](#8-快速决策树)
    - [8.1 问题分析决策树](#81-问题分析决策树)
    - [8.2 技术栈选择树](#82-技术栈选择树)
  - [9 常用不等式](#9-常用不等式)
    - [9.1 信息论不等式](#91-信息论不等式)
    - [9.2 学习理论不等式](#92-学习理论不等式)
    - [9.3 复杂性不等式](#93-复杂性不等式)
  - [10 相关资源](#10-相关资源)

---

## 2 核心公式

> 📝 **使用说明**: 每个公式都有唯一编号，可在其他文档中引用
> 格式：`[分类-编号]` 如 `[INFO-01]` 表示信息论第1个公式

### 2.1 信息论

**[INFO-01] Shannon熵**:

```text
H(X) = -Σ p(x) log p(x)
H(X|Y) = -ΣΣ p(x,y) log p(x|y)
```

**[INFO-02] 互信息**:

```text
I(X;Y) = H(X) + H(Y) - H(X,Y)
       = H(X) - H(X|Y)
       = H(Y) - H(Y|X)
       = D_KL(P(X,Y) || P(X)P(Y))
```

> 💡 **详细分析**: 七视角深度解析见 [概念索引: 互信息](CONCEPT_CROSS_INDEX.md#互信息-mutual-information-七视角)

**[INFO-03] 条件互信息**:

```text
I(X;Y|Z) = H(X|Z) - H(X|Y,Z)
```

**[INFO-04] 数据处理不等式**:

```text
X → Y → Z  ⟹  I(X;Z) ≤ I(X;Y)
```

**[INFO-05] Fano不等式**:

```text
H(X|Y) ≤ H(P_e) + P_e log(|𝒳| - 1)
```

**[INFO-06] Shannon信道容量**:

```text
C = max I(X;Y)
    P(X)

AWGN信道: C = (1/2) log(1 + SNR)
```

**[INFO-07] 率失真函数**:

```text
R(D) = min I(X;X̂)
      E[d(X,X̂)]≤D
```

**[INFO-08] Kolmogorov复杂度**:

```text
K(x) = min{|p| : U(p) = x}
K(x|y) = min{|p| : U(p,y) = x}
K(x,y) ≤ K(x) + K(y) + O(1)
```

> 💡 **详细分析**: 七视角深度解析见 [概念索引: Kolmogorov复杂度](CONCEPT_CROSS_INDEX.md#kolmogorov复杂度-kolmogorov-complexity-七视角)

**[PHYS-01] Landauer极限**:

```text
E_min = kT ln 2  ≈ 2.9 × 10^(-21) J @ 300K
```

> 💡 **详细分析**: 七视角深度解析见 [概念索引: Landauer极限](CONCEPT_CROSS_INDEX.md#landauer极限-landauer-limit-七视角)

### 2.2 学习理论

**[LEARN-01] VC维与样本复杂度**:

```text
m ≥ O((d/ε²) log(1/δ))   # d = VC维
```

> 💡 **详细分析**: 七视角深度解析见 [概念索引: VC维](CONCEPT_CROSS_INDEX.md#vc维-vapnik-chervonenkis-dimension-七视角)

**[LEARN-02] 泛化误差界（PAC）**:

```text
P(|R(h) - R̂(h)| ≤ ε) ≥ 1 - δ

ε = O(√((d log(m/d) + log(1/δ)) / m))
```

**[LEARN-03] Rademacher复杂度**:

```text
R_m(ℋ) = E_σ[sup_{h∈ℋ} (1/m) Σᵢ σᵢ h(xᵢ)]

R(h) ≤ R̂(h) + 2R_m(ℋ) + √(log(1/δ) / 2m)
```

**[LEARN-04] No Free Lunch定理**:

```text
E_f[error(A₁, f)] = E_f[error(A₂, f)]  # 对所有学习算法
```

**[LEARN-05] Gold可学习性**:

```text
可从正例学习 ⟺ 有限弹性 ⟺ 有限告知数
```

### 2.3 控制论

**[CTRL-01] Ashby必要多样性定律**:

```text
V_controller ≥ V_system

其中 V = log |S| (系统状态空间大小)
```

> 💡 **详细分析**: 七视角深度解析见 [概念索引: Ashby定律](CONCEPT_CROSS_INDEX.md#ashby必要多样性定律-ashbys-law-of-requisite-variety-七视角)

**[CTRL-02] Data Rate定理**:

```text
R ≥ Σᵢ log₂ λᵢ   # λᵢ > 1 是不稳定极点模值
```

**[CTRL-03] PID控制**:

```text
u(t) = K_p e(t) + K_i ∫e(τ)dτ + K_d de/dt
```

**[CTRL-04] Lyapunov稳定性**:

```text
存在 V(x) s.t.
1. V(0) = 0, V(x) > 0 ∀x≠0
2. dV/dt ≤ 0  ⟹  稳定
3. dV/dt < 0  ⟹  渐近稳定
```

**[CTRL-05] Bode积分定理**:

```text
∫₀^∞ log|S(jω)| dω = 0   # S = 灵敏度函数
```

### 2.4 计算复杂性

**[COMP-01] 时间复杂性类**:

```text
P = DTIME(n^O(1))
NP = NTIME(n^O(1))
EXPTIME = DTIME(2^n^O(1))
```

**[COMP-02] 空间复杂性类**:

```text
L = DSPACE(log n)
PSPACE = DSPACE(n^O(1))
```

**[COMP-03] Savitch定理**:

```text
NSPACE(f(n)) ⊆ DSPACE(f(n)²)
```

**[COMP-04] 时间-空间权衡**:

```text
时间 × 空间 ≥ Ω(n²)  # 某些问题
```

### 2.5 分布式系统

**[DIST-01] 拜占庭容错阈值**:

```text
n ≥ 3f + 1   # n个节点容忍f个恶意节点
```

**[DIST-02] 最终一致性时间**:

```text
T_convergence = O(log n)   # Gossip协议
```

**[DIST-03] CAP权衡**:

```text
Consistency ∧ Availability ∧ Partition-tolerance
任选其二
```

> 💡 **详细分析**: 七视角深度解析见 [概念索引: CAP定理](CONCEPT_CROSS_INDEX.md#cap定理-cap-theorem-新增分布式核心)

### 2.6 编程算法设计 ✨ **NEW!**

**[PROG-01] UH-Cost 统一元模型**:

```text
UH-Cost = ⟨Σ, ⟶, κ, Φ⟩

其中：
  Σ  : 系统状态空间（State Space）
  ⟶  : 转换关系（Transition Relation）
  κ  : 代价函数（Cost Function）
  Φ  : 属性规范（Property Specifications）
```

> 💡 **详细分析**: 七视角深度解析见 [概念索引: UH-Cost统一元模型](CONCEPT_CROSS_INDEX.md#uh-cost-统一元模型-unified-hypergraph-cost-model-新增编程算法视角)

**[PROG-02] 三元视角分解**:

```text
System = ⟨C, E, D⟩

其中：
  C : 控制层（Control）   - 程序执行路径
  E : 执行层（Execution） - 状态转换规则
  D : 数据层（Data）      - 信息传递与变换
```

**[PROG-03] 操作语义推导规则**:

```text
小步语义（Small-Step）:
  ⟨stmt, σ⟩ → ⟨stmt', σ'⟩   # 单步转换

大步语义（Big-Step）:
  ⟨stmt, σ⟩ ⇓ σ'             # 最终结果

形式化：
  ─────────────────
   ⟨skip, σ⟩ ⇓ σ

  ⟨s₁, σ⟩ ⇓ σ'   ⟨s₂, σ'⟩ ⇓ σ''
  ──────────────────────────────
      ⟨s₁;s₂, σ⟩ ⇓ σ''
```

**[PROG-04] 20 维复杂度理论**:

```text
传统复杂度：
  T(n)  : 时间复杂度
  S(n)  : 空间复杂度

UH-Cost 扩展到 20 维：
  κ = (κ₁, κ₂, ..., κ₂₀)

关键维度：
  κ₁  : 时间（Time）
  κ₂  : 空间（Space）
  κ₃  : 通讯（Communication）
  κ₄  : 样本（Sample） - AI/学习理论
  κ₅  : 查询（Query）
  κ₆  : 证明（Proof） - 形式验证
  κ₇  : 电路（Circuit）
  κ₈  : 随机比特（Randomness）
  κ₉  : 量子（Quantum）
  κ₁₀ : 并行（Parallel）
  ...（详见 Program_Algorithm_Perspective/03.1）
```

> 💡 **详细文档**: [多维复杂度理论](Program_Algorithm_Perspective/03_Algorithm_Complexity/03.1_Multidimensional_Complexity.md)

**[PROG-05] 霍尔三元组（Hoare Triple）**:

```text
{P} C {Q}

其中：
  P : 前置条件（Precondition）
  C : 程序/命令（Command）
  Q : 后置条件（Postcondition）

公理语义规则：
  {P} skip {P}                        # Skip规则

  {P[e/x]} x := e {P}                 # 赋值规则

  {P} C₁ {Q}  {Q} C₂ {R}
  ────────────────────────            # 顺序组合
  {P} C₁;C₂ {R}

  {P ∧ b} C₁ {Q}  {P ∧ ¬b} C₂ {Q}
  ───────────────────────────────     # 条件分支
  {P} if b then C₁ else C₂ {Q}
```

> 💡 **完整工具链**: [Coq/Lean4/K-Framework/mCRL2](Program_Algorithm_Perspective/QUICK_REFERENCE.md)

---

## 3 重要定理

### 3.1 不可判定性/不可能性

| 定理 | 陈述 | 领域 |
|-----|------|------|
| **停机问题** | HALT(⟨M,w⟩)不可判定 | 计算理论 |
| **Rice定理** | 所有非平凡语义性质不可判定 | 计算理论 |
| **Gödel第一** | 一致系统含不可证命题 | 数理逻辑 |
| **Gödel第二** | 系统无法证明自身一致性 | 数理逻辑 |
| **CAP定理** | C ∧ A ∧ P不可兼得 | 分布式 |
| **FLP定理** | 异步网络无确定性共识 | 分布式 |

### 3.2 可学习性

| 定理 | 陈述 | 条件 |
|-----|------|------|
| **Gold定理** | 超限类不可从正例学习 | 仅正例 |
| **VC定理** | PAC可学习 ⟺ 有限VC维 | 一致情况 |
| **NFL定理** | 没有普遍最优算法 | 所有问题 |

### 3.3 系统与控制

| 定理 | 陈述 | 意义 |
|-----|------|------|
| **Ashby定律** | V_c ≥ V_s | 控制器复杂度下界 |
| **Data Rate** | R ≥ Σlog₂λᵢ | 信息速率下界 |
| **Shannon** | C = maxI(X;Y) | 信道容量上界 |
| **Landauer** | E ≥ kTln2 | 信息擦除能耗下界 |
| **Popek-Goldberg** | 敏感⊆特权 | 虚拟化条件 |

---

## 4 关键常数

### 4.1 物理常数

```text
k  = 1.380649 × 10^(-23) J/K     # Boltzmann常数
T  = 300 K                        # 室温
c  = 2.998 × 10^8 m/s             # 光速
ℏ  = 1.054572 × 10^(-34) J·s      # 约化Planck常数
```

### 4.2 信息理论界限

```text
Landauer极限 (300K):
  E_min = kT ln2 ≈ 2.9 × 10^(-21) J/bit

Shannon极限 (AWGN, SNR=10dB):
  C ≈ 3.46 bit/s/Hz

Bekenstein界 (1kg, 1m):
  I_max ≈ 10^69 bits
```

### 4.3 生物极限

```text
人脑:
  神经元: ~8.6 × 10^10
  突触:   ~10^14 - 10^15
  功耗:   ~20W
  效率:   ~10^16 ops/W (估计)

DNA:
  存储密度: ~10^19 bits/cm³
  纠错码:   Hamming距离≥1
```

### 4.4 计算极限

```text
现代GPU (H100):
  FLOPS:  ~10^15 FP16 ops/s
  功耗:   ~700W
  效率:   ~10^12 ops/W

量子计算:
  量子比特退相干时间: ~100μs (超导)
  量子门保真度: >99.9%
```

---

## 5 复杂性类

### 5.1 时间复杂性层级

```text
L ⊆ NL ⊆ P ⊆ NP ⊆ PSPACE ⊆ EXPTIME ⊆ NEXPTIME ⊆ 2-EXPTIME ⊆ ...
     ↓                ↓
    NC              coNP

已知: P ⊊ EXPTIME, NP ⊊ NEXPTIME
未知: P ?= NP, NP ?= coNP, P ?= PSPACE
```

### 5.2 概率复杂性

```text
P ⊆ BPP ⊆ PSPACE
P ⊆ RP ⊆ NP
ZPP = RP ∩ coRP
```

### 5.3 量子复杂性

```text
BQP 与 NP 不可比
P ⊆ BQP ⊆ PSPACE
BQP ⊊ PP ⊆ #P
```

---

## 6 不可能三角

### 6.1 CAP三角

```text
       Consistency (C)
            /\
           /  \
          /    \
         /  CA  \
        /  (CP)  \
       /__________\
      AP          CP
Available -------- Partition
                   Tolerant

选择:
- CA: 单数据中心 (传统RDBMS)
- CP: Paxos/Raft (HBase, MongoDB)
- AP: Eventual Consistency (Cassandra, DynamoDB)
```

### 6.2 虚拟化三角 (冯·诺依曼)

```text
       性能 (Performance)
            /\
           /  \
          /    \
         /      \
        /________\
    隔离          兼容性
 (Isolation)   (Compatibility)

权衡:
- 性能+兼容: 直接执行（无隔离）
- 性能+隔离: 硬件虚拟化（兼容性差）
- 隔离+兼容: 半虚拟化/解释（慢）
```

### 6.3 三票不可能三角

```text
       能量盈余
         /\
        /  \
       /    \
      /______\
  信息外化   冗余容错

现状:
- 前工业: 仅冗余容错 (农业文明)
- 工业化: 能量+冗余 (化石能源)
- 信息化: 能量+信息 (互联网)
- 2025+:  三票齐备 (AI时代)
```

---

## 7 等价关系

### 7.1 跨视角等价

```text
n阶反身性 (形式语言)
    ≡
n阶Meta-learning (AI)
    ≡
n阶反馈控制 (控制论)
    ≡
n层嵌套虚拟化 (图灵)
    ≡
n阶Reflexive Consent (分布式)
```

```text
CAP不可能 (分布式)
    ≡
Ashby定律 (控制论)
    ≡
Data Rate定理 (信息论)
    ≡
主权矩阵权衡 (图灵)
```

```text
Gödel不完备 (形式语言)
    ≡
停机问题 (图灵)
    ≡
K(x)不可计算 (信息论)
    ≡
完美AI对齐不可能 (AI)
    ≡
完美建模不可能 (控制论)
```

### 7.2 学习理论等价

```text
PAC可学习 ⟺ 有限VC维 (一致情况)
Gold可学习 ⟺ 有限弹性 (从正例)
Gold可学习 ⟺ 有限告知数 (从正例)
```

---

## 8 快速决策树

### 8.1 问题分析决策树

```text
问题类型?
├─ 判定问题
│  ├─ 语义性质? → Rice定理 (不可判定)
│  ├─ 停机问题? → 不可判定
│  └─ P类问题? → 多项式时间
│
├─ 学习问题
│  ├─ 有限VC维? → PAC可学习
│  ├─ 超限类+正例? → Gold定理 (不可学习)
│  └─ 有限弹性? → 可从正例学习
│
├─ 系统设计
│  ├─ 分布式? → 考虑CAP权衡
│  ├─ 虚拟化? → Popek-Goldberg + 性能权衡
│  └─ 控制系统? → Ashby定律 + Data Rate
│
└─ 信息度量
   ├─ 不确定性? → Shannon熵
   ├─ 共享信息? → 互信息
   └─ 最短描述? → Kolmogorov复杂度
```

### 8.2 技术栈选择树

```text
应用场景?
├─ AI/ML
│  ├─ 模型选择? → VC维 + 样本复杂度
│  ├─ 特征选择? → 互信息
│  └─ 压缩? → 信息瓶颈
│
├─ 系统架构
│  ├─ 单机? → 考虑冯·诺依曼瓶颈
│  ├─ 分布式? → CAP + FLP
│  └─ 虚拟化? → 主权矩阵 + 隔离熵
│
├─ 区块链
│  ├─ 共识? → BFT (n≥3f+1)
│  ├─ 一致性? → CAP (CP系统)
│  └─ 治理? → 反身性
│
└─ 控制系统
   ├─ 稳定性? → Lyapunov
   ├─ 优化? → MPC
   └─ 信息速率? → Data Rate定理
```

---

## 9 常用不等式

### 9.1 信息论不等式

```text
H(X) ≥ 0                              # 非负性
H(X|Y) ≤ H(X)                         # 条件减少熵
I(X;Y) ≥ 0                            # 非负性
I(X;Y) = I(Y;X)                       # 对称性
H(X,Y) ≤ H(X) + H(Y)                  # 次可加性
I(X;Y|Z) ≥ 0                          # 条件互信息非负
```

### 9.2 学习理论不等式

```text
R(h) ≤ R̂(h) + ε                     # 泛化误差界
VC(ℋ₁ ∩ ℋ₂) ≤ VC(ℋ₁) + VC(ℋ₂)       # VC维可加性
m ≥ O((d/ε²) log(1/δ))               # 样本复杂度
```

### 9.3 复杂性不等式

```text
TIME(f(n)) ⊆ SPACE(f(n))
SPACE(f(n)) ⊆ TIME(2^O(f(n)))
NSPACE(f(n)) ⊆ DSPACE(f(n)²)         # Savitch
```

---

## 10 相关资源

- [完整概念分析](CONCEPT_CROSS_INDEX.md) - 详细推导和证明
- [术语表](GLOSSARY.md) - 术语定义
- [FAQ](FAQ.md) - 常见问题
- [学习路径](LEARNING_PATHS.md) - 系统学习

---

**文档版本**: v1.0.0
**创建日期**: 2025-10-25
**维护状态**: ✅ 活跃维护
**公式总数**: 50+

**📐 打印本页作为速查手册！📐**-
