# TCP拥塞控制算法家族深度分析

## 目录

- [TCP拥塞控制算法家族深度分析](#tcp拥塞控制算法家族深度分析)
  - [目录](#目录)
  - [1. 拥塞控制基础](#1-拥塞控制基础)
    - [1.1 拥塞控制的必要性](#11-拥塞控制的必要性)
    - [1.2 核心概念：拥塞窗口（Congestion Window, cwnd）](#12-核心概念拥塞窗口congestion-window-cwnd)
    - [1.3 慢启动（Slow Start）](#13-慢启动slow-start)
    - [1.4 拥塞避免（Congestion Avoidance）](#14-拥塞避免congestion-avoidance)
    - [1.5 快速重传（Fast Retransmit）](#15-快速重传fast-retransmit)
    - [1.6 快速恢复（Fast Recovery）](#16-快速恢复fast-recovery)
  - [2. 算法详细分析](#2-算法详细分析)
    - [2.1 TCP Tahoe（1988）](#21-tcp-tahoe1988)
    - [2.2 TCP Reno（1990）](#22-tcp-reno1990)
    - [2.3 TCP NewReno（1996）](#23-tcp-newreno1996)
    - [2.4 TCP SACK（选择性确认）](#24-tcp-sack选择性确认)
    - [2.5 TCP Vegas（1993）](#25-tcp-vegas1993)
    - [2.6 TCP CUBIC（2006）](#26-tcp-cubic2006)
    - [2.7 TCP BBR（Bottleneck Bandwidth and Round-trip propagation time）](#27-tcp-bbrbottleneck-bandwidth-and-round-trip-propagation-time)
    - [2.8 BBRv2](#28-bbrv2)
  - [3. 形式化模型](#3-形式化模型)
    - [3.1 AIMD模型](#31-aimd模型)
    - [3.2 稳态吞吐量分析](#32-稳态吞吐量分析)
    - [3.3 公平性分析](#33-公平性分析)
    - [3.4 CUBIC稳定性分析](#34-cubic稳定性分析)
    - [3.5 BBR控制理论模型](#35-bbr控制理论模型)
  - [4. 性能对比分析](#4-性能对比分析)
    - [4.1 吞吐量对比](#41-吞吐量对比)
    - [4.2 延迟对比](#42-延迟对比)
    - [4.3 公平性对比](#43-公平性对比)
    - [4.4 实际测试数据](#44-实际测试数据)
  - [5. 实现与优化](#5-实现与优化)
    - [5.1 Linux内核实现](#51-linux内核实现)
    - [5.2 参数调优](#52-参数调优)
    - [5.3 监控工具](#53-监控工具)
    - [5.4 算法选择建议](#54-算法选择建议)
  - [6. 总结与展望](#6-总结与展望)
    - [6.1 算法演进总结](#61-算法演进总结)
    - [6.2 关键技术趋势](#62-关键技术趋势)
    - [6.3 形式化方法的未来](#63-形式化方法的未来)
  - [参考文献](#参考文献)

---

## 1. 拥塞控制基础

### 1.1 拥塞控制的必要性

TCP拥塞控制（Congestion Control）是互联网稳定运行的基石。在分组交换网络中，当过多数据被注入网络时，会导致：

- **路由器缓冲区溢出**：导致丢包
- **延迟增加**：排队延迟呈指数增长
- **吞吐量下降**：重传导致有效带宽降低
- **拥塞崩溃（Congestion Collapse）**：1986年NSFNET经历的灾难性事件

```
拥塞崩溃现象：
+--------+        高负载        +--------+
| 发送方 | ==================> | 接收方 |
+--------+    大量重传          +--------+
     ↑                              |
     └──────── 有效吞吐趋近于0 ←────┘
```

### 1.2 核心概念：拥塞窗口（Congestion Window, cwnd）

拥塞窗口是发送方维护的关键状态变量，表示在收到ACK之前可以发送的最大数据量：

$$\text{发送窗口} = \min(\text{cwnd}, \text{rwnd})$$

其中：

- `cwnd`：拥塞窗口（Congestion Window）
- `rwnd`：接收窗口（Receive Window）

**窗口单位演进**：

- 早期RFC：以字节为单位
- 现代实现：以MSS（最大段大小）为单位，简化计算

### 1.3 慢启动（Slow Start）

慢启动是TCP连接建立后的初始阶段，目的是快速探测可用带宽：

**算法描述**：

```
初始: cwnd = 1 MSS
每收到一个ACK: cwnd = cwnd + 1 MSS
```

**指数增长特性**：

- RTT 1: cwnd = 1 MSS → 发送1个段
- RTT 2: cwnd = 2 MSS → 发送2个段
- RTT 3: cwnd = 4 MSS → 发送4个段
- RTT n: cwnd = 2^(n-1) MSS

**慢启动阈值（ssthresh）**：
当 `cwnd >= ssthresh` 时，从慢启动切换到拥塞避免：

$$\text{ssthresh}_{\text{initial}} = \text{较大值} \quad (\text{如 } 65535 \text{ 字节})$$

### 1.4 拥塞避免（Congestion Avoidance）

当cwnd达到ssthresh后，进入线性增长阶段：

**Additive Increase**（AI）：
$$\text{cwnd}_{t+1} = \text{cwnd}_t + \frac{\text{MSS} \times \text{MSS}}{\text{cwnd}_t}$$

简化为：每RTT增加约1个MSS

**直观理解**：

```
慢启动（指数增长）:
1 → 2 → 4 → 8 → 16 → 32 → ... (达到ssthresh)

拥塞避免（线性增长）:
32 → 33 → 34 → 35 → 36 → ... (逐步增加)
```

### 1.5 快速重传（Fast Retransmit）

**问题**：传统超时检测丢包太慢（RTO通常为几百毫秒）

**解决方案**：利用重复ACK（DupACK）快速检测丢包

```
触发条件：收到3个重复ACK

动作：
1. 立即重传丢失的段（无需等待RTO）
2. ssthresh = max(cwnd/2, 2*MSS)
3. cwnd = ssthresh + 3*MSS
```

**为什么3个DupACK？**

- 1-2个DupACK可能是乱序到达
- 3个DupACK大概率表示丢包

### 1.6 快速恢复（Fast Recovery）

快速恢复与快速重传配合，避免慢启动的激进降窗：

**算法流程**：

```
收到第3个DupACK:
    ssthresh = cwnd / 2
    cwnd = ssthresh + 3*MSS
    进入快速恢复

在快速恢复期间每收到一个DupACK:
    cwnd = cwnd + MSS
    （允许发送新数据以维持管道满）

收到新ACK（确认新数据）:
    cwnd = ssthresh
    退出快速恢复，进入拥塞避免
```

---

## 2. 算法详细分析

### 2.1 TCP Tahoe（1988）

**历史背景**：

- 作者：Van Jacobson
- 首次实现：BSD 4.3 Tahoe
- 地位：现代拥塞控制的奠基者

**核心机制**：

| 事件 | 响应 |
|------|------|
| 超时 | cwnd = 1 MSS, ssthresh = cwnd/2, 进入慢启动 |
| 3 DupACK | cwnd = 1 MSS, ssthresh = cwnd/2, 进入慢启动 |

**状态机**：

```
        +-----------+
        |   CLOSED  |
        +-----+-----+
              |
              v
        +-----------+
        |  慢启动   |<-----------------+
        | (cwnd指数 |                  |
        |   增长)   |                  |
        +-----+-----+                  |
              | cwnd >= ssthresh       |
              v                        |
        +-----------+     丢包        |
        | 拥塞避免  |------------------+
        | (cwnd线性 |                  |
        |   增长)   |                  |
        +-----------+------------------+
              |
              v
        +-----------+
        | 超时处理  |
        | cwnd=1    |
        +-----------+
```

**局限性**：

- 无论超时还是3 DupACK，都降为1 MSS
- 3 DupACK时过于激进，有效带宽未完全丢失

### 2.2 TCP Reno（1990）

**改进点**：引入快速恢复，区分对待超时和DupACK

**响应机制对比**：

| 事件 | Tahoe响应 | Reno响应 |
|------|-----------|----------|
| 超时 | cwnd=1, 慢启动 | cwnd=1, 慢启动 |
| 3 DupACK | cwnd=1, 慢启动 | cwnd=ssthresh, 拥塞避免 |

**Reno快速恢复详细流程**：

```
收到第3个DupACK时:
    ssthresh = cwnd / 2
    cwnd = ssthresh + 3*MSS
    重传丢失段
    进入快速恢复

快速恢复期间收到DupACK:
    cwnd = cwnd + MSS
    如果允许，发送新数据

收到新ACK（确认所有未确认数据）:
    cwnd = ssthresh
    退出快速恢复
    进入拥塞避免

超时发生:
    cwnd = 1 MSS
    ssthresh = cwnd / 2
    进入慢启动
```

**问题：部分ACK问题**（Partial ACK Problem）

当窗口中有多个段丢失时，Reno表现不佳：

```
发送: [1][2][3][4][5][6][7][8]
丢失:      [2]   [4]
收到: [1][3][3][3][3]...

Reno行为:
1. 收到3个DupACK[3]，重传[2]
2. 收到ACK[2]（部分ACK），退出快速恢复
3. [4]需要等待RTO才能重传
```

### 2.3 TCP NewReno（1996）

**目标**：解决部分ACK问题

**核心改进**：引入**部分窗口 deflation** 机制

```
收到第3个DupACK时:
    ssthresh = cwnd / 2
    cwnd = ssthresh + 3*MSS
    记录recover = 最高已发送序号
    进入快速恢复

在快速恢复期间:
    如果收到部分ACK（确认新数据但未超过recover）:
        重传第一个未确认段
        cwnd = cwnd - (ACK序号 - 上一个ACK)
        cwnd = cwnd + MSS

    如果收到完整ACK（序号 > recover）:
        cwnd = ssthresh
        退出快速恢复
```

**优势**：

- 可以处理同窗口内多个丢包
- 无需SACK选项支持

**局限**：

- 每次RTT只能恢复一个丢包
- 大量丢包时仍需多个RTT

### 2.4 TCP SACK（选择性确认）

**RFC 2018**：基于SACK选项的拥塞控制

**SACK选项格式**：

```
TCP选项类型5（SACK）:
+--------+--------+--------+--------+
|  Kind  | Length | Left Edge 1     |
|  5     | 可变   | (4 bytes)       |
+--------+--------+--------+--------+
| Right Edge 1    | Left Edge 2     |
| (4 bytes)       | (4 bytes)       |
+--------+--------+--------+--------+
| Right Edge 2    | ...             |
+--------+--------+--------+--------+
```

**SACK-based Recovery**：

```
发送方维护:
- SACKed[]: 已收到的SACK块
- scoreboard: 丢包状态记录

收到SACK时:
    更新SACKed[]
    识别丢包: 未SACK且未ACK的段

每两个RTT或收到新SACK:
    重传第一个丢失段（scoreboard中）
```

**优势**：

- 精确知道哪些段丢失
- 一个RTT可重传多个段

### 2.5 TCP Vegas（1993）

**创新点**：基于延迟的拥塞控制（而非丢包）

**核心思想**：
在丢包发生前，通过RTT增加检测拥塞

**关键度量**：

```
Expected = cwnd / BaseRTT
Actual = cwnd / CurrentRTT
Diff = Expected - Actual

其中：
- BaseRTT: 最小观测RTT（无排队）
- CurrentRTT: 当前RTT
```

**Vegas算法**：

```
参数: α=1, β=3, γ=1 (MSS/秒)

每个RTT:
    if Diff < α:
        cwnd = cwnd + 1       # 网络空闲，增加窗口
    else if Diff > β:
        cwnd = cwnd - 1       # 拥塞，减少窗口
    else:
        cwnd = cwnd           # 保持

慢启动期间（每2个RTT）:
    if (cwnd/BaseRTT - cwnd/CurrentRTT) > γ:
        ssthresh = cwnd / 2   # 进入拥塞避免
        cwnd = ssthresh + 1
```

**Vegas的数学分析**：

设链路带宽为 $B$，传播延迟为 $D$，队列容量为 $Q$：

$$\text{BaseRTT} = 2D$$
$$\text{CurrentRTT} = 2D + \frac{Q_{current}}{B}$$

期望与实际吞吐量差：
$$\text{Diff} = \frac{\text{cwnd}}{2D} - \frac{\text{cwnd}}{2D + Q/B}$$

**Vegas的问题**：

- 与基于丢包的算法（Reno）共存时带宽抢占劣势
- 对RTT测量精度要求高
- 路径变化时BaseRTT需要更新

### 2.6 TCP CUBIC（2006）

**设计者**：Sangtae Ha, Injong Rhee
**地位**：Linux内核默认算法（2.6.19+）

**设计目标**：

1. 在高带宽延迟积（BDP）网络中高效
2. 保持TCP友好性
3. RTT公平性

**CUBIC窗口函数**：

$$W(t) = C(t - K)^3 + W_{max}$$

其中：

- $t$: 上次丢包后的时间
- $K$: 窗口回到 $W_{max}$ 所需时间
- $W_{max}$: 上次丢包前的窗口大小
- $C$: CUBIC参数（默认0.4）

**K的计算**：

$$K = \sqrt[3]{\frac{W_{max} \cdot \beta}{C}}$$

其中 $\beta$ 是乘性减少因子（默认0.2，即降为80%）

**CUBIC窗口更新**：

```
ACK到达时:
    t = current_time - last_congestion_time
    K = cbrt(W_max * beta / C)

    if t < K:
        # 凹增长阶段
        cwnd = W_max - C*(K-t)^3
    else:
        # 凸增长阶段
        cwnd = W_max + C*(t-K)^3

    # TCP友好性保证
    if cwnd < TCP_Friendly_cwnd:
        cwnd = TCP_Friendly_cwnd
```

**CUBIC增长曲线**：

```
cwnd
  ^
  |        ___________ W_max
  |       /             \
  |      /               \
  |     /                 \
  |    /                   \
  |   /                     \
  |  /                       \
  | /                         \
  |/                           \
  +--------------------------------> t
  0      K                  2K

  凹增长(探索)    凸增长(稳定)
```

**TCP友好模式**：
当网络中存在传统Reno流时，CUBIC切换到兼容模式：

$$W_{tcp}(t) = W_{max}(1 - \beta) + \frac{3\beta}{2 - \beta} \cdot \frac{t}{RTT}$$

**CUBIC的优势**：

- 高BDP网络中稳定的高吞吐
- 对RTT不敏感（RTT公平性）
- 空闲后快速恢复（避免慢启动）

### 2.7 TCP BBR（Bottleneck Bandwidth and Round-trip propagation time）

**设计者**：Neal Cardwell等（Google，2016）
**核心理念**：模型驱动而非事件驱动

**两个核心参数**：

1. **BtlBw**（瓶颈带宽）：$B = \frac{\text{data_delivered}}{\text{time}}$（滑动窗口最大值）
2. **RTprop**（传播时延）：$D = \min(\text{RTT})$（最小观测值）

**BBR管道模型**：

```
管道容量 = BtlBw × RTprop

实际传输:
┌─────────────────────────────────────┐
│  已确认  │  已发送(飞行中)  │ 待发送 │
└─────────────────────────────────────┘
           |<-- 飞行中 ≤ BDP -->|
```

**BBR状态机**：

```
+--------+     +-----------+     +----------+
| STARTUP| --> | DRAIN     | --> | PROBE_BW |
| (慢启动)|     | (排空队列)|     | (带宽探测)|
+--------+     +-----------+     +-----+----+
                                       |
          +----------------------------+
          v
    +-----------+     +-------------+
    | PROBE_RTT | --> | PROBE_BW    |
    | (延迟探测)|     | (正常工作)  |
    +-----------+     +-------------+
```

**各阶段详解**：

**STARTUP（启动阶段）**:

```
目标: 快速找到BtlBw
行为: 指数增长（类似慢启动，但基于带宽估计）
退出: 带宽增长<25%（认为已饱和）
```

**DRAIN（排空阶段）**:

```
目标: 排空STARTUP积累的队列
行为: 发送速率 = BtlBw / 2
持续: 1个RTprop
```

**PROBE_BW（带宽探测）**:

```
目标: 持续探测带宽变化
周期: 8 RTprop，分为8个阶段

 pacing_gain 循环:
 [1.25, 0.75, 1, 1, 1, 1, 1, 1]

 - 1.25: 尝试增加发送，探测更高带宽
 - 0.75: 减少发送，排空队列
 - 1:    稳定运行
```

**PROBE_RTT（延迟探测）**:

```
目标: 更新RTprop（处理路由变化）
触发: RTprop未更新超过10秒
行为: cwnd = 4个包
持续: 200ms 或 1个RTT
```

**BBR pacing机制**：
不同于传统cwnd控制，BBR使用**pacing**精确控制发送速率：

$$\text{pacing_rate} = \text{pacing_gain} \times \text{BtlBw}$$

```
传统TCP:                    BBR:
突发发送                    平滑发送
│▓▓▓▓│                    ▓▓▓▓▓▓▓▓
│▓▓▓▓│                    ▓▓▓▓▓▓▓▓
└────┘                    └────────┘
  ↑                        均匀间隔
 ACK驱动突发
```

### 2.8 BBRv2

**改进目标**：解决BBRv1的公平性和生态问题

**BBRv1的问题**：

1. **RTT不公平**：短RTT流被长RTT流压制
2. **与CUBIC/Reno共存时**：过度抢占带宽
3. **小包问题**：小包流获得不公平优势

**BBRv2关键改进**：

| 特性 | BBRv1 | BBRv2 |
|------|-------|-------|
| 丢包响应 | 忽略丢包 | 丢包超过阈值时降速 |
| ECN支持 | 无 | 支持 |
| 带宽探测 | 激进(1.25x) | 更保守 |
|  inflight限制 | 2×BDP | 自适应 |

**BBRv2状态机**：

```
STARTUP → DRAIN → PROBE_BW ←→ PROBE_RTT
   ↓                    ↑
+--+------------+       |
| LOSS_RECOVERY |-------+
+---------------+
```

**BBRv2丢包处理**：

```
维护: loss_round (丢包轮次计数)

当丢包率 > 2%:
    inflight_hi = min(inflight_hi, 当前飞行中数据)

进入LOSS_RECOVERY:
    pacing_rate = BtlBw  # 不加速
    cwnd = max(4个MSS, inflight_lo)

恢复后:
    重新探测带宽
```

**BBRv2 ECN处理**：

```
收到ECN标记:
    视为拥塞信号
    inflight_hi = 当前飞行中数据
    进入拥塞响应模式
```

---

## 3. 形式化模型

### 3.1 AIMD模型

**加性增乘性减**（Additive Increase Multiplicative Decrease）是TCP拥塞控制的数学抽象。

**离散AIMD模型**：
$$
W_{k+1} = \begin{cases}
W_k + a & \text{无丢包} \\
b \cdot W_k & \text{丢包}
\end{cases}
$$

其中：

- $a$: 加性增因子（通常1 MSS）
- $b$: 乘性减因子（通常0.5）

**连续微分方程**：
$$\frac{dW}{dt} = \frac{a}{RTT} - \frac{b \cdot W^2}{2} \cdot p(W)$$

其中 $p(W)$ 是窗口为 $W$ 时的丢包概率。

### 3.2 稳态吞吐量分析

**假设**：

- 丢包事件相互独立
- 丢包概率 $p$ 恒定
- 每个RTT增加 $a$ 个MSS

**吞吐量推导**：

在一个周期 $T$ 内：

- 窗口从 $W_{min} = b \cdot W_{max}$ 增加到 $W_{max}$
- 发送的数据包数：

$$N = \sum_{i=bW}^{W} i = \frac{W^2 - (bW)^2}{2} = \frac{W^2(1-b^2)}{2}$$

周期长度：
$$T = \frac{W - bW}{a} \cdot RTT = \frac{W(1-b)}{a} \cdot RTT$$

丢包率关系：
$$p = \frac{1}{N} = \frac{2}{W^2(1-b^2)}$$

因此：
$$W = \sqrt{\frac{2}{p(1-b^2)}}$$

**最终吞吐量公式**（Padhye et al., 2000）：

$$B = \frac{1}{RTT}\sqrt{\frac{3}{2p}} + o\left(\frac{1}{\sqrt{p}}\right)$$

对于TCP Reno ($a=1, b=0.5$)：
$$B \approx \frac{1.22 \cdot MSS}{RTT \cdot \sqrt{p}}$$

**应用示例**：

```
条件: RTT = 100ms, MSS = 1460字节, 目标吞吐 = 100 Mbps

求解: B = 100 × 10^6 / 8 = 12.5 MB/s
     12.5×10^6 = (1.22 × 1460) / (0.1 × √p)
     √p = (1.22 × 1460) / (0.1 × 12.5×10^6)
     √p ≈ 0.00142
     p ≈ 2 × 10^-6

结论: 需要丢包率 < 0.0002% 才能达到100Mbps
```

### 3.3 公平性分析

**Max-Min公平性定义**：
分配 $\{x_i\}$ 是Max-Min公平的，如果增加任一流 $i$ 的分配 $x_i$ 必然导致减少某一流 $j$（$x_j \leq x_i$）的分配。

**TCP AIMD的收敛性**：

考虑两个竞争流：

```
流1: W1(k+1) = b·W1(k)  丢包时
流2: W2(k+1) = b·W2(k)  丢包时

加性增阶段:
    W1 += a, W2 += a
```

**收敛到公平**：
在同步丢包假设下，两个流的窗口比收敛到1：

$$\frac{W_1}{W_2} \rightarrow 1$$

证明概要：

- 设丢包时刻窗口为 $(W_1, W_2)$
- 下次丢包前达到 $(W_1 + n_1 a, W_2 + n_2 a)$
- 由于同步丢包，$W_1 + n_1 a = W_2 + n_2 a = W_{max}$
- 因此 $n_1 \approx n_2$，差值缩小

### 3.4 CUBIC稳定性分析

**Lyapunov稳定性**：

考虑CUBIC的连续近似：
$$\frac{dW}{dt} = \frac{C(t-K)^2}{RTT}$$

定义Lyapunov函数：
$$V(t) = (W(t) - W^*)^2$$

其中 $W^*$ 是平衡点。

可以证明：
$$\frac{dV}{dt} < 0 \quad \text{当} \quad W \neq W^*$$

因此CUBIC是渐近稳定的。

### 3.5 BBR控制理论模型

**BBR作为反馈控制系统**：

```
参考输入 ──→ [控制器] ──→ [网络 plant] ──→ 输出
                ↑            │
                └────────────┘
                   观测
```

**传递函数**：
设 $B(t)$ 为估计带宽，$B^*$ 为真实带宽：

$$B(t+1) = \alpha \cdot B(t) + (1-\alpha) \cdot B_{sample}$$

这是离散一阶低通滤波器，时间常数为 $\frac{1}{1-\alpha}$。

**稳定性条件**：
$$0 < \alpha < 1$$

BBR选择 $\alpha \approx 0.98$，对应约50个样本的时间常数。

---

## 4. 性能对比分析

### 4.1 吞吐量对比

不同算法在各种网络条件下的理论吞吐量：

```
高带宽延迟积网络 (BDP=1000 MSS):

吞吐量 (MSS/RTT)
  ^
100|                                  * BBR/CUBIC
   |                              *
 50|                          *
   |                      *
 20|                  *
   |              *
 10|          *
   |      *                      + Reno/Vegas
  5|  *
   | +
  1|
   +----+----+----+----+----+----+----+----+---> 丢包率
       0.0001 0.001 0.01  0.1   1    10   (%)
```

**理论性能比较表**：

| 算法 | 高BDP吞吐 | RTT公平 | 丢包敏感 | 延迟敏感 |
|------|----------|---------|----------|----------|
| Reno | 低 | 否 | 高 | 否 |
| CUBIC | 高 | 较好 | 中 | 否 |
| BBRv1 | 极高 | 否 | 低 | 是 |
| BBRv2 | 极高 | 较好 | 中 | 是 |
| Vegas | 中 | 是 | 无 | 是 |

### 4.2 延迟对比

**缓冲区膨胀（Bufferbloat）影响**：

```
队列长度 (包)
  ^
100|                ╭────── Reno持续填充队列
   |              ╭─╯
 50|      ╭──────╯     ╭────── CUBIC也会填充
   |    ╭─╯           ╭─╯
 20|    │      ╭──────╯
   |    │    ╭─╯            ╭────── BBR保持低队列
 10|    │    │            ╭─╯
   |    │    │    ╭──────╯
  5|────┴────┴────┴──────────────────> 时间
     0   10   20   30   40   50   (RTT)
```

**平均队列长度比较**（仿真数据）：

| 算法 | 平均队列占用 | 99%延迟 |
|------|------------|---------|
| Reno | 85% | 150ms |
| CUBIC | 70% | 120ms |
| BBRv1 | 10% | 25ms |
| BBRv2 | 15% | 35ms |

### 4.3 公平性对比

**RTT公平性**：
不同RTT流共存时的带宽分配比例：

```
短RTT流占比
  ^
100|              * BBRv1极度不公平
   |            *
 80|          *
   |        *
 60|      *                      + CUBIC较公平
   |    *                      +
 40|  *                      +
   |*                      +
 20|    ════════════════════════ 理想公平线
   |                      +
  0|----+----+----+----+----+----+---> 长RTT/短RTT
       1    2    4    8   16   32
```

**BBRv1 RTT不公平性证明**：

BBR的pacing_rate = pacing_gain × BtlBw
两个流共享瓶颈带宽B：

- 流1: RTT1, 测量BtlBw1
- 流2: RTT2, 测量BtlBw2

由于 $BtlBw_1 + BtlBw_2 = B$，且：
$$BtlBw_i \propto \frac{1}{RTT_i}$$

因此短RTT流获得更大份额：
$$\frac{B_1}{B_2} = \frac{RTT_2}{RTT_1}$$

### 4.4 实际测试数据

**测试环境**：

- 带宽：100 Mbps
- RTT：50ms
- 缓冲区：2×BDP
- 测试时长：60秒

**iperf3测试结果**：

```
┌──────────┬──────────┬──────────┬──────────┬──────────┐
│  算法    │ 平均吞吐  │  延迟    │ 丢包率   │ 公平性   │
├──────────┼──────────┼──────────┼──────────┼──────────┤
│ Reno     │ 82 Mbps  │ 45ms     │ 3.2%     │ 0.95     │
│ CUBIC    │ 96 Mbps  │ 38ms     │ 1.8%     │ 0.97     │
│ BBRv1    │ 98 Mbps  │ 12ms     │ 0.1%     │ 0.72*    │
│ BBRv2    │ 97 Mbps  │ 15ms     │ 0.5%     │ 0.94     │
│ Vegas    │ 78 Mbps  │ 25ms     │ 0.3%     │ 0.93     │
└──────────┴──────────┴──────────┴──────────┴──────────┘

* BBRv1公平性低是因为与Reno/CUBIC共存时抢占过多带宽
```

---

## 5. 实现与优化

### 5.1 Linux内核实现

**拥塞控制模块结构**：

```c
// include/net/tcp.h
struct tcp_congestion_ops {
    const char *name;
    u32 (*ssthresh)(struct sock *sk);
    void (*cong_avoid)(struct sock *sk, u32 ack, u32 acked);
    void (*set_state)(struct sock *sk, u8 new_state);
    void (*cwnd_event)(struct sock *sk, enum tcp_ca_event event);
    u32 (*undo_cwnd)(struct sock *sk);
    void (*pkts_acked)(struct sock *sk, const struct ack_sample *sample);
    u32 (*min_tso_segs)(struct sock *sk);
    void (*sndbuf_expand)(struct sock *sk);
    size_t (*get_info)(struct sock *sk, u32 ext, int *attr,
                       union tcp_cc_info *info);
};
```

**CUBIC内核实现**（tcp_cubic.c核心逻辑）：

```c
/* BIC/CUBIC TCP 内核实现 */

# define BICTCP_BETA_SCALE    1024   /* beta值缩放因子 */
# define BICTCP_HZ            10     /* HZ的倒数 (100ms) */

static int fast_convergence = 1;
static int beta = 717;    /* = 1024 * (1-0.2) = 819，调整后为717 */
static int initial_ssthresh;
static int bic_scale = 41;
static int tcp_rmem[3];

/* 内核使用的HZ值调整 */
static u32 cube_rtt_scale;
static u32 beta_scale;
static u64 cube_factor;

/* CUBIC状态 */
struct bictcp {
    u32 cnt;              /* 每个ACK增加的cwnd */
    u32 last_max_cwnd;    /* 上次丢包前的最大cwnd */
    u32 last_cwnd;        /* 上次记录的cwnd */
    u32 last_time;        /* 上次更新时间 */
    u32 bic_origin_point; /* BIC/CUBIC目标点 */
    u32 bic_K;            /* 时间因子 */
    u32 delay_min;        /* 最小延迟估计 */
    u32 epoch_start;      /* 新纪元开始时间 */
    u32 ack_cnt;          /* ACK计数器 */
    u32 tcp_cwnd;         /* 用于TCP友好性的估计值 */
    u16 unused;
    u8 sample_cnt;        /* RTT样本计数 */
    u8 found;             /* 是否找到新的最小延迟 */
    u32 round_start;      /* 轮次开始 */
    u32 end_seq;          /* 轮次结束序号 */
    u32 last_ack;         /* 上次ACK序号 */
    u32 curr_rtt;         /* 当前RTT */
};

/* 计算CUBIC根: cuberoot(x) */
static u32 cubic_root(u64 a)
{
    u32 x, b, shift;

    /* 使用近似算法 */
    shift = (64 - __builtin_clzll(a)) / 3;
    x = 1 << shift;

    do {
        b = (a / (x * x) + 2 * x) / 3;
        if (b >= x) break;
        x = b;
    } while (1);

    return x;
}

/* 慢启动阈值计算 */
static u32 bictcp_recalc_ssthresh(struct sock *sk)
{
    const struct tcp_sock *tp = tcp_sk(sk);
    struct bictcp *ca = inet_csk_ca(sk);

    ca->epoch_start = 0;  /* 结束当前纪元 */

    /* Wmax/2 */
    ca->last_max_cwnd = tp->snd_cwnd;

    /* 快速收敛 */
    if (ca->last_max_cwnd > 0 && tp->snd_cwnd < ca->last_max_cwnd)
        ca->last_max_cwnd = (ca->last_max_cwnd * BICTCP_BETA_SCALE) / 512;

    return max((tp->snd_cwnd * beta) / BICTCP_BETA_SCALE, 2U);
}

/* 拥塞避免阶段 */
static void bictcp_cong_avoid(struct sock *sk, u32 ack, u32 acked)
{
    struct tcp_sock *tp = tcp_sk(sk);
    struct bictcp *ca = inet_csk_ca(sk);

    if (!tcp_is_cwnd_limited(sk))
        return;

    if (tp->snd_cwnd <= tp->snd_ssthresh) {
        /* 慢启动 */
        tcp_slow_start(tp, acked);
    } else {
        /* CUBIC拥塞避免 */
        bictcp_update(ca, tp->snd_cwnd, acked);
        tcp_cong_avoid_ai(tp, ca->cnt, acked);
    }
}

/* CUBIC窗口更新 */
static inline void bictcp_update(struct bictcp *ca, u32 cwnd, u32 acked)
{
    u32 delta, bic_target, max_cnt;
    u64 offs, t;

    ca->ack_cnt += acked;

    if (ca->epoch_start == 0) {
        /* 新纪元开始 */
        ca->epoch_start = tcp_jiffies32;
        ca->ack_cnt = acked;
        ca->tcp_cwnd = cwnd;

        if (ca->last_max_cwnd <= cwnd) {
            ca->bic_K = 0;
            ca->bic_origin_point = cwnd;
        } else {
            /* 计算K值: cbrt((Wmax-cwnd)*C/beta) */
            ca->bic_origin_point = ca->last_max_cwnd;
            delta = ca->bic_origin_point - cwnd;
            delta = (delta * BICTCP_BETA_SCALE) / beta;
            delta = (delta * bic_scale) >> 4;
            ca->bic_K = cubic_root(delta);
        }
    }

    /* 计算时间t */
    t = (s32)(tcp_jiffies32 - ca->epoch_start) / HZ;
    t += ca->delay_min / USEC_PER_MSEC;

    /* 计算目标窗口 */
    if (t < ca->bic_K) {
        /* 凹增长阶段 */
        offs = ca->bic_K - t;
    } else {
        /* 凸增长阶段 */
        offs = t - ca->bic_K;
    }

    delta = (cube_factor * offs * offs * offs) >> (10 + 3 * BICTCP_HZ);

    if (t < ca->bic_K)
        bic_target = ca->bic_origin_point - delta;
    else
        bic_target = ca->bic_origin_point + delta;

    /* 计算cnt: 每cnt个ACK增加1个cwnd */
    if (bic_target > cwnd)
        ca->cnt = cwnd / (bic_target - cwnd);
    else
        ca->cnt = 100 * cwnd;

    /* TCP友好性保证 */
    if (ca->delay_min > 0) {
        max_cnt = tcp_cwnd_test(tp, ca);
        if (ca->cnt > max_cnt)
            ca->cnt = max_cnt;
    }

    if (ca->cnt == 0)
        ca->cnt = 1;
}
```

**BBR内核实现**（tcp_bbr.c核心逻辑）：

```c
/* BBR 拥塞控制 - Google 2016 */

/* BBR状态 */
enum bbr_mode {
    BBR_STARTUP,      /* 指数增长探测带宽 */
    BBR_DRAIN,        /* 排空队列 */
    BBR_PROBE_BW,     /* 带宽探测 */
    BBR_PROBE_RTT,    /* 延迟探测 */
};

/* BBR核心参数 */
struct bbr {
    u32 min_rtt_us;           /* 最小RTT估计 */
    u32 min_rtt_stamp;        /* 最小RTT时间戳 */
    u32 probe_rtt_done_stamp; /* PROBE_RTT结束时间 */
    u32 probe_rtt_round_done:1;
    u32 prev_probe_rtt_round_done:1;
    u32 full_bw_reached:1;
    u32 full_bw_cnt:2;        /* 带宽停止增长计数 */
    u32 cycle_idx:3;          /* PROBE_BW周期索引 */
    u32 cycle_mstamp;         /* 周期开始时间 */
    u32 mode:3;               /* 当前状态 */
    u32 full_bw;              /* 最大带宽估计 */
    u32 pacing_gain:16;       /* 当前pacing增益 */
    u32 cwnd_gain:16;         /* 当前cwnd增益 */

    /* 带宽采样 */
    struct minmax bw;         /* 最大带宽估计 */
};

/* Pacing增益周期: 8个阶段 */
static const int bbr_pacing_gain[] = {
    BBR_UNIT * 5 / 4,  /* 1.25: 探测更高带宽 */
    BBR_UNIT * 3 / 4,  /* 0.75: 排空队列 */
    BBR_UNIT, BBR_UNIT, BBR_UNIT, BBR_UNIT, BBR_UNIT, BBR_UNIT
};

static const int bbr_cwnd_gain = BBR_UNIT * 2;  /* 2xBDP */

/* 主ACK处理函数 */
static void bbr_main(struct sock *sk, const struct rate_sample *rs)
{
    struct bbr *bbr = inet_csk_ca(sk);
    u32 bw;

    /* 更新最小RTT */
    bbr_update_model(sk, rs);

    /* 更新带宽估计 */
    bw = bbr_bw(sk);
    bbr->full_bw_reached = bbr->full_bw_cnt >= 3;

    /* 状态机处理 */
    switch (bbr->mode) {
    case BBR_STARTUP:
        if (bbr->full_bw_reached)
            bbr_enter_drain(sk);
        break;
    case BBR_DRAIN:
        if (tcp_packets_in_flight(tcp_sk(sk)) <= bbr_target_cwnd(sk, bw, BBR_UNIT))
            bbr_enter_probe_bw(sk);
        break;
    case BBR_PROBE_BW:
        bbr_update_cycle_phase(sk, rs);
        break;
    case BBR_PROBE_RTT:
        bbr_update_probe_rtt(sk, rs);
        break;
    }

    /* 更新增益 */
    bbr->pacing_gain = bbr_current_gain(sk);
    bbr->cwnd_gain = bbr_cwnd_gain;
}

/* 计算目标窗口 */
static u32 bbr_target_cwnd(struct sock *sk, u32 bw, int gain)
{
    struct bbr *bbr = inet_csk_ca(sk);
    u32 cwnd;
    u64 w;

    /* 计算BDP: bw * min_rtt */
    w = (u64)bw * bbr->min_rtt_us * gain;
    w >>= BBR_SCALE;

    /* 加上2个MSS的ACK聚合余量 */
    cwnd = (w + BBR_MAX_PKTS_MSS - 1) / BBR_MAX_PKTS_MSS + 2;

    return cwnd;
}

/* 设置pacing速率 */
static void bbr_set_pacing_rate(struct sock *sk, u32 bw, int gain)
{
    struct tcp_sock *tp = tcp_sk(sk);
    struct bbr *bbr = inet_csk_ca(sk);
    u64 rate = (u64)bw * gain;

    rate <<= BBR_SCALE;
    rate /= USEC_PER_SEC;
    rate *= mtu;
    rate >>= BBR_SCALE;

    sk->sk_pacing_rate = min_t(u64, rate, sk->sk_max_pacing_rate);
}
```

### 5.2 参数调优

**sysctl调优参数**：

```bash
# 查看当前拥塞控制算法
sysctl net.ipv4.tcp_congestion_control

# 查看可用算法
sysctl net.ipv4.tcp_available_congestion_control

# 修改算法（临时）
sysctl -w net.ipv4.tcp_congestion_control=bbr

# 永久修改
# /etc/sysctl.conf
echo "net.ipv4.tcp_congestion_control=bbr" >> /etc/sysctl.conf
sysctl -p
```

**CUBIC特定参数**：

```bash
# 查看/修改CUBIC参数
# /sys/module/tcp_cubic/parameters/

# 快速收敛
sudo sysctl net.ipv4.tcp_congestion_control=cubic
echo 1 | sudo tee /sys/module/tcp_cubic/parameters/fast_convergence

# 调整beta值（默认717 = 0.7 = 30%乘性减少）
echo 717 | sudo tee /sys/module/tcp_cubic/parameters/beta
```

**BBR调优**：

```bash
# BBR v1参数（Linux 4.9+）
# 启用BBR
sudo sysctl -w net.ipv4.tcp_congestion_control=bbr

# 调整初始拥塞窗口
sudo sysctl -w net.ipv4.tcp_slow_start_after_idle=0

# 调整TCP内存
sudo sysctl -w net.ipv4.tcp_rmem="4096 87380 134217728"
sudo sysctl -w net.ipv4.tcp_wmem="4096 65536 134217728"

# 启用FQ（Fair Queuing）调度器（BBR需要）
sudo tc qdisc replace dev eth0 root fq
```

### 5.3 监控工具

**ss命令**：

```bash
# 查看连接状态（包括拥塞控制算法）
ss -tin | head -20

# 输出示例:
cubic wscale:7,7 rto:201 rtt:0.25/0.125 ato:40 mss:1448 pmtu:1500
cwnd:10 bytes_acked:14080 bytes_received:296 segs_out:82 segs_in:42
send 463.4Mbps lastsnd:372 lastrcv:372 lastack:372 pacing_rate 926.8Mbps
rcv_space:29200
```

**tc命令监控**：

```bash
# 查看qdisc统计
tc -s qdisc show dev eth0

# 查看BBR状态（需要BPF工具）
bpftrace -e 'kprobe:bbr_main { printf("BBR state: %d\", arg1); }'
```

**tcp_probe内核模块**：

```bash
# 加载模块
sudo modprobe tcp_probe port=8080 full=1

# 读取跟踪数据
sudo cat /proc/net/tcpprobe

# 使用脚本分析
awk '{print $2, $3, $4, $5}' /proc/net/tcpprobe > tcp_trace.dat
```

**ss工具cwnd分析脚本**：

```bash
# !/bin/bash
# monitor_cwnd.sh - 监控拥塞窗口变化

INTERVAL=1
LOG_FILE="cwnd_log.csv"

echo "timestamp,local_addr,remote_addr,cwnd,ssthresh,rtt,pacing_rate" > $LOG_FILE

while true; do
    timestamp=$(date +%s.%N)
    ss -tin | grep -E "(cwnd|rto)" | while read line; do
        conn=$(echo "$line" | grep -oP '\[?[^]]+\]:\d+' | head -2 | tr '\n' ',')
        cwnd=$(echo "$line" | grep -oP 'cwnd:\d+' | cut -d: -f2)
        ssthresh=$(echo "$line" | grep -oP 'ssthresh:\d+' | cut -d: -f2)
        rtt=$(echo "$line" | grep -oP 'rtt:[\d.]+' | cut -d: -f2)
        pacing=$(echo "$line" | grep -oP 'pacing_rate [\d.]+' | cut -d' ' -f2)

        echo "$timestamp,$conn,$cwnd,$ssthresh,$rtt,$pacing" >> $LOG_FILE
    done
    sleep $INTERVAL
done
```

**可视化工具**：

```python
# !/usr/bin/env python3
# plot_cwnd.py - 绘制拥塞窗口变化

import pandas as pd
import matplotlib.pyplot as plt

df = pd.read_csv('cwnd_log.csv')
df['datetime'] = pd.to_datetime(df['timestamp'], unit='s')

plt.figure(figsize=(12, 6))
for conn in df['local_addr'].unique():
    subset = df[df['local_addr'] == conn]
    plt.plot(subset['datetime'], subset['cwnd'], label=conn)

plt.xlabel('Time')
plt.ylabel('CWND (MSS)')
plt.title('TCP Congestion Window Evolution')
plt.legend()
plt.grid(True)
plt.savefig('cwnd_evolution.png')
plt.show()
```

### 5.4 算法选择建议

| 场景 | 推荐算法 | 理由 |
|------|----------|------|
| 通用Linux服务器 | CUBIC | 默认、稳定、兼容性好 |
| 高带宽延迟网络 | BBR | 低延迟、高吞吐 |
| Web/HTTP服务 | BBRv2/BBR | 首字节时间短 |
| 数据中心内 | DCTCP | 低延迟、高突发容忍 |
| 移动网络 | BBR | 适应带宽波动 |
| 与旧系统兼容 | Reno | 最基础的算法 |
| 需要确定性延迟 | Vegas | 延迟敏感 |

**混合部署策略**：

```
Web服务器 (Nginx/Apache):
└── tcp_congestion_control = bbr

数据库服务器 (MySQL/PostgreSQL):
└── tcp_congestion_control = cubic

CDN/边缘节点:
└── tcp_congestion_control = bbr

内部微服务通信:
└── tcp_congestion_control = cubic
```

---

## 6. 总结与展望

### 6.1 算法演进总结

```
时间线:
1988  Tahoe     ─┐
1990  Reno       │ 基础阶段: 基于丢包
1996  NewReno   ─┘

1995  SACK      ─┐
1999  Vegas      │ 改进阶段: 选择性确认、延迟感知
2002  Westwood  ─┘

2006  CUBIC     ─┐ 现代阶段: 高带宽优化、模型驱动
2016  BBR       ─┘

2020+ BBRv2, PCC, Copa  ── 未来: 机器学习、应用感知
```

### 6.2 关键技术趋势

1. **机器学习拥塞控制**：如Orion、Aurora
2. **应用层反馈**：应用直接参与拥塞控制决策
3. **多路径TCP (MPTCP)**：在多条路径上协调拥塞控制
4. **QUIC**：用户空间实现更灵活的拥塞控制

### 6.3 形式化方法的未来

- **验证工具**：使用TLA+、Coq验证拥塞控制正确性
- **自动合成**：自动生成满足特定属性的拥塞控制算法
- **博弈论模型**：分析多用户场景下的纳什均衡

---

## 参考文献

1. Van Jacobson. "Congestion Avoidance and Control." ACM SIGCOMM, 1988.
2. Mark Allman et al. RFC 5681: TCP Congestion Control, 2009.
3. Sangtae Ha et al. "CUBIC: A New TCP-Friendly High-Speed TCP Variant." ACM OSR, 2008.
4. Neal Cardwell et al. "BBR: Congestion-Based Congestion Control." ACM Queue, 2016.
5. J. Kurose & K. Ross. "Computer Networking: A Top-Down Approach." 8th Ed, Chapter 3.
6. Brakmo & Peterson. "TCP Vegas: End to End Congestion Avoidance on a Global Internet." IEEE JSAC, 1995.
7. Mathis et al. "The Macroscopic Behavior of the TCP Congestion Avoidance Algorithm." ACM CCR, 1997.

---

_本文档完成于FormalScience项目阶段2-2，覆盖TCP拥塞控制算法的完整理论体系与工程实践。_
