# 网络包调度（Packet Scheduling）领域权威研究综述

## 目录

- [网络包调度（Packet Scheduling）领域权威研究综述](#网络包调度packet-scheduling领域权威研究综述)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 核心挑战](#11-核心挑战)
    - [1.2 调度算法分类](#12-调度算法分类)
  - [2. 顶级会议论文](#2-顶级会议论文)
    - [2.1 ACM SIGCOMM](#21-acm-sigcomm)
      - [2.1.1 Programmable Packet Scheduling at Line Rate (SIGCOMM 2016)](#211-programmable-packet-scheduling-at-line-rate-sigcomm-2016)
      - [2.1.2 Programmable Packet Scheduling with a Single Queue (SIGCOMM 2021)](#212-programmable-packet-scheduling-with-a-single-queue-sigcomm-2021)
      - [2.1.3 BMW Tree: Large-scale PIFO Implementation (SIGCOMM 2023)](#213-bmw-tree-large-scale-pifo-implementation-sigcomm-2023)
    - [2.2 USENIX NSDI](#22-usenix-nsdi)
      - [2.2.1 Gearbox: Hierarchical Packet Scheduler for Approximate WFQ (NSDI 2022)](#221-gearbox-hierarchical-packet-scheduler-for-approximate-wfq-nsdi-2022)
      - [2.2.2 Hierarchical Core-Stateless Fair Queueing (NSDI 2021)](#222-hierarchical-core-stateless-fair-queueing-nsdi-2021)
      - [2.2.3 SP-PIFO: Approximating PIFO with Strict-Priority Queues (NSDI 2020)](#223-sp-pifo-approximating-pifo-with-strict-priority-queues-nsdi-2020)
      - [2.2.4 Programmable Calendar Queues (NSDI 2020)](#224-programmable-calendar-queues-nsdi-2020)
    - [2.3 IEEE INFOCOM](#23-ieee-infocom)
      - [2.3.1 Recent INFOCOM Scheduling Papers](#231-recent-infocom-scheduling-papers)
  - [3. RFC标准](#3-rfc标准)
    - [3.1 RFC 8289: Controlled Delay Active Queue Management (CoDel)](#31-rfc-8289-controlled-delay-active-queue-management-codel)
      - [3.1.1 核心思想](#311-核心思想)
      - [3.1.2 算法描述](#312-算法描述)
      - [3.1.3 复杂度分析](#313-复杂度分析)
    - [3.2 RFC 8290: The Flow Queue CoDel Packet Scheduler (FQ-CoDel)](#32-rfc-8290-the-flow-queue-codel-packet-scheduler-fq-codel)
      - [3.2.1 架构](#321-架构)
      - [3.2.2 流分类](#322-流分类)
      - [3.2.3 DRR调度器](#323-drr调度器)
      - [3.2.4 内存开销](#324-内存开销)
    - [3.3 RFC 8033: Proportional Integral Controller Enhanced (PIE)](#33-rfc-8033-proportional-integral-controller-enhanced-pie)
      - [3.3.1 核心思想](#331-核心思想)
      - [3.3.2 算法描述](#332-算法描述)
      - [3.3.3 FQ-PIE](#333-fq-pie)
  - [4. 经典调度算法](#4-经典调度算法)
    - [4.1 Weighted Fair Queuing (WFQ)](#41-weighted-fair-queuing-wfq)
      - [4.1.1 理论模型](#411-理论模型)
      - [4.1.2 复杂度分析](#412-复杂度分析)
      - [4.1.3 延迟边界](#413-延迟边界)
    - [4.2 WF2Q+ (Worst-case Fair Weighted Fair Queuing Plus)](#42-wf2q-worst-case-fair-weighted-fair-queuing-plus)
      - [4.2.1 算法改进](#421-算法改进)
      - [4.2.2 简化实现](#422-简化实现)
      - [4.2.3 理论保证](#423-理论保证)
      - [4.2.4 复杂度](#424-复杂度)
    - [4.3 DRR (Deficit Round Robin)](#43-drr-deficit-round-robin)
      - [4.3.1 算法描述](#431-算法描述)
      - [4.3.2 复杂度分析](#432-复杂度分析)
      - [4.3.3 公平性分析](#433-公平性分析)
    - [4.4 SCFQ (Self-Clocked Fair Queuing)](#44-scfq-self-clocked-fair-queuing)
      - [4.4.1 核心思想](#441-核心思想)
      - [4.4.2 复杂度](#442-复杂度)
      - [4.4.3 性质](#443-性质)
    - [4.5 SFQ (Stochastic Fairness Queuing)](#45-sfq-stochastic-fairness-queuing)
      - [4.5.1 算法描述](#451-算法描述)
      - [4.5.2 复杂度](#452-复杂度)
      - [4.5.3 特性](#453-特性)
    - [4.6 SRPT (Shortest Remaining Processing Time)](#46-srpt-shortest-remaining-processing-time)
      - [4.6.1 核心思想](#461-核心思想)
      - [4.6.2 理论分析](#462-理论分析)
      - [4.6.3 近似实现 (ADS)](#463-近似实现-ads)
  - [5. 实现与工业实践](#5-实现与工业实践)
    - [5.1 Linux内核 net/sched 实现](#51-linux内核-netsched-实现)
      - [5.1.1 Qdisc架构](#511-qdisc架构)
      - [5.1.2 主要Qdisc实现](#512-主要qdisc实现)
      - [5.1.3 配置示例](#513-配置示例)
    - [5.2 DPDK QoS调度器](#52-dpdk-qos调度器)
      - [5.2.1 层次结构](#521-层次结构)
      - [5.2.2 核心API](#522-核心api)
      - [5.2.3 应用场景](#523-应用场景)
    - [5.3 CAKE (Common Applications Kept Enhanced)](#53-cake-common-applications-kept-enhanced)
      - [5.3.1 设计理念](#531-设计理念)
      - [5.3.2 核心组件](#532-核心组件)
      - [5.3.3 配置示例](#533-配置示例)
      - [5.3.4 部署案例](#534-部署案例)
  - [6. 形式化理论](#6-形式化理论)
    - [6.1 Max-Min Fairness (最大-最小公平性)](#61-max-min-fairness-最大-最小公平性)
      - [6.1.1 定义](#611-定义)
      - [6.1.2 形式化](#612-形式化)
      - [6.1.3 算法实现](#613-算法实现)
    - [6.2 Proportional Fairness (比例公平性)](#62-proportional-fairness-比例公平性)
      - [6.2.1 定义](#621-定义)
      - [6.2.2 数学性质](#622-数学性质)
      - [6.2.3 加权比例公平](#623-加权比例公平)
    - [6.3 网络演算 (Network Calculus)](#63-网络演算-network-calculus)
      - [6.3.1 基本概念](#631-基本概念)
      - [6.3.2 延迟边界定理](#632-延迟边界定理)
      - [6.3.3 积压边界定理](#633-积压边界定理)
      - [6.3.4 级联定理](#634-级联定理)
      - [6.3.5 端到端延迟边界](#635-端到端延迟边界)
      - [6.3.6 与公平性结合](#636-与公平性结合)
  - [7. 性能对比总结](#7-性能对比总结)
    - [7.1 算法复杂度对比](#71-算法复杂度对比)
    - [7.2 延迟保证对比](#72-延迟保证对比)
    - [7.3 公平性对比](#73-公平性对比)
    - [7.4 实际部署对比](#74-实际部署对比)
  - [8. 参考文献](#8-参考文献)
    - [顶级会议论文](#顶级会议论文)
    - [经典算法论文](#经典算法论文)
    - [RFC标准](#rfc标准)
    - [工业实现](#工业实现)
    - [形式化理论](#形式化理论)
  - [附录：符号对照表](#附录符号对照表)

---

## 1. 概述

网络包调度是计算机网络中的核心机制，负责决定数据包在路由器、交换机或其他网络设备中的传输顺序。优秀的调度算法需要同时满足公平性、低延迟、高吞吐量和可扩展性等多个目标。

### 1.1 核心挑战

- **公平性（Fairness）**：确保各个流或用户获得合理的带宽分配
- **延迟保证（Delay Guarantees）**：为实时流量提供确定性延迟边界
- **可扩展性（Scalability）**：支持大量并发流的高速线速处理
- **灵活性（Flexibility）**：支持可编程调度以适应不同应用场景

### 1.2 调度算法分类

| 分类维度 | 类别 | 代表算法 |
|---------|------|---------|
| 公平性模型 | GPS-based | WFQ, WF2Q+, SCFQ, SFQ |
| | Round-robin based | DRR, WRR |
| | Size-based | SRPT, SJF, LAS |
| 实现复杂度 | O(1) | DRR, SFQ |
| | O(log N) | WFQ, WF2Q+, SCFQ |
| 可编程性 | 可编程调度 | PIFO, SP-PIFO, AIFO, RIFO |

---

## 2. 顶级会议论文

### 2.1 ACM SIGCOMM

#### 2.1.1 Programmable Packet Scheduling at Line Rate (SIGCOMM 2016)

**作者**: Anirudh Sivaraman, Suvinay Subramanian, Mohammad Alizadeh, et al.
**机构**: MIT CSAIL, Barefoot Networks
**核心贡献**: 提出PIFO（Push-In First-Out）抽象模型

**PIFO核心概念**:

- PIFO是一种优先级队列，允许根据元素的rank将元素插入任意位置，但只能从头部出队
- 支持两种事务类型：
  - **调度事务（Scheduling Transaction）**：计算数据包的调度顺序
  - **整形事务（Shaping Transaction）**：确定数据包的发送时间

**PIFO可编程的算法示例**:

```
// 加权公平队列（WFQ）的PIFO实现
p.rank = p.virtual_finish_time

// 最短剩余处理时间（SRPT）
p.rank = p.remaining_flow_size

// 最早截止时间优先（EDF）
p.rank = p.deadline

// 停止-等待队列（Stop-and-Go）
if (now >= frame_end_time):
    frame_begin_time = frame_end_time
    frame_end_time = frame_begin_time + T
p.rank = frame_end_time
```

**理论复杂度**: O(log N)
**硬件实现**: 支持线速（line-rate）处理

---

#### 2.1.2 Programmable Packet Scheduling with a Single Queue (SIGCOMM 2021)

**作者**: Zhuolong Yu, Chuheng Hu, Jingfeng Wu, et al.
**机构**: Johns Hopkins University, UC Berkeley
**核心贡献**: 提出AIFO（Approximate Inverted FIFO Overflow）算法

**关键创新**:

- 使用单个FIFO队列实现近似PIFO调度
- 基于队列长度自适应调整准入阈值

**AIFO准入控制**:

```
n(c) = (1/(1-k)) * ((C-c)/C) * n
```

其中：

- `n(c)`：可准入的数据包优先级阈值
- `C`：队列容量
- `c`：当前队列占用
- `k`：配置参数

**复杂度**: O(1)
**资源消耗**: 极低的硬件资源需求

---

#### 2.1.3 BMW Tree: Large-scale PIFO Implementation (SIGCOMM 2023)

**作者**: Jingling Liu, et al.
**核心贡献**: 使用平衡多路排序树实现大规模PIFO

**技术特点**:

- 支持百万级PIFO容量
- 线速处理能力
- FPGA友好实现

---

### 2.2 USENIX NSDI

#### 2.2.1 Gearbox: Hierarchical Packet Scheduler for Approximate WFQ (NSDI 2022)

**作者**: Peixuan Gao, Anthony Dalleggio, Yang Xu, H. Jonathan Chao
**机构**: New York University, Fudan University

**核心贡献**:

- 提出分层调度架构近似实现WFQ
- 使用Calendar Queue结构管理多个FIFO队列

**Gearbox架构**:

```
Level 0: [T, 2T)     - 最低精度时间槽
Level 1: [2T, 4T)    - 中等精度时间槽
Level 2: [4T, 8T)    - 高精度时间槽
...
```

**关键公式**:

- **归一化延迟差异界**（Normalized Discrepancy Bound）: 有界且可控
- 每个分层级别维护独立的FIFO队列

**复杂度分析**:

- 入队操作: O(1)
- 出队操作: O(1)
- 空间复杂度: O(log(ΔT))，其中ΔT为最大延迟范围

**性能评估**:

- FPGA原型：350MHz运行频率
- 支持100GbE线速（数据包≥123字节）
- 逻辑资源消耗 < 1%
- 块内存消耗 < 4%

---

#### 2.2.2 Hierarchical Core-Stateless Fair Queueing (NSDI 2021)

**作者**: Zhuolong Yu, Jingfeng Wu, Vladimir Braverman, Ion Stoica, Xin Jin
**核心贡献**: 将CSFQ扩展到分层场景

**HCSFQ特点**:

- 使用单个FIFO队列
- 无需逐包调度
- 仅需维护层次结构内部节点状态

**理论保证**:

- 公平带宽分配
- 流隔离性
- 可证明的下界

---

#### 2.2.3 SP-PIFO: Approximating PIFO with Strict-Priority Queues (NSDI 2020)

**作者**: Albert Gran Alcoz, Alexander Dietmüller, Laurent Vanbever
**机构**: ETH Zurich

**核心思想**:

- 使用严格优先级队列近似PIFO行为
- 入队时根据rank映射到适当的优先级队列

---

#### 2.2.4 Programmable Calendar Queues (NSDI 2020)

**作者**: Naveen Kr Sharma, et al.
**核心贡献**: 可编程日历队列抽象

---

### 2.3 IEEE INFOCOM

#### 2.3.1 Recent INFOCOM Scheduling Papers

| 年份 | 论文 | 核心贡献 |
|-----|------|---------|
| 2023 | Exp-PIFO | 可扩展高效的PIFO实现 |
| 2022 | Programmable Packet Scheduling with SP-PIFO (Workshop) | SP-PIFO理论分析 |
| 2021 | PIPO: Efficient Programmable Scheduling for TSN | 时间敏感网络调度 |

---

## 3. RFC标准

### 3.1 RFC 8289: Controlled Delay Active Queue Management (CoDel)

**发布时间**: January 2018
**作者**: Kathleen Nichols, Van Jacobson
**状态**: Experimental

#### 3.1.1 核心思想

CoDel旨在解决bufferbloat问题，通过控制队列延迟而非队列长度来管理拥塞。

#### 3.1.2 算法描述

```
Variables:
- target: 目标队列延迟 (默认 5ms)
- interval: 控制间隔 (默认 100ms)
- count: 连续丢包计数
- dropping: 是否处于丢包状态

On Enqueue(packet):
    if (dropping == true && now >= drop_next):
        drop packet
        count += 1
        drop_next = control_law(count)
        return
    enqueue packet

On Dequeue(packet):
    sojourn_time = now - packet.enqueue_time
    if (sojourn_time < target || queue_bytes < MTU):
        if (dropping == true):
            dropping = false
        return packet
    if (dropping == false):
        dropping = true
        count = 1
        drop_next = now + interval
        drop packet
        return

Control Law(count):
    return now + interval / sqrt(count)
```

#### 3.1.3 复杂度分析

- **时间复杂度**: O(1) 每包处理
- **空间复杂度**: O(1) 每队列状态

---

### 3.2 RFC 8290: The Flow Queue CoDel Packet Scheduler (FQ-CoDel)

**发布时间**: January 2018
**作者**: Toke Høiland-Jørgensen, et al.
**状态**: Experimental

#### 3.2.1 架构

FQ-CoDel结合了两个组件：

1. **调度器（Scheduler）**：基于DRR（Deficit Round Robin）选择出队队列
2. **CoDel AQM**：对每个队列独立运行CoDel算法

#### 3.2.2 流分类

```
// 默认使用5-tuple哈希分类
hash = JenkinsHash(protocol, src_ip, dst_ip, src_port, dst_port)
queue_id = hash % num_queues

// 扰动哈希防止DoS攻击
hash = (hash + salt) % num_queues
```

#### 3.2.3 DRR调度器

```
// 每个队列维护的赤字计数器
struct flow {
    int deficit;        // 赤字计数器
    int quantum;        // 量子值（默认MTU）
    bool in_new_list;   // 是否在新队列列表
};

Dequeue():
    // 优先处理新队列列表
    for queue in new_queues:
        if (queue.deficit <= 0):
            queue.deficit += quantum
            move_to_old_queues(queue)
            continue
        packet = codel_dequeue(queue)
        if (packet):
            queue.deficit -= packet.length
            return packet
        else:
            move_to_old_queues(queue)

    // 处理旧队列列表
    for queue in old_queues:
        // 类似处理...
```

#### 3.2.4 内存开销

Linux实现中每个队列约需 **< 64 bytes**（64位系统）。

核心数据结构：

```c
struct codel_vars {
    u32 count;              // 丢包计数
    u32 lastcount;          // 进入丢包状态的计数
    bool dropping;          // 是否正在丢包
    u16 rec_inv_sqrt;       // 倒数平方根计算
    codel_time_t first_above_time;  // 延迟超过目标时间
    codel_time_t drop_next;         // 下次丢包时间
};
```

---

### 3.3 RFC 8033: Proportional Integral Controller Enhanced (PIE)

**发布时间**: February 2017
**作者**: Rong Pan, et al.
**状态**: Experimental

#### 3.3.1 核心思想

PIE使用比例-积分控制器主动控制队列延迟在目标值附近。

#### 3.3.2 算法描述

```
Parameters:
- QDELAY_REF: 目标延迟 (默认 15ms)
- T_UPDATE: 更新周期 (默认 15ms)
- ALPHA: 比例增益 (默认 0.125)
- BETA: 积分增益 (默认 1.25)

Variables:
- drop_prob: 当前丢包概率
- qdelay_old: 上一周期队列延迟

Every T_UPDATE:
    // 计算当前队列延迟（基于Little's Law或时间戳）
    qdelay = estimate_delay()

    // 计算延迟变化趋势
    delta = qdelay - qdelay_old

    // PI控制器
    p = ALPHA * (qdelay - QDELAY_REF) + BETA * delta

    // 更新丢包概率
    drop_prob += p
    drop_prob = clamp(drop_prob, 0, 1)

    qdelay_old = qdelay

On Enqueue(packet):
    if (random() < drop_prob):
        drop packet (or ECN mark)
    else:
        enqueue packet
```

#### 3.3.3 FQ-PIE

将PIE与流队列结合的混合算法，已在Linux 5.6中实现。

---

## 4. 经典调度算法

### 4.1 Weighted Fair Queuing (WFQ)

#### 4.1.1 理论模型

WFQ是GPS（Generalized Processor Sharing）的分组近似实现。

**GPS流体模型**:

```
对于N个流，每个流i的权重为φ_i
在时刻t，流i的服务速率为:
    r_i(t) = (φ_i / Σφ_j) * C
其中C为链路容量
```

**WFQ分组实现**:

```
// 虚拟时间函数
V(t) = 服务包的数量（按字节计）

// 包的虚拟开始时间
S_i^k = max(F_i^{k-1}, V(a_i^k))

// 包的虚拟完成时间
F_i^k = S_i^k + L_i^k / φ_i

// 调度策略: 选择具有最小F_i^k的包
```

#### 4.1.2 复杂度分析

- **时间复杂度**: O(N) 更新虚拟时间 + O(log N) 优先级队列
- **空间复杂度**: O(N) 每流状态

#### 4.1.3 延迟边界

对于漏桶约束(σ_i, ρ_i)的流：

```
Delay_bound = σ_i / r_i + (N-1) * L_max / C
```

---

### 4.2 WF2Q+ (Worst-case Fair Weighted Fair Queuing Plus)

#### 4.2.1 算法改进

WF2Q+是WF2Q的低复杂度实现，同时保持最优的延迟和公平性保证。

**虚拟时间函数**:

```
V(t+τ) = max(V(t) + W(t, t+τ), min_{i∈B(t+τ)}(S_i))
```

其中：

- `W(t, t+τ)`: 服务器在[t, t+τ]期间提供的总服务量
- `B(t)`: 在t时刻积压的会话集合
- `S_i`: 会话i头包的虚拟开始时间

#### 4.2.2 简化实现

```
// 每会话只需维护一对(F_i, S_i)
当包p_i^k到达队列头部时:
    if (Q_i(a_i^-) ≠ 0):      // 队列非空
        S_i = F_i
    else:                     // 队列为空
        S_i = max(F_i, V(a_i^k))
    F_i = S_i + L_i^k / r_i
```

#### 4.2.3 理论保证

**定理 4.1**: WF2Q+具有以下性质：

1. **工作保持性（Work-conserving）**
2. **最坏情况公平性**:

   ```
   α_{i,WF2Q+} = L_{i,max} + (L_{max} - L_{i,max}) * r_i / r
   ```

3. **延迟边界**:

   ```
   D_i ≤ σ_i / r_i + L_{max} / r
   ```

#### 4.2.4 复杂度

- **时间复杂度**: O(log N)
- **空间复杂度**: O(N)

---

### 4.3 DRR (Deficit Round Robin)

#### 4.3.1 算法描述

```
Data Structures:
- ActiveList: 活动队列列表
- DeficitCounter[i]: 队列i的赤字计数器
- Quantum[i]: 队列i的量子值

Initialization:
    for i = 0 to N-1:
        DeficitCounter[i] = 0

Enqueue(packet p, queue i):
    if (i not in ActiveList):
        append i to ActiveList
        DeficitCounter[i] = 0
    enqueue p to queue i

Dequeue():
    while (ActiveList not empty):
        i = remove_head(ActiveList)
        DeficitCounter[i] += Quantum[i]

        while (queue i not empty AND DeficitCounter[i] > 0):
            packet = head(queue i)
            if (packet.length <= DeficitCounter[i]):
                send(packet)
                DeficitCounter[i] -= packet.length
                dequeue(queue i)
            else:
                break

        if (queue i not empty):
            append i to ActiveList
        else:
            DeficitCounter[i] = 0
```

#### 4.3.2 复杂度分析

- **时间复杂度**: O(1) 每包平均
- **空间复杂度**: O(N)

#### 4.3.3 公平性分析

**公平性界**:

```
对于任意两个积压流i和j，在时间间隔[t1, t2]内:
|W_i(t1, t2)/φ_i - W_j(t1, t2)/φ_j| ≤ Max / φ_i + Max / φ_j

其中Max = max(Quantum, L_max)
```

**延迟边界**: 取决于Quantum值和包大小分布

---

### 4.4 SCFQ (Self-Clocked Fair Queuing)

#### 4.4.1 核心思想

SCFQ使用虚拟时间函数简化实现，基于当前服务包的标签计算虚拟时间。

```
// 系统虚拟时间 = 当前服务包的完成标签
V(t) = F_i^k, 其中包p_i^k在时间t正在服务

// 新到达包的标签
F_i^k = max(F_i^{k-1}, V(a_i^k)) + L_i^k / φ_i

// 调度: 选择最小标签的包
```

#### 4.4.2 复杂度

- **时间复杂度**: O(log N)
- **空间复杂度**: O(N)

#### 4.4.3 性质

- 实现简单，但延迟边界依赖于系统中流的数量
- 短期公平性好

---

### 4.5 SFQ (Stochastic Fairness Queuing)

#### 4.5.1 算法描述

```
Parameters:
- N: 队列数量（通常远大于期望的并发流数）
- Salt: 随机盐值（定期更换）

Enqueue(packet p):
    // 哈希分类
    queue_id = hash(flow_id(p), salt) % N

    if (queue[queue_id] not in ActiveList):
        add_to_active_list(queue[queue_id])

    if (buffer_full):
        drop_from_longest_queue()

    enqueue(queue[queue_id], p)

Dequeue():
    // 轮询调度
    queue = round_robin_select()
    if (queue not empty):
        return dequeue(queue)
    else:
        remove_from_active_list(queue)
```

#### 4.5.2 复杂度

- **时间复杂度**: O(1)（使用桶排序）
- **空间复杂度**: O(N)

#### 4.5.3 特性

- 概率公平性：流哈希冲突时共享带宽
- 哈希变化周期：数秒（避免长期不公平）
- 适用于流数量远大于队列数量的情况

---

### 4.6 SRPT (Shortest Remaining Processing Time)

#### 4.6.1 核心思想

SRPT优先调度剩余处理时间最短的任务，在M/G/1队列中最小化平均响应时间。

```
Scheduling Policy:
当服务器空闲或完成当前包时:
    选择剩余流大小最小的包发送

// 对于流i的第k个包:
priority_i^k = remaining_bytes_of_flow_i
```

#### 4.6.2 理论分析

**最优性定理**: 在M/G/1队列中，SRPT最小化平均响应时间（平均逗留时间）。

**平均响应时间**:

```
E[T_SRPT] ≤ E[T_FIFO] * log(1/(1-ρ))
```

其中ρ为系统利用率。

**公平性分析**:

- 短流获得显著优于FIFO的性能
- 大流的性能损失很小（反直觉）
- 在重尾分布下表现优异

#### 4.6.3 近似实现 (ADS)

由于需要知道流大小信息，提出Approximate and Deployable SRPT (ADS):

```
// 使用K个FIFO队列近似SRPT
// 基于原始流大小（而非剩余大小）分类

for k = 1 to K:
    threshold[k] = 某个阈值

Enqueue(packet p):
    size = get_flow_size(p)
    for k = 1 to K:
        if (size <= threshold[k]):
            enqueue(queue[k], p)
            break

Dequeue():
    for k = 1 to K:
        if (queue[k] not empty):
            return dequeue(queue[k])
```

**性能**: 实验表明，8个FIFO队列的ADS可接近真实SRPT性能。

---

## 5. 实现与工业实践

### 5.1 Linux内核 net/sched 实现

#### 5.1.1 Qdisc架构

```c
// Linux内核Qdisc结构
struct Qdisc {
    int (*enqueue)(struct sk_buff *skb,
                   struct Qdisc *sch,
                   struct sk_buff **to_free);
    struct sk_buff *(*dequeue)(struct Qdisc *sch);

    u32 limit;
    const struct Qdisc_ops *ops;

    // 统计数据
    struct gnet_stats_basic_sync bstats;
    struct gnet_stats_queue qstats;

    // 私有数据
    long privdata[] ____cacheline_aligned;
};
```

#### 5.1.2 主要Qdisc实现

| Qdisc | 类型 | 功能 | 源码文件 |
|-------|------|------|---------|
| pfifo_fast | Classless | 默认FIFO调度 | sch_fifo.c |
| TBF | Classless | 令牌桶流量整形 | sch_tbf.c |
| CoDel | Classless | 延迟控制AQM | sch_codel.c |
| FQ-CoDel | Classless | 流队列+CoDel | sch_fq_codel.c |
| FQ-PIE | Classless | 流队列+PIE | sch_fq_pie.c |
| CAKE | Classless | 综合调度器 | sch_cake.c |
| DRR | Classful | 赤字轮询 | sch_drr.c |
| HTB | Classful | 层次令牌桶 | sch_htb.c |
| HFSC | Classful | 层次公平服务曲线 | sch_hfsc.c |
| QFQ | Classful | 快速公平队列 | sch_qfq.c |

#### 5.1.3 配置示例

```bash
# FQ-CoDel配置
tc qdisc add dev eth0 root fq_codel \
    limit 10240 \
    flows 1024 \
    quantum 1514 \
    target 5ms \
    interval 100ms

# CAKE配置
tc qdisc add dev eth0 root cake \
    bandwidth 100mbit \
    rtt 100ms \
    ack-filter-aggressive
```

---

### 5.2 DPDK QoS调度器

#### 5.2.1 层次结构

DPDK rte_sched实现5层层次调度：

```
Level 1: Port (输出以太网端口)
Level 2: Subport (用户组，令牌桶整形)
Level 3: Pipe (单个用户，令牌桶整形)
Level 4: Traffic Class (严格优先级)
Level 5: Queue (WRR轮询)
```

#### 5.2.2 核心API

```c
// 端口配置
struct rte_sched_port_params {
    uint32_t n_subports;        // 子端口数量
    uint32_t n_pipes_per_subport; // 每子端口管道数
    uint32_t n_queues_per_pipe;   // 每管道队列数
    uint16_t qsize[RTE_SCHED_QUEUES_PER_PIPE]; // 队列大小
    uint64_t rate;              // 端口速率
    uint32_t mtu;               // MTU
};

// 拥塞管理模式
enum rte_sched_cman_mode {
    RTE_SCHED_CMAN_RED,    // 随机早期检测
    RTE_SCHED_CMAN_PIE     // PIE AQM
};

// 核心操作
int rte_sched_port_enqueue(struct rte_sched_port *port,
                           struct rte_mbuf **pkts,
                           uint32_t n_pkts);

int rte_sched_port_dequeue(struct rte_sched_port *port,
                           struct rte_mbuf **pkts,
                           uint32_t n_pkts);
```

#### 5.2.3 应用场景

- 移动基站回传
- 数据中心网络虚拟化
- 企业级QoS策略

---

### 5.3 CAKE (Common Applications Kept Enhanced)

#### 5.3.1 设计理念

CAKE是整合多种功能的综合队列管理器，目标是简化配置并优化家庭网络体验。

#### 5.3.2 核心组件

```
1. 带宽整形器（Shaper）
   - 基于速率的整形
   - 支持DSL/ATM/PPPoE开销补偿

2. 优先级队列（Priority Queue）
   - 基于DiffServ优先级
   - 带宽上限保护（如最高优先级限制25%）

3. 流隔离（Flow Isolation）
   - DRR++变体
   - 主机间公平性

4. AQM（Cobalt）
   - CoDel + BLUE混合算法
   - 改进的延迟控制

5. 报文管理
   - ACK过滤（不对称链路优化）
   - TSO/GSO/GRO peeling
```

#### 5.3.3 配置示例

```bash
# 基础配置
tc qdisc add dev eth0 root cake \
    bandwidth 50mbit

# 高级配置
tc qdisc add dev eth0 root cake \
    bandwidth 100mbit \
    rtt 100ms \
    diffserv4 \
    ack-filter-aggressive \
    split-gso \
    wash
```

#### 5.3.4 部署案例

| 平台 | 支持版本 | 配置方式 |
|------|---------|---------|
| OpenWrt | 全版本 | SQM Scripts |
| MikroTik RouterOS | v7.1+ | /queue type |
| DD-WRT | r40529+ | QoS设置 |
| 主线Linux | 4.19+ | tc命令 |

---

## 6. 形式化理论

### 6.1 Max-Min Fairness (最大-最小公平性)

#### 6.1.1 定义

**定义**: 分配x是max-min公平的，如果对于任何其他可行分配y，对于每个满足y_i > x_i的流i，存在流j使得：

1. x_j ≤ x_i（j的分配不大于i）
2. y_j < x_j（j在y中获得更少）

#### 6.1.2 形式化

```
Max-Min Fairness定义:

令C为链路容量，N为流数，r_i为流i的需求

分配{x_i}是max-min公平的当且仅当:
∀i: x_i = min(r_i, f_i)

其中f_i是流i的公平份额，满足:
- 如果Σr_i ≤ C: f_i = r_i（满足所有需求）
- 如果Σr_i > C: 最小化max_i (f_i - r_i)^+ 的解

等价地:
1. 升序排列x: x_(1) ≤ x_(2) ≤ ... ≤ x_(N)
2. 对于任何其他可行分配y，设y_(i)同样排序
3. 存在k使得x_(k) > y_(k)且对所有i < k, x_(i) = y_(i)
```

#### 6.1.3 算法实现

```
// 水填充算法（Water Filling）
算法 MaxMinFair(C, demands):
    remaining = C
    flows = all flows
    allocation = {0 for each flow}

    while flows not empty:
        fair_share = remaining / |flows|
        bottleneck = min_{i in flows} (demands[i])

        if fair_share >= bottleneck:
            allocation[i] = bottleneck for all i in flows
            remaining -= Σ bottleneck
            remove from flows all i where demands[i] = bottleneck
        else:
            allocation[i] = fair_share for all i in flows
            break

    return allocation
```

---

### 6.2 Proportional Fairness (比例公平性)

#### 6.2.1 定义

**定义**: 分配x是比例公平的，如果对于任何其他可行分配y：

```
Σ_i (y_i - x_i) / x_i ≤ 0
```

即：按比例增加分配的总量非正。

#### 6.2.2 数学性质

```
比例公平分配是以下优化问题的解:

max Σ_i log(x_i)
s.t. Σ_i x_i ≤ C
     x_i ≥ 0

通过拉格朗日乘子法:
L = Σ_i log(x_i) - λ(Σ_i x_i - C)

求导得最优条件:
1/x_i = λ  =>  x_i = 1/λ = C/N

即：当所有流权重相等时，比例公平等价于均分带宽
```

#### 6.2.3 加权比例公平

```
max Σ_i w_i * log(x_i)
s.t. Σ_i x_i ≤ C

解为: x_i = (w_i / Σ_j w_j) * C
```

---

### 6.3 网络演算 (Network Calculus)

#### 6.3.1 基本概念

网络演算基于min-plus代数，用于推导确定性延迟边界。

**到达曲线（Arrival Curve）**:

```
定义: α(t)是流R的到达曲线，如果:
∀s ≤ t: R(t) - R(s) ≤ α(t-s)

漏桶到达曲线:
α(t) = σ + ρ*t
其中σ为突发量，ρ为平均速率
```

**服务曲线（Service Curve）**:

```
定义: β(t)是节点的服务曲线，如果:
∀t: D(t) ≥ inf_{0≤s≤t} {R(s) + β(t-s)}

速率-延迟服务曲线:
β(t) = R * (t - T)^+
其中R为服务速率，T为延迟
```

#### 6.3.2 延迟边界定理

**定理（延迟边界）**:
如果流的到达曲线为α(t)，节点的服务曲线为β(t)，则延迟边界为：

```
D ≤ sup_{s≥0} {inf{τ≥0: α(s) ≤ β(s+τ)}}

对于漏桶+速率-延迟模型:
α(t) = σ + ρ*t
β(t) = R*(t-T)^+

延迟边界 = T + σ/R
（当ρ ≤ R时）
```

#### 6.3.3 积压边界定理

**定理（积压边界）**:

```
B ≤ sup_{s≥0} {α(s) - β(s)}

对于漏桶+速率-延迟模型:
积压边界 = σ + ρ*T
```

#### 6.3.4 级联定理

**定理（服务曲线级联）**:
若节点1提供服务曲线β1，节点2提供服务曲线β2，则级联提供服务曲线：

```
β = β1 ⊗ β2

其中(min-plus卷积):
(β1 ⊗ β2)(t) = inf_{0≤s≤t} {β1(s) + β2(t-s)}

对于速率-延迟模型:
β_{R1,T1} ⊗ β_{R2,T2} = β_{min(R1,R2), T1+T2}
```

#### 6.3.5 端到端延迟边界

对于H跳路径，每跳提供相同服务曲线β_{R,T}：

```
端到端服务曲线 = β_{R, H*T}

端到端延迟边界 = H*T + σ/R
```

#### 6.3.6 与公平性结合

**WF2Q+的延迟边界证明**:

```
定理: 对于WF2Q+服务器中的会话i，
若受漏桶(σ_i, ρ_i)约束且L_max = L_{i,max}，
延迟边界为:

D_i ≤ σ_i/r_i + L_max/r

其中r_i为会话i的保证速率，r为链路总速率
```

**分层WF2Q+的延迟边界**:

```
对于具有H层祖先的会话i:
D_i ≤ σ_i/r_i + Σ_{h=0}^{H-1} L_max/r_{h(i)}

其中r_{h(i)}是会话i在第h层祖先的保证速率
```

---

## 7. 性能对比总结

### 7.1 算法复杂度对比

| 算法 | 入队复杂度 | 出队复杂度 | 空间复杂度 | 每流状态 |
|-----|-----------|-----------|-----------|---------|
| FIFO | O(1) | O(1) | O(1) | 无 |
| DRR | O(1) | O(1) | O(N) | DC |
| SFQ | O(1) | O(1) | O(N) | 哈希表 |
| SCFQ | O(log N) | O(log N) | O(N) | 虚拟时间 |
| WFQ | O(N) + O(log N) | O(log N) | O(N) | 虚拟时间 |
| WF2Q+ | O(log N) | O(log N) | O(N) | (S_i, F_i) |
| PIFO | O(log N) | O(log N) | O(N) | Rank |
| SP-PIFO | O(1) | O(1) | O(K) | K个优先级队列 |
| Gearbox | O(1) | O(1) | O(log ΔT) | 日历队列 |

### 7.2 延迟保证对比

| 算法 | 延迟边界 | 依赖因素 |
|-----|---------|---------|
| GPS | σ_i/r_i | 理想模型 |
| WFQ | σ_i/r_i + (N-1)L_max/C | 流数N |
| WF2Q+ | σ_i/r_i + L_max/C | 最大包长 |
| SCFQ | σ_i/r_i + (N-1)L_max/C | 流数N |
| DRR | 取决于Quantum | Quantum, 包分布 |
| SRPT | 最优平均延迟 | 流大小分布 |

### 7.3 公平性对比

| 算法 | 长期公平性 | 短期公平性 | 最坏情况公平指数 |
|-----|-----------|-----------|----------------|
| WFQ | 好 | 中 | O(N) |
| WF2Q+ | 好 | 好 | O(1) |
| SCFQ | 好 | 好 | O(N) |
| DRR | 好 | 差 | O(Quantum) |
| SFQ | 概率性 | 概率性 | O(1) |

### 7.4 实际部署对比

| 算法 | 部署场景 | 硬件要求 | Linux支持 |
|-----|---------|---------|----------|
| FQ-CoDel | 通用，家庭路由器 | 低 | 内置 |
| CAKE | 家庭路由器，SQM | 中 | 内置(4.19+) |
| DPDK QoS | 数据中心，基站 | 高（DPDK） | 外部 |
| PIFO | 可编程交换机 | 高（P4/Tofino） | 不支持 |
| Gearbox | FPGA智能网卡 | 高（FPGA） | 不支持 |

---

## 8. 参考文献

### 顶级会议论文

1. **Sivaraman et al.** "Programmable Packet Scheduling at Line Rate", ACM SIGCOMM 2016
2. **Yu et al.** "Programmable Packet Scheduling with a Single Queue", ACM SIGCOMM 2021
3. **Liu et al.** "BMW Tree: Large-scale PIFO Implementation", ACM SIGCOMM 2023
4. **Gao et al.** "Gearbox: A Hierarchical Packet Scheduler for Approximate WFQ", USENIX NSDI 2022
5. **Yu et al.** "Twenty Years After: Hierarchical Core-Stateless Fair Queueing", USENIX NSDI 2021
6. **Alcoz et al.** "SP-PIFO: Approximating PIFO with Strict-Priority Queues", USENIX NSDI 2020
7. **Sharma et al.** "Programmable Calendar Queues for High-speed Packet Scheduling", USENIX NSDI 2020
8. **Mostafaei et al.** "RIFO: Pushing the Efficiency of Programmable Packet Schedulers", IEEE Trans. Networking 2025
9. **Alcoz et al.** "Everything Matters in Programmable Packet Scheduling", USENIX NSDI 2025

### 经典算法论文

1. **Demers et al.** "Analysis and Simulation of a Fair Queuing Algorithm", ACM SIGCOMM 1989
2. **Parekh & Gallager** "A Generalized Processor Sharing Approach to Flow Control", IEEE/ACM Trans. Networking 1993
3. **Bennett & Zhang** "Hierarchical Packet Fair Queueing Algorithms", IEEE/ACM Trans. Networking 1997
4. **Golestani** "A Self-Clocked Fair Queueing Scheme for Broadband Applications", IEEE INFOCOM 1994
5. **McKenney** "Stochastic Fairness Queuing", IEEE INFOCOM 1990
6. **Shreedhar & Varghese** "Efficient Fair Queuing using Deficit Round Robin", IEEE/ACM Trans. Networking 1996
7. **Goyal et al.** "Start-time Fair Queuing", ACM SIGCOMM 1996
8. **Bansal & Harchol-Balter** "Analysis of SRPT Scheduling", SIGMETRICS 2001

### RFC标准

1. **RFC 8289** "Controlled Delay Active Queue Management", January 2018
2. **RFC 8290** "The Flow Queue CoDel Packet Scheduler and Active Queue Management Algorithm", January 2018
3. **RFC 8033** "Proportional Integral Controller Enhanced (PIE)", February 2017
4. **RFC 3247** "Supplemental Information for the New Definition of the EF PHB", March 2002

### 工业实现

1. **Høiland-Jørgensen et al.** "CAKE - Common Applications Kept Enhanced", IEEE LANMAN 2018
2. **DPDK Documentation** "RTE Hierarchical Scheduler (rte_sched)"
3. **Linux Kernel Documentation** "Traffic Control (tc) and Qdisc"

### 形式化理论

1. **Cruz** "A Calculus for Network Delay", IEEE Trans. Information Theory 1991
2. **Le Boudec & Thiran** "Network Calculus: A Theory of Deterministic Queuing Systems for the Internet", Springer 2001
3. **Jiang & Liebeherr** "On the Convexity of Generalized Feedback Shift Register (GFSR) Sequences", 2020

---

## 附录：符号对照表

| 符号 | 含义 |
|-----|------|
| N | 流/队列数量 |
| C | 链路容量 |
| r_i | 流i的保证速率 |
| φ_i | 流i的权重 |
| σ_i | 流i的漏桶突发量 |
| ρ_i | 流i的漏桶平均速率 |
| L_i | 流i的包长度 |
| L_max | 最大包长度 |
| V(t) | 虚拟时间函数 |
| S_i^k | 包p_i^k的虚拟开始时间 |
| F_i^k | 包p_i^k的虚拟完成时间 |
| WFI | 最坏情况公平指数 |
| PIFO | Push-In First-Out队列 |
| AQM | 主动队列管理 |
| ECN | 显式拥塞通知 |

---

_报告生成时间: 2026年4月10日_
_最后更新: 2026年4月10日_
