# 存储调度（Storage Scheduling）领域权威国际化内容研究报告

> 报告生成日期：2026年4月10日
> 研究领域：操作系统存储子系统、IO调度、QoS保证、分布式存储

---

## 目录

- [存储调度（Storage Scheduling）领域权威国际化内容研究报告](#存储调度storage-scheduling领域权威国际化内容研究报告)
  - [目录](#目录)
  - [1. IO调度算法](#1-io调度算法)
    - [1.1 CFQ (Completely Fair Queuing) - 完全公平队列](#11-cfq-completely-fair-queuing---完全公平队列)
      - [核心概念](#核心概念)
    - [1.2 Deadline IO Scheduler - 期限调度器](#12-deadline-io-scheduler---期限调度器)
      - [核心概念](#核心概念-1)
    - [1.3 BFQ (Budget Fair Queuing) - 预算公平队列](#13-bfq-budget-fair-queuing---预算公平队列)
      - [核心概念](#核心概念-2)
    - [1.4 MQ-Deadline (Multi-Queue Deadline)](#14-mq-deadline-multi-queue-deadline)
      - [核心概念](#核心概念-3)
    - [1.5 Kyber](#15-kyber)
      - [核心概念](#核心概念-4)
    - [1.6 BFQ-v2](#16-bfq-v2)
      - [演进方向](#演进方向)
  - [2. 存储QoS机制](#2-存储qos机制)
    - [2.1 Linux blk-throttle](#21-linux-blk-throttle)
      - [概述](#概述)
    - [2.2 cgroup IO控制演进](#22-cgroup-io控制演进)
      - [2.2.1 blk-iocost（IOCost）](#221-blk-iocostiocost)
      - [2.2.2 IOLatency](#222-iolatency)
    - [2.3 NVMe QoS](#23-nvme-qos)
      - [2.3.1 NVMe规范中的QoS特性](#231-nvme规范中的qos特性)
      - [2.3.2 设备级QoS解决方案](#232-设备级qos解决方案)
    - [2.4 SSD并行度管理](#24-ssd并行度管理)
      - [2.4.1 SSD内部架构](#241-ssd内部架构)
      - [2.4.2 并行调度优化](#242-并行调度优化)
  - [3. 形式化模型](#3-形式化模型)
    - [3.1 IO调度形式化定义](#31-io调度形式化定义)
      - [3.1.1 基本形式化框架](#311-基本形式化框架)
      - [3.1.2 公平性定义](#312-公平性定义)
    - [3.2 延迟保证](#32-延迟保证)
      - [3.2.1 延迟界限分析](#321-延迟界限分析)
      - [3.2.2 延迟优化策略](#322-延迟优化策略)
    - [3.3 吞吐量优化](#33-吞吐量优化)
      - [3.3.1 吞吐量模型](#331-吞吐量模型)
      - [3.3.2 调度与吞吐量权衡](#332-调度与吞吐量权衡)
  - [4. 最新研究进展](#4-最新研究进展)
    - [4.1 键值存储调度](#41-键值存储调度)
      - [4.1.1 LSM-Tree优化调度](#411-lsm-tree优化调度)
      - [4.1.2 调度策略](#412-调度策略)
      - [4.1.3 键值分离](#413-键值分离)
    - [4.2 分布式存储调度](#42-分布式存储调度)
      - [4.2.1 主流分布式文件系统](#421-主流分布式文件系统)
      - [4.2.2 QoS保证机制](#422-qos保证机制)
      - [4.2.3 多租户性能隔离](#423-多租户性能隔离)
    - [4.3 云存储QoS](#43-云存储qos)
      - [4.3.1 云存储QoS要求](#431-云存储qos要求)
      - [4.3.2 Kubernetes存储QoS](#432-kubernetes存储qos)
      - [4.3.3 NVMe/TCP QoS](#433-nvmetcp-qos)
    - [4.4 研究趋势与开放问题](#44-研究趋势与开放问题)
      - [4.4.1 当前研究热点](#441-当前研究热点)
      - [4.4.2 开放研究问题](#442-开放研究问题)
  - [5. 参考文献与资源](#5-参考文献与资源)
    - [5.1 学术论文](#51-学术论文)
    - [5.2 技术文档与规范](#52-技术文档与规范)
    - [5.3 开源项目与工具](#53-开源项目与工具)
    - [5.4 关键研究人员与机构](#54-关键研究人员与机构)
  - [附录：调度器选择指南](#附录调度器选择指南)
    - [按存储类型选择](#按存储类型选择)
    - [按工作负载选择](#按工作负载选择)

---

## 1. IO调度算法

### 1.1 CFQ (Completely Fair Queuing) - 完全公平队列

#### 核心概念

CFQ是Linux内核中经典的IO调度算法，自2003年起被引入，曾是桌面系统的默认调度器。

**设计目标：**

- 为所有发起IO请求的进程提供公平的磁盘IO带宽分配
- 基于时间片（time slice）而非IOPS进行资源分配
- 支持进程级别的优先级控制

**技术实现：**

- 为每个进程维护独立的IO请求队列（基于PID哈希，默认64个队列）
- 使用红黑树（red-black tree）实现每进程请求队列的排序和合并
- 采用轮询（round-robin）方式调度各队列
- 同步请求按进程分类，异步请求按优先级批量处理

**关键参数：**

- `slice_idle`: 定义CFQ在特定队列上等待下一个请求的空闲时间
- `back_seek_max`: 指定向后寻道的最大距离（KB）
- 默认从每个队列提取4个请求进行调度

**分类体系：**

- Real time（最高优先级，0-7级）
- Best effort（默认类别，4级为默认优先级）
- Idle（最低优先级，仅当无其他IO时服务）

**局限性：**

- 在SSD上表现较差，因为SSD没有寻道开销，CFQ的idling机制反而增加延迟
- 异构工作负载共存时 vulnerable：高优先级应用发送小IO，低优先级应用发送大IO时，后者可能垄断存储设备

**引用文献：**

- Linux Kernel Development, 3rd Edition - Robert Love
- ACM SOSP'01: Anticipatory scheduling paper

---

### 1.2 Deadline IO Scheduler - 期限调度器

#### 核心概念

Deadline调度器旨在保证每个请求的服务开始时间，防止请求饿死。

**设计目标：**

- 保证最大延迟（max latency per request）
- 读请求具有更低的deadline（500ms），因为进程通常阻塞等待读完成
- 写请求deadline较长（5秒），允许更多合并机会

**数据结构：**

- 维护两个FIFO队列（读/写），按deadline排序
- 维护两个LBA（Logical Block Address）排序队列
- 每个请求分配deadline = 当前时间 + expire值

**调度策略：**

1. 检查FIFO队列中是否有请求超过deadline
2. 如有过期请求，优先处理
3. 如无过期请求，从LBA排序队列提取请求
4. 采用批量（batch）处理，优先读请求
5. 防止写请求饿死：通过`writes_starved`参数控制读优先次数

**关键参数：**

```
read_expire (ms): 读请求过期时间，默认500ms
write_expire (ms): 写请求过期时间，默认5000ms
fifo_batch: 每批处理的最大请求数
writes_starved: 读优先于写的次数限制
```

**适用场景：**

- 数据库工作负载
- 延迟敏感应用
- 传统HDD（依赖寻道优化）

**引用文献：**

- Linux Kernel Documentation: deadline-iosched.txt
- Red Hat Customer Portal Technical Solutions

---

### 1.3 BFQ (Budget Fair Queuing) - 预算公平队列

#### 核心概念

BFQ是一种比例共享（proportional-share）IO调度器，由Paolo Valente等人开发，Linux 4.12合并入主内核。

**设计目标：**

- 为交互式和软实时应用提供低延迟
- 保证各进程按权重比例获得设备吞吐量
- 提供强公平性/带宽/延迟保证

**核心机制：**

- 基于预算（budget）而非时间片：预算以扇区数（sectors）计量
- 每个进程关联一个权重和一个bfq_queue
- 采用B-WF2Q+（Budget-Worst-case Fair Weighted Fair Queuing+）算法
- 使用增强红黑树实现O(log N)复杂度

**预算管理：**

```
- 队列获得设备访问权后，预算随请求派发递减
- 预算耗尽、队列变空或预算超时发生时，队列过期
- 预算超时防止随机IO进程持有设备时间过长
```

**关键优化启发式算法：**

1. **权重提升（Weight-Raising）**：检测交互式和软实时应用，给予超过公平份额的吞吐量
2. **早期队列合并（EQM）**：检测交错IO（cooperating processes），合并队列提高吞吐量
3. **突发队列处理**：自动禁用突发创建队列的idling，提高吞吐量

**预算自适应：**

- 顺序IO绑定应用：分配大预算
- 时间敏感应用：分配小预算

**性能表现：**

- 与CFQ相比：改善延迟达50.3%
- 与noop相比：提升带宽公平性达37.3%
- 在NVMe上开销较高：BFQ吞吐量仅为none调度器的0.43-0.63倍

**引用文献：**

- ACM SYSTOR 2012: "Improving Application Responsiveness with the BFQ Disk I/O Scheduler"
- Linux Kernel Documentation: bfq-iosched.html

---

### 1.4 MQ-Deadline (Multi-Queue Deadline)

#### 核心概念

MQ-Deadline是传统Deadline调度器的blk-mq（多队列块层）适配版本。

**架构适配：**

- 支持多队列硬件（NVMe等）
- 维护独立的读写FIFO队列
- 维护按扇区号排序的sorted FIFO队列

**调度流程：**

1. 优先从sorted FIFO队列派发请求（LBA顺序）
2. 监控读写队列的deadline
3. 请求即将违反deadline时提升优先级
4. 批量派发后根据历史性能调整读写优先级

**默认参数：**

- 读请求deadline：500ms
- 写请求deadline：5000ms

**适用场景：**

- RHEL默认调度器（大多数设备）
- 混合读写工作负载
- 需要延迟保证的数据库应用

**引用文献：**

- Linux Kernel Patchwork: "add blk-mq adaptation of the deadline IO scheduler"
- RHEL Documentation: Monitoring and Managing System Status

---

### 1.5 Kyber

#### 核心概念

Kyber是Facebook（Omar Sandoval）开发的低开销多队列IO调度器，Linux 4.12合并。

**设计特点：**

- 完全MQ感知（blk-mq native）
- 使用可扩展的令牌（token-based）算法
- 自调节队列深度以满足目标延迟

**调度域（Scheduling Domains）：**

```c
KYBER_READ          // 同步读请求
KYBER_SYNC_WRITE    // 同步写请求
KYBER_OTHER         // 异步写、discard等
```

**核心机制：**

- 为每个调度域维护独立的请求队列和令牌池
- 动态调整各域的队列深度（in-flight requests）
- 基于延迟统计信息自调节

**延迟目标（默认）：**

- 读延迟目标：2ms（2,000,000 ns）
- 同步写延迟目标：10ms（10,000,000 ns）

**自适应算法：**

```
GOOD: 延迟 ≤ 目标值
BAD:  延迟 > 目标值
AWFUL: 延迟 ≥ 2×目标值
GREAT: 延迟 ≤ 0.5×目标值
```

根据状态调整队列深度，实现延迟控制。

**性能表现：**

- 在NVMe上比BFQ开销低
- 吞吐量比none调度器降低14-47%
- 适合低延迟设备（NVMe、SSD）

**可调参数：**

```
/sys/block/<device>/queue/iosched/read_lat_nsec
/sys/block/<device>/queue/iosched/write_lat_nsec
```

**引用文献：**

- Linux Kernel Patchwork: "blk-mq: introduce Kyber multiqueue I/O scheduler"
- Phoronix: "BFQ I/O Scheduler Lands Along With New Kyber Scheduler"

---

### 1.6 BFQ-v2

#### 演进方向

BFQ-v2是BFQ的持续演进版本，主要改进包括：

**优化方向：**

- 降低多队列环境下的开销
- 改进SSD上的性能表现
- 增强cgroup v2支持
- 优化延迟-吞吐量权衡

**主要改进：**

1. **更精确的预算预测**：基于历史IO模式动态调整
2. **改进的idling策略**：在NVMe上更智能地禁用不必要的idling
3. **增强的权重提升机制**：更准确地检测交互式应用
4. **更好的并行性利用**：与blk-mq更深度的集成

---

## 2. 存储QoS机制

### 2.1 Linux blk-throttle

#### 概述

blk-throttle是Linux内核中的IO限流机制，基于cgroup实现。

**功能特性：**

- 支持IOPS（每秒IO操作数）限流
- 支持带宽（bytes/s）限流
- 支持读写独立配置
- 基于cgroup v1/v2层级管理

**配置接口：**

```bash
# cgroup v1
/sys/fs/cgroup/blkio/blkio.throttle.read_bps_device
/sys/fs/cgroup/blkio/blkio.throttle.write_bps_device
/sys/fs/cgroup/blkio/blkio.throttle.read_iops_device
/sys/fs/cgroup/blkio/blkio.throttle.write_iops_device

# 配置格式: "major:minor limit"
echo "8:0 1048576" > blkio.throttle.read_bps_device  # 限制1MB/s读
```

**局限性：**

- **非工作守恒（non-work-conserving）**：即使设备有剩余能力也不允许超过限制
- 无法根据工作负载动态调整
- 固定限制难以适应异构存储设备

**适用场景：**

- 防止特定进程/容器占用过多IO资源
- 基础的多租户资源隔离

---

### 2.2 cgroup IO控制演进

#### 2.2.1 blk-iocost（IOCost）

**核心改进：**
IOCOST使用IO成本模型改进QoS控制。

**成本模型：**

```
请求成本 = f(请求类型, 大小, 随机/顺序)
默认使用四个线性模型：
- 顺序读成本
- 随机读成本
- 顺序写成本
- 随机写成本
```

**工作机制：**

- 请求提交时，cgroup本地虚拟时间按成本增加
- 根据cgroup IO权重调整成本
- 如果cgroup领先于全局虚拟时间，则限流

**高级特性：**

- 支持自定义成本模型（eBPF程序）
- 自动检测磁盘饱和度
- 动态调整发送速率（50%-150%范围）

**配置接口：**

```bash
# cgroup v2
/sys/fs/cgroup/io.cost.qos
/sys/fs/cgroup/io.cost.model

# 启用blk-iocost
echo "254:48 enable=1 ctrl=user rpct=95.00 rlat=5000 wpct=95.00 wlat=5000 min=50.00 max=150.00" > io.cost.qos
```

#### 2.2.2 IOLatency

**功能：**

- 设置每组的IO延迟目标
- 基于延迟反馈进行调节

**挑战：**

- 现实世界中最优延迟阈值难以确定
- 需要针对不同设备和负载调优

---

### 2.3 NVMe QoS

#### 2.3.1 NVMe规范中的QoS特性

**NVMe 1.4+ 规范特性：**

**1. NVM Sets和IO Determinism：**

- 支持更好的性能隔离
- 改善QoS保证

**2. Endurance Groups：**

- 在namespace级别实现QoS
- 独立的擦除管理

**3. Predictable Latency Mode：**

- 提供可预测的延迟模式
- 减少尾部延迟（tail latency）

#### 2.3.2 设备级QoS解决方案

**OPS Isolation（Over-Provisioning Space Isolation）：**

- 按工作负载分区预留空间
- 擦除块仅包含单个工作负载的页面
- 防止GC（垃圾回收）干扰

**WA-BC（Write Amplification - Budget Controller）：**

- 实现擦除块级隔离
- 考虑不同VM的WAF（写放大因子）
- 实现良好的性能隔离

**FlashBlox：**

- 硬件级隔离：将通道划分为虚拟SSD（vSSD）
- 每个通道独立运行
- 引入迁移机制均衡磨损

**ttFlash：**

- 通过最小化GC导致的资源阻塞消除尾部延迟
- 为内部功能预留共享资源

---

### 2.4 SSD并行度管理

#### 2.4.1 SSD内部架构

**并行层次：**

```
Channel（通道）→ Chip（芯片）→ Die（晶粒）→ Plane（平面）
```

**Flash Translation Layer（FTL）职责：**

1. 逻辑块映射（LBA→PBA）
2. 垃圾回收管理
3. 磨损均衡
4. 地址翻译缓存管理

#### 2.4.2 并行调度优化

**Parallel-DFTL：**

- 将地址翻译请求与数据访问请求分离
- 独立队列管理，允许并行调度
- 隐藏地址翻译开销
- 性能提升达32%

**PIOS（Parallelizable I/O Scheduler）：**

- 精确定位地址翻译中的冲突flash请求
- 引入CER（Conflict Eliminated Requests）重组请求
- 读写差异化调度策略
- 小尺寸优先写调度
- 高并行密度优先读调度

**内部调度挑战：**

- NCQ（Native Command Queuing）限制
- GC活动干扰主机请求
- 多租户环境下尾部延迟恶化

---

## 3. 形式化模型

### 3.1 IO调度形式化定义

#### 3.1.1 基本形式化框架

**请求模型：**

```
请求 r = (arrival_time, deadline, size, type, priority)
其中 type ∈ {READ, WRITE}
```

**调度器状态：**

```
S = (Q, T, B)
Q: 请求队列集合
T: 当前时间
B: 各队列预算/权重
```

**调度策略形式化：**

```
schedule(S) → r ∈ ⋃Q 或 NULL
满足：
- 如果存在 r 使得 current_time > r.deadline，优先调度
- 否则根据公平性策略选择
```

#### 3.1.2 公平性定义

**比例公平（Proportional Fairness）：**

```
对于权重为w_i的队列i，其获得的带宽B_i满足：
B_i / B_j = w_i / w_j
```

**WF2Q+（Worst-case Fair Weighted Fair Queuing+）：**

- 保证每个队列获得与其权重成比例的吞吐量份额
- 偏差有界，与预算无关

**BFQ形式化特性：**

```
延迟界限：D ≤ (n-1) × max_budget / device_throughput + request_service_time
其中n为活跃队列数
```

### 3.2 延迟保证

#### 3.2.1 延迟界限分析

**硬实时（Hard Real-Time）保证：**

```
对于周期任务τ_i = (C_i, T_i, D_i)：
- C_i: 最坏执行时间
- T_i: 周期
- D_i: 相对截止时间

可调度性条件（EDF）：
∑(C_i / T_i) ≤ 1
```

**软实时（Soft Real-Time）保证：**

```
尾部延迟界限：P(latency > L) ≤ ε
```

**MittOS方法：**

- 快速拒绝无法在规定时间内完成的请求
- 返回EBUSY错误，允许应用转向其他副本
- 使用Open Channel SSD监控每通道争用

#### 3.2.2 延迟优化策略

**读写隔离：**

- 优先处理读请求（同步IO）
- 延迟写请求（异步IO）
- 防止写操作阻塞读操作

**时间片管理：**

- 公平时间片管理允许IO时间片分割
- 并发请求发出
- 读写干扰管理

### 3.3 吞吐量优化

#### 3.3.1 吞吐量模型

**系统吞吐量：**

```
Throughput = N / (Σservice_time_i + Σwaiting_time_i)
```

**优化目标：**

```
maximize: Throughput
subject to: latency_i ≤ deadline_i 或 E[latency] ≤ threshold
```

#### 3.3.2 调度与吞吐量权衡

**批量调度（Batch Scheduling）：**

- 合并相邻扇区请求减少寻道
- 通过`fifo_batch`参数控制批量大小
- 增加吞吐量但增加延迟方差

**并行性利用：**

- 利用SSD内部并行性（多通道）
- 请求拆分与并行执行
- 隐藏地址翻译开销

---

## 4. 最新研究进展

### 4.1 键值存储调度

#### 4.1.1 LSM-Tree优化调度

**LSM-Tree基本结构：**

```
Level 0 (MemTable→Immutable→SSTable)
Level 1 (合并后的SSTable)
...
Level N (最大层)
```

**Autumn键值存储：**

- 新颖的Garnering合并策略
- 动态调整相邻层容量比
- 点查询和范围查询复杂度：O(√log N)
- 在RocksDB/LevelDB上实现

**Dostoevsky：**

- 动态适应Fluid LSM-tree设计空间
- 引入Lazy Leveling合并策略
- 优化Bloom filter内存分配（Monkey算法）
- 最大化最差情况吞吐量

**写放大（Write Amplification）优化：**

```
WAF_LSM = 合并开销因子
WAF_SSD = SSD内部写放大
总WAF = WAF_LSM × WAF_SSD
```

#### 4.1.2 调度策略

**Compaction调度：**

- CaaS-LSM（Compaction-as-a-Service）
- 基于资源、类型、应用优先级和SST文件级别的调度
- 分离存储架构中的远程compaction执行

**SILK策略：**

- 在低负载期间推迟flush和compaction
- 允许小层compaction抢占大层compaction
- 减少写停顿（write stall）

#### 4.1.3 键值分离

**WiscKey：**

- 将值存储在单独的日志中
- 减少compaction时的数据移动
- 利用SSD随机读性能快速检索值

---

### 4.2 分布式存储调度

#### 4.2.1 主流分布式文件系统

**Ceph：**

- 统一存储（对象、块、文件）
- CRUSH算法实现数据分布
- 支持自适应映射和异构设备
- SLA感知资源管理

**GlusterFS：**

- 无中心元数据服务器设计
- 基于哈希的数据分布
- 弹性哈希算法
- 小文件性能挑战

**HDFS：**

- 主从架构（NameNode + DataNode）
- 大文件优化
- 高吞吐顺序访问

#### 4.2.2 QoS保证机制

**SLA感知自适应映射：**

- 隔离模式（isolated mode）：紧急客户端专用资源
- 共享模式（shared mode）：正常客户端访问所有资源
- 逻辑集群（logical cluster）技术
- 正常包含（normal inclusion）策略

**Token-Based QoS（bQueue）：**

- 将令牌分配建模为max-flow问题
- 在存储桶级别提供QoS
- 支持上下限IO速率控制

**SolidFire QoS架构：**

1. **全SSD架构**：一致的延迟
2. **真正的横向扩展**：线性可预测性能
3. **无RAID数据保护**：故障时可预测性能
4. **均衡负载分布**：消除热点
5. **细粒度QoS控制**：消除吵闹邻居
6. **性能虚拟化**：独立于容量的性能控制

#### 4.2.3 多租户性能隔离

**主要挑战：**

- 吵闹邻居（noisy neighbor）效应
- 资源争用导致的性能抖动
- 故障情况下的SLA保证

**解决方案：**

- 基于权重的I/O调度
- 最小IOPS保证
- 优先级调度
- 资源预留与限制

---

### 4.3 云存储QoS

#### 4.3.1 云存储QoS要求

**六大核心要求：**

1. **全SSD架构**：为每个IO提供一致延迟
2. **真正的横向扩展架构**：线性、可预测的性能增长
3. **无RAID数据保护**：任何故障情况下可预测的性能
4. **均衡负载分布**：消除造成不可预测IO延迟的热点
5. **细粒度QoS控制**：完全消除吵闹邻居，保证卷性能
6. **性能虚拟化**：按需独立于容量控制性能

#### 4.3.2 Kubernetes存储QoS

**实现机制：**

- PersistentVolumeClaim（PVC）级别QoS注解
- CSI（Container Storage Interface）参数
- 基于cgroup的blkio控制

**SimplyBlock QoS特性：**

- 每卷IOPS和吞吐量策略
- 跨租户/命名空间的优先级调度
- 节点故障或扩展期间的实时性能保证
- 与多租户和快照共存

#### 4.3.3 NVMe/TCP QoS

**LightOS实现：**

- 读写分离：避免队头阻塞
- 每租户IO上限：保证隔离性能
- 全局FTL：跨SSD均匀平衡写入
- 统一擦除和垃圾回收活动

**网络级QoS：**

- 启用巨型帧（9000 MTU）
- 配置PFC（Priority Flow Control）
- 实施ETS（Enhanced Transmission Selection）
- 存储流量优先分配

---

### 4.4 研究趋势与开放问题

#### 4.4.1 当前研究热点

1. **ML/AI驱动的IO调度**
   - 基于负载预测的预取
   - 自适应调度策略选择
   - 强化学习优化调度决策

2. **存算一体架构**
   - 计算存储（Computational Storage）
   - 近数据处理减少传输
   - 智能SSD（SmartNIC + SSD）

3. **新型存储介质**
   - CXL（Compute Express Link）内存扩展
   - SCM（Storage Class Memory）优化
   - ZNS（Zoned Namespace）SSD

4. **形式化验证**
   - 调度算法的正确性证明
   - 延迟保证的形式化验证
   - 使用Coq/TLA+等工具验证

#### 4.4.2 开放研究问题

1. **异构存储环境下的统一调度**
   - HDD/SSD/NVMe/SCM混合调度
   - 自动分层与数据放置

2. **云原生存储QoS**
   - 容器化环境下的细粒度控制
   - Serverless存储性能保证

3. **可持续存储调度**
   - 能耗感知的调度策略
   - 碳足迹优化

4. **安全与隔离**
   - 机密计算环境下的存储隔离
   - 侧信道攻击防护

---

## 5. 参考文献与资源

### 5.1 学术论文

| 论文 | 会议/期刊 | 年份 |
|------|----------|------|
| Improving Application Responsiveness with the BFQ Disk I/O Scheduler | ACM SYSTOR | 2012 |
| Dostoevsky: Better Space-Time Trade-Offs for LSM-Tree | ACM SIGMOD | 2018 |
| Autumn: A Scalable Read Optimized LSM-tree | arXiv/PVLDB | 2020 |
| Fairness, Isolation, Predictability and Performance Management in NVMe Devices: A Survey | ATLarge Research | 2023 |
| Performance Characterization of Modern Storage Stacks | ACM CHEOPS | 2023 |
| File Fragmentation from the Perspective of I/O Control | USENIX HotStorage | 2022 |
| CFFQ: Completely Fair FIFO Queueing | ACM IMCOM | 2017 |

### 5.2 技术文档与规范

- Linux Kernel Documentation:
  - `Documentation/block/cfq-iosched.txt`
  - `Documentation/block/deadline-iosched.txt`
  - `Documentation/block/bfq-iosched.html`
  - `Documentation/block/kyber-iosched.txt`
  - `Documentation/admin-guide/cgroup-v1/blkio-controller.rst`

- NVMe Specifications:
  - NVMe Base Specification 2.0
  - NVMe-oF Specification 1.1

### 5.3 开源项目与工具

- **FIO**: Flexible I/O Tester - 存储性能基准测试
- **blktrace/blkparse**: 块层IO跟踪
- **iostat/vmstat**: 系统IO监控
- **bpftrace/eBPF**: 动态跟踪与性能分析

### 5.4 关键研究人员与机构

- **Paolo Valente** (University of Modena and Reggio Emilia) - BFQ作者
- **Jens Axboe** (Meta) - Linux块层维护者
- **ATLarge Research** (Vrije Universiteit Amsterdam) - NVMe QoS研究
- **UMass Amherst** - 存储系统研究

---

## 附录：调度器选择指南

### 按存储类型选择

| 存储类型 | 推荐调度器 | 说明 |
|---------|-----------|------|
| SATA/SAS HDD | mq-deadline / bfq | 需要寻道优化 |
| SATA SSD | mq-deadline | 平衡的延迟和吞吐量 |
| NVMe SSD | none / kyber | 设备自带调度，减少软件开销 |
| 混合环境 | bfq | 公平性和响应性优先 |

### 按工作负载选择

| 工作负载 | 推荐调度器 | 关键参数 |
|---------|-----------|---------|
| 数据库 | mq-deadline | 降低read_expire |
| 桌面/交互 | bfq | 启用低延迟模式 |
| 虚拟化 | none / mq-deadline | 依赖hypervisor调度 |
| 大数据 | none | 最大化吞吐量 |
| 实时系统 | 自定义调度器 | 硬延迟保证 |

---

_报告结束_

> 注：本报告基于公开可获取的学术论文、技术文档和权威资源整理，涵盖了存储调度领域的主要国际权威内容。
