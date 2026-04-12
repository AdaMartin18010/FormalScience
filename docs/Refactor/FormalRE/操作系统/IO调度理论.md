---
title: "IO调度理论"
status: "已完成"
created: "2026-04-12"
updated: "2026-04-12"
tags: ["IO调度", "磁盘调度", "电梯算法", "存储系统"]
---

# IO调度理论

## 1. 概述

I/O调度是操作系统管理磁盘和其他存储设备访问请求的关键机制。由于I/O操作（尤其是磁盘I/O）相对于CPU操作非常缓慢，有效的I/O调度可以显著提高系统整体性能和响应能力。

### 1.1 I/O性能瓶颈

```
┌─────────────────────────────────────────────────────────┐
│  CPU: 执行数亿条指令只需1秒                               │
├─────────────────────────────────────────────────────────┤
│  内存访问: 需要100-300纳秒                               │
├─────────────────────────────────────────────────────────┤
│  SSD I/O: 需要10-100微秒   (~1000x内存)                  │
├─────────────────────────────────────────────────────────┤
│  磁盘I/O: 需要5-10毫秒     (~10,000,000x内存)            │
└─────────────────────────────────────────────────────────┘
```

### 1.2 I/O调度目标

1. **最小化寻道时间**：减少磁盘磁头移动距离
2. **最大化吞吐量**：单位时间内处理更多I/O请求
3. **公平性**：各进程获得合理的I/O带宽
4. **响应延迟**：保证交互式应用的低延迟
5. **避免饥饿**：防止某些请求长期得不到服务

## 2. 磁盘I/O基础

### 2.1 磁盘结构

```
        盘片(Platter)
    ┌─────────────────┐
   ╱    磁道(Track)    ╲
  │   ┌───────────┐    │
  │  ╱  扇区      ╲   │ ← 磁头(Head)
  │ │  (Sector)    │  │
  │  ╲             ╱   │
  │   └───────────┘    │
   ╲                  ╱
    └─────────────────┘

柱面(Cylinder): 相同半径的所有磁道
```

### 2.2 磁盘访问时间

$$T_{access} = T_{seek} + T_{rotation} + T_{transfer}$$

| 组件 | 典型值 | 说明 |
|------|--------|------|
| 寻道时间($T_{seek}$) | 3-10ms | 磁头移动到目标磁道 |
| 旋转延迟($T_{rotation}$) | 2-4ms | 等待扇区转到磁头下(平均半圈) |
| 传输时间($T_{transfer}$) | 0.1-1ms | 实际数据传输 |

**寻道时间主导**：占总延迟的70-80%

### 2.3 I/O请求特性

- **顺序访问**：连续扇区，高带宽，低寻道
- **随机访问**：分散扇区，低带宽，高寻道

## 3. 磁盘调度算法

### 3.1 先来先服务（FCFS）

**原理**：按照请求到达顺序服务。

**示例**：

```
当前磁头位置：50
请求队列：95, 180, 34, 119, 11, 123, 62, 64

FCFS服务顺序：50 → 95 → 180 → 34 → 119 → 11 → 123 → 62 → 64

总磁头移动：
|95-50| + |180-95| + |34-180| + |119-34| + |11-119| + |123-11| + |62-123| + |64-62|
= 45 + 85 + 146 + 85 + 108 + 112 + 61 + 2 = 644 磁道
```

**特点**：

- 实现简单
- 公平性好
- 性能较差（随机寻道多）

### 3.2 最短寻道时间优先（SSTF）

**原理**：优先服务距离当前磁头位置最近的请求。

**形式化定义**：
$$\text{选择 } r_i \text{ 使得 } |pos(r_i) - head| = \min_{r_j} |pos(r_j) - head|$$

**示例**：

```
当前磁头位置：50
请求队列：95, 180, 34, 119, 11, 123, 62, 64

SSTF服务顺序：50 → 62 → 64 → 34 → 11 → 95 → 119 → 123 → 180

总磁头移动：
12 + 2 + 30 + 23 + 84 + 24 + 4 + 57 = 236 磁道 (比FCFS减少63%)
```

**问题**：

- 可能导致饥饿（中间位置请求持续到达时，边缘请求被忽略）

### 3.3 电梯算法（SCAN）

**原理**：磁头单向移动，服务沿途请求，到达边界后反向。

**示例**（向高地址移动）：

```
当前磁头位置：50，磁道范围：0-199，方向：向上
请求队列：95, 180, 34, 119, 11, 123, 62, 64

SCAN服务顺序：50 → 62 → 64 → 95 → 119 → 123 → 180 → 199 → 34 → 11

总磁头移动：
(199-50) + (199-11) = 149 + 188 = 337 磁道
```

**变体**：

- **LOOK**：不到达物理边界，只到最远请求处反向
- **C-SCAN（循环扫描）**：单向扫描，到达边界后直接跳回起始点

### 3.4 C-SCAN（循环扫描）

**原理**：

- 磁头单向移动（如从外向内）
- 到达最大请求后，直接返回最小请求（不服务）
- 重新开始单向扫描

**示例**：

```
当前磁头位置：50，方向：向上
请求队列：95, 180, 34, 119, 11, 123, 62, 64

C-SCAN服务顺序：50 → 62 → 64 → 95 → 119 → 123 → 180 → 11 → 34

总磁头移动：
(180-50) + (180-11) + (34-11) = 130 + 169 + 23 = 322 磁道
```

**优点**：

- 更均匀的等待时间
- 避免两端请求等待时间过长

### 3.5 C-LOOK

**改进的C-SCAN**：不移动到物理边界，只在有请求的范围内移动。

```
C-LOOK服务顺序：50 → 62 → 64 → 95 → 119 → 123 → 180 → 11 → 34

总磁头移动：
(180-50) + (180-11) + (34-11) = 322 磁道（本例与C-SCAN相同）
```

### 3.6 算法对比

| 算法 | 优点 | 缺点 | 适用场景 |
|------|------|------|----------|
| FCFS | 简单、公平 | 性能差 | 轻负载 |
| SSTF | 低延迟 | 可能饥饿 | 交互式系统 |
| SCAN | 无饥饿、较好性能 | 两端请求等待不均 | 通用 |
| C-SCAN | 等待时间均匀 | 存在空移动 | 高负载 |
| C-LOOK | 高效、均匀 | 实现稍复杂 | 现代系统 |

## 4. 现代I/O调度器

### 4.1 Linux I/O调度器

#### 4.1.1 NOOP

**特点**：

- 最简单的调度器
- 基本FIFO，只做简单合并
- 适合SSD（无寻道延迟）

#### 4.1.2 Deadline调度器

**目标**：保证请求在截止时间前完成，防止饥饿。

**队列结构**：

```
┌─────────────────────────────────────────┐
│           排序队列（按扇区号）            │
│  [1034] → [2056] → [3089] → [4123]     │
└─────────────────────────────────────────┘
┌─────────────────────────────────────────┐
│           读请求截止时间队列              │
│  [Req1:500ms] → [Req2:500ms] → ...     │
└─────────────────────────────────────────┘
┌─────────────────────────────────────────┐
│           写请求截止时间队列              │
│  [Req3:5000ms] → [Req4:5000ms] → ...   │
└─────────────────────────────────────────┘
```

**调度策略**：

- 优先处理截止时间最近的请求
- 读请求截止时间（默认500ms）< 写请求（默认5s）
- 批量处理相邻请求

#### 4.1.3 CFQ（Complete Fair Queuing）

**目标**：公平分配I/O带宽给各进程。

**原理**：

- 每个进程拥有自己的请求队列
- 使用时间片轮转调度各队列
- 每个进程获得相等的I/O时间份额

```
┌─────────────────────────────────────────┐
│              CFQ队列结构                 │
├─────────────────────────────────────────┤
│  进程A队列: [R1] → [R2] → [R3]          │
│  进程B队列: [R4] → [R5]                 │
│  进程C队列: [R6] → [R7] → [R8] → [R9]   │
├─────────────────────────────────────────┤
│  时间片轮转: A → B → C → A → B → C ... │
└─────────────────────────────────────────┘
```

**I/O优先级**：

- RT（实时）：最高优先级
- BE（尽力）：默认优先级
- IDLE：空闲时执行

#### 4.1.4 BFQ（Budget Fair Queuing）

**改进的CFQ**：

- 基于预算而非时间片
- 预算 = 预计传输的字节数
- 适合交互式应用

**优势**：

- 更好的响应性
- 更低的延迟
- 适合桌面系统

#### 4.1.5 Kyber

**目标**：低延迟，高吞吐量。

**双队列结构**：

- 同步请求队列（读 + 同步写）
- 异步请求队列（异步写）

**令牌桶机制**：

- 控制每个队列的I/O速率
- 动态调整令牌数量

### 4.2 I/O调度器选择

| 设备类型 | 推荐调度器 | 原因 |
|----------|-----------|------|
| HDD | BFQ/MQ-DEADLINE | 减少寻道、公平性 |
| SSD | NONE/NOOP/MQ-DEADLINE | 无寻道延迟 |
| NVMe | NONE | 设备自带调度 |
| 混合存储 | MQ-DEADLINE | 兼顾两者 |

## 5. RAID与I/O调度

### 5.1 RAID级别对比

| RAID | 读性能 | 写性能 | 容错 | 空间利用率 |
|------|--------|--------|------|-----------|
| 0 | Nx | Nx | 无 | 100% |
| 1 | 1x-2x | 1x | 1盘 | 50% |
| 5 | (N-1)x | (N-1)x（小写慢） | 1盘 | (N-1)/N |
| 6 | (N-2)x | (N-2)x（小写慢） | 2盘 | (N-2)/N |
| 10 | Nx | Nx | 每对1盘 | 50% |

### 5.2 RAID 5写惩罚

**小写操作**（修改一个块）：

```
读旧数据 → 读旧校验 → 计算新校验 → 写新数据 → 写新校验
(4次I/O)
```

**写惩罚因子**：4

## 6. SSD I/O调度

### 6.1 SSD特性

| 特性 | 影响 |
|------|------|
| 无机械延迟 | 随机/顺序访问差异小 |
| 写前擦除 | 写放大问题 |
| 有限擦写次数 | 需要磨损均衡 |
| 并行通道 | 高并发性能 |

### 6.2 SSD优化策略

**1. TRIM/UNMAP**：

- 通知SSD哪些块不再使用
- 允许SSD提前擦除，加速后续写入

**2. 写入合并**：

- 将小写合并为大块写入
- 减少写放大

**3. 避免原地更新**：

- 使用日志结构（如LFS）
- 减少块擦除次数

## 7. 形式化分析

### 7.1 I/O调度模型

**系统状态**：
$$S = (H, Q, T)$$
其中：

- $H$：当前磁头位置
- $Q$：请求队列
- $T$：当前时间

**状态转移**：
$$S \xrightarrow{serve(r)} S'$$
$$H' = pos(r), \quad Q' = Q - \{r\}, \quad T' = T + T_{access}(H, r)$$

### 7.2 优化目标

**最小化总寻道距离**：
$$\min \sum_{i=1}^{n} |H_i - H_{i-1}|$$

**最小化最大响应时间**：
$$\min \max_{r \in Q} (T_{completion}(r) - T_{arrival}(r))$$

**NP完全性**：最优磁盘调度是NP完全问题，启发式算法是实用的选择。

## 8. 代码示例

### 8.1 SSTF调度实现

```c
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#define MAX_REQUESTS 100

typedef struct {
    int track;
    int arrival_time;
} IORequest;

int sstf_schedule(IORequest requests[], int n, int head_pos) {
    int completed[MAX_REQUESTS] = {0};
    int total_seek = 0;
    int current_pos = head_pos;
    int completed_count = 0;

    printf("SSTF调度顺序: %d", current_pos);

    while (completed_count < n) {
        int min_dist = 999999;
        int next_idx = -1;

        // 找最近的请求
        for (int i = 0; i < n; i++) {
            if (!completed[i]) {
                int dist = abs(requests[i].track - current_pos);
                if (dist < min_dist) {
                    min_dist = dist;
                    next_idx = i;
                }
            }
        }

        if (next_idx != -1) {
            completed[next_idx] = 1;
            total_seek += min_dist;
            current_pos = requests[next_idx].track;
            completed_count++;
            printf(" → %d", current_pos);
        }
    }

    printf("\n总寻道距离: %d\n", total_seek);
    printf("平均寻道距离: %.2f\n", (float)total_seek / n);

    return total_seek;
}

int main() {
    IORequest requests[] = {
        {95, 0}, {180, 0}, {34, 0}, {119, 0},
        {11, 0}, {123, 0}, {62, 0}, {64, 0}
    };
    int n = sizeof(requests) / sizeof(requests[0]);
    int head = 50;

    sstf_schedule(requests, n, head);

    return 0;
}
```

### 8.2 SCAN电梯算法

```c
int scan_schedule(IORequest requests[], int n, int head_pos, int max_track, int direction) {
    int completed[MAX_REQUESTS] = {0};
    int total_seek = 0;
    int current_pos = head_pos;

    printf("SCAN调度顺序: %d", current_pos);

    // 按磁道排序
    for (int i = 0; i < n; i++) {
        for (int j = i+1; j < n; j++) {
            if (requests[i].track > requests[j].track) {
                IORequest tmp = requests[i];
                requests[i] = requests[j];
                requests[j] = tmp;
            }
        }
    }

    // 找到起始位置
    int start_idx = 0;
    for (int i = 0; i < n; i++) {
        if (requests[i].track >= current_pos) {
            start_idx = i;
            break;
        }
    }

    if (direction == 1) {  // 向上
        // 向上扫描
        for (int i = start_idx; i < n; i++) {
            if (!completed[i]) {
                total_seek += abs(requests[i].track - current_pos);
                current_pos = requests[i].track;
                completed[i] = 1;
                printf(" → %d", current_pos);
            }
        }
        // 到边界后向下
        total_seek += abs(max_track - current_pos);
        current_pos = max_track;
        printf(" → %d(边界)", current_pos);

        for (int i = start_idx - 1; i >= 0; i--) {
            if (!completed[i]) {
                total_seek += abs(requests[i].track - current_pos);
                current_pos = requests[i].track;
                completed[i] = 1;
                printf(" → %d", current_pos);
            }
        }
    }

    printf("\n总寻道距离: %d\n", total_seek);
    return total_seek;
}
```

### 8.3 I/O调度模拟

```python
import heapq
from dataclasses import dataclass
from typing import List

@dataclass
class IORequest:
    track: int
    arrival_time: int
    deadline: int = float('inf')

def calculate_seek_distance(track1: int, track2: int) -> int:
    return abs(track1 - track2)

def fcfs_schedule(requests: List[IORequest], head: int) -> dict:
    """FCFS调度算法"""
    total_seek = 0
    current = head
    order = [current]

    for req in requests:
        total_seek += calculate_seek_distance(current, req.track)
        current = req.track
        order.append(current)

    return {
        'total_seek': total_seek,
        'average_seek': total_seek / len(requests),
        'order': order
    }

def sstf_schedule(requests: List[IORequest], head: int) -> dict:
    """SSTF调度算法"""
    remaining = requests.copy()
    total_seek = 0
    current = head
    order = [current]

    while remaining:
        nearest = min(remaining, key=lambda r: calculate_seek_distance(current, r.track))
        total_seek += calculate_seek_distance(current, nearest.track)
        current = nearest.track
        order.append(current)
        remaining.remove(nearest)

    return {
        'total_seek': total_seek,
        'average_seek': total_seek / len(requests),
        'order': order
    }

def scan_schedule(requests: List[IORequest], head: int, max_track: int = 199) -> dict:
    """SCAN电梯算法"""
    tracks = sorted([r.track for r in requests])
    total_seek = 0
    current = head
    order = [current]

    # 分离上下方向的请求
    up = [t for t in tracks if t >= head]
    down = [t for t in tracks if t < head]

    # 向上扫描
    for track in up:
        total_seek += calculate_seek_distance(current, track)
        current = track
        order.append(current)

    # 到边界反向
    if down:
        total_seek += calculate_seek_distance(current, max_track)
        current = max_track
        order.append(current)

        for track in reversed(down):
            total_seek += calculate_seek_distance(current, track)
            current = track
            order.append(current)

    return {
        'total_seek': total_seek,
        'average_seek': total_seek / len(requests),
        'order': order
    }

# 测试
requests = [IORequest(t, 0) for t in [95, 180, 34, 119, 11, 123, 62, 64]]
head = 50

print("FCFS:", fcfs_schedule(requests, head))
print("SSTF:", sstf_schedule(requests, head))
print("SCAN:", scan_schedule(requests, head))
```

## 9. 性能数据

### 9.1 算法寻道距离对比

| 算法 | 示例寻道距离 | 相对FCFS改进 |
|------|-------------|-------------|
| FCFS | 644 | - |
| SSTF | 236 | 63% |
| SCAN | 337 | 48% |
| C-SCAN | 322 | 50% |
| LOOK | 299 | 54% |

### 9.2 Linux I/O调度器性能

| 调度器 | 吞吐量 | 延迟 | 公平性 | 适用场景 |
|--------|--------|------|--------|----------|
| NOOP | 高 | 低 | 一般 | SSD |
| DEADLINE | 中 | 低 | 好 | 通用 |
| CFQ | 中 | 中 | 优秀 | 多用户 |
| BFQ | 中 | 极低 | 优秀 | 桌面 |

### 9.3 磁盘性能指标

| 指标 | HDD | SSD | NVMe |
|------|-----|-----|------|
| 顺序读 | 200 MB/s | 500 MB/s | 3+ GB/s |
| 随机读 | 0.5 MB/s | 400 MB/s | 2+ GB/s |
| 寻道/访问延迟 | 5-10ms | 0.1ms | 0.02ms |
| IOPS | 100-200 | 10,000+ | 500,000+ |

## 10. 参考链接

- [01.5 内存管理](./01.5_内存管理.md)
- [01.8 磁盘调度](./01.8_磁盘调度.md)
- [存储调度系统](../../Composed/schedule_formal_view/14_存储调度系统/README.md)
- [Linux I/O调度器](https://www.kernel.org/doc/html/latest/block/index.html)

---

_本文档已完成功能性填充，包含完整的理论知识、形式化定义、代码示例和性能数据。_
