---
title: "GPU调度模型"
status: "已完成"
created: "2026-04-12"
updated: "2026-04-12"
tags: ["GPU调度", "CUDA", "异构计算", "并行调度"]
---

# GPU调度模型

## 1. 概述

GPU（图形处理器）调度模型是异构计算体系中的关键组成部分。与CPU面向低延迟的调度不同，GPU调度更注重高吞吐量和数据并行性。现代GPU不仅是图形渲染设备，更是通用并行计算的加速器。

### 1.1 CPU vs GPU 调度差异

| 特性 | CPU调度 | GPU调度 |
|------|---------|---------|
| 设计目标 | 低延迟、高响应 | 高吞吐量、高并行 |
| 线程开销 | 高（上下文切换ms级） | 低（零开销切换） |
| 线程数量 | 少（数十个） | 多（数万个） |
| 调度粒度 | 进程/线程级 | Warp/Wavefront级 |
| 内存模型 | 统一内存 | 分层内存 |

### 1.2 GPU执行模型

```
┌─────────────────────────────────────────────────────┐
│                   GPU设备                            │
│  ┌─────────────────────────────────────────────┐   │
│  │              网格 (Grid)                     │   │
│  │  ┌─────────────────────────────────────┐   │   │
│  │  │           线程块 (Block)             │   │   │
│  │  │  ┌─────────────────────────────┐   │   │   │
│  │  │  │      Warp (32线程)           │   │   │   │
│  │  │  │  [T0][T1]...[T31]           │   │   │   │
│  │  │  └─────────────────────────────┘   │   │   │
│  │  │  ┌─────────────────────────────┐   │   │   │
│  │  │  │      Warp (32线程)           │   │   │   │
│  │  │  │  [T0][T1]...[T31]           │   │   │   │
│  │  │  └─────────────────────────────┘   │   │   │
│  │  └─────────────────────────────────────┘   │   │
│  │  [更多线程块...]                            │   │
│  └─────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────┘
```

## 2. GPU硬件架构

### 2.1 NVIDIA CUDA架构

```
┌─────────────────────────────────────────────────────────┐
│                     GPU芯片                              │
│  ┌─────────────────────────────────────────────────┐   │
│  │  GPC (图形处理集群)                              │   │
│  │  ┌─────────────────────────────────────────┐   │   │
│  │  │  SM (流式多处理器)                        │   │   │
│  │  │  ┌─────────────────────────────────┐   │   │   │
│  │  │  │  CUDA核心                        │   │   │   │
│  │  │  │  ┌─────┐ ┌─────┐ ┌─────┐       │   │   │   │
│  │  │  │  │ ALU │ │ ALU │ │ ALU │ ...   │   │   │   │
│  │  │  │  └─────┘ └─────┘ └─────┘       │   │   │   │
│  │  │  ├─────────────────────────────────┤   │   │   │
│  │  │  │  寄存器文件 (256KB)               │   │   │   │
│  │  │  ├─────────────────────────────────┤   │   │   │
│  │  │  │  共享内存/L1 (64KB)              │   │   │   │
│  │  │  ├─────────────────────────────────┤   │   │   │
│  │  │  │  Warp调度器                      │   │   │   │
│  │  │  └─────────────────────────────────┘   │   │   │
│  │  └─────────────────────────────────────────┘   │   │
│  └─────────────────────────────────────────────────┘   │
├─────────────────────────────────────────────────────────┤
│  全局内存 (GDDR6/HBM)                                    │
└─────────────────────────────────────────────────────────┘
```

### 2.2 AMD RDNA/CDNA架构

| 特性 | RDNA（消费级） | CDNA（数据中心） |
|------|---------------|-----------------|
| 设计目标 | 图形+计算 | 纯计算 |
| Workgroup大小 | 128 (Wave64) | 64 (Wave64) |
| 寄存器文件 | 大 | 更大 |
| 双精度性能 | 低 | 高 |
| 矩阵加速 | 有限 | 完整 |

### 2.3 GPU内存层次

```
┌─────────────────────────────────────────────────────────┐
│  寄存器 (Register)                                      │
│  大小: 256KB/SM | 延迟: 1 cycle | 带宽: 20+ TB/s       │
├─────────────────────────────────────────────────────────┤
│  共享内存/L1 (Shared Memory)                            │
│  大小: 164KB/SM | 延迟: 20-30 cycles | 带宽: ~10 TB/s  │
├─────────────────────────────────────────────────────────┤
│  L2缓存                                                 │
│  大小: 4-8MB | 延迟: 100-200 cycles | 带宽: ~2 TB/s    │
├─────────────────────────────────────────────────────────┤
│  全局内存 (Global Memory)                               │
│  大小: 8-80GB | 延迟: 300-500 cycles | 带宽: 1-3 TB/s  │
├─────────────────────────────────────────────────────────┤
│  主机内存 (Host Memory)                                 │
│  大小: 系统内存 | 延迟: 数千cycles | 带宽: ~50 GB/s    │
└─────────────────────────────────────────────────────────┘
```

## 3. GPU调度机制

### 3.1 Warp调度

**Warp（NVIDIA）/ Wavefront（AMD）**：

- 32个（NVIDIA）或64个（AMD）线程的集合
- SIMT（单指令多线程）执行模型
- Warp内线程执行相同指令

**零开销切换**：

```
时间线:
Warp0  ████████░░░░░░░░████████░░░░░░░░
Warp1  ░░░░░░░░████████░░░░░░░░████████
Warp2  ████████░░░░░░░░░░░░░░░░████████

注: █ 执行中  ░ 等待中（内存/同步）
```

**双发射调度**：

- 每个周期可调度2个独立Warp
- 隐藏内存访问延迟

### 3.2 线程块调度

**调度目标**：

- 最大化SM利用率
- 平衡负载
- 考虑共享内存和寄存器限制

**资源约束**：
$$\text{占用率} = \frac{\text{活跃Warp数}}{\text{最大Warp数}}$$

**影响因素**：

- 每线程寄存器使用
- 每Block共享内存使用
- 每Block线程数

### 3.3 网格级调度

**多流执行**：

```cuda
// CUDA流示例
cudaStream_t stream1, stream2;
cudaStreamCreate(&stream1);
cudaStreamCreate(&stream2);

// 两个内核并发执行
kernel1<<<grid, block, 0, stream1>>>(data1);
kernel2<<<grid, block, 0, stream2>>>(data2);
```

**调度策略**：

1. **时间片轮转**：多个应用交替使用GPU
2. **空间分割**：将GPU SMs分配给不同应用
3. **抢占式调度**：高优先级任务可中断低优先级

## 4. 内核调度策略

### 4.1 先到先服务（FCFS）

**特点**：

- 简单实现
- 可能导致队头阻塞（Head-of-Line Blocking）
- 低优先级任务可能饿死

### 4.2 最短作业优先（SJF）

**启发式估计**：
$$EstimatedTime = \alpha \cdot T_{last} + (1-\alpha) \cdot T_{history}$$

**适用场景**：

- 作业时间可预测
- 批处理工作负载

### 4.3 优先级调度

**优先级因素**：

- 用户指定优先级
- 作业类型（交互式 vs 批处理）
- 等待时间（老化）

**抢占机制**：

- **上下文切换**：保存/恢复寄存器状态
- **计算抢占**：检查点机制

### 4.4 公平共享调度

**目标**：各应用获得公平的GPU时间份额。

**实现方式**：

```
应用A: 配额 = 40% → 使用35% → 下次优先
应用B: 配额 = 60% → 使用65% → 下次限制
```

## 5. 内存调度与优化

### 5.1 全局内存访问模式

**合并访问（Coalesced Access）**：

```
理想情况（合并访问）:
Thread0 访问地址 0x1000
Thread1 访问地址 0x1004
Thread2 访问地址 0x1008
... → 合并为1次128字节传输

非合并访问:
Thread0 访问地址 0x1000
Thread1 访问地址 0x2000
Thread2 访问地址 0x3000
... → 32次独立传输
```

**性能影响**：

- 合并访问：带宽利用率高
- 非合并访问：带宽下降90%+

### 5.2 共享内存优化

**bank冲突**：

```
无冲突（每个线程访问不同bank）:
Thread0 → Bank0
Thread1 → Bank1
...
Thread31 → Bank31

有冲突（多线程访问同bank）:
Thread0 → Bank0
Thread1 → Bank0  ← 冲突！需要串行访问
```

**解决方案**：

- 数据填充（Padding）
- 访问模式调整

### 5.3 零拷贝内存

**原理**：

- 页锁定（Pinned）内存
- CPU和GPU共享虚拟地址
- 避免显式数据传输

**适用场景**：

- 数据只访问一次
- 数据量小
- 频繁同步场景

## 6. 多GPU调度

### 6.1 数据并行

```
┌─────────────┐     ┌─────────────┐
│   GPU 0     │     │   GPU 1     │
│  Batch 0-3  │     │  Batch 4-7  │
└─────────────┘     └─────────────┘
      │                   │
      └─────────┬─────────┘
                ↓
          ┌─────────┐
          │ 结果聚合 │
          └─────────┘
```

### 6.2 模型并行

```
┌─────────────┐     ┌─────────────┐
│   GPU 0     │     │   GPU 1     │
│  层0-层4    │ ──→ │  层5-层8    │
└─────────────┘     └─────────────┘
```

### 6.3 流水线并行

```
时间 →
GPU0: [F1] [F2] [F3] [F4]
GPU1:      [B1] [B2] [B3] [B4]
GPU2:           [F1'] [F2'] [F3'] [F4']
```

## 7. 深度学习中的GPU调度

### 7.1 训练作业调度

**挑战**：

- 长作业占用GPU资源
- 不同作业资源需求差异大
- 优先级动态变化

**调度策略**：

| 策略 | 描述 | 优点 |
|------|------|------|
| Gandiva | 时间切片+迁移 | 支持抢占、资源可预测 |
| Tiresias | 离散事件模拟 | 减少平均JCT |
| Themis | 基于份额的公平 | 保证最小份额 |
| HiveD | 虚拟集群 | 支持异构需求 |

### 7.2 推理服务调度

**批处理（Batching）**：

```
独立处理:
Req1: [处理] → [结果]
Req2:      [处理] → [结果]
Req3:           [处理] → [结果]

动态批处理:
Req1: [         ]
Req2: [  批处理  ] → [结果1,2,3]
Req3: [         ]
```

**连续批处理（Continuous Batching）**：

- 请求到达立即加入当前批
- 已完成的请求退出
- 提高GPU利用率

### 7.3 KV Cache管理

**PagedAttention**：

```
传统: 预分配连续大块内存 → 内部碎片、无法共享

PagedAttention: 分页管理 → 按需分配、支持共享
┌─────┬─────┬─────┬─────┬─────┐
│ P0  │ P1  │ P2  │ P3  │ P4  │  物理块
└─────┴─────┴─────┴─────┴─────┘

请求A逻辑页: 0→P0, 1→P1, 2→P2
请求B逻辑页: 0→P0, 1→P1, 2→P3 (共享前缀)
```

## 8. 形式化模型

### 8.1 GPU调度问题建模

**系统模型**：
$$G = (S, M, K, R)$$
其中：

- $S$：SM集合
- $M$：内存层次
- $K$：内核集合
- $R$：资源约束

**调度目标**：
$$\min \sum_{k \in K} T_{completion}(k) \quad \text{s.t.} \quad \forall r \in R: \text{usage}(r) \leq \text{capacity}(r)$$

### 8.2 占用率计算

$$\text{Occupancy} = \frac{B_{active} \times W_{per\_block}}{W_{max}}$$

其中：

- $B_{active}$：活跃Block数
- $W_{per\_block}$：每Block Warp数
- $W_{max}$：SM最大Warp数

**寄存器限制**：
$$B_{reg} = \frac{R_{total}}{R_{per\_thread} \times T_{per\_block}}$$

### 8.3 内存带宽模型

$$T_{memory} = \frac{D_{total}}{B_{effective}}$$

$$B_{effective} = B_{peak} \times \eta_{coalesced} \times \eta_{cache}$$

## 9. 代码示例

### 9.1 CUDA内核基础

```cuda
// 向量加法内核
__global__ void vectorAdd(const float *A, const float *B, float *C, int numElements)
{
    int i = blockDim.x * blockIdx.x + threadIdx.x;
    if (i < numElements)
        C[i] = A[i] + B[i];
}

// 主机代码
int main()
{
    int numElements = 50000;
    size_t size = numElements * sizeof(float);

    // 分配主机内存
    float *h_A = (float *)malloc(size);
    float *h_B = (float *)malloc(size);
    float *h_C = (float *)malloc(size);

    // 初始化数据
    for (int i = 0; i < numElements; ++i) {
        h_A[i] = rand() / (float)RAND_MAX;
        h_B[i] = rand() / (float)RAND_MAX;
    }

    // 分配设备内存
    float *d_A, *d_B, *d_C;
    cudaMalloc((void **)&d_A, size);
    cudaMalloc((void **)&d_B, size);
    cudaMalloc((void **)&d_C, size);

    // 拷贝数据到设备
    cudaMemcpy(d_A, h_A, size, cudaMemcpyHostToDevice);
    cudaMemcpy(d_B, h_B, size, cudaMemcpyHostToDevice);

    // 启动内核
    int threadsPerBlock = 256;
    int blocksPerGrid = (numElements + threadsPerBlock - 1) / threadsPerBlock;
    vectorAdd<<<blocksPerGrid, threadsPerBlock>>>(d_A, d_B, d_C, numElements);

    // 拷贝结果回主机
    cudaMemcpy(h_C, d_C, size, cudaMemcpyDeviceToHost);

    // 释放资源
    cudaFree(d_A); cudaFree(d_B); cudaFree(d_C);
    free(h_A); free(h_B); free(h_C);

    return 0;
}
```

### 9.2 共享内存优化矩阵乘法

```cuda
#define TILE_WIDTH 16

__global__ void matrixMulShared(float *C, float *A, float *B, int width)
{
    __shared__ float ds_A[TILE_WIDTH][TILE_WIDTH];
    __shared__ float ds_B[TILE_WIDTH][TILE_WIDTH];

    int bx = blockIdx.x, by = blockIdx.y;
    int tx = threadIdx.x, ty = threadIdx.y;

    int Row = by * TILE_WIDTH + ty;
    int Col = bx * TILE_WIDTH + tx;

    float Cvalue = 0;

    for (int m = 0; m < width / TILE_WIDTH; ++m) {
        // 协作加载 tile 到共享内存
        ds_A[ty][tx] = A[Row * width + (m * TILE_WIDTH + tx)];
        ds_B[ty][tx] = B[(m * TILE_WIDTH + ty) * width + Col];
        __syncthreads();

        // 计算部分结果
        for (int k = 0; k < TILE_WIDTH; ++k)
            Cvalue += ds_A[ty][k] * ds_B[k][tx];
        __syncthreads();
    }

    C[Row * width + Col] = Cvalue;
}
```

### 9.3 多流异步执行

```cuda
const int N = 1 << 20;
const int numStreams = 4;
const int streamSize = N / numStreams;
cudaStream_t streams[numStreams];

// 创建流
for (int i = 0; i < numStreams; i++)
    cudaStreamCreate(&streams[i]);

// 分流传输和计算
for (int i = 0; i < numStreams; i++) {
    int offset = i * streamSize;
    cudaMemcpyAsync(d_a + offset, h_a + offset,
                    streamSize * sizeof(float),
                    cudaMemcpyHostToDevice, streams[i]);
    kernel<<<streamSize/256, 256, 0, streams[i]>>>(d_a + offset);
    cudaMemcpyAsync(h_a + offset, d_a + offset,
                    streamSize * sizeof(float),
                    cudaMemcpyDeviceToHost, streams[i]);
}

// 同步
for (int i = 0; i < numStreams; i++)
    cudaStreamSynchronize(streams[i]);
```

### 9.4 GPU利用率监控

```python
import pynvml

pynvml.nvmlInit()

def get_gpu_utilization():
    """获取GPU利用率"""
    device_count = pynvml.nvmlDeviceGetCount()
    utilizations = []

    for i in range(device_count):
        handle = pynvml.nvmlDeviceGetHandleByIndex(i)
        util = pynvml.nvmlDeviceGetUtilizationRates(handle)
        memory = pynvml.nvmlDeviceGetMemoryInfo(handle)

        utilizations.append({
            'gpu_id': i,
            'gpu_util': util.gpu,  # GPU利用率 %
            'memory_util': util.memory,  # 内存控制器利用率 %
            'memory_used': memory.used / 1024**2,  # MB
            'memory_total': memory.total / 1024**2,  # MB
        })

    return utilizations

# 监控示例
import time
while True:
    stats = get_gpu_utilization()
    for stat in stats:
        print(f"GPU {stat['gpu_id']}: "
              f"Util={stat['gpu_util']}%, "
              f"Mem={stat['memory_used']:.0f}/{stat['memory_total']:.0f}MB")
    time.sleep(1)
```

## 10. 性能数据

### 10.1 GPU架构性能对比

| GPU | 架构 | SMs | CUDA核心 | 显存 | 显存带宽 | FP32 TFLOPS |
|-----|------|-----|----------|------|----------|-------------|
| RTX 4090 | Ada | 128 | 16384 | 24GB | 1008 GB/s | 82.6 |
| A100 | Ampere | 108 | 6912 | 80GB | 2039 GB/s | 19.5 |
| H100 | Hopper | 132 | 16896 | 80GB | 3350 GB/s | 67.0 |
| MI300X | CDNA3 | 304 | 19456 | 192GB | 5300 GB/s | 130.0 |

### 10.2 内存带宽效率

| 访问模式 | 效率 | 说明 |
|----------|------|------|
| 对齐合并 | 90-100% | 理想情况 |
| 跨步访问 | 50-80% | 需调整线程映射 |
| 随机访问 | 10-30% | 严重性能损失 |
| 银行冲突 | 下降50%+ | 共享内存问题 |

### 10.3 调度延迟

| 操作 | 延迟 |
|------|------|
| 寄存器访问 | 1 cycle |
| 共享内存（无冲突） | 20-30 cycles |
| 共享内存（有冲突） | 20-30 * n cycles |
| L1缓存命中 | 20-40 cycles |
| L2缓存命中 | 100-200 cycles |
| 全局内存 | 300-500 cycles |
| 内核启动 | 5-50 μs |
| 页锁定内存传输 | 5-10 GB/s |

## 11. 参考链接

- [AI加速器调度](./AI加速器调度.md)
- [GPU任务调度](../../Composed/schedule_formal_view/16_GPU与加速器调度/16.1_GPU任务调度.md)
- [异构计算调度](../../Composed/schedule_formal_view/16_GPU与加速器调度/16.4_异构计算调度.md)
- [CUDA编程指南](https://docs.nvidia.com/cuda/cuda-c-programming-guide/)

---

_本文档已完成功能性填充，包含完整的理论知识、形式化定义、代码示例和性能数据。_
