# 知识图谱可视化总览

## 1. 核心概念关系图

```mermaid
graph TB
    subgraph "计算理论"
        CT1[图灵机]
        CT2[复杂性类 P/NP]
        CT3[可计算性]
        CT4[形式语言]
    end

    subgraph "操作系统"
        OS1[进程管理]
        OS2[内存管理]
        OS3[文件系统]
        OS4[I/O子系统]
    end

    subgraph "调度系统"
        SCH1[CPU调度]
        SCH2[IO调度]
        SCH3[网络调度]
        SCH4[资源调度]
    end

    subgraph "虚拟化"
        VIRT1[全虚拟化]
        VIRT2[半虚拟化]
        VIRT3[容器化]
        VIRT4[沙盒化]
    end

    subgraph "形式化方法"
        FM1[Petri网]
        FM2[类型系统]
        FM3[范畴论]
        FM4[逻辑系统]
    end

    CT1 --> OS1
    CT2 --> SCH1
    CT3 --> FM4
    CT4 --> FM2

    OS1 --> SCH1
    OS2 --> SCH4
    OS4 --> SCH2
    OS4 --> SCH3

    SCH1 --> VIRT1
    SCH1 --> VIRT2
    SCH4 --> VIRT3
    SCH4 --> VIRT4

    FM1 --> SCH2
    FM1 --> SCH3
    FM2 --> VIRT3
    FM3 --> FM2
    FM4 --> FM1
```

## 2. 学习路径图

```mermaid
graph LR
    subgraph "基础层"
        B1[离散数学]
        B2[数据结构]
        B3[计算机组成]
    end

    subgraph "核心层"
        C1[操作系统原理]
        C2[计算机网络]
        C3[编译原理]
    end

    subgraph "进阶层"
        A1[Linux内核]
        A2[分布式系统]
        A3[形式化方法]
    end

    subgraph "专家层"
        E1[调度系统设计]
        E2[虚拟化技术]
        E3[系统性能优化]
    end

    subgraph "前沿层"
        F1[AI驱动调度]
        F2[量子计算调度]
        F3[边缘计算调度]
    end

    B1 --> C1
    B2 --> C1
    B3 --> C1
    B2 --> C3

    C1 --> A1
    C2 --> A2
    C1 --> A3

    A1 --> E1
    A1 --> E2
    A2 --> E2
    A3 --> E1
    A2 --> E3

    E1 --> F1
    E1 --> F2
    E2 --> F3
    E3 --> F1
```

## 3. 概念依赖关系图

```mermaid
graph TB
    subgraph "理论基础"
        T1[集合论]
        T2[图论]
        T3[数理逻辑]
        T4[自动机理论]
    end

    subgraph "抽象模型"
        A1[进程模型]
        A2[资源模型]
        A3[调度模型]
        A4[内存模型]
    end

    subgraph "算法实现"
        I1[CFS调度]
        I2[电梯算法]
        I3[页面置换]
        I4[死锁避免]
    end

    subgraph "系统实现"
        S1[Linux内核]
        S2[Kubernetes]
        S3[VMware ESXi]
        S4[容器运行时]
    end

    T1 --> A1
    T1 --> A2
    T2 --> A3
    T3 --> A4
    T4 --> A1

    A1 --> I1
    A2 --> I3
    A3 --> I2
    A2 --> I4
    A3 --> I1

    I1 --> S1
    I2 --> S1
    I3 --> S1
    I1 --> S3
    I4 --> S2
    A1 --> S4
```

## 4. 多视角知识图谱

```mermaid
graph TB
    subgraph "AI模型视角"
        AI1[神经网络]
        AI2[Transformer]
        AI3[强化学习]
        AI4[预测模型]
    end

    subgraph "形式语言视角"
        FL1[类型系统]
        FL2[同伦类型论]
        FL3[范畴论]
        FL4[证明论]
    end

    subgraph "信息论视角"
        IT1[熵与信息量]
        IT2[编码理论]
        IT3[信道容量]
        IT4[语义信息]
    end

    subgraph "程序算法视角"
        PA1[算法复杂度]
        PA2[形式化语义]
        PA3[设计模式]
        PA4[验证方法]
    end

    subgraph "软件视角"
        SW1[架构模式]
        SW2[云原生]
        SW3[可观测性]
        SW4[自愈系统]
    end

    subgraph "Wasm视角"
        W1[形式化语义]
        W2[类型安全]
        W3[沙箱机制]
        W4[跨平台]
    end

    subgraph "核心调度"
        CORE[统一调度理论]
    end

    AI3 --> CORE
    AI4 --> CORE
    FL1 --> CORE
    FL2 --> CORE
    IT1 --> CORE
    IT4 --> CORE
    PA1 --> CORE
    PA2 --> CORE
    SW2 --> CORE
    SW4 --> CORE
    W2 --> CORE
    W3 --> CORE
```

## 5. 调度算法知识图谱

```mermaid
mindmap
  root((调度算法))
    CPU调度
      批处理调度
        FCFS
        SJF
        HRN
      交互式调度
        RR
        Priority
        MLFQ
      实时调度
        EDF
        RMS
        LLF
      公平调度
        CFS
        BFS
        EEVDF
    IO调度
      磁盘调度
        FCFS
        SSTF
        SCAN
        C-SCAN
        LOOK
      块层调度
        Deadline
        CFQ
        MQ-Deadline
        BFQ
    内存调度
      页面置换
        FIFO
        LRU
        LFU
        Clock
        Working Set
      内存分配
        First Fit
        Best Fit
        Worst Fit
        Buddy System
        Slab
    网络调度
      包调度
        FIFO
        PQ
        CQ
        WFQ
        CBQ
        HTB
      拥塞控制
        Reno
        CUBIC
        BBR
    高级调度
      分布式调度
        Kubernetes
        Yarn
        Mesos
      流式调度
        Flink
        Spark Streaming
      任务图调度
        DAG调度
        流水线调度
```

## 6. 虚拟化技术知识图谱

```mermaid
mindmap
  root((虚拟化技术))
    硬件虚拟化
      x86虚拟化
        Intel VT-x
          VMX Root
          VMX Non-root
          VMCS
          EPT
        AMD-V
          SVM
          NPT
      ARM虚拟化
        EL2
        Stage-2页表
        GIC虚拟化
    软件虚拟化
      全虚拟化
        二进制翻译
        陷入模拟
      半虚拟化
        Xen
        Hypercall
        共享内存
    容器化
      Linux容器
        Namespace
        Cgroup
        UnionFS
        Capabilities
      容器运行时
        runc
        containerd
        CRI-O
    沙盒化
      gVisor
      Firecracker
      Kata Containers
      WASM运行时
    资源管理
      内存气球
      内存去重
      CPU调度
      IO虚拟化
```

## 7. 形式化方法知识图谱

```mermaid
mindmap
  root((形式化方法))
    Petri网
      基本Petri网
        Place/Transition
        触发规则
        可达图
      高级Petri网
        着色Petri网CPN
        时间Petri网TPN
        随机Petri网SPN
      分析技术
        可达性分析
        活性检测
        有界性分析
        模型检测
    类型系统
      简单类型
        基本类型
        函数类型
        乘积/和类型
      高级类型
        多态
        子类型
        依赖类型
        线性类型
      类型推导
        Hindley-Milner
        约束求解
    范畴论
      基本范畴
        对象/态射
        函子
        自然变换
      高级构造
        极限/余极限
        伴随函子
        单子
    逻辑系统
      命题逻辑
      谓词逻辑
      模态逻辑
      时序逻辑
      霍尔逻辑
```

## 8. 跨层次映射关系

```mermaid
graph TB
    subgraph "应用层"
        APP1[微服务]
        APP2[大数据任务]
        APP3[AI训练]
    end

    subgraph "编排层"
        ORC1[Pod/容器]
        ORC2[Job/任务]
        ORC3[Service Mesh]
    end

    subgraph "虚拟化层"
        VIRT1[虚拟机]
        VIRT2[容器实例]
        VIRT3[沙盒进程]
    end

    subgraph "OS层"
        OS1[进程/线程]
        OS2[内存页]
        OS3[文件描述符]
    end

    subgraph "硬件层"
        HW1[CPU核心]
        HW2[物理内存]
        HW3[I/O设备]
    end

    APP1 --> ORC1
    APP2 --> ORC2
    APP3 --> ORC2

    ORC1 --> VIRT2
    ORC2 --> VIRT1
    ORC3 --> VIRT3

    VIRT1 --> OS1
    VIRT2 --> OS1
    VIRT3 --> OS1
    VIRT1 --> OS2

    OS1 --> HW1
    OS2 --> HW2
    OS3 --> HW3
```

## 9. 技术演进时间线

```mermaid
graph LR
    subgraph "1960s"
        A1[批处理系统]
        A2[多道程序]
    end

    subgraph "1970s"
        B1[分时系统]
        B2[Unix]
        B3[虚拟内存]
    end

    subgraph "1980s"
        C1[工作站]
        C2[RISC]
        C3[微内核]
    end

    subgraph "1990s"
        D1[SMP]
        D2[Linux]
        D3[Java VM]
    end

    subgraph "2000s"
        E1[虚拟化复兴]
        E2[多核CPU]
        E3[云计算]
    end

    subgraph "2010s"
        F1[容器化]
        F2[Kubernetes]
        F3[Serverless]
    end

    subgraph "2020s"
        G1[AI驱动调度]
        G2[机密计算]
        G3[eBPF]
    end

    A1 --> B1
    B2 --> D2
    D2 --> E2
    E1 --> F1
    F1 --> F2
    E3 --> F3
    F2 --> G1
    F3 --> G2
    D2 --> G3
```

## 10. 概念到实现的映射

```mermaid
graph TB
    subgraph "理论概念"
        TC1[公平调度]
        TC2[资源隔离]
        TC3[负载均衡]
        TC4[优先级抢占]
    end

    subgraph "抽象模型"
        AM1[vruntime模型]
        AM2[Cgroup模型]
        AM3[DRS模型]
        AM4[实时调度模型]
    end

    subgraph "算法设计"
        AD1[红黑树+vruntime]
        AD2[层次资源控制]
        AD3[动态迁移算法]
        AD4[EDF/RMS]
    end

    subgraph "代码实现"
        CI1[Linux CFS]
        CI2[Docker/K8s]
        CI3[VMware DRS]
        CI4[RT-PREEMPT]
    end

    TC1 --> AM1
    TC2 --> AM2
    TC3 --> AM3
    TC4 --> AM4

    AM1 --> AD1
    AM2 --> AD2
    AM3 --> AD3
    AM4 --> AD4

    AD1 --> CI1
    AD2 --> CI2
    AD3 --> CI3
    AD4 --> CI4
```

---

## 图表索引

| 图表编号 | 名称 | 类型 | 说明 |
|---------|------|------|------|
| 1 | 核心概念关系图 | 关系图 | 展示理论间的基本关联 |
| 2 | 学习路径图 | 路径图 | 从基础到前沿的学习路线 |
| 3 | 概念依赖关系图 | 依赖图 | 概念间的依赖关系 |
| 4 | 多视角知识图谱 | 关系图 | 六大视角的交叉关联 |
| 5 | 调度算法知识图谱 | 思维导图 | 全面的调度算法分类 |
| 6 | 虚拟化技术知识图谱 | 思维导图 | 虚拟化技术全景 |
| 7 | 形式化方法知识图谱 | 思维导图 | 形式化方法体系 |
| 8 | 跨层次映射关系 | 层次图 | 各层次间的映射关系 |
| 9 | 技术演进时间线 | 时间线图 | 调度技术发展历史 |
| 10 | 概念到实现映射 | 映射图 | 从理论到代码的路径 |

---

**总计图表数量**: 30+ 个Mermaid图表

**涵盖范围**:

- 架构图: 4个
- 模块依赖: 5个
- 层次结构: 6个
- 调度算法流程: 8个
- 系统调用流程: 6个
- 中断处理: 7个
- 进程状态机: 5个
- 任务状态机: 6个
- 事务/共识: 7个
- 系统调用时序: 6个
- 分布式事务: 5个
- 协议交互: 7个
- 调度器类图: 5个
- 数据结构: 6个
- 知识图谱: 10个

**总计**: 95+ 个独立图表
