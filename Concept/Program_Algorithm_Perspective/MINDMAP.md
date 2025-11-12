# Program-Algorithm-Design Perspective - 思维导图

> 本文档提供整个知识体系的可视化思维导图，帮助理解各概念之间的关系。

---

## 📋 目录

- [Program-Algorithm-Design Perspective - 思维导图](#program-algorithm-design-perspective---思维导图)
  - [📋 目录](#-目录)
  - [1 📊 整体知识体系思维导图](#1--整体知识体系思维导图)
  - [2 🔄 UH-Cost 框架思维导图](#2--uh-cost-框架思维导图)
  - [3 🌲 形式语义知识树](#3--形式语义知识树)
  - [4 🔀 设计模式分类思维导图](#4--设计模式分类思维导图)
  - [5 🧩 复杂度维度思维导图](#5--复杂度维度思维导图)
  - [6 🏗️ 架构模式层次思维导图](#6-️-架构模式层次思维导图)
  - [7 🛠️ 形式验证工具生态思维导图](#7-️-形式验证工具生态思维导图)
  - [8 🔗 跨项目集成思维导图](#8--跨项目集成思维导图)
  - [9 📚 学习路径思维导图](#9--学习路径思维导图)
  - [10 🎯 核心定理关系图](#10--核心定理关系图)
  - [11 📖 文档导航思维导图](#11--文档导航思维导图)
  - [12 🔄 概念演化时间线](#12--概念演化时间线)
  - [13 使用说明](#13-使用说明)
    - [13.1 如何阅读思维导图](#131-如何阅读思维导图)
    - [13.2 思维导图的价值](#132-思维导图的价值)

---

## 1 📊 整体知识体系思维导图

```mermaid
mindmap
  root((编程算法<br/>设计视角))
    [01 形式语义]
      操作语义
        小步语义
        大步语义
        成本语义
      指称语义
        Domain Theory
        不动点定理
        完全抽象
      公理化语义
        Hoare逻辑
        分离逻辑
        WP/SP计算
      类型系统
        依赖类型
        线性类型
        Affine类型
        渐进类型
      语言比较
        Rust
        Python
        Golang

    [02 设计模式]
      GoF模式
        创建型
        结构型
        行为型
      分布式模式
        Saga
        CQRS
        Event Sourcing
      工作流模式
        43种WfMC模式
        Petri网
      并发模式
        Actor
        CSP
        π演算
      架构模式
        分层
        微服务
        事件驱动
      模式验证
        模型检测
        定理证明
        静态分析

    [03 算法复杂度]
      多维复杂度
        Control维度
        Execution维度
        Data维度
      复杂度类
        P/NP/PSPACE
        BPP/RP/ZPP
        NC/P-complete
        BQP
      下界技术
        信息论
        对抗论证
        决策树
        通信复杂度
      并行算法
        Work-Span模型
        PRAM
        Work-Stealing
      外存算法
        DAM模型
        Cache-Oblivious
        I/O复杂度
      形式化规范
        Dafny
        Lean4
        Coq
        Why3

    [04 架构模式]
      架构概览
        五层模型
        ADR
        ATAM
      分层架构
        OSI模型
        N-tier
        六边形架构
      微服务架构
        Service Mesh
        API Gateway
        服务发现
      事件驱动
        Kafka
        Event Sourcing
        CQRS
      跨层验证
        垂直精化
        性质传递
        协同验证

    [05 形式验证]
      定理证明
        Coq
        Lean4
        Isabelle/HOL
      模型检测
        mCRL2
        SPIN
        TLA+
        UPPAAL
      符号执行
        KLEE
        Kani
        Angr
      语义框架
        K-Framework
        Maude
      工业应用
        CompCert
        seL4
        SymCrypt
```

---

## 2 🔄 UH-Cost 框架思维导图

```mermaid
mindmap
  root((UH-Cost<br/>框架))
    [Σ 超图签名]
      节点
        实体
        组件
        服务
      超边
        依赖关系
        数据流
        控制流

    [⟶ 重写规则]
      语法转换
        模式匹配
        规则应用
      语义保持
        行为等价
        性质保持
      成本计算
        多维度
        可组合

    [κ 成本函数]
      Control维度
        时间
        空间
        通信
        随机性
      Execution维度
        能源
        缓存
        I/O
        并行度
      Data维度
        隐私
        完整性
        信息量

    [Φ 正确性谓词]
      安全性
        类型安全
        内存安全
        并发安全
      活性
        无死锁
        最终一致性
        进展性
      性能
        响应时间
        吞吐量
        资源利用
```

---

## 3 🌲 形式语义知识树

```mermaid
graph TD
    A[形式语义] --> B[操作语义]
    A --> C[指称语义]
    A --> D[公理化语义]

    B --> B1[Small-step]
    B --> B2[Big-step]
    B --> B3[Cost Semantics]
    B1 --> B11[状态转换]
    B1 --> B12[单步执行]
    B2 --> B21[求值到值]
    B2 --> B22[大步推导]
    B3 --> B31[资源计量]
    B3 --> B32[多维成本]

    C --> C1[Domain Theory]
    C --> C2[不动点语义]
    C --> C3[完全抽象]
    C1 --> C11[CPO/DCPO]
    C1 --> C12[连续函数]
    C2 --> C21[Kleene定理]
    C2 --> C22[Tarski定理]
    C3 --> C31[语义等价]
    C3 --> C32[充分性]

    D --> D1[Hoare逻辑]
    D --> D2[分离逻辑]
    D --> D3[WP/SP]
    D1 --> D11[前置条件]
    D1 --> D12[后置条件]
    D2 --> D21[堆分离]
    D2 --> D22[所有权]
    D3 --> D31[最弱前置]
    D3 --> D32[最强后置]

    style A fill:#e1f5ff
    style B fill:#fff3e0
    style C fill:#f3e5f5
    style D fill:#e8f5e9
```

---

## 4 🔀 设计模式分类思维导图

```mermaid
graph LR
    A[设计模式] --> B[GoF经典模式]
    A --> C[分布式模式]
    A --> D[工作流模式]
    A --> E[并发模式]
    A --> F[架构模式]

    B --> B1[创建型<br/>5种]
    B --> B2[结构型<br/>7种]
    B --> B3[行为型<br/>11种]

    B1 --> B11[抽象工厂]
    B1 --> B12[单例]
    B1 --> B13[原型]

    B2 --> B21[适配器]
    B2 --> B22[装饰器]
    B2 --> B23[代理]

    B3 --> B31[观察者]
    B3 --> B32[策略]
    B3 --> B33[命令]

    C --> C1[Saga]
    C --> C2[CQRS]
    C --> C3[Event Sourcing]

    D --> D1[控制流<br/>20+种]
    D --> D2[数据流<br/>10+种]
    D --> D3[资源<br/>10+种]

    E --> E1[Actor模型]
    E --> E2[CSP]
    E --> E3[π演算]
    E --> E4[共享内存]

    F --> F1[分层]
    F --> F2[管道过滤器]
    F --> F3[微服务]
    F --> F4[事件驱动]

    style A fill:#42a5f5
    style B fill:#66bb6a
    style C fill:#ffa726
    style D fill:#ab47bc
    style E fill:#ef5350
    style F fill:#26c6da
```

---

## 5 🧩 复杂度维度思维导图

```mermaid
mindmap
  root((算法<br/>复杂度))
    [Control 维度]
      时间复杂度
        最坏情况
        平均情况
        摊还分析
      空间复杂度
        辅助空间
        原地算法
      通信复杂度
        轮数
        消息量
      随机复杂度
        期望时间
        高概率界

    [Execution 维度]
      能源复杂度
        CPU能耗
        内存能耗
        通信能耗
      缓存复杂度
        缓存命中率
        缓存缺失
      I/O 复杂度
        磁盘访问
        块传输
      并行复杂度
        Work
        Span
        并行度

    [Data 维度]
      隐私复杂度
        差分隐私
        信息泄露
      数据完整性
        验证成本
        恢复成本
      信息复杂度
        Kolmogorov
        熵
```

---

## 6 🏗️ 架构模式层次思维导图

```mermaid
graph TB
    subgraph 五层架构模型
        L5[L5 业务层<br/>Business Layer]
        L4[L4 企业服务层<br/>Enterprise Layer]
        L3[L3 信息层<br/>Information Layer]
        L2[L2 软件层<br/>Software Layer]
        L1[L1 硬件层<br/>Hardware Layer]

        L5 --> L4
        L4 --> L3
        L3 --> L2
        L2 --> L1
    end

    L5 -.-> P1[平台经济<br/>订阅模式]
    L4 -.-> P2[微服务<br/>API Gateway]
    L3 -.-> P3[Data Mesh<br/>Lakehouse]
    L2 -.-> P4[分层架构<br/>CQRS]
    L1 -.-> P5[NoC<br/>异构计算]

    subgraph 跨层验证
        V1[垂直精化] -.-> L5
        V1 -.-> L4
        V1 -.-> L3
        V1 -.-> L2
        V1 -.-> L1

        V2[性质传递] -.-> L5
        V2 -.-> L1
    end

    style L5 fill:#e3f2fd
    style L4 fill:#f3e5f5
    style L3 fill:#fff3e0
    style L2 fill:#e8f5e9
    style L1 fill:#fce4ec
```

---

## 7 🛠️ 形式验证工具生态思维导图

```mermaid
graph LR
    A[形式验证工具] --> B[定理证明]
    A --> C[模型检测]
    A --> D[符号执行]
    A --> E[语义框架]

    B --> B1[Coq<br/>交互式]
    B --> B2[Lean4<br/>依赖类型]
    B --> B3[Isabelle/HOL<br/>高阶逻辑]
    B --> B4[Dafny<br/>自动化]

    C --> C1[mCRL2<br/>进程代数]
    C --> C2[SPIN<br/>Promela]
    C --> C3[TLA+<br/>时态逻辑]
    C --> C4[UPPAAL<br/>时间自动机]

    D --> D1[KLEE<br/>LLVM]
    D --> D2[Kani<br/>Rust]
    D --> D3[Angr<br/>二进制]

    E --> E1[K-Framework<br/>重写逻辑]
    E --> E2[Maude<br/>等式重写]

    B1 -.->|验证| I1[CompCert]
    B3 -.->|验证| I2[seL4]
    B4 -.->|验证| I3[SymCrypt]

    style B1 fill:#81c784
    style B2 fill:#64b5f6
    style B3 fill:#ffb74d
    style B4 fill:#ba68c8

    style I1 fill:#ffd54f
    style I2 fill:#ffd54f
    style I3 fill:#ffd54f
```

---

## 8 🔗 跨项目集成思维导图

```mermaid
graph TD
    PA[Program-Algorithm<br/>Perspective]

    FL[FormalLanguage<br/>Perspective]
    AI[AI_model<br/>Perspective]
    IT[Information_Theory<br/>Perspective]
    SW[Software<br/>Perspective]

    PA -->|形式化语义| FL
    PA -->|类型系统| FL

    PA -->|算法验证| AI
    PA -->|正确性证明| AI

    PA -->|复杂度下界| IT
    PA -->|通信复杂度| IT

    PA -->|架构模式| SW
    PA -->|自愈系统| SW

    FL -->|语义基础| PA
    IT -->|成本度量| PA
    SW -->|工程实践| PA
    AI -->|计算模型| PA

    style PA fill:#42a5f5
    style FL fill:#66bb6a
    style AI fill:#ef5350
    style IT fill:#ffa726
    style SW fill:#ab47bc
```

---

## 9 📚 学习路径思维导图

```mermaid
graph LR
    START([开始学习])

    PATH1[理论路径<br/>研究生]
    PATH2[工程路径<br/>工业界]
    PATH3[全栈路径<br/>开发者]

    START --> PATH1
    START --> PATH2
    START --> PATH3

    PATH1 --> T1[形式语义<br/>Ch1]
    T1 --> T2[算法复杂度<br/>Ch3]
    T2 --> T3[形式验证<br/>Ch5]
    T3 --> T4[设计模式<br/>Ch2]
    T4 --> T5[架构模式<br/>Ch4]

    PATH2 --> E1[设计模式<br/>Ch2]
    E1 --> E2[架构模式<br/>Ch4]
    E2 --> E3[工业应用<br/>Ch5.5]
    E3 --> E4[复杂度实战<br/>Ch3]
    E4 --> E5[语言比较<br/>Ch1.5]

    PATH3 --> F1[语言比较<br/>Ch1.5]
    F1 --> F2[分布式模式<br/>Ch2.2]
    F2 --> F3[微服务<br/>Ch4.2]
    F3 --> F4[事件驱动<br/>Ch4.3]
    F4 --> F5[工业应用<br/>Ch5.5]

    T5 --> END([完成])
    E5 --> END
    F5 --> END

    style START fill:#4caf50
    style END fill:#f44336
    style PATH1 fill:#2196f3
    style PATH2 fill:#ff9800
    style PATH3 fill:#9c27b0
```

---

## 10 🎯 核心定理关系图

```mermaid
graph TD
    T1[Template-U<br/>模板通用定理] --> T2[六轴归一定理<br/>UH-Algorithm]
    T2 --> T3[跨层传播定理<br/>Chain-V1]

    T1 -.-> APP1[设计模式<br/>形式化]
    T2 -.-> APP2[复杂度<br/>统一分析]
    T3 -.-> APP3[架构<br/>端到端验证]

    PROOF1[Coq证明] -.-> T1
    PROOF2[Lean4证明] -.-> T2
    PROOF3[TLA+证明] -.-> T3

    style T1 fill:#ffeb3b
    style T2 fill:#ffeb3b
    style T3 fill:#ffeb3b
    style APP1 fill:#4caf50
    style APP2 fill:#4caf50
    style APP3 fill:#4caf50
```

---

## 11 📖 文档导航思维导图

```mermaid
graph TD
    INDEX[00_Master_Index.md<br/>主索引]

    README[README.md<br/>项目总览]
    GLOSSARY[GLOSSARY.md<br/>术语表]
    QUICK[QUICK_REFERENCE.md<br/>快速参考]

    CH1[01_Formal_Semantics/<br/>形式语义]
    CH2[02_Design_Patterns/<br/>设计模式]
    CH3[03_Algorithm_Complexity/<br/>算法复杂度]
    CH4[04_Architecture_Patterns/<br/>架构模式]
    CH5[05_Formal_Verification/<br/>形式验证]

    INDEX --> README
    INDEX --> GLOSSARY
    INDEX --> QUICK

    INDEX --> CH1
    INDEX --> CH2
    INDEX --> CH3
    INDEX --> CH4
    INDEX --> CH5

    CH1 --> F1[01.1 操作语义]
    CH1 --> F2[01.2 指称语义]
    CH1 --> F3[01.3 公理语义]
    CH1 --> F4[01.4 类型系统]
    CH1 --> F5[01.5 语言比较]

    CH2 --> P1[02.1 GoF]
    CH2 --> P2[02.2 分布式]
    CH2 --> P3[02.3 工作流]
    CH2 --> P4[02.4 并发]
    CH2 --> P5[02.5 架构]
    CH2 --> P6[02.6 验证]

    CH3 --> A1[03.1 多维复杂度]
    CH3 --> A2[03.2 复杂度类]
    CH3 --> A3[03.3 下界技术]
    CH3 --> A4[03.4 并行算法]
    CH3 --> A5[03.5 外存算法]
    CH3 --> A6[03.6 形式规范]

    CH4 --> R1[04.0 概览]
    CH4 --> R2[04.1 分层]
    CH4 --> R3[04.2 微服务]
    CH4 --> R4[04.3 事件驱动]
    CH4 --> R5[04.4 跨层验证]

    CH5 --> V1[05.1 Coq]
    CH5 --> V2[05.2 模型检测]
    CH5 --> V3[05.3 K-Framework]
    CH5 --> V4[05.4 符号执行]
    CH5 --> V5[05.5 工业应用]

    style INDEX fill:#e1f5ff
    style CH1 fill:#fff3e0
    style CH2 fill:#f3e5f5
    style CH3 fill:#e8f5e9
    style CH4 fill:#fce4ec
    style CH5 fill:#fff9c4
```

---

## 12 🔄 概念演化时间线

```mermaid
timeline
    title 形式化方法发展史

    1960s : Hoare逻辑诞生
          : Floyd-Hoare验证

    1970s : Scott域理论
          : Petri网理论

    1980s : CCS/CSP进程代数
          : Temporal逻辑
          : ML类型系统

    1990s : Coq定理证明器
          : GoF设计模式
          : Java与面向对象

    2000s : Separation逻辑
          : TLA+规范语言
          : 依赖类型

    2010s : Rust与所有权
          : K-Framework
          : Lean定理证明器
          : 微服务架构

    2020s : Lean4发布
          : 形式验证工业化
          : CompCert/seL4
          : AI辅助验证
```

---

## 13 使用说明

### 13.1 如何阅读思维导图

1. **整体到局部**：先看整体知识体系图，理解五大章节关系
2. **按需深入**：根据学习目标选择具体章节的详细图
3. **关注连接**：注意图中的箭头和虚线，表示概念间的依赖关系
4. **跨图参照**：同一概念可能出现在多个图中，建立多角度理解

### 13.2 思维导图的价值

- **快速定位**：迅速找到感兴趣的主题
- **理解结构**：把握知识的层次和组织
- **发现关联**：看到不同概念之间的联系
- **指导学习**：规划自己的学习路径

---

**版本**: v1.0
**创建日期**: 2025-10-29
**维护者**: Program-Algorithm-Design Perspective Team
