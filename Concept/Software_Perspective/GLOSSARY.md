# Software Perspective - 术语表

> **文档版本**: v1.0.0  
> **最后更新**: 2025-10-27  
> **文档规模**: 341行 | 软件透视核心术语  
> **阅读建议**: 本文提供软件透视所有核心概念的快速查询

---

## 目录 | Table of Contents

- [Software Perspective - 术语表](#software-perspective---术语表)
  - [目录 | Table of Contents](#目录--table-of-contents)
  - [A](#a)
  - [B](#b)
  - [C](#c)
  - [D](#d)
  - [E](#e)
  - [F](#f)
  - [G](#g)
  - [H](#h)
  - [I](#i)
  - [J-L](#j-l)
  - [M-O](#m-o)
  - [P-R](#p-r)
  - [S-Z](#s-z)

---

## A

### Architecture Sink
**架构下沉**  
软件系统中重复出现的复杂性，从应用层逐步转移到平台层、运行时层、最终固化到硬件层的持续过程。

**相关**：[2.1 架构下沉原理](./02_Architecture_Sink/02.1_Sink_Principles_Drivers.md)

### Accidental Complexity
**偶然复杂度**  
由技术实现引入的复杂度，理论上可以通过更好的抽象消除。

**相关**：[1.3 复杂度守恒](./01_Foundational_Theory/01.3_Software_Complexity_Conservation.md)

### ArgoCD
GitOps 工具，持续监听 Git 仓库变化并自动同步到 Kubernetes 集群。

**相关**：[4.4 GitOps 声明式修复](./04_Self_Healing_Systems/04.4_GitOps_Declarative_Remediation.md)

## C

### Cognitive Load
**认知负载**  
开发者在理解和操作系统时需要保持在工作记忆中的信息量。

**相关**：[8.5 认知负载管理](./08_Platform_Engineering/08.5_Cognitive_Load_Management.md)

### Complexity Conservation
**复杂度守恒**  
在软件系统中，总复杂度（本质复杂度 + 偶然复杂度）是守恒的，不会凭空消失，只会转移。

**公式**：`Total_Complexity = Essential + Accidental = Constant`

**相关**：[1.3 复杂度守恒定律](./01_Foundational_Theory/01.3_Software_Complexity_Conservation.md)

### Control Loop
**控制循环**  
持续比较"期望状态"与"实际状态"，自动调整以消除差异的反馈机制。

**相关**：[4.1 自愈架构原理](./04_Self_Healing_Systems/04.1_Self_Healing_Architecture.md)

## D

### Declarative
**声明式**  
描述"要什么"（What）而非"怎么做"（How）的编程范式。

**示例**：SQL, Kubernetes YAML, Terraform

**相关**：[1.5 声明式与命令式](./01_Foundational_Theory/01.5_Declarative_Imperative_Paradigms.md)

### DORA Metrics
DevOps Research and Assessment 定义的四个关键指标：
1. 部署频率（Deployment Frequency）
2. 变更前置时间（Lead Time for Changes）
3. MTTR（平均修复时间）
4. 变更失败率（Change Failure Rate）

## E

### Essential Complexity
**本质复杂度**  
问题本身固有的复杂度，无法消除。

**示例**：业务规则的复杂性、领域模型的固有关系

**相关**：[1.3 复杂度守恒](./01_Foundational_Theory/01.3_Software_Complexity_Conservation.md)

## F

### Formal Layer
**形式层**  
可计算的规则世界，包括代码、类型系统、逻辑门等可机械执行的符号系统。

**相关**：[1.1 语义形式对偶](./01_Foundational_Theory/01.1_Semantic_Formal_Duality.md)

## G

### GitOps
以 Git 为唯一真实源（Single Source of Truth）的运维模式，所有变更通过 Git 提交触发。

**核心原则**：
1. Git 是唯一真实源
2. 声明式配置
3. 自动同步
4. 持续调和

**相关**：[4.4 GitOps 声明式修复](./04_Self_Healing_Systems/04.4_GitOps_Declarative_Remediation.md)

### Golden Path
**黄金路径**  
为常见场景预设的、阻力最小的开发路径，覆盖 80% 的需求。

**相关**：[8.3 黄金路径](./08_Platform_Engineering/08.3_Golden_Path.md)

## H

### HPA (Horizontal Pod Autoscaler)
Kubernetes 水平 Pod 自动扩缩容器，根据 CPU/内存/自定义指标自动调整副本数。

**相关**：[5.3 HPA 与 KEDA](./05_Configuration_Scaling/05.3_HPA_KEDA.md)

## I

### Imperative
**命令式**  
描述"怎么做"（How），逐步指定执行步骤的编程范式。

**示例**：Shell 脚本、C 语言、手工 kubectl 命令

**相关**：[1.5 声明式与命令式](./01_Foundational_Theory/01.5_Declarative_Imperative_Paradigms.md)

### Internal Developer Platform (IDP)
**内部开发者平台**  
企业内部构建的平台，为开发者提供自助服务能力，降低认知负载。

**相关**：[8.2 内部开发者平台](./08_Platform_Engineering/08.2_Internal_Developer_Platform.md)

### Intent-Driven
**意图驱动**  
用户表达意图（"我要高可用"），系统自动生成具体实现的编程范式。

**相关**：[10.1 意图驱动编程](./10_Future_Directions/10.1_Intent_Driven_Programming.md)

## K

### KEDA (Kubernetes Event-Driven Autoscaler)
基于事件源（Kafka、SQS、Prometheus 等）的 Kubernetes 自动扩缩容器。

**相关**：[5.3 HPA 与 KEDA](./05_Configuration_Scaling/05.3_HPA_KEDA.md)

## L

### Leaky Abstraction
**抽象泄漏**  
抽象层无法完全隐藏底层细节，导致用户被迫理解底层实现的现象。

**示例**：GC 暂停、网络延迟、K8s 资源配额

**相关**：[1.2 计算抽象层次](./01_Foundational_Theory/01.2_Computational_Abstraction_Layers.md)

## M

### MTTR (Mean Time To Repair/Recovery)
**平均修复/恢复时间**  
从故障发生到系统恢复的平均时间。

**目标值**：
- 传统运维：30+ 分钟
- 平台化：5-10 分钟
- 自愈系统：< 2 分钟

## O

### OPA (Open Policy Agent)
策略引擎，使用 Rego 语言定义策略，实现 Policy-as-Code。

**用途**：准入控制、自愈策略、合规检查

**相关**：[4.3 OPA 策略引擎](./04_Self_Healing_Systems/04.3_OPA_Policy_Engine.md)

### OTLP (OpenTelemetry Protocol)
OpenTelemetry 项目定义的统一可观测性协议，支持 Metrics、Traces、Logs 三支柱。

**相关**：[4.2 OTLP 可观测性](./04_Self_Healing_Systems/04.2_OTLP_Observability.md)

### Observability
**可观测性**  
通过系统外部输出（指标、日志、追踪）推断系统内部状态的能力。

**三支柱**：Metrics, Traces, Logs

**相关**：[6.1 三支柱可观测性](./06_Observability_Governance/06.1_Three_Pillars_Observability.md)

## P

### Platform Engineering
**平台工程**  
构建和维护内部开发者平台的工程实践，目标是降低认知负载、提升开发者体验。

**相关**：[8.1 平台工程定义](./08_Platform_Engineering/08.1_Platform_Engineering_Definition.md)

### Policy-as-Code
**策略即代码**  
将治理策略、安全规则、合规要求以代码形式表达，可版本化、测试、自动执行。

**工具**：OPA、Kyverno、Gatekeeper

**相关**：[6.3 策略即代码](./06_Observability_Governance/06.3_Policy_as_Code.md)

## R

### Rego
OPA 使用的策略语言，声明式、逻辑式编程语言。

**示例**：
```rego
allow {
    input.user.role == "admin"
}
```

## S

### Semantic Gap
**语义缺口**  
意义世界中尚未被形式化、自动化的部分。

**示例**：
- 市场不确定性（2020 年代缺口）
- AI 伦理（未来缺口）

**相关**：[3.2 语义缺口识别](./03_Semantic_Formal_Duality/03.2_Semantic_Gap_Formalization.md)

### Semantic Layer
**语义层**  
人类自创的意义世界，包括商业价值、用户故事、领域概念等。

**特征**：可被解释、争论、再叙事

**相关**：[1.1 语义形式对偶](./01_Foundational_Theory/01.1_Semantic_Formal_Duality.md)

### Semantic-Formal Duality
**语义-形式对偶**  
意义世界与规则世界之间的永恒张力与相互转化。

**核心机制**：形式化 → 下沉 → 缺口重生

**相关**：[1.1 语义形式对偶](./01_Foundational_Theory/01.1_Semantic_Formal_Duality.md)

### Self-Healing
**自愈**  
系统自动检测异常、诊断根因、执行修复并验证效果的闭环能力。

**相关**：[4.1 自愈架构原理](./04_Self_Healing_Systems/04.1_Self_Healing_Architecture.md)

### Service Mesh
服务网格，为微服务提供服务发现、负载均衡、加密、可观测性等能力的基础设施层。

**代表**：Istio, Linkerd

**相关**：[9.3 Service Mesh](./09_Cloud_Native_Patterns/09.3_Service_Mesh.md)

### Sink Stage Model
**下沉阶段模型**  
描述架构下沉的五个层级（L1-L5）：运行时下沉 → 策略下沉 → 智能下沉 → 芯片级下沉 → 零代码态。

**相关**：[2.5 下沉阶段模型](./02_Architecture_Sink/02.5_Sink_Stage_Model.md)

## T

### Three Pillars of Observability
**可观测性三支柱**
1. **Metrics**：时间序列数据（CPU、内存、QPS）
2. **Traces**：分布式请求追踪
3. **Logs**：事件详细记录

**相关**：[6.1 三支柱可观测性](./06_Observability_Governance/06.1_Three_Pillars_Observability.md)

## 缩写对照

| 缩写 | 全称 | 中文 |
|-----|------|------|
| **CA** | Cluster Autoscaler | 集群自动扩缩容器 |
| **CCA** | Confidential Compute Architecture | 机密计算架构 |
| **CI/CD** | Continuous Integration/Continuous Deployment | 持续集成/持续部署 |
| **DDD** | Domain-Driven Design | 领域驱动设计 |
| **DORA** | DevOps Research and Assessment | DevOps 研究与评估 |
| **GC** | Garbage Collection | 垃圾回收 |
| **HPA** | Horizontal Pod Autoscaler | 水平 Pod 自动扩缩容器 |
| **IDP** | Internal Developer Platform | 内部开发者平台 |
| **ISA** | Instruction Set Architecture | 指令集架构 |
| **KEDA** | Kubernetes Event-Driven Autoscaler | Kubernetes 事件驱动自动扩缩容器 |
| **MTTR** | Mean Time To Repair/Recovery | 平均修复/恢复时间 |
| **OPA** | Open Policy Agent | 开放策略代理 |
| **OTLP** | OpenTelemetry Protocol | OpenTelemetry 协议 |
| **SLO** | Service Level Objective | 服务等级目标 |
| **SRE** | Site Reliability Engineering | 站点可靠性工程 |
| **VPA** | Vertical Pod Autoscaler | 垂直 Pod 自动扩缩容器 |

## 框架与工具

### 可观测性
- **Prometheus**：指标采集与告警
- **Grafana**：可视化
- **Jaeger/Tempo**：分布式追踪
- **Loki**：日志聚合
- **OpenTelemetry**：统一协议

### GitOps
- **ArgoCD**：声明式 CD
- **Flux**：GitOps operator
- **Helm**：K8s 包管理

### 策略治理
- **OPA**：策略引擎
- **Gatekeeper**：K8s 准入控制器
- **Kyverno**：K8s 原生策略引擎

### 自动扩缩容
- **HPA**：K8s 内置
- **KEDA**：事件驱动扩缩容
- **VPA**：垂直扩缩容
- **Cluster Autoscaler**：节点扩缩容

## 概念层次

```
意图层 (Intent)
    ↓
语义层 (Semantic)
    ↓
领域层 (Domain)
    ↓
应用层 (Application)
    ↓
平台层 (Platform)
    ↓
运行时层 (Runtime)
    ↓
操作系统层 (OS)
    ↓
指令集层 (ISA)
    ↓
硅片层 (Silicon)
```

## 延伸阅读

- [完整索引](./00_Master_Index.md)
- [快速参考](./QUICK_REFERENCE.md)
- [常见问题](./FAQ.md)
- [学习路径](./LEARNING_PATHS.md)

---

**导航**：[返回主页](./README.md) | [快速参考 →](./QUICK_REFERENCE.md)

