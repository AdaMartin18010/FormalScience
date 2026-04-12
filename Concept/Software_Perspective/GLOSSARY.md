- --
topic: "Software Perspective - 术语表"
dependencies: []
status: "review"
author: "FormalScience Project"
date: "2026-04-12"
version: "1.0.0"
tags: ["类型", "形式化", "计算", "逻辑", "集合"]
category: "reference"
priority: "medium"
- --

# Software Perspective - 术语表

> **文档版本**: v1.0.0
> **最后更新**: 2025-10-27
> **文档规模**: 341行 | 软件透视核心术语
> **阅读建议**: 本文提供软件透视所有核心概念的快速查询

- --

## 1. 📋 目录 {#-目录}

- [Software Perspective - 术语表](#software-perspective---术语表)
  - [1. 📋 目录 {#-目录}](#1--目录--目录)
  - [1. A {#a}](#1-a-a)
    - [1 1 Architecture Sink {#1-architecture-sink}](#1-1-architecture-sink-1-architecture-sink)
    - [1 2 Accidental Complexity {#2-accidental-complexity}](#1-2-accidental-complexity-2-accidental-complexity)
    - [1 3 ArgoCD {#3-argocd}](#1-3-argocd-3-argocd)
  - [2. C {#c}](#2-c-c)
    - [2 1 Cognitive Load {#1-cognitive-load}](#2-1-cognitive-load-1-cognitive-load)
    - [2 2 Complexity Conservation {#2-complexity-conservation}](#2-2-complexity-conservation-2-complexity-conservation)
    - [2 3 Control Loop {#3-control-loop}](#2-3-control-loop-3-control-loop)
  - [3. D {#d}](#3-d-d)
    - [3 1 Declarative {#1-declarative}](#3-1-declarative-1-declarative)
    - [3 2 DORA Metrics {#2-dora-metrics}](#3-2-dora-metrics-2-dora-metrics)
  - [4. E {#e}](#4-e-e)
    - [4 1 Essential Complexity {#1-essential-complexity}](#4-1-essential-complexity-1-essential-complexity)
  - [5. F {#f}](#5-f-f)
    - [5 1 Formal Layer {#1-formal-layer}](#5-1-formal-layer-1-formal-layer)
  - [6. G {#g}](#6-g-g)
    - [6 1 GitOps {#1-gitops}](#6-1-gitops-1-gitops)
    - [6 2 Golden Path {#2-golden-path}](#6-2-golden-path-2-golden-path)
  - [7. H {#h}](#7-h-h)
    - [7 1 HPA (Horizontal Pod Autoscaler) {#1-hpa-horizontal-pod-autoscale}](#7-1-hpa-horizontal-pod-autoscaler-1-hpa-horizontal-pod-autoscale)
  - [8. I {#i}](#8-i-i)
    - [8 1 Imperative {#1-imperative}](#8-1-imperative-1-imperative)
    - [8 2 Internal Developer Platform (IDP) {#2-internal-developer-platform-}](#8-2-internal-developer-platform-idp-2-internal-developer-platform-)
    - [8 3 Intent-Driven {#3-intent-driven}](#8-3-intent-driven-3-intent-driven)
  - [9. K {#k}](#9-k-k)
    - [9 1 KEDA (Kubernetes Event-Driven Autoscaler) {#1-keda-kubernetes-event-driven}](#9-1-keda-kubernetes-event-driven-autoscaler-1-keda-kubernetes-event-driven)
  - [10. L {#l}](#10-l-l)
    - [10 1 Leaky Abstraction {#1-leaky-abstraction}](#10-1-leaky-abstraction-1-leaky-abstraction)
  - [11. M {#m}](#11-m-m)
    - [11 1 MTTR (Mean Time To Repair/Recovery) {#1-mttr-mean-time-to-repairreco}](#11-1-mttr-mean-time-to-repairrecovery-1-mttr-mean-time-to-repairreco)
  - [12. O {#o}](#12-o-o)
    - [12 1 OPA (Open Policy Agent) {#1-opa-open-policy-agent}](#12-1-opa-open-policy-agent-1-opa-open-policy-agent)
    - [12 2 OTLP (OpenTelemetry Protocol) {#2-otlp-opentelemetry-protocol}](#12-2-otlp-opentelemetry-protocol-2-otlp-opentelemetry-protocol)
    - [12 3 Observability {#3-observability}](#12-3-observability-3-observability)
  - [13. P {#p}](#13-p-p)
    - [13 1 Platform Engineering {#1-platform-engineering}](#13-1-platform-engineering-1-platform-engineering)
    - [13 2 Policy-as-Code {#2-policy-as-code}](#13-2-policy-as-code-2-policy-as-code)
  - [14. R {#r}](#14-r-r)
    - [14 1 Rego {#1-rego}](#14-1-rego-1-rego)
  - [15. S {#s}](#15-s-s)
    - [15 1 Semantic Gap {#1-semantic-gap}](#15-1-semantic-gap-1-semantic-gap)
    - [15 2 Semantic Layer {#2-semantic-layer}](#15-2-semantic-layer-2-semantic-layer)
    - [15 3 Semantic-Formal Duality {#3-semantic-formal-duality}](#15-3-semantic-formal-duality-3-semantic-formal-duality)
    - [15 4 Self-Healing {#4-self-healing}](#15-4-self-healing-4-self-healing)
    - [15 5 Service Mesh {#5-service-mesh}](#15-5-service-mesh-5-service-mesh)
    - [15 6 Sink Stage Model {#6-sink-stage-model}](#15-6-sink-stage-model-6-sink-stage-model)
  - [16. T {#t}](#16-t-t)
    - [16 1 Three Pillars of Observability {#1-three-pillars-of-observabili}](#16-1-three-pillars-of-observability-1-three-pillars-of-observabili)
  - [17. 缩写对照 {#缩写对照}](#17-缩写对照-缩写对照)
  - [18. 框架与工具 {#框架与工具}](#18-框架与工具-框架与工具)
    - [18 1 可观测性 {#1-可观测性}](#18-1-可观测性-1-可观测性)
    - [18 2 GitOps {#2-gitops}](#18-2-gitops-2-gitops)
    - [18 3 策略治理 {#3-策略治理}](#18-3-策略治理-3-策略治理)
    - [18 4 自动扩缩容 {#4-自动扩缩容}](#18-4-自动扩缩容-4-自动扩缩容)
  - [19. 概念层次 {#概念层次}](#19-概念层次-概念层次)
  - [20. 延伸阅读 {#延伸阅读}](#20-延伸阅读-延伸阅读)
  - [关联网络](#关联网络)
    - [前向引用](#前向引用)
    - [后向引用](#后向引用)
    - [交叉链接](#交叉链接)

- --

## 1. A {#a}

### 1 1 Architecture Sink {#1-architecture-sink}

- _架构下沉_*
软件系统中重复出现的复杂性，从应用层逐步转移到平台层、运行时层、最终固化到硬件层的持续过程。

- _相关_*：[2.1 架构下沉原理](./02_Architecture_Sink/02.1_Sink_Principles_Drivers.md)

### 1 2 Accidental Complexity {#2-accidental-complexity}

- _偶然复杂度_*
由技术实现引入的复杂度，理论上可以通过更好的抽象消除。

- _相关_*：[1.3 复杂度守恒](./01_Foundational_Theory/01.3_Software_Complexity_Conservation.md)

### 1 3 ArgoCD {#3-argocd}

GitOps 工具，持续监听 Git 仓库变化并自动同步到 Kubernetes 集群。

- _相关_*：[4.4 GitOps 声明式修复](./04_Self_Healing_Systems/04.4_GitOps_Declarative_Remediation.md)

## 2. C {#c}

### 2 1 Cognitive Load {#1-cognitive-load}

- _认知负载_*
开发者在理解和操作系统时需要保持在工作记忆中的信息量。

### 2 2 Complexity Conservation {#2-complexity-conservation}

- _复杂度守恒_*
在软件系统中，总复杂度（本质复杂度 + 偶然复杂度）是守恒的，不会凭空消失，只会转移。

- _公式_*：`Total_Complexity = Essential + Accidental = Constant`

- _相关_*：[1.3 复杂度守恒定律](./01_Foundational_Theory/01.3_Software_Complexity_Conservation.md)

### 2 3 Control Loop {#3-control-loop}

- _控制循环_*
持续比较"期望状态"与"实际状态"，自动调整以消除差异的反馈机制。

- _相关_*：[4.1 自愈架构原理](./04_Self_Healing_Systems/04.1_Self_Healing_Architecture.md)

## 3. D {#d}

### 3 1 Declarative {#1-declarative}

- _声明式_*
描述"要什么"（What）而非"怎么做"（How）的编程范式。

- _示例_*：SQL, Kubernetes YAML, Terraform

- _相关_*：[1.5 声明式与命令式](./01_Foundational_Theory/01.5_Declarative_Imperative_Paradigms.md)

### 3 2 DORA Metrics {#2-dora-metrics}

DevOps Research and Assessment 定义的四个关键指标：

1. 部署频率（Deployment Frequency）
2. 变更前置时间（Lead Time for Changes）
3. MTTR（平均修复时间）
4. 变更失败率（Change Failure Rate）

## 4. E {#e}

### 4 1 Essential Complexity {#1-essential-complexity}

- _本质复杂度_*
问题本身固有的复杂度，无法消除。

- _示例_*：业务规则的复杂性、领域模型的固有关系

- _相关_*：[1.3 复杂度守恒](./01_Foundational_Theory/01.3_Software_Complexity_Conservation.md)

## 5. F {#f}

### 5 1 Formal Layer {#1-formal-layer}

- _形式层_*
可计算的规则世界，包括代码、类型系统、逻辑门等可机械执行的符号系统。

- _相关_*：[1.1 语义形式对偶](./01_Foundational_Theory/01.1_Semantic_Formal_Duality.md)

## 6. G {#g}

### 6 1 GitOps {#1-gitops}

以 Git 为唯一真实源（Single Source of Truth）的运维模式，所有变更通过 Git 提交触发。

- _核心原则_*：

1. Git 是唯一真实源
2. 声明式配置
3. 自动同步
4. 持续调和

- _相关_*：[4.4 GitOps 声明式修复](./04_Self_Healing_Systems/04.4_GitOps_Declarative_Remediation.md)

### 6 2 Golden Path {#2-golden-path}

- _黄金路径_*
为常见场景预设的、阻力最小的开发路径，覆盖 80% 的需求。

- _相关_*：[8.3 黄金路径](./08_Platform_Engineering/08.3_Golden_Path.md)

## 7. H {#h}

### 7 1 HPA (Horizontal Pod Autoscaler) {#1-hpa-horizontal-pod-autoscale}

Kubernetes 水平 Pod 自动扩缩容器，根据 CPU/内存/自定义指标自动调整副本数。

## 8. I {#i}

### 8 1 Imperative {#1-imperative}

- _命令式_*
描述"怎么做"（How），逐步指定执行步骤的编程范式。

- _示例_*：Shell 脚本、C 语言、手工 kubectl 命令

- _相关_*：[1.5 声明式与命令式](./01_Foundational_Theory/01.5_Declarative_Imperative_Paradigms.md)

### 8 2 Internal Developer Platform (IDP) {#2-internal-developer-platform-}

- _内部开发者平台_*
企业内部构建的平台，为开发者提供自助服务能力，降低认知负载。

### 8 3 Intent-Driven {#3-intent-driven}

- _意图驱动_*
用户表达意图（"我要高可用"），系统自动生成具体实现的编程范式。

- _相关_*：[10.1 意图驱动编程](./10_Future_Directions/10.1_Intent_Driven_Programming.md)

## 9. K {#k}

### 9 1 KEDA (Kubernetes Event-Driven Autoscaler) {#1-keda-kubernetes-event-driven}

基于事件源（Kafka、SQS、Prometheus 等）的 Kubernetes 自动扩缩容器。

## 10. L {#l}

### 10 1 Leaky Abstraction {#1-leaky-abstraction}

- _抽象泄漏_*
抽象层无法完全隐藏底层细节，导致用户被迫理解底层实现的现象。

- _示例_*：GC 暂停、网络延迟、K8s 资源配额

- _相关_*：[1.2 计算抽象层次](./01_Foundational_Theory/01.2_Computational_Abstraction_Layers.md)

## 11. M {#m}

### 11 1 MTTR (Mean Time To Repair/Recovery) {#1-mttr-mean-time-to-repairreco}

- _平均修复/恢复时间_*
从故障发生到系统恢复的平均时间。

- _目标值_*：

- 传统运维：30+ 分钟
- 平台化：5-10 分钟
- 自愈系统：< 2 分钟

## 12. O {#o}

### 12 1 OPA (Open Policy Agent) {#1-opa-open-policy-agent}

策略引擎，使用 Rego 语言定义策略，实现 Policy-as-Code。

- _用途_*：准入控制、自愈策略、合规检查

- _相关_*：[4.3 OPA 策略引擎](./04_Self_Healing_Systems/04.3_OPA_Policy_Engine.md)

### 12 2 OTLP (OpenTelemetry Protocol) {#2-otlp-opentelemetry-protocol}

OpenTelemetry 项目定义的统一可观测性协议，支持 Metrics、Traces、Logs 三支柱。

- _相关_*：[4.2 OTLP 可观测性](./04_Self_Healing_Systems/04.2_OTLP_Observability.md)

### 12 3 Observability {#3-observability}

- _可观测性_*
通过系统外部输出（指标、日志、追踪）推断系统内部状态的能力。

- _三支柱_*：Metrics, Traces, Logs

- _相关_*：[6.1 三支柱可观测性](./06_Observability_Governance/06.1_Three_Pillars_Observability.md)

## 13. P {#p}

### 13 1 Platform Engineering {#1-platform-engineering}

- _平台工程_*
构建和维护内部开发者平台的工程实践，目标是降低认知负载、提升开发者体验。

- _相关_*：[8.1 平台工程定义](./08_Platform_Engineering/08.1_Platform_Engineering_Definition.md)

### 13 2 Policy-as-Code {#2-policy-as-code}

- _策略即代码_*
将治理策略、安全规则、合规要求以代码形式表达，可版本化、测试、自动执行。

- _工具_*：OPA、Kyverno、Gatekeeper

## 14. R {#r}

### 14 1 Rego {#1-rego}

OPA 使用的策略语言，声明式、逻辑式编程语言。

- _示例_*：

```rego
allow {
    input.user.role == "admin"
}
```

## 15. S {#s}

### 15 1 Semantic Gap {#1-semantic-gap}

- _语义缺口_*
意义世界中尚未被形式化、自动化的部分。

- _示例_*：

- 市场不确定性（2020 年代缺口）
- AI 伦理（未来缺口）

### 15 2 Semantic Layer {#2-semantic-layer}

- _语义层_*
人类自创的意义世界，包括商业价值、用户故事、领域概念等。

- _特征_*：可被解释、争论、再叙事

- _相关_*：[1.1 语义形式对偶](./01_Foundational_Theory/01.1_Semantic_Formal_Duality.md)

### 15 3 Semantic-Formal Duality {#3-semantic-formal-duality}

- _语义-形式对偶_*
意义世界与规则世界之间的永恒张力与相互转化。

- _核心机制_*：形式化 → 下沉 → 缺口重生

- _相关_*：[1.1 语义形式对偶](./01_Foundational_Theory/01.1_Semantic_Formal_Duality.md)

### 15 4 Self-Healing {#4-self-healing}

- _自愈_*
系统自动检测异常、诊断根因、执行修复并验证效果的闭环能力。

- _相关_*：[4.1 自愈架构原理](./04_Self_Healing_Systems/04.1_Self_Healing_Architecture.md)

### 15 5 Service Mesh {#5-service-mesh}

服务网格，为微服务提供服务发现、负载均衡、加密、可观测性等能力的基础设施层。

- _代表_*：Istio, Linkerd

- _相关_*：[9.3 Service Mesh](./09_Cloud_Native_Patterns/09.3_Service_Mesh.md)

### 15 6 Sink Stage Model {#6-sink-stage-model}

- _下沉阶段模型_*
描述架构下沉的五个层级（L1-L5）：运行时下沉 → 策略下沉 → 智能下沉 → 芯片级下沉 → 零代码态。

- _相关_*：[2.5 下沉阶段模型](./02_Architecture_Sink/02.5_Sink_Stage_Model.md)

## 16. T {#t}

### 16 1 Three Pillars of Observability {#1-three-pillars-of-observabili}

- _可观测性三支柱_*

1. **Metrics**：时间序列数据（CPU、内存、QPS）
2. **Traces**：分布式请求追踪
3. **Logs**：事件详细记录

- _相关_*：[6.1 三支柱可观测性](./06_Observability_Governance/06.1_Three_Pillars_Observability.md)

## 17. 缩写对照 {#缩写对照}

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

## 18. 框架与工具 {#框架与工具}

### 18 1 可观测性 {#1-可观测性}

- **Prometheus**：指标采集与告警
- **Grafana**：可视化
- **Jaeger/Tempo**：分布式追踪
- **Loki**：日志聚合
- **OpenTelemetry**：统一协议

### 18 2 GitOps {#2-gitops}

- **ArgoCD**：声明式 CD
- **Flux**：GitOps operator
- **Helm**：K8s 包管理

### 18 3 策略治理 {#3-策略治理}

- **OPA**：策略引擎
- **Gatekeeper**：K8s 准入控制器
- **Kyverno**：K8s 原生策略引擎

### 18 4 自动扩缩容 {#4-自动扩缩容}

- **HPA**：K8s 内置
- **KEDA**：事件驱动扩缩容
- **VPA**：垂直扩缩容
- **Cluster Autoscaler**：节点扩缩容

## 19. 概念层次 {#概念层次}

```text
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

## 20. 延伸阅读 {#延伸阅读}

- [完整索引](./00_Master_Index.md)
- [快速参考](./QUICK_REFERENCE.md)
- [常见问题](./FAQ.md)
- [学习路径](./LEARNING_PATHS.md)

- --


---

## 关联网络

### 前向引用

> 本文档为以下文档提供基础：
>
> - [相关文档](./) (待补充)

### 后向引用

> 本文档依赖以下基础文档：
>
> - [基础文档](./) (待补充)

### 交叉链接

> 相关主题：
>
> - [主题A](./) (待补充)
> - [主题B](./) (待补充)

---

_本文档由 FormalScience 文档规范化工具自动生成_
