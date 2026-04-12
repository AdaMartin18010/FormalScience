- --
topic: "Software Perspective - 快速参考"
dependencies: []
status: "review"
author: "FormalScience Project"
date: "2026-04-12"
version: "1.0.0"
tags: ["类型", "形式化", "逻辑", "AI", "模型"]
category: "reference"
priority: "medium"
- --

# Software Perspective - 快速参考

> **文档版本**: v1.0.0
> **最后更新**: 2025-10-27
> **文档规模**: 380行 | 核心概念速查手册
> **阅读建议**: 本文提供软件透视核心概念的快速索引和图表

- --

## 1. 📋 目录 {#-目录}

- [Software Perspective - 快速参考](#software-perspective---快速参考)
  - [1. 📋 目录 {#-目录}](#1--目录--目录)
  - [1. 核心框架速查 {#核心框架速查}](#1-核心框架速查-核心框架速查)
    - [1 1 语义-形式对偶螺旋 {#1-语义-形式对偶螺旋}](#1-1-语义-形式对偶螺旋-1-语义-形式对偶螺旋)
    - [1 2 六段螺旋（2020-2025） {#2-六段螺旋2020-2025}](#1-2-六段螺旋2020-2025-2-六段螺旋2020-2025)
  - [2. 架构下沉速查 {#架构下沉速查}](#2-架构下沉速查-架构下沉速查)
    - [2 1 五层模型 {#1-五层模型}](#2-1-五层模型-1-五层模型)
    - [2 2 下沉动因公式 {#2-下沉动因公式}](#2-2-下沉动因公式-2-下沉动因公式)
  - [3. 自愈系统速查 {#自愈系统速查}](#3-自愈系统速查-自愈系统速查)
    - [3 1 OODA 循环 {#1-ooda-循环}](#3-1-ooda-循环-1-ooda-循环)
    - [3 2 三位一体 {#2-三位一体}](#3-2-三位一体-2-三位一体)
    - [3 3 自愈成熟度 {#3-自愈成熟度}](#3-3-自愈成熟度-3-自愈成熟度)
  - [4. 配置与扩缩容速查 {#配置与扩缩容速查}](#4-配置与扩缩容速查-配置与扩缩容速查)
    - [4 1 配置管理对比 {#1-配置管理对比}](#4-1-配置管理对比-1-配置管理对比)
    - [4 2 扩缩容对比 {#2-扩缩容对比}](#4-2-扩缩容对比-2-扩缩容对比)
    - [4 3 选型速查 {#3-选型速查}](#4-3-选型速查-3-选型速查)
  - [5. 开发者演进速查 {#开发者演进速查}](#5-开发者演进速查-开发者演进速查)
    - [5 1 三次跃迁 {#1-三次跃迁}](#5-1-三次跃迁-1-三次跃迁)
    - [5 2 六维元能力 {#2-六维元能力}](#5-2-六维元能力-2-六维元能力)
    - [5 3 角色转型 {#3-角色转型}](#5-3-角色转型-3-角色转型)
  - [6. 复杂度守恒速查 {#复杂度守恒速查}](#6-复杂度守恒速查-复杂度守恒速查)
    - [6 1 守恒公式 {#1-守恒公式}](#6-1-守恒公式-1-守恒公式)
    - [6 2 转移模式 {#2-转移模式}](#6-2-转移模式-2-转移模式)
  - [7. 命令速查 {#命令速查}](#7-命令速查-命令速查)
    - [7 1 Kubernetes 常用 {#1-kubernetes-常用}](#7-1-kubernetes-常用-1-kubernetes-常用)
    - [7 2 Git 操作 {#2-git-操作}](#7-2-git-操作-2-git-操作)
    - [7 3 OPA 策略测试 {#3-opa-策略测试}](#7-3-opa-策略测试-3-opa-策略测试)
    - [7 4 Prometheus 查询 {#4-prometheus-查询}](#7-4-prometheus-查询-4-prometheus-查询)
  - [8. YAML 模板速查 {#yaml-模板速查}](#8-yaml-模板速查-yaml-模板速查)
    - [8 1 Deployment 基础 {#1-deployment-基础}](#8-1-deployment-基础-1-deployment-基础)
    - [8 2 HPA 配置 {#2-hpa-配置}](#8-2-hpa-配置-2-hpa-配置)
    - [8 3 OPA 策略示例 {#3-opa-策略示例}](#8-3-opa-策略示例-3-opa-策略示例)
    - [8 4 KEDA ScaledObject {#4-keda-scaledobject}](#8-4-keda-scaledobject-4-keda-scaledobject)
  - [9. 度量指标速查 {#度量指标速查}](#9-度量指标速查-度量指标速查)
    - [9 1 DORA 四大指标 {#1-dora-四大指标}](#9-1-dora-四大指标-1-dora-四大指标)
    - [9 2 平台成熟度指标 {#2-平台成熟度指标}](#9-2-平台成熟度指标-2-平台成熟度指标)
  - [10. 诊断流程速查 {#诊断流程速查}](#10-诊断流程速查-诊断流程速查)
    - [10 1 性能问题 {#1-性能问题}](#10-1-性能问题-1-性能问题)
    - [10 2 故障排查 {#2-故障排查}](#10-2-故障排查-2-故障排查)
  - [11. 学习资源 {#学习资源}](#11-学习资源-学习资源)
    - [11 1 书籍 {#1-书籍}](#11-1-书籍-1-书籍)
    - [11 2 在线文档 {#2-在线文档}](#11-2-在线文档-2-在线文档)
    - [11 3 认证 {#3-认证}](#11-3-认证-3-认证)
  - [12. 常用链接 {#常用链接}](#12-常用链接-常用链接)
  - [关联网络](#关联网络)
    - [前向引用](#前向引用)
    - [后向引用](#后向引用)
    - [交叉链接](#交叉链接)

- --

## 1. 核心框架速查 {#核心框架速查}

### 1 1 语义-形式对偶螺旋 {#1-语义-形式对偶螺旋}

```text
语义缺口 → 形式化 → 平台化 → 硬件化 → 新语义缺口
```

- *当前位置（2025）**：智能下沉阶段（L2→L3）

### 1 2 六段螺旋（2020-2025） {#2-六段螺旋2020-2025}

| 缺口 | 响应 | 下沉形式 | 即将物理化 |
|-----|------|---------|-----------|
| 业务不确定性 | Feature Flag | YAML trafficWeight | 芯片级可信配置 |
| 人-机责任模糊 | Policy-as-Code | AdmissionReview | 硅签名拒绝 |
| 注意力稀缺 | Auto-Remediation | PromQL + Rego | FPGA 硬管道 |
| 能源成本 | 碳感知调度 | CO₂ 权重 | 焦耳算力寄存器 |
| 多模现实 | 链上日志 | 不可变 ConfigMap | 哈希验证进 CPU |
| 意义量化 | KPI-as-Code | PromQL 指标 | 硅片级 AB 电路 |

## 2. 架构下沉速查 {#架构下沉速查}

### 2 1 五层模型 {#1-五层模型}

| 层级 | 时间 | 特征 | 程序员体感 |
|-----|------|------|-----------|
| L1 运行时 | 2015-2022 | K8s/容器 | "不写脚本了" |
| L2 策略 | 2022-2025 | OPA/Gatekeeper | "不写 if-else" |
| **L3 智能** | **2024-2026** | **AI 决策+自愈** | **"不写回滚"** ← 当前 |
| L4 芯片级 | 2025-2028 | ISA 固化 | "代码消失" |
| L5 零代码 | >2028 | 自然语言 | "角色消失" |

### 2 2 下沉动因公式 {#2-下沉动因公式}

```text
下沉收益 > 下沉成本

收益 = N × (应用成本 - 平台边际成本)
成本 = 平台开发成本 + 维护成本

临界点：N ≈ 10-20 个团队
```

## 3. 自愈系统速查 {#自愈系统速查}

### 3 1 OODA 循环 {#1-ooda-循环}

```text
Observe (OTLP) → Orient (异常检测) → Decide (OPA) → Act (GitOps)
     ↑                                                    |
     └────────────────────────────────────────────────────┘
```

### 3 2 三位一体 {#2-三位一体}

| 组件 | 职责 | 工具 |
|-----|------|------|
| **OTLP** | 感知（Metrics/Traces/Logs） | OpenTelemetry |
| **OPA** | 决策（策略匹配） | Rego 规则 |
| **GitOps** | 执行（声明式修复） | ArgoCD/Flux |

### 3 3 自愈成熟度 {#3-自愈成熟度}

| 级别 | MTTR | 人工介入率 |
|-----|------|-----------|
| L0 无自愈 | > 30 min | 100% |
| L1 半自动 | 10-30 min | 50% |
| L2 基础自愈 | 2-10 min | 20% |
| L3 智能自愈 | < 2 min | < 10% |
| L4 自治 | < 30 sec | < 1% |

## 4. 配置与扩缩容速查 {#配置与扩缩容速查}

### 4 1 配置管理对比 {#1-配置管理对比}

| 方案 | 热更新 | 审计 | 适用场景 |
|-----|--------|------|---------|
| 环境变量 | ❌ | ⚠️ | 少量非敏感配置 |
| ConfigMap | ✅ | ✅ | 常规集群内 |
| 外部配置中心 | ✅ | ✅ | 多语言/混合云 |
| GitOps | ✅ | ✅✅ | 云原生成熟团队 |

### 4 2 扩缩容对比 {#2-扩缩容对比}

| 方案 | 触发维度 | 最小粒度 | 冷启动 |
|-----|---------|---------|--------|
| HPA | CPU/内存/自定义 | Pod | 秒级 |
| KEDA | 事件源 | Pod | 秒级 |
| VPA | 资源推荐 | 容器 | 需重启 |
| Cluster Autoscaler | 节点不足 | 节点 | 分钟级 |

### 4 3 选型速查 {#3-选型速查}

| 企业阶段 | 配置方案 | 扩缩方案 |
|---------|---------|---------|
| 初创/单体 | ConfigMap + 环境变量 | HPA (CPU 70%) |
| 成长/微服务 | GitOps + ConfigMap | HPA + KEDA |
| 数据驱动 | Nacos | KEDA + 自定义指标 |
| Serverless | 函数环境变量 | Knative HCP |

## 5. 开发者演进速查 {#开发者演进速查}

### 5 1 三次跃迁 {#1-三次跃迁}

| 时代 | 核心工具 | 关键产出 | 评价指标 |
|-----|---------|---------|---------|
| 旧 | IDE + Debugger | 源代码 | 代码行数 |
| 过渡 | Copilot + AI Chat | 功能+策略 | 功能完成度 |
| 新 | Prompt IDE + DSL | 商业策略库 | 营收/留存/效率 |

### 5 2 六维元能力 {#2-六维元能力}

1. **形式化建模**：把模糊需求变可验证命题
2. **数据叙事**：用数据讲因果故事
3. **实验设计**：假设→实验→决策
4. **提示词工程**：精准驱动大模型
5. **责任边界感**：知道 AI 能/不能决定什么
6. **多域语言切换**：在财务-运营-技术-法律间翻译

### 5 3 角色转型 {#3-角色转型}

```text
CRUD 程序员
    ↓
功能开发者
    ↓
提示词工程师
    ↓
系统守门人
    ↓
商业洞察编译器
```

## 6. 复杂度守恒速查 {#复杂度守恒速查}

### 6 1 守恒公式 {#1-守恒公式}

```text
Total = Essential + Accidental = Constant
```

### 6 2 转移模式 {#2-转移模式}

| 模式 | 示例 | 权衡 |
|-----|------|------|
| 用户→平台 | TCP 重传逻辑下沉 | 用户解放，平台复杂 |
| 开发时→运行时 | 反射调用 | 开发快，运行慢 |
| 代码→配置 | K8s YAML | 声明简单，调试难 |
| 单体→分布式 | 微服务 | 扩展好，运维难 |
| 人工→自动化 | 自愈系统 | MTTR 低，系统复杂 |

## 7. 命令速查 {#命令速查}

### 7 1 Kubernetes 常用 {#1-kubernetes-常用}

```bash
# 查看资源
kubectl get pods/deployments/services
kubectl describe pod <name>
kubectl logs -f <pod>

# 调试
kubectl exec -it <pod> -- bash
kubectl port-forward <pod> 8080:80

# GitOps
kubectl apply -f manifest.yaml
kubectl diff -f manifest.yaml
```

### 7 2 Git 操作 {#2-git-操作}

```bash
# GitOps 工作流
git add .
git commit -m "feat: enable auto-scaling"
git push origin main

# 回滚
git revert HEAD
git push origin main

# 审计
git log --author=self-heal-bot
git blame <file>
```

### 7 3 OPA 策略测试 {#3-opa-策略测试}

```bash
# 测试 Rego 规则
opa test policy/ --verbose

# 评估策略
opa eval -d policy.rego -i input.json "data.policy.allow"

# 运行 OPA 服务器
opa run --server policy.rego
```

### 7 4 Prometheus 查询 {#4-prometheus-查询}

```promql
# 错误率
rate(http_errors_total[5m]) / rate(http_requests_total[5m])

# CPU 使用率
100 - (avg by (instance) (irate(node_cpu_seconds_total{mode="idle"}[5m])) * 100)

# P99 延迟
histogram_quantile(0.99, rate(http_request_duration_seconds_bucket[5m]))
```

## 8. YAML 模板速查 {#yaml-模板速查}

### 8 1 Deployment 基础 {#1-deployment-基础}

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: my-app
spec:
  replicas: 3
  selector:
    matchLabels:
      app: my-app
  template:
    metadata:
      labels:
        app: my-app
    spec:
      containers:
      - name: app
        image: my-app:v1.0.0
        ports:
        - containerPort: 8080
        resources:
          requests:
            memory: "128Mi"
            cpu: "100m"
          limits:
            memory: "256Mi"
            cpu: "200m"
```

### 8 2 HPA 配置 {#2-hpa-配置}

```yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: my-app-hpa
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: my-app
  minReplicas: 2
  maxReplicas: 10
  metrics:
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70
```

### 8 3 OPA 策略示例 {#3-opa-策略示例}

```rego
package kubernetes.admission

deny[msg] {
  input.request.kind.kind == "Pod"
  image := input.request.object.spec.containers[_].image
  not startswith(image, "registry.company.com/")
  msg := "Only images from company registry are allowed"
}
```

### 8 4 KEDA ScaledObject {#4-keda-scaledobject}

```yaml
apiVersion: keda.sh/v1alpha1
kind: ScaledObject
metadata:
  name: my-app-scaler
spec:
  scaleTargetRef:
    name: my-app
  minReplicaCount: 1
  maxReplicaCount: 100
  triggers:
  - type: prometheus
    metadata:
      serverAddress: http://prometheus:9090
      query: sum(rate(http_requests_total[1m]))
      threshold: "1000"
```

## 9. 度量指标速查 {#度量指标速查}

### 9 1 DORA 四大指标 {#1-dora-四大指标}

| 指标 | 精英团队 | 高绩效 | 中等 | 低绩效 |
|-----|---------|--------|------|--------|
| **部署频率** | 按需（多次/天） | 每周-每月 | 每月-每6月 | 更低 |
| **前置时间** | < 1 天 | 1 天-1 周 | 1 周-1 月 | > 1 月 |
| **MTTR** | < 1 小时 | < 1 天 | 1 天-1 周 | > 1 周 |
| **变更失败率** | 0-15% | 16-30% | 31-45% | > 45% |

### 9 2 平台成熟度指标 {#2-平台成熟度指标}

| 指标 | L1 | L2 | L3 |
|-----|----|----|-----|
| 自动化率 | 60% | 80% | 95% |
| 平台复用率 | 50% | 80% | 95% |
| 认知负载（概念数） | 50 | 30 | < 20 |
| 开发者满意度 | 6/10 | 8/10 | 9/10 |

## 10. 诊断流程速查 {#诊断流程速查}

### 10 1 性能问题 {#1-性能问题}

```text
1. 查看指标：Grafana 看 CPU/内存/延迟
2. 分析追踪：Jaeger 找慢链路
3. 查看日志：Loki 搜索错误
4. 定位代码：Profiling 找热点
5. 优化验证：压测对比
```

### 10 2 故障排查 {#2-故障排查}

```text
1. 确认现象：什么服务、什么时间、什么影响
2. 查看事件：kubectl get events
3. 检查日志：kubectl logs
4. 检查配置：kubectl get/describe
5. 回滚验证：git revert + ArgoCD sync
```

## 11. 学习资源 {#学习资源}

### 11 1 书籍 {#1-书籍}

- 《Site Reliability Engineering》 - Google SRE
- 《Designing Data-Intensive Applications》 - Martin Kleppmann
- 《Team Topologies》 - Matthew Skelton

### 11 2 在线文档 {#2-在线文档}

- [Kubernetes 官方文档](https://kubernetes.io/docs/)
- [OpenTelemetry 文档](https://opentelemetry.io/docs/)
- [OPA 文档](https://www.openpolicyagent.org/docs/)
- [CNCF Landscape](https://landscape.cncf.io/)

### 11 3 认证 {#3-认证}

- CKA (Certified Kubernetes Administrator)
- CKAD (Certified Kubernetes Application Developer)
- CKS (Certified Kubernetes Security Specialist)

## 12. 常用链接 {#常用链接}

- [完整索引](./00_Master_Index.md)
- [术语表](./GLOSSARY.md)
- [常见问题](./FAQ.md)
- [学习路径](./LEARNING_PATHS.md)

- --


---

## 关联网络

### 前向引用

> 本文档为以下文档提供基础：
>
> - [相关文档](./README.md) (待补充)

### 后向引用

> 本文档依赖以下基础文档：
>
> - [基础文档](./README.md) (待补充)

### 交叉链接

> 相关主题：
>
> - [主题A](./README.md) (待补充)
> - [主题B](./README.md) (待补充)

---

_本文档由 FormalScience 文档规范化工具自动生成_
