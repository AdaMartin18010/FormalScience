# Kubernetes调度系统深度分析

> 本文档基于Kubernetes v1.28+源码进行深度分析，结合形式化方法对调度系统进行系统性研究。

---

## 目录

- [Kubernetes调度系统深度分析](#kubernetes调度系统深度分析)
  - [目录](#目录)
  - [1. Kubernetes架构概述](#1-kubernetes架构概述)
    - [1.1 控制平面组件](#11-控制平面组件)
      - [1.1.1 API Server (kube-apiserver)](#111-api-server-kube-apiserver)
      - [1.1.2 etcd](#112-etcd)
      - [1.1.3 Controller Manager (kube-controller-manager)](#113-controller-manager-kube-controller-manager)
    - [1.2 数据平面组件](#12-数据平面组件)
      - [1.2.1 kubelet](#121-kubelet)
      - [1.2.2 kube-proxy](#122-kube-proxy)
    - [1.3 调度器在架构中的位置](#13-调度器在架构中的位置)
      - [1.3.1 调度器与其他组件的交互](#131-调度器与其他组件的交互)
  - [2. kube-scheduler详细分析](#2-kube-scheduler详细分析)
    - [2.1 调度框架设计](#21-调度框架设计)
      - [2.1.1 调度框架接口定义](#211-调度框架接口定义)
      - [2.1.2 框架实现核心代码](#212-框架实现核心代码)
    - [2.2 调度队列](#22-调度队列)
      - [2.2.1 调度队列实现](#221-调度队列实现)
    - [2.3 预选阶段（Predicates）](#23-预选阶段predicates)
      - [2.3.1 核心预选函数实现](#231-核心预选函数实现)
      - [2.3.2 Pod亲和性与反亲和性过滤](#232-pod亲和性与反亲和性过滤)
    - [2.4 优选阶段（Priorities）](#24-优选阶段priorities)
      - [2.4.1 优选函数核心实现](#241-优选函数核心实现)
      - [2.4.2 分数归一化](#242-分数归一化)
    - [2.5 调度算法插件机制](#25-调度算法插件机制)
      - [2.5.1 插件注册机制](#251-插件注册机制)
  - [3. 调度策略详解](#3-调度策略详解)
    - [3.1 NodeName/NodeSelector](#31-nodenamenodeselector)
    - [3.2 Affinity/Anti-affinity](#32-affinityanti-affinity)
    - [3.3 Taints/Tolerations](#33-taintstolerations)
    - [3.4 Pod拓扑分布约束](#34-pod拓扑分布约束)
    - [3.5 资源请求与限制](#35-资源请求与限制)
  - [4. 源码级分析](#4-源码级分析)
    - [4.1 scheduler.go核心代码](#41-schedulergo核心代码)
    - [4.2 调度缓存机制](#42-调度缓存机制)
  - [5. 性能优化](#5-性能优化)
    - [5.1 调度延迟优化](#51-调度延迟优化)
      - [5.1.1 节点采样优化](#511-节点采样优化)
      - [5.1.2 并行化优化](#512-并行化优化)
    - [5.2 大规模集群优化](#52-大规模集群优化)
      - [5.2.1 大规模集群配置](#521-大规模集群配置)
    - [5.3 自定义调度器开发](#53-自定义调度器开发)
  - [6. 形式化分析](#6-形式化分析)
    - [6.1 调度决策的形式化模型](#61-调度决策的形式化模型)
    - [6.2 资源分配的正确性证明](#62-资源分配的正确性证明)
    - [6.3 负载均衡的数学分析](#63-负载均衡的数学分析)
    - [6.4 调度算法复杂度分析](#64-调度算法复杂度分析)
  - [7. 实践案例](#7-实践案例)
    - [7.1 大规模生产集群配置](#71-大规模生产集群配置)
    - [7.2 调度问题排查](#72-调度问题排查)
    - [7.3 常见调度问题及解决方案](#73-常见调度问题及解决方案)
    - [7.4 性能调优案例](#74-性能调优案例)
  - [8. Rust实现示例](#8-rust实现示例)
    - [8.1 简化版调度器框架](#81-简化版调度器框架)
    - [8.2 调度算法模拟](#82-调度算法模拟)
    - [8.3 性能基准测试](#83-性能基准测试)
    - [8.4 Cargo.toml配置](#84-cargotoml配置)
  - [总结](#总结)
  - [参考资源](#参考资源)

---

## 1. Kubernetes架构概述

### 1.1 控制平面组件

Kubernetes控制平面（Control Plane）是集群的大脑，负责全局决策和集群事件的检测与响应。

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           Kubernetes Control Plane                          │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐    │
│  │   API Server │  │   etcd       │  │  Scheduler   │  │  Controller  │    │
│  │              │  │              │  │              │  │   Manager    │    │
│  │  ┌────────┐  │  │  ┌────────┐  │  │  ┌────────┐  │  │  ┌────────┐  │    │
│  │  │  REST  │  │  │  │  KV    │  │  │  │ Schedule│  │  │  │Replica │  │    │
│  │  │  API   │  │  │  │ Store  │  │  │  │ Engine │  │  │  │Set Ctrl│  │    │
│  │  └────────┘  │  │  └────────┘  │  │  └────────┘  │  │  └────────┘  │    │
│  │  ┌────────┐  │  │              │  │              │  │  ┌────────┐  │    │
│  │  │  Auth  │  │  │  - All K8s   │  │  - Pod       │  │  │Node    │  │    │
│  │  │  AuthZ │  │  │    cluster   │  │    placement │  │  │Controller│  │    │
│  │  └────────┘  │  │    state     │  │  - Node      │  │  └────────┘  │    │
│  │              │  │              │  │    selection │  │              │    │
│  └──────┬───────┘  └──────┬───────┘  └──────┬───────┘  └──────┬───────┘    │
│         │                 │                 │                 │            │
│         └─────────────────┴─────────────────┴─────────────────┘            │
│                                    │                                       │
│                                    ▼                                       │
│                          ┌─────────────────┐                               │
│                          │   etcd Cluster  │                               │
│                          │  (Distributed)  │                               │
│                          └─────────────────┘                               │
└─────────────────────────────────────────────────────────────────────────────┘
```

#### 1.1.1 API Server (kube-apiserver)

API Server是Kubernetes控制平面的前端，暴露Kubernetes API：

```go
// kubernetes/cmd/kube-apiserver/app/server.go
// API Server核心启动逻辑

func CreateServerChain(completedOptions completedServerRunOptions, stopCh <-chan struct{}) (*aggregatorapiserver.APIAggregator, error) {
    // 创建API Server配置
    kubeAPIServerConfig, serviceResolver, pluginInitializer, err := CreateKubeAPIServerConfig(completedOptions)
    if err != nil {
        return nil, err
    }

    // 创建API扩展服务器
    apiExtensionsConfig, err := createAPIExtensionsConfig(*kubeAPIServerConfig.GenericConfig, completedOptions.ServerRunOptions,
        completedOptions.MasterCount, serviceResolver, completedOptions.MasterCount)
    if err != nil {
        return nil, err
    }

    // 链式创建服务器
    notFoundHandler := notfoundhandler.New(kubeAPIServerConfig.GenericConfig.Serializer, genericapifilters.NoMuxAndDiscoveryContainerKey)
    kubeAPIServer, err := CreateKubeAPIServer(kubeAPIServerConfig, apiExtensionsConfig.GenericConfig, notFoundHandler)
    if err != nil {
        return nil, err
    }

    return kubeAPIServer, nil
}
```

**API Server核心职责：**

| 职责 | 说明 | 关键代码路径 |
|------|------|-------------|
| RESTful API暴露 | 提供对Kubernetes资源的CRUD操作 | `pkg/apiserver` |
| 认证与授权 | 处理所有请求的认证和RBAC | `pkg/auth` |
| 准入控制 | 验证和修改传入的请求 | `plugin/pkg/admission` |
| 状态持久化 | 将所有数据写入etcd | `pkg/storage` |

#### 1.1.2 etcd

etcd是Kubernetes的后端存储，保存所有集群状态：

```go
// Kubernetes使用etcd v3 API进行存储
// 存储的数据包括：
// - Nodes: /registry/minions
// - Pods: /registry/pods
// - Services: /registry/services
// - ConfigMaps: /registry/configmaps
// - Secrets: /registry/secrets
// - 所有其他Kubernetes资源

// etcd数据存储路径示例
const (
    // 节点注册表路径
    NodeRegistryPath = "/registry/minions"
    // Pod注册表路径
    PodRegistryPath = "/registry/pods"
    // 调度决策存储路径
    BindingRegistryPath = "/registry/bindings"
)
```

#### 1.1.3 Controller Manager (kube-controller-manager)

Controller Manager运行各种控制器，确保集群状态与期望状态一致：

```go
// kubernetes/cmd/kube-controller-manager/app/controllermanager.go

// NewControllerInitializers返回所有控制器的初始化函数
func NewControllerInitializers(loopMode ControllerLoopMode) map[string]InitFunc {
    controllers := map[string]InitFunc{}

    // 核心控制器
    controllers["endpoint"] = startEndpointController
    controllers["endpointslice"] = startEndpointSliceController
    controllers["replicationcontroller"] = startReplicationController
    controllers["podgc"] = startPodGCController
    controllers["resourcequota"] = startResourceQuotaController
    controllers["namespace"] = startNamespaceController
    controllers["serviceaccount"] = startServiceAccountController
    controllers["garbagecollector"] = startGarbageCollectorController
    controllers["daemonset"] = startDaemonSetController
    controllers["job"] = startJobController
    controllers["deployment"] = startDeploymentController
    controllers["replicaset"] = startReplicaSetController
    controllers["horizontalpodautoscaling"] = startHPAController
    controllers["disruption"] = startDisruptionController
    controllers["statefulset"] = startStatefulSetController
    controllers["cronjob"] = startCronJobController
    controllers["csrcleaning"] = startCSRCleaningController
    controllers["csrapproving"] = startCSRApprovingController
    controllers["ttl"] = startTTLController
    controllers["bootstrapsigner"] = startBootstrapSignerController
    controllers["tokencleaner"] = startTokenCleanerController
    controllers["nodeipam"] = startNodeIpamController
    controllers["nodelifecycle"] = startNodeLifecycleController

    // 云提供商相关控制器
    controllers["service"] = startServiceController
    controllers["route"] = startRouteController
    controllers["cloud-node-lifecycle"] = startCloudNodeLifecycleController

    return controllers
}
```

### 1.2 数据平面组件

数据平面（Data Plane）负责实际运行工作负载。

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           Kubernetes Data Plane                             │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌──────────────────────────┐    ┌──────────────────────────┐              │
│  │        Node 1            │    │        Node 2            │              │
│  │  ┌──────────────────┐   │    │  ┌──────────────────┐   │              │
│  │  │   kubelet        │   │    │  │   kubelet        │   │              │
│  │  │  ┌────────────┐  │   │    │  │  ┌────────────┐  │   │              │
│  │  │  │ Pod Status │  │   │    │  │  │ Pod Status │  │   │              │
│  │  │  │ Reporting  │  │   │    │  │  │ Reporting  │  │   │              │
│  │  │  └────────────┘  │   │    │  │  └────────────┘  │   │              │
│  │  │  ┌────────────┐  │   │    │  │  ┌────────────┐  │   │              │
│  │  │  │ Container  │  │   │    │  │  │ Container  │  │   │              │
│  │  │  │ Runtime    │  │   │    │  │  │ Runtime    │  │   │              │
│  │  │  │ (CRI)      │  │   │    │  │  │ (CRI)      │  │   │              │
│  │  │  └────────────┘  │   │    │  │  └────────────┘  │   │              │
│  │  └──────────────────┘   │    │  └──────────────────┘   │              │
│  │  ┌──────────────────┐   │    │  ┌──────────────────┐   │              │
│  │  │  kube-proxy      │   │    │  │  kube-proxy      │   │              │
│  │  │  ┌────────────┐  │   │    │  │  ┌────────────┐  │   │              │
│  │  │  │ iptables/  │  │   │    │  │  │ iptables/  │  │   │              │
│  │  │  │ IPVS       │  │   │    │  │  │ IPVS       │  │   │              │
│  │  │  └────────────┘  │   │    │  │  └────────────┘  │   │              │
│  │  └──────────────────┘   │    │  └──────────────────┘   │              │
│  └──────────────────────────┘    └──────────────────────────┘              │
│                                                                             │
│  ┌────────────────────────────────────────────────────────────┐           │
│  │                    Container Runtime                        │           │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐        │           │
│  │  │ containerd  │  │    CRI-O    │  │  dockerd    │        │           │
│  │  └─────────────┘  └─────────────┘  └─────────────┘        │           │
│  └────────────────────────────────────────────────────────────┘           │
└─────────────────────────────────────────────────────────────────────────────┘
```

#### 1.2.1 kubelet

kubelet是每个节点上的主要代理，负责Pod的生命周期管理：

```go
// kubernetes/pkg/kubelet/kubelet.go
// kubelet核心结构体

type Kubelet struct {
    // 节点名称
    hostname string
    nodeName types.NodeName

    // 容器运行时接口
    runtime kubecontainer.Runtime

    // Pod管理器
    podManager kubepod.Manager

    // Pod workers处理Pod的创建、更新和删除
    podWorkers PodWorkers

    // Pod缓存
    podCache kubecontainer.Cache

    // 状态管理器
    statusManager status.Manager

    // 探针管理器
    probeManager prober.Manager

    // 卷管理器
    volumeManager volumemanager.VolumeManager

    // CNI网络插件
    networkPlugin network.NetworkPlugin

    // 资源分析器
    resourceAnalyzer serverstats.ResourceAnalyzer

    // 运行时类管理器
    runtimeClassManager *runtimeclass.Manager

    // ... 其他字段
}

// syncPod是kubelet同步Pod的核心函数
func (kl *Kubelet) syncPod(ctx context.Context, updateType kubetypes.SyncPodType, pod *v1.Pod,
    mirrorPod *v1.Pod, podStatus *kubecontainer.PodStatus) error {

    // 1. 计算Pod状态
    apiPodStatus := kl.generateAPIPodStatus(pod, podStatus)

    // 2. 检查Pod是否被准入
    runnable := kl.canRunPod(pod)
    if !runnable.Admit {
        kl.recordNodeStatusEvent("NodeNotReady", runnable.Reason)
        return fmt.Errorf(runnable.Reason)
    }

    // 3. 创建沙箱（如果必要）
    podIPs := []string{}
    if err := kl.runtimeState.errors()[ErrKubeletStart]; err != nil {
        return fmt.Errorf("kubelet is not ready: %v", err)
    }

    // 4. 同步Pod网络
    if err := kl.syncPodNetwork(ctx, pod, podStatus); err != nil {
        return err
    }

    // 5. 创建和启动容器
    result := kl.containerRuntime.SyncPod(pod, podStatus, pullSecrets, kl.backOff)

    return result.Error()
}
```

#### 1.2.2 kube-proxy

kube-proxy负责Service的负载均衡和网络代理：

```go
// kubernetes/pkg/proxy/iptables/proxier.go
// iptables模式的kube-proxy实现

type Proxier struct {
    // 服务端口和端点管理
    servicePortMap proxy.ServicePortMap
    endpointsMap   proxy.EndpointsMap

    // iptables接口
    iptables utiliptables.Interface

    // 规则管理
    natChains     utilproxy.LineBuffer
    natRules      utilproxy.LineBuffer
    filterChains  utilproxy.LineBuffer
    filterRules   utilproxy.LineBuffer

    // 节点IP配置
    nodeIP net.IP

    // 端口范围
    portRange string

    // 同步周期
    syncPeriod    time.Duration
    minSyncPeriod time.Duration

    // ... 其他字段
}

// syncProxyRules生成并应用iptables规则
func (proxier *Proxier) syncProxyRules() {
    // 1. 获取当前服务和端点状态
    serviceUpdateResult := proxier.servicePortMap.Update(proxier.serviceChanges)
    endpointUpdateResult := proxier.endpointsMap.Update(proxier.endpointsChanges)

    // 2. 如果没有变化则跳过
    if !serviceUpdateResult.UpstreamIPNumberChanged && !endpointUpdateResult.HcEndpointsChanged {
        // 检查是否需要强制同步
        if !proxier.needFullSync {
            return
        }
    }

    // 3. 重置iptables缓冲区
    proxier.natChains.Reset()
    proxier.natRules.Reset()
    proxier.filterChains.Reset()
    proxier.filterRules.Reset()

    // 4. 为每个服务生成规则
    for svcName, svc := range proxier.servicePortMap {
        // 创建服务端点规则
        proxier.writeServiceRules(svcName, svc)
    }

    // 5. 应用iptables规则
    proxier.applyRules()
}
```

### 1.3 调度器在架构中的位置

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         调度器在Kubernetes中的位置                          │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   User/API Client                                                           │
│        │                                                                    │
│        ▼                                                                    │
│   ┌──────────────┐                                                          │
│   │  API Server  │ ◄──────────────────────────────────────────────┐        │
│   │              │                                                │        │
│   │  Watch API   │ ── Pod Create Event ───────────────────────────┼──┐     │
│   └──────────────┘                                                │  │     │
│          │                                                        │  │     │
│          │ etcd Write                                              │  │     │
│          ▼                                                        │  │     │
│   ┌──────────────┐                                                │  │     │
│   │     etcd     │                                                │  │     │
│   └──────────────┘                                                │  │     │
│                                                                   │  │     │
│   ╔═══════════════════════════════════════════════════════════╗   │  │     │
│   ║              ┌─────────────────────────┐                  ║   │  │     │
│   ║              │     kube-scheduler      │                  ║   │  │     │
│   ║              │                         │                  ║   │  │     │
│   ║  Watch ─────►│  ┌───────────────────┐  │                  ║   │  │     │
│   ║  Pending     │  │   Scheduling      │  │                  ║   │  │     │
│   ║  Pods        │  │   Queue           │  │                  ║   │  │     │
│   ║              │  └─────────┬─────────┘  │                  ║   │  │     │
│   ║              │            │            │                  ║   │  │     │
│   ║              │            ▼            │                  ║   │  │     │
│   ║              │  ┌───────────────────┐  │                  ║   │  │     │
│   ║              │  │  Scheduling Cycle │  │                  ║   │  │     │
│   ║              │  │  ┌─────────────┐  │  │                  ║   │  │     │
│   ║              │  │  │ Predicates  │  │  │  Filter Nodes    ║   │  │     │
│   ║              │  │  └─────────────┘  │  │                  ║   │  │     │
│   ║              │  │  ┌─────────────┐  │  │                  ║   │  │     │
│   ║              │  │  │ Priorities  │  │  │  Score Nodes     ║   │  │     │
│   ║              │  │  └─────────────┘  │  │                  ║   │  │     │
│   ║              │  │  ┌─────────────┐  │  │                  ║   │  │     │
│   ║              │  │  │    Bind     │  │  │  Select Node     ║   │  │     │
│   ║              │  │  └─────────────┘  │  │                  ║   │  │     │
│   ║              │  └───────────────────┘  │                  ║   │  │     │
│   ║              │            │            │                  ║   │  │     │
│   ║              └────────────┼────────────┘                  ║   │  │     │
│   ╚═══════════════════════════╪═══════════════════════════════╝   │  │     │
│                               │                                   │  │     │
│   Binding Response ◄──────────┘                                   │  │     │
│        │                                                          │  │     │
│        ▼                                                          │  │     │
│   ┌──────────────┐                                                │  │     │
│   │  API Server  │ ── Node Assignment ────────────────────────────┘  │     │
│   └──────────────┘                                                   │     │
│          │                                                           │     │
│          ▼                                                           │     │
│   ┌──────────────┐  ┌──────────────┐  ┌──────────────┐              │     │
│   │   kubelet    │  │   kubelet    │  │   kubelet    │              │     │
│   │   (Node 1)   │  │   (Node 2)   │  │   (Node 3)   │              │     │
│   │              │  │              │  │              │              │     │
│   │ ┌──────────┐ │  │ ┌──────────┐ │  │ ┌──────────┐ │              │     │
│   │ │  Pod A   │ │  │ │  Pod B   │ │  │ │  Pod C   │ │              │     │
│   │ └──────────┘ │  │ └──────────┘ │  │ └──────────┘ │              │     │
│   └──────────────┘  └──────────────┘  └──────────────┘              │     │
│                                                                     │     │
│   ═══════════════════════════════════════════════════════════════   │     │
│                        Scheduling Loop                              │     │
│   ─────────────────────────────────────────────────────────────     │     │
│                        Continuous Watch                             │     │
└─────────────────────────────────────────────────────────────────────────────┘
```

#### 1.3.1 调度器与其他组件的交互

```go
// kubernetes/pkg/scheduler/scheduler.go
// Scheduler结构体展示了与其他组件的交互

type Scheduler struct {
    // 内部缓存，存储节点和Pod信息
    Cache internalcache.Cache

    // 扩展器接口，用于外部调度器扩展
    Extenders []framework.Extender

    // 调度框架，包含所有插件
    Framework framework.Framework

    // 下一个Pod通道
    NextPod func() (*framework.QueuedPodInfo, error)

    // 错误处理函数
    Error func(*framework.QueuedPodInfo, error)

    // 调度器名称
    SchedulerName string

    // 关闭通道
    StopEverything <-chan struct{}

    // 调度配置
    Profiles []schedulerapi.KubeSchedulerProfile

    // 客户端
    client clientset.Interface
}

// scheduleOne执行一次完整的调度周期
func (sched *Scheduler) scheduleOne(ctx context.Context) {
    // 1. 从队列中获取下一个待调度的Pod
    podInfo, err := sched.NextPod()
    if err != nil {
        klog.ErrorS(err, "Error while retrieving next pod from scheduling queue")
        return
    }

    pod := podInfo.Pod

    // 2. 获取调度配置文件
    fw := sched.Profiles[podInfo.ProfileName()]

    // 3. 执行调度
    state := framework.NewCycleState()
    state.SetRecordPluginMetrics(rand.Intn(100) < pluginMetricsSamplePercent)

    // 4. 调度上下文
    schedulingCycleCtx, cancel := context.WithCancel(ctx)
    defer cancel()

    // 5. 执行调度算法
    scheduleResult, err := sched.SchedulePod(schedulingCycleCtx, fw, state, pod)
    if err != nil {
        // 调度失败处理
        sched.FailureHandler(schedulingCycleCtx, fw, podInfo, err, state)
        return
    }

    // 6. 绑定Pod到节点
    assumedPodInfo := podInfo.DeepCopy()
    assumedPod := assumedPodInfo.Pod
    err = sched.assume(schedulingCycleCtx, fw, assumedPod, scheduleResult.SuggestedHost)
    if err != nil {
        sched.FailureHandler(schedulingCycleCtx, fw, podInfo, err, state)
        return
    }

    // 7. 异步绑定
    go func() {
        bindingCycleCtx, cancel := context.WithCancel(ctx)
        defer cancel()

        // 执行Permit插件
        status := fw.RunPermitPlugins(bindingCycleCtx, state, assumedPod, scheduleResult.SuggestedHost)
        if !status.IsSuccess() {
            sched.handleBindingCycleError(bindingCycleCtx, assumedPodInfo, state, status)
            return
        }

        // 执行绑定
        err := sched.bind(bindingCycleCtx, fw, assumedPod, scheduleResult.SuggestedHost, state)
        if err != nil {
            sched.handleBindingCycleError(bindingCycleCtx, assumedPodInfo, state, framework.AsStatus(err))
            return
        }

        // 执行Reserve插件的Unreserve（清理）
        fw.RunReservePluginsUnreserve(bindingCycleCtx, state, assumedPod, scheduleResult.SuggestedHost)
    }()
}
```

---

## 2. kube-scheduler详细分析

### 2.1 调度框架设计

Kubernetes调度框架（Scheduling Framework）是在Kubernetes v1.15引入的插件架构，用于替代传统的调度器扩展模式。

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                        Kubernetes Scheduling Framework                      │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   Pod创建                                                                   │
│      │                                                                      │
│      ▼                                                                      │
│   ┌───────────────────────────────────────────────────────────────────┐    │
│   │                      Scheduling Queue                             │    │
│   │  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐          │    │
│   │  │ Active   │  │ Backoff  │  │ Unschedulable │ Pending    │          │    │
│   │  │ Queue    │  │ Queue    │  │ Queue         │ Pods       │          │    │
│   │  └──────────┘  └──────────┘  └──────────┘  └──────────┘          │    │
│   └───────────────────────────────────────────────────────────────────┘    │
│                                    │                                        │
│                                    ▼                                        │
│   ┌───────────────────────────────────────────────────────────────────┐    │
│   │                      Scheduling Cycle                             │    │
│   │                                                                   │    │
│   │   ┌──────────┐   ┌──────────┐   ┌──────────┐   ┌──────────┐      │    │
│   │   │  Sort    │──►│  Pre     │──►│  Filter  │──►│  Post    │      │    │
│   │   │  Queue   │   │  Filter  │   │          │   │  Filter  │      │    │
│   │   └──────────┘   └──────────┘   └──────────┘   └──────────┘      │    │
│   │                      (Predicates Phase)                          │    │
│   │                                                                   │    │
│   │   ┌──────────┐   ┌──────────┐   ┌──────────┐                     │    │
│   │   │  Pre     │──►│   Score  │──►│  Reserve │                     │    │
│   │   │  Score   │   │          │   │          │                     │    │
│   │   └──────────┘   └──────────┘   └──────────┘                     │    │
│   │                      (Priorities Phase)                          │    │
│   │                                                                   │    │
│   │                    ┌──────────┐                                  │    │
│   │                    │  Permit  │                                  │    │
│   │                    └──────────┘                                  │    │
│   │                          │                                        │    │
│   └──────────────────────────┼────────────────────────────────────────┘    │
│                              │                                              │
│                              ▼                                              │
│   ┌───────────────────────────────────────────────────────────────────┐    │
│   │                      Binding Cycle                                │    │
│   │                                                                   │    │
│   │   ┌──────────┐   ┌──────────┐   ┌──────────┐                     │    │
│   │   │  Pre     │──►│   Bind   │──►│  Post    │                     │    │
│   │   │  Bind    │   │          │   │  Bind    │                     │    │
│   │   └──────────┘   └──────────┘   └──────────┘                     │    │
│   │                                                                   │    │
│   └───────────────────────────────────────────────────────────────────┘    │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

#### 2.1.1 调度框架接口定义

```go
// kubernetes/pkg/scheduler/framework/interface.go
// 调度框架的核心接口定义

// Framework定义了调度框架的完整接口
type Framework interface {
    // PreEnqueue插件在Pod进入调度队列前执行
    RunPreEnqueuePlugins(ctx context.Context, pod *v1.Pod) *Status

    // EnqueueExtensions返回需要监听哪些事件的扩展点
    EnqueueExtensions

    // QueueSort插件定义Pod在调度队列中的排序
    QueueSortFunc() LessFunc

    // PreFilter插件在Filter前执行预处理
    RunPreFilterPlugins(ctx context.Context, state *CycleState, pod *v1.Pod) (*PreFilterResult, *Status)

    // Filter插件筛选合适的节点
    RunFilterPlugins(ctx context.Context, state *CycleState, pod *v1.Pod, nodeInfo *NodeInfo) PluginToStatus

    // PostFilter插件在Filter后执行
    RunPostFilterPlugins(ctx context.Context, state *CycleState, pod *v1.Pod, filteredNodeStatusMap NodeToStatusMap) (*PostFilterResult, *Status)

    // PreScore插件在Score前执行预处理
    RunPreScorePlugins(ctx context.Context, state *CycleState, pod *v1.Pod, nodes []*NodeInfo) *Status

    // Score插件为节点打分
    RunScorePlugins(ctx context.Context, state *CycleState, pod *v1.Pod, nodes []*NodeInfo) (PluginToNodeScores, *Status)

    // Reserve插件为Pod预留资源
    RunReservePluginsReserve(ctx context.Context, state *CycleState, pod *v1.Pod, nodeName string) *Status
    RunReservePluginsUnreserve(ctx context.Context, state *CycleState, pod *v1.Pod, nodeName string)

    // Permit插件阻止或延迟Pod绑定
    RunPermitPlugins(ctx context.Context, state *CycleState, pod *v1.Pod, nodeName string) *Status
    WaitOnPermit(ctx context.Context, pod *v1.Pod) *Status

    // PreBind插件在绑定前执行
    RunPreBindPlugins(ctx context.Context, state *CycleState, pod *v1.Pod, nodeName string) *Status

    // Bind插件执行Pod绑定
    RunBindPlugins(ctx context.Context, state *CycleState, pod *v1.Pod, nodeName string) *Status

    // PostBind插件在绑定后执行
    RunPostBindPlugins(ctx context.Context, state *CycleState, pod *v1.Pod, nodeName string)
}

// Plugin是所有调度插件的基础接口
type Plugin interface {
    Name() string
}

// 各扩展点的具体接口定义

// PreEnqueuePlugin在Pod进入调度队列前执行
type PreEnqueuePlugin interface {
    Plugin
    PreEnqueue(ctx context.Context, pod *v1.Pod) *Status
}

// QueueSortPlugin定义队列排序
type QueueSortPlugin interface {
    Plugin
    Less(a, b *QueuedPodInfo) bool
}

// PreFilterPlugin在Filter前执行
type PreFilterPlugin interface {
    Plugin
    PreFilter(ctx context.Context, state *CycleState, pod *v1.Pod) (*PreFilterResult, *Status)
    PreFilterExtensions() PreFilterExtensions
}

type PreFilterExtensions interface {
    AddPod(ctx context.Context, state *CycleState, podToSchedule *v1.Pod, podInfo *PodInfo, nodeInfo *NodeInfo) (*Status)
    RemovePod(ctx context.Context, state *CycleState, podToSchedule *v1.Pod, podInfo *PodInfo, nodeInfo *NodeInfo) (*Status)
}

// FilterPlugin筛选节点
type FilterPlugin interface {
    Plugin
    Filter(ctx context.Context, state *CycleState, pod *v1.Pod, nodeInfo *NodeInfo) *Status
}

// PostFilterPlugin在Filter后执行
type PostFilterPlugin interface {
    Plugin
    PostFilter(ctx context.Context, state *CycleState, pod *v1.Pod, filteredNodeStatusMap NodeToStatusMap) (*PostFilterResult, *Status)
}

// PreScorePlugin在Score前执行
type PreScorePlugin interface {
    Plugin
    PreScore(ctx context.Context, state *CycleState, pod *v1.Pod, nodes []*NodeInfo) *Status
}

// ScorePlugin为节点打分
type ScorePlugin interface {
    Plugin
    Score(ctx context.Context, state *CycleState, pod *v1.Pod, nodeName string) (int64, *Status)
    ScoreExtensions() ScoreExtensions
}

type ScoreExtensions interface {
    NormalizeScore(ctx context.Context, state *CycleState, pod *v1.Pod, scores NodeScoreList) *Status
}

// ReservePlugin预留资源
type ReservePlugin interface {
    Plugin
    Reserve(ctx context.Context, state *CycleState, pod *v1.Pod, nodeName string) *Status
    Unreserve(ctx context.Context, state *CycleState, pod *v1.Pod, nodeName string)
}

// PermitPlugin阻止或延迟绑定
type PermitPlugin interface {
    Plugin
    Permit(ctx context.Context, state *CycleState, pod *v1.Pod, nodeName string) (*Status, time.Duration)
}

// PreBindPlugin在绑定前执行
type PreBindPlugin interface {
    Plugin
    PreBind(ctx context.Context, state *CycleState, pod *v1.Pod, nodeName string) *Status
}

// BindPlugin执行绑定
type BindPlugin interface {
    Plugin
    Bind(ctx context.Context, state *CycleState, pod *v1.Pod, nodeName string) *Status
}

// PostBindPlugin在绑定后执行
type PostBindPlugin interface {
    Plugin
    PostBind(ctx context.Context, state *CycleState, pod *v1.Pod, nodeName string)
}
```

#### 2.1.2 框架实现核心代码

```go
// kubernetes/pkg/scheduler/framework/runtime/framework.go
// 调度框架的实现

type frameworkImpl struct {
    // 所有已注册的插件
    waitingPods           *waitingPodsMap
    snapshotSharedLister  framework.SharedLister
    captureProfileOutput  func(string, string, string)

    // 按扩展点组织的插件
    preEnqueuePlugins     map[string]framework.PreEnqueuePlugin
    queueSortPlugins      []framework.QueueSortPlugin
    preFilterPlugins      []framework.PreFilterPlugin
    filterPlugins         []framework.FilterPlugin
    postFilterPlugins     []framework.PostFilterPlugin
    preScorePlugins       []framework.PreScorePlugin
    scorePlugins          []framework.ScorePlugin
    reservePlugins        []framework.ReservePlugin
    permitPlugins         []framework.PermitPlugin
    preBindPlugins        []framework.PreBindPlugin
    bindPlugins           []framework.BindPlugin
    postBindPlugins       []framework.PostBindPlugin

    // 插件监控
    metricsRecorder       *metricsRecorder

    // 扩展器
    extenderInfo          map[string]framework.ExtenderInfo

    // 配置
    profileName           string
    percentageOfNodesToScore int32
    logger                *klog.Logger
}

// RunPreFilterPlugins执行所有PreFilter插件
func (f *frameworkImpl) RunPreFilterPlugins(ctx context.Context, state *framework.CycleState, pod *v1.Pod) (*framework.PreFilterResult, *framework.Status) {
    var result *framework.PreFilterResult
    var status *framework.Status

    for _, pl := range f.preFilterPlugins {
        // 记录插件执行开始
        ctxWithSpan := ctx
        if f.logger != nil && f.logger.V(5).Enabled() {
            ctxWithSpan, _ = framework.ContextWithSpan(ctxWithSpan, pl.Name())
        }

        // 执行插件
        r, s := f.runPreFilterPlugin(ctxWithSpan, pl, state, pod)

        // 记录指标
        f.metricsRecorder.observePluginDurationAsync(preFilter, pl.Name(), status.Code().String(), metrics.SinceInSeconds(start))

        if !s.IsSuccess() {
            s.SetPlugin(pl.Name())
            if s.Code() == framework.UnschedulableAndUnresolvable {
                return nil, s
            }
            return nil, s
        }

        // 合并结果
        if r != nil {
            if result == nil {
                result = r
            } else {
                result = result.Merge(r)
            }
        }
    }

    return result, nil
}

// RunFilterPluginsWithNominatedPods执行Filter插件，考虑抢占的Pod
func (f *frameworkImpl) RunFilterPluginsWithNominatedPods(ctx context.Context, state *framework.CycleState,
    pod *v1.Pod, info *framework.NodeInfo, nodes []*framework.NodeInfo) (map[string]*framework.Status, error) {

    // 克隆NodeInfo以避免修改原始数据
    nodeInfoCopy := info.Clone()

    // 移除已经被提名的Pod（可能被抢占的Pod）
    statusMap := make(map[string]*framework.Status)

    // 获取当前节点上被提名的Pod
    nominatedPods := f.getNominatedPods(pod, nodeInfoCopy.Node().Name)

    // 添加提名Pod到节点以模拟调度
    for _, p := range nominatedPods {
        nodeInfoCopy.AddPod(p)
    }

    // 执行Filter插件
    status := f.RunFilterPlugins(ctx, state, pod, nodeInfoCopy)

    return status, nil
}

// RunScorePlugins执行所有Score插件
func (f *frameworkImpl) RunScorePlugins(ctx context.Context, state *framework.CycleState,
    pod *v1.Pod, nodes []*framework.NodeInfo) (framework.PluginToNodeScores, *framework.Status) {

    numPlugins := len(f.scorePlugins) - state.SkipScorePlugins.Len()
    numNodes := len(nodes)

    // 初始化分数存储
    scoresMap := make(framework.PluginToNodeScores, numPlugins)

    pluginsMap := make(map[string]framework.ScorePlugin)
    for _, pl := range f.scorePlugins {
        pluginsMap[pl.Name()] = pl
    }

    ctx, cancel := context.WithCancel(ctx)
    defer cancel()

    errCh := parallelize.NewErrorChannel()

    // 并行执行所有插件的所有节点打分
    for _, pl := range f.scorePlugins {
        if state.SkipScorePlugins.Has(pl.Name()) {
            continue
        }

        // 为每个插件启动goroutine
        func(pl framework.ScorePlugin) {
            nodeScores := make(framework.NodeScoreList, len(nodes))

            for index, node := range nodes {
                nodeName := node.Node().Name
                s, status := f.runScorePlugin(ctx, pl, state, pod, nodeName)

                if !status.IsSuccess() {
                    errCh.SendErrorWithCancel(status.AsError(), cancel)
                    return
                }

                nodeScores[index] = framework.NodeScore{
                    Name:  nodeName,
                    Score: s,
                }
            }

            // 执行归一化
            if pl.ScoreExtensions() != nil {
                status := f.runScoreExtension(ctx, pl, state, pod, nodeScores)
                if !status.IsSuccess() {
                    errCh.SendErrorWithCancel(status.AsError(), cancel)
                    return
                }
            }

            // 应用权重
            weight := f.scorePluginWeight[pl.Name()]
            for i := range nodeScores {
                nodeScores[i].Score = nodeScores[i].Score * int64(weight)
            }

            scoresMap[pl.Name()] = nodeScores
        }(pl)
    }

    if err := errCh.ReceiveError(); err != nil {
        return nil, framework.AsStatus(fmt.Errorf("running Score plugins: %w", err))
    }

    return scoresMap, nil
}
```

### 2.2 调度队列

调度队列是调度器管理待调度Pod的核心组件。

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                          Scheduling Queue Architecture                      │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                         SchedulingQueue                             │   │
│  │                                                                     │   │
│  │   ┌─────────────────────────────────────────────────────────────┐  │   │
│  │   │                    Active Queue                              │  │   │
│  │   │  (基于堆实现的优先队列，按优先级排序)                         │  │   │
│  │   │                                                                │  │   │
│  │   │   Priority: High ──► Low                                       │  │   │
│  │   │                                                                     │  │   │
│  │   │   ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐  │  │   │
│  │   │   │Pod A    │  │Pod B    │  │Pod C    │  │Pod D    │  │Pod E    │  │  │   │
│  │   │   │Priority │  │Priority │  │Priority │  │Priority │  │Priority │  │  │   │
│  │   │   │1000     │  │900      │  │800      │  │700      │  │600      │  │  │   │
│  │   │   └─────────┘  └─────────┘  └─────────┘  └─────────┘  └─────────┘  │  │   │
│  │   └─────────────────────────────────────────────────────────────┘  │   │
│  │                              │                                      │   │
│  │                              ▼                                      │   │
│  │   ┌─────────────────────────────────────────────────────────────┐  │   │
│  │   │                   Backoff Queue                              │  │   │
│  │   │  (指数退避，失败的Pod暂时放入这里)                           │  │   │
│  │   │                                                                │  │   │
│  │   │   Backoff Time: Increasing                                     │  │   │
│  │   │                                                                     │  │   │
│  │   │   ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐          │  │   │
│  │   │   │Pod X    │  │Pod Y    │  │Pod Z    │  │Pod W    │          │  │   │
│  │   │   │Backoff  │  │Backoff  │  │Backoff  │  │Backoff  │          │  │   │
│  │   │   │10s      │  │20s      │  │40s      │  │80s      │          │  │   │
│  │   │   └─────────┘  └─────────┘  └─────────┘  └─────────┘          │  │   │
│  │   └─────────────────────────────────────────────────────────────┘  │   │
│  │                              │                                      │   │
│  │                              ▼                                      │   │
│  │   ┌─────────────────────────────────────────────────────────────┐  │   │
│  │   │              Unschedulable Pods Pool                         │  │   │
│  │   │  (等待集群状态变化的不可调度Pod)                             │  │   │
│  │   │                                                                │  │   │
│  │   │   ┌─────────┐  ┌─────────┐  ┌─────────┐  ┌─────────┐          │  │   │
│  │   │   │Pod M    │  │Pod N    │  │Pod O    │  │Pod P    │          │  │   │
│  │   │   │(资源不足)│  │(亲和性) │  │(污点)   │  │(选择器) │          │  │   │
│  │   │   └─────────┘  └─────────┘  └─────────┘  └─────────┘          │  │   │
│  │   └─────────────────────────────────────────────────────────────┘  │   │
│  │                                                                     │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

#### 2.2.1 调度队列实现

```go
// kubernetes/pkg/scheduler/internal/queue/scheduling_queue.go
// PriorityQueue实现

type PriorityQueue struct {
    // Pod内部信息映射
    podInfo map[string]*framework.QueuedPodInfo

    // 活跃队列 - 堆实现
    activeQ *heap.Heap

    // Pod Nominator，用于抢占
    nominator *nominator

    // 不可调度Pod队列
    unschedulablePods *UnschedulablePodsMap

    // 退避队列
    podBackoffQ *heap.Heap

    // 退避机制
    podBackoff *PodBackoff

    // 关闭标志
    closed bool

    // 事件处理器
    moveRequestCycle int64

    // 调度器配置
    cfg  config.SchedulerConfig

    // 队列活动锁
    lock sync.RWMutex

    // 条件变量
    cond *sync.Cond

    // 插件监控
    metricsRecorder metrics.MetricRecorder
}

// QueuedPodInfo存储Pod在队列中的信息
type QueuedPodInfo struct {
    Pod *v1.Pod

    // 时间戳
    Timestamp time.Time

    // 调度尝试次数
    Attempts int

    // 最后调度时间
    InitialAttemptTimestamp time.Time

    // 最后调度失败时间
    LastSchedulingTime time.Time

    // 不可调度原因
    UnschedulablePlugins sets.Set[string]

    // 集群事件
    PendingInQueueEvents *framework.ClusterEvent

    // 是否被激活
    Activated bool
}

// NewPriorityQueue创建新的优先队列
func NewPriorityQueue(
    lessFn framework.LessFunc,
    informerFactory informers.SharedInformerFactory,
    opts ...Option,
) (*PriorityQueue, error) {

    options := defaultPriorityQueueOptions
    for _, opt := range opts {
        opt(&options)
    }

    pq := &PriorityQueue{
        podInfo:              make(map[string]*framework.QueuedPodInfo),
        nominator:            newPodNominator(options.podLister),
        unschedulablePods:    newUnschedulablePodsMap(),
        activeQ:              heap.NewWithRecorder("activeQ", lessFn, options.metricsRecorder),
        podBackoffQ:          heap.NewWithRecorder("podBackoffQ", lessFn, options.metricsRecorder),
        podBackoff:           NewPodBackoff(options.podInitialBackoffDuration, options.podMaxBackoffDuration),
        waitingPods:          make(map[string]*waitingPod),
        metricsRecorder:      options.metricsRecorder,
        moveRequestCycle:     -1,
    }

    pq.cond = sync.NewCond(&pq.lock)

    return pq, nil
}

// Add将Pod添加到队列
func (p *PriorityQueue) Add(logger klog.Logger, pod *v1.Pod) error {
    p.lock.Lock()
    defer p.lock.Unlock()

    // 创建Pod信息
    pInfo := p.newQueuedPodInfo(pod, nil)

    // 添加到活跃队列
    if err := p.activeQ.Add(pInfo); err != nil {
        return fmt.Errorf("error adding pod %v to the active queue: %v", nsNameForPod(pod), err)
    }

    // 从不可调度集合中移除
    if p.unschedulablePods.get(pod) != nil {
        p.unschedulablePods.delete(pod, pInfo.Gated)
    }

    // 通知等待的调度器
    p.cond.Broadcast()

    p.podInfo[pInfo.Pod.Name] = pInfo

    logger.V(4).Info("Pod added to the active queue", "pod", klog.KObj(pod))

    return nil
}

// Pop从活跃队列获取下一个Pod
func (p *PriorityQueue) Pop() (*framework.QueuedPodInfo, error) {
    p.lock.Lock()
    defer p.lock.Unlock()

    for p.activeQ.Len() == 0 {
        if p.closed {
            return nil, fmt.Errorf("queue is closed")
        }
        p.cond.Wait()
    }

    // 获取队列头部Pod
    pInfo, err := p.activeQ.Pop()
    if err != nil {
        return nil, err
    }

    pInfo.Attempts++
    pInfo.LastSchedulingTime = time.Now()

    return pInfo, nil
}

// Done标记Pod调度完成
func (p *PriorityQueue) Done(pod *v1.Pod) {
    p.lock.Lock()
    defer p.lock.Unlock()

    // 从nominatedPods中移除
    p.nominator.deletePod(pod)
}

// Update更新队列中的Pod
func (p *PriorityQueue) Update(logger klog.Logger, oldPod, newPod *v1.Pod) error {
    p.lock.Lock()
    defer p.lock.Unlock()

    // 检查Pod是否已在队列中
    pInfo := p.podInfo[namespacedNameForPod(oldPod)]

    if pInfo != nil {
        // 更新Pod信息
        pInfo.Pod = newPod

        // 如果Pod在unschedulablePods中，需要更新
        if p.unschedulablePods.get(oldPod) != nil {
            p.unschedulablePods.addOrUpdate(pInfo)
        }

        // 如果Pod在backoffQ中，需要更新
        if p.podBackoffQ.Get(newPod) != nil {
            if err := p.podBackoffQ.Update(pInfo); err != nil {
                return err
            }
        }
    }

    return nil
}

// Delete从队列中删除Pod
func (p *PriorityQueue) Delete(pod *v1.Pod) error {
    p.lock.Lock()
    defer p.lock.Unlock()

    pInfo := p.podInfo[namespacedNameForPod(pod)]
    if pInfo == nil {
        return fmt.Errorf("pod %v not found in scheduling queue", namespacedNameForPod(pod))
    }

    // 从各个队列中删除
    p.activeQ.Delete(pInfo)
    p.podBackoffQ.Delete(pInfo)
    p.unschedulablePods.delete(pod, pInfo.Gated)

    delete(p.podInfo, namespacedNameForPod(pod))
    p.nominator.deletePod(pod)

    return nil
}

// MoveAllToActiveOrBackoffQueue将所有不可调度Pod移动到活跃或退避队列
func (p *PriorityQueue) MoveAllToActiveOrBackoffQueue(logger klog.Logger, event framework.ClusterEvent, oldObj, newObj interface{}, preCheck PreEnqueueCheck) {
    p.lock.Lock()
    defer p.lock.Unlock()

    unschedulablePods := make([]*framework.QueuedPodInfo, 0, len(p.unschedulablePods.podInfoMap))
    for _, pInfo := range p.unschedulablePods.podInfoMap {
        unschedulablePods = append(unschedulablePods, pInfo)
    }

    p.movePodsToActiveOrBackoffQueue(logger, unschedulablePods, event, oldObj, newObj, preCheck)
}

// AssignedPodAdded处理已分配Pod的添加事件
func (p *PriorityQueue) AssignedPodAdded(logger klog.Logger, pod *v1.Pod) {
    p.lock.Lock()
    defer p.lock.Unlock()

    // 从unschedulablePods中移除可以被调度的Pod
    p.movePodsToActiveOrBackoffQueue(logger, p.getUnschedulablePodsWithCrossTopologyAffinities(),
        framework.AssignedPodAdd, pod, nil, nil)
}

// NominatedPodsForNode返回指定节点上的提名Pod
func (p *PriorityQueue) NominatedPodsForNode(nodeName string) []*framework.PodInfo {
    p.lock.RLock()
    defer p.lock.RUnlock()

    return p.nominator.nominatedPodsForNode(nodeName)
}
```

### 2.3 预选阶段（Predicates）

预选阶段是调度过程的第一阶段，筛选出满足Pod基本需求的节点。

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         Predicates (Filter) Phase                          │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   Input: Pod + 所有可用节点                                                  │
│      │                                                                      │
│      ▼                                                                      │
│   ┌───────────────────────────────────────────────────────────────────┐    │
│   │                    Filter Pipeline                                 │    │
│   │                                                                   │    │
│   │  1. NodeName Filter      ──► 检查spec.nodeName匹配               │    │
│   │       │                                                           │    │
│   │       ▼                                                           │    │
│   │  2. NodeSelector Filter  ──► 检查labels匹配                       │    │
│   │       │                                                           │    │
│   │       ▼                                                           │    │
│   │  3. NodeAffinity Filter  ──► 检查亲和性约束                       │    │
│   │       │                                                           │    │
│   │       ▼                                                           │    │
│   │  4. Taints Filter        ──► 检查tolerations                      │    │
│   │       │                                                           │    │
│   │       ▼                                                           │    │
│   │  5. NodeResources Filter ──► 检查CPU/Memory/GPU资源               │    │
│   │       │                                                           │    │
│   │       ▼                                                           │    │
│   │  6. Volume Filter        ──► 检查卷约束                           │    │
│   │       │                                                           │    │
│   │       ▼                                                           │    │
│   │  7. Pod Affinity Filter  ──► 检查Pod间亲和/反亲和                 │    │
│   │       │                                                           │    │
│   │       ▼                                                           │    │
│   │  8. Topology Filter      ──► 检查拓扑分布约束                     │    │
│   │       │                                                           │    │
│   │       ▼                                                           │    │
│   │  9. Others...            ──► 其他过滤器                           │    │
│   │                                                                   │    │
│   └───────────────────────────────────────────────────────────────────┘    │
│                                    │                                        │
│                                    ▼                                        │
│   Output: 过滤后的节点列表（可能为空）                                       │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

#### 2.3.1 核心预选函数实现

```go
// kubernetes/pkg/scheduler/framework/plugins/nodename/node_name.go
// NodeName Filter实现

type NodeName struct {}

var _ framework.FilterPlugin = &NodeName{}

const (
    Name = "NodeName"
)

func (pl *NodeName) Name() string {
    return Name
}

func (pl *NodeName) Filter(ctx context.Context, state *framework.CycleState, pod *v1.Pod, nodeInfo *framework.NodeInfo) *framework.Status {
    if len(pod.Spec.NodeName) == 0 {
        return nil
    }

    if pod.Spec.NodeName != nodeInfo.Node().Name {
        return framework.NewStatus(framework.UnschedulableAndUnresolvable, ErrReason)
    }

    return nil
}

// kubernetes/pkg/scheduler/framework/plugins/nodeselector/node_selector.go
// NodeSelector Filter实现

type NodeSelector struct {}

func (pl *NodeSelector) Filter(ctx context.Context, state *framework.CycleState, pod *v1.Pod, nodeInfo *framework.NodeInfo) *framework.Status {
    if nodeInfo.Node() == nil {
        return framework.NewStatus(framework.Error, "node not found")
    }

    // 检查Pod的nodeSelector是否匹配节点的labels
    if !labelsMatches(nodeInfo.Node().Labels, pod.Spec.NodeSelector) {
        return framework.NewStatus(framework.UnschedulableAndUnresolvable, ErrReason)
    }

    return nil
}

func labelsMatches(nodeLabels, selector map[string]string) bool {
    for k, v := range selector {
        if nodeLabels[k] != v {
            return false
        }
    }
    return true
}

// kubernetes/pkg/scheduler/framework/plugins/tainttoleration/taint_toleration.go
// TaintToleration Filter实现

type TaintToleration struct {}

func (pl *TaintToleration) Filter(ctx context.Context, state *framework.CycleState, pod *v1.Pod, nodeInfo *framework.NodeInfo) *framework.Status {
    if nodeInfo.Node() == nil {
        return framework.NewStatus(framework.Error, "node not found")
    }

    // 检查Pod是否能容忍节点的所有污点
    filterPredicate := func(t *v1.Taint) bool {
        // 只检查NoSchedule和NoExecute效果的污点
        return t.Effect == v1.TaintEffectNoSchedule || t.Effect == v1.TaintEffectNoExecute
    }

    taints := getFilteredTaints(nodeInfo.Node().Spec.Taints, filterPredicate)

    if !v1helper.TolerationsTolerateTaintsWithFilter(pod.Spec.Tolerations, taints, filterPredicate) {
        return framework.NewStatus(framework.Unschedulable, ErrReasonNotMatch)
    }

    return nil
}

// kubernetes/pkg/scheduler/framework/plugins/noderesources/fit.go
// NodeResourcesFit Filter实现

// Fit定义了资源适配插件
type Fit struct {
    ignoredResources        sets.Set[string]
    ignoredResourceGroups   sets.Set[string]
    enableResourceLimitsEnforcement bool
}

// PreFilter计算Pod的资源需求
func (f *Fit) PreFilter(ctx context.Context, state *framework.CycleState, pod *v1.Pod) (*framework.PreFilterResult, *framework.Status) {
    // 计算Pod的请求资源
    req := computePodResourceRequest(pod)

    // 计算节点的资源限制
    if f.enableResourceLimitsEnforcement {
        limitReq := computePodResourceLimit(pod)
        state.Write(preFilterStateKey, &preFilterState{
            Requests:   req,
            Limits:     limitReq,
        })
    } else {
        state.Write(preFilterStateKey, &preFilterState{
            Requests:   req,
        })
    }

    // 返回需要检查的节点
    return &framework.PreFilterResult{
        NodeNames: f.getNodesWithSufficientResources(req),
    }, nil
}

// Filter检查节点是否有足够资源
func (f *Fit) Filter(ctx context.Context, state *framework.CycleState, pod *v1.Pod, nodeInfo *framework.NodeInfo) *framework.Status {
    // 获取PreFilter阶段计算的资源需求
    s, err := getPreFilterState(state)
    if err != nil {
        return framework.AsStatus(err)
    }

    // 计算节点可分配资源
    nodeInfoAvailable := nodeInfo.Allocatable

    // 检查每种资源
    insufficientResources := make([]InsufficientResource, 0)

    // 检查CPU
    if s.Requests.MilliCPU > 0 {
        availableCPU := nodeInfoAvailable.MilliCPU - nodeInfo.Requested.MilliCPU
        if availableCPU < s.Requests.MilliCPU {
            insufficientResources = append(insufficientResources, InsufficientResource{
                ResourceName: v1.ResourceCPU,
                Reason:       fmt.Sprintf("Insufficient cpu"),
                Requested:    s.Requests.MilliCPU,
                Used:         nodeInfo.Requested.MilliCPU,
                Capacity:     nodeInfoAvailable.MilliCPU,
            })
        }
    }

    // 检查Memory
    if s.Requests.Memory > 0 {
        availableMemory := nodeInfoAvailable.Memory - nodeInfo.Requested.Memory
        if availableMemory < s.Requests.Memory {
            insufficientResources = append(insufficientResources, InsufficientResource{
                ResourceName: v1.ResourceMemory,
                Reason:       fmt.Sprintf("Insufficient memory"),
                Requested:    s.Requests.Memory,
                Used:         nodeInfo.Requested.Memory,
                Capacity:     nodeInfoAvailable.Memory,
            })
        }
    }

    // 检查其他资源（GPU、HugePages等）
    for rName, rQuant := range s.Requests.ScalarResources {
        if rQuant <= 0 {
            continue
        }

        availableScalar := nodeInfoAvailable.ScalarResources[rName] - nodeInfo.Requested.ScalarResources[rName]
        if availableScalar < rQuant {
            insufficientResources = append(insufficientResources, InsufficientResource{
                ResourceName: rName,
                Reason:       fmt.Sprintf("Insufficient %s", rName),
                Requested:    rQuant,
                Used:         nodeInfo.Requested.ScalarResources[rName],
                Capacity:     nodeInfoAvailable.ScalarResources[rName],
            })
        }
    }

    if len(insufficientResources) > 0 {
        // 构建错误信息
        failureReasons := make([]string, 0, len(insufficientResources))
        for _, r := range insufficientResources {
            failureReasons = append(failureReasons, r.Reason)
        }
        return framework.NewStatus(framework.Unschedulable, failureReasons...)
    }

    return nil
}

// computePodResourceRequest计算Pod的资源请求
func computePodResourceRequest(pod *v1.Pod) *framework.Resource {
    result := &framework.Resource{}

    for _, container := range pod.Spec.Containers {
        result.Add(container.Resources.Requests)
    }

    // 取init容器和常规容器的最大值
    for _, container := range pod.Spec.InitContainers {
        result.SetMaxResource(container.Resources.Requests)
    }

    // 添加overhead
    if pod.Spec.Overhead != nil {
        result.Add(pod.Spec.Overhead)
    }

    return result
}
```


#### 2.3.2 Pod亲和性与反亲和性过滤

```go
// kubernetes/pkg/scheduler/framework/plugins/interpodaffinity/filtering.go
// InterPodAffinity Filter实现

func (pl *InterPodAffinity) Filter(ctx context.Context, state *framework.CycleState, pod *v1.Pod, nodeInfo *framework.NodeInfo) *framework.Status {
    if nodeInfo.Node() == nil {
        return framework.NewStatus(framework.Error, "node not found")
    }

    // 获取PreFilter阶段计算的状态
    s, err := getPreFilterState(state)
    if err != nil {
        return framework.AsStatus(err)
    }

    // 检查PodAffinity
    if s.hasAffinityRequirements {
        // 检查节点是否满足亲和性要求
        if !satisfiesAffinityRequirements(pod, nodeInfo, s) {
            return framework.NewStatus(framework.Unschedulable, ErrReasonAffinityRulesNotMatch)
        }
    }

    // 检查PodAntiAffinity
    if s.hasAntiAffinityRequirements {
        // 检查节点是否违反反亲和性要求
        if violatesAntiAffinityRequirements(pod, nodeInfo, s) {
            return framework.NewStatus(framework.Unschedulable, ErrReasonAntiAffinityRulesNotMatch)
        }
    }

    return nil
}

// satisfiesAffinityRequirements检查是否满足亲和性要求
func satisfiesAffinityRequirements(pod *v1.Pod, nodeInfo *framework.NodeInfo, state *preFilterState) bool {
    // 遍历所有亲和性条款
    for _, term := range state.affinity.PodAffinity.RequiredDuringSchedulingIgnoredDuringExecution {
        // 检查节点上是否有匹配的Pod
        matched := false
        for _, existingPod := range nodeInfo.Pods {
            if podMatchesAffinityTerm(existingPod, pod, &term) {
                matched = true
                break
            }
        }

        if !matched {
            return false
        }
    }

    return true
}

// violatesAntiAffinityRequirements检查是否违反反亲和性要求
func violatesAntiAffinityRequirements(pod *v1.Pod, nodeInfo *framework.NodeInfo, state *preFilterState) bool {
    // 检查Pod级别的反亲和性
    for _, term := range state.affinity.PodAntiAffinity.RequiredDuringSchedulingIgnoredDuringExecution {
        // 检查节点上是否有违反反亲和性的Pod
        for _, existingPod := range nodeInfo.Pods {
            if podMatchesAntiAffinityTerm(existingPod, pod, &term) {
                return true
            }
        }
    }

    // 检查其他Pod的反亲和性（对称检查）
    for _, existingPod := range nodeInfo.Pods {
        existingPodAffinity := existingPod.Spec.Affinity
        if existingPodAffinity == nil || existingPodAffinity.PodAntiAffinity == nil {
            continue
        }

        for _, term := range existingPodAffinity.PodAntiAffinity.RequiredDuringSchedulingIgnoredDuringExecution {
            if podMatchesAntiAffinityTermSymmetric(pod, existingPod, &term) {
                return true
            }
        }
    }

    return false
}
```

### 2.4 优选阶段（Priorities）

优选阶段为通过预选的节点打分，选出最优节点。

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                        Priorities (Score) Phase                             │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   Input: 通过预选的节点列表                                                   │
│      │                                                                      │
│      ▼                                                                      │
│   ┌───────────────────────────────────────────────────────────────────┐     │
│   │                     Score Pipeline                                 │    │
│   │                                                                   │    │
│   │  1. NodeResourcesFit      ──► 资源利用率平衡 (0-100)              │    │
│   │       分数 = (容量 - 请求) / 容量 * 100                           │    │
│   │                                                                   │    │
│   │  2. NodeResourcesBalancedAllocation ──► 资源类型间平衡            │    │
│   │       分数 = variance(cpu%, memory%)                              │    │
│   │                                                                   │    │
│   │  3. ImageLocality       ──► 镜像本地存在性                        │    │
│   │       分数 = 本地镜像大小 / 总镜像大小 * 100                       │    │
│   │                                                                   │    │
│   │  4. InterPodAffinity    ──► Pod亲和性满足程度                     │    │
│   │       分数 = 匹配的亲和性Pod数量                                  │    │
│   │                                                                   │    │
│   │  5. PodTopologySpread   ──► 拓扑分布均匀性                        │    │
│   │       分数 = 基于skew的分布评分                                   │    │
│   │                                                                   │    │
│   │  6. SelectorSpread      ──► 服务/RS/Pod分散性                     │    │
│   │       分数 = 节点上同服务Pod数量越少越好                          │    │
│   │                                                                   │    │
│   │  7. TaintToleration     ──► 污点容忍匹配度                        │    │
│   │       分数 = PreferNoSchedule污点越少越好                         │    │
│   │                                                                   │    │
│   │  8. NodeAffinity        ──► 节点亲和性匹配度                      │    │
│   │       分数 = 基于preferred规则的匹配程度                          │    │
│   │                                                                   │    │
│   │  9. LeastAllocated      ──► 资源分配最少                          │    │
│   │       分数 = (容量 - 已用 - 请求) / 容量 * 100                    │    │
│   │                                                                   │    │
│   │  10. MostAllocated      ──► 资源分配最多                          │    │
│   │       分数 = (已用 + 请求) / 容量 * 100                           │    │
│   │                                                                   │    │
│   │  11. RequestedToCapacityRatio ──► 请求容量比率                    │    │
│   │       自定义评分函数                                              │    │
│   │                                                                   │    │
│   └───────────────────────────────────────────────────────────────────┘    │
│                                    │                                        │
│                                    ▼                                        │
│   Output: 节点分数列表，选择最高分节点                                         │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

#### 2.4.1 优选函数核心实现

```go
// kubernetes/pkg/scheduler/framework/plugins/noderesources/allocated.go
// NodeResourcesAllocated（LeastAllocated）评分实现

type LeastAllocated struct {
    resources []schedulingconfig.ResourceSpec
    handle    framework.Handle
}

func (la *LeastAllocated) Score(ctx context.Context, state *framework.CycleState, pod *v1.Pod, nodeName string) (int64, *framework.Status) {
    nodeInfo, err := la.handle.SnapshotSharedLister().NodeInfos().Get(nodeName)
    if err != nil {
        return 0, framework.AsStatus(fmt.Errorf("getting node %q from Snapshot: %w", nodeName, err))
    }

    // 获取节点资源容量
    allocatable := nodeInfo.Allocatable
    if allocatable.MilliCPU == 0 || allocatable.Memory == 0 {
        return 0, nil
    }

    // 获取Pod资源请求
    requested := calculatePodResourceRequest(pod, la.resources)

    // 计算分数：资源剩余越多分数越高
    var score int64
    for _, resource := range la.resources {
        switch resource.Name {
        case v1.ResourceCPU:
            // CPU分数计算
            fraction := (allocatable.MilliCPU - nodeInfo.Requested.MilliCPU - requested.MilliCPU) * 100 / allocatable.MilliCPU
            score += fraction * int64(resource.Weight) / framework.MaxNodeScore

        case v1.ResourceMemory:
            // Memory分数计算
            fraction := (allocatable.Memory - nodeInfo.Requested.Memory - requested.Memory) * 100 / allocatable.Memory
            score += fraction * int64(resource.Weight) / framework.MaxNodeScore
        }
    }

    return score, nil
}

// kubernetes/pkg/scheduler/framework/plugins/noderesources/balanced_allocation.go
// NodeResourcesBalancedAllocation评分实现

type BalancedAllocation struct {
    resources []schedulingconfig.ResourceSpec
    handle    framework.Handle
}

func (ba *BalancedAllocation) Score(ctx context.Context, state *framework.CycleState, pod *v1.Pod, nodeName string) (int64, *framework.Status) {
    nodeInfo, err := ba.handle.SnapshotSharedLister().NodeInfos().Get(nodeName)
    if err != nil {
        return 0, framework.AsStatus(fmt.Errorf("getting node %q from Snapshot: %w", nodeName, err))
    }

    // 获取请求资源
    requested := calculatePodResourceRequest(pod, ba.resources)

    // 计算分配后的资源使用率
    allocatable := nodeInfo.Allocatable

    var resourceFractions []float64
    for _, resource := range ba.resources {
        var fraction float64
        switch resource.Name {
        case v1.ResourceCPU:
            fraction = float64(nodeInfo.Requested.MilliCPU+requested.MilliCPU) / float64(allocatable.MilliCPU)
        case v1.ResourceMemory:
            fraction = float64(nodeInfo.Requested.Memory+requested.Memory) / float64(allocatable.Memory)
        }
        resourceFractions = append(resourceFractions, fraction)
    }

    // 计算标准差，标准差越小说明资源分配越均衡
    mean := 0.0
    for _, f := range resourceFractions {
        mean += f
    }
    mean /= float64(len(resourceFractions))

    variance := 0.0
    for _, f := range resourceFractions {
        variance += (f - mean) * (f - mean)
    }
    variance /= float64(len(resourceFractions))

    stdDev := math.Sqrt(variance)

    // 将标准差转换为分数 (0-100)
    // 标准差越小，分数越高
    score := int64((1 - stdDev) * float64(framework.MaxNodeScore))

    return score, nil
}

// kubernetes/pkg/scheduler/framework/plugins/interpodaffinity/scoring.go
// InterPodAffinity评分实现

type Score struct {
    handle framework.Handle
}

func (pl *Score) Score(ctx context.Context, state *framework.CycleState, pod *v1.Pod, nodeName string) (int64, *framework.Status) {
    nodeInfo, err := pl.handle.SnapshotSharedLister().NodeInfos().Get(nodeName)
    if err != nil {
        return 0, framework.AsStatus(fmt.Errorf("getting node %q from Snapshot: %w", nodeName, err))
    }

    // 获取PreFilter阶段计算的状态
    s, err := getPreFilterState(state)
    if err != nil {
        return 0, framework.AsStatus(err)
    }

    // 获取节点拓扑域
    topologyScore := int64(0)

    // 处理PodAffinity软约束
    if s.affinity.PodAffinity != nil && s.affinity.PodAffinity.PreferredDuringSchedulingIgnoredDuringExecution != nil {
        for _, preferredTerm := range s.affinity.PodAffinity.PreferredDuringSchedulingIgnoredDuringExecution {
            // 计算匹配权重
            weight := preferredTerm.Weight
            matchingPods := countMatchingPods(pod, nodeInfo, &preferredTerm.PodAffinityTerm)
            topologyScore += int64(weight) * int64(matchingPods)
        }
    }

    // 处理PodAntiAffinity软约束
    if s.affinity.PodAntiAffinity != nil && s.affinity.PodAntiAffinity.PreferredDuringSchedulingIgnoredDuringExecution != nil {
        for _, preferredTerm := range s.affinity.PodAntiAffinity.PreferredDuringSchedulingIgnoredDuringExecution {
            weight := preferredTerm.Weight
            matchingPods := countMatchingAntiAffinityPods(pod, nodeInfo, &preferredTerm.PodAffinityTerm)
            // 反亲和性：匹配的Pod越多，分数越低
            topologyScore -= int64(weight) * int64(matchingPods)
        }
    }

    // 归一化分数到0-100范围
    if topologyScore > framework.MaxNodeScore {
        topologyScore = framework.MaxNodeScore
    }
    if topologyScore < 0 {
        topologyScore = 0
    }

    return topologyScore, nil
}

// kubernetes/pkg/scheduler/framework/plugins/podtopologyspread/scoring.go
// PodTopologySpread评分实现

type Score struct {
    handle                    framework.Handle
    defaultConstraints        []v1.TopologySpreadConstraint
    defaultingType            config.PodTopologySpreadConstraintDefaulting
}

func (pl *Score) Score(ctx context.Context, state *framework.CycleState, pod *v1.Pod, nodeName string) (int64, *framework.Status) {
    nodeInfo, err := pl.handle.SnapshotSharedLister().NodeInfos().Get(nodeName)
    if err != nil {
        return 0, framework.AsStatus(fmt.Errorf("getting node %q from Snapshot: %w", nodeName, err))
    }

    node := nodeInfo.Node()
    if node == nil {
        return 0, framework.NewStatus(framework.Error, fmt.Sprintf("node not found in NodeInfo: %q", nodeName))
    }

    // 获取PreFilter阶段计算的状态
    s, err := getPreFilterState(state)
    if err != nil {
        return 0, framework.AsStatus(err)
    }

    if s == nil || len(s.Constraints) == 0 {
        return 0, nil
    }

    // 计算拓扑分布分数
    var totalScore float64

    for _, constraint := range s.Constraints {
        // 获取节点在该拓扑域的值
        topologyValue, ok := node.Labels[constraint.TopologyKey]
        if !ok {
            // 节点没有该拓扑标签，给予最低分
            totalScore += 0
            continue
        }

        // 获取该拓扑域的Pod分布情况
        pair := topologyPair{key: constraint.TopologyKey, value: topologyValue}
        count := s.TopologyPairToPodCounts[pair]

        // 计算skew（偏差）
        // skew = count - minCount
        skew := count - s.MinPods

        // 根据skew计算分数
        // skew越小（分布越均匀），分数越高
        if skew == 0 {
            totalScore += float64(framework.MaxNodeScore)
        } else if skew == 1 {
            totalScore += float64(framework.MaxNodeScore) * 0.5
        } else {
            totalScore += 0
        }
    }

    // 计算平均分
    finalScore := totalScore / float64(len(s.Constraints))

    return int64(finalScore), nil
}
```

#### 2.4.2 分数归一化

```go
// kubernetes/pkg/scheduler/framework/plugins/noderesources/score_normalization.go
// 分数归一化实现

func normalizeScore(scores framework.NodeScoreList) {
    // 找到最高分和最低分
    var highest int64 = -math.MaxInt64
    var lowest int64 = math.MaxInt64

    for _, score := range scores {
        if score.Score > highest {
            highest = score.Score
        }
        if score.Score < lowest {
            lowest = score.Score
        }
    }

    // 如果所有分数相同，全部设为最高分
    if highest == lowest {
        for i := range scores {
            scores[i].Score = framework.MaxNodeScore
        }
        return
    }

    // 线性归一化到0-100
    for i := range scores {
        score := scores[i].Score
        normalized := (score - lowest) * framework.MaxNodeScore / (highest - lowest)
        scores[i].Score = normalized
    }
}
```

### 2.5 调度算法插件机制

Kubernetes调度器使用插件机制来扩展调度功能。

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                     Scheduling Plugin Registry                              │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                      In-tree Plugins                                │   │
│  │  ┌─────────────────┬────────────────────────────────────────────┐  │   │
│  │  │ Filter Plugins  │                                            │  │   │
│  │  │ (Predicates)    │  - NodeName                                │  │   │
│  │  │                 │  - NodeSelector                            │  │   │
│  │  │                 │  - NodeAffinity                            │  │   │
│  │  │                 │  - NodeResourcesFit                        │  │   │
│  │  │                 │  - NodeResourcesFitWithOptions             │  │   │
│  │  │                 │  - TaintToleration                         │  │   │
│  │  │                 │  - PodTopologySpread                       │  │   │
│  │  │                 │  - InterPodAffinity                        │  │   │
│  │  │                 │  - VolumeBinding                           │  │   │
│  │  │                 │  - VolumeZone                              │  │   │
│  │  │                 │  - VolumeRestrictions                      │  │   │
│  │  │                 │  - NodeUnschedulable                       │  │   │
│  │  │                 │  - NodeCondition                           │  │   │
│  │  │                 │  - NodePorts                               │  │   │
│  │  │                 │  - NodeLabels                              │  │   │
│  │  │                 │  - NodePreferAvoidPods                     │  │   │
│  │  │                 │  - CSINode                                 │  │   │
│  │  └─────────────────┴────────────────────────────────────────────┘  │   │
│  │  ┌─────────────────┬────────────────────────────────────────────┐  │   │
│  │  │ Score Plugins   │                                            │  │   │
│  │  │ (Priorities)    │  - NodeResourcesBalancedAllocation         │  │   │
│  │  │                 │  - NodeResourcesFit                        │  │   │
│  │  │                 │  - ImageLocality                           │  │   │
│  │  │                 │  - InterPodAffinity                        │  │   │
│  │  │                 │  - PodTopologySpread                       │  │   │
│  │  │                 │  - SelectorSpread                          │  │   │
│  │  │                 │  - TaintToleration                         │  │   │
│  │  │                 │  - NodeAffinity                            │  │   │
│  │  │                 │  - RequestedToCapacityRatio                │  │   │
│  │  └─────────────────┴────────────────────────────────────────────┘  │   │
│  │  ┌─────────────────┬────────────────────────────────────────────┐  │   │
│  │  │ Reserve Plugins │  - VolumeBinding                           │  │   │
│  │  │ Permit Plugins  │  - (custom implementation)                 │  │   │
│  │  │ Bind Plugins    │  - DefaultBinder                           │  │   │
│  │  └─────────────────┴────────────────────────────────────────────┘  │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                     Out-of-tree Plugins                             │   │
│  │                                                                     │   │
│  │  - 通过Webhook扩展的调度器扩展器                                     │   │
│  │  - 自定义开发的调度框架插件                                          │   │
│  │  - 多调度器部署                                                      │   │
│  │                                                                     │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

#### 2.5.1 插件注册机制

```go
// kubernetes/pkg/scheduler/framework/plugins/registry.go
// 插件注册表

func NewInTreeRegistry() runtime.Registry {
    return runtime.Registry{
        // Filter Plugins
        selectorspread.Name:              selectorspread.New,
        podtopologyspread.Name:           podtopologyspread.New,
        nodeports.Name:                   nodeports.New,
        nodeaffinity.Name:                nodeaffinity.New,
        nodeunschedulable.Name:           nodeunschedulable.New,
        nodelabel.Name:                   nodelabel.New,
        nodename.Name:                    nodename.New,
        nodepreferavoidpods.Name:         nodepreferavoidpods.New,
        nodeaffinity.Name:                nodeaffinity.New,
        nodevolumelimits.Name:            nodevolumelimits.NewCSILimits,
        noderesources.Name:               noderesources.NewFit,
        nodeports.Name:                   nodeports.New,
        noderesources.Name:               noderesources.NewBalancedAllocation,
        volumebinding.Name:               volumebinding.New,
        volumezone.Name:                  volumezone.New,
        volumerestrictions.Name:          volumerestrictions.New,
        interpodaffinity.Name:            interpodaffinity.New,
        tainttoleration.Name:             tainttoleration.New,
        csinode.Name:                     csinode.New,

        // Score Plugins
        imagelocality.Name:               imagelocality.New,
        interpodaffinity.Name:            interpodaffinity.New,
        nodeaffinity.Name:                nodeaffinity.New,
        noderesources.Name:               noderesources.NewLeastAllocated,
        noderesources.Name:               noderesources.NewMostAllocated,
        noderesources.Name:               noderesources.NewRequestedToCapacityRatio,
        podtopologyspread.Name:           podtopologyspread.New,
        selectorspread.Name:              selectorspread.New,
        tainttoleration.Name:             tainttoleration.New,

        // Reserve Plugins
        volumebinding.Name:               volumebinding.New,
        dynamicresources.Name:            dynamicresources.New,

        // Permit Plugins
        // (用户自定义实现)

        // Bind Plugins
        defaultbinder.Name:               defaultbinder.New,
    }
}

// kubernetes/pkg/scheduler/scheduler.go
// 调度器创建时加载插件

func New(ctx context.Context,
    client clientset.Interface,
    informerFactory informers.SharedInformerFactory,
    dynInformerFactory dynamicinformer.DynamicSharedInformerFactory,
    recorderFactory profile.RecorderFactory,
    opts ...Option,
) (*Scheduler, error) {

    // 创建默认配置
    options := defaultSchedulerOptions
    for _, opt := range opts {
        opt(&options)
    }

    // 创建调度器配置
    profiles, err := profiles.New(ctx,
        options.profiles,
        options.frameworkCapturer,
        recorderFactory,
        options.extenders,
        options.applyDefaultProfile,
    )
    if err != nil {
        return nil, fmt.Errorf("initializing profiles: %w", err)
    }

    // 创建调度队列
    podQueue := internalqueue.NewSchedulingQueue(
        profiles[options.profiles[0].SchedulerName].QueueSortFunc(),
        informerFactory,
        internalqueue.WithPodInitialBackoffDuration(options.podInitialBackoffDuration),
        internalqueue.WithPodMaxBackoffDuration(options.podMaxBackoffDuration),
    )

    // 创建调度器实例
    sched := &Scheduler{
        Profiles:           profiles,
        NextPod:            podQueue.Pop,
        Error:              makeDefaultErrorFunc(client, podQueue),
        StopEverything:     stopEverything,
        SchedulingQueue:    podQueue,
        client:             client,
    }

    return sched, nil
}
```

---

## 3. 调度策略详解

### 3.1 NodeName/NodeSelector

NodeName是最简单的节点选择方式，直接指定节点名称。

```yaml
# 直接指定节点名称
apiVersion: v1
kind: Pod
metadata:
  name: nginx-nodename
spec:
  containers:
  - name: nginx
    image: nginx
  nodeName: node-1  # 直接绑定到node-1
```

NodeSelector通过标签匹配选择节点。

```yaml
# 使用NodeSelector
apiVersion: v1
kind: Pod
metadata:
  name: nginx-nodeselector
spec:
  containers:
  - name: nginx
    image: nginx
  nodeSelector:
    disktype: ssd
    environment: production
```

```go
// NodeSelector实现原理
func nodeSelectorMatches(nodeLabels, selector map[string]string) bool {
    for k, v := range selector {
        if nodeLabels[k] != v {
            return false
        }
    }
    return true
}
```

### 3.2 Affinity/Anti-affinity

节点亲和性和Pod亲和性提供了更灵活的调度控制。

```yaml
# 节点亲和性 - 软约束
apiVersion: v1
kind: Pod
metadata:
  name: with-node-affinity
spec:
  affinity:
    nodeAffinity:
      requiredDuringSchedulingIgnoredDuringExecution:
        nodeSelectorTerms:
        - matchExpressions:
          - key: kubernetes.io/os
            operator: In
            values:
            - linux
      preferredDuringSchedulingIgnoredDuringExecution:
      - weight: 1
        preference:
          matchExpressions:
          - key: zone
            operator: In
            values:
            - zone-a
  containers:
  - name: nginx
    image: nginx
```

```yaml
# Pod亲和性 - 与其他Pod在一起
apiVersion: v1
kind: Pod
metadata:
  name: with-pod-affinity
spec:
  affinity:
    podAffinity:
      requiredDuringSchedulingIgnoredDuringExecution:
      - labelSelector:
          matchExpressions:
          - key: app
            operator: In
            values:
            - cache
        topologyKey: kubernetes.io/hostname
    podAntiAffinity:
      preferredDuringSchedulingIgnoredDuringExecution:
      - weight: 100
        podAffinityTerm:
          labelSelector:
            matchExpressions:
            - key: app
              operator: In
              values:
              - frontend
          topologyKey: kubernetes.io/hostname
  containers:
  - name: nginx
    image: nginx
```

### 3.3 Taints/Tolerations

Taints用于标记节点的不希望被调度的属性，Tolerations用于容忍这些属性。

```bash
# 为节点添加污点
kubectl taint nodes node1 key1=value1:NoSchedule
kubectl taint nodes node1 key1=value1:NoExecute
kubectl taint nodes node1 key2=value2:PreferNoSchedule

# 移除污点
kubectl taint nodes node1 key1=value1:NoSchedule-
```

```yaml
# Pod容忍污点
apiVersion: v1
kind: Pod
metadata:
  name: with-tolerations
spec:
  tolerations:
  # 完全匹配污点
  - key: "key1"
    operator: "Equal"
    value: "value1"
    effect: "NoSchedule"
  # 仅匹配key和effect
  - key: "key1"
    operator: "Exists"
    effect: "NoExecute"
    tolerationSeconds: 3600
  # 匹配所有污点
  - operator: "Exists"
  containers:
  - name: nginx
    image: nginx
```

### 3.4 Pod拓扑分布约束

PodTopologySpread确保Pod在拓扑域内均匀分布。

```yaml
# Pod拓扑分布约束
apiVersion: apps/v1
kind: Deployment
metadata:
  name: web-deployment
spec:
  replicas: 6
  selector:
    matchLabels:
      app: web
  template:
    metadata:
      labels:
        app: web
    spec:
      topologySpreadConstraints:
      - maxSkew: 1
        topologyKey: topology.kubernetes.io/zone
        whenUnsatisfiable: DoNotSchedule
        labelSelector:
          matchLabels:
            app: web
      - maxSkew: 1
        topologyKey: kubernetes.io/hostname
        whenUnsatisfiable: ScheduleAnyway
        labelSelector:
          matchLabels:
            app: web
      containers:
      - name: nginx
        image: nginx
```

**拓扑分布约束关键参数：**

| 参数 | 说明 | 值 |
|------|------|-----|
| maxSkew | 允许的最大偏差 | 整数，如1、2 |
| topologyKey | 拓扑域标签键 | 如topology.kubernetes.io/zone |
| whenUnsatisfiable | 不满足时的处理方式 | DoNotSchedule / ScheduleAnyway |
| labelSelector | 选择要统计的Pod | 标签选择器 |
| minDomains | 最小拓扑域数量（可选） | 整数 |

### 3.5 资源请求与限制

资源管理是调度决策的核心因素。

```yaml
# 资源请求与限制
apiVersion: v1
kind: Pod
metadata:
  name: resource-demo
spec:
  containers:
  - name: nginx
    image: nginx
    resources:
      requests:
        cpu: "100m"           # 100 millicores
        memory: "128Mi"       # 128 MiB
        ephemeral-storage: "1Gi"
        nvidia.com/gpu: 1     # 请求1个GPU
      limits:
        cpu: "500m"           # 500 millicores
        memory: "512Mi"       # 512 MiB
        ephemeral-storage: "2Gi"
        nvidia.com/gpu: 1     # GPU限制通常等于请求
```

**资源类型说明：**

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                           Kubernetes Resources                              │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  计算资源：                                                                  │
│  ├── CPU (可压缩资源)                                                        │
│  │   ├── 单位：millicores (m)                                                │
│  │   ├── 1 CPU = 1000m = 1 vCPU (云) / 1 hyperthread (裸机)                 │
│  │   └── 调度基于requests，运行时基于limits限制                              │
│  │                                                                           │
│  ├── Memory (不可压缩资源)                                                   │
│  │   ├── 单位：bytes                                                         │
│  │   ├── E, P, T, G, M, k (1000进制)                                         │
│  │   ├── Ei, Pi, Ti, Gi, Mi, Ki (1024进制)                                   │
│  │   └── 超出limits时Pod会被OOMKilled                                       │
│  │                                                                           │
│  └── GPU (扩展资源)                                                          │
│      ├── 设备插件注册 (如nvidia.com/gpu)                                     │
│      ├── 调度时按整数分配                                                    │
│      └── 不支持超配                                                          │
│                                                                             │
│  存储资源：                                                                  │
│  ├── ephemeral-storage                                                       │
│  │   └── 临时存储（容器层、emptyDir、日志）                                  │
│  └── 持久卷（通过存储类动态配置）                                            │
│                                                                             │
│  其他扩展资源：                                                              │
│  ├── 自定义资源 (如example.com/custom-resource)                              │
│  └── 设备插件暴露的设备                                                      │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 4. 源码级分析

### 4.1 scheduler.go核心代码

```go
// kubernetes/pkg/scheduler/scheduler.go
// 调度器核心实现

package scheduler

import (
    "context"
    "fmt"
    "time"

    v1 "k8s.io/api/core/v1"
    metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
    "k8s.io/apimachinery/pkg/util/wait"
    "k8s.io/client-go/informers"
    "k8s.io/client-go/kubernetes"
    "k8s.io/klog/v2"

    "k8s.io/kubernetes/pkg/scheduler/framework"
    internalcache "k8s.io/kubernetes/pkg/scheduler/internal/cache"
    internalqueue "k8s.io/kubernetes/pkg/scheduler/internal/queue"
    "k8s.io/kubernetes/pkg/scheduler/profile"
)

// Scheduler是Kubernetes调度器的核心结构
type Scheduler struct {
    // 调度框架实例，包含所有插件
    Profiles map[string]framework.Framework

    // 下一个Pod的获取函数
    NextPod func() (*framework.QueuedPodInfo, error)

    // 错误处理函数
    Error func(*framework.QueuedPodInfo, error)

    // 调度器名称
    SchedulerName string

    // 关闭信号
    StopEverything <-chan struct{}

    // 调度队列
    SchedulingQueue internalqueue.SchedulingQueue

    // 内部缓存
    Cache internalcache.Cache

    // 扩展器
    Extenders []framework.Extender

    // 客户端
    client kubernetes.Interface
}

// Run启动调度器的主循环
func (sched *Scheduler) Run(ctx context.Context) {
    sched.SchedulingQueue.Run(logger)

    // 等待所有缓存同步
    wait.UntilWithContext(ctx, func(ctx context.Context) {
        sched.scheduleOne(ctx)
    }, 0)

    sched.SchedulingQueue.Close()
}

// scheduleOne执行一次完整的调度
func (sched *Scheduler) scheduleOne(ctx context.Context) {
    // 1. 从队列获取下一个Pod
    podInfo, err := sched.NextPod()
    if err != nil {
        klog.ErrorS(err, "Error while retrieving next pod from scheduling queue")
        return
    }

    pod := podInfo.Pod

    // 2. 获取对应的调度框架
    fw, ok := sched.Profiles[pod.Spec.SchedulerName]
    if !ok {
        klog.V(4).InfoS("Unable to find profile for scheduler name, using default",
            "schedulerName", pod.Spec.SchedulerName)
        fw = sched.Profiles[sched.SchedulerName]
    }

    // 3. 创建调度周期状态
    state := framework.NewCycleState()

    // 4. 调度阶段
    schedulingCycleCtx, cancel := context.WithCancel(ctx)
    defer cancel()

    klog.V(4).InfoS("Attempting to schedule pod", "pod", klog.KObj(pod))

    // 执行调度算法
    scheduleResult, err := sched.SchedulePod(schedulingCycleCtx, fw, state, pod)
    if err != nil {
        // 调度失败处理
        sched.FailureHandler(schedulingCycleCtx, fw, podInfo, err, state)
        return
    }

    // 5. 假设阶段 - 在缓存中预留资源
    assumedPodInfo := podInfo.DeepCopy()
    assumedPod := assumedPodInfo.Pod

    err = sched.assume(schedulingCycleCtx, fw, assumedPod, scheduleResult.SuggestedHost)
    if err != nil {
        klog.ErrorS(err, "Error assuming pod", "pod", klog.KObj(pod))
        sched.FailureHandler(schedulingCycleCtx, fw, podInfo, err, state)
        return
    }

    // 6. 绑定阶段 - 异步执行
    go func() {
        bindingCycleCtx, cancel := context.WithCancel(ctx)
        defer cancel()

        // 执行Permit插件
        status := fw.RunPermitPlugins(bindingCycleCtx, state, assumedPod, scheduleResult.SuggestedHost)
        if !status.IsSuccess() {
            sched.handleBindingCycleError(bindingCycleCtx, assumedPodInfo, state, status)
            return
        }

        // 等待Permit批准
        status = fw.WaitOnPermit(bindingCycleCtx, assumedPod)
        if !status.IsSuccess() {
            sched.handleBindingCycleError(bindingCycleCtx, assumedPodInfo, state, status)
            return
        }

        // 执行绑定
        err := sched.bind(bindingCycleCtx, fw, assumedPod, scheduleResult.SuggestedHost, state)
        if err != nil {
            klog.ErrorS(err, "Error binding pod", "pod", klog.KObj(assumedPod))
            sched.handleBindingCycleError(bindingCycleCtx, assumedPodInfo, state, framework.AsStatus(err))
            return
        }

        // 执行PostBind插件
        fw.RunPostBindPlugins(bindingCycleCtx, state, assumedPod, scheduleResult.SuggestedHost)
    }()
}

// SchedulePod执行调度算法
func (sched *Scheduler) SchedulePod(ctx context.Context, fw framework.Framework,
    state *framework.CycleState, pod *v1.Pod) (ScheduleResult, error) {

    // 如果Pod已指定节点，直接使用
    if pod.Spec.NodeName != "" {
        return ScheduleResult{SuggestedHost: pod.Spec.NodeName}, nil
    }

    // 执行PreFilter插件
    preFilterResult, status := fw.RunPreFilterPlugins(ctx, state, pod)
    if !status.IsSuccess() {
        return ScheduleResult{}, status.AsError()
    }

    // 获取候选节点
    feasibleNodes, diagnosis, err := sched.findNodesThatFitPod(ctx, fw, state, pod, preFilterResult)
    if err != nil {
        return ScheduleResult{}, err
    }

    // 如果没有符合条件的节点
    if len(feasibleNodes) == 0 {
        return ScheduleResult{}, &framework.FitError{
            Pod:         pod,
            NumAllNodes: diagnosis.NodeToStatusMap.Len(),
            Diagnosis:   diagnosis,
        }
    }

    // 如果只有一个候选节点，直接选择
    if len(feasibleNodes) == 1 {
        return ScheduleResult{
            SuggestedHost: feasibleNodes[0].Name,
        }, nil
    }

    // 执行Prioritize（打分）
    priorityList, err := sched.prioritizeNodes(ctx, fw, state, pod, feasibleNodes)
    if err != nil {
        return ScheduleResult{}, err
    }

    // 选择得分最高的节点
    host, err := sched.selectHost(priorityList)
    if err != nil {
        return ScheduleResult{}, err
    }

    return ScheduleResult{
        SuggestedHost: host,
    }, nil
}

// findNodesThatFitPod查找适合Pod的节点
func (sched *Scheduler) findNodesThatFitPod(ctx context.Context, fw framework.Framework,
    state *framework.CycleState, pod *v1.Pod, preFilterResult *framework.PreFilterResult) ([]*v1.Node, framework.Diagnosis, error) {

    diagnosis := framework.Diagnosis{
        NodeToStatusMap:      make(framework.NodeToStatusMap),
        UnschedulablePlugins: sets.New[string](),
    }

    // 获取所有节点
    allNodes, err := fw.SnapshotSharedLister().NodeInfos().List()
    if err != nil {
        return nil, diagnosis, err
    }

    // 如果PreFilter给出了节点列表，只检查这些节点
    nodes := allNodes
    if preFilterResult != nil && len(preFilterResult.NodeNames) > 0 {
        nodes = make([]*framework.NodeInfo, 0, len(preFilterResult.NodeNames))
        for _, name := range preFilterResult.NodeNames.UnsortedList() {
            n, err := fw.SnapshotSharedLister().NodeInfos().Get(name)
            if err != nil {
                continue
            }
            nodes = append(nodes, n)
        }
    }

    // 并行执行Filter
    feasibleNodes := make([]*v1.Node, 0, len(nodes))

    // 检查所有节点
    for _, nodeInfo := range nodes {
        status := fw.RunFilterPluginsWithNominatedPods(ctx, state, pod, nodeInfo, nil)

        if status.Code() == framework.Error {
            return nil, diagnosis, status.AsError()
        }

        if status.IsSuccess() {
            feasibleNodes = append(feasibleNodes, nodeInfo.Node())
        } else {
            diagnosis.NodeToStatusMap[nodeInfo.Node().Name] = status
            diagnosis.UnschedulablePlugins.Insert(status.FailedPlugin())
        }
    }

    return feasibleNodes, diagnosis, nil
}

// prioritizeNodes为节点打分
func (sched *Scheduler) prioritizeNodes(ctx context.Context, fw framework.Framework,
    state *framework.CycleState, pod *v1.Pod, nodes []*v1.Node) (framework.NodeScoreList, error) {

    // 如果没有打分插件，所有节点得相同分数
    if len(fw.ListPlugins()["ScorePlugin"]) == 0 {
        result := make(framework.NodeScoreList, 0, len(nodes))
        for _, node := range nodes {
            result = append(result, framework.NodeScore{
                Name:  node.Name,
                Score: 1,
            })
        }
        return result, nil
    }

    // 执行PreScore插件
    status := fw.RunPreScorePlugins(ctx, state, pod, toNodeInfo(nodes))
    if !status.IsSuccess() {
        return nil, status.AsError()
    }

    // 执行Score插件
    scoresMap, status := fw.RunScorePlugins(ctx, state, pod, toNodeInfo(nodes))
    if !status.IsSuccess() {
        return nil, status.AsError()
    }

    // 合并所有插件的分数
    result := make(framework.NodeScoreList, 0, len(nodes))
    for i := range nodes {
        score := int64(0)
        for _, pluginScores := range scoresMap {
            score += pluginScores[i].Score
        }
        result = append(result, framework.NodeScore{
            Name:  nodes[i].Name,
            Score: score,
        })
    }

    return result, nil
}

// selectHost选择得分最高的节点
func (sched *Scheduler) selectHost(nodeScoreList framework.NodeScoreList) (string, error) {
    if len(nodeScoreList) == 0 {
        return "", fmt.Errorf("empty priorityList")
    }

    // 找到最高分
    maxScore := nodeScoreList[0].Score
    selected := nodeScoreList[0].Name

    cntOfMaxScore := 1
    for _, ns := range nodeScoreList[1:] {
        if ns.Score > maxScore {
            maxScore = ns.Score
            selected = ns.Name
            cntOfMaxScore = 1
        } else if ns.Score == maxScore {
            // 随机选择相同最高分的节点
            cntOfMaxScore++
            if rand.Intn(cntOfMaxScore) == 0 {
                selected = ns.Name
            }
        }
    }

    return selected, nil
}

// assume在缓存中假设Pod已被调度
func (sched *Scheduler) assume(ctx context.Context, fw framework.Framework,
    pod *v1.Pod, nodeName string) error {

    // 创建假设的Pod副本
    assumedPod := pod.DeepCopy()
    assumedPod.Spec.NodeName = nodeName

    // 添加到缓存
    if err := sched.Cache.AssumePod(assumedPod); err != nil {
        klog.ErrorS(err, "Error assuming pod", "pod", klog.KObj(pod))
        return err
    }

    // 执行Reserve插件
    if status := fw.RunReservePluginsReserve(ctx, state, assumedPod, nodeName); !status.IsSuccess() {
        // 取消假设
        sched.Cache.ForgetPod(assumedPod)
        return status.AsError()
    }

    return nil
}

// bind执行实际的Pod绑定
func (sched *Scheduler) bind(ctx context.Context, fw framework.Framework,
    pod *v1.Pod, nodeName string, state *framework.CycleState) error {

    // 执行PreBind插件
    if status := fw.RunPreBindPlugins(ctx, state, pod, nodeName); !status.IsSuccess() {
        return status.AsError()
    }

    // 执行Bind插件
    if status := fw.RunBindPlugins(ctx, state, pod, nodeName); !status.IsSuccess() {
        return status.AsError()
    }

    return nil
}
```

### 4.2 调度缓存机制

```go
// kubernetes/pkg/scheduler/internal/cache/cache.go
// 调度缓存实现

type cacheImpl struct {
    stop <-chan struct{}

    // 互斥锁保护缓存数据
    mu sync.RWMutex

    // 假设Pod集合
    assumedPods map[string]bool

    // Pod状态映射
    podStates map[string]*podState

    // 节点信息映射
    nodes map[string]*nodeInfoListItem

    // 节点信息列表头尾（用于快速添加/删除）
    headNode *nodeInfoListItem

    // 节点数量
    nodeTree *nodeTree

    // 镜像状态
    imageStates map[string]*imageState
}

// NodeInfo是节点信息的完整表示
type NodeInfo struct {
    // 节点对象
    node *v1.Node

    // 已分配的资源
    requested *Resource

    // 非终止状态的Pod
    pods []*PodInfo

    // 使用的端口
    usedPorts HostPortInfo

    // PVC引用计数
    pvcRefCounts map[string]int

    // 镜像信息
    imageStates map[string]*imageState

    // 亲和性和反亲和性信息
    podsWithAffinity    []*PodInfo
    podsWithRequiredAntiAffinity []*PodInfo

    // 拓扑键值映射
    topologyKeys map[TopologyPair]int
}

// AssumePod在缓存中假设Pod已被调度
func (cache *cacheImpl) AssumePod(pod *v1.Pod) error {
    key, err := framework.GetPodKey(pod)
    if err != nil {
        return err
    }

    cache.mu.Lock()
    defer cache.mu.Unlock()

    // 检查Pod是否已存在
    if _, ok := cache.podStates[key]; ok {
        return fmt.Errorf("pod %v already in cache", key)
    }

    // 添加到假设Pod集合
    cache.assumedPods[key] = true

    // 添加到缓存
    ps := &podState{
        pod: pod,
    }
    cache.podStates[key] = ps

    // 更新节点资源
    if err := cache.addPod(pod); err != nil {
        return err
    }

    return nil
}

// ForgetPod取消假设的Pod
func (cache *cacheImpl) ForgetPod(pod *v1.Pod) error {
    key, err := framework.GetPodKey(pod)
    if err != nil {
        return err
    }

    cache.mu.Lock()
    defer cache.mu.Unlock()

    // 检查是否是假设的Pod
    if !cache.assumedPods[key] {
        return fmt.Errorf("pod %v wasn't assumed", key)
    }

    // 从假设集合中移除
    delete(cache.assumedPods, key)

    // 从缓存中移除
    delete(cache.podStates, key)

    // 更新节点资源
    if err := cache.removePod(pod); err != nil {
        return err
    }

    return nil
}

// AddPod添加已调度的Pod
func (cache *cacheImpl) AddPod(pod *v1.Pod) error {
    key, err := framework.GetPodKey(pod)
    if err != nil {
        return err
    }

    cache.mu.Lock()
    defer cache.mu.Unlock()

    // 如果是假设的Pod，确认它
    if cache.assumedPods[key] {
        delete(cache.assumedPods, key)
    }

    // 更新缓存
    ps, ok := cache.podStates[key]
    if !ok {
        ps = &podState{
            pod: pod,
        }
        cache.podStates[key] = ps
    } else {
        ps.pod = pod
    }

    // 更新节点资源
    if err := cache.addPod(pod); err != nil {
        return err
    }

    return nil
}

// UpdateNode更新节点信息
func (cache *cacheImpl) UpdateNode(oldNode, newNode *v1.Node) error {
    cache.mu.Lock()
    defer cache.mu.Unlock()

    // 获取旧节点信息
    n, ok := cache.nodes[newNode.Name]
    if !ok {
        // 节点不存在，作为新节点添加
        return cache.addNode(newNode)
    }

    // 更新节点信息
    n.info.SetNode(newNode)

    // 更新nodeTree
    cache.nodeTree.updateNode(oldNode, newNode)

    return nil
}

// Snapshot创建缓存的快照
func (cache *cacheImpl) Snapshot() *Snapshot {
    cache.mu.RLock()
    defer cache.mu.RUnlock()

    snapshot := &Snapshot{
        Nodes: make(map[string]*framework.NodeInfo),
    }

    // 复制所有节点信息
    for name, nodeItem := range cache.nodes {
        snapshot.Nodes[name] = nodeItem.info.Clone()
    }

    return snapshot
}

// addPod更新节点以反映Pod的添加
func (cache *cacheImpl) addPod(pod *v1.Pod) error {
    nodeName := pod.Spec.NodeName
    if nodeName == "" {
        return nil
    }

    nodeItem, ok := cache.nodes[nodeName]
    if !ok {
        return fmt.Errorf("node %q not found in cache", nodeName)
    }

    // 添加Pod到节点
    nodeItem.info.AddPod(pod)

    return nil
}

// removePod更新节点以反映Pod的移除
func (cache *cacheImpl) removePod(pod *v1.Pod) error {
    nodeName := pod.Spec.NodeName
    if nodeName == "" {
        return nil
    }

    nodeItem, ok := cache.nodes[nodeName]
    if !ok {
        return fmt.Errorf("node %q not found in cache", nodeName)
    }

    // 从节点移除Pod
    nodeItem.info.RemovePod(pod)

    return nil
}
```


## 5. 性能优化

### 5.1 调度延迟优化

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                       Scheduling Latency Optimization                       │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  1. 调度延迟来源分析：                                                       │
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                     Scheduling Latency Breakdown                     │   │
│  │                                                                     │   │
│  │   ┌─────────────┐                                                   │   │
│  │   │ API Server  │  ► 获取Pod和节点信息延迟                          │   │
│  │   │   Latency   │     (通常 < 10ms)                                 │   │
│  │   └──────┬──────┘                                                   │   │
│  │          │                                                          │   │
│  │          ▼                                                          │   │
│  │   ┌─────────────┐                                                   │   │
│  │   │   PreFilter │  ► 预处理计算                                     │   │
│  │   │   Latency   │     (与Pod复杂度相关)                             │   │
│  │   └──────┬──────┘                                                   │   │
│  │          │                                                          │   │
│  │          ▼                                                          │   │
│  │   ┌─────────────┐                                                   │   │
│  │   │    Filter   │  ► 筛选节点（主要延迟来源）                       │   │
│  │   │   Latency   │     O(n) - n为节点数                             │   │
│  │   └──────┬──────┘                                                   │   │
│  │          │                                                          │   │
│  │          ▼                                                          │   │
│  │   ┌─────────────┐                                                   │   │
│  │   │    Score    │  ► 节点打分                                       │   │
│  │   │   Latency   │     O(m*n) - m为打分插件数                       │   │
│  │   └──────┬──────┘                                                   │   │
│  │          │                                                          │   │
│  │          ▼                                                          │   │
│  │   ┌─────────────┐                                                   │   │
│  │   │  Preemption │  ► 抢占处理                                       │   │
│  │   │   Latency   │     (可选，仅在需要时)                            │   │
│  │   └──────┬──────┘                                                   │   │
│  │          │                                                          │   │
│  │          ▼                                                          │   │
│  │   ┌─────────────┐                                                   │   │
│  │   │    Bind     │  ► 绑定Pod到节点                                  │   │
│  │   │   Latency   │     (通常 < 100ms)                                │   │
│  │   └─────────────┘                                                   │   │
│  │                                                                     │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│  2. 优化策略：                                                               │
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │ 策略                    │ 方法                              │ 效果   │   │
│  ├─────────────────────────┼───────────────────────────────────┼────────┤   │
│  │ 采样节点               │ percentageOfNodesToScore           │ 高     │   │
│  │ 并行过滤               │ 并行执行Filter插件                 │ 高     │   │
│  │ 并行打分               │ 并行执行Score插件                  │ 中     │   │
│  │ 缓存优化               │ 增量更新NodeInfo                   │ 高     │   │
│  │ 快照优化               │ 减少全量快照                       │ 中     │   │
│  │ 插件优化               │ 减少不必要的插件调用               │ 中     │   │
│  └─────────────────────────┴───────────────────────────────────┴────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

#### 5.1.1 节点采样优化

```go
// kubernetes/pkg/scheduler/scheduler.go
// 节点采样机制

// percentageOfNodesToScore控制只评估部分节点
// 默认：对于小于50个节点的集群，评估所有节点
//      对于更大的集群，评估50-100%的节点

func (sched *Scheduler) findNodesThatFitPod(ctx context.Context, fw framework.Framework,
    state *framework.CycleState, pod *v1.Pod, preFilterResult *framework.PreFilterResult) ([]*v1.Node, framework.Diagnosis, error) {

    allNodes, err := fw.SnapshotSharedLister().NodeInfos().List()
    if err != nil {
        return nil, diagnosis, err
    }

    // 计算需要评估的节点数
    numNodesToFind := sched.calculateNumNodes(len(allNodes))

    // 如果节点数少于阈值，评估所有节点
    if len(allNodes) <= numNodesToFind {
        // 评估所有节点
        return sched.evaluateAllNodes(ctx, fw, state, pod, allNodes)
    }

    // 随机采样节点
    return sched.evaluateSampledNodes(ctx, fw, state, pod, allNodes, numNodesToFind)
}

func (sched *Scheduler) calculateNumNodes(totalNodes int) int {
    if totalNodes < 50 {
        return totalNodes
    }

    // 计算采样比例
    // 随着集群增大，比例逐渐减小，但最少评估5%的节点
    percentage := 50 - int32(math.Log2(float64(totalNodes-50)))
    if percentage < 5 {
        percentage = 5
    }

    numNodes := int32(totalNodes) * percentage / 100
    if numNodes < 50 {
        numNodes = 50
    }

    return int(numNodes)
}
```

#### 5.1.2 并行化优化

```go
// kubernetes/pkg/scheduler/framework/parallelize/parallelism.go
// 并行化执行框架

// Until并行执行函数
func Until(ctx context.Context, pieces int, doWorkPiece workFunc) error {
    if pieces == 0 {
        return nil
    }

    // 获取worker数量
    numWorkers := runtime.GOMAXPROCS(0)
    if pieces < numWorkers {
        numWorkers = pieces
    }

    // 创建work channel
    workCh := make(chan int, pieces)
    for i := 0; i < pieces; i++ {
        workCh <- i
    }
    close(workCh)

    // 启动workers
    var wg sync.WaitGroup
    wg.Add(numWorkers)

    errCh := make(chan error, numWorkers)

    for i := 0; i < numWorkers; i++ {
        go func() {
            defer wg.Done()
            for piece := range workCh {
                if err := doWorkPiece(piece); err != nil {
                    select {
                    case errCh <- err:
                    case <-ctx.Done():
                    }
                    return
                }
            }
        }()
    }

    wg.Wait()

    select {
    case err := <-errCh:
        return err
    default:
        return nil
    }
}

// 在Filter中使用并行化
func (f *frameworkImpl) RunFilterPlugins(ctx context.Context, state *framework.CycleState,
    pod *v1.Pod, nodes []*framework.NodeInfo) framework.PluginToStatus {

    statuses := make(framework.PluginToStatus)

    // 并行执行Filter插件
    errCh := parallelize.NewErrorChannel()

    for _, nodeInfo := range nodes {
        nodeInfo := nodeInfo
        go func() {
            status := f.runFilterPlugin(ctx, state, pod, nodeInfo)
            if !status.IsSuccess() {
                statuses[nodeInfo.Node().Name] = status
            }
        }()
    }

    if err := errCh.ReceiveError(); err != nil {
        return statuses
    }

    return statuses
}
```

### 5.2 大规模集群优化

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                     Large Scale Cluster Optimization                        │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  1. 大规模集群挑战：                                                         │
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │ 挑战                     │ 影响                  │ 解决方案         │   │
│  ├─────────────────────────┼───────────────────────┼─────────────────┤   │
│  │ 节点数量多              │ 调度延迟增加          │ 节点采样        │   │
│  │ Pod数量多               │ 调度队列压力大        │ 多调度器        │   │
│  │ 资源碎片                │ 调度失败增加          │ 碎片整理        │   │
│  │ 网络开销                │ API Server压力大      │ 本地缓存        │   │
│  │ 热点节点                │ 负载不均衡            │ 负载均衡算法    │   │
│  └─────────────────────────┴───────────────────────┴─────────────────┘   │
│                                                                             │
│  2. 多调度器部署架构：                                                       │
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                         Multi-Scheduler Setup                        │   │
│  │                                                                     │   │
│  │     ┌─────────────────────────────────────────────────────┐        │   │
│  │     │                   API Server                        │        │   │
│  │     └──────────────────────┬──────────────────────────────┘        │   │
│  │                            │                                       │   │
│  │        ┌───────────────────┼───────────────────┐                   │   │
│  │        │                   │                   │                   │   │
│  │        ▼                   ▼                   ▼                   │   │
│  │   ┌─────────┐        ┌─────────┐        ┌─────────┐              │   │
│  │   │scheduler│        │scheduler│        │scheduler│              │   │
│  │   │-default │        │-batch   │        │-service │              │   │
│  │   │         │        │         │        │         │              │   │
│  │   │Pods w/o │        │CronJobs │        │Services │              │   │
│  │   │explicit │        │Batch Jobs│       │Web Pods │              │   │
│  │   │scheduler│        │         │        │         │              │   │
│  │   │name     │        │         │        │         │              │   │
│  │   └────┬────┘        └────┬────┘        └────┬────┘              │   │
│  │        │                  │                  │                    │   │
│  │        └──────────────────┼──────────────────┘                    │   │
│  │                           │                                       │   │
│  │                    ┌──────┴──────┐                                │   │
│  │                    │  All Nodes  │                                │   │
│  │                    └─────────────┘                                │   │
│  │                                                                     │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│  3. 调度器配置示例：                                                         │
│                                                                             │
│  apiVersion: v1                                                            │
│  kind: ConfigMap                                                           │
│  metadata:                                                                 │
│    name: scheduler-config                                                  │
│  data:                                                                     │
│    scheduler-config.yaml: |                                                │
│      apiVersion: kubescheduler.config.k8s.io/v1                            │
│      kind: KubeSchedulerConfiguration                                      │
│      profiles:                                                             │
│        - schedulerName: default-scheduler                                  │
│          plugins:                                                          │
│            score:                                                          │
│              disabled:                                                     │
│                - name: PodTopologySpread                                   │
│              enabled:                                                      │
│                - name: NodeResourcesBalancedAllocation                     │
│                  weight: 2                                                 │
│        - schedulerName: batch-scheduler                                    │
│          plugins:                                                          │
│            filter:                                                         │
│              disabled:                                                     │
│                - name: NodeResourcesFit                                    │
│              enabled:                                                      │
│                - name: NodeResourcesFit                                    │
│                  arguments:                                                │
│                    ignoredResources:                                       │
│                      - nvidia.com/gpu                                      │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

#### 5.2.1 大规模集群配置

```yaml
# 大规模集群调度器配置
apiVersion: kubescheduler.config.k8s.io/v1
kind: KubeSchedulerConfiguration
clientConnection:
  kubeconfig: /etc/kubernetes/scheduler.conf
leaderElection:
  leaderElect: true
  resourceNamespace: kube-system
  resourceName: kube-scheduler
# 性能相关配置
percentageOfNodesToScore: 10  # 只评估10%的节点
parallelism: 16               # 并行度
# 调度队列配置
profiles:
  - schedulerName: default-scheduler
    # 优化插件配置
    plugins:
      queueSort:
        enabled:
          - name: PrioritySort
      preFilter:
        enabled:
          - name: NodeResourcesFit
          - name: NodePorts
          - name: VolumeBinding
          - name: PodTopologySpread
          - name: InterPodAffinity
          - name: TaintToleration
      filter:
        enabled:
          - name: NodeUnschedulable
          - name: NodeName
          - name: TaintToleration
          - name: NodeAffinity
          - name: NodePorts
          - name: NodeResourcesFit
          - name: VolumeBinding
          - name: VolumeZone
          - name: PodTopologySpread
          - name: InterPodAffinity
      preScore:
        enabled:
          - name: InterPodAffinity
          - name: PodTopologySpread
          - name: TaintToleration
          - name: NodeAffinity
      score:
        enabled:
          - name: NodeResourcesBalancedAllocation
            weight: 1
          - name: ImageLocality
            weight: 1
          - name: InterPodAffinity
            weight: 1
          - name: NodeResourcesFit
            weight: 1
          - name: PodTopologySpread
            weight: 2
          - name: TaintToleration
            weight: 1
          - name: NodeAffinity
            weight: 1
      reserve:
        enabled:
          - name: VolumeBinding
      permit:
        enabled: []
      preBind:
        enabled:
          - name: VolumeBinding
      bind:
        enabled:
          - name: DefaultBinder
      postBind:
        enabled: []
    # 插件参数
    pluginConfig:
      - name: NodeResourcesFit
        args:
          ignoredResources:
            - nvidia.com/gpu
          ignoredResourceGroups:
            - example.com
      - name: PodTopologySpread
        args:
          defaultConstraints:
            - maxSkew: 3
              topologyKey: kubernetes.io/hostname
              whenUnsatisfiable: ScheduleAnyway
          defaultingType: List
```

### 5.3 自定义调度器开发

```go
// 自定义调度器示例 - GPU感知调度器
package main

import (
    "context"
    "fmt"
    "math"

    v1 "k8s.io/api/core/v1"
    "k8s.io/apimachinery/pkg/runtime"
    "k8s.io/kubernetes/pkg/scheduler/framework"
)

// GPUPriority是一个GPU感知的调度插件
type GPUPriority struct {
    handle framework.Handle
}

var _ framework.ScorePlugin = &GPUPriority{}

const (
    Name = "GPUPriority"
)

func (g *GPUPriority) Name() string {
    return Name
}

func (g *GPUPriority) Score(ctx context.Context, state *framework.CycleState,
    pod *v1.Pod, nodeName string) (int64, *framework.Status) {

    nodeInfo, err := g.handle.SnapshotSharedLister().NodeInfos().Get(nodeName)
    if err != nil {
        return 0, framework.AsStatus(fmt.Errorf("getting node %q from Snapshot: %w", nodeName, err))
    }

    node := nodeInfo.Node()
    if node == nil {
        return 0, framework.NewStatus(framework.Error, fmt.Sprintf("node not found: %q", nodeName))
    }

    // 获取Pod的GPU请求
    podGPURequest := getPodGPURequest(pod)

    // 获取节点的可用GPU
    nodeAvailableGPU := getNodeAvailableGPU(nodeInfo)

    // 计算GPU匹配分数
    score := calculateGPUScore(podGPURequest, nodeAvailableGPU, node)

    return score, nil
}

func (g *GPUPriority) ScoreExtensions() framework.ScoreExtensions {
    return nil
}

// getPodGPURequest获取Pod的GPU请求数量
func getPodGPURequest(pod *v1.Pod) int64 {
    var totalGPU int64 = 0

    for _, container := range pod.Spec.Containers {
        if gpu, ok := container.Resources.Requests["nvidia.com/gpu"]; ok {
            totalGPU += gpu.Value()
        }
    }

    return totalGPU
}

// getNodeAvailableGPU获取节点的可用GPU数量
func getNodeAvailableGPU(nodeInfo *framework.NodeInfo) int64 {
    node := nodeInfo.Node()
    if node == nil {
        return 0
    }

    // 获取节点总GPU
    allocatableGPU := node.Status.Allocatable["nvidia.com/gpu"]
    totalGPU := allocatableGPU.Value()

    // 获取已分配GPU
    allocatedGPU := nodeInfo.Requested.ScalarResources["nvidia.com/gpu"]

    return totalGPU - allocatedGPU
}

// calculateGPUScore计算GPU匹配分数
func calculateGPUScore(podGPURequest, nodeAvailableGPU int64, node *v1.Node) int64 {
    // 如果没有GPU请求，返回中性分数
    if podGPURequest == 0 {
        return 50
    }

    // 如果节点没有足够GPU，返回0
    if nodeAvailableGPU < podGPURequest {
        return 0
    }

    // 获取节点总GPU
    totalGPU := node.Status.Allocatable["nvidia.com/gpu"].Value()

    // 计算GPU使用率
    gpuUsage := float64(podGPURequest) / float64(totalGPU)

    // 分数计算：优先选择GPU使用率高的节点（减少GPU碎片）
    // 但也保留一些灵活性
    if gpuUsage >= 0.8 {
        // 高使用率，最高分
        return 100
    } else if gpuUsage >= 0.5 {
        return 80
    } else if gpuUsage >= 0.25 {
        return 60
    } else {
        return 40
    }
}

// New初始化函数
func New(_ runtime.Object, handle framework.Handle) (framework.Plugin, error) {
    return &GPUPriority{
        handle: handle,
    }, nil
}
```

---

## 6. 形式化分析

### 6.1 调度决策的形式化模型

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    Formal Model of Kubernetes Scheduling                    │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  1. 基本定义：                                                               │
│                                                                             │
│  设：                                                                        │
│  - N = {n₁, n₂, ..., nₘ} 为节点集合                                         │
│  - P = {p₁, p₂, ..., pₙ} 为待调度Pod集合                                    │
│  - R = {cpu, mem, gpu, ...} 为资源类型集合                                  │
│                                                                             │
│  2. 节点资源模型：                                                           │
│                                                                             │
│  对于每个节点 n ∈ N，定义：                                                  │
│  - Capacity(n) = {cᵣ(n) | r ∈ R}           // 节点总容量                    │
│  - Allocated(n) = {aᵣ(n) | r ∈ R}          // 已分配资源                    │
│  - Available(n) = {cᵣ(n) - aᵣ(n) | r ∈ R}  // 可用资源                      │
│                                                                             │
│  3. Pod资源需求：                                                            │
│                                                                             │
│  对于每个Pod p ∈ P，定义：                                                   │
│  - Request(p) = {reqᵣ(p) | r ∈ R}          // 资源请求                      │
│  - Limit(p) = {limᵣ(p) | r ∈ R}            // 资源限制                      │
│  - Affinity(p) = 亲和性约束                                               │
│  - AntiAffinity(p) = 反亲和性约束                                         │
│                                                                             │
│  4. 调度函数：                                                               │
│                                                                             │
│  调度函数 S: P → N ∪ {⊥}                                                   │
│                                                                             │
│  S(p) = {                                                                    │
│    n ∈ N, 如果 ∃n 满足所有约束条件                                           │
│    ⊥,      如果不存在满足条件的节点                                          │
│  }                                                                           │
│                                                                             │
│  5. 约束条件形式化：                                                         │
│                                                                             │
│  a) 资源约束：                                                               │
│     ∀r ∈ R: reqᵣ(p) ≤ availableᵣ(n)                                        │
│                                                                             │
│  b) 节点选择器：                                                             │
│     selector(p) ⊆ labels(n)                                                │
│                                                                             │
│  c) 节点亲和性：                                                             │
│     ∀term ∈ requiredAffinity(p): satisfies(term, n)                        │
│                                                                             │
│  d) Pod亲和性：                                                              │
│     ∀term ∈ requiredPodAffinity(p):                                         │
│       ∃p' ∈ podsOnNode(n): matches(p', term)                               │
│                                                                             │
│  e) Pod反亲和性：                                                            │
│     ∀term ∈ requiredPodAntiAffinity(p):                                     │
│       ¬∃p' ∈ podsOnNode(n): matches(p', term)                              │
│                                                                             │
│  f) 污点容忍：                                                               │
│     ∀taint ∈ taints(n): tolerates(p, taint)                                │
│                                                                             │
│  g) 拓扑分布：                                                               │
│     ∀constraint ∈ topologySpread(p):                                        │
│       skew(constraint, n) ≤ maxSkew(constraint)                            │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 6.2 资源分配的正确性证明

```
┌─────────────────────────────────────────────────────────────────────────────┐
│              Correctness Proof of Resource Allocation                       │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  定理 1: 资源分配的安全性（Safety）                                          │
│                                                                             │
│  陈述：对于任何被调度的Pod p 和节点 n，满足：                                │
│         ∀r ∈ R: allocatedᵣ(n) ≤ capacityᵣ(n)                               │
│                                                                             │
│  证明：                                                                      │
│                                                                             │
│  基例：初始状态，allocatedᵣ(n) = 0 ≤ capacityᵣ(n)，成立。                   │
│                                                                             │
│  归纳假设：假设在某次调度前，定理成立。                                      │
│                                                                             │
│  归纳步骤：考虑调度Pod p到节点 n。                                          │
│                                                                             │
│  根据Filter阶段的NodeResourcesFit插件：                                      │
│  - 调度前检查：reqᵣ(p) ≤ availableᵣ(n) = capacityᵣ(n) - allocatedᵣ(n)      │
│  - 即：allocatedᵣ(n) + reqᵣ(p) ≤ capacityᵣ(n)                              │
│                                                                             │
│  调度后新的分配：                                                            │
│  allocated'ᵣ(n) = allocatedᵣ(n) + reqᵣ(p) ≤ capacityᵣ(n)                   │
│                                                                             │
│  因此，定理在调度后仍然成立。                                                │
│                                                                             │
│  □                                                                          │
│                                                                             │
│  ─────────────────────────────────────────────────────────────────────────  │
│                                                                             │
│  定理 2: 调度决策的完备性（Completeness）                                    │
│                                                                             │
│  陈述：如果存在节点 n 满足Pod p的所有约束，调度器最终会找到并选择这样的节点。│
│                                                                             │
│  证明：                                                                      │
│                                                                             │
│  设 N' ⊆ N 为满足Pod p所有约束的节点集合。                                   │
│                                                                             │
│  Filter阶段：                                                                │
│  - 对于每个节点 n ∈ N，Filter插件集合 F 会评估所有约束                       │
│  - 对于 n ∈ N'，所有Filter返回Success                                       │
│  - 对于 n ∉ N'，至少一个Filter返回Unschedulable                             │
│  - 因此，Filter阶段后，feasibleNodes = N'                                    │
│                                                                             │
│  Score阶段：                                                                 │
│  - 对于 n ∈ N'，Score插件会计算分数 score(n)                                 │
│  - selectHost选择分数最高的节点                                              │
│  - 由于 N' ≠ ∅，必定会选择某个 n* ∈ N'                                       │
│                                                                             │
│  因此，调度器会选择满足所有约束的节点。                                      │
│                                                                             │
│  □                                                                          │
│                                                                             │
│  ─────────────────────────────────────────────────────────────────────────  │
│                                                                             │
│  定理 3: 调度算法的终止性（Termination）                                     │
│                                                                             │
│  陈述：对于任何Pod p，调度算法在有限步内终止。                               │
│                                                                             │
│  证明：                                                                      │
│                                                                             │
│  Filter阶段：                                                                │
│  - 评估的节点数 |N| 是有限的                                                 │
│  - 每个Filter插件的计算是有限操作                                            │
│  - Filter阶段在 O(|N| × |F|) 时间内完成                                     │
│                                                                             │
│  Score阶段（仅当|feasibleNodes| > 1时执行）：                               │
│  - 需要打分的节点数 ≤ |N|                                                    │
│  - 每个Score插件的计算是有限操作                                             │
│  - Score阶段在 O(|feasibleNodes| × |S|) 时间内完成                          │
│                                                                             │
│  Bind阶段：                                                                  │
│  - API调用是有限操作                                                         │
│  - 超时机制确保不会无限等待                                                  │
│                                                                             │
│  因此，整个调度算法在有限时间内终止。                                        │
│                                                                             │
│  □                                                                          │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 6.3 负载均衡的数学分析

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                Mathematical Analysis of Load Balancing                      │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  1. 资源利用率方差分析：                                                     │
│                                                                             │
│  定义节点n的资源利用率：                                                     │
│  Uᵣ(n) = allocatedᵣ(n) / capacityᵣ(n)                                      │
│                                                                             │
│  对于资源类型r，所有节点的平均利用率：                                       │
│  Ūᵣ = (1/|N|) × Σₙ Uᵣ(n)                                                   │
│                                                                             │
│  资源利用率的方差：                                                          │
│  Var(Uᵣ) = (1/|N|) × Σₙ (Uᵣ(n) - Ūᵣ)²                                      │
│                                                                             │
│  NodeResourcesBalancedAllocation插件的目标：                                 │
│  minimize Σᵣ Var(Uᵣ)  即最小化资源利用率方差                                │
│                                                                             │
│  ─────────────────────────────────────────────────────────────────────────  │
│                                                                             │
│  2. Pod拓扑分布的数学模型：                                                  │
│                                                                             │
│  设拓扑域T的值为{v₁, v₂, ..., vₖ}                                           │
│                                                                             │
│  对于每个值vᵢ，定义：                                                        │
│  - count(vᵢ) = 拓扑值为vᵢ的节点上匹配的Pod数量                              │
│  - minCount = min(count(vᵢ))                                                │
│  - maxCount = max(count(vᵢ))                                                │
│                                                                             │
│  Skew（偏差）计算：                                                          │
│  skew(vᵢ) = count(vᵢ) - minCount                                           │
│                                                                             │
│  约束条件：                                                                  │
│  skew(vᵢ) ≤ maxSkew                                                          │
│                                                                             │
│  目标：在调度新Pod p后，新的skew满足约束。                                   │
│                                                                             │
│  3. 评分函数的数学性质：                                                     │
│                                                                             │
│  对于每个Score插件s，定义评分函数：                                          │
│  scoreₛ(n, p) ∈ [0, 100]                                                    │
│                                                                             │
│  最终得分是加权平均：                                                        │
│  Score(n, p) = Σₛ wₛ × scoreₛ(n, p) / Σₛ wₛ                                │
│                                                                             │
│  性质：                                                                      │
│  - 有界性：0 ≤ Score(n, p) ≤ 100                                            │
│  - 单调性：如果对于所有s，scoreₛ(n₁, p) ≥ scoreₛ(n₂, p)                     │
│            则 Score(n₁, p) ≥ Score(n₂, p)                                   │
│                                                                             │
│  ─────────────────────────────────────────────────────────────────────────  │
│                                                                             │
│  4. 调度决策的优化问题：                                                     │
│                                                                             │
│  给定Pod p，调度问题可以形式化为：                                           │
│                                                                             │
│  最大化：   Score(n, p)                                                      │
│  约束于：   n ∈ feasible(p)                                                  │
│                                                                             │
│  其中feasible(p)是满足所有硬约束的节点集合。                                 │
│                                                                             │
│  这是一个经典的约束优化问题，调度器使用贪心算法求解：                        │
│  1) 先使用Filter确定feasible(p)                                             │
│  2) 再使用Score在feasible(p)中选择最优节点                                  │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 6.4 调度算法复杂度分析

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                Complexity Analysis of Scheduling Algorithm                  │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  设：                                                                        │
│  - m = |N| 节点数量                                                          │
│  - k = |F| Filter插件数量                                                    │
│  - l = |S| Score插件数量                                                     │
│  - p = feasibleNodes数量（通过Filter的节点）                                 │
│                                                                             │
│  1. Filter阶段复杂度：                                                       │
│                                                                             │
│  最坏情况：                                                                  │
│  O(m × k × f_avg)                                                           │
│  其中f_avg是单个Filter插件在单个节点上的平均执行时间                         │
│                                                                             │
│  使用采样优化后（评估比例为α）：                                             │
│  O(α × m × k × f_avg), 其中α ∈ [0.05, 1.0]                                  │
│                                                                             │
│  2. Score阶段复杂度：                                                        │
│                                                                             │
│  O(p × l × s_avg)                                                           │
│  其中s_avg是单个Score插件在单个节点上的平均执行时间                          │
│                                                                             │
│  使用并行化后（w个worker）：                                                 │
│  O(p × l × s_avg / w)                                                       │
│                                                                             │
│  3. 总体复杂度：                                                             │
│                                                                             │
│  T(m, k, l, p) = O(α × m × k × f_avg + p × l × s_avg / w)                   │
│                                                                             │
│  典型值：                                                                    │
│  - m = 1000（节点数）                                                        │
│  - α = 0.1（采样比例）                                                       │
│  - k = 10（Filter插件数）                                                    │
│  - p = 100（通过Filter的节点数）                                             │
│  - l = 5（Score插件数）                                                      │
│  - w = 8（并行worker数）                                                     │
│  - f_avg = 1ms, s_avg = 0.5ms                                               │
│                                                                             │
│  T ≈ 100 × 10 × 1 + 100 × 5 × 0.5 / 8                                       │
│    ≈ 1000 + 31.25                                                           │
│    ≈ 1031.25 ms                                                             │
│    ≈ 1.03 seconds                                                           │
│                                                                             │
│  4. 空间复杂度：                                                             │
│                                                                             │
│  - Node缓存：O(m × r)，其中r是每种资源的存储大小                             │
│  - Pod缓存：O(n × pod_info_size)，n是Pod数量                                │
│  - 调度状态：O(p × state_size)                                              │
│                                                                             │
│  总体空间复杂度：O(m × r + n × pod_info_size)                               │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 7. 实践案例

### 7.1 大规模生产集群配置

```yaml
# 大规模生产环境调度器配置（5000+节点）
apiVersion: kubescheduler.config.k8s.io/v1
kind: KubeSchedulerConfiguration
clientConnection:
  kubeconfig: /etc/kubernetes/scheduler.conf
  acceptContentTypes: "application/vnd.kubernetes.protobuf,application/json"
  contentType: "application/vnd.kubernetes.protobuf"
  qps: 100
  burst: 150
leaderElection:
  leaderElect: true
  leaseDuration: 15s
  renewDeadline: 10s
  retryPeriod: 2s
  resourceNamespace: kube-system
  resourceName: kube-scheduler
# 性能调优参数
parallelism: 32
percentageOfNodesToScore: 5  # 大规模集群使用更小的比例
# 调度队列配置
profiles:
  - schedulerName: default-scheduler
    # 重试和退避配置
    schedulerQueue:
      sort: {}
      preEnqueue:
        enabled:
          - name: SchedulingGates
          - name: PrioritySort
      queueingHints:
        enabled:
          - name: TaintToleration
          - name: NodeAffinity
          - name: NodePorts
          - name: NodeResourcesFit
          - name: VolumeBinding
          - name: PodTopologySpread
          - name: InterPodAffinity
    # 插件配置
    plugins:
      queueSort:
        enabled:
          - name: PrioritySort
      preFilter:
        enabled:
          - name: NodeResourcesFit
          - name: NodePorts
          - name: VolumeBinding
          - name: PodTopologySpread
          - name: InterPodAffinity
          - name: TaintToleration
      filter:
        enabled:
          - name: NodeUnschedulable
          - name: NodeName
          - name: TaintToleration
          - name: NodeAffinity
          - name: NodePorts
          - name: NodeResourcesFit
          - name: VolumeBinding
          - name: VolumeZone
          - name: PodTopologySpread
          - name: InterPodAffinity
          - name: CSINode
      preScore:
        enabled:
          - name: InterPodAffinity
          - name: PodTopologySpread
          - name: TaintToleration
          - name: NodeAffinity
      score:
        enabled:
          - name: NodeResourcesBalancedAllocation
            weight: 1
          - name: ImageLocality
            weight: 1
          - name: InterPodAffinity
            weight: 1
          - name: NodeResourcesFit
            weight: 1
          - name: PodTopologySpread
            weight: 2
          - name: TaintToleration
            weight: 1
          - name: NodeAffinity
            weight: 1
      reserve:
        enabled:
          - name: VolumeBinding
      preBind:
        enabled:
          - name: VolumeBinding
      bind:
        enabled:
          - name: DefaultBinder
    pluginConfig:
      - name: NodeResourcesFit
        args:
          ignoredResources:
            - nvidia.com/gpu
            - amd.com/gpu
          ignoredResourceGroups:
            - example.com
            - vendor.io
      - name: PodTopologySpread
        args:
          defaultConstraints:
            - maxSkew: 3
              topologyKey: kubernetes.io/hostname
              whenUnsatisfiable: ScheduleAnyway
            - maxSkew: 5
              topologyKey: topology.kubernetes.io/zone
              whenUnsatisfiable: ScheduleAnyway
          defaultingType: List
```

### 7.2 调度问题排查

```bash
#!/bin/bash
# Kubernetes调度问题排查脚本
# 保存为: debug-scheduling.sh

echo "========== Kubernetes调度问题排查 =========="

# 1. 检查Pod状态
echo ""
echo "1. 检查Pending Pod:"
kubectl get pods --all-namespaces --field-selector=status.phase=Pending

# 2. 查看调度事件
echo ""
echo "2. 查看调度相关事件:"
kubectl get events --all-namespaces --field-selector reason=FailedScheduling --sort-by='.lastTimestamp' | tail -20

# 3. 详细查看Pending Pod信息
echo ""
echo "3. 输入Pod名称查看详细信息:"
read -p "Pod名称: " POD_NAME
read -p "命名空间 (默认default): " NAMESPACE
NAMESPACE=${NAMESPACE:-default}

echo ""
echo "3.1 Pod描述:"
kubectl describe pod $POD_NAME -n $NAMESPACE

echo ""
echo "3.2 Pod YAML:"
kubectl get pod $POD_NAME -n $NAMESPACE -o yaml

# 4. 检查节点资源
echo ""
echo "4. 节点资源使用情况:"
kubectl top nodes

# 5. 检查节点标签
echo ""
echo "5. 节点标签:"
kubectl get nodes --show-labels

# 6. 检查污点
echo ""
echo "6. 节点污点:"
kubectl get nodes -o custom-columns=NAME:.metadata.name,TAINTS:.spec.taints

# 7. 检查调度器日志
echo ""
echo "7. 调度器日志:"
kubectl logs -n kube-system -l component=kube-scheduler --tail=100

# 8. 检查调度器配置
echo ""
echo "8. 调度器Pod配置:"
kubectl get pods -n kube-system -l component=kube-scheduler -o yaml

# 9. 检查调度扩展器
echo ""
echo "9. 检查调度扩展器配置:"
kubectl get configmap -n kube-system scheduler-config -o yaml 2>/dev/null || echo "未找到scheduler-config ConfigMap"

echo ""
echo "========== 排查完成 =========="
```

### 7.3 常见调度问题及解决方案

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                     Common Scheduling Issues & Solutions                    │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  1. Pod一直处于Pending状态                                                  │
│                                                                             │
│  症状：Pod创建后长时间处于Pending，无调度事件                                │
│  原因：                                                                      │
│  - 调度器未运行或配置错误                                                    │
│  - 调度器名称不匹配                                                          │
│  - 调度队列积压                                                              │
│                                                                             │
│  解决：                                                                      │
│  kubectl get pods -n kube-system -l component=kube-scheduler                 │
│  kubectl logs -n kube-system -l component=kube-scheduler                     │
│                                                                             │
│  ─────────────────────────────────────────────────────────────────────────  │
│                                                                             │
│  2. Insufficient CPU/Memory                                                 │
│                                                                             │
│  症状：FailedScheduling事件显示资源不足                                      │
│  原因：                                                                      │
│  - 节点资源实际不足                                                          │
│  - 资源碎片导致无法分配                                                      │
│  - 其他Pod已占用资源                                                         │
│                                                                             │
│  解决：                                                                      │
│  # 检查节点资源                                                              │
│  kubectl describe node <node-name>                                           │
│  # 检查已分配资源                                                            │
│  kubectl top nodes                                                           │
│  # 方案：增加节点、调整资源请求、使用更小的Pod                               │
│                                                                             │
│  ─────────────────────────────────────────────────────────────────────────  │
│                                                                             │
│  3. NodeSelector/NodeAffinity不匹配                                         │
│                                                                             │
│  症状：0/3 nodes are available: 3 node(s) didn't match Pod's node            │
│       affinity/selector.                                                    │
│                                                                             │
│  解决：                                                                      │
│  # 检查Pod的节点选择器                                                       │
│  kubectl get pod <pod> -o yaml | grep -A 10 nodeSelector                     │
│  # 检查节点标签                                                              │
│  kubectl get nodes --show-labels                                             │
│  # 方案：修改标签或调整选择器                                                │
│                                                                             │
│  ─────────────────────────────────────────────────────────────────────────  │
│                                                                             │
│  4. TaintToleration不匹配                                                   │
│                                                                             │
│  症状：0/3 nodes are available: 1 node(s) had taint {key: value},            │
│       that the pod didn't tolerate.                                         │
│                                                                             │
│  解决：                                                                      │
│  # 检查节点污点                                                              │
│  kubectl describe node <node> | grep Taints                                  │
│  # 为Pod添加容忍                                                             │
│  kubectl patch pod <pod> -p '{"spec":{"tolerations":[{"key":"key",            │
│       "operator":"Equal","value":"value","effect":"NoSchedule"}]}}'          │
│                                                                             │
│  ─────────────────────────────────────────────────────────────────────────  │
│                                                                             │
│  5. PodAntiAffinity导致无法调度                                             │
│                                                                             │
│  症状：0/3 nodes are available: 3 node(s) didn't match pod affinity/anti     │
│       affinity rules                                                        │
│                                                                             │
│  解决：                                                                      │
│  # 检查Pod亲和性配置                                                         │
│  kubectl get pod <pod> -o yaml | grep -A 20 affinity                         │
│  # 方案：调整拓扑域、放宽约束为软约束                                        │
│                                                                             │
│  ─────────────────────────────────────────────────────────────────────────  │
│                                                                             │
│  6. VolumeBinding失败                                                       │
│                                                                             │
│  症状：0/3 nodes are available: 3 node(s) had volume node affinity conflict  │
│                                                                             │
│  解决：                                                                      │
│  # 检查PV的节点亲和性                                                        │
│  kubectl get pv <pv> -o yaml | grep -A 10 nodeAffinity                       │
│  # 检查PVC状态                                                               │
│  kubectl get pvc                                                             │
│  # 方案：使用支持动态供给的StorageClass                                      │
│                                                                             │
│  ─────────────────────────────────────────────────────────────────────────  │
│                                                                             │
│  7. 调度延迟高                                                              │
│                                                                             │
│  症状：Pod从创建到Running状态时间长                                          │
│  原因：                                                                      │
│  - 集群规模大但未调优                                                        │
│  - 调度器资源不足                                                            │
│  - 插件执行时间长                                                            │
│                                                                             │
│  解决：                                                                      │
│  # 查看调度器指标                                                            │
│  kubectl get --raw /apis/metrics.k8s.io/v1beta1/pods/kube-system             │
│  # 调整调度器配置                                                            │
│  # - 增加percentageOfNodesToScore                                            │
│  # - 增加调度器CPU/内存                                                      │
│  # - 禁用不必要的插件                                                        │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 7.4 性能调优案例

```yaml
# 案例：从50秒优化到2秒的调度延迟

# 优化前配置（问题配置）
# - 评估100%节点
# - 单线程执行
# - 启用所有插件

# 优化后配置
apiVersion: kubescheduler.config.k8s.io/v1
kind: KubeSchedulerConfiguration
clientConnection:
  kubeconfig: /etc/kubernetes/scheduler.conf
  qps: 100
  burst: 150
leaderElection:
  leaderElect: true
parallelism: 32              # 增加并行度
percentageOfNodesToScore: 10 # 只评估10%节点
profiles:
  - schedulerName: default-scheduler
    plugins:
      # 禁用不必要的插件以提高性能
      filter:
        disabled:
          - name: NodePreferAvoidPods  # 很少使用
          - name: NodeLabels           # 使用NodeSelector替代
        enabled:
          - name: NodeUnschedulable
          - name: NodeName
          - name: TaintToleration
          - name: NodeAffinity
          - name: NodePorts
          - name: NodeResourcesFit
          - name: VolumeBinding
      score:
        disabled:
          - name: SelectorSpread       # 被PodTopologySpread替代
        enabled:
          - name: NodeResourcesBalancedAllocation
            weight: 1
          - name: ImageLocality
            weight: 1
          - name: NodeResourcesFit
            weight: 1
          - name: PodTopologySpread
            weight: 2
    # 优化插件参数
    pluginConfig:
      - name: NodeResourcesFit
        args:
          # 忽略不常用的资源类型
          ignoredResources:
            - nvidia.com/gpu
      - name: PodTopologySpread
        args:
          # 设置合理的默认约束，减少计算量
          defaultConstraints:
            - maxSkew: 3
              topologyKey: kubernetes.io/hostname
              whenUnsatisfiable: ScheduleAnyway
```

---

## 8. Rust实现示例

### 8.1 简化版调度器框架

```rust
// scheduler.rs
// 简化版Kubernetes调度器Rust实现

use std::collections::{HashMap, HashSet, BinaryHeap};
use std::cmp::Ordering;
use std::sync::{Arc, Mutex};
use async_trait::async_trait;

/// 资源定义
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Resources {
    pub cpu: i64,      // millicores
    pub memory: i64,   // bytes
}

impl Resources {
    pub fn new(cpu: i64, memory: i64) -> Self {
        Self { cpu, memory }
    }

    /// 检查资源是否足够
    pub fn satisfies(&self, request: &Resources) -> bool {
        self.cpu >= request.cpu && self.memory >= request.memory
    }

    /// 减去资源
    pub fn sub(&mut self, other: &Resources) {
        self.cpu -= other.cpu;
        self.memory -= other.memory;
    }

    /// 添加资源
    pub fn add(&mut self, other: &Resources) {
        self.cpu += other.cpu;
        self.memory += other.memory;
    }
}

/// 节点定义
#[derive(Debug, Clone)]
pub struct Node {
    pub name: String,
    pub capacity: Resources,
    pub allocated: Resources,
    pub labels: HashMap<String, String>,
    pub taints: Vec<Taint>,
}

impl Node {
    pub fn new(name: &str, cpu: i64, memory: i64) -> Self {
        let capacity = Resources::new(cpu, memory);
        Self {
            name: name.to_string(),
            capacity: capacity.clone(),
            allocated: Resources::new(0, 0),
            labels: HashMap::new(),
            taints: Vec::new(),
        }
    }

    /// 获取可用资源
    pub fn available(&self) -> Resources {
        Resources {
            cpu: self.capacity.cpu - self.allocated.cpu,
            memory: self.capacity.memory - self.allocated.memory,
        }
    }

    /// 添加标签
    pub fn with_label(mut self, key: &str, value: &str) -> Self {
        self.labels.insert(key.to_string(), value.to_string());
        self
    }

    /// 添加污点
    pub fn with_taint(mut self, taint: Taint) -> Self {
        self.taints.push(taint);
        self
    }
}

/// 污点定义
#[derive(Debug, Clone)]
pub struct Taint {
    pub key: String,
    pub value: String,
    pub effect: TaintEffect,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TaintEffect {
    NoSchedule,
    PreferNoSchedule,
    NoExecute,
}

/// 容忍定义
#[derive(Debug, Clone)]
pub struct Toleration {
    pub key: String,
    pub operator: String,
    pub value: String,
    pub effect: TaintEffect,
}

/// Pod定义
#[derive(Debug, Clone)]
pub struct Pod {
    pub name: String,
    pub namespace: String,
    pub requests: Resources,
    pub labels: HashMap<String, String>,
    pub node_selector: HashMap<String, String>,
    pub tolerations: Vec<Toleration>,
    pub priority: i32,
}

impl Pod {
    pub fn new(name: &str, cpu: i64, memory: i64) -> Self {
        Self {
            name: name.to_string(),
            namespace: "default".to_string(),
            requests: Resources::new(cpu, memory),
            labels: HashMap::new(),
            node_selector: HashMap::new(),
            tolerations: Vec::new(),
            priority: 0,
        }
    }

    /// 容忍污点
    pub fn tolerates(&self, taint: &Taint) -> bool {
        for toleration in &self.tolerations {
            if toleration.key == taint.key
                && toleration.effect == taint.effect
                && (toleration.operator == "Exists" || toleration.value == taint.value) {
                return true;
            }
        }
        false
    }
}

/// 调度结果
#[derive(Debug)]
pub struct ScheduleResult {
    pub pod_name: String,
    pub node_name: String,
    pub score: i64,
}

/// 调度错误
#[derive(Debug)]
pub enum ScheduleError {
    NoNodeAvailable(String),
    NodeNotFound(String),
    ResourceNotAvailable,
}

impl std::fmt::Display for ScheduleError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ScheduleError::NoNodeAvailable(msg) => write!(f, "No node available: {}", msg),
            ScheduleError::NodeNotFound(name) => write!(f, "Node not found: {}", name),
            ScheduleError::ResourceNotAvailable => write!(f, "Resource not available"),
        }
    }
}

impl std::error::Error for ScheduleError {}

/// Filter插件接口
#[async_trait]
pub trait FilterPlugin: Send + Sync {
    fn name(&self) -> &'static str;
    async fn filter(&self, pod: &Pod, node: &Node) -> Result<(), String>;
}

/// Score插件接口
#[async_trait]
pub trait ScorePlugin: Send + Sync {
    fn name(&self) -> &'static str;
    async fn score(&self, pod: &Pod, node: &Node) -> i64;
}

/// 资源适配Filter
pub struct NodeResourcesFit;

#[async_trait]
impl FilterPlugin for NodeResourcesFit {
    fn name(&self) -> &'static str {
        "NodeResourcesFit"
    }

    async fn filter(&self, pod: &Pod, node: &Node) -> Result<(), String> {
        let available = node.available();
        if !available.satisfies(&pod.requests) {
            return Err(format!(
                "Insufficient resources: requested {:?}, available {:?}",
                pod.requests, available
            ));
        }
        Ok(())
    }
}

/// 节点选择器Filter
pub struct NodeSelectorFit;

#[async_trait]
impl FilterPlugin for NodeSelectorFit {
    fn name(&self) -> &'static str {
        "NodeSelectorFit"
    }

    async fn filter(&self, pod: &Pod, node: &Node) -> Result<(), String> {
        for (key, value) in &pod.node_selector {
            match node.labels.get(key) {
                Some(node_value) if node_value == value => continue,
                _ => return Err(format!("Node selector mismatch: {}={}", key, value)),
            }
        }
        Ok(())
    }
}

/// 污点容忍Filter
pub struct TaintToleration;

#[async_trait]
impl FilterPlugin for TaintToleration {
    fn name(&self) -> &'static str {
        "TaintToleration"
    }

    async fn filter(&self, pod: &Pod, node: &Node) -> Result<(), String> {
        for taint in &node.taints {
            if taint.effect == TaintEffect::NoSchedule && !pod.tolerates(taint) {
                return Err(format!(
                    "Pod does not tolerate taint: {:?}",
                    taint
                ));
            }
        }
        Ok(())
    }
}

/// 最少分配Score（优先选择资源剩余多的节点）
pub struct LeastAllocated;

#[async_trait]
impl ScorePlugin for LeastAllocated {
    fn name(&self) -> &'static str {
        "LeastAllocated"
    }

    async fn score(&self, _pod: &Pod, node: &Node) -> i64 {
        let available = node.available();

        // 计算资源使用率分数 (0-100)
        let cpu_score = if node.capacity.cpu > 0 {
            (available.cpu * 100) / node.capacity.cpu
        } else {
            0
        };

        let mem_score = if node.capacity.memory > 0 {
            (available.memory * 100) / node.capacity.memory
        } else {
            0
        };

        // 平均分
        (cpu_score + mem_score) / 2
    }
}

/// 平衡分配Score（优先选择资源类型使用均衡的节点）
pub struct BalancedAllocation;

#[async_trait]
impl ScorePlugin for BalancedAllocation {
    fn name(&self) -> &'static str {
        "BalancedAllocation"
    }

    async fn score(&self, pod: &Pod, node: &Node) -> i64 {
        let available = node.available();

        // 计算分配后的使用率
        let cpu_usage = if node.capacity.cpu > 0 {
            (node.allocated.cpu + pod.requests.cpu) as f64 / node.capacity.cpu as f64
        } else {
            0.0
        };

        let mem_usage = if node.capacity.memory > 0 {
            (node.allocated.memory + pod.requests.memory) as f64 / node.capacity.memory as f64
        } else {
            0.0
        };

        // 计算标准差（越小越好）
        let mean = (cpu_usage + mem_usage) / 2.0;
        let variance = ((cpu_usage - mean).powi(2) + (mem_usage - mean).powi(2)) / 2.0;
        let std_dev = variance.sqrt();

        // 转换为分数 (0-100)
        ((1.0 - std_dev) * 100.0) as i64
    }
}

/// 调度器
pub struct Scheduler {
    nodes: Arc<Mutex<Vec<Node>>>,
    filter_plugins: Vec<Box<dyn FilterPlugin>>,
    score_plugins: Vec<Box<dyn ScorePlugin>>,
    plugin_weights: HashMap<String, i64>,
}

impl Scheduler {
    pub fn new() -> Self {
        Self {
            nodes: Arc::new(Mutex::new(Vec::new())),
            filter_plugins: Vec::new(),
            score_plugins: Vec::new(),
            plugin_weights: HashMap::new(),
        }
    }

    /// 添加节点
    pub fn add_node(&self, node: Node) {
        let mut nodes = self.nodes.lock().unwrap();
        nodes.push(node);
    }

    /// 注册Filter插件
    pub fn add_filter_plugin(&mut self, plugin: Box<dyn FilterPlugin>) {
        self.filter_plugins.push(plugin);
    }

    /// 注册Score插件
    pub fn add_score_plugin(&mut self, plugin: Box<dyn ScorePlugin>, weight: i64) {
        self.plugin_weights.insert(plugin.name().to_string(), weight);
        self.score_plugins.push(plugin);
    }

    /// 调度单个Pod
    pub async fn schedule(&self, pod: &Pod) -> Result<ScheduleResult, ScheduleError> {
        // Phase 1: Filter
        let feasible_nodes = self.filter(pod).await?;

        if feasible_nodes.is_empty() {
            return Err(ScheduleError::NoNodeAvailable(
                "No nodes passed filter phase".to_string()
            ));
        }

        // 如果只有一个可行节点，直接返回
        if feasible_nodes.len() == 1 {
            return Ok(ScheduleResult {
                pod_name: pod.name.clone(),
                node_name: feasible_nodes[0].name.clone(),
                score: 100,
            });
        }

        // Phase 2: Score
        let scored_nodes = self.score(pod, &feasible_nodes).await;

        // 选择得分最高的节点
        let best = scored_nodes.iter()
            .max_by(|a, b| a.1.cmp(&b.1))
            .ok_or_else(|| ScheduleError::NoNodeAvailable("No nodes after scoring".to_string()))?;

        Ok(ScheduleResult {
            pod_name: pod.name.clone(),
            node_name: best.0.name.clone(),
            score: best.1,
        })
    }

    /// Filter阶段
    async fn filter(&self, pod: &Pod) -> Result<Vec<Node>, ScheduleError> {
        let nodes = self.nodes.lock().unwrap();
        let mut feasible = Vec::new();

        for node in nodes.iter() {
            let mut passed = true;

            for plugin in &self.filter_plugins {
                if let Err(reason) = plugin.filter(pod, node).await {
                    println!("  Filter {} rejected node {}: {}",
                        plugin.name(), node.name, reason);
                    passed = false;
                    break;
                }
            }

            if passed {
                feasible.push(node.clone());
            }
        }

        Ok(feasible)
    }

    /// Score阶段
    async fn score(&self, pod: &Pod, nodes: &[Node]) -> Vec<(Node, i64)> {
        let mut scored = Vec::new();

        for node in nodes {
            let mut total_score: i64 = 0;
            let mut total_weight: i64 = 0;

            for plugin in &self.score_plugins {
                let score = plugin.score(pod, node).await;
                let weight = self.plugin_weights.get(plugin.name()).copied().unwrap_or(1);

                total_score += score * weight;
                total_weight += weight;
            }

            // 归一化
            let normalized_score = if total_weight > 0 {
                total_score / total_weight
            } else {
                0
            };

            scored.push((node.clone(), normalized_score));
        }

        scored
    }

    /// 绑定Pod到节点（模拟）
    pub fn bind(&self, pod_name: &str, node_name: &str) -> Result<(), ScheduleError> {
        let mut nodes = self.nodes.lock().unwrap();

        for node in nodes.iter_mut() {
            if node.name == node_name {
                // 这里简化处理，实际应该从Pod获取请求
                println!("Pod {} bound to node {}", pod_name, node_name);
                return Ok(());
            }
        }

        Err(ScheduleError::NodeNotFound(node_name.to_string()))
    }
}

/// 调度队列
#[derive(Debug)]
struct QueuedPod {
    pod: Pod,
    priority: i32,
    timestamp: std::time::Instant,
}

impl PartialEq for QueuedPod {
    fn eq(&self, other: &Self) -> bool {
        self.priority == other.priority && self.timestamp == other.timestamp
    }
}

impl Eq for QueuedPod {}

impl PartialOrd for QueuedPod {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // 高优先级在前，相同优先级时先创建的在前
        Some(self.cmp(other))
    }
}

impl Ord for QueuedPod {
    fn cmp(&self, other: &Self) -> Ordering {
        self.priority.cmp(&other.priority)
            .then_with(|| other.timestamp.cmp(&self.timestamp))
    }
}

/// 调度队列管理器
pub struct SchedulingQueue {
    active_q: BinaryHeap<QueuedPod>,
    backoff_q: Vec<QueuedPod>,
}

impl SchedulingQueue {
    pub fn new() -> Self {
        Self {
            active_q: BinaryHeap::new(),
            backoff_q: Vec::new(),
        }
    }

    pub fn add(&mut self, pod: Pod) {
        self.active_q.push(QueuedPod {
            priority: pod.priority,
            pod,
            timestamp: std::time::Instant::now(),
        });
    }

    pub fn pop(&mut self) -> Option<Pod> {
        self.active_q.pop().map(|qp| qp.pod)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_scheduler() {
        let mut scheduler = Scheduler::new();

        // 添加节点
        scheduler.add_node(
            Node::new("node-1", 4000, 16000000000)
                .with_label("zone", "zone-a")
        );
        scheduler.add_node(
            Node::new("node-2", 4000, 16000000000)
                .with_label("zone", "zone-b")
                .with_taint(Taint {
                    key: "dedicated".to_string(),
                    value: "gpu".to_string(),
                    effect: TaintEffect::NoSchedule,
                })
        );
        scheduler.add_node(
            Node::new("node-3", 2000, 8000000000)
                .with_label("zone", "zone-a")
        );

        // 注册插件
        scheduler.add_filter_plugin(Box::new(NodeResourcesFit));
        scheduler.add_filter_plugin(Box::new(NodeSelectorFit));
        scheduler.add_filter_plugin(Box::new(TaintToleration));

        scheduler.add_score_plugin(Box::new(LeastAllocated), 1);
        scheduler.add_score_plugin(Box::new(BalancedAllocation), 1);

        // 创建Pod
        let pod = Pod::new("test-pod", 500, 1000000000)
            .with_label("app", "web");

        // 调度
        match scheduler.schedule(&pod).await {
            Ok(result) => {
                println!("Pod {} scheduled to {} with score {}",
                    result.pod_name, result.node_name, result.score);
            }
            Err(e) => {
                println!("Scheduling failed: {}", e);
            }
        }

        // 测试带污点的Pod
        let pod_with_toleration = Pod::new("gpu-pod", 1000, 2000000000)
            .with_toleration(Toleration {
                key: "dedicated".to_string(),
                operator: "Equal".to_string(),
                value: "gpu".to_string(),
                effect: TaintEffect::NoSchedule,
            });

        match scheduler.schedule(&pod_with_toleration).await {
            Ok(result) => {
                println!("GPU Pod {} scheduled to {} with score {}",
                    result.pod_name, result.node_name, result.score);
            }
            Err(e) => {
                println!("GPU Scheduling failed: {}", e);
            }
        }
    }
}
```

### 8.2 调度算法模拟

```rust
// simulation.rs
// 调度算法模拟和性能测试

use std::collections::HashMap;
use std::time::{Duration, Instant};
use rand::Rng;

/// 模拟调度性能
pub struct SchedulerSimulator {
    node_count: usize,
    pod_count: usize,
    nodes: Vec<SimulatedNode>,
    pods: Vec<SimulatedPod>,
}

#[derive(Clone)]
struct SimulatedNode {
    name: String,
    capacity: (i64, i64),  // (cpu, memory)
    allocated: (i64, i64),
}

#[derive(Clone)]
struct SimulatedPod {
    name: String,
    requests: (i64, i64),
    assigned_node: Option<String>,
}

impl SchedulerSimulator {
    pub fn new(node_count: usize, pod_count: usize) -> Self {
        Self {
            node_count,
            pod_count,
            nodes: Vec::new(),
            pods: Vec::new(),
        }
    }

    /// 初始化随机数据
    pub fn initialize(&mut self) {
        let mut rng = rand::thread_rng();

        // 创建节点
        for i in 0..self.node_count {
            self.nodes.push(SimulatedNode {
                name: format!("node-{}", i),
                capacity: (
                    rng.gen_range(4000..16000),     // CPU: 4-16 cores
                    rng.gen_range(16000000000..64000000000), // Memory: 16-64GB
                ),
                allocated: (0, 0),
            });
        }

        // 创建Pod
        for i in 0..self.pod_count {
            self.pods.push(SimulatedPod {
                name: format!("pod-{}", i),
                requests: (
                    rng.gen_range(100..1000),       // CPU: 0.1-1 core
                    rng.gen_range(100000000..1000000000), // Memory: 100MB-1GB
                ),
                assigned_node: None,
            });
        }
    }

    /// 简单调度算法（先到先得）
    pub fn schedule_first_fit(&mut self) -> (usize, Duration) {
        let start = Instant::now();
        let mut scheduled = 0;

        for pod in &mut self.pods {
            for node in &mut self.nodes {
                if Self::can_fit(pod, node) {
                    // 分配资源
                    node.allocated.0 += pod.requests.0;
                    node.allocated.1 += pod.requests.1;
                    pod.assigned_node = Some(node.name.clone());
                    scheduled += 1;
                    break;
                }
            }
        }

        (scheduled, start.elapsed())
    }

    /// 最佳适配调度（最小剩余资源）
    pub fn schedule_best_fit(&mut self) -> (usize, Duration) {
        let start = Instant::now();
        let mut scheduled = 0;

        for pod in &mut self.pods {
            let mut best_node: Option<usize> = None;
            let mut min_remaining: i64 = i64::MAX;

            for (idx, node) in self.nodes.iter().enumerate() {
                if Self::can_fit(pod, node) {
                    let remaining = Self::calculate_remaining(pod, node);
                    if remaining < min_remaining {
                        min_remaining = remaining;
                        best_node = Some(idx);
                    }
                }
            }

            if let Some(idx) = best_node {
                let node = &mut self.nodes[idx];
                node.allocated.0 += pod.requests.0;
                node.allocated.1 += pod.requests.1;
                pod.assigned_node = Some(node.name.clone());
                scheduled += 1;
            }
        }

        (scheduled, start.elapsed())
    }

    /// 最差适配调度（最大剩余资源）- 负载均衡
    pub fn schedule_worst_fit(&mut self) -> (usize, Duration) {
        let start = Instant::now();
        let mut scheduled = 0;

        for pod in &mut self.pods {
            let mut best_node: Option<usize> = None;
            let mut max_remaining: i64 = -1;

            for (idx, node) in self.nodes.iter().enumerate() {
                if Self::can_fit(pod, node) {
                    let remaining = Self::calculate_remaining(pod, node);
                    if remaining > max_remaining {
                        max_remaining = remaining;
                        best_node = Some(idx);
                    }
                }
            }

            if let Some(idx) = best_node {
                let node = &mut self.nodes[idx];
                node.allocated.0 += pod.requests.0;
                node.allocated.1 += pod.requests.1;
                pod.assigned_node = Some(node.name.clone());
                scheduled += 1;
            }
        }

        (scheduled, start.elapsed())
    }

    /// 资源均衡调度（类似Kubernetes的NodeResourcesBalancedAllocation）
    pub fn schedule_balanced(&mut self) -> (usize, Duration) {
        let start = Instant::now();
        let mut scheduled = 0;

        for pod in &mut self.pods {
            let mut best_node: Option<usize> = None;
            let mut min_variance: f64 = f64::MAX;

            for (idx, node) in self.nodes.iter().enumerate() {
                if Self::can_fit(pod, node) {
                    let variance = Self::calculate_variance(pod, node);
                    if variance < min_variance {
                        min_variance = variance;
                        best_node = Some(idx);
                    }
                }
            }

            if let Some(idx) = best_node {
                let node = &mut self.nodes[idx];
                node.allocated.0 += pod.requests.0;
                node.allocated.1 += pod.requests.1;
                pod.assigned_node = Some(node.name.clone());
                scheduled += 1;
            }
        }

        (scheduled, start.elapsed())
    }

    /// 检查Pod是否能放入节点
    fn can_fit(pod: &SimulatedPod, node: &SimulatedNode) -> bool {
        let available_cpu = node.capacity.0 - node.allocated.0;
        let available_mem = node.capacity.1 - node.allocated.1;

        available_cpu >= pod.requests.0 && available_mem >= pod.requests.1
    }

    /// 计算分配后的剩余资源
    fn calculate_remaining(pod: &SimulatedPod, node: &SimulatedNode) -> i64 {
        let remaining_cpu = node.capacity.0 - node.allocated.0 - pod.requests.0;
        let remaining_mem = node.capacity.1 - node.allocated.1 - pod.requests.1;

        // 加权总和
        remaining_cpu + remaining_mem / 1000000
    }

    /// 计算资源使用方差（越低越均衡）
    fn calculate_variance(pod: &SimulatedPod, node: &SimulatedNode) -> f64 {
        let cpu_usage = (node.allocated.0 + pod.requests.0) as f64 / node.capacity.0 as f64;
        let mem_usage = (node.allocated.1 + pod.requests.1) as f64 / node.capacity.1 as f64;

        let mean = (cpu_usage + mem_usage) / 2.0;
        let variance = ((cpu_usage - mean).powi(2) + (mem_usage - mean).powi(2)) / 2.0;

        variance
    }

    /// 计算资源使用率标准差（评估负载均衡）
    pub fn calculate_load_imbalance(&self) -> f64 {
        let usages: Vec<f64> = self.nodes.iter()
            .map(|n| {
                let cpu_ratio = n.allocated.0 as f64 / n.capacity.0 as f64;
                let mem_ratio = n.allocated.1 as f64 / n.capacity.1 as f64;
                (cpu_ratio + mem_ratio) / 2.0
            })
            .collect();

        let mean = usages.iter().sum::<f64>() / usages.len() as f64;
        let variance = usages.iter()
            .map(|&u| (u - mean).powi(2))
            .sum::<f64>() / usages.len() as f64;

        variance.sqrt()
    }

    /// 打印统计信息
    pub fn print_stats(&self, algorithm: &str, scheduled: usize, duration: Duration) {
        let total_requested_cpu: i64 = self.pods.iter().map(|p| p.requests.0).sum();
        let total_requested_mem: i64 = self.pods.iter().map(|p| p.requests.1).sum();
        let total_capacity_cpu: i64 = self.nodes.iter().map(|n| n.capacity.0).sum();
        let total_capacity_mem: i64 = self.nodes.iter().map(|n| n.capacity.1).sum();

        println!("\n=== {} ===", algorithm);
        println!("Scheduled: {}/{} pods", scheduled, self.pod_count);
        println!("Duration: {:?}", duration);
        println!("Throughput: {:.2} pods/sec", scheduled as f64 / duration.as_secs_f64());
        println!("Resource utilization: CPU {:.2}%, Memory {:.2}%",
            total_requested_cpu as f64 / total_capacity_cpu as f64 * 100.0,
            total_requested_mem as f64 / total_capacity_mem as f64 * 100.0
        );
        println!("Load imbalance (std dev): {:.4}", self.calculate_load_imbalance());
    }

    /// 重置状态
    pub fn reset(&mut self) {
        for node in &mut self.nodes {
            node.allocated = (0, 0);
        }
        for pod in &mut self.pods {
            pod.assigned_node = None;
        }
    }
}

/// 运行模拟测试
pub fn run_simulation() {
    println!("Starting scheduling simulation...\n");

    let mut simulator = SchedulerSimulator::new(100, 1000);
    simulator.initialize();

    // 测试不同算法
    let mut sim_clone = simulator.clone();
    let (scheduled, duration) = sim_clone.schedule_first_fit();
    sim_clone.print_stats("First Fit", scheduled, duration);

    simulator.reset();
    let mut sim_clone = simulator.clone();
    let (scheduled, duration) = sim_clone.schedule_best_fit();
    sim_clone.print_stats("Best Fit", scheduled, duration);

    simulator.reset();
    let mut sim_clone = simulator.clone();
    let (scheduled, duration) = sim_clone.schedule_worst_fit();
    sim_clone.print_stats("Worst Fit", scheduled, duration);

    simulator.reset();
    let mut sim_clone = simulator.clone();
    let (scheduled, duration) = sim_clone.schedule_balanced();
    sim_clone.print_stats("Balanced (K8s-like)", scheduled, duration);
}

fn main() {
    run_simulation();
}
```

### 8.3 性能基准测试

```rust
// benches/scheduler_bench.rs
// 调度器性能基准测试

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use scheduler::{Scheduler, Node, Pod, NodeResourcesFit, LeastAllocated};

fn bench_filter_phase(c: &mut Criterion) {
    let mut group = c.benchmark_group("filter_phase");

    for node_count in [10, 100, 500, 1000].iter() {
        group.bench_with_input(
            BenchmarkId::new("nodes", node_count),
            node_count,
            |b, &node_count| {
                let mut scheduler = Scheduler::new();

                // 添加节点
                for i in 0..node_count {
                    scheduler.add_node(Node::new(&format!("node-{}", i), 4000, 16000000000));
                }

                // 注册Filter插件
                scheduler.add_filter_plugin(Box::new(NodeResourcesFit));

                let pod = Pod::new("test-pod", 500, 1000000000);

                b.iter(|| {
                    let _ = scheduler.schedule(black_box(&pod));
                });
            }
        );
    }

    group.finish();
}

fn bench_score_phase(c: &mut Criterion) {
    let mut group = c.benchmark_group("score_phase");

    for node_count in [10, 50, 100].iter() {
        group.bench_with_input(
            BenchmarkId::new("nodes", node_count),
            node_count,
            |b, &node_count| {
                let mut scheduler = Scheduler::new();

                // 添加所有节点
                for i in 0..node_count {
                    scheduler.add_node(Node::new(&format!("node-{}", i), 4000, 16000000000));
                }

                // 注册Score插件
                scheduler.add_score_plugin(Box::new(LeastAllocated), 1);

                let pod = Pod::new("test-pod", 500, 1000000000);

                b.iter(|| {
                    let _ = scheduler.schedule(black_box(&pod));
                });
            }
        );
    }

    group.finish();
}

criterion_group!(benches, bench_filter_phase, bench_score_phase);
criterion_main!(benches);
```

### 8.4 Cargo.toml配置

```toml
# Cargo.toml
[package]
name = "k8s-scheduler-rust"
version = "0.1.0"
edition = "2021"

[dependencies]
async-trait = "0.1"
tokio = { version = "1", features = ["full"] }
rand = "0.8"
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
log = "0.4"
env_logger = "0.10"

[dev-dependencies]
criterion = { version = "0.5", features = ["async_tokio"] }
tokio-test = "0.4"

[[bench]]
name = "scheduler_bench"
harness = false
```

---

## 总结

本文档深入分析了Kubernetes调度系统的各个方面：

1. **架构层面**：详细剖析了控制平面和数据平面的组件，以及调度器在其中的位置和交互方式。

2. **调度框架**：深入讲解了Scheduling Framework的设计理念、扩展点接口和插件注册机制。

3. **调度算法**：系统分析了Filter（预选）和Score（优选）阶段的实现原理和核心算法。

4. **调度策略**：详细说明了各种调度约束（NodeName、NodeSelector、Affinity、Taints、TopologySpread）的配置和实现。

5. **源码分析**：从scheduler.go、framework.go、cache.go等核心文件深入讲解了调度器的源码实现。

6. **性能优化**：提供了大规模集群的优化方案，包括节点采样、并行化、多调度器部署等。

7. **形式化分析**：使用数学方法证明了调度算法的正确性、安全性和终止性。

8. **实践案例**：提供了生产环境的配置模板、问题排查脚本和性能调优案例。

9. **Rust实现**：提供了简化版调度器的Rust实现，包括核心框架、插件系统和性能模拟。

Kubernetes调度系统是一个复杂而精密的分布式系统组件，其设计充分考虑了扩展性、性能和可靠性。通过深入理解其内部原理，可以更好地进行集群规划、故障排查和性能优化。

---

## 参考资源

1. Kubernetes官方文档：https://kubernetes.io/docs/concepts/scheduling-eviction/
2. Kubernetes源码：https://github.com/kubernetes/kubernetes/tree/master/pkg/scheduler
3. 《Kubernetes权威指南》（第五版）
4. Kubernetes Scheduler Framework设计文档：https://kubernetes.io/docs/concepts/scheduling-eviction/scheduling-framework/
5. CNCF官方最佳实践指南

---

_文档版本：v1.0_
_基于Kubernetes版本：v1.28+_
_创建日期：2026-04-12_
