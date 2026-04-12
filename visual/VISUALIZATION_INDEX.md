# 可视化图表详细索引

## 架构图 (Architecture)

### 1. system_overall_architecture.md

| 图表 | 类型 | 描述 |
|------|------|------|
| FormalScience项目层次架构 | flowchart TB | 展示项目4层架构 |
| 调度系统层次架构 | flowchart TB | 从硬件到应用5层调度 |
| 知识表示架构 | flowchart LR | 概念→表示→应用3层 |
| 多视角对应架构 | flowchart TB | 调度系统多视角映射 |
| 数据流架构 | flowchart TB | 从输入到输出的处理流 |

### 2. module_dependency.md

| 图表 | 类型 | 描述 |
|------|------|------|
| 核心模块依赖图 | flowchart TD | 基础→理论→建模→应用 |
| 调度模型模块依赖 | flowchart TD | 硬件→OS→虚拟化→分布式 |
| 形式化方法模块依赖 | flowchart LR | 数学→形式化→验证→应用 |
| 知识库模块依赖 | flowchart TB | 元数据→内容→表示→输出 |
| 跨层次依赖关系 | flowchart TB | L1理论→L2模型→L3设计→L4实现 |

### 3. layer_hierarchy.md

| 图表 | 类型 | 描述 |
|------|------|------|
| 调度系统层次金字塔 | flowchart TB | 金字塔形6层结构 |
| 形式化抽象层次 | flowchart BT | 实现→算法→模型→数学 |
| 虚拟化层次栈 | flowchart LR | Guest→VMM→Host→HW |
| 容器层次栈 | flowchart LR | App→Container→Runtime→OS→HW |
| 调度层次时间粒度 | flowchart TB | ns→μs→ms→s→min |
| 知识抽象层次 | flowchart TB | 实例→模式→理论→元理论 |

---

## 流程图 (Flowcharts)

### 4. scheduling_algorithms.md

| 图表 | 类型 | 描述 |
|------|------|------|
| CFS算法流程 | flowchart TD | 完全公平调度器完整流程 |
| 电梯算法(SCAN) | flowchart TD | 磁盘调度SCAN算法 |
| 优先级调度算法 | flowchart TD | 多级优先级调度 |
| 多级反馈队列MLFQ | flowchart TD | 4级队列时间片调度 |
| 最短作业优先SJF | flowchart TD | SJF作业调度 |
| 银行家算法 | flowchart TD | 死锁避免算法 |
| 工作窃取算法 | flowchart TD | Work Stealing并行调度 |
| Kubernetes调度器 | flowchart TD | K8s Filter+Score+Bind |

### 5. system_calls.md

| 图表 | 类型 | 描述 |
|------|------|------|
| 通用系统调用 | sequenceDiagram | 用户态→内核态流程 |
| fork()流程 | flowchart TD | 进程创建完整流程 |
| execve()流程 | flowchart TD | 程序执行流程 |
| mmap()流程 | flowchart TD | 内存映射流程 |
| pipe()流程 | flowchart TD | 管道读写流程 |
| select()/poll()流程 | flowchart TD | IO多路复用流程 |

### 6. interrupt_handling.md

| 图表 | 类型 | 描述 |
|------|------|------|
| 硬件中断处理 | flowchart TD | 完整中断处理流程 |
| SoftIRQ/Tasklet | flowchart TD | 软中断处理流程 |
| 系统调用中断 | flowchart TD | syscall指令处理 |
| 时钟中断处理(Tick) | flowchart TD | 定时器中断处理 |
| NMI处理 | flowchart TD | 不可屏蔽中断 |
| 中断上下半部协作 | sequenceDiagram | Top/Bottom Half协作 |
| 中断嵌套处理 | flowchart TD | 嵌套中断处理 |

---

## 状态图 (State Diagrams)

### 7. process_state_machine.md

| 图表 | 类型 | 描述 |
|------|------|------|
| Linux进程状态机 | stateDiagram-v2 | 7种基本状态转换 |
| 详细进程生命周期 | stateDiagram-v2 | 12种详细状态 |
| 线程状态机 | stateDiagram-v2 | pthread状态转换 |
| 实时进程状态机 | stateDiagram-v2 | 实时调度状态 |
| 进程状态转换矩阵 | flowchart TB | 状态转换表格 |

### 8. task_state_machine.md

| 图表 | 类型 | 描述 |
|------|------|------|
| Kubernetes Pod生命周期 | stateDiagram-v2 | Pod 5种状态 |
| 工作流任务状态机 | stateDiagram-v2 | 任务11种状态 |
| 批处理作业状态机 | stateDiagram-v2 | 作业14种状态 |
| 协程状态机 | stateDiagram-v2 | Coroutine 7种状态 |
| 定时任务状态机 | stateDiagram-v2 | 定时任务10种状态 |
| 任务依赖状态机 | stateDiagram-v2 | 依赖任务12种状态 |

### 9. transaction_consensus.md

| 图表 | 类型 | 描述 |
|------|------|------|
| 两阶段提交(2PC) | stateDiagram-v2 | 协调者状态机 |
| 参与者状态机 | stateDiagram-v2 | 2PC参与者状态 |
| Raft共识算法 | stateDiagram-v2 | 3种角色状态转换 |
| Paxos状态机 | stateDiagram-v2 | Paxos提案状态 |
| Saga分布式事务 | stateDiagram-v2 | Saga补偿状态 |
| PBFT状态机 | stateDiagram-v2 | 拜占庭容错状态 |
| 数据库事务ACID | stateDiagram-v2 | 事务4种状态 |

---

## 时序图 (Sequence Diagrams)

### 10. system_calls.md

| 图表 | 类型 | 描述 |
|------|------|------|
| read()系统调用 | sequenceDiagram | 7个参与者的完整流程 |
| write()系统调用 | sequenceDiagram | 同步/异步写流程 |
| fork()+execve() | sequenceDiagram | 进程创建+执行 |
| mmap()时序 | sequenceDiagram | 内存映射详细流程 |
| pipe()时序 | sequenceDiagram | 管道读写交互 |
| futex()同步原语 | sequenceDiagram | 用户态/内核态协作 |

### 11. distributed_transactions.md

| 图表 | 类型 | 描述 |
|------|------|------|
| 两阶段提交(2PC) | sequenceDiagram | 投票+提交/回滚 |
| 三阶段提交(3PC) | sequenceDiagram | Can+Pre+Do Commit |
| Saga分布式事务 | sequenceDiagram | 补偿事务流程 |
| TCC | sequenceDiagram | Try-Confirm-Cancel |
| 消息队列最终一致性 | sequenceDiagram | 消息表+MQ模式 |

### 12. protocol_interactions.md

| 图表 | 类型 | 描述 |
|------|------|------|
| TCP三次握手/四次挥手 | sequenceDiagram | 完整TCP状态转换 |
| Raft共识交互 | sequenceDiagram | Leader-Follower交互 |
| Kubernetes Pod创建 | sequenceDiagram | 6个组件交互 |
| gRPC调用流程 | sequenceDiagram | 一元/流式RPC |
| 数据库两阶段锁 | sequenceDiagram | 2PL锁获取释放 |
| MESI缓存一致性 | sequenceDiagram | 缓存状态转换 |
| ZooKeeper领导者选举 | sequenceDiagram | Fast Leader Election |

---

## 类图 (Class Diagrams)

### 13. scheduler_hierarchy.md

| 图表 | 类型 | 描述 |
|------|------|------|
| Linux调度器类层次 | classDiagram | 5种调度类 |
| 调度实体关系 | classDiagram | task_struct完整关系 |
| Kubernetes调度器架构 | classDiagram | Scheduler+Algorithm+
| 容器运行时接口CRI | classDiagram | Runtime+Image Service |
| 虚拟化层架构 | classDiagram | Hypervisor+VM+VCPU |

### 14. data_structures.md

| 图表 | 类型 | 描述 |
|------|------|------|
| 进程控制块关系 | classDiagram | task_struct关联结构 |
| 内存管理数据结构 | classDiagram | pglist_data→page层次 |
| 文件系统核心结构 | classDiagram | super_block→inode→file |
| 网络协议栈结构 | classDiagram | sock→sk_buff→net_device |
| 红黑树调度结构 | classDiagram | rb_root→sched_entity |
| Petri网核心结构 | classDiagram | PetriNet+Place+Transition |

---

## 知识图谱 (Knowledge Graph)

### 15. knowledge_graph.md

| 图表 | 类型 | 描述 |
|------|------|------|
| 核心概念关系图 | graph TB | 5大领域关联 |
| 学习路径图 | graph LR | 4层学习路线 |
| 概念依赖关系图 | graph TB | 4层依赖关系 |
| 多视角知识图谱 | graph TB | 6视角核心关联 |
| 调度算法知识图谱 | mindmap | 调度算法完整分类 |
| 虚拟化技术知识图谱 | mindmap | 虚拟化技术全景 |
| 形式化方法知识图谱 | mindmap | 形式化方法体系 |
| 跨层次映射关系 | graph TB | 5层映射关系 |
| 技术演进时间线 | graph LR | 1960s-2020s演进 |
| 概念到实现映射 | graph TB | 4层映射关系 |

---

## 统计汇总

### 按文件统计

| 序号 | 文件名 | 图表数 |
|------|--------|--------|
| 1 | architecture/system_overall_architecture.md | 5 |
| 2 | architecture/module_dependency.md | 5 |
| 3 | architecture/layer_hierarchy.md | 6 |
| 4 | flowcharts/scheduling_algorithms.md | 8 |
| 5 | flowcharts/system_calls.md | 6 |
| 6 | flowcharts/interrupt_handling.md | 7 |
| 7 | state_diagrams/process_state_machine.md | 5 |
| 8 | state_diagrams/task_state_machine.md | 6 |
| 9 | state_diagrams/transaction_consensus.md | 7 |
| 10 | sequence_diagrams/system_calls.md | 6 |
| 11 | sequence_diagrams/distributed_transactions.md | 5 |
| 12 | sequence_diagrams/protocol_interactions.md | 7 |
| 13 | class_diagrams/scheduler_hierarchy.md | 5 |
| 14 | class_diagrams/data_structures.md | 6 |
| 15 | knowledge_graph.md | 10 |
| **总计** | **15个文件** | **99个图表** |

### 按类型统计

| 类型 | 数量 | 占比 |
|------|------|------|
| flowchart | 32 | 32% |
| stateDiagram | 21 | 21% |
| sequenceDiagram | 18 | 18% |
| graph | 12 | 12% |
| classDiagram | 11 | 11% |
| mindmap | 3 | 3% |
| other | 2 | 2% |

### 按主题统计

| 主题 | 图表数 |
|------|--------|
| 调度系统 | 25 |
| 操作系统内核 | 20 |
| 虚拟化/容器 | 15 |
| 分布式系统 | 14 |
| 形式化方法 | 12 |
| 网络协议 | 8 |
| 其他 | 5 |

---

## 使用方式

### 在VS Code中查看

安装 Mermaid 插件后，Markdown文件中的图表会自动渲染。

### 在GitHub/GitLab中查看

这些图表原生支持在GitHub/GitLab中渲染。

### 导出为图片

使用 [Mermaid Live Editor](https://mermaid.live/) 或命令行工具导出。

---

**最后更新**: 2026-04-12
**维护者**: FormalScience Project
