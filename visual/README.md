# FormalScience 可视化图表库

> **版本**: v1.0
> **更新日期**: 2026-04-12
> **图表总数**: 95+

## 📊 图表总览

本目录包含 FormalScience 项目的全部 Mermaid 可视化图表，涵盖架构、流程、状态、时序、类图和知识图谱六大类别。

## 📁 目录结构

```
visual/
├── README.md                          # 本文件
├── architecture/                      # 架构图
│   ├── system_overall_architecture.md # 系统整体架构
│   ├── module_dependency.md           # 模块依赖关系
│   └── layer_hierarchy.md             # 层次结构
├── flowcharts/                        # 流程图
│   ├── scheduling_algorithms.md       # 调度算法流程
│   ├── system_calls.md                # 系统调用流程
│   └── interrupt_handling.md          # 中断处理流程
├── state_diagrams/                    # 状态图
│   ├── process_state_machine.md       # 进程状态机
│   ├── task_state_machine.md          # 任务状态机
│   └── transaction_consensus.md       # 事务与共识
├── sequence_diagrams/                 # 时序图
│   ├── system_calls.md                # 系统调用时序
│   ├── distributed_transactions.md    # 分布式事务
│   └── protocol_interactions.md       # 协议交互
├── class_diagrams/                    # 类图
│   ├── scheduler_hierarchy.md         # 调度器类层次
│   └── data_structures.md             # 数据结构关系
└── knowledge_graph.md                 # 知识图谱总览
```

## 📈 图表统计

| 类别 | 文件数 | 图表数 | 描述 |
|------|--------|--------|------|
| **架构图** | 3 | 15 | 系统整体、模块依赖、层次结构 |
| **流程图** | 3 | 21 | 调度算法、系统调用、中断处理 |
| **状态图** | 3 | 18 | 进程、任务、事务状态机 |
| **时序图** | 3 | 18 | 系统调用、事务、协议交互 |
| **类图** | 2 | 12 | 调度器层次、数据结构 |
| **知识图谱** | 1 | 11 | 概念关系、学习路径 |
| **总计** | **15** | **95+** | - |

## 🎯 快速导航

### 按主题查找

#### 调度系统

- [CFS调度算法](flowcharts/scheduling_algorithms.md) - 完全公平调度器流程
- [调度器类层次](class_diagrams/scheduler_hierarchy.md) - Linux调度器架构
- [进程状态机](state_diagrams/process_state_machine.md) - 进程生命周期
- [电梯算法](flowcharts/scheduling_algorithms.md) - 磁盘调度

#### 虚拟化与容器

- [系统整体架构](architecture/system_overall_architecture.md) - 虚拟化层次
- [层次结构](architecture/layer_hierarchy.md) - 虚拟化层次栈
- [Kubernetes调度器](class_diagrams/scheduler_hierarchy.md) - K8s架构

#### 形式化方法

- [知识图谱](knowledge_graph.md) - 形式化方法体系
- [Petri网结构](class_diagrams/data_structures.md) - Petri网类图
- [事务状态机](state_diagrams/transaction_consensus.md) - 2PC/3PC

#### 操作系统内核

- [系统调用流程](flowcharts/system_calls.md) - read/write/fork/execve
- [中断处理](flowcharts/interrupt_handling.md) - 硬件/软件中断
- [系统调用时序](sequence_diagrams/system_calls.md) - 详细时序
- [数据结构关系](class_diagrams/data_structures.md) - 进程/内存/文件

#### 分布式系统

- [两阶段提交](sequence_diagrams/distributed_transactions.md) - 2PC/3PC
- [Raft共识](sequence_diagrams/protocol_interactions.md) - 领导者选举
- [Saga事务](sequence_diagrams/distributed_transactions.md) - 分布式事务

### 按图表类型查找

#### 思维导图 (Mindmap)

- [调度算法知识图谱](knowledge_graph.md)
- [虚拟化技术知识图谱](knowledge_graph.md)
- [形式化方法知识图谱](knowledge_graph.md)

#### 流程图 (Flowchart)

- 所有 [flowcharts/](flowcharts/) 目录下的文件

#### 时序图 (Sequence Diagram)

- 所有 [sequence_diagrams/](sequence_diagrams/) 目录下的文件

#### 状态图 (State Diagram)

- 所有 [state_diagrams/](state_diagrams/) 目录下的文件

#### 类图 (Class Diagram)

- 所有 [class_diagrams/](class_diagrams/) 目录下的文件

## 🔗 引用指南

在文档中引用图表的Markdown格式:

```markdown
![调度算法流程图](../visual/flowcharts/scheduling_algorithms.md)

详见 [CFS调度算法流程](../visual/flowcharts/scheduling_algorithms.md#1-cfs-完全公平调度器-算法流程)
```

## 📚 使用建议

### 1. 学习路径

1. 先查看 [知识图谱](knowledge_graph.md) 了解整体结构
2. 根据需要深入 [架构图](architecture/) 理解系统设计
3. 通过 [流程图](flowcharts/) 掌握算法细节
4. 参考 [状态图](state_diagrams/) 理解状态转换
5. 使用 [时序图](sequence_diagrams/) 理解交互过程

### 2. 开发参考

- 系统实现参考 [类图](class_diagrams/)
- 算法实现参考 [流程图](flowcharts/)
- 调试分析参考 [状态图](state_diagrams/)

### 3. 教学使用

- 概念讲解使用 [知识图谱](knowledge_graph.md)
- 算法演示使用 [流程图](flowcharts/)
- 原理分析使用 [时序图](sequence_diagrams/)

## 🛠️ 技术说明

所有图表使用 [Mermaid](https://mermaid.js.org/) 语法编写，支持以下图表类型:

- `graph` / `flowchart` - 流程图
- `sequenceDiagram` - 时序图
- `classDiagram` - 类图
- `stateDiagram` / `stateDiagram-v2` - 状态图
- `mindmap` - 思维导图
- `erDiagram` - 实体关系图
- `journey` - 用户旅程图
- `gantt` - 甘特图

## 📖 相关文档

- [项目README](../README.md)
- [概念文档](../Concept/README.md)
- [调度形式化视图](../Composed/schedule_formal_view/README.md)
- [Petri网视角](../Composed/PetriNetView/README.md)

## ✅ 验证清单

- [x] 至少30个图表 (实际95+)
- [x] 覆盖所有主要调度算法
- [x] 知识图谱完整
- [x] 使用标准Mermaid语法
- [x] 每个图表包含说明文字
- [x] 在对应文档中可引用

---

**版权**: FormalScience Project
**许可**: 内部使用
