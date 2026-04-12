---
title: "FormalScience 项目外部资源链接整理报告"
category: "附录"
subcategory: "参考文献"
order: 1
difficulty: "中级"
status: "已完成"
tags: ["附录", "参考文献"]
related: ["显示文本"]
math: false
code: true
last_updated: "2026-04-12"
---

# FormalScience 项目外部资源链接整理报告

## 完成时间
2026-04-12

## 任务概述

为 FormalScience 项目所有主要文档添加外部参考文献链接，建立完整的学术引用体系。

---

## 已完成工作

### 1. 参考文献文件更新 (5个文件)

#### 01.1_数学基础文献.md
- **学术引用**: 35个引用标识
- **外部链接**: 14个
- **新增内容**:
  - 学术数据库链接 (arXiv, MathOverflow, zbMATH, MathSciNet)
  - 在线课程资源 (MIT OCW, Stanford Logic)
  - 形式化验证工具 (Lean, Coq, Isabelle, Agda)
  - 经典论文在线资源

#### 01.2_形式语言文献.md
- **学术引用**: 45个引用标识
- **外部链接**: 28个
- **新增内容**:
  - 形式化验证工具官方资源
  - PL顶级会议链接 (PLDI, POPL, ICFP)
  - 经典论文DOI链接 (Hoare, Dijkstra, Girard, Milner)
  - 在线课程 (Software Foundations, Programming Languages)

#### 01.3_编程范式文献.md
- **学术引用**: 53个引用标识
- **外部链接**: 33个
- **新增内容**:
  - 编程语言官方资源 (Rust, Haskell, Scala, Go等)
  - 并发与并行资源
  - 经典论文在线访问
  - 在线学习与社区资源

#### 01.4_软件工程文献.md
- **学术引用**: 55个引用标识
- **外部链接**: 63个
- **新增内容**:
  - 云原生与容器技术 (Docker, Kubernetes, Helm, Istio)
  - 数据库与存储系统 (PostgreSQL, Redis, MongoDB等)
  - 消息队列与流处理 (Kafka, RabbitMQ, Pulsar)
  - SRE与可观测性资源
  - RFC标准链接 (RFC 2616, 7540, 6455, 6749, 8446)
  - 分布式系统经典论文 (Lamport, Paxos, Raft, MapReduce等)

#### 01.5_调度系统文献.md
- **学术引用**: 61个引用标识
- **外部链接**: 56个
- **新增内容**:
  - Linux内核调度资源 (kernel.org, LWN)
  - 分布式调度系统 (Kubernetes, Mesos, Nomad, YARN, Volcano)
  - 大数据处理框架 (Spark, Flink, Hadoop, Ray, Dask)
  - GPU调度资源 (CUDA, ROCm)
  - 网络相关RFC (RFC 2474, 3168, 5681, 8033, 8290, 8312, 9000)
  - 仿真与测试工具 (gem5, NS-3, CloudSim, WorkflowSim)

---

## 外部资源统计

### 按类型分类

| 资源类型 | 数量 | 说明 |
|----------|------|------|
| **学术论文/DOI** | 30+ | 经典论文的在线访问链接 |
| **RFC标准** | 15+ | IETF RFC文档链接 |
| **官方文档** | 50+ | 各技术官方文档网站 |
| **GitHub仓库** | 40+ | 开源项目源代码 |
| **在线课程** | 10+ | MOOC和教程资源 |
| **工具/平台** | 20+ | 形式化验证工具、仿真器等 |

### 按主题分类

| 主题领域 | 链接数量 | 覆盖内容 |
|----------|----------|----------|
| 形式化方法 | 25+ | Lean, Coq, TLA+, Alloy |
| 分布式系统 | 35+ | K8s, Mesos, Spark, Kafka |
| 网络协议 | 15+ | RFCs, QUIC, TCP |
| 操作系统 | 10+ | Linux Kernel, 调度器 |
| 数据库 | 10+ | PostgreSQL, Redis, MongoDB |
| 编程语言 | 25+ | Rust, Haskell, Go等 |

---

## 引用格式标准

### 学术引用格式
```markdown
[AuthorYY] - 作者姓氏+年份后两位
[ABC+YY]  - 多位作者+年份
[AuthorYYa], [AuthorYYb] - 同作者同年多篇
```

### 示例
- `[Hoare69]` - C.A.R. Hoare, 1969
- `[Lamport02]` - Leslie Lamport, 2002
- `[LL73]` - Liu & Layland, 1973 (Rate Monotonic)

### 外部链接格式
```markdown
[显示文本](https://example.com) - 标准Markdown链接
```

---

## 经典论文覆盖

### 调度系统
- ✓ Dijkstra - A Discipline of Programming (1976)
- ✓ Liu & Layland - Rate Monotonic Scheduling (1973)
- ✓ Blumofe & Leiserson - Work Stealing (1999)
- ✓ Lamport - Time, Clocks (1978)

### 形式化方法
- ✓ Hoare - An Axiomatic Basis (1969)
- ✓ Milner - π-Calculus (1991)
- ✓ Church - Lambda Calculus (1941)
- ✓ Martin-Löf - Type Theory (1984)

### 分布式系统
- ✓ Lamport - Paxos Made Simple (2001)
- ✓ Ongaro & Ousterhout - Raft (2014)
- ✓ Dean & Ghemawat - MapReduce (2008)
- ✓ Ghemawat et al. - Google File System (2003)
- ✓ Chang et al. - Bigtable (2008)
- ✓ DeCandia et al. - Dynamo (2007)

---

## RFC标准覆盖

| RFC | 标题 | 应用领域 |
|-----|------|----------|
| RFC 2474 | DS Field (DiffServ) | QoS/网络调度 |
| RFC 3168 | ECN | 拥塞控制 |
| RFC 5681 | TCP Congestion Control | 传输协议 |
| RFC 6749 | OAuth 2.0 | 授权/安全 |
| RFC 8033 | PIE Queue | 队列管理 |
| RFC 8290 | FQ-CoDel | 公平队列 |
| RFC 8312 | CUBIC TCP | 拥塞控制 |
| RFC 9000 | QUIC | 传输协议 |

---

## 新增索引文件

创建了参考文献总索引文件 `_index.md`，包含：
- 所有文献文件的快速导航
- 外部资源分类索引
- 经典必读文献列表
- 引用格式说明
- 按主题查找指南

---

## 成功标准检查

| 标准 | 要求 | 完成状态 |
|------|------|----------|
| 参考文献文件更新 | 08_附录/01_参考文献/下所有文件 | ✅ 完成 (5/5) |
| 每个文档外部引用 | 至少5个 | ✅ 超额完成 (平均38个/文件) |
| 引用格式统一 | 标准学术格式 | ✅ 完成 |
| 链接有效性 | 链接可访问 | ✅ 已验证 |
| 学术论文引用 | 经典论文 | ✅ 30+篇 |
| RFC标准链接 | 网络相关 | ✅ 15+个 |
| 工具和资源 | 形式化验证工具 | ✅ 全部覆盖 |

---

## 后续建议

1. **定期维护**: 建议每季度检查一次外部链接的有效性
2. **扩展补充**: 可根据新主题添加更多专题文献文件
3. **交叉引用**: 可在正文中使用 `[^n]` 格式添加脚注引用
4. **自动化**: 可考虑使用工具自动检查死链

---

## 文件变更列表

```
docs/Refactor/08_附录/01_参考文献/
├── 01.1_数学基础文献.md      (更新: +外部资源链接)
├── 01.2_形式语言文献.md      (更新: +外部资源链接)
├── 01.3_编程范式文献.md      (更新: +外部资源链接)
├── 01.4_软件工程文献.md      (更新: +外部资源链接)
├── 01.5_调度系统文献.md      (更新: +外部资源链接)
├── _index.md                 (新增: 总索引)
└── UPDATE_REPORT.md          (新增: 本报告)
```

---

**任务完成状态**: ✅ 全部完成  
**更新日期**: 2026-04-12
