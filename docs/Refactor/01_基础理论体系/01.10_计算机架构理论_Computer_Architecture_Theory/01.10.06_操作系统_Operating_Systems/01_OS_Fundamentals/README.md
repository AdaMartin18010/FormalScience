# 操作系统基础（OS Fundamentals）

## 📋 目录

- [操作系统基础（OS Fundamentals）](#操作系统基础os-fundamentals)
  - [📋 目录](#-目录)
  - [1 学习路径](#1-学习路径)
  - [2 交叉引用](#2-交叉引用)
  - [3 推荐阅读](#3-推荐阅读)
  - [4 批判性视角简](#4-批判性视角简)

---

## 1 学习路径

- 进程与线程：抽象、调度、同步、死锁
- 内存管理：分页、分段、虚拟内存、置换算法
- 文件与存储：文件系统、日志、I/O 调度
- 设备与中断：驱动、DMA、缓存一致性
- 并发与同步：互斥、条件变量、锁/无锁数据结构
- 安全与隔离：权限、沙箱、系统调用接口

## 2 交叉引用

- 计算机体系结构：`../..` 目录中的缓存、总线、NUMA 影响 OS 设计
- 并发理论：见 `docs/Refactor/13_Concurrency_Theory`
- 分布式系统：见 `docs/Refactor/11_Distributed_Systems_Theory`

## 3 推荐阅读

- Silberschatz et al. Operating System Concepts
- Tanenbaum. Modern Operating Systems

## 4 批判性视角简

- 资源抽象与开销：抽象边界的代价与可观测性
- 一致性与性能：持久化、一致性、延迟三者的权衡
- 安全边界：最小权限与可用性的张力

---
最后更新: 2025-01-26
