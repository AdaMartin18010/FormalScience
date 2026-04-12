# 参考文献总览

## 概述

本文档汇总了 FormalScience 项目所有主题的参考文献资源，建立了完整的学术引用体系和外部资源链接网络。

## 文献分类

| 文献类别 | 文件 | 主要主题 | 引用数量 | 外部链接 |
|----------|------|----------|----------|----------|
| 数学基础 | [01.1_数学基础文献.md](./01.1_数学基础文献.md) | 集合论、类型论、数理逻辑、计算理论 | 35 | 14 |
| 形式语言 | [01.2_形式语言文献.md](./01.2_形式语言文献.md) | λ演算、类型系统、形式语义、形式化方法 | 45 | 28 |
| 编程范式 | [01.3_编程范式文献.md](./01.3_编程范式文献.md) | 函数式、OO、并发、系统编程 | 53 | 33 |
| 软件工程 | [01.4_软件工程文献.md](./01.4_软件工程文献.md) | 设计模式、测试、DevOps、SRE | 55 | 63 |
| 调度系统 | [01.5_调度系统文献.md](./01.5_调度系统文献.md) | 实时调度、OS调度、分布式调度 | 61 | 56 |

**总计**: 5个文件 | 249个学术引用 | 194个外部链接

---

## 外部资源类型

### 1. 学术论文与经典著作

#### 调度系统经典论文
- Dijkstra - _A Discipline of Programming_ (1976)
- Liu & Layland - Rate Monotonic Scheduling (1973)
- Blumofe & Leiserson - Work Stealing (1999)
- Lamport - Time, Clocks, and the Ordering of Events (1978)

#### 形式化方法经典论文
- Hoare - _An Axiomatic Basis for Computer Programming_ (1969)
- Milner - _The Polyadic π-Calculus_ (1991)
- Church - _The Calculi of Lambda Conversion_ (1941)
- Martin-Löf - _Intuitionistic Type Theory_ (1984)

#### 分布式系统经典论文
- Lamport - Paxos Made Simple (2001)
- Ongaro & Ousterhout - Raft (2014)
- Dean & Ghemawat - MapReduce (2008)
- Corbett et al. - Spanner (2013)

### 2. RFC标准链接

| RFC | 标题 | 领域 |
|-----|------|------|
| RFC 2474 | Definition of DS Field | QoS/DiffServ |
| RFC 3168 | ECN | 拥塞控制 |
| RFC 5681 | TCP Congestion Control | 网络协议 |
| RFC 8033 | PIE Queue | 队列管理 |
| RFC 8290 | FQ-CoDel | 公平队列 |
| RFC 8312 | CUBIC TCP | 拥塞控制 |
| RFC 9000 | QUIC | 传输协议 |

更多详见各专题文献文件中的RFC章节。

### 3. 教材和经典书籍

| 书名 | 作者 | 年份 | 适用主题 |
|------|------|------|----------|
| _Computer Networks_ | Kurose & Ross | 2021 | 网络基础 |
| _Modern Operating Systems_ | Tanenbaum | 2014 | 操作系统 |
| _Types and Programming Languages_ | Benjamin Pierce | 2002 | 类型理论 |
| _Design Patterns_ | Gamma et al. | 1994 | 软件设计 |
| _Designing Data-Intensive Applications_ | Martin Kleppmann | 2017 | 数据系统 |
| _Operating Systems: Three Easy Pieces_ | Remzi Arpaci-Dusseau | 2018 | OS教学 |

### 4. 在线资源

#### 官方文档
- [Linux Kernel Documentation](https://docs.kernel.org/)
- [Kubernetes Documentation](https://kubernetes.io/docs/)
- [Docker Documentation](https://docs.docker.com/)
- [PostgreSQL Documentation](https://www.postgresql.org/docs/)

#### 学术资源
- [arXiv cs.PL](https://arxiv.org/cs.PL) - 编程语言预印本
- [ACM Digital Library](https://dl.acm.org/)
- [IEEE Xplore](https://ieeexplore.ieee.org/)

#### 开源项目
- [Linux Kernel (GitHub)](https://github.com/torvalds/linux)
- [Kubernetes (GitHub)](https://github.com/kubernetes/kubernetes)
- [Apache Spark (GitHub)](https://github.com/apache/spark)
- [Rust (GitHub)](https://github.com/rust-lang/rust)

### 5. 形式化验证工具

| 工具 | 类型 | 官方网站 | GitHub |
|------|------|----------|--------|
| **Lean 4** | 定理证明器 | [leanprover.github.io](https://leanprover.github.io/) | [leanprover/lean4](https://github.com/leanprover/lean4) |
| **Coq** | 定理证明器 | [coq.inria.fr](https://coq.inria.fr/) | [coq/coq](https://github.com/coq/coq) |
| **Isabelle/HOL** | 定理证明器 | [isabelle.in.tum.de](https://isabelle.in.tum.de/) | [isabelle-dev](https://isabelle-dev.sketis.net/) |
| **TLA+** | 形式化规范 | [lamport.azurewebsites.net](https://lamport.azurewebsites.net/tla/tla.html) | [tlaplus/tlaplus](https://github.com/tlaplus/tlaplus) |
| **Alloy** | 建模分析 | [alloytools.org](https://alloytools.org/) | [AlloyTools](https://github.com/AlloyTools) |

---

## 引用格式说明

### 学术引用格式

```markdown
- `[AuthorYY]` - 作者姓氏缩写+年份后两位，如 `[Hoare69]`
- `[ABC+YY]` - 多位作者+年份，如 `[CGP99]`
- `[AuthorYYa]`, `[AuthorYYb]` - 同作者同年多篇论文
```

### 引用示例

在正文中使用引用标记：

```markdown
如 Hoare 在程序验证方面的工作[^1] 所示...

[^1]: C.A.R. Hoare. "An Axiomatic Basis for Computer Programming". CACM, 1969.
       [DOI:10.1145/363235.363259](https://doi.org/10.1145/363235.363259)
```

---

## 快速导航

### 按主题查找

| 主题 | 推荐文献文件 |
|------|--------------|
| 类型论与λ演算 | [01.2_形式语言文献.md](./01.2_形式语言文献.md) |
| 函数式编程 | [01.3_编程范式文献.md](./01.3_编程范式文献.md) |
| 并发与并行 | [01.3_编程范式文献.md](./01.3_编程范式文献.md) |
| 分布式系统 | [01.4_软件工程文献.md](./01.4_软件工程文献.md) |
| 实时调度 | [01.5_调度系统文献.md](./01.5_调度系统文献.md) |
| 形式化验证 | [01.2_形式语言文献.md](./01.2_形式语言文献.md) |

### 经典必读 (★)

- `[Turing36]` - 可计算性理论奠基
- `[Church40]` - 类型论起源
- `[Hoare69]` - Hoare逻辑
- `[Dijkstra76]` - 最弱前置条件
- `[Pierce02]` - 类型理论教材
- `[GoF94]` - 设计模式
- `[LL73]` - 实时调度基础
- `[Lamport02]` - TLA+规范

---

## 更新日志

| 日期 | 更新内容 |
|------|----------|
| 2026-04-12 | 添加外部资源链接：RFC标准、学术论文、工具链接、在线资源 |
| 2026-04-12 | 创建参考文献总索引 |
| 原始 | 初始参考文献整理 |

---

## 相关索引

- [符号表总览](../02_符号表/_index.md)
- [概念索引](../03_索引/03.1_概念索引.md)
- [定理索引](../03_索引/03.2_定理索引.md)
- [项目主索引](../../00_INDEX.md)
