# Linux内核调度系统深度分析

## 目录

- [Linux内核调度系统深度分析](#linux内核调度系统深度分析)
  - [目录](#目录)
  - [1. 概述](#1-概述)
    - [1.1 调度器演进历史](#11-调度器演进历史)
    - [1.2 调度器架构概览](#12-调度器架构概览)
  - [2. CFS完全公平调度器](#2-cfs完全公平调度器)
    - [2.1 CFS设计原理](#21-cfs设计原理)
    - [2.2 红黑树实现](#22-红黑树实现)
    - [2.3 vruntime计算](#23-vruntime计算)
    - [2.4 调度周期](#24-调度周期)
    - [2.5 负载均衡](#25-负载均衡)
    - [2.6 CFS核心源码分析](#26-cfs核心源码分析)
  - [3. 实时调度](#3-实时调度)
    - [3.1 实时调度策略](#31-实时调度策略)
    - [3.2 实时调度数据结构](#32-实时调度数据结构)
    - [3.3 实时调度源码分析](#33-实时调度源码分析)
    - [3.4 实时优先级实现](#34-实时优先级实现)
    - [3.5 可调度性验证](#35-可调度性验证)
  - [4. 调度器核心数据结构](#4-调度器核心数据结构)
    - [4.1 task\_struct结构](#41-task_struct结构)
    - [4.2 sched\_entity结构](#42-sched_entity结构)
    - [4.3 rq运行队列结构](#43-rq运行队列结构)
    - [4.4 调度类结构](#44-调度类结构)
  - [5. 调度流程](#5-调度流程)
    - [5.1 schedule()函数详解](#51-schedule函数详解)
    - [5.2 上下文切换](#52-上下文切换)
    - [5.3 唤醒路径](#53-唤醒路径)
  - [6. 现代Linux特性](#6-现代linux特性)
    - [6.1 eBPF调度扩展](#61-ebpf调度扩展)
    - [6.2 Core Scheduling](#62-core-scheduling)
    - [6.3 SCHED\_DEADLINE](#63-sched_deadline)
  - [7. 性能调优](#7-性能调优)
    - [7.1 内核参数调优](#71-内核参数调优)
    - [7.2 调度策略选择指南](#72-调度策略选择指南)
    - [7.3 监控工具](#73-监控工具)
    - [7.4 性能调优案例](#74-性能调优案例)
  - [8. 总结与展望](#8-总结与展望)
    - [8.1 关键技术总结](#81-关键技术总结)
    - [8.2 未来发展趋势](#82-未来发展趋势)
    - [8.3 参考资源](#83-参考资源)
  - [附录A: 数据流程图](#附录a-数据流程图)
    - [A.1 CFS调度完整流程](#a1-cfs调度完整流程)
    - [A.2 任务状态转换图](#a2-任务状态转换图)
    - [A.3 调度域层级结构](#a3-调度域层级结构)
  - [附录B: 完整源码索引](#附录b-完整源码索引)
    - [B.1 核心调度文件](#b1-核心调度文件)
    - [B.2 头文件](#b2-头文件)
    - [B.3 架构相关调度代码](#b3-架构相关调度代码)

---

## 1. 概述

### 1.1 调度器演进历史

Linux内核调度器经历了多次重大演进：

| 版本 | 调度器 | 特点 |
|------|--------|------|
| 2.4 | O(n)调度器 | 遍历所有任务，时间复杂度O(n) |
| 2.6 | O(1)调度器 | 优先级数组，时间复杂度O(1) |
| 2.6.23+ | CFS | 红黑树实现，完全公平调度 |
| 3.14+ | SCHED_DEADLINE | 最早截止时间优先调度 |
| 5.x+ | eBPF调度扩展 | 可编程调度器 |
| 6.x+ | Core Scheduling | 核心调度安全增强 |

### 1.2 调度器架构概览

```
┌─────────────────────────────────────────────────────────────────┐
│                     Linux Kernel Scheduler                       │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐           │
│  │   CFS        │  │   RT         │  │  DL          │           │
│  │  (SCHED_OTHER│  │(SCHED_FIFO/  │  │(SCHED_DEADLINE│           │
│  │  SCHED_BATCH │  │  SCHED_RR)   │  │              │           │
│  │  SCHED_IDLE) │  │              │  │              │           │
│  └──────┬───────┘  └──────┬───────┘  └──────┬───────┘           │
│         │                 │                 │                   │
│         └────────┬────────┴────────┬────────┘                   │
│                  │                 │                            │
│                  ▼                 ▼                            │
│         ┌────────────────────────────────┐                      │
│         │      通用调度层 (core.c)        │                      │
│         │  - schedule()                   │                      │
│         │  - 上下文切换                   │                      │
│         │  - 负载均衡                     │                      │
│         └────────────────────────────────┘                      │
│                             │                                   │
│                             ▼                                   │
│         ┌────────────────────────────────┐                      │
│         │      运行队列 (per-CPU rq)      │                      │
│         └────────────────────────────────┘                      │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## 2. CFS完全公平调度器

### 2.1 CFS设计原理

CFS（Completely Fair Scheduler）是Linux内核默认的调度器，其核心设计理念：

1. **公平性**：每个进程获得公平的CPU时间份额
2. **红黑树**：O(log n)时间复杂度的任务组织
3. **虚拟运行时间(vruntime)**：基于权重的公平度量
4. **最小化延迟**：优化交互式任务响应

### 2.2 红黑树实现

CFS使用红黑树（Red-Black Tree）组织可运行任务，以vruntime为键值：

```
                    ┌─────────────────────────────────────┐
                    │         CFS红黑树结构                │
                    └─────────────────────────────────────┘
                                     │
                    ┌────────────────┴────────────────┐
                    ▼                                 ▼
         ┌─────────────────────┐          ┌─────────────────────┐
         │  任务A (vruntime=10)│          │  任务B (vruntime=50)│
         │  (调度实体se)       │          │  (调度实体se)       │
         └──────────┬──────────┘          └──────────┬──────────┘
                    │                                │
          ┌─────────┴─────────┐              ┌──────┴──────┐
          ▼                   ▼              ▼             ▼
┌──────────────────┐ ┌──────────────────┐  ┌──────────┐  ┌──────────┐
│ 任务C (vruntime=5)│ │ 任务D (vruntime=15)│  │ 任务E    │  │ 任务F    │
│  (最左侧=下一个    │ │                  │  │          │  │          │
│   运行任务)       │ │                  │  │          │  │          │
└──────────────────┘ └──────────────────┘  └──────────┘  └──────────┘
```

### 2.3 vruntime计算

vruntime（虚拟运行时间）是CFS的核心概念，计算公式：

```
vruntime = 实际运行时间 × (nice=0的权重 / 当前进程权重)
         = delta_exec × (NICE_0_LOAD / se->load.weight)
```

**权重计算**：

```c
// kernel/sched/core.c
/*
 * Nice levels are multiplicative, with a gentle 10% change for every
 * nice level changed. I.e. when a CPU-bound nice +19 task competes
 * with nice 0 task, the +19 task gets ~10% of the CPU time.
 */
const int sched_prio_to_weight[40] = {
 /* -20 */     88761,     71755,     56483,     46273,     36291,
 /* -15 */     29154,     23254,     18705,     14949,     11916,
 /* -10 */      9548,      7620,      6100,      4904,      3906,
 /*  -5 */      3121,      2501,      1991,      1586,      1277,
 /*   0 */      1024,       820,       655,       526,       423,
 /*   5 */       335,       272,       215,       172,       137,
 /*  10 */       110,        87,        70,        56,        45,
 /*  15 */        36,        29,        23,        18,        15,
};
```

权重分配遵循指数衰减规律，每增加1个nice值，权重减少约10%。

### 2.4 调度周期

CFS调度周期相关源码分析：

```c
// kernel/sched/fair.c

/*
 * The idea is to set a period in which each task runs once.
 *
 * When there are too many tasks (sysctl_sched_nr_latency) we have to stretch
 * this period because otherwise the slices get too small.
 *
 * p = (nr <= nl) ? l : l*nr/nl
 */
static u64 __sched_period(unsigned long nr_running)
{
    if (unlikely(nr_running > sched_nr_latency))
        return nr_running * sysctl_sched_min_granularity;
    else
        return sysctl_sched_latency;
}
```

**关键参数**：

| 参数 | 默认值 | 说明 |
|------|--------|------|
| `sched_latency_ns` | 6ms | 目标调度延迟 |
| `sched_min_granularity_ns` | 0.75ms | 最小调度粒度 |
| `sched_nr_latency` | 8 | 保证延迟的任务数阈值 |
| `sched_wakeup_granularity_ns` | 1ms | 唤醒抢占粒度 |

**调度周期计算示例**：

```
场景1: 任务数 <= 8
周期 = sched_latency_ns = 6ms
每个任务时间片 = 6ms / 任务数

场景2: 任务数 > 8
周期 = 任务数 × sched_min_granularity_ns
每个任务时间片 = sched_min_granularity_ns = 0.75ms
```

### 2.5 负载均衡

CFS在多核系统上的负载均衡机制：

```
┌─────────────────────────────────────────────────────────────────┐
│                    CFS负载均衡架构                               │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  CPU0 rq                      CPU1 rq                      CPU2 rq│
│  ┌──────────────────┐        ┌──────────────────┐        ┌─────┐│
│  │ CFS: [A,B,C]     │◄──────►│ CFS: [D,E]       │◄──────►│CFS: ││
│  │ RT:  [X]         │  周期  │ RT:  [Y]         │  周期  │[F]  ││
│  │ DL:  []          │  检查  │ DL:  []          │  检查  │     ││
│  └──────────────────┘        └──────────────────┘        └─────┘│
│         │                           │                           │
│         └───────────────────────────┼───────────────────────────┘
│                                     │
│                              ┌──────┴──────┐
│                              │ 调度域层级  │
│                              │ (MC/SMT/Die)│
│                              └─────────────┘
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

**负载均衡源码分析**：

```c
// kernel/sched/fair.c

/*
 * load_balance - the load balancing main function
 * @cpu:        CPU to check for load balancing
 * @sd:         The scheduling domain to check
 * @flags:      Flags governing the behavior of load balance
 */
static int load_balance(int cpu, struct rq *rq, struct sched_domain *sd,
                        enum cpu_idle_type idle, int *continue_balancing)
{
    int ld_moved = 0;
    struct lb_env env = {
        .sd             = sd,
        .dst_cpu        = cpu,
        .dst_rq         = rq,
        .dst_grpmask    = sched_group_cpus(sd->groups),
        .idle           = idle,
        .loop           = 0,
        .loop_break     = sched_nr_migrate_break,
        .cpus           = kzalloc(cpumask_size(), GFP_ATOMIC),
        .fbq_type       = all,
        .flags          = 0,
        .loop_max       = sysctl_sched_nr_migrate,
    };

    /*
     * Find the busiest group and the busiest CPU within that group.
     * If the busiest CPU is this CPU, try to find the next busiest
     * group.
     */
    schedstat_add(sd->lb_count[idle]);

    // 查找最忙的调度组
    group = find_busiest_group(&env, &balance);
    if (!group) {
        schedstat_inc(sd->lb_nobusyg[idle]);
        goto out_balanced;
    }

    // 查找最忙的CPU
    busiest = find_busiest_queue(&env, group);
    if (!busiest) {
        schedstat_inc(sd->lb_nobusyq[idle]);
        goto out_balanced;
    }

    // 迁移任务
    env.src_cpu = busiest->cpu;
    env.src_rq = busiest;
    env.loop_max = min(sysctl_sched_nr_migrate, busiest->cfs.h_nr_running);

    ld_moved = detach_tasks(&env);

    if (env.detached) {
        // 将任务附加到目标运行队列
        attach_tasks(&env);
    }

    return ld_moved;
}
```

### 2.6 CFS核心源码分析

**task_tick_fair - 时钟滴答处理**：

```c
// kernel/sched/fair.c

/*
 * scheduler tick hitting a task of our scheduling class:
 */
static void task_tick_fair(struct rq *rq, struct task_struct *curr, int queued)
{
    struct cfs_rq *cfs_rq;
    struct sched_entity *se = &curr->se;

    // 更新实体统计信息
    for_each_sched_entity(se) {
        cfs_rq = cfs_rq_of(se);
        entity_tick(cfs_rq, se, queued);
    }

    // 检查是否需要重新调度
    if (static_branch_unlikely(&sched_numa_balancing))
        task_tick_numa(rq, curr);
}

static void entity_tick(struct cfs_rq *cfs_rq, struct sched_entity *curr, int queued)
{
    /*
     * Update run-time statistics of the 'current'.
     */
    update_curr(cfs_rq);

    /*
     * Ensure that runnable average is periodically updated.
     */
    update_load_avg(cfs_rq, curr, UPDATE_TG);
    update_cfs_group(curr);

    /*
     * Reschedule if the current task has run for longer than the
     * ideal time slice.
     */
    if (cfs_rq->nr_running > 1)
        check_preempt_tick(cfs_rq, curr);
}
```

**check_preempt_tick - 检查抢占**：

```c
// kernel/sched/fair.c

/*
 * Preempt the current task with a newly woken task if needed:
 */
static void check_preempt_tick(struct cfs_rq *cfs_rq, struct sched_entity *curr)
{
    unsigned long ideal_runtime, delta_exec;
    struct sched_entity *se;
    s64 delta;

    // 计算理想运行时间
    ideal_runtime = sched_slice(cfs_rq, curr);
    delta_exec = curr->sum_exec_runtime - curr->prev_sum_exec_runtime;

    // 如果当前任务运行时间超过理想时间，标记需要重新调度
    if (delta_exec > ideal_runtime) {
        resched_curr(rq_of(cfs_rq));
        /*
         * The current task ran long enough, ensure it doesn't get
         * re-elected due to buddy favours.
         */
        clear_buddies(cfs_rq, curr);
        return;
    }

    /*
     * Ensure that a task that missed wakeup preemption by a
     * narrow margin doesn't have to wait for a full slice.
     * This also mitigates buddy induced latencies under load.
     */
    if (delta_exec < sysctl_sched_min_granularity)
        return;

    // 检查是否有任务的vruntime更小（应该优先运行）
    se = __pick_first_entity(cfs_rq);
    delta = curr->vruntime - se->vruntime;

    if (delta < 0)
        return;

    // 如果当前任务的vruntime比最左任务大一定阈值，抢占
    if (delta > ideal_runtime)
        resched_curr(rq_of(cfs_rq));
}
```

**update_curr - 更新当前任务统计**：

```c
// kernel/sched/fair.c

static void update_curr(struct cfs_rq *cfs_rq)
{
    struct sched_entity *curr = cfs_rq->curr;
    u64 now = rq_clock_task(rq_of(cfs_rq));
    u64 delta_exec;

    if (unlikely(!curr))
        return;

    // 计算本次执行的时间差
    delta_exec = now - curr->exec_start;
    if (unlikely((s64)delta_exec <= 0))
        return;

    curr->exec_start = now;

    // 累加总执行时间
    curr->sum_exec_runtime += delta_exec;

    // 更新vruntime
    curr->vruntime += calc_delta_fair(delta_exec, curr);
    update_min_vruntime(cfs_rq);

    // 更新负载统计
    if (entity_is_task(curr)) {
        struct task_struct *curtask = task_of(curr);

        trace_sched_stat_runtime(curtask, delta_exec, curr->vruntime);
        cpuacct_charge(curtask, delta_exec);
        account_group_exec_runtime(curtask, delta_exec);
    }

    account_cfs_rq_runtime(cfs_rq, delta_exec);
}
```

---

## 3. 实时调度

### 3.1 实时调度策略

Linux内核支持两种实时调度策略：

```
┌─────────────────────────────────────────────────────────────────┐
│                    实时调度策略对比                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌──────────────────────────┐    ┌──────────────────────────┐   │
│  │      SCHED_FIFO          │    │       SCHED_RR           │   │
│  ├──────────────────────────┤    ├──────────────────────────┤   │
│  │ 特点:                    │    │ 特点:                    │   │
│  │ - 先到先服务              │    │ - 时间片轮转              │   │
│  │ - 无时间片               │    │ - 有时间片(默认100ms)     │   │
│  │ - 一直运行直到:          │    │ - 时间片用完排到队尾      │   │
│  │   · 主动放弃CPU          │    │ - 同优先级轮转            │   │
│  │   · 被高优先级抢占       │    │                          │   │
│  │   · 退出/阻塞            │    │                          │   │
│  └──────────────────────────┘    └──────────────────────────┘   │
│                                                                  │
│  优先级范围: 1-99 (RT优先级，数值越大优先级越高)                  │
│  对比: CFS优先级范围 100-139 (nice -20 到 19)                   │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### 3.2 实时调度数据结构

```c
// kernel/sched/rt.c

/*
 * Real-Time classes' related field in a runqueue:
 */
struct rt_rq {
    struct rt_prio_array active;    // 活跃的任务数组
    unsigned int rt_nr_running;     // 运行的RT任务数
    unsigned int rr_nr_running;
#if defined CONFIG_SMP || defined CONFIG_RT_GROUP_SCHED
    struct {
        int curr; /* highest queued rt task prio */
    } highest_prio;
#endif
#ifdef CONFIG_SMP
    unsigned long rt_nr_migratory;
    int overloaded;
    struct plist_head pushable_tasks;
#endif
    int rt_queued;

    int rt_throttled;
    u64 rt_time;
    u64 rt_runtime;
    /* Nests inside the rq lock: */
    raw_spinlock_t rt_runtime_lock;

#ifdef CONFIG_RT_GROUP_SCHED
    unsigned long rt_nr_boosted;

    struct rq *rq;
    struct task_group *tg;
#endif
};

/*
 * This is the priority-queue data structure of the RT scheduling class:
 */
struct rt_prio_array {
    DECLARE_BITMAP(bitmap, MAX_RT_PRIO+1); /* include 1 bit for delimiter */
    struct list_head queue[MAX_RT_PRIO];
};
```

### 3.3 实时调度源码分析

**pick_next_task_rt - 选择下一个RT任务**：

```c
// kernel/sched/rt.c

static struct task_struct *pick_next_task_rt(struct rq *rq)
{
    struct task_struct *p, *prev;
    struct sched_rt_entity *rt_se;
    struct rt_rq *rt_rq;

    rt_rq = &rq->rt;

    // 如果没有RT任务运行，返回NULL
    if (!rt_rq->rt_nr_running)
        return NULL;

    // 检查RT调度是否被限制
    if (rt_rq_throttled(rt_rq))
        return NULL;

    // 选择最高优先级的RT任务
    rt_se = pick_next_rt_entity(rq, rt_rq);
    BUG_ON(!rt_se);

    p = rt_task_of(rt_se);
    prev = rq->curr;

    // 设置当前运行的任务
    set_next_task_rt(rq, p, true);

    return p;
}

static struct sched_rt_entity *pick_next_rt_entity(struct rq *rq,
                                                   struct rt_rq *rt_rq)
{
    struct rt_prio_array *array = &rt_rq->active;
    struct sched_rt_entity *next = NULL;
    struct list_head *queue;
    int idx;

    // 找到最高优先级的位图索引
    idx = sched_find_first_bit(array->bitmap);
    BUG_ON(idx >= MAX_RT_PRIO);

    // 获取对应优先级的队列
    queue = array->queue + idx;
    next = list_entry(queue->next, struct sched_rt_entity, run_list);

    return next;
}
```

**enqueue_task_rt - 将RT任务加入运行队列**：

```c
// kernel/sched/rt.c

static void enqueue_task_rt(struct rq *rq, struct task_struct *p, int flags)
{
    struct sched_rt_entity *rt_se = &p->rt;

    // 如果任务正在迁移，推迟入队
    if (p->on_rq)
        return;

    // 重新计算时间片（对于SCHED_RR）
    if (p->policy == SCHED_RR)
        p->rt.time_slice = RR_TIMESLICE;

    // 将调度实体加入RT运行队列
    enqueue_rt_entity(rt_se, flags);

    // 检查是否需要抢占当前任务
    if (!task_current(rq, p) && p->nr_cpus_allowed > 1)
        enqueue_pushable_task(rq, p);
}

static void enqueue_rt_entity(struct sched_rt_entity *rt_se, unsigned int flags)
{
    struct rq *rq = rq_of_rt_se(rt_se);
    struct rt_rq *rt_rq;

    // 如果已经在队列中，无需处理
    if (on_rt_rq(rt_se))
        return;

    // 对于组调度，需要找到对应的rt_rq
    if (rt_se->rt_rq)
        rt_rq = rt_se->rt_rq;
    else
        rt_rq = &rq->rt;

    // 加入优先级队列
    __enqueue_rt_entity(rt_se, flags);

    // 更新负载统计
    inc_rt_tasks(rt_se, rt_rq);
}

/*
 * Adding/removing a task to/from a priority array:
 */
static void __enqueue_rt_entity(struct sched_rt_entity *rt_se, unsigned int flags)
{
    struct rt_rq *rt_rq = rt_rq_of_se(rt_se);
    struct rt_prio_array *array = &rt_rq->active;
    struct list_head *queue = array->queue + rt_se_prio(rt_se);

    /*
     * Don't enqueue the group if its throttled, or when empty.
     * The latter is necessary because an entity's run_list left
     * on the list from a previous activation needs to be cleaned up.
     */
    if (group_rt_rq(rt_se) && (rt_rq_throttled(group_rt_rq(rt_se)) || !rt_se->my_q))
        return;

    if (flags & ENQUEUE_HEAD)
        list_add(&rt_se->run_list, queue);
    else
        list_add_tail(&rt_se->run_list, queue);

    __set_bit(rt_se_prio(rt_se), array->bitmap);

    inc_rt_migration(rt_se, rt_rq);
    inc_rt_group(rt_se, rt_rq);
}
```

### 3.4 实时优先级实现

```c
// include/linux/sched/prio.h

/*
 * Priority of a process goes from 0..MAX_PRIO-1, valid RT
 * priority is 0..MAX_RT_PRIO-1, and SCHED_NORMAL/SCHED_BATCH
 * tasks go from MAX_RT_PRIO..MAX_PRIO-1. Priority values
 * are inverted: lower p->prio value means higher priority.
 *
 * The MAX_USER_RT_PRIO value allows the actual maximum
 * RT priority to be separate from the value exported to
 * user-space.  This allows kernel threads to set their
 * priority to a value higher than any user task.
 */
#define MAX_USER_RT_PRIO    100
#define MAX_RT_PRIO         MAX_USER_RT_PRIO

#define MAX_PRIO            (MAX_RT_PRIO + 40)
#define DEFAULT_PRIO        (MAX_RT_PRIO + 20)

/*
 * Convert user-nice values [ -20 ... 0 ... 19 ]
 * to static priority [ MAX_RT_PRIO..MAX_PRIO-1 ],
 * and back.
 */
#define NICE_TO_PRIO(nice)  ((nice) + DEFAULT_PRIO)
#define PRIO_TO_NICE(prio)  ((prio) - DEFAULT_PRIO)

/*
 * 'User priority' is the nice value converted to something we
 * can work with better when scaling various scheduler parameters,
 * it's a [ 0 ... 39 ] range.
 */
#define USER_PRIO(p)        ((p)-MAX_RT_PRIO)
#define TASK_USER_PRIO(p)   USER_PRIO((p)->static_prio)
#define MAX_USER_PRIO       (USER_PRIO(MAX_PRIO))
```

### 3.5 可调度性验证

对于实时系统，需要进行可调度性分析：

**速率单调调度（Rate-Monotonic）**：

```
对于n个周期性任务，如果满足以下条件则可调度：

Σ(Ci/Ti) ≤ n(2^(1/n) - 1)

其中：
- Ci: 任务i的最坏执行时间
- Ti: 任务i的周期

当n→∞时，右侧趋近于ln(2) ≈ 0.693
```

**最早截止时间优先（EDF）**：

```
对于EDF调度，可调度条件为：

Σ(Ci/Ti) ≤ 1

这是最优的调度算法，但实现复杂度较高。
```

---

## 4. 调度器核心数据结构

### 4.1 task_struct结构

```c
// include/linux/sched.h

struct task_struct {
    /*
     * State flags:
     * - TASK_RUNNING: 可运行或正在运行
     * - TASK_INTERRUPTIBLE: 可中断睡眠
     * - TASK_UNINTERRUPTIBLE: 不可中断睡眠
     * - __TASK_STOPPED: 停止
     * - __TASK_TRACED: 被跟踪
     */
    volatile long state;

    /*
     * Scheduling class and priority:
     */
    int prio, static_prio, normal_prio;
    unsigned int rt_priority;

    /*
     * Scheduling class determines the scheduler (CFS, RT, DL, etc.)
     */
    const struct sched_class *sched_class;
    struct sched_entity se;          // CFS调度实体
    struct sched_rt_entity rt;       // RT调度实体
    struct sched_dl_entity dl;       // 截止时间调度实体

    /*
     * CPU information:
     */
    int on_cpu;
    struct cpu_stop_work *stop_work;

    /*
     * Runqueue handling:
     */
    struct sched_info sched_info;

    /*
     * Affinity and migration:
     */
    cpumask_t cpus_mask;
    cpumask_t cpus_ptr;
    cpumask_t nr_cpus_allowed;

    /*
     * Current CPU:
     */
    int cpu;
    unsigned int wake_cpu;

    /*
     * Policy and nice:
     */
    int policy;
    int nr_cpus_allowed;

    /* ... 其他字段 ... */
};
```

**task_struct调度相关字段详解**：

```
┌─────────────────────────────────────────────────────────────────┐
│              task_struct 调度相关字段                            │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  优先级字段:                                                      │
│  ┌────────────────────────────────────────────────────────┐    │
│  │ static_prio  ──► 静态优先级 (nice值转换而来)            │    │
│  │ normal_prio  ──► 普通优先级 (根据调度策略计算)          │    │
│  │ prio         ──► 动态优先级 (最终使用的优先级)          │    │
│  │ rt_priority  ──► 实时优先级 (1-99)                      │    │
│  └────────────────────────────────────────────────────────┘    │
│                                                                  │
│  调度实体:                                                        │
│  ┌────────────────────────────────────────────────────────┐    │
│  │ struct sched_entity se  ──► CFS调度实体                 │    │
│  │ struct sched_rt_entity rt ──► RT调度实体                │    │
│  │ struct sched_dl_entity dl ──► 截止时间调度实体          │    │
│  └────────────────────────────────────────────────────────┘    │
│                                                                  │
│  调度策略:                                                        │
│  ┌────────────────────────────────────────────────────────┐    │
│  │ int policy ──► 调度策略                                │    │
│  │   - SCHED_OTHER (0)  = CFS                             │    │
│  │   - SCHED_FIFO (1)   = 实时FIFO                        │    │
│  │   - SCHED_RR (2)     = 实时RR                          │    │
│  │   - SCHED_BATCH (3)  = 批处理                          │    │
│  │   - SCHED_IDLE (5)   = 空闲                            │    │
│  │   - SCHED_DEADLINE (6) = 截止时间                      │    │
│  └────────────────────────────────────────────────────────┘    │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### 4.2 sched_entity结构

```c
// include/linux/sched.h

struct sched_entity {
    /*
     * Load tracking:
     */
    struct load_weight load;         // 权重
    unsigned long runnable_weight;   // 可运行权重

    /*
     * Runqueue handling:
     */
    struct rb_node run_node;         // 红黑树节点
    struct list_head group_node;     // 组调度节点
    unsigned int on_rq;              // 是否在运行队列上

    /*
     * Statistics:
     */
    u64 exec_start;                  // 本次开始执行时间
    u64 sum_exec_runtime;            // 总执行时间
    u64 vruntime;                    // 虚拟运行时间
    u64 prev_sum_exec_runtime;       // 上次总执行时间

    u64 nr_migrations;               // 迁移次数

    /*
     * Statistics for CONFIG_SCHEDSTATS:
     */
#ifdef CONFIG_SCHEDSTATS
    struct sched_statistics statistics;
#endif

#ifdef CONFIG_FAIR_GROUP_SCHED
    /*
     * Depth of the schedule entity hierarchy:
     */
    int depth;

    /*
     * Group scheduling hierarchy:
     */
    struct sched_entity *parent;     // 父实体
    struct cfs_rq *cfs_rq;           // 所属CFS运行队列
    struct cfs_rq *my_q;             // 子CFS运行队列（组调度）
#endif

#ifdef CONFIG_SMP
    /*
     * Per-entity load-tracking:
     */
    struct sched_avg avg;            // 平均负载
#endif
};

/*
 * Load weight for a task:
 */
struct load_weight {
    unsigned long weight;            // 权重值
    u32 inv_weight;                  // 权重倒数（用于除法优化）
};
```

### 4.3 rq运行队列结构

```c
// kernel/sched/sched.h

/*
 * This is the main, per-CPU runqueue data structure.
 */
struct rq {
    /*
     * nr_running and cpu_load should be in the same cacheline because
     * remote CPUs use both these fields when doing load calculation.
     */
    unsigned int nr_running;
    #define CPU_LOAD_IDX_MAX 5
    unsigned long cpu_load[CPU_LOAD_IDX_MAX];

    /*
     * This is part of a global counter where only the total sum
     * over all CPUs matters. A task can increase or decrease this
     * counter on one CPU and if it got migrated afterwards it may
     * get accounted on another CPU.
     */
    unsigned long nr_load_updates;

    u64 nr_switches;
    u64 nr_migrations_in;

    /*
     * The following fields are kept on a per-CPU basis:
     */
    struct cfs_rq cfs;               // CFS运行队列
    struct rt_rq rt;                 // RT运行队列
    struct dl_rq dl;                 // DL运行队列

    /*
     * curr and idle are always set, but can be the same if the
     * CPU is idle.
     */
    struct task_struct *curr;        // 当前运行任务
    struct task_struct *idle;        // 空闲任务
    struct task_struct *stop;        // 迁移/停止任务

    /*
     * On SMP we have a sequence lock for the last task migration
     * information:
     */
    u64 nr_last_overflow;
    u64 clock;
    u64 clock_task;

    atomic_t nr_iowait;

#ifdef CONFIG_SMP
    struct root_domain *rd;
    struct sched_domain *sd;

    unsigned long cpu_capacity;
    unsigned long cpu_capacity_orig;

    struct callback_head *balance_callback;

    unsigned char idle_balance;
    unsigned char nohz_idle_balance;

    /* For active balancing */
    int active_balance;
    int push_cpu;
    struct cpu_stop_work active_balance_work;
#endif

#ifdef CONFIG_IRQ_TIME_ACCOUNTING
    u64 prev_irq_time;
#endif

    /* Per-CPU latency stats: */
    struct sched_avg avg_rt;
    struct sched_avg avg_dl;

    /* Cacheline boundary here... */

    /* Time-based average load: */
    u64 clock_pelt;
    unsigned long lost_idle_time;

    /* cpufreq scaling */
    struct update_util_data *update_util_data;
};
```

**运行队列结构示意图**：

```
┌─────────────────────────────────────────────────────────────────┐
│                     Per-CPU Run Queue (rq)                       │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  基本统计:                                                        │
│  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐                │
│  │ nr_running  │ │ nr_switches │ │ nr_iowait   │                │
│  │ (运行任务数) │ │ (上下文切换) │ │ (IO等待)    │                │
│  └─────────────┘ └─────────────┘ └─────────────┘                │
│                                                                  │
│  调度类运行队列:                                                   │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │ struct cfs_rq cfs                                       │    │
│  │  ├─ tasks_timeline (红黑树根节点)                        │    │
│  │  ├─ nr_running (CFS任务数)                              │    │
│  │  ├─ min_vruntime (最小vruntime基准)                     │    │
│  │  └─ load (总负载)                                       │    │
│  ├─────────────────────────────────────────────────────────┤    │
│  │ struct rt_rq rt                                         │    │
│  │  ├─ active (优先级数组)                                 │    │
│  │  ├─ rt_nr_running (RT任务数)                            │    │
│  │  └─ highest_prio (最高优先级)                           │    │
│  ├─────────────────────────────────────────────────────────┤    │
│  │ struct dl_rq dl                                         │    │
│  │  ├─ root (红黑树根节点)                                 │    │
│  │  ├─ dl_nr_running (DL任务数)                            │    │
│  │  └─ earliest_dl (最早截止时间)                          │    │
│  └─────────────────────────────────────────────────────────┘    │
│                                                                  │
│  当前任务指针:                                                    │
│  ┌─────────────────────────────────────────────────────────┐    │
│  │ struct task_struct *curr  ──► 当前正在运行的任务         │    │
│  │ struct task_struct *idle  ──► 空闲任务                   │    │
│  │ struct task_struct *stop  ──► 停止任务(用于迁移)         │    │
│  └─────────────────────────────────────────────────────────┘    │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### 4.4 调度类结构

```c
// include/linux/sched.h

/*
 * Scheduling classes:
 */
const struct sched_class fair_sched_class;
const struct sched_class rt_sched_class;
const struct sched_class dl_sched_class;
const struct sched_class idle_sched_class;

struct sched_class {
    const struct sched_class *next;

    void (*enqueue_task) (struct rq *rq, struct task_struct *p, int flags);
    void (*dequeue_task) (struct rq *rq, struct task_struct *p, int flags);
    void (*yield_task)   (struct rq *rq);
    bool (*yield_to_task)(struct rq *rq, struct task_struct *p);

    void (*check_preempt_curr)(struct rq *rq, struct task_struct *p, int flags);

    struct task_struct * (*pick_next_task)(struct rq *rq);

    void (*put_prev_task)(struct rq *rq, struct task_struct *p);
    void (*set_next_task)(struct rq *rq, struct task_struct *p, bool first);

#ifdef CONFIG_SMP
    int (*balance)(struct rq *rq, struct task_struct *prev, struct rq_flags *rf);
    int  (*select_task_rq)(struct task_struct *p, int task_cpu, int sd_flag, int flags);
    void (*migrate_task_rq)(struct task_struct *p, int new_cpu);

    void (*task_woken)(struct rq *this_rq, struct task_struct *task);

    void (*set_cpus_allowed)(struct task_struct *p, const struct cpumask *newmask);

    void (*rq_online)(struct rq *rq);
    void (*rq_offline)(struct rq *rq);
#endif

    void (*task_tick)(struct rq *rq, struct task_struct *p, int queued);
    void (*task_fork)(struct task_struct *p);
    void (*task_dead)(struct task_struct *p);

    /*
     * The switched_from() call is the last thing a task is allowed
     * to do before it is removed from the runqueue.
     */
    void (*switched_from)(struct rq *this_rq, struct task_struct *task);
    void (*switched_to)  (struct rq *this_rq, struct task_struct *task);
    void (*prio_changed) (struct rq *this_rq, struct task_struct *task, int oldprio);

    unsigned int (*get_rr_interval)(struct rq *rq, struct task_struct *task);

    void (*update_curr)(struct rq *rq);

#define TASK_SET_GROUP      0
#define TASK_MOVE_GROUP     1

#ifdef CONFIG_FAIR_GROUP_SCHED
    void (*task_change_group)(struct task_struct *p, int type);
#endif
};
```

**调度类优先级顺序**：

```
stop_sched_class    ──► 最高优先级 (停止任务)
    ↓
dl_sched_class      ──► 截止时间调度
    ↓
rt_sched_class      ──► 实时调度
    ↓
fair_sched_class    ──► CFS公平调度
    ↓
idle_sched_class    ──► 最低优先级 (空闲调度)
```

---

## 5. 调度流程

### 5.1 schedule()函数详解

```c
// kernel/sched/core.c

/*
 * __schedule() is the main scheduler function.
 *
 * The main means of driving the scheduler and thus entering this function are:
 *
 *   1. Explicit blocking: mutex, semaphore, waitqueue, etc.
 *
 *   2. TIF_NEED_RESCHED flag is checked on interrupt and userspace return
 *      paths. For example, see arch/x86/entry_64.S.
 *
 *      To drive preemption between tasks, the scheduler sets the flag in timer
 *      handler handler_tick().
 *
 *   3. Wakeups don't really cause entry into schedule(). They add a
 *      task to the run-queue and that's it.
 *
 *      Now, if the new task added to the run-queue preempts the current
 *      task, then the wakeup sets TIF_NEED_RESCHED and schedule() gets
 *      called on the nearest possible occasion:
 *
 *       - If the kernel is preemptible (CONFIG_PREEMPTION=y):
 *
 *         - in syscall or exception context, at the next outmost
 *           preempt_enable(). (in this case, to guarantee progress, the
 *           preempt_enable has a barrier() pair which forces an
 *           instruction stream barrier.)
 *
 *         - in IRQ context, return from interrupt-handler to
 *           preemptible context
 *
 *       - If the kernel is not preemptible (CONFIG_PREEMPTION is not set)
 *         then at the next:
 *
 *          - cond_resched() call
 *          - explicit schedule() call
 *          - return from syscall or exception to user-space
 *          - return from interrupt-handler to user-space
 */
static void __sched notrace __schedule(bool scheduling)
{
    struct task_struct *prev, *next;
    unsigned long *switch_count;
    unsigned long prev_state;
    struct rq_flags rf;
    struct rq *rq;
    int cpu;

    cpu = smp_processor_id();
    rq = cpu_rq(cpu);
    prev = rq->curr;

    /*
     * do_exit() calls schedule() with TASK_DEAD set, the task has
     * already accounted for the impending cycle and should just
     * schedule away.
     */
    if (unlikely(prev->state == TASK_DEAD))
        goto out_dead;

    // 获取rq锁
    rq_lock(rq, &rf);
    smp_mb__before_spinlock();

    // 更新rq时钟
    rq->clock_skip_update <<= 1; /* propagate SKIP to clearly */

    // 保存前一个任务的状态
    prev_state = prev->state;
    if (!sched_mode_masked(sc, SM_MASK_PREEMPT) && prev_state) {
        // 如果是非抢占式调度且任务状态不为0，需要处理睡眠
        if (signal_pending_state(prev_state, prev)) {
            prev->state = TASK_RUNNING;
        } else {
            // 将任务从运行队列移除
            deactivate_task(rq, prev, DEQUEUE_SLEEP | DEQUEUE_NOCLOCK);
            prev->on_rq = 0;

            if (prev->in_iowait) {
                atomic_inc(&rq->nr_iowait);
                delayacct_blkio_end(prev);
            }
        }
    }

    // 选择下一个要运行的任务
    next = pick_next_task(rq, prev, &rf);
    clear_tsk_need_resched(prev);
    clear_preempt_need_resched();

    // 如果选择的任务与当前任务不同，需要进行上下文切换
    if (likely(prev != next)) {
        rq->nr_switches++;
        RCU_INIT_POINTER(rq->curr, next);

        ++*switch_count;

        // 执行上下文切换
        rq = context_switch(rq, prev, next, &rf);
    } else {
        rq->clock_skip_update &= ~SKIP_IS_TICK;
        rq_unlock_irq(rq, &rf);
    }

    balance_callback(rq);
    return;

out_dead:
    // 处理已结束任务
    rq_unlock_irq(rq, &rf);
}

/*
 * Pick up the highest-prio task:
 */
static inline struct task_struct *pick_next_task(struct rq *rq,
                         struct task_struct *prev, struct rq_flags *rf)
{
    const struct sched_class *class;
    struct task_struct *p;

    /*
     * Optimization: we know that if all tasks are in the fair class we can
     * call that function directly:
     */
    if (likely(prev->sched_class == &fair_sched_class &&
           rq->nr_running == rq->cfs.h_nr_running)) {
        p = fair_sched_class.pick_next_task(rq);
        if (likely(p))
            return p;
    }

    // 按照调度类优先级顺序选择任务
    for_each_class(class) {
        p = class->pick_next_task(rq);
        if (p)
            return p;
    }

    BUG(); /* the idle class will always have a runnable task */
}
```

### 5.2 上下文切换

```c
// kernel/sched/core.c

/*
 * context_switch - switch to the new MM and the new thread's register state.
 */
static __always_inline struct rq *context_switch(struct rq *rq,
        struct task_struct *prev, struct task_struct *next,
        struct rq_flags *rf)
{
    struct mm_struct *mm, *oldmm;

    // 准备进行上下文切换
    prepare_task_switch(rq, prev, next);

    mm = next->mm;
    oldmm = prev->active_mm;

    /*
     * For paravirt, this is coupled with an exit in switch_to to
     * combine the page table reload and the switch backend into
     * one hypercall.
     */
    arch_start_context_switch(prev);

    /*
     * If it's a kernel thread (no mm), borrow the previous task's mm.
     */
    if (!mm) {
        next->active_mm = oldmm;
        mmgrab(oldmm);
        enter_lazy_tlb(oldmm, next);
    } else {
        // 切换到新的地址空间
        switch_mm_irqs_off(oldmm, mm, next);

        // 如果之前的任务是内核线程，释放mm引用
        if (!prev->mm) {
            prev->active_mm = NULL;
            rq->prev_mm = oldmm;
        }
    }

    // 切换CPU状态
    /* Here we just switch the register state and the stack. */
    switch_to(prev, next, prev);

    // 上下文切换完成后的处理
    barrier();
    return finish_task_switch(prev);
}
```

**上下文切换流程图**：

```
┌─────────────────────────────────────────────────────────────────┐
│                    上下文切换流程                                │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │ 1. prepare_task_switch()                                 │  │
│  │    - 调用sched_out钩子                                   │  │
│  │    - 更新统计信息                                        │  │
│  └──────────────────────────────────────────────────────────┘  │
│                              │                                   │
│                              ▼                                   │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │ 2. 地址空间切换                                           │  │
│  │    - switch_mm_irqs_off()                                │  │
│  │    - 切换页表                                            │  │
│  │    - 更新TLB                                             │  │
│  │    - 如果新任务是内核线程，借用旧mm                      │  │
│  └──────────────────────────────────────────────────────────┘  │
│                              │                                   │
│                              ▼                                   │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │ 3. switch_to() - 寄存器状态切换                           │  │
│  │    - 保存旧任务寄存器 (PC, SP, 通用寄存器)               │  │
│  │    - 恢复新任务寄存器                                    │  │
│  │    - 切换内核栈                                          │  │
│  │    - 切换TLS (Thread Local Storage)                      │  │
│  └──────────────────────────────────────────────────────────┘  │
│                              │                                   │
│                              ▼                                   │
│  ┌──────────────────────────────────────────────────────────┐  │
│  │ 4. finish_task_switch()                                  │  │
│  │    - 调用sched_in钩子                                    │  │
│  │    - 清理旧任务的mm (如果是内核线程)                     │  │
│  │    - 解锁rq                                              │  │
│  └──────────────────────────────────────────────────────────┘  │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### 5.3 唤醒路径

```c
// kernel/sched/core.c

/*
 * wake_up_new_task - wake up a newly created task for the first time.
 *
 * This function will do some initial scheduler statistics housekeeping
 * that must be done for every newly created context, then puts the task
 * on the runqueue and wakes it.
 */
void wake_up_new_task(struct task_struct *p)
{
    struct rq_flags rf;
    struct rq *rq;

    raw_spin_lock_irqsave(&p->pi_lock, rf.flags);

    // 初始化调度信息
    init_entity_runnable_average(&p->se);

    // 选择最佳运行CPU
    p->recent_used_cpu = task_cpu(p);
    __set_task_cpu(p, select_task_rq(p, task_cpu(p), SD_BALANCE_FORK, 0));

    rq = __task_rq_lock(p, &rf);

    // 记录唤醒信息
    post_init_entity_util_avg(&p->se);

    // 激活任务
    activate_task(rq, p, ENQUEUE_NOCLOCK);

    // 追踪唤醒
    trace_sched_wakeup_new(p);

    // 检查是否需要抢占当前任务
    check_preempt_curr(rq, p, WF_FORK);

    // 唤醒后的处理
    task_rq_unlock(rq, p, &rf);
}

/*
 * wake_up_process - Wake up a specific process
 * @p: The process to be woken up.
 *
 * Attempt to wake up the nominated process and move it to the set of runnable
 * processes.
 *
 * Return: 1 if the process was woken up, 0 if it was already running.
 */
int wake_up_process(struct task_struct *p)
{
    return try_to_wake_up(p, TASK_NORMAL, 0);
}

static int try_to_wake_up(struct task_struct *p, unsigned int state, int wake_flags)
{
    struct rq_flags rf;
    struct rq *rq;
    int cpu, success = 0;

    // 设置需要重新调度标志
    smp_mb__before_spinlock();
    raw_spin_lock_irqsave(&p->pi_lock, rf.flags);

    // 检查状态
    if (!(p->state & state))
        goto out;

    // 如果任务已经在运行队列上
    if (p->on_rq) {
        // 标记为正在运行
        if (sched_mode(SM_PREEMPT))
            ttwu_do_wakeup(rq, p, wake_flags, &rf);
        else
            ttwu_do_activate(rq, p, wake_flags, &rf);
        success = 1;
        goto out;
    }

    // 获取上一次运行的CPU
    cpu = task_cpu(p);

    // 选择最佳CPU
    if (p->in_iowait) {
        delayacct_blkio_start();
        atomic_inc(&rq->nr_iowait);
    }

    // 如果不在当前CPU且可以迁移
    if (cpu != smp_processor_id()) {
        wake_flags |= WF_MIGRATED;
        cpu = select_task_rq(p, cpu, SD_BALANCE_WAKE, wake_flags);
    }

    // 获取新CPU的运行队列
    if (cpu != task_cpu(p))
        set_task_cpu(p, cpu);

    rq = cpu_rq(cpu);
    raw_spin_lock(&rq->lock);

    // 唤醒任务
    ttwu_do_activate(rq, p, wake_flags, &rf);

    success = 1;
out:
    raw_spin_unlock_irqrestore(&p->pi_lock, rf.flags);

    return success;
}
```

**唤醒路径流程图**：

```
┌─────────────────────────────────────────────────────────────────┐
│                    任务唤醒流程                                  │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  触发点:                                                          │
│  ┌────────────────────────────────────────────────────────────┐│
│  │ • wake_up_process()      - 通用唤醒接口                    ││
│  │ • wake_up_new_task()     - 新任务唤醒                      ││
│  │ • try_to_wake_up_local() - 本地唤醒                        ││
│  └────────────────────────────────────────────────────────────┘│
│                              │                                   │
│                              ▼                                   │
│  ┌────────────────────────────────────────────────────────────┐│
│  │ try_to_wake_up()                                          ││
│  │  ├─ 1. 获取pi_lock                                        ││
│  │  ├─ 2. 检查任务状态                                       ││
│  │  ├─ 3. 如果已在rq，调用ttwu_do_wakeup()                   ││
│  │  └─ 4. 否则调用ttwu_do_activate()                         ││
│  └────────────────────────────────────────────────────────────┘│
│                              │                                   │
│                              ▼                                   │
│  ┌────────────────────────────────────────────────────────────┐│
│  │ ttwu_do_activate()                                        ││
│  │  ├─ activate_task() - 将任务加入运行队列                   ││
│  │  │   └─ enqueue_task()                                    ││
│  │  │       ├─ cfs: enqueue_task_fair()                      ││
│  │  │       ├─ rt:  enqueue_task_rt()                        ││
│  │  │       └─ dl:  enqueue_task_dl()                        ││
│  │  └─ ttwu_do_wakeup() - 检查抢占                            ││
│  │      └─ check_preempt_curr()                             ││
│  └────────────────────────────────────────────────────────────┘│
│                              │                                   │
│                              ▼                                   │
│  ┌────────────────────────────────────────────────────────────┐│
│  │ check_preempt_curr()                                      ││
│  │  ├─ check_preempt_wakeup() - CFS检查                      ││
│  │  ├─ check_preempt_curr_rt() - RT检查                      ││
│  │  └─ 如果需要，设置TIF_NEED_RESCHED                        ││
│  └────────────────────────────────────────────────────────────┘│
│                              │                                   │
│                              ▼                                   │
│  ┌────────────────────────────────────────────────────────────┐│
│  │ schedule() - 在适当时机进行调度                            ││
│  └────────────────────────────────────────────────────────────┘│
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## 6. 现代Linux特性

### 6.1 eBPF调度扩展

Linux 5.x+ 引入了eBPF可编程调度器，允许动态修改调度行为：

```c
// kernel/sched/ext.c

/*
 * eBPF-based extensible scheduler (sched_ext) allows implementing custom
 * scheduling policies in BPF programs.
 */

/*
 * BPF Scheduler interface structures:
 */
struct sched_ext_ops {
    /*
     * Task lifecycle:
     */
    void (*enqueue)(struct task_struct *p, u64 enq_flags);
    void (*dequeue)(struct task_struct *p, u64 deq_flags);
    void (*dispatch)(s32 cpu, struct task_struct *prev);
    struct task_struct *(*pick_next_task)(s32 cpu, struct task_struct *prev);

    /*
     * Task state changes:
     */
    void (*runnable)(struct task_struct *p, u64 enq_flags);
    void (*running)(struct task_struct *p);
    void (*stopping)(struct task_struct *p, bool runnable);
    void (*quiescent)(struct task_struct *p, u64 deq_flags);

    /*
     * CPU lifecycle:
     */
    s32 (*select_cpu)(struct task_struct *p, s32 prev_cpu, u64 wake_flags);
    void (*set_cpumask)(struct task_struct *p, const struct cpumask *cpumask);
    void (*set_weight)(struct task_struct *p, u32 weight);

    /*
     * Group operations:
     */
    void (*cpu_acquire)(s32 cpu, struct cgroup *cgrp);
    void (*cpu_release)(s32 cpu, struct cgroup *cgrp);

    /*
     * Timer:
     */
    void (*update_idle)(s32 cpu, bool idle);
    u64 (*run_timer)(s32 cpu, u64 now);

    /*
     * Init/Exit:
     */
    s32 (*init)(void);
    void (*exit)(struct scx_exit_info *info);

    /* ... 其他操作 ... */
};
```

**eBPF调度器工作流程**：

```
┌─────────────────────────────────────────────────────────────────┐
│                  eBPF可扩展调度器架构                            │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │              用户空间 BPF 程序                           │   │
│  │  (自定义调度策略实现)                                    │   │
│  └──────────────────────┬──────────────────────────────────┘   │
│                         │                                        │
│                         ▼ BPF系统调用                            │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │              BPF 验证器和安全检查                        │   │
│  └──────────────────────┬──────────────────────────────────┘   │
│                         │                                        │
│                         ▼                                        │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │              sched_ext 调度类                            │   │
│  │  ┌─────────────────────────────────────────────────┐   │   │
│  │  │ sched_ext_ops (BPF回调函数表)                    │   │   │
│  │  │  - enqueue_task_bpf()                            │   │   │
│  │  │  - dequeue_task_bpf()                            │   │   │
│  │  │  - pick_next_task_bpf()                          │   │   │
│  │  │  - ...                                           │   │   │
│  │  └─────────────────────────────────────────────────┘   │   │
│  └──────────────────────┬──────────────────────────────────┘   │
│                         │                                        │
│                         ▼                                        │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │              通用调度层 (schedule())                     │   │
│  └──────────────────────┬──────────────────────────────────┘   │
│                         │                                        │
│                         ▼                                        │
│  ┌─────────────────────────────────────────────────────────┐   │
│  │              运行队列 (rq/cfs_rq/rt_rq)                  │   │
│  └─────────────────────────────────────────────────────────┘   │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### 6.2 Core Scheduling

Core Scheduling是Linux 5.x引入的安全特性，用于防止跨进程侧信道攻击（如Spectre）：

```c
// kernel/sched/core.c

/*
 * Core scheduling is a feature that ensures only trusted tasks run
 * concurrently on siblings of a physical core (hyperthreads).
 * This mitigates side-channel attacks like L1TF and MDS.
 */

struct core_sched_cookie {
    atomic_t ref;
    unsigned long cookie;
};

/*
 * Core scheduling groups tasks based on their "cookie".
 * Tasks with the same cookie are considered trusted to share
 * a physical core. Untrusted tasks (different cookies) are
 * never scheduled simultaneously on the same core.
 */

static void core_sched_assign(struct task_struct *p, struct core_sched_cookie *cookie)
{
    if (p->core_cookie == cookie)
        return;

    // 从旧的core组移除
    if (p->core_cookie)
        dec_core_cookie(p);

    p->core_cookie = cookie;

    // 添加到新的core组
    if (cookie)
        inc_core_cookie(p);
}

/*
 * Pick a task from the core for core-scheduling:
 */
static struct task_struct *pick_task_from_core(struct rq *rq)
{
    struct task_struct *p, *max = NULL;
    struct cfs_rq *cfs_rq = &rq->cfs;
    struct sched_entity *se;

    // 遍历core上的所有任务
    for_each_task_on_core(rq, p) {
        se = &p->se;

        // 检查core cookie兼容性
        if (!match_core_cookie(p, rq->core_cookie))
            continue;

        // 选择最高优先级的任务
        if (!max || entity_before(se, &max->se))
            max = p;
    }

    return max;
}
```

**Core Scheduling架构**：

```
┌─────────────────────────────────────────────────────────────────┐
│                   Core Scheduling 架构                           │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  物理核心 (Physical Core)                                         │
│  ┌───────────────────────────────────────────────────────────┐ │
│  │                                                           │ │
│  │  CPU线程0 (SMT Thread 0)      CPU线程1 (SMT Thread 1)     │ │
│  │  ┌─────────────────────┐     ┌─────────────────────┐      │ │
│  │  │ 任务A (cookie=1)    │     │ 任务B (cookie=1)    │      │ │
│  │  │ 任务C (cookie=1)    │     │ 任务D (cookie=2)    │ ❌   │ │
│  │  │                     │     │                     │      │ │
│  │  │ 可运行: A,C         │     │ 可运行: B           │      │ │
│  │  │ 不能运行D           │     │ 不能运行A,C         │      │ │
│  │  └─────────────────────┘     └─────────────────────┘      │ │
│  │                                                           │ │
│  │  Cookie分配策略:                                          │ │
│  │  ├─ 相同Cookie = 可共享物理核心                            │ │
│  │  └─ 不同Cookie = 不能同时运行                              │ │
│  │                                                           │ │
│  │  应用场景:                                                │ │
│  │  ├─ 多租户隔离                                            │ │
│  │  ├─ 虚拟机安全                                            │ │
│  │  └─ 防止侧信道攻击                                        │ │
│  │                                                           │ │
│  └───────────────────────────────────────────────────────────┘ │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### 6.3 SCHED_DEADLINE

SCHED_DEADLINE实现了最早截止时间优先（EDF）和常量带宽服务器（CBS）算法：

```c
// kernel/sched/deadline.c

/*
 * Deadline scheduling class:
 *
 * This class implements the SCHED_DEADLINE scheduling policy.
 * It uses the Earliest Deadline First (EDF) algorithm and
 * Constant Bandwidth Server (CBS) for bandwidth management.
 */

struct sched_dl_entity {
    struct rb_node rb_node;          // 红黑树节点
    u64 dl_runtime;                  // 运行时间预算
    u64 dl_deadline;                 // 绝对截止时间
    u64 dl_period;                   // 周期
    u64 dl_bw;                       // 带宽 (runtime/period)
    u64 dl_density;                  // 密度

    /*
     * Actual scheduling parameters:
     */
    s64 runtime;                     // 剩余运行时间
    u64 deadline;                    // 当前截止时间
    unsigned int flags;

    /*
     * Some bool flags:
     */
    int dl_throttled      : 1;
    int dl_boosted        : 1;
    int dl_yielded        : 1;
    int dl_non_contending : 1;

    struct hrtimer dl_timer;         // 截止时间定时器
    struct hrtimer dl_watchdog;      // 看门狗定时器

#ifdef CONFIG_SMP
    /*
     * DS (Deadline scheduling) fields:
     */
    struct rq *rq;                   // 当前运行队列
    struct cpumask *span;            // 允许的CPU掩码
#endif
};

/*
 * Earliest Deadline First (EDF) pick:
 */
static struct task_struct *pick_next_task_dl(struct rq *rq)
{
    struct task_struct *p;
    struct sched_dl_entity *dl_se;
    struct dl_rq *dl_rq = &rq->dl;

    // 如果没有DL任务
    if (!dl_rq->dl_nr_running)
        return NULL;

    // 检查DL任务是否被限制
    if (dl_rq->dl_throttled)
        return NULL;

    // 选择最早截止时间的任务
    dl_se = rb_entry(dl_rq->rb_leftmost, struct sched_dl_entity, rb_node);
    p = dl_task_of(dl_se);

    return p;
}

/*
 * Constant Bandwidth Server (CBS) replenishment:
 */
static void replenish_dl_entity(struct sched_dl_entity *dl_se)
{
    struct dl_rq *dl_rq = dl_rq_of_se(dl_se);

    // 补充运行时间
    dl_se->runtime = dl_se->dl_runtime;

    // 更新截止时间
    dl_se->deadline = rq_clock(rq_of_dl_rq(dl_rq)) + dl_se->dl_deadline;

    // 重新加入队列
    if (!dl_se->on_rq)
        enqueue_dl_entity(dl_se);
}

/*
 * Check if we need to throttle the task:
 */
static void update_curr_dl(struct rq *rq)
{
    struct task_struct *curr = rq->curr;
    struct sched_dl_entity *dl_se = &curr->dl;
    s64 runtime;

    runtime = dl_se->runtime;

    // 如果运行时间耗尽
    if (runtime <= 0) {
        // 限制任务
        dl_se->dl_throttled = 1;
        dequeue_dl_entity(dl_se);

        // 设置定时器在下一个周期补充
        hrtimer_start(&dl_se->dl_timer,
                      ns_to_ktime(dl_se->deadline - dl_se->dl_deadline + dl_se->dl_period),
                      HRTIMER_MODE_ABS_PINNED);
    }
}
```

**SCHED_DEADLINE参数设置**：

```c
// 使用sched_setattr()系统调用设置DEADLINE参数
struct sched_attr {
    __u32 size;              // 结构体大小
    __u32 sched_policy;      // SCHED_DEADLINE
    __u64 sched_flags;       // 标志
    __s32 sched_nice;        // nice值(不用于DL)
    __u32 sched_priority;    // 优先级(不用于DL)
    __u64 sched_runtime;     // 运行时间预算 (ns)
    __u64 sched_deadline;    // 相对截止时间 (ns)
    __u64 sched_period;      // 周期 (ns)
};

/*
 * 示例: 设置一个周期为10ms、运行时间3ms、截止时间10ms的任务
 */
struct sched_attr attr = {
    .size = sizeof(struct sched_attr),
    .sched_policy = SCHED_DEADLINE,
    .sched_runtime = 3 * 1000 * 1000,    // 3ms
    .sched_deadline = 10 * 1000 * 1000,  // 10ms
    .sched_period = 10 * 1000 * 1000,    // 10ms
};

syscall(__NR_sched_setattr, pid, &attr, flags);
```

**SCHED_DEADLINE带宽管理**：

```
┌─────────────────────────────────────────────────────────────────┐
│              SCHED_DEADLINE 带宽管理 (CBS)                       │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  任务参数:                                                        │
│  ┌───────────────────────────────────────────────────────────┐ │
│  │ Runtime = 3ms, Deadline = 10ms, Period = 10ms             │ │
│  │ Bandwidth = Runtime/Period = 30%                          │ │
│  └───────────────────────────────────────────────────────────┘ │
│                                                                  │
│  运行时序:                                                        │
│  ┌───────────────────────────────────────────────────────────┐ │
│  │                                                           │ │
│  │  Time:  0    3    6    9    10   13   20   23            │ │
│  │         │▓▓▓▓▓▓▓│    │    │▓▓▓▓▓▓▓│    │▓▓▓▓▓▓▓│         │ │
│  │         │ 运行   │    │    │ 运行   │    │ 运行   │         │ │
│  │         └──┬─────┘    │    └──┬─────┘    └──┬─────┘         │ │
│  │      截止  │          │       │             │               │ │
│  │      时间  │          │       │             │               │ │
│  │      ──────┘          │       │             │               │ │
│  │                       │       │             │               │ │
│  │  如果Runtime耗尽:                                     │ │
│  │  - 任务被限制(throttled)                              │ │
│  │  - 等待下一个周期补充                                 │ │
│  │                                                       │ │
│  └───────────────────────────────────────────────────────────┘ │
│                                                                  │
│  系统带宽限制:                                                     │
│  ┌───────────────────────────────────────────────────────────┐ │
│  │ 总带宽 <= SCHED_DL_BANDWIDTH (默认95%)                    │ │
│  │ 防止实时任务耗尽所有CPU资源                               │ │
│  └───────────────────────────────────────────────────────────┘ │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

---

## 7. 性能调优

### 7.1 内核参数调优

**CFS调度参数**：

```bash
# /proc/sys/kernel/

# 目标调度延迟 (ns)
# 默认值: 6000000 (6ms)
# 降低此值可以提高交互性，但会增加上下文切换开销
kernel.sched_latency_ns = 6000000

# 最小调度粒度 (ns)
# 默认值: 750000 (0.75ms)
# 防止时间片过小kernel.sched_min_granularity_ns = 750000

# 唤醒抢占粒度 (ns)
# 默认值: 1000000 (1ms)
# 控制唤醒任务抢占当前任务的阈值
kernel.sched_wakeup_granularity_ns = 1000000

# 迁移成本 (ns)
# 默认值: 500000 (0.5ms)
# 估计的缓存冷启动成本
kernel.sched_migration_cost_ns = 500000

# 平均负载周期 (us)
# 默认值: 1000 (1ms)
kernel.sched_avg_period_us = 1000

# 可运行平均半衰期 (us)
# 默认值: 10000 (10ms)
kernel.sched_ravg_window = 10000000
```

**实时调度参数**：

```bash
# 实时任务运行时间限制 (us)
# 默认值: 950000 (950ms/秒)
kernel.sched_rt_runtime_us = 950000

# 实时任务周期 (us)
# 默认值: 1000000 (1秒)
kernel.sched_rt_period_us = 1000000

# 注意: 如果 sched_rt_runtime_us = -1, 实时任务可以占用100% CPU
```

**CPU亲和性配置**：

```bash
# 禁用自动NUMA平衡 (如果不需要)
kernel.numa_balancing = 0

# CFS负载均衡权重
kernel.sched_child_runs_first = 0

# 节能调度器
# 启用后可降低空闲CPU的功耗
kernel.sched_energy_aware = 1
```

### 7.2 调度策略选择指南

**调度策略选择决策树**：

```
┌─────────────────────────────────────────────────────────────────┐
│                  调度策略选择决策树                              │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  开始                                                             │
│   │                                                              │
│   ▼                                                              │
│  任务是否是实时任务?                                               │
│   │                                                              │
│   ├─ 是 ──► 任务是否有截止时间要求?                                │
│   │           │                                                  │
│   │           ├─ 是 ──► 使用 SCHED_DEADLINE                       │
│   │           │         (最优实时性能，可验证)                     │
│   │           │                                                  │
│   │           └─ 否 ──► 任务是否需要时间片轮转?                     │
│   │                     │                                        │
│   │                     ├─ 是 ──► 使用 SCHED_RR                   │
│   │                     │         (同优先级轮转)                   │
│   │                     │                                        │
│   │                     └─ 否 ──► 使用 SCHED_FIFO                 │
│   │                               (先到先服务)                     │
│   │                                                              │
│   └─ 否 ──► 任务是否是批处理任务?                                  │
│             │                                                    │
│             ├─ 是 ──► 使用 SCHED_BATCH                            │
│             │         (减少缓存抖动，延长任务运行时间)               │
│             │                                                    │
│             └─ 否 ──► 任务优先级是否最低?                          │
│                       │                                          │
│                       ├─ 是 ──► 使用 SCHED_IDLE                   │
│                       │         (仅在其他任务不运行时执行)          │
│                       │                                          │
│                       └─ 否 ──► 使用 SCHED_OTHER (默认)           │
│                                 (CFS公平调度，适合大多数应用)        │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

**调度策略对比表**：

| 策略 | 优先级范围 | 适用场景 | 特点 |
|------|-----------|---------|------|
| SCHED_OTHER | nice -20~19 | 通用应用 | 公平分享CPU，默认策略 |
| SCHED_FIFO | 1-99 | 硬实时 | 无时间片，一直运行直到阻塞 |
| SCHED_RR | 1-99 | 软实时 | 有时间片，同优先级轮转 |
| SCHED_BATCH | nice -20~19 | 批处理 | 减少缓存抖动，降低优先级 |
| SCHED_IDLE | 0 | 最低优先级 | 仅在其他任务不运行时执行 |
| SCHED_DEADLINE | 0 | 实时任务 | 基于截止时间调度，可验证 |

### 7.3 监控工具

**schedstat统计**：

```bash
# 启用调度统计
CONFIG_SCHEDSTATS=y

# 查看调度统计
$ cat /proc/schedstat
version 15
timestamp 1234567890
cpu0 12345 67890 111 222 333 444 555 666 777 888 999 0
cpu1 12345 67890 111 222 333 444 555 666 777 888 999 0
...

# 字段说明:
# cpu<n> yld_count smt_count sched_count sched_goidle ttwu_count ttwu_local
#        rq_cpu_time [run/sleep/wait]_count [run/sleep/wait]_time [...]
```

**perf sched分析**：

```bash
# 记录调度事件
$ perf sched record -a -- sleep 60

# 报告调度延迟
$ perf sched latency

# 示例输出:
# -------------------------------------------------------------------------
#  Task                  |   Runtime ms  | Switches | Average delay ms   |
# -------------------------------------------------------------------------
#  ksoftirqd/0:3         |      0.000 ms |        1 | avg:  233.9399 ms  |
#  migration/0:9         |      0.002 ms |       10 | avg:   92.1423 ms  |
#  sshd(1234):2345       |      5.234 ms |       50 | avg:    0.5234 ms  |
# -------------------------------------------------------------------------

# 查看调度图
$ perf sched map

# 查看时间线
$ perf sched timehist
```

**eBPF/BCC工具**：

```python
#!/usr/bin/env python3
# runqlat.py - 运行队列延迟直方图

from bcc import BPF

# BPF程序
bpf_text = """
#include <uapi/linux/ptrace.h>
#include <linux/sched.h>

struct key_t {
    u32 cpu;
    u32 pid;
    u32 tgid;
};

struct val_t {
    u64 ts;
    char comm[TASK_COMM_LEN];
};

BPF_HASH(start, struct key_t, struct val_t);
BPF_HISTOGRAM(dist);

int trace_enqueue(struct pt_regs *ctx, struct rq *rq, struct task_struct *p, int flags)
{
    struct key_t key = {};
    struct val_t val = {};

    key.cpu = bpf_get_smp_processor_id();
    key.pid = p->pid;
    key.tgid = p->tgid;

    val.ts = bpf_ktime_get_ns();
    bpf_get_current_comm(&val.comm, sizeof(val.comm));

    start.update(&key, &val);
    return 0;
}

int trace_run(struct pt_regs *ctx, struct task_struct *prev)
{
    u64 ts = bpf_ktime_get_ns();
    struct key_t key = {};
    struct val_t *valp;

    key.cpu = bpf_get_smp_processor_id();
    key.pid = bpf_get_current_pid_tgid() >> 32;
    key.tgid = bpf_get_current_pid_tgid() & 0xFFFFFFFF;

    valp = start.lookup(&key);
    if (valp) {
        u64 delta = ts - valp->ts;
        delta /= 1000; // 转换为us
        dist.increment(bpf_log2l(delta));
        start.delete(&key);
    }

    return 0;
}
"""

b = BPF(text=bpf_text)
b.attach_kprobe(event="ttwu_do_activate", fn_name="trace_enqueue")
b.attach_kprobe(event="finish_task_switch.isra.0", fn_name="trace_run")

print("Tracing run queue latency... Hit Ctrl-C to end.")

try:
    sleep(99999999)
except KeyboardInterrupt:
    print()

b["dist"].print_log2_hist("usecs")
```

**systemd-cgtop监控**：

```bash
# 按cgroup查看资源使用
$ systemd-cgtop

# 输出示例:
# Control Group                    Tasks   %CPU   Memory  Input/s Output/s
# /                                  450   25.0    8.5G        -        -
# /user.slice                        200   15.0    4.2G        -        -
# /system.slice                      150    8.0    3.5G        -        -
# /system.slice/nginx.service         10    2.0    128M        -        -
```

**irqbalance调优**：

```bash
# 查看当前IRQ分布
$ cat /proc/interrupts

# 禁用irqbalance手动调优
$ systemctl stop irqbalance

# 设置IRQ亲和性 (例如将IRQ 16绑定到CPU 0-3)
$ echo "f" > /proc/irq/16/smp_affinity

# 或者在irqbalance配置中设置
$ cat /etc/sysconfig/irqbalance
IRQBALANCE_ARGS="--hintpolicy=exact"
```

### 7.4 性能调优案例

**案例1: 数据库服务器调优**

```bash
# 目标: 最大化吞吐量和降低延迟

# 1. 禁用NUMA自动平衡 (避免内存迁移开销)
echo 0 > /proc/sys/kernel/numa_balancing

# 2. 增加CFS调度延迟 (减少上下文切换)
echo 12000000 > /proc/sys/kernel/sched_latency_ns
echo 1500000 > /proc/sys/kernel/sched_min_granularity_ns

# 3. 禁用节能调度器 (最大化性能)
echo 0 > /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor
echo performance > /sys/devices/system/cpu/cpu*/cpufreq/scaling_governor

# 4. 将数据库线程绑定到特定CPU
# 在应用程序中使用 sched_setaffinity()

# 5. 使用 HugePages 减少TLB miss
echo 1024 > /proc/sys/vm/nr_hugepages
```

**案例2: 实时应用调优**

```bash
# 目标: 保证实时任务的确定性延迟

# 1. 隔离CPU (防止其他任务在隔离CPU上运行)
# 在GRUB参数中添加: isolcpus=2,3

# 2. 禁用CPU频率调节
cpufreq-set -c 2 -g performance
cpufreq-set -c 3 -g performance

# 3. 禁用软中断在隔离CPU上
echo 0 > /proc/irq/default_smp_affinity
echo 2 > /proc/irq/IRQ_NUMBER/smp_affinity  # 仅允许CPU1处理IRQ

# 4. 将实时任务绑定到隔离CPU
chrt -f 99 taskset -c 2,3 ./realtime_app

# 5. 禁用内存压缩
echo 0 > /proc/sys/vm/compact_unevictable_allowed

# 6. 锁定内存 (防止页交换)
# 在应用程序中使用 mlockall(MCL_CURRENT | MCL_FUTURE)
```

**案例3: 容器/云环境调优**

```bash
# 目标: 公平的资源分配和良好的多租户隔离

# 1. 启用CPU份额调度 (CFS shares)
# Docker: --cpu-shares=1024

# 2. 设置CPU配额和周期
# Docker: --cpu-quota=50000 --cpu-period=100000  (限制50% CPU)

# 3. 使用CPU sets限制CPU
# Docker: --cpuset-cpus="0-3"

# 4. 在Kubernetes中配置资源限制:
# resources:
#   limits:
#     cpu: "1"
#   requests:
#     cpu: "500m"

# 5. 启用CPU节流统计
CONFIG_SCHED_DEBUG=y

# 查看节流统计:
cat /proc/sys/kernel/sched_cfs_bandwidth_slice_us
cat /sys/fs/cgroup/cpu/kubepods/podXXX/cpu.stat
cat /sys/fs/cgroup/cpu/kubepods/podXXX/cpu.cfs_throttled_seconds_total
```

---

## 8. 总结与展望

### 8.1 关键技术总结

| 特性 | 版本 | 核心贡献 | 适用场景 |
|------|------|---------|---------|
| CFS | 2.6.23+ | 红黑树+vruntime | 通用任务调度 |
| RT调度 | 早期 | 优先级队列 | 硬实时应用 |
| SCHED_DEADLINE | 3.14+ | EDF+CBS | 可验证实时系统 |
| eBPF调度 | 5.x+ | 可编程调度器 | 自定义策略 |
| Core Scheduling | 5.x+ | SMT安全 | 多租户/云环境 |
| Energy Aware | 5.x+ | 功耗优化 | 移动/嵌入式 |

### 8.2 未来发展趋势

1. **异构调度**：支持big.LITTLE等异构CPU架构
2. **ML增强调度**：利用机器学习预测任务行为
3. **更细粒度调度**：用户态调度、协程调度集成
4. **跨层优化**：调度器与内存管理、IO子系统协同

### 8.3 参考资源

- Linux内核源码: https://github.com/torvalds/linux
- 内核文档: Documentation/scheduler/
- LWN.net调度器文章: https://lwn.net/Kernel/Index/#Scheduler
- 经典书籍: "Linux Kernel Development" by Robert Love

---

## 附录A: 数据流程图

### A.1 CFS调度完整流程

```
┌──────────────────────────────────────────────────────────────────────────────┐
│                        CFS调度完整流程图                                       │
├──────────────────────────────────────────────────────────────────────────────┤
│                                                                               │
│  时钟中断                                                                        │
│     │                                                                         │
│     ▼                                                                         │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │ scheduler_tick()                                                       │  │
│  │  ├─ update_rq_clock() - 更新运行队列时钟                              │  │
│  │  └─ task_tick_fair() - CFS时钟处理                                     │  │
│  │      └─ entity_tick()                                                 │  │
│  │          ├─ update_curr() - 更新当前任务统计                           │  │
│  │          │   ├─ delta_exec = now - curr->exec_start                   │  │
│  │          │   ├─ curr->sum_exec_runtime += delta_exec                  │  │
│  │          │   └─ curr->vruntime += calc_delta_fair()                   │  │
│  │          ├─ update_load_avg() - 更新负载平均                           │  │
│  │          └─ check_preempt_tick() - 检查抢占                            │  │
│  │              ├─ sched_slice() - 计算时间片                             │  │
│  │              ├─ if (delta_exec > slice) resched_curr()                │  │
│  │              └─ if (vruntime_diff > threshold) resched_curr()         │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│     │                                                                         │
│     │ (如果需要重新调度)                                                        │
│     ▼                                                                         │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │ schedule() - 主调度函数                                                │  │
│  │  ├─ rq_lock() - 获取运行队列锁                                         │  │
│  │  ├─ deactivate_task() - 如果任务睡眠则移除                             │  │
│  │  ├─ pick_next_task() - 选择下一个任务                                  │  │
│  │  │   └─ fair_sched_class.pick_next_task()                             │  │
│  │  │       └─ pick_next_task_fair()                                     │  │
│  │  │           ├─ pick_next_entity() - 选择最左实体                      │  │
│  │  │           │   └─ __pick_first_entity()                             │  │
│  │  │           │       └─ rb_first() - 红黑树最左节点                    │  │
│  │  │           └─ set_next_entity() - 设置为当前运行                     │  │
│  │  │               ├─ cfs_rq->curr = se                                 │  │
│  │  │               └─ se->prev_sum_exec_runtime = se->sum_exec_runtime  │  │
│  │  ├─ context_switch() - 上下文切换                                      │  │
│  │  │   ├─ switch_mm() - 切换地址空间                                     │  │
│  │  │   └─ switch_to() - 切换寄存器和栈                                   │  │
│  │  └─ rq_unlock() - 释放运行队列锁                                       │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│                                                                               │
└──────────────────────────────────────────────────────────────────────────────┘
```

### A.2 任务状态转换图

```
┌──────────────────────────────────────────────────────────────────────────────┐
│                        任务状态转换图                                         │
├──────────────────────────────────────────────────────────────────────────────┤
│                                                                               │
│                         ┌──────────────────┐                                  │
│                         │   创建 (fork)    │                                  │
│                         └────────┬─────────┘                                  │
│                                  │                                            │
│                                  ▼                                            │
│              ┌──────────────────────────────────┐                            │
│              │   TASK_RUNNING (可运行/正在运行)  │                            │
│              └──────────────────────────────────┘                            │
│                 │        ▲      │        ▲                                   │
│                 │        │      │        │                                   │
│   schedule()    │        │      │        │  被唤醒                            │
│   (抢占/时间    │        │      │        │  (wake_up_process)                 │
│    片用完)      │        │      │        │                                   │
│                 ▼        │      ▼        │                                   │
│   ┌──────────────────────────┐   ┌──────────────────────────┐               │
│   │ TASK_INTERRUPTIBLE       │   │ TASK_UNINTERRUPTIBLE     │               │
│   │ (可中断睡眠)              │   │ (不可中断睡眠)            │               │
│   │ 等待:                    │   │ 等待:                    │               │
│   │ - 信号                   │   │ - IO完成                 │               │
│   │ - 超时                   │   │ (忽略信号)                │               │
│   └──────────────────────────┘   └──────────────────────────┘               │
│              │                           │                                   │
│              └───────────┬───────────────┘                                   │
│                          │                                                   │
│                          ▼ (事件完成)                                         │
│              ┌──────────────────────────┐                                   │
│              │ __TASK_STOPPED           │                                   │
│              │ (被信号停止)              │                                   │
│              └──────────────────────────┘                                   │
│                          │                                                   │
│                          ▼ (SIGCONT)                                          │
│              ┌──────────────────────────┐                                   │
│              │ __TASK_TRACED            │                                   │
│              │ (被调试器跟踪)            │                                   │
│              └──────────────────────────┘                                   │
│                          │                                                   │
│                          ▼ (exit)                                             │
│              ┌──────────────────────────┐                                   │
│              │ TASK_DEAD (ZOMBIE)       │                                   │
│              │ (等待父进程收尸)          │                                   │
│              └──────────────────────────┘                                   │
│                                                                               │
└──────────────────────────────────────────────────────────────────────────────┘
```

### A.3 调度域层级结构

```
┌──────────────────────────────────────────────────────────────────────────────┐
│                        调度域层级结构                                          │
├──────────────────────────────────────────────────────────────────────────────┤
│                                                                               │
│  NUMA节点级别 (MC)                                                              │
│  ┌─────────────────────────────────────────────────────────────────────────┐│
│  │  MC (Multi-Core)                                                         ││
│  │  ├─ span: 所有CPU                                                         ││
│  │  ├─ level: SD_LV_MC                                                       ││
│  │  └─ 目的: 跨NUMA节点负载均衡                                               ││
│  └─────────────────────────────────────────────────────────────────────────┘│
│                              │                                                │
│                              ▼                                                │
│  CPU Package/Die级别 (DIE)                                                     │
│  ┌─────────────────────────────────────────────────────────────────────────┐│
│  │  DIE                                                                     ││
│  │  ├─ span: 同一Package的所有CPU                                             ││
│  │  ├─ level: SD_LV_DIE                                                      ││
│  │  └─ 目的: Package内部负载均衡                                              ││
│  └─────────────────────────────────────────────────────────────────────────┘│
│                              │                                                │
│                              ▼                                                │
│  L3缓存级别 (BOOK)                                                              │
│  ┌─────────────────────────────────────────────────────────────────────────┐│
│  │  BOOK                                                                    ││
│  │  ├─ span: 共享L3缓存的CPU                                                 ││
│  │  ├─ level: SD_LV_BOOK                                                     ││
│  │  └─ 目的: L3缓存友好的任务分配                                             ││
│  └─────────────────────────────────────────────────────────────────────────┘│
│                              │                                                │
│                              ▼                                                │
│  核心级别 (MC)                                                                  │
│  ┌─────────────────────────────────────────────────────────────────────────┐│
│  │  MC (Core)                                                               ││
│  │  ├─ span: 同一物理核心的SMT兄弟                                           ││
│  │  ├─ level: SD_LV_MC                                                       ││
│  │  └─ 目的: SMT线程均衡                                                      ││
│  └─────────────────────────────────────────────────────────────────────────┘│
│                              │                                                │
│                              ▼                                                │
│  SMT线程级别 (SIBLING)                                                          │
│  ┌─────────────────────────────────────────────────────────────────────────┐│
│  │  SIBLING                                                                 ││
│  │  ├─ span: 超线程兄弟CPU                                                   ││
│  │  ├─ level: SD_LV_SIBLING                                                  ││
│  │  └─ 目的: 超线程之间任务均衡                                               ││
│  └─────────────────────────────────────────────────────────────────────────┘│
│                                                                               │
│  负载均衡策略:                                                                  │
│  ├─ 下层 (SMT/CORE): 更频繁的检查，考虑缓存亲和性                              │
│  ├─ 中层 (BOOK/DIE): 平衡检查，考虑内存带宽                                    │
│  └─ 上层 (MC/NUMA): 较少检查，避免NUMA远程访问开销                              │
│                                                                               │
└──────────────────────────────────────────────────────────────────────────────┘
```

---

## 附录B: 完整源码索引

### B.1 核心调度文件

| 文件路径 | 说明 |
|---------|------|
| `kernel/sched/core.c` | 调度器核心实现 |
| `kernel/sched/fair.c` | CFS调度器实现 |
| `kernel/sched/rt.c` | 实时调度器实现 |
| `kernel/sched/deadline.c` | DEADLINE调度器实现 |
| `kernel/sched/idle.c` | 空闲调度器实现 |
| `kernel/sched/wait.c` | 等待队列实现 |
| `kernel/sched/wait_bit.c` | 位等待实现 |
| `kernel/sched/loadavg.c` | 负载平均值计算 |
| `kernel/sched/cpufreq.c` | CPU频率调度集成 |
| `kernel/sched/cpufreq_schedutil.c` | schedutil频率调节器 |
| `kernel/sched/membarrier.c` | 内存屏障调度 |
| `kernel/sched/isolation.c` | CPU隔离支持 |
| `kernel/sched/swait.c` | 简单等待队列 |

### B.2 头文件

| 文件路径 | 说明 |
|---------|------|
| `include/linux/sched.h` | 调度器主头文件 |
| `kernel/sched/sched.h` | 调度器内部头文件 |
| `include/linux/sched/signal.h` | 信号相关调度 |
| `include/linux/sched/mm.h` | 内存调度相关 |
| `include/linux/sched/cpufreq.h` | 频率调度相关 |
| `include/linux/sched/deadline.h` | DEADLINE调度相关 |
| `include/linux/sched/rt.h` | 实时调度相关 |
| `include/linux/sched/topology.h` | 调度拓扑相关 |
| `include/linux/sched/hotplug.h` | CPU热插拔相关 |

### B.3 架构相关调度代码

| 文件路径 | 说明 |
|---------|------|
| `arch/x86/kernel/process.c` | x86进程切换 |
| `arch/arm64/kernel/process.c` | ARM64进程切换 |
| `arch/x86/include/asm/switch_to.h` | x86上下文切换 |

---

_文档版本: 1.0_
_最后更新: 2026-04-12_
_基于Linux内核版本: 5.x/6.x_

---

**注**: 本文档基于Linux内核5.x/6.x源码进行分析，具体实现细节可能因内核版本而有所差异。建议结合具体内核版本的源码进行阅读。
