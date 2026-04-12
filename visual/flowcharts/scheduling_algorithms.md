# 调度算法流程图

## 1. CFS (完全公平调度器) 算法流程

```mermaid
flowchart TD
    Start([开始]) --> Init[初始化vruntime]
    Init --> CheckQueue{运行队列<br/>是否为空?}

    CheckQueue -->|是| Idle[执行idle任务]
    CheckQueue -->|否| PickMin[选择vruntime<br/>最小的任务]

    PickMin --> CheckSlice{当前任务<br/>时间片用完?}
    CheckSlice -->|否| Continue[继续执行]
    CheckSlice -->|是| Update[更新vruntime]

    Update --> Insert[插入红黑树]
    Insert --> PickNext[选择下一个任务]
    PickNext --> ContextSwitch[上下文切换]
    ContextSwitch --> CheckQueue

    Continue --> CheckPreempt{有新任务<br/>vruntime更小?}
    CheckPreempt -->|是| Preempt[抢占当前任务]
    CheckPreempt -->|否| Continue

    Preempt --> Update
    Idle --> CheckNew{有新任务?}
    CheckNew -->|是| PickMin
    CheckNew -->|否| Idle

    style PickMin fill:#90EE90
    style ContextSwitch fill:#FFB6C1
```

## 2. 电梯算法 (SCAN) 磁盘调度

```mermaid
flowchart TD
    Start([开始]) --> Init[初始化磁头方向<br/>向上/向下]
    Init --> CheckRequests{请求队列<br/>是否为空?}

    CheckRequests -->|是| Idle[等待新请求]
    CheckRequests -->|否| Scan[沿当前方向扫描]

    Scan --> FindNearest[找到最近请求]
    FindNearest --> Execute[执行I/O操作]
    Execute --> Remove[从队列移除]
    Remove --> CheckDirection{到达磁盘<br/>边界?}

    CheckDirection -->|是| Reverse[反转方向]
    CheckDirection -->|否| CheckRequests
    Reverse --> CheckRequests
    Idle --> CheckNew{有新请求?}
    CheckNew -->|是| FindNearest
    CheckNew -->|否| Idle

    style Scan fill:#87CEEB
    style Reverse fill:#DDA0DD
```

## 3. 优先级调度算法

```mermaid
flowchart TD
    Start([开始]) --> Init[初始化优先级队列]
    Init --> CheckQueue{高优先级队列<br/>是否有任务?}

    CheckQueue -->|是| PickHigh[选择最高<br/>优先级任务]
    CheckQueue -->|否| CheckMedium{中优先级队列<br/>是否有任务?}

    CheckMedium -->|是| PickMedium[选择中优先级任务]
    CheckMedium -->|否| CheckLow{低优先级队列<br/>是否有任务?}

    CheckLow -->|是| PickLow[选择低优先级任务]
    CheckLow -->|否| Idle[执行idle]

    PickHigh --> Execute[执行任务]
    PickMedium --> Execute
    PickLow --> Execute
    Idle --> CheckWakeup{有新任务?}
    CheckWakeup -->|是| CheckQueue

    Execute --> CheckComplete{任务完成?}
    CheckComplete -->|否| CheckPreempt{被抢占?}
    CheckComplete -->|是| Remove[移除任务]

    CheckPreempt -->|是| SaveState[保存状态]
    CheckPreempt -->|否| Execute
    SaveState --> InsertQueue[插入合适队列]

    Remove --> CheckQueue
    InsertQueue --> CheckQueue
    CheckWakeup -->|否| Idle

    style PickHigh fill:#FF6B6B
    style PickMedium fill:#FFD93D
    style PickLow fill:#6BCF7F
```

## 4. 多级反馈队列 (MLFQ) 算法

```mermaid
flowchart TD
    Start([开始]) --> Init[创建多级队列<br/>Q0-Qn]
    Init --> SetQuantum[设置各级<br/>时间片长度]
    SetQuantum --> CheckQ0{Q0队列<br/>是否为空?}

    CheckQ0 -->|否| ExecQ0[执行Q0任务<br/>时间片=8ms]
    CheckQ0 -->|是| CheckQ1{Q1队列<br/>是否为空?}

    CheckQ1 -->|否| ExecQ1[执行Q1任务<br/>时间片=16ms]
    CheckQ1 -->|是| CheckQ2{Q2队列<br/>是否为空?}

    CheckQ2 -->|否| ExecQ2[执行Q2任务<br/>时间片=32ms]
    CheckQ2 -->|是| Idle[执行idle]

    ExecQ0 --> CheckIO{I/O请求?}
    ExecQ1 --> CheckIO
    ExecQ2 --> CheckIO

    CheckIO -->|是| Block[阻塞任务]
    CheckIO -->|否| CheckTimeSlice{时间片<br/>用完?}

    CheckTimeSlice -->|否| ExecQ0
    CheckTimeSlice -->|是| Demote[降级到<br/>下一级队列]

    Block --> WaitIO[等待I/O完成]
    WaitIO --> CheckBoost{需要<br/>优先级提升?}

    CheckBoost -->|是| Promote[提升到<br/>更高级队列]
    CheckBoost -->|否| InsertSame[插入原队列]

    Demote --> CheckQ0
    Promote --> CheckQ0
    InsertSame --> CheckQ0
    Idle --> CheckWakeup{有新任务?}
    CheckWakeup -->|是| InsertNew[插入Q0]
    InsertNew --> CheckQ0
    CheckWakeup -->|否| Idle

    style ExecQ0 fill:#FF9999
    style ExecQ1 fill:#FFCC99
    style ExecQ2 fill:#FFFF99
    style Demote fill:#FF6666
    style Promote fill:#66FF66
```

## 5. 最短作业优先 (SJF) 算法

```mermaid
flowchart TD
    Start([开始]) --> Init[初始化作业队列]
    Init --> CalculateBurst[估算每个作业的<br/>执行时间burst]
    CalculateBurst --> Sort[按burst时间<br/>升序排序]

    Sort --> CheckEmpty{队列<br/>是否为空?}
    CheckEmpty -->|是| Done([结束])
    CheckEmpty -->|否| PickShortest[选择burst<br/>最短的作业]

    PickShortest --> Execute[执行作业]
    Execute --> WaitComplete[等待完成]
    WaitComplete --> Record[记录实际<br/>执行时间]
    Record --> UpdateEstimate[更新估计模型]
    UpdateEstimate --> Remove[从队列移除]
    Remove --> CheckEmpty

    style PickShortest fill:#90EE90
    style Execute fill:#87CEEB
```

## 6. 银行家算法 (死锁避免)

```mermaid
flowchart TD
    Start([资源请求]) --> CheckRequest{请求 ≤<br/>Need?}
    CheckRequest -->|否| Error[错误:超出最大需求]
    CheckRequest -->|是| CheckAvailable{请求 ≤<br/>Available?}

    CheckAvailable -->|否| Wait[进程等待]
    CheckAvailable -->|是| Pretend[假装分配资源]
    Pretend --> UpdateState[更新状态]
    UpdateState --> SafetyCheck{检查<br/>安全状态?}

    SafetyCheck -->|是| Allocate[正式分配资源]
    SafetyCheck -->|否| Rollback[回滚状态]
    Rollback --> Wait

    Allocate --> Done([分配成功])
    Error --> Done
    Wait --> CheckAvailable

    style SafetyCheck fill:#FFD700
    style Allocate fill:#90EE90
    style Rollback fill:#FF6B6B
```

## 7. 工作窃取 (Work Stealing) 算法

```mermaid
flowchart TD
    Start([线程寻找任务]) --> CheckLocal{本地队列<br/>有任务?}

    CheckLocal -->|是| PopBottom[从底部<br/>取出任务]
    CheckLocal -->|否| CheckVictim{ Victim队列<br/>有任务?}

    CheckVictim -->|是| Steal[从顶部窃取<br/>任务]
    CheckVictim -->|否| CheckGlobal{全局队列<br/>有任务?}

    CheckGlobal -->|是| Dequeue[从全局队列<br/>取出任务]
    CheckGlobal -->|否| Park[线程休眠
等待信号]

    PopBottom --> Execute[执行任务]
    Steal --> Execute
    Dequeue --> Execute

    Execute --> Spawn{产生<br/>新任务?}
    Spawn -->|是| PushBottom[推入本地队列]
    Spawn -->|否| CheckLocal

    PushBottom --> CheckLocal
    Park --> Wake{被唤醒?}
    Wake -->|是| CheckLocal
    Wake -->|否| Park

    style Steal fill:#FF6B6B
    style PopBottom fill:#4ECDC4
    style Park fill:#95E1D3
```

## 8. Kubernetes调度器流程

```mermaid
flowchart TD
    Start([Pod创建]) --> Predicates[Filter阶段<br/>Predicates]

    Predicates --> CheckNodeFit{节点适合?}
    CheckNodeFit -->|否| FilterOut[过滤掉节点]
    CheckNodeFit -->|是| Keep[保留节点]

    FilterOut --> MoreNodes{还有更多<br/>节点?}
    Keep --> MoreNodes
    MoreNodes -->|是| CheckNodeFit
    MoreNodes -->|否| CheckFeasible{可行节点<br/>列表为空?}

    CheckFeasible -->|是| Pending[Pod置为Pending]
    CheckFeasible -->|否| Priorities[Score阶段<br/>Priorities]

    Priorities --> CalculateScore[计算每个节点<br/>优先级分数]
    CalculateScore --> SelectMax[选择最高分节点]
    SelectMax --> Bind[Bind阶段<br/>绑定Pod到节点]
    Bind --> UpdateAPI[更新API Server]
    UpdateAPI --> Done([调度完成])
    Pending --> Retry{重试?}
    Retry -->|是| Predicates
    Retry -->|否| Failed([调度失败])

    style Predicates fill:#E74C3C
    style Priorities fill:#3498DB
    style Bind fill:#2ECC71
```
