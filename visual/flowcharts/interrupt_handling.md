# 中断处理流程图

## 1. 硬件中断处理流程

```mermaid
flowchart TD
    Start([硬件中断]) --> SaveContext[保存当前上下文]
    SaveContext --> SwitchStack[切换到<br/>中断堆栈]
    SwitchStack --> AckPIC[向PIC/APIC<br/>发送ACK]

    AckPIC --> LookupVector[查找中断向量表]
    LookupVector --> CallHandler[调用中断处理程序]

    CallHandler --> TopHalf[执行Top Half<br/>紧急处理]
    TopHalf --> ScheduleBH{需要<br/>Bottom Half?}

    ScheduleBH -->|是| MarkPending[标记BH待执行]
    ScheduleBH -->|否| CheckMore{更多中断?}
    MarkPending --> CheckMore

    CheckMore -->|是| ProcessNext[处理下一个]
    CheckMore -->|否| RestoreContext[恢复上下文]
    ProcessNext --> LookupVector

    RestoreContext --> IRET[IRET返回]
    IRET --> End([结束])

    style TopHalf fill:#FF6B6B
    style MarkPending fill:#FFD93D
    style IRET fill:#6BCF7F
```

## 2. SoftIRQ / Tasklet 处理流程

```mermaid
flowchart TD
    Start([检查SoftIRQ]) --> CheckPending{有pending<br/>的SoftIRQ?}
    CheckPending -->|否| End([结束])
    CheckPending -->|是| DisableIRQ[关闭本地中断]

    DisableIRQ --> ClearMask[清除pending掩码]
    ClearMask --> EnableIRQ[开启本地中断]

    EnableIRQ --> LoopStart[遍历优先级]
    LoopStart --> CheckBit{该位pending?}

    CheckBit -->|否| NextBit[下一个优先级]
    CheckBit -->|是| InvokeHandler[调用处理函数]

    InvokeHandler --> CheckResched{需要<br/>重新调度?}
    CheckResched -->|是| Schedule[调用schedule]
    CheckResched -->|否| NextBit
    Schedule --> NextBit

    NextBit --> MoreBits{更多位?}
    MoreBits -->|是| LoopStart
    MoreBits -->|否| CheckAgain{又产生<br/>SoftIRQ?}

    CheckAgain -->|是| CheckPending
    CheckAgain -->|否| End

    style InvokeHandler fill:#4ECDC4
    style Schedule fill:#95E1D3
```

## 3. 系统调用中断流程

```mermaid
flowchart TD
    Start([syscall指令]) --> SaveRegs[保存寄存器]
    SaveRegs --> SwitchToKernel[切换到<br/>内核堆栈]

    SwitchToKernel --> LoadSyscallNum[加载系统调用号]
    LoadSyscallNum --> ValidateNum{检查<br/>有效性}

    ValidateNum -->|无效| SetError[设置错误码<br/>-ENOSYS]
    ValidateNum -->|有效| LookupTable[查syscall表]

    LookupTable --> CheckArgs{参数<br/>检查通过?}
    CheckArgs -->|否| SetError
    CheckArgs -->|是| CallSyscall[调用系统调用]

    CallSyscall --> HandleResult[处理返回值]
    SetError --> HandleResult
    HandleResult --> RestoreRegs[恢复寄存器]
    RestoreRegs --> SYSRET[SYSRET返回]
    SYSRET --> End([结束])

    style CallSyscall fill:#90EE90
    style SYSRET fill:#87CEEB
    style SetError fill:#FF6B6B
```

## 4. 时钟中断处理流程 (Tick)

```mermaid
flowchart TD
    Start([时钟中断]) --> UpdateJiffies[更新jiffies]
    UpdateJiffies --> UpdateTime[更新系统时间]

    UpdateTime --> UpdateProcess[更新当前进程统计]
    UpdateProcess --> DecreaseTimeslice[减少时间片]

    DecreaseTimeslice --> CheckTimeslice{时间片<br/>用完?}
    CheckTimeslice -->|是| SetNeedResched[设置<br/>TIF_NEED_RESCHED]
    CheckTimeslice -->|否| CheckTimer
    SetNeedResched --> CheckTimer

    CheckTimer[检查定时器] --> TimerExpired{定时器<br/>到期?}
    TimerExpired -->|是| RunTimer[执行定时器函数]
    TimerExpired -->|否| CheckRCU
    RunTimer --> CheckRCU

    CheckRCU[检查RCU回调] --> RCUPending{有pending<br/>回调?}
    RCUPending -->|是| RunRCU[执行RCU回调]
    RCUPending -->|否| CheckSchedule
    RunRCU --> CheckSchedule

    CheckSchedule{需要<br/>调度?} -->|是| InvokeSchedule[调用schedule]
    CheckSchedule -->|否| EndInt
    InvokeSchedule --> EndInt

    EndInt([结束]) --> End([返回])

    style SetNeedResched fill:#FFD93D
    style InvokeSchedule fill:#6BCF7F
    style RunTimer fill:#4ECDC4
```

## 5. NMI (不可屏蔽中断) 处理

```mermaid
flowchart TD
    Start([NMI]) --> SaveMinimal[最小化保存<br/>关键寄存器]
    SaveMinimal --> CheckSource{检查NMI源}

    CheckSource -->|内存校验错| HandleParity[处理内存错误]
    CheckSource -->|看门狗| HandleWatchdog[处理看门狗超时]
    CheckSource -->|性能监控| HandlePerf[处理PMC溢出]
    CheckSource -->|未知| LogUnknown[记录未知NMI]

    HandleParity --> TryRecover{尝试恢复?}
    HandleWatchdog --> DumpStack[转储堆栈]
    HandlePerf --> RecordSample[记录样本]
    LogUnknown --> End

    TryRecover -->|成功| Continue[继续执行]
    TryRecover -->|失败| Panic[系统崩溃]
    DumpStack --> PanicCheck{严重错误?}
    RecordSample --> End

    PanicCheck -->|是| Panic
    PanicCheck -->|否| End
    Continue --> End
    Panic --> EndSystem([系统停止])

    style Panic fill:#FF6B6B
    style HandleParity fill:#FFD93D
    style HandleWatchdog fill:#FF9999
```

## 6. 中断上下半部协作流程

```mermaid
sequenceDiagram
    participant H as Hardware
    participant T as Top Half
    participant Q as Work Queue
    participant B as Bottom Half
    participant P as Process Context

    H->>T: 硬件中断触发
    T->>T: 快速关键处理
    T->>Q: 调度Bottom Half
    T->>H: 中断返回

    Note over Q: 稍后处理

    Q->>B: 执行Bottom Half
    B->>B: 非紧急处理
    B->>P: 唤醒等待进程

    P->>P: 处理数据
    P->>P: 用户态处理
```

## 7. 中断嵌套处理流程

```mermaid
flowchart TD
    Start([中断发生]) --> CheckLevel{当前<br/>中断级别}

    CheckLevel -->|禁止中断| QueueInt[排队等待]
    CheckLevel -->|允许中断| CheckPriority{新中断<br/>优先级更高?}

    CheckPriority -->|否| QueueInt
    CheckPriority -->|是| SaveCurrent[保存当前<br/>中断上下文]

    SaveCurrent --> NestLevel++[嵌套深度+1]
    NestLevel++ --> AckNew[ACK新中断]
    AckNew --> ProcessNew[处理新中断]

    ProcessNew --> CompleteNew{处理完成?}
    CompleteNew -->|否| ProcessNew
    CompleteNew -->|是| NestLevel--[嵌套深度-1]

    NestLevel-- --> RestorePrev[恢复前中断
上下文]
    RestorePrev --> ResumePrev[继续原中断]

    QueueInt --> CheckDequeue{可以<br/>出队?}
    CheckDequeue -->|是| ProcessQueued[处理排队中断]
    CheckDequeue -->|否| End
    ProcessQueued --> End
    ResumePrev --> End([结束])

    style SaveCurrent fill:#FFD93D
    style NestLevel++ fill:#FF9999
    style NestLevel-- fill:#90EE90
```
