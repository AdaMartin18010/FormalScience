# 系统调用流程图

## 1. 通用系统调用流程

```mermaid
sequenceDiagram
    participant U as User Space
    participant L as libc
    participant K as Kernel Space
    participant S as System Call Table
    participant H as Handler

    U->>L: syscall(args)
    L->>L: 设置syscall编号
    L->>K: int 0x80 / syscall指令
    K->>K: 保存用户态上下文
    K->>K: 切换到内核态
    K->>S: 查表获取处理函数
    S->>H: 调用对应handler
    H->>H: 执行系统调用
    H->>K: 返回结果
    K->>K: 恢复用户态上下文
    K->>U: 返回用户空间
```

## 2. fork() 系统调用流程

```mermaid
flowchart TD
    Start([fork]) --> CheckResource{检查资源限制}
    CheckResource -->|超出| ReturnError[返回-ENOMEM]
    CheckResource -->|OK| AllocPID[分配新PID]

    AllocPID --> CopyMM[复制内存描述符]
    CopyMM --> CopyFiles[复制文件描述符表]
    CopyFiles --> CopySignal[复制信号处理]

    CopySignal --> UpdateParent[更新父进程<br/>子进程列表]
    UpdateParent --> SetState[设置子进程状态<br/>TASK_RUNNING]

    SetState --> WakeUp[唤醒子进程]
    WakeUp --> ReturnParent[父进程返回<br/>子进程PID]
    ReturnParent --> ReturnChild[子进程返回0]

    ReturnError --> End([结束])
    ReturnParent --> End
    ReturnChild --> End

    style CopyMM fill:#FFB6C1
    style ReturnParent fill:#90EE90
    style ReturnChild fill:#87CEEB
```

## 3. execve() 系统调用流程

```mermaid
flowchart TD
    Start([execve]) --> CheckPermission{检查<br/>执行权限}
    CheckPermission -->|无权限| ReturnEACCES[返回-EACCES]
    CheckPermission -->|有权限| ReadHeader[读取文件头]

    ReadHeader --> CheckFormat{检查文件格式}
    CheckFormat -->|ELF| LoadELF[加载ELF文件]
    CheckFormat -->|脚本| ExecInterpreter[执行解释器]
    CheckFormat -->|其他| ReturnENOEXEC[返回-ENOEXEC]

    LoadELF --> CleanOld[清理旧地址空间]
    CleanOld --> AllocNew[分配新地址空间]
    AllocNew --> LoadSegments[加载程序段]

    LoadSegments --> SetupStack[设置堆栈]
    SetupStack --> SetEntry[设置入口点]
    SetEntry --> ResetSignal[重置信号处理]
    ResetSignal --> StartProcess[开始执行新程序]

    ExecInterpreter --> FindInterp[查找解释器]
    FindInterp --> SetupArgs[设置参数]
    SetupArgs --> LoadELF

    ReturnEACCES --> End([结束])
    ReturnENOEXEC --> End
    StartProcess --> End

    style LoadELF fill:#90EE90
    style CleanOld fill:#FFB6C1
    style StartProcess fill:#87CEEB
```

## 4. mmap() 系统调用流程

```mermaid
flowchart TD
    Start([mmap]) --> CheckParams{检查参数}
    CheckParams -->|无效| ReturnEINVAL[返回-EINVAL]
    CheckParams -->|有效| FindVMA[查找合适的VMA]

    FindVMA --> CheckConflict{检查地址冲突}
    CheckConflict -->|冲突| ReturnEEXIST[返回-EEXIST]
    CheckConflict -->|无冲突| AllocVMA[分配VMA结构]

    AllocVMA --> SetFlags[设置保护标志]
    SetFlags --> CheckAnon{匿名映射?}

    CheckAnon -->|是| SetupAnon[设置匿名页处理]
    CheckAnon -->|否| CheckFile{文件映射?}

    CheckFile -->|是| SetupFile[设置文件页缓存]
    CheckFile -->|否| CheckShared{共享映射?}

    CheckShared -->|是| SetupShared[设置共享内存]
    CheckShared -->|否| ReturnError[返回错误]

    SetupAnon --> InsertVMA[插入VMA链表]
    SetupFile --> InsertVMA
    SetupShared --> InsertVMA

    InsertVMA --> UpdateMM[更新内存统计]
    UpdateMM --> ReturnAddr[返回虚拟地址]

    ReturnEINVAL --> End([结束])
    ReturnEEXIST --> End
    ReturnError --> End
    ReturnAddr --> End

    style InsertVMA fill:#90EE90
    style SetupFile fill:#87CEEB
    style SetupShared fill:#FFD700
```

## 5. 进程间通信 - pipe() 流程

```mermaid
flowchart TD
    Start([pipe]) --> AllocInode[分配inode]
    AllocInode --> CreatePipe[创建管道文件]

    CreatePipe --> AllocReadFD[分配读端fd]
    AllocReadFD --> AllocWriteFD[分配写端fd]

    AllocWriteFD --> SetupBuffer[设置环形缓冲区]
    SetupBuffer --> InitLock[初始化读写锁]

    InitLock --> ReturnFD[返回fd数组<br/>fd[0]=读, fd[1]=写]
    ReturnFD --> End([结束])

    subgraph 读操作
        ReadStart[read] --> CheckEmpty{缓冲区空?}
        CheckEmpty -->|是| BlockRead[阻塞等待]
        CheckEmpty -->|否| ReadData[读取数据]
        BlockRead --> CheckEmpty
        ReadData --> WakeWriter[唤醒写者]
    end

    subgraph 写操作
        WriteStart[write] --> CheckFull{缓冲区满?}
        CheckFull -->|是| BlockWrite[阻塞等待]
        CheckFull -->|否| WriteData[写入数据]
        BlockWrite --> CheckFull
        WriteData --> WakeReader[唤醒读者]
    end

    style AllocReadFD fill:#87CEEB
    style AllocWriteFD fill:#FFB6C1
    style SetupBuffer fill:#90EE90
```

## 6. select() / poll() 流程

```mermaid
flowchart TD
    Start([select]) --> CopyFDs[拷贝fd_set<br/>到内核]
    CopyFDs --> InitTable[初始化poll_table]

    InitTable --> LoopStart[遍历所有fd]
    LoopStart --> CheckReady{fd就绪?}

    CheckReady -->|是| MarkReady[标记为就绪]
    CheckReady -->|否| AddWaitQueue[加入等待队列]

    MarkReady --> MoreFD{更多fd?}
    AddWaitQueue --> MoreFD
    MoreFD -->|是| LoopStart
    MoreFD -->|否| CheckAny{有就绪fd?}

    CheckAny -->|是| CopyBack[拷贝结果<br/>到用户空间]
    CheckAny -->|否| Schedule[进程睡眠]

    Schedule --> WakeUp{被唤醒?}
    WakeUp -->|信号| ReturnEINTR[返回-EINTR]
    WakeUp -->|超时| Return0[返回0]
    WakeUp -->|事件| LoopStart

    CopyBack --> ReturnCount[返回就绪fd数]
    ReturnEINTR --> End([结束])
    Return0 --> End
    ReturnCount --> End

    style MarkReady fill:#90EE90
    style Schedule fill:#FFB6C1
    style CopyBack fill:#87CEEB
```
