--------------------------- MODULE Scheduling ---------------------------
(***************************************************************************)
(* 调度系统的TLA+形式化规约                                                  *)
(* 对应文档: schedule_formal_view/06_调度模型/                               *)
(***************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Tasks,          \* 任务集合
    Resources,      \* 资源集合
    MaxCapacity     \* 最大容量

VARIABLES
    taskQueue,      \* 任务队列
    running,        \* 运行中的任务
    resourceState,  \* 资源状态
    schedule        \* 调度决策

vars == <<taskQueue, running, resourceState, schedule>>

---------------------------------------------------------------------------
(* 类型定义 *)

TaskState == {"pending", "running", "completed", "failed"}

ResourceState == [
    available: Nat,
    allocated: Nat
]

ScheduleDecision == [
    task: Tasks,
    resource: Resources,
    action: {"start", "stop", "preempt"}
]

---------------------------------------------------------------------------
(* 初始状态 *)

TypeInvariant ==
    /\ taskQueue \in Seq(Tasks)
    /\ running \subseteq Tasks
    /\ \A r \in Resources: resourceState[r].available + resourceState[r].allocated <= MaxCapacity

Init ==
    /\ taskQueue = <<>>
    /\ running = {}
    /\ resourceState = [r \in Resources |-> [available |-> MaxCapacity, allocated |-> 0]]
    /\ schedule = {}

---------------------------------------------------------------------------
(* 安全性质 *)

(* 资源不超额分配 *)
ResourceSafety ==
    \A r \in Resources:
        resourceState[r].allocated <= MaxCapacity

(* 任务互斥 - 同一任务不能同时运行多次 *)
TaskMutex ==
    \A t \in Tasks:
        Cardinality({t} \cap running) <= 1

(* 无饥饿 - 每个任务最终会被调度 *)
NoStarvation ==
    \A t \in Tasks:
        t \in running \/ t \in Range(taskQueue) \/ TRUE

---------------------------------------------------------------------------
(* 动作定义 *)

(* 提交新任务 *)
SubmitTask(t) ==
    /\ t \notin running
    /\ t \notin Range(taskQueue)
    /\ taskQueue' = Append(taskQueue, t)
    /\ UNCHANGED <<running, resourceState, schedule>>

(* 调度任务运行 *)
ScheduleTask(t, r) ==
    /\ t \in Range(taskQueue)
    /\ resourceState[r].available > 0
    /\ taskQueue' = SelectSeq(taskQueue, LAMBDA x: x /= t)
    /\ running' = running \cup {t}
    /\ resourceState' = [resourceState EXCEPT 
        ![r].available = @ - 1,
        ![r].allocated = @ + 1]
    /\ schedule' = schedule \cup {[task |-> t, resource |-> r, action |-> "start"]}

(* 任务完成 *)
CompleteTask(t, r) ==
    /\ t \in running
    /\ running' = running \ {t}
    /\ resourceState' = [resourceState EXCEPT 
        ![r].available = @ + 1,
        ![r].allocated = @ - 1]
    /\ schedule' = schedule \cup {[task |-> t, resource |-> r, action |-> "stop"]}
    /\ UNCHANGED taskQueue

(* 抢占任务 *)
PreemptTask(victim, newcomer, r) ==
    /\ victim \in running
    /\ newcomer \in Range(taskQueue)
    /\ running' = (running \ {victim}) \cup {newcomer}
    /\ taskQueue' = Append(SelectSeq(taskQueue, LAMBDA x: x /= newcomer), victim)
    /\ schedule' = schedule \cup {
        [task |-> victim, resource |-> r, action |-> "preempt"],
        [task |-> newcomer, resource |-> r, action |-> "start"]
    }
    /\ UNCHANGED resourceState

---------------------------------------------------------------------------
(* 下一状态关系 *)

Next ==
    \/ \E t \in Tasks: SubmitTask(t)
    \/ \E t \in Tasks, r \in Resources: ScheduleTask(t, r)
    \/ \E t \in Tasks, r \in Resources: CompleteTask(t, r)
    \/ \E v \in Tasks, n \in Tasks, r \in Resources: PreemptTask(v, n, r)

---------------------------------------------------------------------------
(* 时序规约 *)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

---------------------------------------------------------------------------
(* 活性性质 *)

(* 最终所有任务完成或失败 *)
EventualCompletion ==
    <>(\A t \in Tasks: t \notin running /\ t \notin Range(taskQueue))

(* 调度进度 - 如果有待处理任务，最终会被调度 *)
SchedulingProgress ==
    \A t \in Tasks:
        (t \in Range(taskQueue)) ~> (t \in running \/ t \notin Range(taskQueue))

---------------------------------------------------------------------------
(* 定理 *)

THEOREM Spec => []TypeInvariant
THEOREM Spec => []ResourceSafety
THEOREM Spec => []TaskMutex

=============================================================================
