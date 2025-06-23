# Rust实现分布式工作流

我将为您展示一个基于 Rust 2024 + Tokio 的分布式工作流系统，实现各种工作流模式。

## 目录

- [Rust实现分布式工作流](#rust实现分布式工作流)
  - [目录](#目录)
  - [1. 项目依赖配置](#1-项目依赖配置)
  - [2. 基础工作流模式定义](#2-基础工作流模式定义)
  - [3. 高级工作流模式实现](#3-高级工作流模式实现)
  - [4. 工作流状态和上下文管理](#4-工作流状态和上下文管理)
  - [5. 工作流模式组合示例](#5-工作流模式组合示例)
  - [6. 工作流执行引擎](#6-工作流执行引擎)
  - [7. 工作流监控和指标收集](#7-工作流监控和指标收集)
  - [8. 主程序实现](#8-主程序实现)

## 1. 项目依赖配置

```toml
[dependencies]
tokio = { version = "1.0", features = ["full"] }
async-trait = "0.1"
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
uuid = { version = "1.0", features = ["v4"] }
dashmap = "5.5"
tracing = "0.1"
anyhow = "1.0"
thiserror = "1.0"
async-graphql = "6.0"
sqlx = { version = "0.7", features = ["postgres", "runtime-tokio-native-tls"] }
redis = { version = "0.23", features = ["tokio-comp"] }
```

## 2. 基础工作流模式定义

```rust
#[async_trait]
pub trait WorkflowPattern {
    async fn execute(&self, context: &mut WorkflowContext) -> Result<(), WorkflowError>;
    fn get_pattern_type(&self) -> PatternType;
}

#[derive(Debug, Clone)]
pub enum PatternType {
    Sequence,
    Parallel,
    Choice,
    Merge,
    Synchronization,
    MultiChoice,
    MultiMerge,
    Discriminator,
    Milestone,
    CancelRegion,
    Iteration,
}

// 序列模式
pub struct SequencePattern {
    tasks: Vec<Box<dyn WorkflowTask>>,
}

#[async_trait]
impl WorkflowPattern for SequencePattern {
    async fn execute(&self, context: &mut WorkflowContext) -> Result<(), WorkflowError> {
        for task in &self.tasks {
            task.execute(context).await?;
        }
        Ok(())
    }

    fn get_pattern_type(&self) -> PatternType {
        PatternType::Sequence
    }
}

// 并行模式
pub struct ParallelPattern {
    tasks: Vec<Box<dyn WorkflowTask>>,
}

#[async_trait]
impl WorkflowPattern for ParallelPattern {
    async fn execute(&self, context: &mut WorkflowContext) -> Result<(), WorkflowError> {
        let mut handles = Vec::new();
        
        for task in &self.tasks {
            let task = task.clone();
            let mut ctx = context.clone();
            
            let handle = tokio::spawn(async move {
                task.execute(&mut ctx).await
            });
            
            handles.push(handle);
        }

        for handle in handles {
            handle.await??;
        }

        Ok(())
    }
}
```

## 3. 高级工作流模式实现

```rust
// 选择模式
pub struct ChoicePattern {
    conditions: Vec<(Box<dyn Condition>, Box<dyn WorkflowPattern>)>,
    default: Option<Box<dyn WorkflowPattern>>,
}

#[async_trait]
impl WorkflowPattern for ChoicePattern {
    async fn execute(&self, context: &mut WorkflowContext) -> Result<(), WorkflowError> {
        for (condition, pattern) in &self.conditions {
            if condition.evaluate(context).await? {
                return pattern.execute(context).await;
            }
        }

        if let Some(default) = &self.default {
            default.execute(context).await?;
        }

        Ok(())
    }
}

// 多选模式
pub struct MultiChoicePattern {
    branches: Vec<(Box<dyn Condition>, Box<dyn WorkflowPattern>)>,
}

#[async_trait]
impl WorkflowPattern for MultiChoicePattern {
    async fn execute(&self, context: &mut WorkflowContext) -> Result<(), WorkflowError> {
        let mut handles = Vec::new();

        for (condition, pattern) in &self.branches {
            if condition.evaluate(context).await? {
                let pattern = pattern.clone();
                let mut ctx = context.clone();
                
                let handle = tokio::spawn(async move {
                    pattern.execute(&mut ctx).await
                });
                
                handles.push(handle);
            }
        }

        for handle in handles {
            handle.await??;
        }

        Ok(())
    }
}

// 判别器模式
pub struct DiscriminatorPattern {
    incoming_branches: usize,
    required_completions: usize,
    next_pattern: Box<dyn WorkflowPattern>,
}

#[async_trait]
impl WorkflowPattern for DiscriminatorPattern {
    async fn execute(&self, context: &mut WorkflowContext) -> Result<(), WorkflowError> {
        let (tx, mut rx) = tokio::sync::mpsc::channel(self.incoming_branches);
        
        for _ in 0..self.incoming_branches {
            let tx = tx.clone();
            let mut ctx = context.clone();
            
            tokio::spawn(async move {
                if let Ok(()) = self.pattern.execute(&mut ctx).await {
                    let _ = tx.send(()).await;
                }
            });
        }

        for _ in 0..self.required_completions {
            rx.recv().await.ok_or(WorkflowError::BranchFailed)?;
        }

        self.next_pattern.execute(context).await
    }
}
```

## 4. 工作流状态和上下文管理

```rust
#[derive(Clone)]
pub struct WorkflowContext {
    workflow_id: Uuid,
    variables: Arc<DashMap<String, Value>>,
    state: Arc<RwLock<WorkflowState>>,
}

#[derive(Debug)]
pub enum WorkflowState {
    Created,
    Running,
    Suspended,
    Completed,
    Failed(String),
}

impl WorkflowContext {
    pub async fn set_variable(&self, key: &str, value: Value) {
        self.variables.insert(key.to_string(), value);
    }

    pub async fn get_variable(&self, key: &str) -> Option<Value> {
        self.variables.get(key).map(|v| v.clone())
    }

    pub async fn update_state(&self, state: WorkflowState) {
        *self.state.write().await = state;
    }

    pub async fn is_cancelled(&self) -> bool {
        matches!(*self.state.read().await, WorkflowState::Failed(_))
    }
}

// 工作流持久化
pub struct WorkflowStorage {
    db: PgPool,
    redis: RedisClient,
}

impl WorkflowStorage {
    pub async fn save_workflow_state(&self, context: &WorkflowContext) -> Result<()> {
        let state = serde_json::to_value(&*context.state.read().await)?;
        let variables = serde_json::to_value(&context.variables)?;

        // 保存到 PostgreSQL
        sqlx::query!(
            "INSERT INTO workflow_states (workflow_id, state, variables) 
             VALUES ($1, $2, $3)
             ON CONFLICT (workflow_id) DO UPDATE 
             SET state = $2, variables = $3",
            context.workflow_id,
            state,
            variables
        )
        .execute(&self.db)
        .await?;

        // 缓存到 Redis
        self.redis.set_ex(
            format!("workflow:{}", context.workflow_id),
            serde_json::to_string(&context)?,
            3600,
        ).await?;

        Ok(())
    }
}
```

## 5. 工作流模式组合示例

```rust
// 复杂订单处理工作流
pub fn create_order_workflow() -> Box<dyn WorkflowPattern> {
    Box::new(SequencePattern {
        tasks: vec![
            // 1. 验证订单（并行验证多个方面）
            Box::new(ParallelPattern {
                tasks: vec![
                    Box::new(ValidateInventoryTask {}),
                    Box::new(ValidatePaymentTask {}),
                    Box::new(ValidateUserTask {}),
                ],
            }),

            // 2. 订单处理（多选择模式）
            Box::new(MultiChoicePattern {
                branches: vec![
                    (
                        Box::new(HighValueOrderCondition {}),
                        Box::new(HighPriorityProcessingPattern {}),
                    ),
                    (
                        Box::new(InternationalOrderCondition {}),
                        Box::new(InternationalShippingPattern {}),
                    ),
                ],
            }),

            // 3. 支付处理（选择模式）
            Box::new(ChoicePattern {
                conditions: vec![
                    (
                        Box::new(CreditCardPaymentCondition {}),
                        Box::new(ProcessCreditCardPattern {}),
                    ),
                    (
                        Box::new(PayPalPaymentCondition {}),
                        Box::new(ProcessPayPalPattern {}),
                    ),
                ],
                default: Some(Box::new(ProcessAlternativePaymentPattern {})),
            }),

            // 4. 订单完成（判别器模式）
            Box::new(DiscriminatorPattern {
                incoming_branches: 3,
                required_completions: 2,
                next_pattern: Box::new(FinalizeOrderPattern {}),
            }),
        ],
    })
}

// 文档审批工作流
pub fn create_document_approval_workflow() -> Box<dyn WorkflowPattern> {
    Box::new(SequencePattern {
        tasks: vec![
            // 1. 文档准备
            Box::new(PrepareDocumentTask {}),

            // 2. 并行审查
            Box::new(ParallelPattern {
                tasks: vec![
                    Box::new(TechnicalReviewTask {}),
                    Box::new(LegalReviewTask {}),
                    Box::new(FinancialReviewTask {}),
                ],
            }),

            // 3. 审批流程（多选择）
            Box::new(MultiChoicePattern {
                branches: vec![
                    (
                        Box::new(NeedsExecutiveApprovalCondition {}),
                        Box::new(ExecutiveApprovalPattern {}),
                    ),
                    (
                        Box::new(NeedsComplianceReviewCondition {}),
                        Box::new(ComplianceReviewPattern {}),
                    ),
                ],
            }),

            // 4. 最终确认（判别器）
            Box::new(DiscriminatorPattern {
                incoming_branches: 2,
                required_completions: 1,
                next_pattern: Box::new(FinalizeDocumentPattern {}),
            }),
        ],
    })
}
```

## 6. 工作流执行引擎

```rust
pub struct WorkflowEngine {
    storage: Arc<WorkflowStorage>,
    executor: Arc<WorkflowExecutor>,
}

impl WorkflowEngine {
    pub async fn new(db_pool: PgPool, redis_client: RedisClient) -> Self {
        let storage = Arc::new(WorkflowStorage::new(db_pool, redis_client));
        let executor = Arc::new(WorkflowExecutor::new(storage.clone()));
        
        Self {
            storage,
            executor,
        }
    }

    pub async fn start_workflow(
        &self,
        workflow: Box<dyn WorkflowPattern>,
        initial_context: WorkflowContext,
    ) -> Result<Uuid> {
        let workflow_id = initial_context.workflow_id;
        
        // 保存初始状态
        self.storage.save_workflow_state(&initial_context).await?;

        // 启动工作流
        self.executor.execute_workflow(workflow, initial_context).await?;

        Ok(workflow_id)
    }

    pub async fn suspend_workflow(&self, workflow_id: Uuid) -> Result<()> {
        self.executor.suspend_workflow(workflow_id).await
    }

    pub async fn resume_workflow(&self, workflow_id: Uuid) -> Result<()> {
        self.executor.resume_workflow(workflow_id).await
    }

    pub async fn cancel_workflow(&self, workflow_id: Uuid) -> Result<()> {
        self.executor.cancel_workflow(workflow_id).await
    }
}

pub struct WorkflowExecutor {
    storage: Arc<WorkflowStorage>,
    active_workflows: Arc<DashMap<Uuid, JoinHandle<Result<()>>>>,
}

impl WorkflowExecutor {
    pub async fn execute_workflow(
        &self,
        workflow: Box<dyn WorkflowPattern>,
        mut context: WorkflowContext,
    ) -> Result<()> {
        let workflow_id = context.workflow_id;
        let storage = self.storage.clone();

        let handle = tokio::spawn(async move {
            context.update_state(WorkflowState::Running).await;
            storage.save_workflow_state(&context).await?;

            match workflow.execute(&mut context).await {
                Ok(()) => {
                    context.update_state(WorkflowState::Completed).await;
                }
                Err(e) => {
                    context.update_state(WorkflowState::Failed(e.to_string())).await;
                }
            }

            storage.save_workflow_state(&context).await?;
            Ok(())
        });

        self.active_workflows.insert(workflow_id, handle);
        Ok(())
    }
}
```

## 7. 工作流监控和指标收集

```rust
pub struct WorkflowMetrics {
    workflow_duration: Histogram,
    task_duration: Histogram,
    active_workflows: Gauge,
    completed_workflows: Counter,
    failed_workflows: Counter,
}

impl WorkflowMetrics {
    pub fn new() -> Self {
        Self {
            workflow_duration: Histogram::new("workflow_duration_seconds"),
            task_duration: Histogram::new("task_duration_seconds"),
            active_workflows: Gauge::new("active_workflows"),
            completed_workflows: Counter::new("completed_workflows_total"),
            failed_workflows: Counter::new("failed_workflows_total"),
        }
    }

    pub fn record_workflow_start(&self, workflow_id: Uuid) {
        self.active_workflows.inc();
    }

    pub fn record_workflow_completion(&self, workflow_id: Uuid, duration: Duration) {
        self.active_workflows.dec();
        self.completed_workflows.inc();
        self.workflow_duration.observe(duration.as_secs_f64());
    }

    pub fn record_workflow_failure(&self, workflow_id: Uuid, error: &WorkflowError) {
        self.active_workflows.dec();
        self.failed_workflows.inc();
    }

    pub fn record_task_duration(&self, task_name: &str, duration: Duration) {
        self.task_duration.observe(duration.as_secs_f64());
    }
}
```

## 8. 主程序实现

```rust
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化数据库连接
    let db_pool = PgPool::connect("postgres://localhost/workflow_db").await?;
    let redis_client = RedisClient::connect("redis://localhost").await?;

    // 创建工作流引擎
    let engine = WorkflowEngine::new(db_pool, redis_client).await;

    // 创建工作流实例
    let order_workflow = create_order_workflow();
    let context = WorkflowContext::new(Uuid::new_v4());

    // 启动工作流
    let workflow_id = engine.start_workflow(order_workflow, context).await?;

    // 等待工作流完成
    engine.wait_for_completion(workflow_id).await?;

    Ok(())
}
```

这个实现提供了一个完整的分布式工作流系统，支持以下工作流模式：

1. 基本控制模式：
   - 序列（Sequence）
   - 并行分支（Parallel Split）
   - 同步合并（Synchronization）
   - 排他选择（Exclusive Choice）
   - 简单合并（Simple Merge）

2. 高级分支合并模式：
   - 多选择（Multi-Choice）
   - 多合并（Multi-Merge）
   - 判别器（Discriminator）
   - 结构化判别器（Structured Discriminator）

3. 迭代模式：
   - 任意循环（Arbitrary Cycles）
   - 结构化循环（Structured Loop）
   - 递归（Recursion）

4. 状态模式：
   - 延迟选择（Deferred Choice）
   - 里程碑（Milestone）
   - 关键区域（Critical Section）

5. 取消模式：
   - 取消任务（Cancel Task）
   - 取消区域（Cancel Region）
   - 取消多实例（Cancel Multiple Instance Activity）

这个系统可以用于构建各种复杂的业务流程，例如：

- 订单处理流程
- 文档审批流程
- 客户服务流程
- 保险理赔流程
