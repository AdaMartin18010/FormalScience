# 使用Rust的Hyperswitch实现高级支付处理系统

```text
让我分析一下这个需求，并规划如何使用Rust的Hyperswitch实现支付流系统。

Hyperswitch是一个开源的支付交换机/支付路由/支付网关系统，它允许商家连接多个支付处理商，提供统一的API接口，并且能够智能路由支付交易以获得更高的成功率和更低的成本。

基于用户的要求，我需要设计一个系统，该系统能够：
1. 跟踪所有支付路径和处理各种异常
2. 支持完整的支付生命周期操作
3. 支持分布式的对账、流水和会计分析

让我规划一下实现方案：
```

## 系统架构概览

```text
┌─────────────────────────────────────────────────────────────────────┐
│                       支付前端与商户接入层                           │
└──────────────────────────────────┬──────────────────────────────────┘
                                   │
┌──────────────────────────────────▼──────────────────────────────────┐
│                         API网关与认证服务                            │
└──────────────────────────────────┬──────────────────────────────────┘
                                   │
┌──────────────────────────────────▼──────────────────────────────────┐
│                       Hyperswitch核心服务层                         │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐ │
│  │ 支付处理服务 │  │ 支付路由服务 │  │ 支付跟踪服务 │  │ 风控服务    │ │
│  └─────────────┘  └─────────────┘  └─────────────┘  └─────────────┘ │
└──────────────────────────────────┬──────────────────────────────────┘
                                   │
┌──────────────────────────────────▼──────────────────────────────────┐
│                          财务与对账服务层                            │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐ │
│  │ 对账服务    │  │ 清算服务    │  │ 结算服务    │  │ 会计分析服务 │ │
│  └─────────────┘  └─────────────┘  └─────────────┘  └─────────────┘ │
└──────────────────────────────────┬──────────────────────────────────┘
                                   │
┌──────────────────────────────────▼──────────────────────────────────┐
│                           数据存储与消息层                           │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐ │
│  │ PostgreSQL  │  │ Redis缓存   │  │ Kafka消息队列│  │ ClickHouse  │ │
│  └─────────────┘  └─────────────┘  └─────────────┘  └─────────────┘ │
└─────────────────────────────────────────────────────────────────────┘
```

## 一、Hyperswitch支付核心系统实现

```rust
use axum::{
    routing::{get, post},
    Router, Extension, Json,
    extract::{Path, Query},
    response::{IntoResponse, Json as JsonResponse},
    http::StatusCode,
};
use chrono::{DateTime, Utc};
use hyperswitch_client::HyperSwitchClient;
use serde::{Deserialize, Serialize};
use sqlx::{postgres::PgPoolOptions, PgPool, Row};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::{RwLock, Mutex};
use tracing::{info, error, warn, instrument, Span};
use uuid::Uuid;

// 支付状态枚举
#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
enum PaymentStatus {
    Created,
    Authorized,
    Captured,
    Failed,
    Cancelled,
    Refunded,
    PartiallyRefunded,
    Processing,
    Declined,
    PendingVerification,
    Disputed,
    Chargebacked,
    Settled,
}

// 支付方法
#[derive(Debug, Clone, Serialize, Deserialize)]
enum PaymentMethod {
    Card {
        card_number: String,
        card_exp_month: String,
        card_exp_year: String,
        card_holder_name: String,
    },
    WalletRedirect {
        wallet_type: String,
        return_url: String,
    },
    BankTransfer {
        account_number: String,
        routing_number: String,
        bank_name: String,
    },
    Cryptocurrency {
        currency: String,
        wallet_address: String,
    },
}

// 支付请求模型
#[derive(Debug, Clone, Serialize, Deserialize)]
struct PaymentRequest {
    merchant_id: String,
    amount: u64,
    currency: String,
    payment_method: PaymentMethod,
    description: Option<String>,
    metadata: Option<HashMap<String, String>>,
    customer_id: Option<String>,
    return_url: Option<String>,
    preferred_connector: Option<String>,
}

// 支付响应模型
#[derive(Debug, Clone, Serialize, Deserialize)]
struct PaymentResponse {
    payment_id: Uuid,
    status: PaymentStatus,
    amount: u64,
    currency: String,
    connector_used: String,
    redirect_url: Option<String>,
    customer_id: Option<String>,
    created_at: DateTime<Utc>,
    updated_at: DateTime<Utc>,
    metadata: Option<HashMap<String, String>>,
}

// 支付路径跟踪
#[derive(Debug, Clone, Serialize, Deserialize)]
struct PaymentTrace {
    trace_id: Uuid,
    payment_id: Uuid,
    merchant_id: String,
    timestamp: DateTime<Utc>,
    status: PaymentStatus,
    connector: String,
    attempt_number: u32,
    error_message: Option<String>,
    error_code: Option<String>,
    duration_ms: u64,
    request_data: Option<serde_json::Value>,
    response_data: Option<serde_json::Value>,
}

// 异常处理记录
#[derive(Debug, Clone, Serialize, Deserialize)]
struct PaymentException {
    exception_id: Uuid,
    payment_id: Uuid,
    merchant_id: String,
    timestamp: DateTime<Utc>,
    exception_type: String,
    severity: String,
    description: String,
    resolution_status: String,
    resolution_details: Option<String>,
    retry_count: u32,
    resolution_timestamp: Option<DateTime<Utc>>,
}

// 支付核心服务
struct PaymentCoreService {
    hyperswitch_client: HyperSwitchClient,
    db_pool: PgPool,
    redis_client: redis::Client,
    exception_handlers: HashMap<String, Box<dyn ExceptionHandler>>,
}

// 异常处理特征
#[async_trait::async_trait]
trait ExceptionHandler: Send + Sync {
    async fn handle(&self, exception: &PaymentException) -> Result<PaymentStatus, Box<dyn std::error::Error>>;
}

// 网络异常处理器
struct NetworkExceptionHandler {
    max_retries: u32,
}

#[async_trait::async_trait]
impl ExceptionHandler for NetworkExceptionHandler {
    async fn handle(&self, exception: &PaymentException) -> Result<PaymentStatus, Box<dyn std::error::Error>> {
        if exception.retry_count < self.max_retries {
            // 获取原始支付信息并重试
            info!(
                payment_id = %exception.payment_id,
                retry = exception.retry_count + 1,
                "正在重试因网络异常失败的支付"
            );
            
            // 这里应该包含重试逻辑
            // ...
            
            Ok(PaymentStatus::Processing)
        } else {
            warn!(
                payment_id = %exception.payment_id,
                retries = exception.retry_count,
                "支付网络异常重试次数已达上限"
            );
            Ok(PaymentStatus::Failed)
        }
    }
}

impl PaymentCoreService {
    async fn new(
        hyperswitch_api_key: &str,
        hyperswitch_url: &str,
        database_url: &str,
        redis_url: &str,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        // 初始化Hyperswitch客户端
        let hyperswitch_client = HyperSwitchClient::new(
            hyperswitch_api_key, 
            hyperswitch_url
        );
        
        // 初始化数据库连接池
        let db_pool = PgPoolOptions::new()
            .max_connections(20)
            .connect(database_url)
            .await?;
            
        // 初始化Redis客户端
        let redis_client = redis::Client::open(redis_url)?;
        
        // 初始化异常处理器
        let mut exception_handlers: HashMap<String, Box<dyn ExceptionHandler>> = HashMap::new();
        exception_handlers.insert(
            "network".to_string(), 
            Box::new(NetworkExceptionHandler { max_retries: 3 })
        );
        
        // 更多异常处理器...
        
        Ok(Self {
            hyperswitch_client,
            db_pool,
            redis_client,
            exception_handlers,
        })
    }
    
    // 创建新支付
    #[instrument(skip(self), fields(merchant_id = %request.merchant_id))]
    async fn create_payment(&self, request: PaymentRequest) -> Result<PaymentResponse, Box<dyn std::error::Error>> {
        let span = Span::current();
        let payment_id = Uuid::new_v4();
        span.record("payment_id", payment_id.to_string());
        
        info!("创建新支付流程");
        
        // 1. 请求参数验证
        // ...
        
        // 2. 风控检查
        // ...
        
        // 3. 转换为Hyperswitch格式的请求
        let hyperswitch_request = self.convert_to_hyperswitch_request(request.clone(), payment_id)?;
        
        // 4. 跟踪开始
        let trace_id = Uuid::new_v4();
        self.create_trace(PaymentTrace {
            trace_id,
            payment_id,
            merchant_id: request.merchant_id.clone(),
            timestamp: Utc::now(),
            status: PaymentStatus::Created,
            connector: "pending".to_string(),
            attempt_number: 1,
            error_message: None,
            error_code: None,
            duration_ms: 0,
            request_data: Some(serde_json::to_value(&hyperswitch_request)?),
            response_data: None,
        }).await?;
        
        // 5. 调用Hyperswitch创建支付
        let start_time = std::time::Instant::now();
        let hyperswitch_response = match self.hyperswitch_client.create_payment(hyperswitch_request).await {
            Ok(response) => response,
            Err(e) => {
                // 记录异常并启动异常处理流程
                let exception = PaymentException {
                    exception_id: Uuid::new_v4(),
                    payment_id,
                    merchant_id: request.merchant_id,
                    timestamp: Utc::now(),
                    exception_type: "network".to_string(),
                    severity: "high".to_string(),
                    description: format!("创建支付失败: {}", e),
                    resolution_status: "pending".to_string(),
                    resolution_details: None,
                    retry_count: 0,
                    resolution_timestamp: None,
                };
                
                self.record_exception(&exception).await?;
                self.handle_exception(&exception).await?;
                
                return Err(format!("支付创建失败: {}", e).into());
            }
        };
        
        let duration_ms = start_time.elapsed().as_millis() as u64;
        
        // 6. 更新跟踪
        self.update_trace(PaymentTrace {
            trace_id,
            payment_id,
            merchant_id: request.merchant_id.clone(),
            timestamp: Utc::now(),
            status: self.convert_hyperswitch_status(&hyperswitch_response.status),
            connector: hyperswitch_response.connector.clone(),
            attempt_number: 1,
            error_message: None,
            error_code: None,
            duration_ms,
            request_data: Some(serde_json::to_value(&hyperswitch_request)?),
            response_data: Some(serde_json::to_value(&hyperswitch_response)?),
        }).await?;
        
        // 7. 保存支付记录
        // ...
        
        // 8. 构建响应
        let payment_response = PaymentResponse {
            payment_id,
            status: self.convert_hyperswitch_status(&hyperswitch_response.status),
            amount: request.amount,
            currency: request.currency,
            connector_used: hyperswitch_response.connector,
            redirect_url: hyperswitch_response.redirect_url,
            customer_id: request.customer_id,
            created_at: Utc::now(),
            updated_at: Utc::now(),
            metadata: request.metadata,
        };
        
        Ok(payment_response)
    }
    
    // 记录跟踪数据
    async fn create_trace(&self, trace: PaymentTrace) -> Result<(), Box<dyn std::error::Error>> {
        sqlx::query(
            r#"
            INSERT INTO payment_traces (
                trace_id, payment_id, merchant_id, timestamp, status, 
                connector, attempt_number, error_message, error_code, 
                duration_ms, request_data, response_data
            )
            VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11, $12)
            "#
        )
        .bind(trace.trace_id)
        .bind(trace.payment_id)
        .bind(&trace.merchant_id)
        .bind(trace.timestamp)
        .bind(trace.status as i32)
        .bind(&trace.connector)
        .bind(trace.attempt_number)
        .bind(&trace.error_message)
        .bind(&trace.error_code)
        .bind(trace.duration_ms)
        .bind(&trace.request_data)
        .bind(&trace.response_data)
        .execute(&self.db_pool)
        .await?;
        
        Ok(())
    }
    
    // 更新跟踪数据
    async fn update_trace(&self, trace: PaymentTrace) -> Result<(), Box<dyn std::error::Error>> {
        // 更新跟踪记录
        // ...
        Ok(())
    }
    
    // 记录异常
    async fn record_exception(&self, exception: &PaymentException) -> Result<(), Box<dyn std::error::Error>> {
        // 记录异常到数据库
        // ...
        Ok(())
    }
    
    // 处理异常
    async fn handle_exception(&self, exception: &PaymentException) -> Result<PaymentStatus, Box<dyn std::error::Error>> {
        if let Some(handler) = self.exception_handlers.get(&exception.exception_type) {
            handler.handle(exception).await
        } else {
            warn!(
                payment_id = %exception.payment_id,
                exception_type = %exception.exception_type,
                "没有找到对应的异常处理器"
            );
            Ok(PaymentStatus::Failed)
        }
    }
    
    // 转换为Hyperswitch请求
    fn convert_to_hyperswitch_request(&self, request: PaymentRequest, payment_id: Uuid) -> Result<serde_json::Value, Box<dyn std::error::Error>> {
        // 根据不同的支付方法构建不同的请求
        // ...
        
        // 示例转换代码
        let hyperswitch_request = match request.payment_method {
            PaymentMethod::Card { card_number, card_exp_month, card_exp_year, card_holder_name } => {
                serde_json::json!({
                    "amount": request.amount,
                    "currency": request.currency,
                    "confirm": true,
                    "capture_method": "automatic",
                    "merchant_id": request.merchant_id,
                    "payment_id": payment_id.to_string(),
                    "description": request.description,
                    "metadata": request.metadata,
                    "customer_id": request.customer_id,
                    "return_url": request.return_url,
                    "payment_method": "card",
                    "payment_method_data": {
                        "card": {
                            "card_number": card_number,
                            "card_exp_month": card_exp_month,
                            "card_exp_year": card_exp_year,
                            "card_holder_name": card_holder_name
                        }
                    },
                    "connector": request.preferred_connector
                })
            },
            // 其他支付方法的处理
            _ => {
                // ...
                serde_json::json!({})
            }
        };
        
        Ok(hyperswitch_request)
    }
    
    // 转换Hyperswitch状态为内部状态
    fn convert_hyperswitch_status(&self, status: &str) -> PaymentStatus {
        match status {
            "succeeded" => PaymentStatus::Captured,
            "processing" => PaymentStatus::Processing,
            "requires_payment_method" => PaymentStatus::Created,
            "requires_confirmation" => PaymentStatus::Created,
            "requires_action" => PaymentStatus::PendingVerification,
            "cancelled" => PaymentStatus::Cancelled,
            "failed" => PaymentStatus::Failed,
            _ => PaymentStatus::Processing,
        }
    }
}
```

## 二、支付撤销、对冲、对账和清算系统

```rust
use chrono::{DateTime, Utc, Duration, NaiveDate};
use rust_decimal::Decimal;
use serde::{Deserialize, Serialize};
use sqlx::{postgres::PgPoolOptions, PgPool, Row};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use tokio::sync::{RwLock, Mutex};
use tracing::{info, error, warn, instrument};
use uuid::Uuid;

// 对账项
#[derive(Debug, Clone, Serialize, Deserialize)]
struct ReconciliationItem {
    payment_id: Uuid,
    merchant_id: String,
    connector: String,
    connector_payment_id: String,
    amount: Decimal,
    currency: String,
    status: PaymentStatus,
    transaction_date: DateTime<Utc>,
    transaction_type: String,
    fees: Decimal,
    system_recorded_status: PaymentStatus,
    is_reconciled: bool,
    discrepancy_reason: Option<String>,
    reconciliation_date: Option<DateTime<Utc>>,
}

// 对账批次
#[derive(Debug, Clone, Serialize, Deserialize)]
struct ReconciliationBatch {
    batch_id: Uuid,
    merchant_id: String,
    connector: String,
    start_date: DateTime<Utc>,
    end_date: DateTime<Utc>,
    status: String,
    total_transactions: i32,
    matched_transactions: i32,
    unmatched_transactions: i32,
    missing_transactions: i32,
    extra_transactions: i32,
    total_amount: Decimal,
    discrepancy_amount: Decimal,
    created_at: DateTime<Utc>,
    completed_at: Option<DateTime<Utc>>,
}

// 清算记录
#[derive(Debug, Clone, Serialize, Deserialize)]
struct SettlementRecord {
    settlement_id: Uuid,
    merchant_id: String,
    connector: String,
    settlement_date: DateTime<Utc>,
    amount: Decimal,
    currency: String,
    fees: Decimal,
    net_amount: Decimal,
    status: String,
    settlement_reference: String,
    payment_ids: Vec<Uuid>,
    created_at: DateTime<Utc>,
    updated_at: DateTime<Utc>,
}

// 会计分录
#[derive(Debug, Clone, Serialize, Deserialize)]
struct AccountingEntry {
    entry_id: Uuid,
    transaction_id: Uuid,
    account_code: String,
    account_name: String,
    debit_amount: Decimal,
    credit_amount: Decimal,
    transaction_date: DateTime<Utc>,
    entry_type: String,
    description: String,
    reference: String,
    created_at: DateTime<Utc>,
}

// 财务服务
struct FinancialService {
    db_pool: PgPool,
    payment_service: Arc<PaymentCoreService>,
    reconciliation_rules: HashMap<String, Box<dyn ReconciliationRule>>,
}

// 对账规则特征
#[async_trait::async_trait]
trait ReconciliationRule: Send + Sync {
    async fn reconcile(
        &self, 
        system_records: &[ReconciliationItem], 
        connector_records: &[ReconciliationItem]
    ) -> Result<Vec<ReconciliationItem>, Box<dyn std::error::Error>>;
}

impl FinancialService {
    async fn new(
        database_url: &str,
        payment_service: Arc<PaymentCoreService>,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        // 初始化数据库连接池
        let db_pool = PgPoolOptions::new()
            .max_connections(20)
            .connect(database_url)
            .await?;
            
        // 初始化对账规则
        let mut reconciliation_rules: HashMap<String, Box<dyn ReconciliationRule>> = HashMap::new();
        
        Ok(Self {
            db_pool,
            payment_service,
            reconciliation_rules,
        })
    }
    
    // 撤销支付
    #[instrument(skip(self), fields(payment_id = %payment_id))]
    async fn cancel_payment(&self, payment_id: Uuid, reason: &str) -> Result<PaymentStatus, Box<dyn std::error::Error>> {
        info!("开始撤销支付流程");
        
        // 1. 检查支付状态是否可撤销
        let payment = self.get_payment(payment_id).await?;
        
        if payment.status != PaymentStatus::Authorized && 
           payment.status != PaymentStatus::Processing && 
           payment.status != PaymentStatus::Created {
            return Err(format!("支付状态为 {:?}, 不可撤销", payment.status).into());
        }
        
        // 2. 调用Hyperswitch撤销接口
        let trace_id = Uuid::new_v4();
        let start_time = std::time::Instant::now();
        
        let result = match self.payment_service.hyperswitch_client.cancel_payment(&payment_id.to_string()).await {
            Ok(response) => {
                // 记录成功的撤销操作
                info!(payment_id = %payment_id, "支付撤销成功");
                
                // 更新支付状态
                let status = self.payment_service.convert_hyperswitch_status(&response.status);
                
                // 创建会计分录
                self.create_accounting_entries(
                    payment_id, 
                    "payment_cancel", 
                    payment.amount, 
                    &payment.currency, 
                    &format!("支付撤销: {}", reason)
                ).await?;
                
                status
            },
            Err(e) => {
                // 记录撤销失败异常
                let exception = PaymentException {
                    exception_id: Uuid::new_v4(),
                    payment_id,
                    merchant_id: payment.customer_id.unwrap_or_default(),
                    timestamp: Utc::now(),
                    exception_type: "cancel_error".to_string(),
                    severity: "high".to_string(),
                    description: format!("支付撤销失败: {}", e),
                    resolution_status: "pending".to_string(),
                    resolution_details: None,
                    retry_count: 0,
                    resolution_timestamp: None,
                };
                
                self.payment_service.record_exception(&exception).await?;
                
                return Err(format!("支付撤销失败: {}", e).into());
            }
        };
        
        let duration_ms = start_time.elapsed().as_millis() as u64;
        
        // 3. 记录撤销轨迹
        self.payment_service.create_trace(PaymentTrace {
            trace_id,
            payment_id,
            merchant_id: payment.customer_id.unwrap_or_default(),
            timestamp: Utc::now(),
            status: result,
            connector: payment.connector_used,
            attempt_number: 1,
            error_message: None,
            error_code: None,
            duration_ms,
            request_data: Some(serde_json::json!({
                "reason": reason
            })),
            response_data: Some(serde_json::json!({
                "status": format!("{:?}", result)
            })),
        }).await?;
        
        Ok(result)
    }
    
    // 支付退款
    #[instrument(skip(self), fields(payment_id = %payment_id))]
    async fn refund_payment(
        &self, 
        payment_id: Uuid, 
        amount: Option<u64>, 
        reason: &str
    ) -> Result<Uuid, Box<dyn std::error::Error>> {
        info!("开始退款流程");
        
        // 1. 检查支付状态是否可退款
        let payment = self.get_payment(payment_id).await?;
        
        if payment.status != PaymentStatus::Captured && 
           payment.status != PaymentStatus::Settled {
            return Err(format!("支付状态为 {:?}, 不可退款", payment.status).into());
        }
        
        // 2. 确定退款金额
        let refund_amount = amount.unwrap_or(payment.amount);
        
        // 3. 调用Hyperswitch退款接口
        let refund_id = Uuid::new_v4();
        let trace_id = Uuid::new_v4();
        let start_time = std::time::Instant::now();
        
        let result = match self.payment_service.hyperswitch_client.refund_payment(
            &payment_id.to_string(),
            &refund_id.to_string(),
            refund_amount,
            reason
        ).await {
            Ok(response) => {
                // 记录成功的退款操作
                info!(
                    payment_id = %payment_id, 
                    refund_id = %refund_id, 
                    amount = refund_amount, 
                    "支付退款成功"
                );
                
                // 创建会计分录
                self.create_accounting_entries(
                    payment_id, 
                    "payment_refund", 
                    Decimal::from(refund_amount), 
                    &payment.currency, 
                    &format!("支付退款: {}", reason)
                ).await?;
                
                refund_id
            },
            Err(e) => {
                // 记录退款失败异常
                let exception = PaymentException {
                    exception_id: Uuid::new_v4(),
                    payment_id,
                    merchant_id: payment.customer_id.unwrap_or_default(),
                    timestamp: Utc::now(),
                    exception_type: "refund_error".to_string(),
                    severity: "high".to_string(),
                    description: format!("支付退款失败: {}", e),
                    resolution_status: "pending".to_string(),
                    resolution_details: None,
                    retry_count: 0,
                    resolution_timestamp: None,
                };
                
                self.payment_service.record_exception(&exception).await?;
                
                return Err(format!("支付退款失败: {}", e).into());
            }
        };
        
        let duration_ms = start_time.elapsed().as_millis() as u64;
        
        // 4. 记录退款轨迹
        self.payment_service.create_trace(PaymentTrace {
            trace_id,
            payment_id,
            merchant_id: payment.customer_id.unwrap_or_default(),
            timestamp: Utc::now(),
            status: if refund_amount == payment.amount { 
                PaymentStatus::Refunded 
            } else { 
                PaymentStatus::PartiallyRefunded 
            },
            connector: payment.connector_used,
            attempt_number: 1,
            error_message: None,
            error_code: None,
            duration_ms,
            request_data: Some(serde_json::json!({
                "refund_id": refund_id.to_string(),
                "amount": refund_amount,
                "reason": reason
            })),
            response_data: Some(serde_json::json!({
                "refund_id": refund_id.to_string()
            })),
        }).await?;
        
        Ok(result)
    }
    
    // 执行对账
    #[instrument(skip(self), fields(merchant_id = %merchant_id, connector = %connector))]
    async fn reconcile_payments(
        &self,
        merchant_id: &str,
        connector: &str,
        start_date: DateTime<Utc>,
        end_date: DateTime<Utc>,
    ) -> Result<ReconciliationBatch, Box<dyn std::error::Error>> {
        info!("开始对账流程");
        
        // 1. 创建对账批次
        let batch_id = Uuid::new_v4();
        
        let batch = ReconciliationBatch {
            batch_id,
            merchant_id: merchant_id.to_string(),
            connector: connector.to_string(),
            start_date,
            end_date,
            status: "processing".to_string(),
            total_transactions: 0,
            matched_transactions: 0,
            unmatched_transactions: 0,
            missing_transactions: 0,
            extra_transactions: 0,
            total_amount: Decimal::new(0, 0),
            discrepancy_amount: Decimal::new(0, 0),
            created_at: Utc::now(),
            completed_at: None,
        };
        
        // 保存批次信息
        // ...
        
        // 2. 获取系统记录
        let system_records = self.get_system_records(merchant_id, connector, start_date, end_date).await?;
        
        // 3. 获取渠道记录（通常是从渠道下载报表或API获取）
        let connector_records = self.fetch_connector_records(connector, merchant_id, start_date, end_date).await?;
        
        // 4. 执行对账
        let rule = self.reconciliation_rules.get(connector).ok_or_else(|| {
            format!("没有找到渠道 {} 的对账规则", connector)
        })?;
        
        let reconciled_items = rule.reconcile(&system_records, &connector_records).await?;
        
        // 5. 处理对账结果
        let mut matched_count = 0;
        let mut unmatched_count = 0;
        let mut discrepancy_amount = Decimal::new(0, 0);
        
        for item in &reconciled_items {
            if item.is_reconciled {
                matched_count += 1;
            } else {
                unmatched_count += 1;
                // 计算差异金额
                let status_discrepancy = item.status != item.system_recorded_status;
                if status_discrepancy {
                    discrepancy_amount += item.amount;
                }
            }
            
            // 保存对账项
            // ...
        }
        
        // 6. 系统中有但渠道没有的记录
        let system_payment_ids: HashSet<_> = system_records.iter()
            .map(|item| item.payment_id)
            .collect();
            
        let connector_payment_ids: HashSet<_> = connector_records.iter()
            .map(|item| item.payment_id)
            .collect();
            
        let missing_transactions = system_payment_ids.difference(&connector_payment_ids).count() as i32;
        let extra_transactions = connector_payment_ids.difference(&system_payment_ids).count() as i32;
        
        // 7. 更新对账批次结果
        let updated_batch = ReconciliationBatch {
            batch_id,
            merchant_id: merchant_id.to_string(),
            connector: connector.to_string(),
            start_date,
            end_date,
            status: "completed".to_string(),
            total_transactions: (system_records.len() + connector_records.len()) as i32,
            matched_transactions: matched_count,
            unmatched_transactions: unmatched_count,
            missing_transactions,
            extra_transactions,
            total_amount: system_records.iter().map(|r| r.amount).sum(),
            discrepancy_amount,
            created_at: batch.created_at,
            completed_at: Some(Utc::now()),
        };
        
        // 保存更新后的批次信息
        // ...
        
        info!(
            batch_id = %batch_id,
            matched = matched_count,
            unmatched = unmatched_count,
            missing = missing_transactions,
            extra = extra_transactions,
            "对账完成"
        );
        
        Ok(updated_batch)
    }
    
    // 生成清算记录
    #[instrument(skip(self), fields(merchant_id = %merchant_id, connector = %connector))]
    async fn generate_settlement(
        &self,
        merchant_id: &str,
        connector: &str,
        settlement_date: DateTime<Utc>,
    ) -> Result<SettlementRecord, Box<dyn std::error::Error>> {
        info!("开始生成清算记录");
        
        // 1. 查询需要清算的交易
        let day_start = settlement_date.date().and_hms_opt(0, 0, 0).unwrap();
        let day_end = settlement_date.date().and_hms_opt(23, 59, 59).unwrap();
        
        let transactions = sqlx::query!(
            r#"
            SELECT 
                payment_id, amount, currency, status, fees
            FROM 
                payments
            WHERE 
                merchant_id = $1 AND
                connector = $2 AND
                created_at BETWEEN $3 AND $4 AND
                status = 'captured' AND
                settlement_id IS NULL
            "#,
            merchant_id,
            connector,
            day_start,
            day_end
        )
        .fetch_all(&self.db_pool)
        .await?;
        
        if transactions.is_empty() {
            return Err("没有找到需要清算的交易".into());
        }
        
        // 2. 计算总金额和手续费
        let mut total_amount = Decimal::new(0, 0);
        let mut total_fees = Decimal::new(0, 0);
        let mut payment_ids = Vec::new();
        let mut currencies = HashSet::new();
        
        for transaction in &transactions {
            total_amount += transaction.amount;
            total_fees += transaction.fees.unwrap_or(Decimal::new(0, 0));
            payment_ids.push(Uuid::parse_str(&transaction.payment_id).unwrap());
            currencies.insert(transaction.currency.clone());
        }
        
        // 确保所有交易都是同一种货币
        if currencies.len() != 1 {
            return Err("清算批次中存在多种货币，无法清算".into());
        }
        let currency = currencies.into_iter().next().unwrap();
        
        // 3. 创建清算记录
        let settlement_id = Uuid::new_v4();
        let settlement_reference = format!("SET-{}-{}", settlement_date.format("%Y%m%d"), merchant_id);
        
        let settlement = SettlementRecord {
            settlement_id,
            merchant_id: merchant_id.to_string(),
            connector: connector.to_string(),
            settlement_date,
            amount: total_amount,
            currency,
//我需要继续编写关于使用Rust的Hyperswitch实现支付流和支付渠道的代码。
//上次我正在编写FinancialService的generate_settlement方法，
//并且在计算结算记录的费用时中断了。
//让我继续完成该方法，然后添加更多关于会计分析和支付对账的功能。

            fees: total_fees,
            net_amount: total_amount - total_fees,
            status: "pending".to_string(),
            settlement_reference,
            payment_ids,
            created_at: Utc::now(),
            updated_at: Utc::now(),
        };
        
        // 4. 保存结算记录到数据库
        sqlx::query!(
            r#"
            INSERT INTO settlements (
                settlement_id, merchant_id, connector, settlement_date, amount, currency, 
                fees, net_amount, status, settlement_reference, created_at, updated_at
            ) VALUES (
                $1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11, $12
            )
            "#,
            settlement.settlement_id,
            settlement.merchant_id,
            settlement.connector,
            settlement.settlement_date,
            settlement.amount,
            settlement.currency,
            settlement.fees,
            settlement.net_amount,
            settlement.status,
            settlement.settlement_reference,
            settlement.created_at,
            settlement.updated_at
        )
        .execute(&self.db_pool)
        .await?;
        
        // 5. 更新支付记录的结算ID
        for payment_id in &settlement.payment_ids {
            sqlx::query!(
                r#"
                UPDATE payments 
                SET settlement_id = $1, updated_at = $2
                WHERE payment_id = $3
                "#,
                settlement.settlement_id,
                Utc::now(),
                payment_id
            )
            .execute(&self.db_pool)
            .await?;
        }
        
        // 6. 生成会计分录
        self.generate_accounting_entries(&settlement).await?;
        
        info!(
            settlement_id = %settlement.settlement_id,
            amount = %settlement.amount,
            fees = %settlement.fees,
            net_amount = %settlement.net_amount,
            "清算记录已生成"
        );
        
        Ok(settlement)
    }
    
    // 处理支付对冲
    #[instrument(skip(self), fields(payment_id = %payment_id))]
    async fn process_payment_reversal(
        &self,
        payment_id: Uuid,
        amount: Option<Decimal>,
        reason: &str
    ) -> Result<PaymentReversal, Box<dyn std::error::Error>> {
        info!("开始处理支付对冲");
        
        // 1. 获取原始支付信息
        let payment = self.payment_service.get_payment(payment_id).await?;
        
        if payment.status != PaymentStatus::Captured {
            return Err(format!("支付状态 {:?} 不允许对冲操作", payment.status).into());
        }
        
        // 2. 确定对冲金额
        let reversal_amount = amount.unwrap_or(payment.amount);
        if reversal_amount > payment.amount {
            return Err("对冲金额不能大于原始支付金额".into());
        }
        
        // 3. 创建对冲记录
        let reversal_id = Uuid::new_v4();
        let reversal = PaymentReversal {
            reversal_id,
            payment_id,
            amount: reversal_amount,
            currency: payment.currency.clone(),
            status: ReversalStatus::Pending,
            reason: reason.to_string(),
            reversal_reference: format!("REV-{}", reversal_id.to_string().split('-').next().unwrap()),
            created_at: Utc::now(),
            updated_at: Utc::now(),
            metadata: HashMap::new(),
        };
        
        // 4. 调用Hyperswitch API执行对冲
        let hyperswitch_request = serde_json::json!({
            "payment_id": payment_id.to_string(),
            "amount": reversal_amount,
            "reason": reason
        });
        
        let hyperswitch_response = self.payment_service
            .hyperswitch_client
            .reverse_payment(&payment.connector_used, &hyperswitch_request)
            .await?;
        
        // 5. 更新对冲状态
        let status = match hyperswitch_response["status"].as_str() {
            Some("succeeded") => ReversalStatus::Completed,
            Some("failed") => ReversalStatus::Failed,
            _ => ReversalStatus::Processing,
        };
        
        let updated_reversal = PaymentReversal {
            status,
            updated_at: Utc::now(),
            metadata: {
                let mut map = HashMap::new();
                map.insert("hyperswitch_response".to_string(), hyperswitch_response.to_string());
                map
            },
            ..reversal
        };
        
        // 6. 保存对冲记录
        sqlx::query!(
            r#"
            INSERT INTO payment_reversals (
                reversal_id, payment_id, amount, currency, status, reason, 
                reversal_reference, created_at, updated_at, metadata
            ) VALUES (
                $1, $2, $3, $4, $5, $6, $7, $8, $9, $10
            )
            "#,
            updated_reversal.reversal_id,
            updated_reversal.payment_id,
            updated_reversal.amount,
            updated_reversal.currency,
            updated_reversal.status as i32,
            updated_reversal.reason,
            updated_reversal.reversal_reference,
            updated_reversal.created_at,
            updated_reversal.updated_at,
            serde_json::to_value(&updated_reversal.metadata).unwrap()
        )
        .execute(&self.db_pool)
        .await?;
        
        // 7. 如果对冲成功，更新支付状态
        if status == ReversalStatus::Completed {
            if reversal_amount == payment.amount {
                // 完全对冲
                self.payment_service.update_payment_status(payment_id, PaymentStatus::Cancelled).await?;
            } else {
                // 部分对冲 - 可能需要更复杂的状态处理
                // 这里简化处理，实际系统中可能需要更精细的状态管理
                self.payment_service.update_payment_status(payment_id, PaymentStatus::PartiallyRefunded).await?;
            }
            
            // 8. 生成对冲的会计分录
            self.generate_reversal_accounting_entries(&updated_reversal, &payment).await?;
        }
        
        info!(
            reversal_id = %updated_reversal.reversal_id,
            status = ?updated_reversal.status,
            amount = %updated_reversal.amount,
            "支付对冲处理完成"
        );
        
        Ok(updated_reversal)
    }
    
    // 生成会计分录
    async fn generate_accounting_entries(
        &self,
        settlement: &SettlementRecord
    ) -> Result<Vec<AccountingEntry>, Box<dyn std::error::Error>> {
        info!(
            settlement_id = %settlement.settlement_id,
            "生成会计分录"
        );
        
        let now = Utc::now();
        let mut entries = Vec::new();
        
        // 1. 收入记账 - 借记商户应收账款
        let receivable_entry = AccountingEntry {
            entry_id: Uuid::new_v4(),
            transaction_id: settlement.settlement_id,
            account_code: "1100".to_string(),  // 应收账款
            account_name: "Merchant Receivables".to_string(),
            debit_amount: settlement.amount,
            credit_amount: Decimal::new(0, 0),
            transaction_date: settlement.settlement_date,
            entry_type: "settlement".to_string(),
            description: format!("Settlement receivable for merchant {}", settlement.merchant_id),
            reference: settlement.settlement_reference.clone(),
            created_at: now,
        };
        entries.push(receivable_entry);
        
        // 2. 收入记账 - 贷记收入账户
        let revenue_entry = AccountingEntry {
            entry_id: Uuid::new_v4(),
            transaction_id: settlement.settlement_id,
            account_code: "4000".to_string(),  // 收入
            account_name: "Processing Revenue".to_string(),
            debit_amount: Decimal::new(0, 0),
            credit_amount: settlement.amount,
            transaction_date: settlement.settlement_date,
            entry_type: "settlement".to_string(),
            description: format!("Settlement revenue for merchant {}", settlement.merchant_id),
            reference: settlement.settlement_reference.clone(),
            created_at: now,
        };
        entries.push(revenue_entry);
        
        // 3. 费用记账 - 借记费用
        if settlement.fees > Decimal::new(0, 0) {
            let fee_expense_entry = AccountingEntry {
                entry_id: Uuid::new_v4(),
                transaction_id: settlement.settlement_id,
                account_code: "5000".to_string(),  // 费用
                account_name: "Processing Fees".to_string(),
                debit_amount: settlement.fees,
                credit_amount: Decimal::new(0, 0),
                transaction_date: settlement.settlement_date,
                entry_type: "settlement_fee".to_string(),
                description: format!("Processing fees for settlement {}", settlement.settlement_id),
                reference: settlement.settlement_reference.clone(),
                created_at: now,
            };
            entries.push(fee_expense_entry);
            
            // 4. 费用记账 - 贷记应付账款
            let fee_payable_entry = AccountingEntry {
                entry_id: Uuid::new_v4(),
                transaction_id: settlement.settlement_id,
                account_code: "2000".to_string(),  // 应付账款
                account_name: "Processor Payables".to_string(),
                debit_amount: Decimal::new(0, 0),
                credit_amount: settlement.fees,
                transaction_date: settlement.settlement_date,
                entry_type: "settlement_fee".to_string(),
                description: format!("Processing fees payable for settlement {}", settlement.settlement_id),
                reference: settlement.settlement_reference.clone(),
                created_at: now,
            };
            entries.push(fee_payable_entry);
        }
        
        // 5. 将分录保存到数据库
        for entry in &entries {
            sqlx::query!(
                r#"
                INSERT INTO accounting_entries (
                    entry_id, transaction_id, account_code, account_name, debit_amount, 
                    credit_amount, transaction_date, entry_type, description, reference, created_at
                ) VALUES (
                    $1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11
                )
                "#,
                entry.entry_id,
                entry.transaction_id,
                entry.account_code,
                entry.account_name,
                entry.debit_amount,
                entry.credit_amount,
                entry.transaction_date,
                entry.entry_type,
                entry.description,
                entry.reference,
                entry.created_at
            )
            .execute(&self.db_pool)
            .await?;
        }
        
        Ok(entries)
    }
    
    // 生成对冲的会计分录
    async fn generate_reversal_accounting_entries(
        &self,
        reversal: &PaymentReversal,
        original_payment: &PaymentResponse
    ) -> Result<Vec<AccountingEntry>, Box<dyn std::error::Error>> {
        let now = Utc::now();
        let mut entries = Vec::new();
        
        // 1. 对冲借记 - 贷记应收账款(冲销原始交易)
        let receivable_entry = AccountingEntry {
            entry_id: Uuid::new_v4(),
            transaction_id: reversal.reversal_id,
            account_code: "1100".to_string(),  // 应收账款
            account_name: "Merchant Receivables".to_string(),
            debit_amount: Decimal::new(0, 0),
            credit_amount: reversal.amount,
            transaction_date: now.date().and_hms_opt(0, 0, 0).unwrap(),
            entry_type: "reversal".to_string(),
            description: format!("Reversal for payment {}", reversal.payment_id),
            reference: reversal.reversal_reference.clone(),
            created_at: now,
        };
        entries.push(receivable_entry);
        
        // 2. 对冲贷记 - 借记收入(冲销收入)
        let revenue_entry = AccountingEntry {
            entry_id: Uuid::new_v4(),
            transaction_id: reversal.reversal_id,
            account_code: "4000".to_string(),  // 收入
            account_name: "Processing Revenue".to_string(),
            debit_amount: reversal.amount,
            credit_amount: Decimal::new(0, 0),
            transaction_date: now.date().and_hms_opt(0, 0, 0).unwrap(),
            entry_type: "reversal".to_string(),
            description: format!("Revenue reversal for payment {}", reversal.payment_id),
            reference: reversal.reversal_reference.clone(),
            created_at: now,
        };
        entries.push(revenue_entry);
        
        // 3. 保存分录到数据库
        for entry in &entries {
            sqlx::query!(
                r#"
                INSERT INTO accounting_entries (
                    entry_id, transaction_id, account_code, account_name, debit_amount, 
                    credit_amount, transaction_date, entry_type, description, reference, created_at
                ) VALUES (
                    $1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11
                )
                "#,
                entry.entry_id,
                entry.transaction_id,
                entry.account_code,
                entry.account_name,
                entry.debit_amount,
                entry.credit_amount,
                entry.transaction_date,
                entry.entry_type,
                entry.description,
                entry.reference,
                entry.created_at
            )
            .execute(&self.db_pool)
            .await?;
        }
        
        Ok(entries)
    }
}
```

## 三、分布式、分层对账与会计分析系统

```rust
use chrono::{DateTime, Utc, Duration, NaiveDate};
use rust_decimal::Decimal;
use serde::{Deserialize, Serialize};
use sqlx::{postgres::PgPoolOptions, PgPool, Row};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use tokio::sync::{RwLock, Mutex};
use tracing::{info, error, warn, instrument};
use uuid::Uuid;

// 分布式对账配置
#[derive(Debug, Clone, Serialize, Deserialize)]
struct ReconciliationConfig {
    layer: String,  // "merchant", "processor", "bank"
    schedule: String,  // "daily", "weekly", "monthly"
    start_time: String,  // "01:00"
    timeout_minutes: i32,
    retry_count: i32,
    notify_on_discrepancy: bool,
    auto_resolve_threshold: Decimal,  // 自动解决的金额阈值
    reconciliation_rules: Vec<String>,  // 应用哪些规则
}

// 对账节点
#[derive(Debug, Clone, Serialize, Deserialize)]
struct ReconciliationNode {
    node_id: Uuid,
    node_name: String,
    node_type: String,  // "merchant", "processor", "bank"
    config: ReconciliationConfig,
    active: bool,
    last_run: Option<DateTime<Utc>>,
    next_run: Option<DateTime<Utc>>,
}

// 会计科目
#[derive(Debug, Clone, Serialize, Deserialize)]
struct AccountingCategory {
    category_id: String,
    name: String,
    parent_id: Option<String>,
    category_type: String,  // "asset", "liability", "equity", "revenue", "expense"
    description: String,
    is_active: bool,
}

// 利润中心
#[derive(Debug, Clone, Serialize, Deserialize)]
struct ProfitCenter {
    center_id: String,
    name: String,
    description: String,
    parent_id: Option<String>,
    is_active: bool,
}

// 预算项
#[derive(Debug, Clone, Serialize, Deserialize)]
struct BudgetItem {
    budget_id: Uuid,
    profit_center_id: String,
    account_category_id: String,
    fiscal_year: i32,
    fiscal_month: i32,
    amount: Decimal,
    actual_amount: Option<Decimal>,
    variance_amount: Option<Decimal>,
    variance_percentage: Option<Decimal>,
    created_at: DateTime<Utc>,
    updated_at: DateTime<Utc>,
}

// 分销商分配
#[derive(Debug, Clone, Serialize, Deserialize)]
struct DistributorAllocation {
    allocation_id: Uuid,
    payment_id: Uuid,
    distributor_id: String,
    merchant_id: String,
    amount: Decimal,
    currency: String,
    commission_rate: Decimal,
    commission_amount: Decimal,
...(about 246 lines omitted)...
        let budget_vs_actual = self.get_budget_vs_actual(
            profit_center_id, 
            account_category_ids, 
            fiscal_year, 
            Some(fiscal_month)
        ).await?;
        
        // 2. 计算各指标
        for item in &budget_vs_actual {
            // 计算差异金额
            if let (Some(budget), Some(actual)) = (item.budget_amount, item.actual_amount) {
                let variance = actual - budget;
                let variance_percentage = if budget != Decimal::new(0, 0) {
                    (variance * Decimal::new(100, 0)) / budget
                } else {
                    Decimal::new(0, 0)
                };
                
                // 更新预算项
                sqlx::query!(
                    r#"
                    UPDATE budget_items
                    SET 
                        actual_amount = $1,
                        variance_amount = $2,
                        variance_percentage = $3,
                        updated_at = $4
                    WHERE 
                        budget_id = $5
                    "#,
                    item.actual_amount,
                    variance,
                    variance_percentage,
                    Utc::now(),
                    item.budget_id
                )
                .execute(&self.db_pool)
                .await?;
            }
        }
        
        Ok(budget_vs_actual)
    }
    
    // 计算支付渠道成本和利润
    async fn calculate_channel_profitability(
        &self,
        start_date: DateTime<Utc>,
        end_date: DateTime<Utc>,
        connector: Option<String>
    ) -> Result<Vec<ChannelProfitability>, Box<dyn std::error::Error>> {
        info!("计算支付渠道成本与利润");
        
        // 构建SQL查询
        let query = if let Some(connector_name) = connector {
            format!(
                "
                SELECT 
                    connector,
                    currency,
                    SUM(amount) as total_amount,
                    SUM(fees) as total_fees,
                    COUNT(*) as transaction_count
                FROM 
                    payments
                WHERE 
                    status = 'captured' AND
                    created_at BETWEEN $1 AND $2 AND
                    connector = '{}'
                GROUP BY 
                    connector, currency
                ",
                connector_name
            )
        } else {
            "
            SELECT 
                connector,
                currency,
                SUM(amount) as total_amount,
                SUM(fees) as total_fees,
                COUNT(*) as transaction_count
            FROM 
                payments
            WHERE 
                status = 'captured' AND
                created_at BETWEEN $1 AND $2
            GROUP BY 
                connector, currency
            ".to_string()
        };
        
        // 执行查询
        let rows = sqlx::query(&query)
            .bind(start_date)
            .bind(end_date)
            .fetch_all(&self.db_pool)
            .await?;
        
        // 处理结果
        let mut results = Vec::new();
        for row in rows {
            let connector: String = row.get("connector");
            let currency: String = row.get("currency");
            let total_amount: Decimal = row.get("total_amount");
            let total_fees: Decimal = row.get("total_fees");
            let transaction_count: i64 = row.get("transaction_count");
            
            // 获取渠道的收费设置
            let merchant_fee_rate = self.get_merchant_fee_rate(&connector, &currency).await?;
            let merchant_fees = total_amount * merchant_fee_rate;
            
            // 计算利润
            let profit = merchant_fees - total_fees;
            let profit_margin = if total_amount != Decimal::new(0, 0) {
                (profit * Decimal::new(100, 0)) / total_amount
            } else {
                Decimal::new(0, 0)
            };
            
            results.push(ChannelProfitability {
                connector,
                currency,
                total_amount,
                processor_fees: total_fees,
                merchant_fees,
                profit,
                profit_margin,
                transaction_count,
                average_transaction_amount: if transaction_count > 0 {
                    total_amount / Decimal::new(transaction_count, 0)
                } else {
                    Decimal::new(0, 0)
                },
                period_start: start_date,
                period_end: end_date,
            });
        }
        
        // 保存到分析表
        for result in &results {
            self.save_channel_profitability(result).await?;
        }
        
        Ok(results)
    }
    
    // 获取商户费率
    async fn get_merchant_fee_rate(
        &self,
        connector: &str,
        currency: &str
    ) -> Result<Decimal, Box<dyn std::error::Error>> {
        // 从费率配置表中查询
        let result = sqlx::query!(
            r#"
            SELECT fee_rate 
            FROM merchant_fee_configs
            WHERE connector = $1 AND currency = $2
            "#,
            connector,
            currency
        )
        .fetch_optional(&self.db_pool)
        .await?;
        
        match result {
            Some(row) => Ok(row.fee_rate),
            None => Ok(Decimal::new(25, 3))  // 默认2.5%
        }
    }
    
    // 保存渠道利润分析
    async fn save_channel_profitability(
        &self,
        profitability: &ChannelProfitability
    ) -> Result<(), Box<dyn std::error::Error>> {
        sqlx::query!(
            r#"
            INSERT INTO channel_profitability (
                connector, currency, total_amount, processor_fees, merchant_fees,
                profit, profit_margin, transaction_count, average_transaction_amount,
                period_start, period_end, created_at
            ) VALUES (
                $1, $2, $3, $4, $5, $6, $7, $8, $9, $10, $11, $12
            )
            ON CONFLICT (connector, currency, period_start, period_end)
            DO UPDATE SET
                total_amount = EXCLUDED.total_amount,
                processor_fees = EXCLUDED.processor_fees,
                merchant_fees = EXCLUDED.merchant_fees,
                profit = EXCLUDED.profit,
                profit_margin = EXCLUDED.profit_margin,
                transaction_count = EXCLUDED.transaction_count,
                average_transaction_amount = EXCLUDED.average_transaction_amount
            "#,
            profitability.connector,
            profitability.currency,
            profitability.total_amount,
            profitability.processor_fees,
            profitability.merchant_fees,
            profitability.profit,
            profitability.profit_margin,
            profitability.transaction_count as i64,
            profitability.average_transaction_amount,
            profitability.period_start,
            profitability.period_end,
            Utc::now()
        )
        .execute(&self.db_pool)
        .await?;
        
        Ok(())
    }
}
```

## 四、API接口实现

```rust
use axum::{
    routing::{get, post, put},
    Router, Extension, Json,
    extract::{Path, Query},
    response::{IntoResponse, Json as JsonResponse},
    http::StatusCode,
};
use chrono::{DateTime, Utc};
use rust_decimal::Decimal;
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use tracing::{info, error, instrument};
use uuid::Uuid;

// API路由设置
async fn setup_api_routes(
    payment_service: Arc<PaymentCoreService>,
    financial_service: Arc<FinancialService>,
    accounting_service: Arc<AccountingService>
) -> Router {
    Router::new()
        // 支付核心API
        .route("/api/v1/payments", post(create_payment))
        .route("/api/v1/payments/:id", get(get_payment))
        .route("/api/v1/payments/:id/capture", post(capture_payment))
        .route("/api/v1/payments/:id/cancel", post(cancel_payment))
        .route("/api/v1/payments/:id/traces", get(get_payment_traces))
        
        // 支付对冲与撤销API
        .route("/api/v1/payments/:id/refunds", post(create_refund))
        .route("/api/v1/payments/:id/refunds", get(list_refunds))
        .route("/api/v1/payments/:id/reversals", post(create_reversal))
        
        // 对账API
        .route("/api/v1/reconciliation/batches", post(create_reconciliation_batch))
        .route("/api/v1/reconciliation/batches/:id", get(get_reconciliation_batch))
        .route("/api/v1/reconciliation/batches/:id/items", get(get_reconciliation_items))
        .route("/api/v1/reconciliation/batches/:id/execute", post(execute_reconciliation))
        
        // 清算API
        .route("/api/v1/settlements", post(create_settlement))
        .route("/api/v1/settlements/:id", get(get_settlement))
        .route("/api/v1/settlements/merchant/:merchant_id", get(list_merchant_settlements))
        
        // 会计分析API
        .route("/api/v1/accounting/entries/:transaction_id", get(get_accounting_entries))
        .route("/api/v1/accounting/ledger", get(get_account_ledger))
        .route("/api/v1/accounting/profit-centers/:id/budget", get(get_profit_center_budget))
        .route("/api/v1/accounting/analytics/channel-profitability", get(get_channel_profitability))
        
        // 共享服务层
        .layer(Extension(payment_service))
        .layer(Extension(financial_service))
        .layer(Extension(accounting_service))
}

// 创建支付
#[instrument(skip(payment_service), fields(merchant_id = %payment_request.merchant_id))]
async fn create_payment(
    Extension(payment_service): Extension<Arc<PaymentCoreService>>,
    Json(payment_request): Json<PaymentRequest>
) -> impl IntoResponse {
    match payment_service.process_payment(payment_request).await {
        Ok(response) => {
            info!(payment_id = %response.payment_id, "支付创建成功");
            (StatusCode::CREATED, JsonResponse(response)).into_response()
        },
        Err(e) => {
            error!(error = %e, "支付创建失败");
            (
                StatusCode::INTERNAL_SERVER_ERROR,
                JsonResponse(serde_json::json!({
                    "error": e.to_string()
                }))
            ).into_response()
        }
    }
}

// 获取支付
async fn get_payment(
    Extension(payment_service): Extension<Arc<PaymentCoreService>>,
    Path(payment_id): Path<Uuid>
) -> impl IntoResponse {
    match payment_service.get_payment(payment_id).await {
        Ok(payment) => (StatusCode::OK, JsonResponse(payment)).into_response(),
        Err(e) => {
            if e.to_string().contains("not found") {
                (
                    StatusCode::NOT_FOUND,
                    JsonResponse(serde_json::json!({
                        "error": format!("Payment with id {} not found", payment_id)
                    }))
                ).into_response()
            } else {
                (
                    StatusCode::INTERNAL_SERVER_ERROR,
                    JsonResponse(serde_json::json!({
                        "error": e.to_string()
                    }))
                ).into_response()
            }
        }
    }
}

// 创建支付对冲
#[instrument(skip(financial_service), fields(payment_id = %payment_id))]
async fn create_reversal(
    Extension(financial_service): Extension<Arc<FinancialService>>,
    Path(payment_id): Path<Uuid>,
    Json(request): Json<ReversalRequest>
) -> impl IntoResponse {
    info!("请求创建支付对冲");
    
    match financial_service.process_payment_reversal(
        payment_id,
        request.amount,
        &request.reason
    ).await {
        Ok(reversal) => {
            info!(reversal_id = %reversal.reversal_id, "支付对冲创建成功");
            (StatusCode::CREATED, JsonResponse(reversal)).into_response()
        },
        Err(e) => {
            error!(error = %e, "支付对冲创建失败");
            (
                StatusCode::INTERNAL_SERVER_ERROR,
                JsonResponse(serde_json::json!({
                    "error": e.to_string()
                }))
            ).into_response()
        }
    }
}

// 创建对账批次
#[instrument(skip(financial_service))]
async fn create_reconciliation_batch(
    Extension(financial_service): Extension<Arc<FinancialService>>,
    Json(request): Json<ReconciliationBatchRequest>
) -> impl IntoResponse {
    info!(
        merchant_id = %request.merchant_id,
        connector = %request.connector,
        "创建对账批次"
    );
    
    match financial_service.create_reconciliation_batch(
        &request.merchant_id,
        &request.connector,
        request.start_date,
        request.end_date
    ).await {
        Ok(batch) => {
            info!(batch_id = %batch.batch_id, "对账批次创建成功");
            (StatusCode::CREATED, JsonResponse(batch)).into_response()
        },
        Err(e) => {
            error!(error = %e, "创建对账批次失败");
            (
                StatusCode::INTERNAL_SERVER_ERROR,
                JsonResponse(serde_json::json!({
                    "error": e.to_string()
                }))
            ).into_response()
        }
    }
}

// 获取渠道利润率分析
#[instrument(skip(accounting_service))]
async fn get_channel_profitability(
    Extension(accounting_service): Extension<Arc<AccountingService>>,
    Query(params): Query<ChannelProfitabilityParams>
) -> impl IntoResponse {
    info!("请求渠道利润率分析");
    
    let start_date = params.start_date.unwrap_or_else(|| {
        Utc::now() - chrono::Duration::days(30)
    });
    
    let end_date = params.end_date.unwrap_or_else(|| Utc::now());
    
    match accounting_service.calculate_channel_profitability(
        start_date,
        end_date,
        params.connector
    ).await {
        Ok(results) => {
            info!("渠道利润率分析成功返回 {} 条记录", results.len());
            (StatusCode::OK, JsonResponse(results)).into_response()
        },
        Err(e) => {
            error!(error = %e, "获取渠道利润率分析失败");
            (
                StatusCode::INTERNAL_SERVER_ERROR,
                JsonResponse(serde_json::json!({
                    "error": e.to_string()
                }))
            ).into_response()
        }
    }
}
```

## 五、数据库模式设计

下面是支持这个系统的关键数据库表设计：

```sql
-- 支付表
CREATE TABLE payments (
    payment_id UUID PRIMARY KEY,
    merchant_id VARCHAR(255) NOT NULL,
    amount DECIMAL(19, 4) NOT NULL,
    currency VARCHAR(3) NOT NULL,
    status INT NOT NULL,
    connector VARCHAR(255) NOT NULL,
    connector_payment_id VARCHAR(255),
    customer_id VARCHAR(255),
    created_at TIMESTAMP WITH TIME ZONE NOT NULL,
    updated_at TIMESTAMP WITH TIME ZONE NOT NULL,
    metadata JSONB,
    settlement_id UUID,
    CONSTRAINT fk_settlement FOREIGN KEY (settlement_id) REFERENCES settlements(settlement_id)
);

-- 支付跟踪表
CREATE TABLE payment_traces (
    trace_id UUID PRIMARY KEY,
    payment_id UUID NOT NULL,
    merchant_id VARCHAR(255) NOT NULL,
    timestamp TIMESTAMP WITH TIME ZONE NOT NULL,
    status INT NOT NULL,
    connector VARCHAR(255) NOT NULL,
    attempt_number INT NOT NULL,
    error_message TEXT,
    error_code VARCHAR(255),
    duration_ms INT,
    request_data JSONB,
    response_data JSONB,
    CONSTRAINT fk_payment FOREIGN KEY (payment_id) REFERENCES payments(payment_id)
);

-- 支付异常表
CREATE TABLE payment_exceptions (
    exception_id UUID PRIMARY KEY,
    payment_id UUID NOT NULL,
    exception_type VARCHAR(255) NOT NULL,
    error_code VARCHAR(255),
    error_message TEXT,
    created_at TIMESTAMP WITH TIME ZONE NOT NULL,
    resolved_at TIMESTAMP WITH TIME ZONE,
    resolution TEXT,
    resolution_type VARCHAR(255),
    resolved_by VARCHAR(255),
    CONSTRAINT fk_payment FOREIGN KEY (payment_id) REFERENCES payments(payment_id)
);

-- 支付对冲表
CREATE TABLE payment_reversals (
    reversal_id UUID PRIMARY KEY,
    payment_id UUID NOT NULL,
    amount DECIMAL(19, 4) NOT NULL,
    currency VARCHAR(3) NOT NULL,
    status INT NOT NULL,
    reason TEXT NOT NULL,
    reversal_reference VARCHAR(255) NOT NULL,
    created_at TIMESTAMP WITH TIME ZONE NOT NULL,
    updated_at TIMESTAMP WITH TIME ZONE NOT NULL,
    metadata JSONB,
    CONSTRAINT fk_payment FOREIGN KEY (payment_id) REFERENCES payments(payment_id)
);

-- 对账批次表
CREATE TABLE reconciliation_batches (
    batch_id UUID PRIMARY KEY,
    merchant_id VARCHAR(255) NOT NULL,
    connector VARCHAR(255) NOT NULL,
    start_date TIMESTAMP WITH TIME ZONE NOT NULL,
    end_date TIMESTAMP WITH TIME ZONE NOT NULL,
    status VARCHAR(50) NOT NULL,
    total_transactions INT NOT NULL,
    matched_transactions INT NOT NULL DEFAULT 0,
    unmatched_transactions INT NOT NULL DEFAULT 0,
    missing_transactions INT NOT NULL DEFAULT 0,
    extra_transactions INT NOT NULL DEFAULT 0,
    total_amount DECIMAL(19, 4) NOT NULL,
    discrepancy_amount DECIMAL(19, 4) NOT NULL DEFAULT 0,
    created_at TIMESTAMP WITH TIME ZONE NOT NULL,
    completed_at TIMESTAMP WITH TIME ZONE
);

-- 对账项目表
CREATE TABLE reconciliation_items (
    item_id UUID PRIMARY KEY,
    batch_id UUID NOT NULL,
    payment_id UUID,
    merchant_id VARCHAR(255) NOT NULL,
    connector VARCHAR(255) NOT NULL,
    connector_payment_id VARCHAR(255),
    amount DECIMAL(19, 4) NOT NULL,
    currency VARCHAR(3) NOT NULL,
    status VARCHAR(50) NOT NULL,
    transaction_date TIMESTAMP WITH TIME ZONE NOT NULL,
    transaction_type VARCHAR(50) NOT NULL,
    fees DECIMAL(19, 4) NOT NULL DEFAULT 0,
    system_recorded_status VARCHAR(50),
    is_reconciled BOOLEAN NOT NULL DEFAULT FALSE,
    discrepancy_reason TEXT,
    reconciliation_date TIMESTAMP WITH TIME ZONE,
    CONSTRAINT fk_batch FOREIGN KEY (batch_id) REFERENCES reconciliation_batches(batch_id),
    CONSTRAINT fk_payment FOREIGN KEY (payment_id) REFERENCES payments(payment_id)
);

/*
Let me continue with the SQL schema definition for 
the payment system using Hyperswitch. 
I need to finish the settlements table and 
add any other remaining tables for 
the accounting and financial management components.
*/

-- 结算表
CREATE TABLE settlements (
    settlement_id UUID PRIMARY KEY,
    merchant_id VARCHAR(255) NOT NULL,
    connector VARCHAR(255) NOT NULL,
    settlement_date TIMESTAMP WITH TIME ZONE NOT NULL,
    amount DECIMAL(19, 4) NOT NULL,
    currency VARCHAR(3) NOT NULL,
    fees DECIMAL(19, 4) NOT NULL,
    net_amount DECIMAL(19, 4) NOT NULL,
    status VARCHAR(50) NOT NULL,
    settlement_reference VARCHAR(255) NOT NULL,
    created_at TIMESTAMP WITH TIME ZONE NOT NULL,
    updated_at TIMESTAMP WITH TIME ZONE NOT NULL
);

-- 会计分录表
CREATE TABLE accounting_entries (
    entry_id UUID PRIMARY KEY,
    transaction_id UUID NOT NULL,
    account_code VARCHAR(20) NOT NULL,
    account_name VARCHAR(255) NOT NULL,
    debit_amount DECIMAL(19, 4) NOT NULL DEFAULT 0,
    credit_amount DECIMAL(19, 4) NOT NULL DEFAULT 0,
    transaction_date TIMESTAMP WITH TIME ZONE NOT NULL,
    entry_type VARCHAR(50) NOT NULL,
    description TEXT,
    reference VARCHAR(255),
    created_at TIMESTAMP WITH TIME ZONE NOT NULL
);

-- 会计科目表
CREATE TABLE accounting_categories (
    category_id VARCHAR(20) PRIMARY KEY,
    name VARCHAR(255) NOT NULL,
    parent_id VARCHAR(20),
    category_type VARCHAR(50) NOT NULL,
    description TEXT,
    is_active BOOLEAN NOT NULL DEFAULT TRUE,
    CONSTRAINT fk_parent FOREIGN KEY (parent_id) REFERENCES accounting_categories(category_id)
);

-- 利润中心表
CREATE TABLE profit_centers (
    center_id VARCHAR(20) PRIMARY KEY,
    name VARCHAR(255) NOT NULL,
    description TEXT,
    parent_id VARCHAR(20),
    is_active BOOLEAN NOT NULL DEFAULT TRUE,
    CONSTRAINT fk_parent FOREIGN KEY (parent_id) REFERENCES profit_centers(center_id)
);

-- 预算表
CREATE TABLE budget_items (
    budget_id UUID PRIMARY KEY,
    profit_center_id VARCHAR(20) NOT NULL,
    account_category_id VARCHAR(20) NOT NULL,
    fiscal_year INT NOT NULL,
    fiscal_month INT NOT NULL,
    amount DECIMAL(19, 4) NOT NULL,
    actual_amount DECIMAL(19, 4),
    variance_amount DECIMAL(19, 4),
    variance_percentage DECIMAL(5, 2),
    created_at TIMESTAMP WITH TIME ZONE NOT NULL,
    updated_at TIMESTAMP WITH TIME ZONE NOT NULL,
    CONSTRAINT fk_profit_center FOREIGN KEY (profit_center_id) REFERENCES profit_centers(center_id),
    CONSTRAINT fk_account_category FOREIGN KEY (account_category_id) REFERENCES accounting_categories(category_id)
);

-- 分销商分配表
CREATE TABLE distributor_allocations (
    allocation_id UUID PRIMARY KEY,
    payment_id UUID NOT NULL,
    distributor_id VARCHAR(255) NOT NULL,
    merchant_id VARCHAR(255) NOT NULL,
    amount DECIMAL(19, 4) NOT NULL,
    currency VARCHAR(3) NOT NULL,
    commission_rate DECIMAL(5, 4) NOT NULL,
    commission_amount DECIMAL(19, 4) NOT NULL,
    allocation_date TIMESTAMP WITH TIME ZONE NOT NULL,
    status VARCHAR(50) NOT NULL,
    settlement_id UUID,
    created_at TIMESTAMP WITH TIME ZONE NOT NULL,
    updated_at TIMESTAMP WITH TIME ZONE NOT NULL,
    CONSTRAINT fk_payment FOREIGN KEY (payment_id) REFERENCES payments(payment_id),
    CONSTRAINT fk_settlement FOREIGN KEY (settlement_id) REFERENCES settlements(settlement_id)
);

-- 渠道利润率分析表
CREATE TABLE channel_profitability (
    id SERIAL PRIMARY KEY,
    connector VARCHAR(255) NOT NULL,
    currency VARCHAR(3) NOT NULL,
    total_amount DECIMAL(19, 4) NOT NULL,
    processor_fees DECIMAL(19, 4) NOT NULL,
    merchant_fees DECIMAL(19, 4) NOT NULL,
    profit DECIMAL(19, 4) NOT NULL,
    profit_margin DECIMAL(5, 2) NOT NULL,
    transaction_count BIGINT NOT NULL,
    average_transaction_amount DECIMAL(19, 4) NOT NULL,
    period_start TIMESTAMP WITH TIME ZONE NOT NULL,
    period_end TIMESTAMP WITH TIME ZONE NOT NULL,
    created_at TIMESTAMP WITH TIME ZONE NOT NULL,
    UNIQUE(connector, currency, period_start, period_end)
);

-- 对账配置表
CREATE TABLE reconciliation_configurations (
    config_id UUID PRIMARY KEY,
    merchant_id VARCHAR(255) NOT NULL,
    connector VARCHAR(255) NOT NULL,
    layer VARCHAR(50) NOT NULL,
    schedule VARCHAR(50) NOT NULL,
    start_time VARCHAR(5) NOT NULL,
    timeout_minutes INT NOT NULL DEFAULT 60,
    retry_count INT NOT NULL DEFAULT 3,
    notify_on_discrepancy BOOLEAN NOT NULL DEFAULT TRUE,
    auto_resolve_threshold DECIMAL(19, 4) NOT NULL DEFAULT 0,
    reconciliation_rules JSONB NOT NULL DEFAULT '[]',
    is_active BOOLEAN NOT NULL DEFAULT TRUE,
    created_at TIMESTAMP WITH TIME ZONE NOT NULL,
    updated_at TIMESTAMP WITH TIME ZONE NOT NULL,
    UNIQUE(merchant_id, connector, layer)
);

-- 商户费率配置表
CREATE TABLE merchant_fee_configs (
    config_id UUID PRIMARY KEY,
    merchant_id VARCHAR(255) NOT NULL,
    connector VARCHAR(255) NOT NULL,
    currency VARCHAR(3) NOT NULL,
    fee_rate DECIMAL(5, 4) NOT NULL,
    fee_fixed DECIMAL(19, 4) NOT NULL DEFAULT 0,
    min_fee DECIMAL(19, 4),
    max_fee DECIMAL(19, 4),
    effective_from TIMESTAMP WITH TIME ZONE NOT NULL,
    effective_to TIMESTAMP WITH TIME ZONE,
    created_at TIMESTAMP WITH TIME ZONE NOT NULL,
    updated_at TIMESTAMP WITH TIME ZONE NOT NULL,
    UNIQUE(merchant_id, connector, currency, effective_from)
);

-- 支付网关费率配置表
CREATE TABLE connector_fee_configs (
    config_id UUID PRIMARY KEY,
    connector VARCHAR(255) NOT NULL,
    currency VARCHAR(3) NOT NULL,
    payment_method VARCHAR(50) NOT NULL,
    card_network VARCHAR(50),
    transaction_type VARCHAR(50) NOT NULL,
    fee_rate DECIMAL(5, 4) NOT NULL,
    fee_fixed DECIMAL(19, 4) NOT NULL DEFAULT 0,
    effective_from TIMESTAMP WITH TIME ZONE NOT NULL,
    effective_to TIMESTAMP WITH TIME ZONE,
    created_at TIMESTAMP WITH TIME ZONE NOT NULL,
    updated_at TIMESTAMP WITH TIME ZONE NOT NULL,
    UNIQUE(connector, currency, payment_method, card_network, transaction_type, effective_from)
);
```

## 六、构建主程序和配置

这里实现主程序，将所有组件连接起来：

```rust
use std::sync::Arc;
use tracing::{info, error};
use tokio::signal;

mod payment;
mod finance;
mod accounting;
mod api;
mod models;
mod database;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt::init();
    
    info!("启动支付系统服务...");
    
    // 加载配置
    let config = load_configuration().await?;
    
    // 初始化数据库连接池
    let db_pool = database::init_database(&config.database_url).await?;
    
    // 初始化Hyperswitch客户端
    let hyperswitch_client = payment::init_hyperswitch_client(&config.hyperswitch_api_key, &config.hyperswitch_url).await?;
    
    // 创建各服务
    let payment_service = Arc::new(payment::PaymentCoreService::new(
        db_pool.clone(),
        hyperswitch_client,
        &config
    ).await?);
    
    let financial_service = Arc::new(finance::FinancialService::new(
        db_pool.clone(),
        payment_service.clone(),
        &config
    ).await?);
    
    let accounting_service = Arc::new(accounting::AccountingService::new(
        db_pool.clone(),
        &config
    ).await?);
    
    // 设置API路由
    let app = api::setup_api_routes(
        payment_service.clone(),
        financial_service.clone(),
        accounting_service.clone()
    ).await;
    
    // 启动后台任务
    start_background_tasks(
        financial_service.clone(),
        accounting_service.clone(),
        &config
    ).await;
    
    // 启动HTTP服务器
    let addr = format!("0.0.0.0:{}", config.port);
    let listener = tokio::net::TcpListener::bind(&addr).await?;
    info!("API服务已启动在 {}", addr);
    
    // 等待优雅关闭信号
    let (shutdown_tx, shutdown_rx) = tokio::sync::oneshot::channel::<()>();
    tokio::spawn(async move {
        let _ = signal::ctrl_c().await;
        info!("接收到关闭信号，开始优雅关闭");
        let _ = shutdown_tx.send(());
    });
    
    // 启动服务器并等待关闭信号
    axum::serve(listener, app)
        .with_graceful_shutdown(async {
            let _ = shutdown_rx.await;
        })
        .await?;
    
    info!("服务优雅关闭完成");
    
    Ok(())
}

// 加载配置
async fn load_configuration() -> Result<Config, Box<dyn std::error::Error>> {
    // 实现配置加载逻辑
    // ...
    
    Ok(Config {
        database_url: std::env::var("DATABASE_URL")
            .unwrap_or_else(|_| "postgres://user:password@localhost:5432/payments".to_string()),
        hyperswitch_url: std::env::var("HYPERSWITCH_URL")
            .unwrap_or_else(|_| "https://sandbox.hyperswitch.io".to_string()),
        hyperswitch_api_key: std::env::var("HYPERSWITCH_API_KEY")
            .unwrap_or_else(|_| "test_api_key".to_string()),
        port: std::env::var("PORT")
            .ok()
            .and_then(|s| s.parse::<u16>().ok())
            .unwrap_or(8080),
        // 其他配置...
    })
}

// 启动后台任务
async fn start_background_tasks(
    financial_service: Arc<finance::FinancialService>,
    accounting_service: Arc<accounting::AccountingService>,
    config: &Config
) {
    // 启动对账任务
    tokio::spawn({
        let service = financial_service.clone();
        async move {
            let mut interval = tokio::time::interval(tokio::time::Duration::from_secs(3600)); // 每小时
            loop {
                interval.tick().await;
                if let Err(e) = service.run_scheduled_reconciliations().await {
                    error!(error = %e, "计划对账任务失败");
                }
            }
        }
    });
    
    // 启动清算任务
    tokio::spawn({
        let service = financial_service.clone();
        async move {
            let mut interval = tokio::time::interval(tokio::time::Duration::from_secs(86400)); // 每天
            loop {
                interval.tick().await;
                if let Err(e) = service.run_scheduled_settlements().await {
                    error!(error = %e, "计划清算任务失败");
                }
            }
        }
    });
    
    // 启动会计分析任务
    tokio::spawn({
        let service = accounting_service.clone();
        async move {
            let mut interval = tokio::time::interval(tokio::time::Duration::from_secs(86400)); // 每天
            loop {
                interval.tick().await;
                if let Err(e) = service.run_scheduled_analytics().await {
                    error!(error = %e, "计划分析任务失败");
                }
            }
        }
    });
}
```

## 七、系统配置和部署

使用Docker Compose实现系统部署：

```yaml
version: '3.8'

services:
  # 支付处理API服务
  payment-api:
    build:
      context: .
      dockerfile: Dockerfile
    ports:
      - "8080:8080"
    environment:
      - DATABASE_URL=postgres://user:password@postgres:5432/payments
      - HYPERSWITCH_URL=https://sandbox.hyperswitch.io
      - HYPERSWITCH_API_KEY=${HYPERSWITCH_API_KEY}
      - REDIS_URL=redis://redis:6379
      - KAFKA_BROKERS=kafka:9092
      - RUST_LOG=info
    depends_on:
      - postgres
      - redis
      - kafka
    restart: unless-stopped
    healthcheck:
      test: ["CMD", "curl", "-f", "http://localhost:8080/health"]
      interval: 30s
      timeout: 10s
      retries: 3
      start_period: 40s

  # 对账服务
  reconciliation-service:
    build:
      context: .
      dockerfile: Dockerfile.reconciliation
    environment:
      - DATABASE_URL=postgres://user:password@postgres:5432/payments
      - HYPERSWITCH_URL=https://sandbox.hyperswitch.io
      - HYPERSWITCH_API_KEY=${HYPERSWITCH_API_KEY}
      - REDIS_URL=redis://redis:6379
      - KAFKA_BROKERS=kafka:9092
      - RUST_LOG=info
    depends_on:
      - postgres
      - redis
      - kafka
    restart: unless-stopped

  # 会计分析服务
  accounting-service:
    build:
      context: .
      dockerfile: Dockerfile.accounting
    environment:
      - DATABASE_URL=postgres://user:password@postgres:5432/payments
      - CLICKHOUSE_URL=clickhouse://clickhouse:9000/analytics
      - KAFKA_BROKERS=kafka:9092
      - RUST_LOG=info
    depends_on:
      - postgres
      - clickhouse
      - kafka
    restart: unless-stopped

  # PostgreSQL数据库
  postgres:
    image: postgres:16
    environment:
      - POSTGRES_USER=user
      - POSTGRES_PASSWORD=password
      - POSTGRES_DB=payments
    volumes:
      - postgres-data:/var/lib/postgresql/data
      - ./init-scripts:/docker-entrypoint-initdb.d
    ports:
      - "5432:5432"
    restart: unless-stopped
    healthcheck:
      test: ["CMD-SHELL", "pg_isready -U user -d payments"]
      interval: 10s
      timeout: 5s
      retries: 5

  # Redis缓存
  redis:
    image: redis:7-alpine
    ports:
      - "6379:6379"
    volumes:
      - redis-data:/data
    restart: unless-stopped
    healthcheck:
      test: ["CMD", "redis-cli", "ping"]
      interval: 10s
      timeout: 5s
      retries: 5

  # Kafka
  kafka:
    image: confluentinc/cp-kafka:7.5.0
    environment:
      KAFKA_ADVERTISED_LISTENERS: PLAINTEXT://kafka:9092
      KAFKA_OFFSETS_TOPIC_REPLICATION_FACTOR: 1
      KAFKA_ZOOKEEPER_CONNECT: zookeeper:2181
    depends_on:
      - zookeeper
    ports:
      - "9092:9092"
    restart: unless-stopped
    healthcheck:
      test: ["CMD-SHELL", "kafka-topics --bootstrap-server kafka:9092 --list"]
      interval: 30s
      timeout: 10s
      retries: 3
      start_period: 30s

  # Zookeeper
  zookeeper:
    image: confluentinc/cp-zookeeper:7.5.0
    environment:
      ZOOKEEPER_CLIENT_PORT: 2181
    restart: unless-stopped

  # ClickHouse for analytics
  clickhouse:
    image: clickhouse/clickhouse-server:23.8
    ports:
      - "8123:8123"
      - "9000:9000"
    volumes:
      - clickhouse-data:/var/lib/clickhouse
    restart: unless-stopped

volumes:
  postgres-data:
  redis-data:
  clickhouse-data:
```

## 八、总结与关键功能

这个使用Rust和Hyperswitch实现的支付系统实现了以下关键功能：

1. **全面的支付跟踪系统**
   - 每个支付请求的全生命周期跟踪
   - 详细的异常处理机制，支持各类异常：网络、支付、账户、资金异常等
   - 异常分类与自动恢复策略

2. **完整的财务操作支持**
   - 支付撤销：通过PaymentReversal实现支付取消和退款
   - 支付对冲：支持部分或全额对冲操作
   - 多层次对账：支持多级对账，包括商户、处理器和银行层面
   - 自动化清算与结算：定期执行清算任务，生成结算记录

3. **高级会计功能**
   - 分布式分层对账：按不同维度和层级进行对账
   - 详细的会计分录生成：每笔交易自动生成相关会计分录
   - 预算管理与分析：支持预算设置和实际与预算比较
   - 利润中心与成本中心：可灵活配置，支持多级利润中心结构

4. **分布式架构优势**
   - 水平扩展：各服务可独立扩展
   - 高可用性：服务冗余和自动恢复
   - 消息队列解耦：通过Kafka实现组件间异步通信
   - 定时任务调度：自动执行对账、清算等批处理任务

5. **异常处理与恢复机制**
   - 全面的异常捕获与记录
   - 自定义异常处理器
   - 自动重试策略
   - 事务保证与一致性维护

通过这个系统，企业可以实现对支付流程的全面控制，
满足财务合规性要求，并提供深入的财务分析功能。
同时，Rust语言的安全性和性能特性，结合Hyperswitch的灵活支付处理能力，
为系统提供了坚实的技术基础。
