
# Rust语言特性与概念模型映射分析：容错与现实世界一致性

## 目录

- [Rust语言特性与概念模型映射分析：容错与现实世界一致性](#rust语言特性与概念模型映射分析容错与现实世界一致性)
  - [目录](#目录)
  - [1. Rust中的容错映射与策略](#1-rust中的容错映射与策略)
    - [1.1 错误处理与恢复机制](#11-错误处理与恢复机制)
    - [1.2 防御性编程与不变性保护](#12-防御性编程与不变性保护)
    - [1.3 部分失败处理](#13-部分失败处理)
    - [1.4 退化模式与优雅降级](#14-退化模式与优雅降级)
    - [1.5 超时与取消机制](#15-超时与取消机制)
    - [1.6 重试策略与指数退避](#16-重试策略与指数退避)
    - [1.7 单向操作与幂等性](#17-单向操作与幂等性)
  - [2. 业务模型与现实世界一致性](#2-业务模型与现实世界一致性)
    - [2.1 时间相关约束建模](#21-时间相关约束建模)
    - [2.2 物理世界限制的表达](#22-物理世界限制的表达)
    - [2.3 外部系统边界处理](#23-外部系统边界处理)
    - [2.4 不确定性与概率建模](#24-不确定性与概率建模)
    - [2.5 法规与合规约束](#25-法规与合规约束)
    - [2.6 经济模型和价值计算](#26-经济模型和价值计算)
  - [3. 实现一致性映射的模式与策略](#3-实现一致性映射的模式与策略)
    - [3.1 抽象层次分离](#31-抽象层次分离)
    - [3.2 抽象接口与可测试设计](#32-抽象接口与可测试设计)
    - [3.3 契约驱动设计](#33-契约驱动设计)
    - [3.4 业务与技术关注点分离](#34-业务与技术关注点分离)
    - [3.5 映射验证与测试策略](#35-映射验证与测试策略)
  - [4. 现实世界映射的挑战与解决方案](#4-现实世界映射的挑战与解决方案)
    - [4.1 处理模型差异与不一致](#41-处理模型差异与不一致)
    - [4.2 处理演化与兼容性](#42-处理演化与兼容性)
    - [4.3 分布式系统中的一致性](#43-分布式系统中的一致性)
    - [4.4 性能优化与缓存策略](#44-性能优化与缓存策略)
  - [5. 总结与最佳实践](#5-总结与最佳实践)
    - [5.1 映射策略选择指南](#51-映射策略选择指南)
    - [5.2 避免常见陷阱](#52-避免常见陷阱)
    - [5.3 测试映射的最佳实践](#53-测试映射的最佳实践)
    - [5.4 映射的自动化和代码生成](#54-映射的自动化和代码生成)
    - [5.5 结论与实践建议](#55-结论与实践建议)
  - [总结](#总结)

## 1. Rust中的容错映射与策略

### 1.1 错误处理与恢复机制

Rust提供了强大的错误处理机制，可以映射领域中的异常情况和恢复策略：

```rust
// 领域错误层次结构
#[derive(Debug, thiserror::Error)]
pub enum DomainError {
    #[error("验证错误: {0}")]
    ValidationError(String),
    
    #[error("业务规则冲突: {0}")]
    BusinessRuleViolation(String),
    
    #[error("资源不足: {0}")]
    ResourceShortage(String),
    
    #[error("不可恢复的系统错误: {0}")]
    SystemError(String),
    
    #[error("外部服务错误: {kind}({message})")]
    ExternalServiceError {
        kind: ExternalErrorKind,
        message: String,
    },
}

// 外部错误分类
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExternalErrorKind {
    Timeout,
    ServiceDown,
    RateLimited,
    InvalidResponse,
    Unknown,
}

// 错误处理策略
impl PaymentService {
    pub async fn process_payment(&self, payment: Payment) -> Result<PaymentReceipt, PaymentError> {
        // 尝试处理支付
        let result = self.gateway_client.process(payment).await;
        
        // 错误映射与恢复策略
        match result {
            Ok(receipt) => Ok(receipt),
            
            Err(GatewayError::Timeout) => {
                // 超时可能意味着支付已处理但未收到响应
                // 查询支付状态确认
                match self.check_payment_status(&payment.id).await {
                    Ok(status) if status == PaymentStatus::Succeeded => {
                        // 支付成功，创建收据
                        Ok(PaymentReceipt::from_payment(&payment, status))
                    },
                    Ok(status) => {
                        // 支付未成功
                        Err(PaymentError::Failed {
                            payment_id: payment.id.clone(),
                            status,
                        })
                    },
                    Err(_) => {
                        // 无法确认状态，需要手动处理
                        self.queue_for_manual_review(&payment).await?;
                        Err(PaymentError::Indeterminate {
                            payment_id: payment.id.clone(),
                            message: "支付状态未知，已加入人工审核队列".to_string(),
                        })
                    }
                }
            },
            
            Err(GatewayError::InsufficientFunds) => {
                // 直接映射到业务错误
                Err(PaymentError::InsufficientFunds {
                    payment_id: payment.id.clone(),
                    amount: payment.amount.clone(),
                })
            },
            
            Err(GatewayError::InvalidCard) => {
                // 映射到验证错误
                Err(PaymentError::InvalidPaymentMethod {
                    payment_id: payment.id.clone(),
                    reason: "信用卡无效或已过期".to_string(),
                })
            },
            
            Err(e) => {
                // 其他错误，记录并报告
                log::error!("支付处理异常: {}", e);
                Err(PaymentError::GatewayError {
                    payment_id: payment.id.clone(),
                    message: e.to_string(),
                })
            }
        }
    }
}
```

**映射分析**:

- 使用特定错误类型表达领域中的不同故障类别
- 区分可恢复和不可恢复的错误场景
- 实现特定于错误类型的恢复策略
- 在无法自动恢复时提供优雅的降级机制

### 1.2 防御性编程与不变性保护

确保域模型在面对意外输入时保持稳健：

```rust
// 防御性构造与验证
pub struct ShippingAddress {
    recipient: String,
    street: String,
    city: String,
    state: String,
    postal_code: String,
    country: CountryCode,
}

impl ShippingAddress {
    pub fn new(
        recipient: String,
        street: String,
        city: String,
        state: String,
        postal_code: String,
        country: CountryCode,
    ) -> Result<Self, ValidationError> {
        // 验证并清理输入
        let recipient = recipient.trim();
        if recipient.is_empty() {
            return Err(ValidationError::EmptyField("收件人".into()));
        }
        
        let street = street.trim();
        if street.is_empty() {
            return Err(ValidationError::EmptyField("街道地址".into()));
        }
        
        let city = city.trim();
        if city.is_empty() {
            return Err(ValidationError::EmptyField("城市".into()));
        }
        
        let state = state.trim();
        // 某些国家可能不需要州/省
        
        // 邮政编码验证和标准化
        let postal_code = postal_code.trim().to_uppercase();
        if !is_valid_postal_code(&postal_code, &country) {
            return Err(ValidationError::InvalidPostalCode(postal_code));
        }
        
        Ok(Self {
            recipient: recipient.to_string(),
            street: street.to_string(),
            city: city.to_string(),
            state: state.to_string(),
            postal_code,
            country,
        })
    }
    
    // 确保地址有效性的不变性检查
    pub fn verify_invariants(&self) -> Result<(), ValidationError> {
        // 检查国家与州/省的一致性
        if self.country == CountryCode::US && !is_valid_us_state(&self.state) {
            return Err(ValidationError::InvalidState(self.state.clone()));
        }
        
        // 检查邮政编码格式与国家匹配
        if !is_postal_code_format_valid_for_country(&self.postal_code, &self.country) {
            return Err(ValidationError::PostalCodeFormatMismatch {
                postal_code: self.postal_code.clone(),
                country: self.country,
            });
        }
        
        Ok(())
    }
    
    // 根据需要提供修饰数据的方法
    pub fn formatted_for_label(&self) -> String {
        // 根据国际邮政标准格式化地址
        match self.country {
            CountryCode::US => format!(
                "{}\n{}\n{}, {} {}\n{}",
                self.recipient, self.street, self.city, self.state, self.postal_code, self.country
            ),
            CountryCode::UK => format!(
                "{}\n{}\n{}\n{}\n{}",
                self.recipient, self.street, self.city, self.postal_code, self.country
            ),
            // 其他国家格式...
            _ => format!(
                "{}\n{}\n{} {}\n{}\n{}",
                self.recipient, self.street, self.postal_code, self.city, self.state, self.country
            ),
        }
    }
}

// 防御性方法调用
impl Order {
    pub fn update_shipping_address(&mut self, address: ShippingAddress) -> Result<(), DomainError> {
        // 检查先决条件
        if !matches!(self.status, OrderStatus::Draft | OrderStatus::Created) {
            return Err(DomainError::InvalidOperation(
                "只有草稿或新建状态的订单才能修改配送地址".into()
            ));
        }
        
        // 验证地址对订单有效
        self.validate_shipping_address(&address)?;
        
        // 检查国家限制
        if !self.is_shipping_available_to_country(&address.country) {
            return Err(DomainError::ShippingRestriction(
                format!("不支持配送到该国家: {:?}", address.country)
            ));
        }
        
        // 更新地址
        self.shipping_address = Some(address);
        self.last_modified = Utc::now();
        
        // 更新派生状态
        self.recalculate_shipping_cost()?;
        self.recalculate_tax()?;
        self.recalculate_total()?;
        
        Ok(())
    }
    
    fn validate_shipping_address(&self, address: &ShippingAddress) -> Result<(), DomainError> {
        // 确认地址不变量
        address.verify_invariants()
            .map_err(|e| DomainError::ValidationError(format!("地址无效: {}", e)))?;
            
        // 检查地址是否与订单商品兼容
        // 例如，某些危险品可能有特殊的配送地址要求
        for item in &self.items {
            if let Some(restriction) = item.shipping_restriction() {
                if !restriction.allows_address(address) {
                    return Err(DomainError::ShippingRestriction(
                        format!("商品 {} 不能配送到该地址", item.name())
                    ));
                }
            }
        }
        
        Ok(())
    }
}
```

**映射分析**:

- 强制输入验证确保无效数据不会进入系统
- 实现不变性检查确保对象状态一致性
- 方法先决条件验证防止非法操作
- 数据清理和标准化处理现实世界输入的不一致性

### 1.3 部分失败处理

处理复杂操作中的部分失败情况：

```rust
// 批量订单处理的部分失败处理
pub struct BulkOrderProcessor {
    order_service: Arc<dyn OrderService>,
    notification_service: Arc<dyn NotificationService>,
}

impl BulkOrderProcessor {
    pub async fn process_bulk_order(&self, bulk_order: BulkOrder) -> BulkOrderResult {
        let mut successful = Vec::new();
        let mut failed = Vec::new();
        
        // 处理每个子订单
        for order_request in bulk_order.orders {
            match self.process_single_order(order_request).await {
                Ok(order_id) => successful.push(order_id),
                Err(error) => failed.push(OrderFailure {
                    order_data: order_request,
                    error,
                }),
            }
        }
        
        // 生成结果报告
        let result = BulkOrderResult {
            bulk_order_id: bulk_order.id,
            successful_orders: successful,
            failed_orders: failed,
            timestamp: Utc::now(),
        };
        
        // 通知结果
        if !failed.is_empty() {
            // 发送部分失败通知
            let _ = self.notification_service
                .notify_partial_failure(&bulk_order.customer_id, &result)
                .await;
        }
        
        result
    }
    
    async fn process_single_order(&self, order_request: OrderRequest) -> Result<OrderId, OrderError> {
        // 验证单个订单
        self.validate_order_request(&order_request)?;
        
        // 创建订单
        let order_id = self.order_service.create_order(&order_request).await?;
        
        // 处理支付
        if let Some(payment_method) = &order_request.payment_method {
            self.order_service.process_payment(&order_id, payment_method).await?;
        }
        
        Ok(order_id)
    }
}

// 异构操作的事务处理
pub struct InventoryAdjustment {
    inventory_repository: Arc<dyn InventoryRepository>,
    notification_service: Arc<dyn NotificationService>,
    audit_logger: Arc<dyn AuditLogger>,
}

impl InventoryAdjustment {
    pub async fn adjust_inventory(&self, adjustments: Vec<StockAdjustment>) -> AdjustmentResult {
        let mut successful = Vec::new();
        let mut failed = Vec::new();
        
        // 尝试所有调整
        for adjustment in adjustments {
            let result = self.apply_single_adjustment(&adjustment).await;
            
            match result {
                Ok(()) => successful.push(adjustment),
                Err(e) => failed.push(AdjustmentFailure {
                    adjustment,
                    error: e,
                }),
            }
        }
        
        // 记录审计日志 - 关键操作，不应失败
        if let Err(e) = self.audit_logger.log_inventory_adjustments(&successful, &failed).await {
            log::error!("Failed to log inventory adjustments: {}", e);
            // 继续执行，不让审计日志失败影响操作
        }
        
        // 可选通知 - 非关键操作
        if !failed.is_empty() {
            let _ = self.notification_service
                .notify_partial_adjustment(&failed)
                .await;
        }
        
        AdjustmentResult {
            successful_count: successful.len(),
            failed_count: failed.len(),
            failed,
        }
    }
    
    async fn apply_single_adjustment(&self, adjustment: &StockAdjustment) -> Result<(), AdjustmentError> {
        // 加载库存项
        let mut inventory = self.inventory_repository
            .find_by_sku(&adjustment.sku)
            .await?
            .ok_or_else(|| AdjustmentError::ItemNotFound(adjustment.sku.clone()))?;
        
        // 应用调整
        match adjustment.kind {
            AdjustmentKind::Increment => {
                inventory.increase_quantity(adjustment.quantity)?;
            },
            AdjustmentKind::Decrement => {
                inventory.decrease_quantity(adjustment.quantity)
                    .map_err(|e| AdjustmentError::InsufficientStock(e.to_string()))?;
            },
            AdjustmentKind::SetAbsolute => {
                inventory.set_quantity(adjustment.quantity)?;
            },
        }
        
        // 保存更新
        self.inventory_repository.save(&inventory).await?;
        
        Ok(())
    }
}
```

**映射分析**:

- 实现批量操作的部分成功/失败处理
- 区分关键和非关键的后续步骤
- 优先完成尽可能多的操作而非全部失败
- 提供详细的失败报告以便后续处理

### 1.4 退化模式与优雅降级

实现系统在异常情况下的优雅降级：

```rust
// 多级服务质量策略
pub struct ProductRecommendationService {
    primary_engine: Arc<dyn RecommendationEngine>,
    fallback_engine: Arc<dyn RecommendationEngine>,
    cache: Arc<Cache<CustomerId, Vec<ProductRecommendation>>>,
}

impl ProductRecommendationService {
    pub async fn get_recommendations(
        &self, 
        customer_id: &CustomerId,
        context: &BrowsingContext,
    ) -> RecommendationResult {
        // 尝试从缓存获取
        if let Some(cached) = self.cache.get(customer_id).await {
            return RecommendationResult {
                products: cached,
                source: RecommendationSource::Cache,
                personalization_level: PersonalizationLevel::Historical,
            };
        }
        
        // 尝试使用主推荐引擎
        match self.primary_engine.recommend(customer_id, context).await {
            Ok(recommendations) => {
                // 缓存并返回结果
                self.cache.set(customer_id, recommendations.clone(), Duration::from_hours(1)).await;
                
                RecommendationResult {
                    products: recommendations,
                    source: RecommendationSource::PrimaryEngine,
                    personalization_level: PersonalizationLevel::Full,
                }
            },
            Err(e) => {
                // 记录错误
                log::warn!("Primary recommendation engine failed: {}", e);
                
                // 降级到备用引擎
                match self.fallback_engine.recommend(customer_id, context).await {
                    Ok(recommendations) => RecommendationResult {
                        products: recommendations,
                        source: RecommendationSource::FallbackEngine,
                        personalization_level: PersonalizationLevel::Basic,
                    },
                    Err(fallback_err) => {
                        // 两个引擎都失败，使用通用推荐
                        log::error!("Both recommendation engines failed. Primary: {}, Fallback: {}", e, fallback_err);
                        
                        RecommendationResult {
                            products: self.get_default_recommendations(context.category).await,
                            source: RecommendationSource::DefaultRules,
                            personalization_level: PersonalizationLevel::None,
                        }
                    }
                }
            }
        }
    }
    
    async fn get_default_recommendations(&self, category: Option<CategoryId>) -> Vec<ProductRecommendation> {
        // 返回基于类别的固定推荐或畅销商品
        match category {
            Some(category_id) => self.get_category_best_sellers(&category_id).await,
            None => self.get_global_best_sellers().await,
        }
    }
}

// 功能层级的降级
pub struct CheckoutService {
    payment_service: Arc<dyn PaymentService>,
    inventory_service: Arc<dyn InventoryService>,
    shipping_service: Arc<dyn ShippingService>,
    feature_flags: Arc<FeatureFlags>,
}

impl CheckoutService {
    pub async fn process_checkout(&self, checkout: CheckoutRequest) -> Result<CheckoutResult, CheckoutError> {
        // 启用基本验证
        self.validate_checkout_request(&checkout)?;
        
        // 根据功能标志决定启用的功能
        let inventory_check = self.feature_flags.is_enabled("inventory_check");
        let shipping_estimate = self.feature_flags.is_enabled("shipping_time_estimate");
        let tax_calculation = self.feature_flags.is_enabled("real_time_tax");
        
        // 构建结果
        let mut result = CheckoutResult {
            order_id: self.create_order(&checkout).await?,
            payment_result: None,
            inventory_status: None,
            shipping_estimate: None,
            tax_details: None,
        };
        
        // 处理支付（核心功能，不可降级）
        result.payment_result = Some(self.process_payment(&checkout, &result.order_id).await?);
        
        // 可降级功能：库存检查
        if inventory_check {
            result.inventory_status = match self.check_inventory(&checkout).await {
                Ok(status) => Some(status),
                Err(e) => {
                    log::warn!("库存检查失败，继续处理: {}", e);
                    None
                }
            };
        }
        
        // 可降级功能：配送时间估计
        if shipping_estimate {
            result.shipping_estimate = match self.estimate_shipping(&checkout).await {
                Ok(estimate) => Some(estimate),
                Err(e) => {
                    log::warn!("配送时间估计失败，继续处理: {}", e);
                    None
                }
            };
        }
        
        // 可降级功能：实时税费计算
        if tax_calculation {
            result.tax_details = match self.calculate_taxes(&checkout).await {
                Ok(tax) => Some(tax),
                Err(e) => {
                    log::warn!("实时税费计算失败，使用估算值: {}", e);
                    Some(self.estimate_tax(&checkout))
                }
            };
        } else {
            // 使用估算税费作为降级选项
            result.tax_details = Some(self.estimate_tax(&checkout));
        }
        
        Ok(result)
    }
}
```

**映射分析**:

- 实现多级服务质量降级策略
- 区分核心功能和可选增强功能
- 使用特性标志控制降级行为
- 保持透明性，向用户传达服务级别变化

### 1.5 超时与取消机制

处理长时间运行的操作和潜在的取消场景：

```rust
// 超时控制
pub struct ExternalServiceClient {
    client: reqwest::Client,
    base_url: String,
    timeout_config: TimeoutConfig,
}

impl ExternalServiceClient {
    pub async fn execute_operation<T: DeserializeOwned>(
        &self,
        endpoint: &str,
        payload: &impl Serialize,
    ) -> Result<T, ServiceError> {
        // 创建一个带有超时的请求任务
        let request_future = self.client
            .post(&format!("{}{}", self.base_url, endpoint))
            .json(payload)
            .send();
            
        // 应用超时
        let response = match tokio::time::timeout(self.timeout_config.request_timeout, request_future).await {
            Ok(result) => result.map_err(|e| ServiceError::ConnectionError(e.to_string()))?,
            Err(_) => return Err(ServiceError::Timeout(format!("请求超时: {}", endpoint))),
        };
        
        // 检查状态码
        if !response.status().is_success() {
            return Err(ServiceError::ErrorResponse {
                status: response.status().as_u16(),
                message: response.text().await.unwrap_or_else(|_| "无法读取错误信息".to_string()),
            });
        }
        
        // 解析响应
        match tokio::time::timeout(self.timeout_config.response_parse_timeout, response.json::<T>()).await {
            Ok(result) => result.map_err(|e| ServiceError::ResponseParseError(e.to_string())),
            Err(_) => Err(ServiceError::Timeout("响应解析超时".to_string())),
        }
    }
}

// 可取消的长时间操作
pub struct ReportGenerator {
    data_service: Arc<dyn DataService>,
    rendering_service: Arc<dyn RenderingService>,
}

impl ReportGenerator {
    pub async fn generate_report(
        &self,
        params: ReportParameters,
        cancellation_token: CancellationToken,
    ) -> Result<Report, ReportError> {
        // 检查取消信号
        if cancellation_token.is_cancelled() {
            return Err(ReportError::Cancelled);
        }
        
        // 第一阶段：获取数据
        let data = self.data_service.fetch_data(params.query.clone()).await?;
        
        // 再次检查取消
        if cancellation_token.is_cancelled() {
            return Err(ReportError::Cancelled);
        }
        
        // 第二阶段：处理数据
        let processed_data = self.process_data(data, &cancellation_token).await?;
        
        // 第三阶段：生成报告
        let report = self.rendering_service.render_report(processed_data, params.format).await?;
        
        Ok(report)
    }
    
    async fn process_data(
        &self,
        data: RawData,
        cancellation_token: &CancellationToken,
    ) -> Result<ProcessedData, ReportError> {
        let mut processed = ProcessedData::new();
        
        // 分批处理以支持取消
        for chunk in data.chunks(100) {
            // 定期检查取消
            if cancellation_token.is_cancelled() {
                return Err(ReportError::Cancelled);
            }
            
            // 处理当前批次
            let processed_chunk = self.process_chunk(chunk).await?;
            processed.extend(processed_chunk);
        }
        
        Ok(processed)
    }
}

// 取消令牌实现
#[derive(Clone)]
pub struct CancellationToken {
    is_cancelled: Arc<AtomicBool>,
}

impl CancellationToken {
    pub fn new() -> Self {
        Self {
            is_cancelled: Arc::new(AtomicBool::new(false)),
        }
    }
    
    pub fn cancel(&self) {
        self.is_cancelled.store(true, Ordering::SeqCst);
    }
    
    pub fn is_cancelled(&self) -> bool {
        self.is_cancelled.load(Ordering::SeqCst)
    }
}
```

**映射分析**:

- 使用超时控制避免操作无限期阻塞
- 实现取消机制支持用户中止长时间操作
- 在关键检查点检查取消状态
- 分段处理大型操作以支持更及时的取消响应

### 1.6 重试策略与指数退避

实现智能重试以处理临时故障：

```rust
// 可配置的重试策略
pub struct RetryConfig {
    max_attempts: u32,
    initial_backoff: Duration,
    max_backoff: Duration,
    backoff_multiplier: f64,
    retry_on: Vec<ErrorKind>,
}

// 重试执行器
pub struct RetryExecutor {
    config: RetryConfig,
}

impl RetryExecutor {
    pub async fn execute<F, Fut, T, E>(&self, operation: F) -> Result<T, RetryError<E>>
    where
        F: Fn() -> Fut,
        Fut: Future<Output = Result<T, E>>,
        E: Error + 'static,
    {
        let mut attempts = 0;
        let mut backoff = self.config.initial_backoff;
        
        loop {
            attempts += 1;
            
            match operation().await {
                Ok(result) => return Ok(result),
                Err(error) => {
                    // 检查是否达到最大尝试次数
                    if attempts >= self.config.max_attempts {
                        return Err(RetryError::MaxAttemptsExceeded {
                            attempts,
                            error: Box::new(error),
                        });
                    }
                    
                    // 检查错误类型是否应该重试
                    let error_kind = self.classify_error(&error);
                    if !self.config.retry_on.contains(&error_kind) {
                        return Err(RetryError::NonRetryableError {
                            error: Box::new(error),
                            kind: error_kind,
                        });
                    }
                    
                    // 记录重试信息
                    log::info!(
                        "操作失败，第{}次尝试，将在{:?}后重试: {}",
                        attempts,
                        backoff,
                        error
                    );
                    
                    // 等待退避时间
                    tokio::time::sleep(backoff).await;
                    
                    // 计算下一次退避时间（指数增长）
                    backoff = min(
                        backoff.mul_f64(self.config.backoff_multiplier),
                        self.config.max_backoff,
                    );
                }
            }
        }
    }
    
    fn classify_error<E: Error>(&self, error: &E) -> ErrorKind {
        // 根据错误类型进行分类
        // 这里是一个简单示例，实际实现会更复杂
        if error.to_string().contains("timeout") {
            ErrorKind::Timeout
        } else if error.to_string().contains("connection") {
            ErrorKind::Connection
        } else if error.to_string().contains("rate limit") {
            ErrorKind::RateLimit
        } else {
            ErrorKind::Unknown
        }
    }
}

// 在支付服务中应用重试策略
pub struct PaymentProcessor {
    gateway_client: Arc<dyn PaymentGateway>,
    retry_executor: RetryExecutor,
}

impl PaymentProcessor {
    pub async fn process_payment(&self, payment: &Payment) -> Result<PaymentResult, PaymentError> {
        // 使用重试执行器处理支付
        let result = self.retry_executor.execute(|| {
            let payment_clone = payment.clone();
            let client = self.gateway_client.clone();
            
            async move {
                client.process_payment(&payment_clone).await
            }
        }).await;
        
        // 处理重试结果
        match result {
            Ok(gateway_result) => {
                // 成功处理
                Ok(PaymentResult {
                    transaction_id: gateway_result.transaction_id,
                    status: gateway_result.status,
                    processed_at: Utc::now(),
                    attempts: gateway_result.attempts,
                })
            },
            Err(RetryError::MaxAttemptsExceeded { attempts, error }) => {
                // 多次尝试后仍然失败
                log::error!("支付处理失败，已尝试{}次: {}", attempts, error);
                Err(PaymentError::ProcessingFailed {
                    payment_id: payment.id.clone(),
                    attempts,
                    reason: error.to_string(),
                })
            },
            Err(RetryError::NonRetryableError { error, kind }) => {
                // 不可重试的错误
                log::error!("支付处理遇到不可重试错误: {:?} - {}", kind, error);
                Err(PaymentError::from_gateway_error(*error))
            },
        }
    }
}
```

**映射分析**:

- 定义可配置的重试策略处理临时故障
- 使用指数退避防止频繁重试对系统造成压力
- 区分可重试和不可重试的错误类型
- 透明地向调用者报告重试历史

### 1.7 单向操作与幂等性

确保在不确定性环境中操作的正确性：

```rust
// 幂等操作接口
pub trait IdempotentOperation<Params, Result> {
    fn operation_key(&self, params: &Params) -> String;
    async fn execute(&self, params: &Params) -> Result;
}

// 幂等操作处理器
pub struct IdempotencyHandler<T, P, R> {
    operation: T,
    store: Arc<dyn IdempotencyStore>,
    lock_manager: Arc<dyn LockManager>,
}

impl<T, P, R> IdempotencyHandler<T, P, R>
where
    T: IdempotentOperation<P, Result<R, OperationError>>,
    P: Clone + Send + Sync,
    R: Clone + Send + Sync,
{
    pub async fn execute(&self, params: &P) -> Result<R, IdempotencyError> {
        // 生成操作键
        let operation_key = self.operation.operation_key(params);
        
        // 检查之前的执行结果
        if let Some(result) = self.store.get(&operation_key).await? {
            return Ok(result);
        }
        
        // 获取锁以防止并发执行
        let lock = self.lock_manager.acquire_lock(&operation_key, Duration::from_secs(30)).await?;
        
        // 双重检查，防止锁等待期间其他进程完成执行
        if let Some(result) = self.store.get(&operation_key).await? {
            lock.release().await?;
            return Ok(result);
        }
        
        // 执行操作
        let result = match self.operation.execute(params).await {
            Ok(result) => result,
            Err(e) => {
                lock.release().await?;
                return Err(IdempotencyError::OperationFailed(e.to_string()));
            }
        };
        
        // 存储结果
        self.store.store(&operation_key, &result).await?;
        
        // 释放锁
        lock.release().await?;
        
        Ok(result)
    }
}

// 支付处理的幂等实现
pub struct PaymentProcessor {
    gateway: Arc<dyn PaymentGateway>,
    idempotency_handler: IdempotencyHandler<Self, PaymentRequest, PaymentResponse>,
}

impl IdempotentOperation<PaymentRequest, Result<PaymentResponse, OperationError>> for PaymentProcessor {
    fn operation_key(&self, params: &PaymentRequest) -> String {
        // 使用请求的唯一属性构建键
        format!("payment:{}:{}:{}", 
            params.order_id,
            params.payment_method_id,
            params.amount
        )
    }
    
    async fn execute(&self, params: &PaymentRequest) -> Result<PaymentResponse, OperationError> {
        // 调用支付网关
        let gateway_response = self.gateway.process_payment(params).await
            .map_err(|e| OperationError::Gateway(e.to_string()))?;
            
        // 转换响应
        Ok(PaymentResponse {
            transaction_id: gateway

```rust
            transaction_id: gateway_response.transaction_id,
            status: gateway_response.status,
            amount: params.amount.clone(),
            processed_at: Utc::now(),
        })
    }
}

impl PaymentProcessor {
    pub async fn process_payment(&self, request: &PaymentRequest) -> Result<PaymentResponse, PaymentError> {
        // 使用幂等处理器执行操作
        match self.idempotency_handler.execute(request).await {
            Ok(response) => Ok(response),
            Err(IdempotencyError::OperationFailed(msg)) => {
                Err(PaymentError::ProcessingFailed {
                    order_id: request.order_id.clone(),
                    reason: msg,
                })
            },
            Err(e) => Err(PaymentError::SystemError(e.to_string())),
        }
    }
}

// 订单出货幂等操作
pub struct OrderShipmentProcessor {
    order_repository: Arc<dyn OrderRepository>,
    inventory_service: Arc<dyn InventoryService>,
    shipping_service: Arc<dyn ShippingService>,
}

impl OrderShipmentProcessor {
    pub async fn process_shipment(&self, order_id: &OrderId) -> Result<ShipmentResult, ShipmentError> {
        // 生成幂等操作键
        let idempotency_key = format!("ship_order:{}", order_id);
        
        // 检查订单是否已出货
        let order = self.order_repository.find_by_id(order_id).await?
            .ok_or_else(|| ShipmentError::OrderNotFound(order_id.clone()))?;
            
        // 如果订单已经处于已发货状态，返回之前的结果
        if let OrderStatus::Shipped { tracking_code, carrier, shipped_at } = order.status() {
            return Ok(ShipmentResult {
                order_id: order_id.clone(),
                tracking_code: tracking_code.clone(),
                carrier: carrier.clone(),
                shipped_at: *shipped_at,
            });
        }
        
        // 验证订单是否可以发货
        if order.status() != &OrderStatus::Paid {
            return Err(ShipmentError::InvalidOrderState(
                format!("订单必须处于已支付状态才能发货，当前状态: {:?}", order.status())
            ));
        }
        
        // 执行出货流程（第一步：提交给配送服务）
        let shipment = self.shipping_service.create_shipment(&order).await?;
        
        // 更新订单状态（第二步：更新订单）
        let mut updated_order = order.clone();
        updated_order.mark_as_shipped(
            &shipment.tracking_code,
            &shipment.carrier,
            shipment.estimated_delivery,
        )?;
        
        self.order_repository.save(&updated_order).await?;
        
        // 返回结果
        Ok(ShipmentResult {
            order_id: order_id.clone(),
            tracking_code: shipment.tracking_code,
            carrier: shipment.carrier,
            shipped_at: Utc::now(),
        })
    }
}
```

**映射分析**:

- 定义幂等操作确保相同请求不会重复执行
- 使用唯一键和结果存储实现幂等性
- 防止分布式系统中的重复处理
- 实现单向操作的安全恢复机制

## 2. 业务模型与现实世界一致性

### 2.1 时间相关约束建模

时间是现实世界中的关键维度，Rust可以精确建模时间约束：

```rust
// 时间敏感的领域对象
#[derive(Debug, Clone)]
pub struct Reservation {
    id: ReservationId,
    resource_id: ResourceId,
    customer_id: CustomerId,
    time_slot: TimeSlot,
    status: ReservationStatus,
    created_at: DateTime<Utc>,
    last_modified: DateTime<Utc>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TimeSlot {
    start: DateTime<Utc>,
    end: DateTime<Utc>,
}

impl TimeSlot {
    pub fn new(start: DateTime<Utc>, end: DateTime<Utc>) -> Result<Self, ValidationError> {
        // 验证时间段的有效性
        if start >= end {
            return Err(ValidationError::InvalidTimeSlot("开始时间必须早于结束时间".into()));
        }
        
        // 验证持续时间
        let duration = end - start;
        if duration < Duration::minutes(15) {
            return Err(ValidationError::InvalidTimeSlot("时间段必须至少15分钟".into()));
        }
        
        if duration > Duration::hours(4) {
            return Err(ValidationError::InvalidTimeSlot("时间段不能超过4小时".into()));
        }
        
        Ok(Self { start, end })
    }
    
    pub fn overlaps_with(&self, other: &TimeSlot) -> bool {
        (self.start < other.end) && (self.end > other.start)
    }
    
    pub fn contains(&self, time: DateTime<Utc>) -> bool {
        time >= self.start && time < self.end
    }
    
    pub fn duration(&self) -> Duration {
        self.end - self.start
    }
    
    // 检查是否在可预订的未来时间范围内
    pub fn is_bookable(&self, booking_policy: &BookingPolicy) -> bool {
        let now = Utc::now();
        
        // 检查最小提前预订时间
        if self.start - now < booking_policy.min_advance_time {
            return false;
        }
        
        // 检查最大提前预订时间
        if self.start - now > booking_policy.max_advance_time {
            return false;
        }
        
        // 检查是否在营业时间内
        booking_policy.is_within_operating_hours(self)
    }
}

// 预订策略
pub struct BookingPolicy {
    min_advance_time: Duration,    // 最小提前预订时间
    max_advance_time: Duration,    // 最大提前预订时间
    operating_hours: Vec<OperatingHoursRule>, // 营业时间规则
    blackout_periods: Vec<TimeSlot>, // 不可预订的时间段
}

impl BookingPolicy {
    pub fn is_within_operating_hours(&self, time_slot: &TimeSlot) -> bool {
        // 获取时间段开始和结束的工作日
        let start_weekday = time_slot.start.weekday().num_days_from_monday();
        let end_weekday = time_slot.end.weekday().num_days_from_monday();
        
        // 如果开始和结束日期不同，需要分段检查
        if start_weekday != end_weekday {
            // 复杂情况处理逻辑...
            todo!()
        } else {
            // 同一天内的时间段
            let applicable_rule = self.operating_hours.iter()
                .find(|rule| rule.applies_to_weekday(start_weekday));
                
            if let Some(rule) = applicable_rule {
                rule.is_within_hours(time_slot)
            } else {
                false // 该工作日没有营业规则，不可预订
            }
        }
    }
    
    pub fn is_in_blackout_period(&self, time_slot: &TimeSlot) -> bool {
        self.blackout_periods.iter().any(|period| period.overlaps_with(time_slot))
    }
}

// 预订服务
pub struct ReservationService {
    reservation_repository: Arc<dyn ReservationRepository>,
    resource_repository: Arc<dyn ResourceRepository>,
    clock: Arc<dyn Clock>,  // 时钟抽象，便于测试
}

impl ReservationService {
    pub async fn create_reservation(
        &self,
        request: CreateReservationRequest
    ) -> Result<Reservation, ReservationError> {
        // 检查资源是否存在
        let resource = self.resource_repository.find_by_id(&request.resource_id).await?
            .ok_or(ReservationError::ResourceNotFound(request.resource_id.clone()))?;
            
        // 创建时间段
        let time_slot = TimeSlot::new(request.start_time, request.end_time)
            .map_err(ReservationError::ValidationError)?;
            
        // 检查预订策略
        if !time_slot.is_bookable(&resource.booking_policy()) {
            return Err(ReservationError::PolicyViolation("所选时间段不符合预订策略".into()));
        }
        
        // 检查时间段是否已被预订
        let conflicting = self.reservation_repository
            .find_overlapping(&request.resource_id, &time_slot).await?;
            
        if !conflicting.is_empty() {
            return Err(ReservationError::TimeSlotUnavailable(
                "所选时间段已被预订".into()
            ));
        }
        
        // 创建预订
        let reservation = Reservation::new(
            ReservationId::new(),
            request.resource_id,
            request.customer_id,
            time_slot,
            self.clock.now(),
        );
        
        // 保存预订
        self.reservation_repository.save(&reservation).await?;
        
        Ok(reservation)
    }
    
    // 检查预订即将到期并发送提醒
    pub async fn check_upcoming_reservations(&self) -> Result<Vec<Reservation>, ReservationError> {
        let now = self.clock.now();
        let reminder_window = now + Duration::hours(24);
        
        // 查找未来24小时内的预订
        let upcoming = self.reservation_repository
            .find_by_time_range(now, reminder_window).await?;
            
        Ok(upcoming)
    }
}

// 时钟抽象
pub trait Clock: Send + Sync {
    fn now(&self) -> DateTime<Utc>;
}

// 实时时钟实现
pub struct RealClock;

impl Clock for RealClock {
    fn now(&self) -> DateTime<Utc> {
        Utc::now()
    }
}

// 用于测试的固定时钟
pub struct FixedClock {
    fixed_time: DateTime<Utc>,
}

impl FixedClock {
    pub fn new(time: DateTime<Utc>) -> Self {
        Self { fixed_time: time }
    }
    
    pub fn advance(&mut self, duration: Duration) {
        self.fixed_time = self.fixed_time + duration;
    }
}

impl Clock for FixedClock {
    fn now(&self) -> DateTime<Utc> {
        self.fixed_time
    }
}
```

**映射分析**:

- 使用明确的时间类型和验证规则表达时间约束
- 处理时间相关的业务规则和政策
- 实现时间重叠和冲突检测
- 通过时钟抽象支持可测试的时间相关逻辑

### 2.2 物理世界限制的表达

将物理世界的约束映射到代码模型中：

```rust
// 物理约束的领域对象
#[derive(Debug, Clone)]
pub struct ShippingPackage {
    id: PackageId,
    items: Vec<ShippableItem>,
    dimensions: Dimensions,
    weight: Weight,
    shipping_class: ShippingClass,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Dimensions {
    length: Measurement,
    width: Measurement,
    height: Measurement,
    unit: LengthUnit,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Weight {
    value: f64,
    unit: WeightUnit,
}

impl ShippingPackage {
    pub fn new(items: Vec<ShippableItem>) -> Result<Self, PackagingError> {
        if items.is_empty() {
            return Err(PackagingError::EmptyPackage);
        }
        
        // 计算包裹尺寸和重量
        let dimensions = Self::calculate_package_dimensions(&items)?;
        let weight = Self::calculate_total_weight(&items)?;
        
        // 确定运输类别
        let shipping_class = Self::determine_shipping_class(&dimensions, &weight, &items);
        
        // 验证物理约束
        Self::validate_physical_constraints(&dimensions, &weight, &shipping_class)?;
        
        Ok(Self {
            id: PackageId::new(),
            items,
            dimensions,
            weight,
            shipping_class,
        })
    }
    
    fn calculate_package_dimensions(items: &[ShippableItem]) -> Result<Dimensions, PackagingError> {
        // 简化版本：使用最大的物品尺寸，实际上需要更复杂的3D装箱算法
        let mut max_length = Measurement::zero();
        let mut max_width = Measurement::zero();
        let mut max_height = Measurement::zero();
        let unit = LengthUnit::Centimeter; // 标准化为厘米
        
        for item in items {
            let item_dims = item.dimensions().to_unit(unit);
            max_length = max_length.max(item_dims.length);
            max_width = max_width.max(item_dims.width);
            max_height = max_height.max(item_dims.height);
        }
        
        // 添加包装材料的额外空间
        let package_length = max_length + Measurement::new(2.0, unit);
        let package_width = max_width + Measurement::new(2.0, unit);
        let package_height = max_height + Measurement::new(2.0, unit);
        
        Ok(Dimensions {
            length: package_length,
            width: package_width,
            height: package_height,
            unit,
        })
    }
    
    fn calculate_total_weight(items: &[ShippableItem]) -> Result<Weight, PackagingError> {
        let unit = WeightUnit::Kilogram; // 标准化为千克
        let mut total = 0.0;
        
        for item in items {
            let item_weight = item.weight().to_unit(unit);
            total += item_weight.value;
        }
        
        // 添加包装材料的重量（估计为物品总重的5%）
        let packaging_weight = total * 0.05;
        let total_weight = total + packaging_weight;
        
        Ok(Weight {
            value: total_weight,
            unit,
        })
    }
    
    fn determine_shipping_class(
        dimensions: &Dimensions,
        weight: &Weight,
        items: &[ShippableItem]
    ) -> ShippingClass {
        // 检查是否含有危险品
        let has_hazardous = items.iter().any(|item| item.is_hazardous());
        
        // 检查是否含有易碎品
        let has_fragile = items.iter().any(|item| item.is_fragile());
        
        // 检查是否超重
        let is_heavy = weight.value > 20.0; // 超过20公斤视为重物
        
        // 检查是否超大
        let volume = dimensions.length.value() * dimensions.width.value() * dimensions.height.value();
        let is_oversized = volume > 125000.0; // 超过125000立方厘米视为超大
        
        // 确定运输类别
        match (has_hazardous, has_fragile, is_heavy, is_oversized) {
            (true, _, _, _) => ShippingClass::Hazardous,
            (_, true, true, _) => ShippingClass::FragileAndHeavy,
            (_, true, _, _) => ShippingClass::Fragile,
            (_, _, true, true) => ShippingClass::HeavyAndOversized,
            (_, _, true, _) => ShippingClass::Heavy,
            (_, _, _, true) => ShippingClass::Oversized,
            _ => ShippingClass::Standard,
        }
    }
    
    fn validate_physical_constraints(
        dimensions: &Dimensions,
        weight: &Weight,
        shipping_class: &ShippingClass
    ) -> Result<(), PackagingError> {
        // 检查尺寸是否超过运输限制
        let max_length = Measurement::new(150.0, LengthUnit::Centimeter);
        if dimensions.length > max_length {
            return Err(PackagingError::ExceedsMaximumLength(dimensions.length.clone()));
        }
        
        let max_girth = Measurement::new(300.0, LengthUnit::Centimeter);
        let girth = (dimensions.width * 2.0) + (dimensions.height * 2.0);
        if girth > max_girth {
            return Err(PackagingError::ExceedsMaximumGirth(girth));
        }
        
        // 检查重量是否超过运输限制
        let max_weight = Weight {
            value: match shipping_class {
                ShippingClass::Standard => 30.0,
                ShippingClass::Heavy | ShippingClass::HeavyAndOversized => 70.0,
                ShippingClass::Hazardous => 20.0,
                _ => 50.0,
            },
            unit: WeightUnit::Kilogram,
        };
        
        if weight.value > max_weight.value {
            return Err(PackagingError::ExceedsMaximumWeight(weight.clone()));
        }
        
        Ok(())
    }
    
    // 计算运输成本
    pub fn calculate_shipping_cost(&self, distance: Distance, carrier: &Carrier) -> Money {
        // 基础运费由重量、尺寸和距离决定
        let volume = self.dimensions.length.value() * 
                     self.dimensions.width.value() * 
                     self.dimensions.height.value();
                     
        let volumetric_weight = volume / 5000.0; // 体积重 (cm³/5000)
        let chargeable_weight = f64::max(self.weight.value, volumetric_weight);
        
        // 基础费率
        let base_rate = carrier.base_rate_per_kg() * chargeable_weight;
        
        // 距离因子
        let distance_factor = match distance.to_unit(DistanceUnit::Kilometer).value() {
            d if d <= 50.0 => 1.0,
            d if d <= 200.0 => 1.2,
            d if d <= 500.0 => 1.5,
            d if d <= 1000.0 => 1.8,
            _ => 2.2,
        };
        
        // 特殊处理附加费
        let special_handling_fee = match self.shipping_class {
            ShippingClass::Fragile => base_rate * 0.2,
            ShippingClass::Heavy => base_rate * 0.3,
            ShippingClass::Oversized => base_rate * 0.5,
            ShippingClass::FragileAndHeavy => base_rate * 0.6,
            ShippingClass::HeavyAndOversized => base_rate * 0.8,
            ShippingClass::Hazardous => base_rate * 1.0,
            ShippingClass::Standard => 0.0,
        };
        
        // 总运费
        let total = (base_rate * distance_factor) + special_handling_fee;
        
        Money::new_usd(total)
    }
}
```

**映射分析**:

- 使用专门的类型表示物理量（尺寸、重量）
- 实现物理约束的验证和检查
- 基于物理特性分类和决策
- 复杂物理规则的分解和模块化

### 2.3 外部系统边界处理

与现实世界系统集成时的边界处理：

```rust
// 外部支付系统集成
pub struct PaymentGatewayAdapter {
    client: reqwest::Client,
    config: PaymentGatewayConfig,
    mapper: PaymentDataMapper,
}

impl PaymentGatewayAdapter {
    pub async fn process_payment(&self, payment: &Payment) -> Result<PaymentResult, GatewayError> {
        // 转换内部支付模型到外部API格式
        let request_data = self.mapper.to_gateway_request(payment, &self.config);
        
        // 构建HTTP请求
        let response = self.client
            .post(&self.config.api_url)
            .header("Authorization", format!("Bearer {}", self.config.api_key))
            .header("Content-Type", "application/json")
            .json(&request_data)
            .send()
            .await
            .map_err(|e| GatewayError::ConnectionError(e.to_string()))?;
            
        // 处理HTTP响应
        if !response.status().is_success() {
            let status = response.status();
            let error_text = response.text().await
                .unwrap_or_else(|_| "Failed to read error response".to_string());
                
            return match status.as_u16() {
                400 => Err(GatewayError::InvalidRequest(parse_error_message(&error_text))),
                401 | 403 => Err(GatewayError::AuthenticationError),
                402 => Err(GatewayError::PaymentRejected(parse_error_code(&error_text))),
                429 => Err(GatewayError::RateLimited),
                500..=599 => Err(GatewayError::GatewayServerError(status.as_u16())),
                _ => Err(GatewayError::UnexpectedResponse(status.as_u16())),
            };
        }
        
        // 解析成功响应
        let gateway_response: GatewayResponse = response.json().await
            .map_err(|e| GatewayError::ResponseParseError(e.to_string()))?;
            
        // 验证响应
        self.validate_gateway_response(&gateway_response, payment)?;
        
        // 转换为内部模型
        let result = self.mapper.from_gateway_response(gateway_response, payment);
        
        Ok(result)
    }
    
    fn validate_gateway_response(
        &self,
        response: &GatewayResponse,
        original_payment: &Payment
    ) -> Result<(), GatewayError> {
        // 验证交易金额匹配
        if !self.is_amount_matching(response.amount, original_payment.amount.value()) {
            return Err(GatewayError::AmountMismatch {
                expected: original_payment.amount.value(),
                actual: response.amount,
            });
        }
        
        // 验证货币匹配
        if response.currency != original_payment.amount.currency().code() {
            return Err(GatewayError::CurrencyMismatch {
                expected: original_payment.amount.currency().code(),
                actual: response.currency.clone(),
            });
        }
        
        // 验证交易状态有效
        match response.status.as_str() {
            "succeeded" | "pending" | "failed" => {}
            unknown => return Err(GatewayError::UnknownTransactionStatus(unknown.to_string())),
        }
        
        Ok(())
    }
    
    // 处理金额比较的浮点数精度问题
    fn is_amount_matching(&self, gateway_amount: f64, original_amount: f64) -> bool {
        (gateway_amount - original_amount).abs() < 0.01
    }
}

// 税务系统集成
pub struct TaxCalculationService {
    tax_provider: Arc<dyn TaxProvider>,
    address_validator: Arc<dyn AddressValidator>,
    product_catalog: Arc<dyn ProductCatalog>,
}

impl TaxCalculationService {
    pub async fn calculate_taxes(
        &self,
        order: &Order,
        shipping_address: &Address,
    ) -> Result<TaxCalculationResult, TaxCalculationError> {
        // 验证地址
        let validated_address = self.address_validator.validate(shipping_address).await
            .map_err(|e| TaxCalculationError::InvalidAddress(e.to_string()))?;
            
        // 准备税务计算请求
        let mut line_items = Vec::with_capacity(order.items().len());
        
        for item in order.items() {
            // 获取产品的税务分类
            let product = self.product_catalog.find_by_id(item.product_id()).await?
                .ok_or_else(|| TaxCalculationError::ProductNotFound(item.product_id().clone()))?;
                
            let tax_code = product.tax_code().unwrap_or("A_GEN_STANDARD");
            
            line_items.push(TaxLineItem {
                id: item.id().to_string(),
                product_code: item.product_id().to_string(),
                quantity: item.quantity(),
                unit_price: item.unit_price().value(),
                tax_code: tax_code.to_string(),
                discount_amount: item.discount_amount().map(|d| d.value()).unwrap_or(0.0),
            });
        }
        
        // 添加运费作为单独的税务项目
        if let Some(shipping_cost) = order.shipping_cost() {
            line_items.push(TaxLineItem {
                id: "shipping".to_string(),
                product_code: "SHIPPING",
                quantity: 1,
                unit_price: shipping_cost.value(),
                tax_code: "FR020100", // 运输服务的税务代码
                discount_amount: 0.0,
            });
        }
        
        // 调用税务提供商
        let calculation_request = TaxCalculationRequest {
            document_type: "SalesOrder".to_string(),
            transaction_id: order.id().to_string(),
            transaction_date: order.created_at().date().to_string(),
            customer_code: order.customer_id().to_string(),
            shipping_address: validated_address,
            line_items,
        };
        
        let tax_response = self.tax_provider.calculate_taxes(&calculation_request).await
            .map_err(|e| match e {
                TaxProviderError::RateLimitExceeded => TaxCalculationError::ProviderThrottled,
                TaxProviderError::ServiceUnavailable => TaxCalculationError::ProviderUnavailable,
                TaxProviderError::InvalidAddress => TaxCalculationError::InvalidAddress(
                    "Tax provider rejected address".to_string()
                ),
                _ => TaxCalculationError::ProviderError(e.to_string()),
            })?;
            
        // 转换响应为内部模型
        let result = self.map_provider_response(tax_response, order)?;
        
        Ok(result)
    }
    
    fn map_provider_response(
        &self,
        response: TaxProviderResponse,
        order: &Order,
    ) -> Result<TaxCalculationResult, TaxCalculationError> {
        // 验证响应
        if response.document_id != order.id().to_string() {
            return Err(TaxCalculationError::ResponseMismatch(
                format!("Transaction ID mismatch: {} vs {}", response.document_id, order.id())
            ));
        }
        
        // 创建税务明细条目
        let mut tax_lines = Vec::with_capacity(response.line_items.len());
        
        for line in response.line_items {
            let item_id = if line.line_id == "shipping" {
                None // 运费的特殊处理
            } else {
                Some(OrderItemId::from_string(&line.line_id)?)
            };
            
            tax_lines.push(TaxLine {
                item_id,
                tax_amount: Money::new(line.tax_amount, Currency::USD)?,
                tax_rate: line.tax_rate,
                tax_jurisdiction: line.jurisdiction,
                tax_name: line.tax_name,
            });
        }
        
        // 计算总税额
        let total_tax = tax_lines.iter()
            .fold(Money::zero(Currency::USD), |acc, line| {
                acc.add(&line.tax_amount).unwrap_or(acc)
            });
            
        Ok(TaxCalculationResult {
            total_tax,
            tax_lines,
            calculation_date: Utc::now(),
            provider_reference: response.document_code,
        })
    }
}
```

**映射分析**:

- 解耦内部领域模型和外部系统表示
- 适配和验证外部系统响应
- 处理外部系统的错误和异常情况
- 维护领域完整性的同时集成外部规则

### 2.4 不确定性与概率建模

处理现实世界中的不确定性：

```rust
// 风险评估模型
pub struct FraudRiskAssessor {
    risk_model: Arc<dyn RiskModel>,
    threshold_config: RiskThresholdConfig,
    fraud_repository: Arc<dyn FraudRepository>,
}

impl FraudRiskAssessor {
    pub async fn assess_transaction_risk(
        &self,
        transaction: &Transaction
    ) -> Result<RiskAssessment, AssessmentError> {
        // 收集风险因素
        let risk_factors = self.collect_risk_factors(transaction).await?;
        
        // 计算风险分数
        let risk_score = self.risk_model.calculate_risk_score(&risk_factors);
        
        // 根据分数确定风险级别
        let risk_level = self.determine_risk_level(risk_score);
        
        // 确定操作建议
        let recommendation = self.get_recommendation(risk_level, &risk_factors);
        
        // 创建评估结果
        let assessment = RiskAssessment {
            transaction_id: transaction.id.clone(),
            risk_score,
            risk_level,
            recommendation,
            risk_factors,
            assessed_at: Utc::now(),
        };
        
        // 保存评估结果
        self.fraud_repository.save_assessment(&assessment).await?;
        
        Ok(assessment)
    }
    
    async fn collect_risk_factors(&self, transaction: &Transaction) -> Result<Vec<RiskFactor>, AssessmentError> {
        let mut factors = Vec::new();
        
        // 检查IP地址与账单地址的地理位置匹配
        if let Some(ip_address) = &transaction.ip_address {
            if let Some(geo_mismatch) = self.check_ip_location_mismatch(ip_address, &transaction.billing_address).await? {
                factors.push(RiskFactor::GeoLocationMismatch(geo_mismatch));
            }
        }
        
        // 检查交易金额异常
        if let Some(amount_anomaly) = self.check_amount_anomaly(transaction).await? {
            factors.push(RiskFactor::AbnormalAmount(amount_anomaly));
        }
        
        // 检查设备是否为新设备
        if transaction.is_new_device {
            factors.push(RiskFactor::NewDevice {
                device_id: transaction.device_id.clone(),
                first_seen: transaction.timestamp,
            });
        }
        
        // 检查账户近期活动
        if let Some(velocity_factor) = self.check_transaction_velocity(transaction).await? {
            factors.push(velocity_factor);
        }
        
        // 其他风险因素检查...
        
        Ok(factors)
    }
    
    fn determine_risk_level(&self, risk_score: f64) -> RiskLevel {
        if risk_score >= self.threshold_config.high_risk_threshold {
            RiskLevel::High
        } else if risk_score >= self.threshold_config.medium_risk_threshold {
            RiskLevel::Medium
        } else {
            RiskLevel::Low
        }
    }
    
    fn get_recommendation(&self, risk_level: RiskLevel, factors: &[RiskFactor]) -> Recommendation {
        match risk_level {
            RiskLevel::High => {
                // 检查是否含有某些高风险因素的组合
                let has_geo_mismatch = factors.iter().any(|f| matches!(f, RiskFactor::GeoLocationMismatch(_)));
                let has_amount_anomaly = factors.iter().any(|f| matches!(f, RiskFactor::AbnormalAmount(_)));
                
                if has_geo_mismatch && has_amount_anomaly {
                    Recommendation::Reject
                } else {
                    Recommendation::ManualReview
                }
            },
            RiskLevel::Medium => {
                // 中等风险通常需要额外验证
                Recommendation::AdditionalVerification
            },
            RiskLevel::Low => {
                // 低风险直接通过
                Recommendation::Approve
            }
        }
    }
    
    async fn check_ip_location_mismatch(
        &self,
        ip_address: &str,
        billing_address: &Address
    ) -> Result<Option<GeoMismatch>, AssessmentError> {
        // 使用地理位置服务获取IP位置
        let ip_location = self.get_ip_location(ip_address).await?;
        
        // 使用地址验证服务获取账单地址位置
        let billing_location = self.get_address_location(billing_address).await?;
        
        // 计算两个位置之间的距离
        let distance = self.calculate_distance(&ip_location, &billing_location);
        
        // 如果距离超过阈值，视为不匹配
        if distance > self.threshold_config.ip_location_mismatch_km {
            Ok(Some(GeoMismatch {
                ip_country: ip_location.country,
                billing_country: billing_location.country,
                distance_km: distance,
            }))
        } else {
            Ok(None)
        }
    }
    
    // 其他风险评估方法...
}

// 库存预测模型
pub struct InventoryForecaster {
    sales_repository: Arc<dyn SalesRepository>,
    inventory_repository: Arc<dyn InventoryRepository>,
    forecast_model: Arc<dyn ForecastModel>,
}

impl InventoryForecaster {
    pub async fn generate_forecast(
        &self,
        product_id: &ProductId,
        forecast_period: ForecastPeriod,
    ) -> Result<InventoryForecast, ForecastError> {
        // 获取历史销售数据
        let sales_history = self.sales_repository
            .get_product_sales_history(product_id, forecast_period.history_window)
            .await?;
            
        // 获取当前库存水平
        let current_inventory = self.inventory_repository
            .get_current_level(product_id)
            .await?
            .ok_or_else(|| ForecastError::ProductNotFound(product_id.clone()))?;
            
        // 获取已知的未来供应
        let future_supply = self.inventory_repository
            .get_expected_supply(product_id, forecast_period.forecast_window)
            .await?;
            
        // 执行需求预测
        let demand_forecast = self.forecast_model.forecast_demand(
            &sales_history,
            forecast_period.forecast_window,
        )?;
        
        // 计算库存预测
        let mut inventory_levels = Vec::with_capacity(forecast_period.forecast_window.num_days() as usize);
        let mut current_level = current_inventory.available_quantity;
        let start_date = Utc::now().date();
        
        for day in 0..forecast_period.forecast_window.num_days() {
            let forecast_date = start_date + Duration::days(day);
            
            // 获取当天预测需求
            let daily_demand = demand_forecast.get_daily_demand(&forecast_date);
            
            // 添加当天的预期供应
            let daily_supply = future_supply.iter()
                .filter(|supply| supply.expected_date.date() == forecast_date)
                .map(|supply| supply.quantity)
                .sum::<u32>();
                
            // 更新库存水平
            current_level = current_level.saturating_sub(daily_demand) + daily_supply;
            
            // 记录预测
            inventory_levels.push(DailyInventoryForecast {
                date: forecast_date,
                expected_demand: daily_demand,
                expected_supply: daily_supply,
                projected_level: current_level,
                status: self.determine_inventory_status(
                    current_level

```rust
                    current_level,
                    current_inventory.reorder_point,
                    current_inventory.safety_stock,
                ),
            });
        }
        
        // 计算预测统计信息
        let stockout_days = inventory_levels.iter()
            .filter(|day| day.status == InventoryStatus::StockOut)
            .count();
            
        let stockout_probability = stockout_days as f64 / inventory_levels.len() as f64;
        
        let avg_inventory_level = inventory_levels.iter()
            .map(|day| day.projected_level as f64)
            .sum::<f64>() / inventory_levels.len() as f64;
            
        // 创建最终预测
        let forecast = InventoryForecast {
            product_id: product_id.clone(),
            current_level: current_inventory.available_quantity,
            reorder_point: current_inventory.reorder_point,
            safety_stock: current_inventory.safety_stock,
            daily_forecasts: inventory_levels,
            stockout_probability,
            avg_inventory_level,
            forecast_generated_at: Utc::now(),
        };
        
        Ok(forecast)
    }
    
    fn determine_inventory_status(
        &self,
        projected_level: u32,
        reorder_point: u32,
        safety_stock: u32,
    ) -> InventoryStatus {
        if projected_level == 0 {
            InventoryStatus::StockOut
        } else if projected_level < safety_stock {
            InventoryStatus::Critical
        } else if projected_level < reorder_point {
            InventoryStatus::LowStock
        } else {
            InventoryStatus::Adequate
        }
    }
    
    pub async fn recommend_reorder(
        &self,
        product_id: &ProductId,
        forecast_period: ForecastPeriod,
    ) -> Result<ReorderRecommendation, ForecastError> {
        // 生成库存预测
        let forecast = self.generate_forecast(product_id, forecast_period).await?;
        
        // 获取产品信息
        let product = self.inventory_repository
            .get_product_details(product_id)
            .await?
            .ok_or_else(|| ForecastError::ProductNotFound(product_id.clone()))?;
            
        // 判断是否需要补货
        let needs_reorder = forecast.daily_forecasts.iter()
            .any(|day| day.status == InventoryStatus::LowStock || 
                 day.status == InventoryStatus::Critical);
                 
        if !needs_reorder {
            return Ok(ReorderRecommendation {
                product_id: product_id.clone(),
                recommendation: ReorderDecision::NoActionNeeded,
                recommended_quantity: 0,
                expected_stockout_date: None,
                confidence_level: 0.95,
                reorder_reasons: vec![],
            });
        }
        
        // 找到第一个低库存或缺货的日期
        let first_low_stock_day = forecast.daily_forecasts.iter()
            .find(|day| day.status == InventoryStatus::LowStock || 
                 day.status == InventoryStatus::Critical)
            .unwrap(); // 安全，因为我们已经检查过存在低库存天
            
        // 计算从现在到低库存日期的天数
        let days_until_low = (first_low_stock_day.date - Utc::now().date()).num_days();
        
        // 找到第一个缺货的日期（如果有）
        let expected_stockout_date = forecast.daily_forecasts.iter()
            .find(|day| day.status == InventoryStatus::StockOut)
            .map(|day| day.date);
            
        // 计算建议的订购数量
        let lead_time_demand = self.calculate_lead_time_demand(
            &forecast, 
            product.lead_time_days as usize
        );
        
        let recommended_quantity = (lead_time_demand * (1.0 + product.safety_factor)) as u32;
        
        // 生成补货建议原因
        let mut reorder_reasons = Vec::new();
        
        if forecast.stockout_probability > 0.05 {
            reorder_reasons.push(ReorderReason::HighStockoutRisk(forecast.stockout_probability));
        }
        
        if days_until_low < product.lead_time_days as i64 {
            reorder_reasons.push(ReorderReason::LeadTimeRisk {
                days_until_low_stock: days_until_low,
                lead_time_days: product.lead_time_days,
            });
        }
        
        // 确定补货决策
        let decision = if days_until_low <= 0 {
            ReorderDecision::OrderImmediately
        } else if days_until_low < product.lead_time_days as i64 {
            ReorderDecision::OrderSoon
        } else {
            ReorderDecision::PlanForReorder
        };
        
        // 创建补货建议
        let recommendation = ReorderRecommendation {
            product_id: product_id.clone(),
            recommendation: decision,
            recommended_quantity,
            expected_stockout_date,
            confidence_level: 0.95 - forecast.stockout_probability,
            reorder_reasons,
        };
        
        Ok(recommendation)
    }
    
    fn calculate_lead_time_demand(&self, forecast: &InventoryForecast, lead_time_days: usize) -> f64 {
        // 计算未来提前期内的总需求
        let lead_time_demand = forecast.daily_forecasts.iter()
            .take(lead_time_days)
            .map(|day| day.expected_demand as f64)
            .sum::<f64>();
            
        lead_time_demand
    }
}
```

**映射分析**:

- 风险评估模型捕捉不同风险因素及其权重
- 库存预测结合历史数据与统计建模
- 实现概率阈值的决策逻辑
- 反映现实世界的不确定性和可变性

### 2.5 法规与合规约束

法规和合规规则的代码表示：

```rust
// 个人数据处理合规
pub struct PersonalDataProcessor {
    data_repository: Arc<dyn PersonalDataRepository>,
    consent_manager: Arc<dyn ConsentManager>,
    audit_logger: Arc<dyn AuditLogger>,
    retention_policy: RetentionPolicy,
}

impl PersonalDataProcessor {
    pub async fn store_personal_data(
        &self,
        data: PersonalData,
        consent_reference: &ConsentReference,
        request_context: &RequestContext,
    ) -> Result<(), DataProcessingError> {
        // 验证是否有合法的处理依据
        self.validate_processing_basis(data.kind(), consent_reference).await?;
        
        // 验证数据最小化
        self.validate_data_minimization(&data)?;
        
        // 记录处理活动
        self.audit_logger.log_processing_activity(
            ProcessingActivity::Store,
            &data.subject_id,
            data.kind(),
            request_context,
        ).await?;
        
        // 计算保留期限
        let retention_period = self.retention_policy.get_retention_period(data.kind());
        let expiration = Utc::now() + retention_period;
        
        // 存储数据，带元数据
        let data_record = PersonalDataRecord {
            data,
            metadata: DataMetadata {
                processing_basis: consent_reference.clone(),
                collected_at: Utc::now(),
                expires_at: expiration,
                purpose: request_context.purpose.clone(),
                controller: request_context.controller.clone(),
            },
        };
        
        self.data_repository.store(&data_record).await?;
        
        Ok(())
    }
    
    pub async fn retrieve_personal_data(
        &self,
        subject_id: &SubjectId,
        data_kind: DataKind,
        request_context: &RequestContext,
    ) -> Result<Option<PersonalData>, DataProcessingError> {
        // 验证访问权限
        self.validate_access_rights(subject_id, data_kind, request_context).await?;
        
        // 检索数据
        let data_record = match self.data_repository.find(subject_id, data_kind).await? {
            Some(record) => record,
            None => return Ok(None),
        };
        
        // 验证数据是否过期
        if data_record.metadata.expires_at < Utc::now() {
            return Err(DataProcessingError::DataExpired {
                subject_id: subject_id.clone(),
                data_kind,
                expired_at: data_record.metadata.expires_at,
            });
        }
        
        // 验证原始处理目的与当前请求目的是否兼容
        if !self.is_purpose_compatible(&data_record.metadata.purpose, &request_context.purpose) {
            return Err(DataProcessingError::IncompatiblePurpose {
                original_purpose: data_record.metadata.purpose.clone(),
                requested_purpose: request_context.purpose.clone(),
            });
        }
        
        // 记录访问活动
        self.audit_logger.log_processing_activity(
            ProcessingActivity::Retrieve,
            subject_id,
            data_kind,
            request_context,
        ).await?;
        
        Ok(Some(data_record.data))
    }
    
    pub async fn delete_personal_data(
        &self,
        subject_id: &SubjectId,
        request_context: &RequestContext,
    ) -> Result<DeletionReport, DataProcessingError> {
        // 验证删除权限
        self.validate_deletion_rights(subject_id, request_context).await?;
        
        // 查找所有相关数据
        let data_records = self.data_repository.find_all_by_subject(subject_id).await?;
        
        if data_records.is_empty() {
            return Ok(DeletionReport {
                subject_id: subject_id.clone(),
                deleted_items: 0,
                exempted_items: 0,
                exemption_reasons: HashMap::new(),
                deleted_at: Utc::now(),
            });
        }
        
        // 预备删除报告
        let mut deleted_items = 0;
        let mut exempted_items = 0;
        let mut exemption_reasons: HashMap<DataKind, ExemptionReason> = HashMap::new();
        
        // 处理每条记录
        for record in data_records {
            // 检查是否有删除豁免
            if let Some(reason) = self.check_deletion_exemption(&record, request_context).await? {
                exempted_items += 1;
                exemption_reasons.insert(record.data.kind(), reason);
                continue;
            }
            
            // 记录删除活动
            self.audit_logger.log_processing_activity(
                ProcessingActivity::Delete,
                subject_id,
                record.data.kind(),
                request_context,
            ).await?;
            
            // 执行删除
            self.data_repository.delete(subject_id, record.data.kind()).await?;
            deleted_items += 1;
        }
        
        // 创建删除报告
        let report = DeletionReport {
            subject_id: subject_id.clone(),
            deleted_items,
            exempted_items,
            exemption_reasons,
            deleted_at: Utc::now(),
        };
        
        Ok(report)
    }
    
    async fn validate_processing_basis(
        &self,
        data_kind: DataKind,
        consent_reference: &ConsentReference,
    ) -> Result<(), DataProcessingError> {
        match consent_reference {
            ConsentReference::ExplicitConsent { consent_id, purposes } => {
                // 验证同意是否存在且有效
                let consent = self.consent_manager.verify_consent(consent_id).await?
                    .ok_or(DataProcessingError::InvalidConsent(consent_id.clone()))?;
                    
                // 验证同意是否包含当前数据类型
                if !consent.data_categories.contains(&data_kind) {
                    return Err(DataProcessingError::ConsentScopeViolation {
                        data_kind,
                        consent_id: consent_id.clone(),
                    });
                }
                
                // 验证同意是否包含所有请求的目的
                for purpose in purposes {
                    if !consent.purposes.contains(purpose) {
                        return Err(DataProcessingError::ConsentScopeViolation {
                            data_kind,
                            consent_id: consent_id.clone(),
                        });
                    }
                }
                
                // 验证同意是否已过期
                if let Some(expiry) = consent.expires_at {
                    if expiry < Utc::now() {
                        return Err(DataProcessingError::ExpiredConsent {
                            consent_id: consent_id.clone(),
                            expired_at: expiry,
                        });
                    }
                }
            }
            
            ConsentReference::LegitimateInterest { interest, balancing_record } => {
                // 验证合法利益的适当性
                if !self.is_legitimate_interest_applicable(data_kind, interest) {
                    return Err(DataProcessingError::InvalidLegitimateInterest {
                        data_kind,
                        interest: interest.clone(),
                    });
                }
                
                // 验证利益平衡测试是否已完成
                if balancing_record.is_empty() {
                    return Err(DataProcessingError::MissingBalancingTest {
                        data_kind,
                        interest: interest.clone(),
                    });
                }
            }
            
            ConsentReference::LegalObligation { regulation, provision } => {
                // 验证法律义务的适用性
                if !self.is_legal_obligation_applicable(data_kind, regulation, provision) {
                    return Err(DataProcessingError::InvalidLegalBasis {
                        data_kind,
                        regulation: regulation.clone(),
                        provision: provision.clone(),
                    });
                }
            }
            
            // 其他处理依据的验证...
        }
        
        Ok(())
    }
    
    fn validate_data_minimization(&self, data: &PersonalData) -> Result<(), DataProcessingError> {
        // 针对每种数据类型实施数据最小化规则
        match data.kind() {
            DataKind::EmailAddress => {
                // 电子邮件地址不需要额外验证
                Ok(())
            }
            
            DataKind::PhoneNumber => {
                // 检查电话号码格式是否标准化
                if !is_phone_number_normalized(&data.value) {
                    return Err(DataProcessingError::DataMinimizationViolation(
                        "电话号码应标准化格式存储".into()
                    ));
                }
                Ok(())
            }
            
            DataKind::Address => {
                // 检查地址是否包含必要字段
                if !is_address_complete(&data.value) {
                    return Err(DataProcessingError::DataMinimizationViolation(
                        "地址必须包含所有必要字段".into()
                    ));
                }
                Ok(())
            }
            
            DataKind::DateOfBirth => {
                // 对于某些目的，可能只需要存储年龄而非具体出生日期
                if data.metadata.get("requires_full_dob").map_or(false, |v| v == "false") {
                    return Err(DataProcessingError::DataMinimizationViolation(
                        "此用途只需存储年龄，不需要完整出生日期".into()
                    ));
                }
                Ok(())
            }
            
            DataKind::FinancialInformation => {
                // 检查是否包含过多财务信息
                if data.value.contains("account_number") && 
                   !data.metadata.get("requires_account_number").map_or(false, |v| v == "true") {
                    return Err(DataProcessingError::DataMinimizationViolation(
                        "不应收集完整账号，除非明确需要".into()
                    ));
                }
                Ok(())
            }
            
            // 其他数据类型的最小化规则...
            _ => Ok(()),
        }
    }
    
    // 其他验证方法...
    
    fn is_purpose_compatible(&self, original_purpose: &ProcessingPurpose, current_purpose: &ProcessingPurpose) -> bool {
        // 如果目的完全相同，则兼容
        if original_purpose == current_purpose {
            return true;
        }
        
        // 检查当前目的是否是原始目的的子集
        match (original_purpose, current_purpose) {
            (ProcessingPurpose::Marketing { channels: orig_channels, .. }, 
             ProcessingPurpose::Marketing { channels: curr_channels, .. }) => {
                // 营销目的兼容性：当前渠道必须是原始渠道的子集
                curr_channels.iter().all(|c| orig_channels.contains(c))
            }
            
            (ProcessingPurpose::ServiceProvision { services: orig_services, .. },
             ProcessingPurpose::ServiceProvision { services: curr_services, .. }) => {
                // 服务提供目的兼容性：当前服务必须是原始服务的子集
                curr_services.iter().all(|s| orig_services.contains(s))
            }
            
            (ProcessingPurpose::LegalCompliance { .. }, 
             ProcessingPurpose::LegalCompliance { .. }) => {
                // 法律合规目的通常被视为兼容
                true
            }
            
            (ProcessingPurpose::Analytics { aggregated: true, .. },
             ProcessingPurpose::Analytics { .. }) => {
                // 聚合分析可以用于任何分析目的
                true
            }
            
            // 其他目的组合的兼容性规则...
            
            _ => false, // 默认认为不同类型的目的不兼容
        }
    }
    
    async fn check_deletion_exemption(
        &self,
        record: &PersonalDataRecord,
        request_context: &RequestContext,
    ) -> Result<Option<ExemptionReason>, DataProcessingError> {
        // 检查法律保留义务
        if let Some(legal_hold) = self.retention_policy.get_legal_hold(&record.data.subject_id).await? {
            if legal_hold.applies_to(record.data.kind()) {
                return Ok(Some(ExemptionReason::LegalHold {
                    reference: legal_hold.reference.clone(),
                    expires_at: legal_hold.expires_at,
                }));
            }
        }
        
        // 检查法规要求的最低保留期
        let min_retention = self.retention_policy.get_minimum_retention(record.data.kind());
        let min_retention_date = record.metadata.collected_at + min_retention;
        
        if min_retention_date > Utc::now() {
            return Ok(Some(ExemptionReason::RegulatoryRequirement {
                regulation: self.retention_policy.get_regulation_reference(record.data.kind()),
                retain_until: min_retention_date,
            }));
        }
        
        // 检查业务关键数据
        if self.is_business_critical(record, request_context) {
            return Ok(Some(ExemptionReason::BusinessCritical {
                justification: "需要保留用于核心业务记录".into(),
                review_date: Utc::now() + Duration::days(90),
            }));
        }
        
        // 无豁免理由
        Ok(None)
    }
    
    // 其他辅助方法...
}
```

**映射分析**:

- 实现数据保护原则（同意、数据最小化、目的限制）
- 合规处理流程中的验证和审计跟踪
- 保留期限和删除权限的管理
- 法规兼容的异常处理机制

### 2.6 经济模型和价值计算

经济因素在代码中的表示：

```rust
// 定价引擎
pub struct DynamicPricingEngine {
    product_repository: Arc<dyn ProductRepository>,
    market_data_service: Arc<dyn MarketDataService>,
    pricing_rules: Arc<PricingRuleEngine>,
    config: PricingConfig,
}

impl DynamicPricingEngine {
    pub async fn calculate_price(
        &self,
        product_id: &ProductId,
        customer_context: &CustomerContext,
        market_context: &MarketContext,
    ) -> Result<PriceCalculation, PricingError> {
        // 获取产品基本信息
        let product = self.product_repository.find_by_id(product_id).await?
            .ok_or_else(|| PricingError::ProductNotFound(product_id.clone()))?;
            
        // 获取成本数据
        let cost_data = self.product_repository.get_cost_data(product_id).await?
            .ok_or_else(|| PricingError::CostDataUnavailable(product_id.clone()))?;
            
        // 获取市场数据
        let market_data = match self.market_data_service.get_market_data(
            product_id,
            &market_context.market_id,
            &market_context.location,
        ).await {
            Ok(data) => Some(data),
            Err(MarketDataError::DataUnavailable) => None,
            Err(e) => return Err(PricingError::MarketDataError(e.to_string())),
        };
        
        // 计算基础价格
        let base_price = self.calculate_base_price(&product, &cost_data);
        
        // 应用市场调整
        let market_adjusted_price = self.apply_market_adjustments(
            base_price,
            &product,
            market_data.as_ref(),
            market_context,
        );
        
        // 计算客户特定价格
        let customer_adjusted_price = self.apply_customer_adjustments(
            market_adjusted_price,
            &product,
            customer_context,
        );
        
        // 应用促销和折扣
        let (final_price, applied_promotions) = self.apply_promotions(
            customer_adjusted_price,
            &product,
            customer_context,
            market_context,
        ).await?;
        
        // 验证利润边界
        self.validate_profit_margins(final_price, &cost_data)?;
        
        // 创建完整价格计算
        let calculation = PriceCalculation {
            product_id: product_id.clone(),
            base_price,
            market_adjusted_price,
            customer_adjusted_price,
            final_price,
            cost_components: cost_data.components.clone(),
            applied_promotions,
            calculation_time: Utc::now(),
            valid_until: Utc::now() + self.config.price_validity_duration,
        };
        
        Ok(calculation)
    }
    
    fn calculate_base_price(&self, product: &Product, cost_data: &CostData) -> Money {
        // 基础计算：成本 + 目标利润率
        let cost_sum = cost_data.components.iter()
            .map(|c| c.amount.value())
            .sum::<f64>();
            
        let target_margin = product.pricing_strategy.target_margin;
        let margin_multiplier = 1.0 / (1.0 - target_margin);
        
        // 基础价格 = 成本 / (1 - 目标利润率)
        let base_price_value = cost_sum * margin_multiplier;
        
        Money::new(base_price_value, cost_data.components[0].amount.currency().clone())
            .unwrap_or_else(|_| Money::zero(cost_data.components[0].amount.currency().clone()))
    }
    
    fn apply_market_adjustments(
        &self,
        base_price: Money,
        product: &Product,
        market_data: Option<&MarketData>,
        market_context: &MarketContext,
    ) -> Money {
        let mut price = base_price;
        
        // 应用市场位置调整
        if let Some(location_adjustment) = product.pricing_strategy.location_adjustments
            .get(&market_context.location) {
            price = match location_adjustment {
                PriceAdjustment::Percentage(pct) => {
                    price * (1.0 + pct)
                },
                PriceAdjustment::FixedAmount(amt) => {
                    price + amt.clone()
                },
            };
        }
        
        // 根据市场数据调整价格
        if let Some(market_data) = market_data {
            // 竞争者定价影响
            if let Some(competitor_adjustment) = self.calculate_competitor_adjustment(
                &price,
                &product.pricing_strategy.competitor_response,
                &market_data.competitor_prices,
            ) {
                price = competitor_adjustment;
            }
            
            // 需求弹性调整
            if let Some(elasticity_adjustment) = self.calculate_elasticity_adjustment(
                &price,
                product,
                market_data,
            ) {
                price = elasticity_adjustment;
            }
            
            // 市场趋势调整
            if let Some(trend_adjustment) = self.calculate_trend_adjustment(
                &price,
                &market_data.pricing_trends,
            ) {
                price = trend_adjustment;
            }
        }
        
        // 应用季节性调整
        if let Some(seasonal_adjustment) = self.calculate_seasonal_adjustment(
            &price,
            &product.pricing_strategy.seasonal_adjustments,
            &market_context.current_date,
        ) {
            price = seasonal_adjustment;
        }
        
        price
    }
    
    fn apply_customer_adjustments(
        &self,
        market_price: Money,
        product: &Product,
        customer_context: &CustomerContext,
    ) -> Money {
        let mut price = market_price;
        
        // 应用客户段调整
        if let Some(segment_adjustment) = product.pricing_strategy.segment_adjustments
            .get(&customer_context.segment) {
            price = match segment_adjustment {
                PriceAdjustment::Percentage(pct) => {
                    price * (1.0 + pct)
                },
                PriceAdjustment::FixedAmount(amt) => {
                    price + amt.clone()
                },
            };
        }
        
        // 应用客户特定定价（如合同价格）
        if let Some(customer_id) = &customer_context.customer_id {
            if let Some(contract_price) = product.contract_prices.get(customer_id) {
                return contract_price.clone();
            }
        }
        
        // 应用数量折扣
        if let Some(quantity) = customer_context.quantity {
            if let Some(volume_discount) = self.calculate_volume_discount(
                &price,
                quantity,
                &product.pricing_strategy.volume_discounts,
            ) {
                price = volume_discount;
            }
        }
        
        // 应用忠诚度调整
        if let Some(loyalty_level) = &customer_context.loyalty_level {
            if let Some(loyalty_discount) = product.pricing_strategy.loyalty_discounts
                .get(loyalty_level) {
                price = price * (1.0 - loyalty_discount);
            }
        }
        
        price
    }
    
    async fn apply_promotions(
        &self,
        customer_price: Money,
        product: &Product,
        customer_context: &CustomerContext,
        market_context: &MarketContext,
    ) -> Result<(Money, Vec<AppliedPromotion>), PricingError> {
        let mut price = customer_price;
        let mut applied_promotions = Vec::new();
        
        // 获取适用的促销活动
        let applicable_promotions = self.pricing_rules
            .find_applicable_promotions(
                &product.id,
                customer_context,
                market_context,
            )
            .await?;
            
        // 应用每个促销活动
        for promotion in applicable_promotions {
            let original_price = price.clone();
            
            price = match &promotion.discount {
                PromotionDiscount::Percentage(pct) => {
                    price * (1.0 - pct)
                },
                PromotionDiscount::FixedAmount(amt) => {
                    price - amt.clone().min(price.clone())
                },
                PromotionDiscount::PriceOverride(override_price) => {
                    override_price.clone()
                },
            };
            
            // 记录已应用的促销
            applied_promotions.push(AppliedPromotion {
                promotion_id: promotion.id.clone(),
                promotion_name: promotion.name.clone(),
                discount_type: promotion.discount.type_name().to_string(),
                discount_value: match &promotion.discount {
                    PromotionDiscount::Percentage(pct) => format!("{:.2}%", pct * 100.0),
                    PromotionDiscount::FixedAmount(amt) => amt.to_string(),
                    PromotionDiscount::PriceOverride(override_price) => override_price.to_string(),
                },
                original_price,
                discounted_price: price.clone(),
            });
        }
        
        Ok((price, applied_promotions))
    }
    
    fn validate_profit_margins(&self, final_price: Money, cost_data: &CostData) -> Result<(), PricingError> {
        // 计算总成本
        let total_cost = cost_data.components.iter()
            .map(|c| c.amount.value())
            .sum::<f64>();
            
        // 计算利润率
        let margin = 1.0 - (total_cost / final_price.value());
        
        // 检查最低利润率
        if margin < self.config.minimum_margin {
            return Err(PricingError::BelowMinimumMargin {
                minimum_margin: self.config.minimum_margin,
                calculated_margin: margin,
            });
        }
        
        // 检查最高利润率（防止过度定价）
        if margin > self.config.maximum_margin {
            return Err(PricingError::AboveMaximumMargin {
                maximum_margin: self.config.maximum_margin,
                calculated_margin: margin,
            });
        }
        
        Ok(())
    }
    
    // 专门的调整计算方法...
}

// 订阅计费系统
pub struct SubscriptionBillingEngine {
    subscription_repository: Arc<dyn SubscriptionRepository>,
    payment_processor: Arc<dyn PaymentProcessor>,
    invoice_repository: Arc<dyn InvoiceRepository>,
    proration_calculator: ProrationCalculator,
}

impl SubscriptionBillingEngine {
    pub async fn generate_invoice(
        &self,
        subscription_id: &SubscriptionId,
        billing_period: DateRange,
    ) -> Result<Invoice, BillingError> {
        // 获取订阅信息
        let subscription = self.subscription_repository.find_by_id(subscription_id).await?
            .ok_or_else(|| BillingError::SubscriptionNotFound(subscription_id.clone()))?;
            
        // 验证订阅状态
        if subscription.status != SubscriptionStatus::Active {
            return Err(BillingError::InactiveSubscription {
                subscription_id: subscription_id.clone(),
                status: subscription.status,
            });
        }
        
        // 计算基本订阅费用
        let base_charge = self.calculate_base_charge(&subscription, &billing_period)?;
        
        // 计算用量费用
        let usage_charges = self.calculate_usage_charges(&subscription, &billing_period).await?;
        
        // 计算一次性费用
        let one_time_charges = self.calculate_one_time_charges(&subscription, &billing_period).await?;
        
        // 计算调整项
        let adjustments = self.calculate_adjustments(&subscription, &billing_period).await?;
        
        // 计算税费
        let taxes = self.calculate_taxes(
            &base_charge,
            &usage_charges,
            &one_time_charges,
            &adjustments,
            &subscription.customer_tax_info,
        ).await?;
        
        // 计算总额
        let subtotal = base_charge.amount +
            usage_charges.iter().map(|c| c.amount.clone()).sum::<Money>() +
            one_time_charges.iter().map(|c| c.amount.clone()).sum::<Money>() +
            adjustments.iter().map(|a| a.amount.clone()).sum::<Money>();
            
        let total = subtotal.clone() + taxes.iter().map(|t| t.amount.clone()).sum::<Money>();
        
        // 创建发票
        let invoice = Invoice {
            id: InvoiceId::new(),
            subscription_id: subscription_id.clone(),
            customer_id: subscription.customer_id.clone(),
            billing_period: billing_period.clone(),
            issue_date: Utc::now(),
            due_date: Utc::now() + Duration::days(subscription.payment_terms.due_days as i64),
            base_charge,
            usage_charges,
            one_time_charges,
            adjustments,
            taxes,
            subtotal,
            total,
            status: InvoiceStatus::Draft,
        };
        
        // 保存发票
        self.invoice_repository.save(&invoice).await?;
        
        Ok(invoice)
    }
    
    pub async fn finalize_invoice(
        &self,
        invoice_id: &InvoiceId,
    ) -> Result<Invoice, BillingError> {
        // 获取发票
        let mut invoice = self.invoice_repository.find_by_id(invoice_id).await?
            .ok_or_else(|| BillingError::InvoiceNotFound(invoice_id.clone()))?;
            
        // 检查发票状态
        if invoice.status != InvoiceStatus::Draft {
            return Err(BillingError::InvalidInvoiceStatus {
                invoice_id: invoice_id.clone(),
                current_status: invoice.status,
                expected_status: InvoiceStatus::Draft,
            });
        }
        
        // 更新发票状态
        invoice.status = InvoiceStatus::Issued;
        
        // 保存更新的发票
        self.invoice_repository.save(&invoice).await?;
        
        Ok(invoice)
    }
    
    pub async fn charge_invoice(
        &self,
        invoice_id: &InvoiceId,
    ) -> Result<PaymentResult, BillingError> {
        // 获取发票
        let mut invoice = self.invoice_repository.find_by_id(invoice_id).await?
            .ok_or_else(|| BillingError::InvoiceNotFound(invoice_id.clone()))?;
            
        // 检查发票状态
        if invoice.status != InvoiceStatus::Issued {
            return Err(BillingError::InvalidInvoiceStatus {
                invoice_id: invoice_id.clone(),
                current_status: invoice.status,
                expected_status: InvoiceStatus::Issued,
            });
        }
        
        // 获取订阅
        let subscription = self.subscription_repository.find_by_id(&invoice.subscription_id).await?
            .ok_or_else(|| BillingError::SubscriptionNotFound(invoice.subscription_id.clone()))?;
            
        // 准备支付请求
        let payment_request = PaymentRequest {
            amount: invoice.total.clone(),
            payment_method_id: subscription.default_payment_method.clone(),
            customer_id: subscription.customer_id.clone(),
            description: format!("Invoice {} for subscription {}", 
                invoice.id, invoice.subscription_id),
            metadata: HashMap::from([
                ("invoice_id".to_string(), invoice.id.to_string()),
                ("subscription_id".to_string(), invoice.subscription_id.to_string()),
            ]),
        };
        
        // 处理支付
        let payment_result = self.payment_processor.process_payment(&payment_request).await
            .map_err(|e| BillingError::PaymentProcessingError(e.to_string()))?;
            
        // 更新发票状态
        invoice.status = match payment_result.status {
            PaymentStatus::Succeeded =>

```rust
            PaymentStatus::Succeeded => InvoiceStatus::Paid,
            PaymentStatus::Failed => InvoiceStatus::PaymentFailed,
            PaymentStatus::Pending => InvoiceStatus::PaymentPending,
        };
        
        invoice.payment_id = Some(payment_result.payment_id.clone());
        invoice.paid_at = if payment_result.status == PaymentStatus::Succeeded {
            Some(Utc::now())
        } else {
            None
        };
        
        // 保存更新的发票
        self.invoice_repository.save(&invoice).await?;
        
        Ok(payment_result)
    }
    
    fn calculate_base_charge(
        &self,
        subscription: &Subscription,
        billing_period: &DateRange,
    ) -> Result<InvoiceLineItem, BillingError> {
        let plan = &subscription.plan;
        
        // 计算周期天数
        let period_days = (billing_period.end - billing_period.start).num_days();
        
        // 对于月度或年度计划，计算每日费率
        let daily_rate = match plan.billing_interval {
            BillingInterval::Monthly => {
                plan.base_price.value() / 30.0 // 简化计算，使用30天
            },
            BillingInterval::Annual => {
                plan.base_price.value() / 365.0
            },
            BillingInterval::Weekly => {
                plan.base_price.value() / 7.0
            },
            BillingInterval::Daily => {
                plan.base_price.value()
            },
        };
        
        // 计算基本费用
        let amount = Money::new(
            daily_rate * period_days as f64,
            plan.base_price.currency().clone(),
        )?;
        
        Ok(InvoiceLineItem {
            description: format!("{} Plan - Base Subscription", plan.name),
            quantity: 1,
            unit_price: plan.base_price.clone(),
            amount,
            item_type: InvoiceItemType::SubscriptionFee,
        })
    }
    
    async fn calculate_usage_charges(
        &self,
        subscription: &Subscription,
        billing_period: &DateRange,
    ) -> Result<Vec<InvoiceLineItem>, BillingError> {
        let mut charges = Vec::new();
        
        // 获取每个计量组件的使用量
        for component in &subscription.plan.metered_components {
            // 查询计量服务获取使用数据
            let usage_data = self.subscription_repository
                .get_usage_data(
                    &subscription.id,
                    &component.id,
                    billing_period,
                )
                .await?;
                
            // 应用计量组件的定价模型
            let amount = match &component.pricing_model {
                MeteredPricingModel::PerUnit { unit_price } => {
                    let total_units = usage_data.total_usage;
                    Money::new(
                        unit_price.value() * total_units as f64,
                        unit_price.currency().clone(),
                    )?
                },
                
                MeteredPricingModel::Tiered { tiers } => {
                    let total_units = usage_data.total_usage;
                    
                    // 按层级计算价格
                    let mut remaining_units = total_units;
                    let mut total_price = 0.0;
                    let currency = tiers[0].unit_price.currency().clone();
                    
                    for tier in tiers {
                        let units_in_tier = if let Some(max) = tier.max_units {
                            remaining_units.min(max - tier.min_units + 1)
                        } else {
                            remaining_units
                        };
                        
                        total_price += tier.unit_price.value() * units_in_tier as f64;
                        remaining_units -= units_in_tier;
                        
                        if remaining_units == 0 {
                            break;
                        }
                    }
                    
                    Money::new(total_price, currency)?
                },
                
                MeteredPricingModel::Volume { tiers } => {
                    let total_units = usage_data.total_usage;
                    let currency = tiers[0].unit_price.currency().clone();
                    
                    // 找到适用的层级
                    let applicable_tier = tiers.iter()
                        .find(|tier| {
                            total_units >= tier.min_units && 
                            (tier.max_units.is_none() || total_units <= tier.max_units.unwrap())
                        })
                        .ok_or_else(|| BillingError::PricingModelError(
                            "No applicable tier found for usage".into()
                        ))?;
                        
                    Money::new(
                        applicable_tier.unit_price.value() * total_units as f64,
                        currency,
                    )?
                },
            };
            
            // 只有在有费用时才添加行项目
            if amount.value() > 0.0 {
                charges.push(InvoiceLineItem {
                    description: format!("{} - Usage ({} {})", 
                        component.name, 
                        usage_data.total_usage,
                        component.unit_label),
                    quantity: usage_data.total_usage,
                    unit_price: match &component.pricing_model {
                        MeteredPricingModel::PerUnit { unit_price } => unit_price.clone(),
                        _ => Money::new(
                            amount.value() / usage_data.total_usage as f64,
                            amount.currency().clone(),
                        )?,
                    },
                    amount,
                    item_type: InvoiceItemType::UsageFee,
                });
            }
        }
        
        Ok(charges)
    }
    
    async fn calculate_one_time_charges(
        &self,
        subscription: &Subscription,
        billing_period: &DateRange,
    ) -> Result<Vec<InvoiceLineItem>, BillingError> {
        // 查询该计费周期内的一次性费用
        let charges = self.subscription_repository
            .get_one_time_charges(&subscription.id, billing_period)
            .await?;
            
        // 转换为发票行项目
        let line_items = charges.into_iter()
            .map(|charge| InvoiceLineItem {
                description: charge.description,
                quantity: 1,
                unit_price: charge.amount.clone(),
                amount: charge.amount,
                item_type: InvoiceItemType::OneTimeFee,
            })
            .collect();
            
        Ok(line_items)
    }
    
    async fn calculate_adjustments(
        &self,
        subscription: &Subscription,
        billing_period: &DateRange,
    ) -> Result<Vec<InvoiceAdjustment>, BillingError> {
        // 查询该计费周期内的调整项
        let adjustments = self.subscription_repository
            .get_adjustments(&subscription.id, billing_period)
            .await?;
            
        Ok(adjustments)
    }
    
    async fn calculate_taxes(
        &self,
        base_charge: &InvoiceLineItem,
        usage_charges: &[InvoiceLineItem],
        one_time_charges: &[InvoiceLineItem],
        adjustments: &[InvoiceAdjustment],
        tax_info: &CustomerTaxInfo,
    ) -> Result<Vec<InvoiceTax>, BillingError> {
        // 如果客户免税，则不计算税费
        if tax_info.tax_exempt {
            return Ok(vec![]);
        }
        
        let mut taxes = Vec::new();
        let currency = base_charge.amount.currency().clone();
        
        // 计算应税金额
        let taxable_amount = base_charge.amount.value() +
            usage_charges.iter().map(|c| c.amount.value()).sum::<f64>() +
            one_time_charges.iter().map(|c| c.amount.value()).sum::<f64>() +
            adjustments.iter().filter(|a| a.taxable).map(|a| a.amount.value()).sum::<f64>();
            
        // 应用税率
        for tax_rate in &tax_info.applicable_tax_rates {
            let tax_amount = taxable_amount * tax_rate.rate;
            
            if tax_amount > 0.0 {
                taxes.push(InvoiceTax {
                    name: tax_rate.name.clone(),
                    rate: tax_rate.rate,
                    amount: Money::new(tax_amount, currency.clone())?,
                    tax_authority: tax_rate.authority.clone(),
                });
            }
        }
        
        Ok(taxes)
    }
}
```

**映射分析**:

- 使用价格计算引擎表达复杂定价规则
- 在订阅计费系统中处理经济价值流转
- 基于业务策略和环境条件的动态价值计算
- 多维度定价策略的组合与应用

## 3. 实现一致性映射的模式与策略

### 3.1 抽象层次分离

将业务领域关注点与技术细节分离：

```rust
// 分层架构示例
// 领域层 - 纯业务逻辑，不依赖基础设施
mod domain {
    use chrono::{DateTime, Utc};
    use uuid::Uuid;
    use std::collections::HashMap;
    
    // 核心领域概念，不包含技术细节
    #[derive(Debug, Clone)]
    pub struct Order {
        id: OrderId,
        customer_id: CustomerId,
        items: Vec<OrderItem>,
        status: OrderStatus,
        shipping_address: Option<Address>,
        payment_status: PaymentStatus,
        created_at: DateTime<Utc>,
        updated_at: DateTime<Utc>,
    }
    
    impl Order {
        // 业务逻辑方法 - 验证领域规则
        pub fn add_item(&mut self, item: OrderItem) -> Result<(), OrderError> {
            // 检查订单状态
            if self.status != OrderStatus::Draft {
                return Err(OrderError::InvalidStateTransition(
                    "只能在草稿状态下添加商品".into()
                ));
            }
            
            // 检查商品是否已存在，如果存在则增加数量
            if let Some(existing_item) = self.items.iter_mut()
                .find(|i| i.product_id == item.product_id) {
                existing_item.quantity += item.quantity;
                existing_item.total_price = existing_item.unit_price * existing_item.quantity as f64;
            } else {
                // 否则添加新商品
                self.items.push(item);
            }
            
            self.updated_at = Utc::now();
            
            Ok(())
        }
        
        pub fn submit(&mut self) -> Result<(), OrderError> {
            // 验证订单可以提交
            if self.status != OrderStatus::Draft {
                return Err(OrderError::InvalidStateTransition(
                    "只能提交草稿状态的订单".into()
                ));
            }
            
            if self.items.is_empty() {
                return Err(OrderError::ValidationError("订单必须包含至少一个商品".into()));
            }
            
            if self.shipping_address.is_none() {
                return Err(OrderError::ValidationError("订单必须包含送货地址".into()));
            }
            
            // 更新状态
            self.status = OrderStatus::Submitted;
            self.updated_at = Utc::now();
            
            Ok(())
        }
        
        // 计算订单总金额 - 纯业务计算
        pub fn calculate_total(&self) -> Money {
            self.items.iter()
                .fold(Money::zero(Currency::USD), |acc, item| {
                    acc + Money::new_usd(item.total_price).unwrap_or(Money::zero(Currency::USD))
                })
        }
        
        // 其他业务逻辑方法...
    }
    
    // 领域服务 - 包含更复杂的业务逻辑
    pub trait OrderService {
        fn place_order(&self, order: &mut Order) -> Result<(), OrderServiceError>;
        fn cancel_order(&self, order: &mut Order, reason: &str) -> Result<(), OrderServiceError>;
        fn refund_order(&self, order: &mut Order, amount: Money) -> Result<(), OrderServiceError>;
    }
    
    // 领域仓储接口 - 定义存储操作但不包含实现
    pub trait OrderRepository {
        fn find_by_id(&self, id: &OrderId) -> Result<Option<Order>, RepositoryError>;
        fn save(&self, order: &Order) -> Result<(), RepositoryError>;
        fn find_by_customer(&self, customer_id: &CustomerId) -> Result<Vec<Order>, RepositoryError>;
    }
    
    // 其他领域定义...
}

// 应用层 - 协调领域和基础设施
mod application {
    use super::domain::*;
    use super::infrastructure::*;
    use std::sync::Arc;
    
    // 应用服务 - 编排领域逻辑和技术操作
    pub struct OrderApplicationService {
        order_repository: Arc<dyn OrderRepository>,
        inventory_service: Arc<dyn InventoryService>,
        payment_service: Arc<dyn PaymentService>,
        notification_service: Arc<dyn NotificationService>,
    }
    
    impl OrderApplicationService {
        // 用例：创建订单
        pub async fn create_order(
            &self,
            customer_id: CustomerId,
            items: Vec<OrderItemDto>,
            shipping_address: Option<AddressDto>,
        ) -> Result<OrderDto, ApplicationError> {
            // 将DTO转换为领域对象
            let shipping_address_domain = shipping_address
                .map(|addr| addr.to_domain())
                .transpose()?;
                
            let order_items = items.into_iter()
                .map(|item| {
                    // 验证商品是否存在并获取最新价格
                    let product = self.inventory_service.get_product(&item.product_id)
                        .map_err(|e| ApplicationError::ExternalServiceError(e.to_string()))?;
                        
                    Ok(OrderItem {
                        id: OrderItemId::new(),
                        product_id: item.product_id,
                        name: product.name,
                        unit_price: product.price.value(),
                        quantity: item.quantity,
                        total_price: product.price.value() * item.quantity as f64,
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;
                
            // 创建领域对象
            let mut order = Order::new(
                OrderId::new(),
                customer_id,
                order_items,
                shipping_address_domain,
            );
            
            // 保存订单
            self.order_repository.save(&order)
                .map_err(|e| ApplicationError::RepositoryError(e.to_string()))?;
                
            // 通知客户
            self.notification_service.send_order_confirmation(&order)
                .map_err(|e| ApplicationError::NotificationError(e.to_string()))?;
                
            // 转换回DTO
            Ok(OrderDto::from_domain(&order))
        }
        
        // 用例：处理订单支付
        pub async fn process_order_payment(
            &self,
            order_id: &OrderId,
            payment_method: PaymentMethodDto,
        ) -> Result<PaymentResultDto, ApplicationError> {
            // 获取订单
            let mut order = self.order_repository.find_by_id(order_id)
                .map_err(|e| ApplicationError::RepositoryError(e.to_string()))?
                .ok_or_else(|| ApplicationError::EntityNotFound(format!("订单 {}", order_id)))?;
                
            // 验证订单状态
            if order.status() != &OrderStatus::Submitted {
                return Err(ApplicationError::InvalidOperation(
                    "只能处理已提交状态的订单支付".into()
                ));
            }
            
            // 计算金额
            let amount = order.calculate_total();
            
            // 处理支付
            let payment_result = self.payment_service.process_payment(
                &PaymentRequest {
                    order_id: order_id.clone(),
                    amount,
                    payment_method: payment_method.to_domain(),
                }
            ).await.map_err(|e| ApplicationError::PaymentError(e.to_string()))?;
            
            // 更新订单状态
            if payment_result.status == PaymentStatus::Succeeded {
                order.mark_as_paid(payment_result.transaction_id.clone())
                    .map_err(|e| ApplicationError::DomainError(e.to_string()))?;
                    
                // 保存更新后的订单
                self.order_repository.save(&order)
                    .map_err(|e| ApplicationError::RepositoryError(e.to_string()))?;
                    
                // 分配库存
                self.inventory_service.allocate_stock(&order)
                    .map_err(|e| ApplicationError::InventoryError(e.to_string()))?;
            }
            
            // 返回支付结果
            Ok(PaymentResultDto::from_domain(&payment_result))
        }
        
        // 其他应用服务方法...
    }
    
    // 其他应用层组件...
}

// 基础设施层 - 实现技术细节
mod infrastructure {
    use super::domain::*;
    use sqlx::{PgPool, postgres::PgRow, Row};
    use reqwest::Client;
    
    // 仓储实现
    pub struct SqlOrderRepository {
        pool: PgPool,
    }
    
    impl OrderRepository for SqlOrderRepository {
        fn find_by_id(&self, id: &OrderId) -> Result<Option<Order>, RepositoryError> {
            // SQL查询实现
            // ...
            todo!()
        }
        
        fn save(&self, order: &Order) -> Result<(), RepositoryError> {
            // SQL插入/更新实现
            // ...
            todo!()
        }
        
        fn find_by_customer(&self, customer_id: &CustomerId) -> Result<Vec<Order>, RepositoryError> {
            // SQL查询实现
            // ...
            todo!()
        }
    }
    
    // 支付服务实现
    pub struct StripePaymentService {
        client: Client,
        api_key: String,
    }
    
    impl PaymentService for StripePaymentService {
        async fn process_payment(&self, request: &PaymentRequest) -> Result<PaymentResult, PaymentServiceError> {
            // Stripe API调用实现
            // ...
            todo!()
        }
        
        async fn refund_payment(&self, transaction_id: &str, amount: Money) -> Result<RefundResult, PaymentServiceError> {
            // Stripe退款API调用实现
            // ...
            todo!()
        }
    }
    
    // 通知服务实现
    pub struct EmailNotificationService {
        email_client: Client,
        sender_email: String,
        templates: HashMap<String, String>,
    }
    
    impl NotificationService for EmailNotificationService {
        fn send_order_confirmation(&self, order: &Order) -> Result<(), NotificationError> {
            // 电子邮件发送实现
            // ...
            todo!()
        }
        
        fn send_shipment_notification(&self, order: &Order, tracking_info: &TrackingInfo) -> Result<(), NotificationError> {
            // 电子邮件发送实现
            // ...
            todo!()
        }
    }
    
    // 库存服务实现
    pub struct WarehouseInventoryService {
        client: Client,
        warehouse_api_url: String,
    }
    
    impl InventoryService for WarehouseInventoryService {
        fn get_product(&self, product_id: &ProductId) -> Result<Product, InventoryServiceError> {
            // 仓库API调用实现
            // ...
            todo!()
        }
        
        fn allocate_stock(&self, order: &Order) -> Result<(), InventoryServiceError> {
            // 库存分配API调用实现
            // ...
            todo!()
        }
    }
    
    // 其他基础设施实现...
}

// 接口层 - 对外暴露API
mod interface {
    use super::application::*;
    use super::domain::*;
    use actix_web::{web, HttpResponse, ResponseError};
    use serde::{Deserialize, Serialize};
    
    // REST API控制器
    pub struct OrderController {
        order_service: Arc<OrderApplicationService>,
    }
    
    impl OrderController {
        // REST API端点
        pub async fn create_order(
            &self,
            req: web::Json<CreateOrderRequest>,
            user_info: UserInfo,
        ) -> Result<HttpResponse, ActixError> {
            // 验证用户权限
            if user_info.customer_id.is_none() {
                return Err(ActixError::Forbidden("必须登录才能创建订单".into()));
            }
            
            // 调用应用服务
            let order = self.order_service.create_order(
                user_info.customer_id.unwrap(),
                req.items.clone(),
                req.shipping_address.clone(),
            ).await?;
            
            // 返回API响应
            Ok(HttpResponse::Created().json(order))
        }
        
        pub async fn process_payment(
            &self,
            order_id: web::Path<String>,
            req: web::Json<ProcessPaymentRequest>,
            user_info: UserInfo,
        ) -> Result<HttpResponse, ActixError> {
            // 验证用户权限
            if user_info.customer_id.is_none() {
                return Err(ActixError::Forbidden("必须登录才能处理支付".into()));
            }
            
            // 解析订单ID
            let order_id = OrderId::from_string(&order_id)?;
            
            // 调用应用服务
            let payment_result = self.order_service.process_order_payment(
                &order_id,
                req.payment_method.clone(),
            ).await?;
            
            // 返回API响应
            Ok(HttpResponse::Ok().json(payment_result))
        }
        
        // 其他API端点...
    }
    
    // 请求/响应DTO
    #[derive(Deserialize)]
    pub struct CreateOrderRequest {
        items: Vec<OrderItemDto>,
        shipping_address: Option<AddressDto>,
    }
    
    #[derive(Deserialize)]
    pub struct ProcessPaymentRequest {
        payment_method: PaymentMethodDto,
    }
    
    // 其他接口层组件...
}
```

**映射分析**:

- 领域层专注纯粹业务规则和领域概念
- 应用层协调业务与技术，处理用例
- 基础设施层实现技术细节和外部系统集成
- 接口层处理API定义和请求/响应格式

### 3.2 抽象接口与可测试设计

通过抽象接口和可测试设计确保业务逻辑的正确性：

```rust
// 抽象接口示例
// 时间服务抽象 - 便于测试时间相关逻辑
pub trait TimeProvider: Send + Sync {
    fn now(&self) -> DateTime<Utc>;
    fn today(&self) -> Date<Utc> {
        self.now().date()
    }
}

// 实时实现
pub struct RealTimeProvider;

impl TimeProvider for RealTimeProvider {
    fn now(&self) -> DateTime<Utc> {
        Utc::now()
    }
}

// 测试实现
pub struct FixedTimeProvider {
    fixed_time: DateTime<Utc>,
}

impl FixedTimeProvider {
    pub fn new(time: DateTime<Utc>) -> Self {
        Self { fixed_time: time }
    }
    
    pub fn advance(&mut self, duration: Duration) {
        self.fixed_time = self.fixed_time + duration;
    }
}

impl TimeProvider for FixedTimeProvider {
    fn now(&self) -> DateTime<Utc> {
        self.fixed_time
    }
}

// 随机生成器抽象 - 便于测试随机性逻辑
pub trait RandomGenerator: Send + Sync {
    fn generate_id(&self) -> String;
    fn random_bool(&self, probability: f64) -> bool;
    fn random_f64(&self, min: f64, max: f64) -> f64;
    fn random_u32(&self, min: u32, max: u32) -> u32;
}

// 实际实现
pub struct DefaultRandomGenerator;

impl RandomGenerator for DefaultRandomGenerator {
    fn generate_id(&self) -> String {
        Uuid::new_v4().to_string()
    }
    
    fn random_bool(&self, probability: f64) -> bool {
        let mut rng = rand::thread_rng();
        rng.gen_bool(probability)
    }
    
    fn random_f64(&self, min: f64, max: f64) -> f64 {
        let mut rng = rand::thread_rng();
        rng.gen_range(min..max)
    }
    
    fn random_u32(&self, min: u32, max: u32) -> u32 {
        let mut rng = rand::thread_rng();
        rng.gen_range(min..max)
    }
}

// 测试实现
pub struct MockRandomGenerator {
    next_id: Option<String>,
    next_bool: Option<bool>,
    next_f64: Option<f64>,
    next_u32: Option<u32>,
}

impl RandomGenerator for MockRandomGenerator {
    fn generate_id(&self) -> String {
        self.next_id.clone().unwrap_or_else(|| "mock-id-123".to_string())
    }
    
    fn random_bool(&self, _probability: f64) -> bool {
        self.next_bool.unwrap_or(false)
    }
    
    fn random_f64(&self, min: f64, _max: f64) -> f64 {
        self.next_f64.unwrap_or(min)
    }
    
    fn random_u32(&self, min: u32, _max: u32) -> u32 {
        self.next_u32.unwrap_or(min)
    }
}

// 使用抽象接口的服务示例
pub struct PromotionService {
    time_provider: Arc<dyn TimeProvider>,
    random_generator: Arc<dyn RandomGenerator>,
    promotion_repository: Arc<dyn PromotionRepository>,
}

impl PromotionService {
    pub fn apply_random_promotion(
        &self,
        customer: &Customer,
        cart: &Cart,
    ) -> Option<Promotion> {
        // 获取有效促销
        let active_promotions = match self.promotion_repository.find_active(self.time_provider.now()) {
            Ok(promotions) => promotions,
            Err(_) => return None,
        };
        
        if active_promotions.is_empty() {
            return None;
        }
        
        // 计算每个促销的适用性和权重
        let mut weighted_promotions = Vec::new();
        
        for promotion in active_promotions {
            // 检查促销适用条件
            if !self.is_promotion_applicable(&promotion, customer, cart) {
                continue;
            }
            
            // 添加到带权重的列表
            weighted_promotions.push((promotion, self.calculate_promotion_weight(&promotion, customer)));
        }
        
        if weighted_promotions.is_empty() {
            return None;
        }
        
        // 根据权重随机选择促销
        let total_weight: f64 = weighted_promotions.iter().map(|(_, weight)| *weight).sum();
        let random_value = self.random_generator.random_f64(0.0, total_weight);
        
        let mut cumulative_weight = 0.0;
        for (promotion, weight) in weighted_promotions {
            cumulative_weight += weight;
            if random_value <= cumulative_weight {
                return Some(promotion);
            }
        }
        
        // 如果随机选择失败，返回第一个
        weighted_promotions.first().map(|(promotion, _)| promotion.clone())
    }
    
    fn is_promotion_applicable(&self, promotion: &Promotion, customer: &Customer, cart: &Cart) -> bool {
        // 检查时间限制
        let now = self.time_provider.now();
        if now < promotion.start_date || now > promotion.end_date {
            return false;
        }
        
        // 检查客户段限制
        if let Some(segments) = &promotion.customer_segments {
            if !segments.contains(&customer.segment) {
                return false;
            }
        }
        
        // 检查最小订单金额
        if let Some(min_amount) = promotion.min_order_amount {
            if cart.calculate_subtotal() < min_amount {
                return false;
            }
        }
        
        // 检查特定产品要求
        if let Some(required_products) = &promotion.required_products {
            let cart_products: HashSet<_> = cart.items.iter()
                .map(|item| item.product_id.clone())
                .collect();
                
            if !required_products.iter().all(|p| cart_products.contains(p)) {
                return false;
            }
        }
        
        // 检查使用配额
        if let Some(usage_limit) = promotion.usage_limit {
            let current_usage = self.promotion_repository.get_usage_count(&promotion.id)
                .unwrap_or(0);
                
            if current_usage >= usage_limit {
                return false;
            }
        }
        
        true
    }
    
    fn calculate_promotion_weight(&self, promotion: &Promotion, customer: &Customer) -> f64 {
        let mut weight = 1.0;
        
        // 新客户权重调整
        if customer.is_new && promotion.boost_for_new_customers {
            weight *= 2.0;
        }
        
        // 即将到期的促销权重增加
        let days_until_expiry = (promotion.end_date - self.time_provider.now()).num_days();
        if days_until_expiry <= 3 {
            weight *= 1.5;
        }
        
        // 按促销优先级调整
        weight *= match promotion.priority {
            PromotionPriority::Low => 0.5,
            PromotionPriority::Normal => 1.0,
            PromotionPriority::High => 2.0,
        };
        
        weight
    }
}

// 针对上述代码的测试
#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    
    // 模拟促销仓储
    struct MockPromotionRepository {
        active_promotions: Vec<Promotion>,
        usage_counts: HashMap<String, u32>,
    }
    
    impl PromotionRepository for MockPromotionRepository {
        fn find_active(&self, _now: DateTime<Utc>) -> Result<Vec<Promotion>, RepositoryError> {
            Ok(self.active_promotions.clone())
        }
        
        fn get_usage_count(&self, promotion_id: &str) -> Result<u32, RepositoryError> {
            Ok(*self.usage_counts.get(promotion_id).unwrap_or(&0))
        }
        
        // 其他必要方法的实现...
    }
    
    #[test]
    fn test_apply_random_promotion_returns_none_when_no_promotions() {
        // 准备
        let time_provider = Arc::new(FixedTimeProvider::new(
            DateTime::parse_from_rfc3339("2023-01-15T12:00:00Z")
                .unwrap()
                .with_timezone(&Utc)
        ));
        
        let random_generator = Arc::new(MockRandomGenerator {
            next_id: None,
            next_bool: None,
            next_f64: Some(0.5), // 随机数固定为0.5
            next_u32: None,
        });
        
        let promotion_repository = Arc::new(MockPromotionRepository {
            active_promotions: vec![],
            usage_counts: HashMap::new(),
        });
        
        let service = PromotionService {
            time_provider,
            random_generator,
            promotion_repository,
        };
        
        let customer = Customer {
            id: CustomerId::new(),
            name: "Test Customer".to_string(),
            segment: CustomerSegment::Regular,
            is_new: false,
        };
        
        let cart = Cart {
            id: CartId::new(),
            items: vec![],
        };
        
        // 执行
        let result = service.apply_random_promotion(&customer, &cart);
        
        // 验证
        assert!(result.is_none());
    }
    
    #[test]
    fn test_apply_random_promotion_respects_time_constraints() {
        // 准备
        let now = DateTime::parse_from_rfc3339("2023-01-15T12:00:00Z")
            .unwrap()
            .with_timezone(&Utc);
            
        let time_provider = Arc::new(FixedTimeProvider::new(now));
        
        let random_generator = Arc::new(MockRandomGenerator {
            next_id: None,
            next_bool: None,
            next_f64: Some(0.5),
            next_u32: None,
        });
        
        // 创建一个过期的促销和一个未来的促销
        let expired_promotion = Promotion {
            id: "promo1".to_string(),
            name: "Expired Promo".to_string(),
            start_date: now - Duration::days(10),
            end_date: now - Duration::days(1),
            // 其他字段设置...
        };
        
        let future_promotion = Promotion {
            id: "promo2".to_string(),
            name: "Future Promo".to_string(),
            start_date: now + Duration::days(1),
            end_date: now + Duration::days(10),
            // 其他字段设置...
        };
        
        let promotion_repository = Arc::new(MockPromotionRepository {
            active_promotions: vec![expired_promotion, future_promotion],
            usage_counts: HashMap::new(),
        });
        
        let service = PromotionService {
            time_provider,
            random_generator,
            promotion_repository,
        };
        
        let customer = Customer {
            id: CustomerId::new(),
            name: "Test Customer".to_string(),
            segment: CustomerSegment::Regular,
            is_new: false,
        };
        
        let cart = Cart {
            id: CartId::new(),
            items: vec![],
        };
        
        // 执行
        let result = service.apply_random_promotion(&customer, &cart);
        
        // 验证 - 两个促销都不应适用
        assert!(result.is_none());
    }
    
    // 更多测试...
}
```

**映射分析**:

- 通过抽象接口（如`TimeProvider`、`RandomGenerator`）隔离外部依赖
- 测试实现提供可控行为，便于单元测试
- 依赖注入模式支持灵活组合和测试
- 可测试设计确保业务规则正确性和稳定性

### 3.3 契约驱动设计

确保系统边界的一致性：

```rust
// 外部系统契约定义
// 支付网关API契约
#[derive(Debug, Serialize)]
pub struct PaymentGatewayRequest {
    pub merchant_id: String,
    pub transaction_id: String,
    pub amount: f64,
    pub currency: String,
    pub card_details: CardDetails,
    pub billing_address: Option<BillingAddress>,
    pub metadata: HashMap<String, String>,
}

#[derive(Debug, Deserialize)]
pub struct PaymentGatewayResponse {
    pub success: bool,
    pub transaction_id: String,
    pub gateway_reference: String,
    pub status: String,
    pub error_code: Option<String>,
    pub error_message: Option<String>,
    pub created_at: String,
}

// 契约验证器
pub struct PaymentGatewayContractValidator;

impl PaymentGatewayContractValidator {
    pub fn validate_request(request: &PaymentGat

```rust
    pub fn validate_request(request: &PaymentGatewayRequest) -> Result<(), ContractValidationError> {
        // 验证商户ID
        if request.merchant_id.is_empty() {
            return Err(ContractValidationError::InvalidField("merchant_id不能为空"));
        }
        
        // 验证交易ID
        if request.transaction_id.is_empty() {
            return Err(ContractValidationError::InvalidField("transaction_id不能为空"));
        }
        
        // 验证金额
        if request.amount <= 0.0 {
            return Err(ContractValidationError::InvalidField("amount必须大于0"));
        }
        
        // 验证货币代码
        if request.currency.len() != 3 {
            return Err(ContractValidationError::InvalidField("currency必须是3字符的ISO代码"));
        }
        
        // 验证卡详情
        if request.card_details.number.len() < 13 || request.card_details.number.len() > 19 {
            return Err(ContractValidationError::InvalidField("卡号长度无效"));
        }
        
        if request.card_details.expiry_month < 1 || request.card_details.expiry_month > 12 {
            return Err(ContractValidationError::InvalidField("到期月份无效"));
        }
        
        // 验证当前年份和月份
        let now = chrono::Utc::now();
        let current_year = now.year() % 100; // 取年份的后两位
        let current_month = now.month() as u8;
        
        if request.card_details.expiry_year < current_year || 
           (request.card_details.expiry_year == current_year && request.card_details.expiry_month < current_month) {
            return Err(ContractValidationError::InvalidField("卡已过期"));
        }
        
        if request.card_details.cvv.len() < 3 || request.card_details.cvv.len() > 4 {
            return Err(ContractValidationError::InvalidField("CVV长度无效"));
        }
        
        // 验证账单地址（如果提供）
        if let Some(address) = &request.billing_address {
            if address.country.len() != 2 {
                return Err(ContractValidationError::InvalidField("国家代码必须是2字符的ISO代码"));
            }
            
            if address.postal_code.is_empty() {
                return Err(ContractValidationError::InvalidField("邮政编码不能为空"));
            }
        }
        
        Ok(())
    }
    
    pub fn validate_response(response: &PaymentGatewayResponse) -> Result<(), ContractValidationError> {
        // 验证交易ID
        if response.transaction_id.is_empty() {
            return Err(ContractValidationError::InvalidField("响应缺少transaction_id"));
        }
        
        // 验证网关引用
        if response.gateway_reference.is_empty() {
            return Err(ContractValidationError::InvalidField("响应缺少gateway_reference"));
        }
        
        // 验证状态
        match response.status.as_str() {
            "succeeded" | "pending" | "failed" => {}
            _ => return Err(ContractValidationError::InvalidField("响应状态无效")),
        }
        
        // 验证错误字段的一致性
        if !response.success && (response.error_code.is_none() || response.error_message.is_none()) {
            return Err(ContractValidationError::InvalidField("失败响应必须包含错误代码和消息"));
        }
        
        // 验证时间戳格式
        match DateTime::parse_from_rfc3339(&response.created_at) {
            Ok(_) => {}
            Err(_) => return Err(ContractValidationError::InvalidField("created_at时间戳格式无效")),
        }
        
        Ok(())
    }
}

// 契约驱动的支付网关适配器
pub struct PaymentGatewayAdapter {
    client: reqwest::Client,
    base_url: String,
    merchant_id: String,
    api_key: String,
    validator: PaymentGatewayContractValidator,
}

impl PaymentGatewayAdapter {
    pub async fn process_payment(&self, payment: &Payment) -> Result<PaymentResult, PaymentAdapterError> {
        // 将内部支付模型转换为网关请求格式
        let request = self.map_to_gateway_request(payment)?;
        
        // 验证请求符合契约
        self.validator.validate_request(&request)
            .map_err(|e| PaymentAdapterError::ContractViolation(e.to_string()))?;
        
        // 发送请求到支付网关
        let response = self.client
            .post(&format!("{}/v1/payments", self.base_url))
            .header("Authorization", format!("Bearer {}", self.api_key))
            .header("Content-Type", "application/json")
            .json(&request)
            .send()
            .await
            .map_err(|e| PaymentAdapterError::CommunicationError(e.to_string()))?;
            
        // 解析响应
        let gateway_response: PaymentGatewayResponse = response.json()
            .await
            .map_err(|e| PaymentAdapterError::ResponseParseError(e.to_string()))?;
            
        // 验证响应符合契约
        self.validator.validate_response(&gateway_response)
            .map_err(|e| PaymentAdapterError::ContractViolation(e.to_string()))?;
            
        // 将网关响应映射回内部模型
        let result = self.map_from_gateway_response(gateway_response, payment)?;
        
        Ok(result)
    }
    
    fn map_to_gateway_request(&self, payment: &Payment) -> Result<PaymentGatewayRequest, PaymentAdapterError> {
        // 提取支付方式详情
        let card_details = match &payment.payment_method {
            PaymentMethod::CreditCard(card) => CardDetails {
                number: card.number.clone(),
                expiry_month: card.expiry_month,
                expiry_year: card.expiry_year,
                cvv: card.cvv.clone(),
                holder_name: card.holder_name.clone(),
            },
            _ => return Err(PaymentAdapterError::UnsupportedPaymentMethod),
        };
        
        // 构建请求
        let request = PaymentGatewayRequest {
            merchant_id: self.merchant_id.clone(),
            transaction_id: payment.id.to_string(),
            amount: payment.amount.value(),
            currency: payment.amount.currency().code().to_string(),
            card_details,
            billing_address: payment.billing_address.as_ref().map(|addr| BillingAddress {
                line1: addr.street_line1.clone(),
                line2: addr.street_line2.clone(),
                city: addr.city.clone(),
                state: addr.state.clone(),
                postal_code: addr.postal_code.clone(),
                country: addr.country.clone(),
            }),
            metadata: HashMap::from([
                ("customer_id".to_string(), payment.customer_id.to_string()),
                ("order_id".to_string(), payment.order_id.map_or("".to_string(), |id| id.to_string())),
            ]),
        };
        
        Ok(request)
    }
    
    fn map_from_gateway_response(
        &self,
        response: PaymentGatewayResponse,
        original_payment: &Payment,
    ) -> Result<PaymentResult, PaymentAdapterError> {
        // 映射支付状态
        let status = match response.status.as_str() {
            "succeeded" => PaymentStatus::Succeeded,
            "pending" => PaymentStatus::Pending,
            "failed" => PaymentStatus::Failed,
            _ => return Err(PaymentAdapterError::UnknownPaymentStatus(response.status)),
        };
        
        // 映射错误（如果有）
        let error = if !response.success {
            Some(PaymentError {
                code: response.error_code.unwrap_or_else(|| "unknown".to_string()),
                message: response.error_message.unwrap_or_else(|| "Unknown error".to_string()),
            })
        } else {
            None
        };
        
        // 创建结果
        let result = PaymentResult {
            payment_id: original_payment.id.clone(),
            status,
            transaction_id: response.transaction_id,
            provider_reference: response.gateway_reference,
            amount: original_payment.amount.clone(),
            processed_at: DateTime::parse_from_rfc3339(&response.created_at)
                .map_err(|_| PaymentAdapterError::InvalidResponseDate)?
                .with_timezone(&Utc),
            error,
        };
        
        Ok(result)
    }
}

// 基于契约的库存系统集成
// 库存API契约
#[derive(Debug, Serialize)]
pub struct InventoryAllocationRequest {
    pub order_id: String,
    pub warehouse_id: Option<String>,
    pub items: Vec<AllocationItem>,
    pub requested_by: String,
    pub allocation_strategy: String, // "FIFO", "LIFO", "FEFO", etc.
}

#[derive(Debug, Serialize)]
pub struct AllocationItem {
    pub product_id: String,
    pub variant_id: Option<String>,
    pub quantity: u32,
}

#[derive(Debug, Deserialize)]
pub struct InventoryAllocationResponse {
    pub allocation_id: String,
    pub order_id: String,
    pub status: String, // "ALLOCATED", "PARTIAL", "FAILED"
    pub items: Vec<AllocatedItem>,
    pub warehouse_id: String,
    pub allocation_date: String,
    pub errors: Option<Vec<AllocationError>>,
}

#[derive(Debug, Deserialize)]
pub struct AllocatedItem {
    pub product_id: String,
    pub variant_id: Option<String>,
    pub requested_quantity: u32,
    pub allocated_quantity: u32,
    pub status: String, // "ALLOCATED", "PARTIAL", "FAILED"
    pub bin_location: Option<String>,
    pub lot_number: Option<String>,
}

// 库存系统集成
pub struct InventorySystemAdapter {
    client: reqwest::Client,
    base_url: String,
    api_key: String,
    default_warehouse: String,
    system_id: String,
}

impl InventorySystemAdapter {
    pub async fn allocate_inventory(
        &self,
        order: &Order,
    ) -> Result<InventoryAllocationResult, InventoryAdapterError> {
        // 将订单转换为库存分配请求
        let request = self.create_allocation_request(order);
        
        // 发送请求
        let response = self.client
            .post(&format!("{}/api/v1/allocations", self.base_url))
            .header("X-API-Key", &self.api_key)
            .header("Content-Type", "application/json")
            .json(&request)
            .send()
            .await
            .map_err(|e| InventoryAdapterError::CommunicationError(e.to_string()))?;
            
        // 处理响应状态
        if !response.status().is_success() {
            let status = response.status();
            let error_text = response.text().await
                .unwrap_or_else(|_| "Failed to read error response".to_string());
                
            return Err(InventoryAdapterError::ApiError {
                status_code: status.as_u16(),
                message: error_text,
            });
        }
        
        // 解析响应
        let allocation_response: InventoryAllocationResponse = response.json()
            .await
            .map_err(|e| InventoryAdapterError::ResponseParseError(e.to_string()))?;
            
        // 转换为内部模型
        self.map_allocation_response(allocation_response)
    }
    
    fn create_allocation_request(&self, order: &Order) -> InventoryAllocationRequest {
        // 映射订单项到分配项
        let items = order.items.iter()
            .map(|item| AllocationItem {
                product_id: item.product_id.to_string(),
                variant_id: item.variant_id.as_ref().map(|v| v.to_string()),
                quantity: item.quantity,
            })
            .collect();
            
        InventoryAllocationRequest {
            order_id: order.id.to_string(),
            warehouse_id: Some(self.default_warehouse.clone()),
            items,
            requested_by: self.system_id.clone(),
            allocation_strategy: "FIFO".to_string(), // 默认策略
        }
    }
    
    fn map_allocation_response(
        &self,
        response: InventoryAllocationResponse,
    ) -> Result<InventoryAllocationResult, InventoryAdapterError> {
        // 映射状态
        let status = match response.status.as_str() {
            "ALLOCATED" => AllocationStatus::Allocated,
            "PARTIAL" => AllocationStatus::PartiallyAllocated,
            "FAILED" => AllocationStatus::Failed,
            unknown => return Err(InventoryAdapterError::UnknownStatus(unknown.to_string())),
        };
        
        // 映射分配项
        let items = response.items.into_iter()
            .map(|item| AllocatedInventoryItem {
                product_id: ProductId::from_string(&item.product_id)
                    .map_err(|_| InventoryAdapterError::InvalidProductId(item.product_id.clone()))?,
                variant_id: item.variant_id.map(|v| VariantId::from_string(&v))
                    .transpose()
                    .map_err(|_| InventoryAdapterError::InvalidVariantId(
                        item.variant_id.unwrap_or_default()
                    ))?,
                requested_quantity: item.requested_quantity,
                allocated_quantity: item.allocated_quantity,
                status: match item.status.as_str() {
                    "ALLOCATED" => ItemAllocationStatus::Allocated,
                    "PARTIAL" => ItemAllocationStatus::PartiallyAllocated,
                    "FAILED" => ItemAllocationStatus::Failed,
                    unknown => return Err(InventoryAdapterError::UnknownItemStatus(unknown.to_string())),
                },
                bin_location: item.bin_location,
                lot_number: item.lot_number,
            })
            .collect();
            
        // 映射错误（如果有）
        let errors = response.errors.map(|errs| {
            errs.into_iter()
                .map(|e| InventoryError {
                    code: e.code,
                    message: e.message,
                    product_id: e.product_id.map(|id| ProductId::from_string(&id).unwrap_or_default()),
                })
                .collect()
        }).unwrap_or_default();
        
        // 解析分配日期
        let allocation_date = DateTime::parse_from_rfc3339(&response.allocation_date)
            .map_err(|_| InventoryAdapterError::InvalidResponseDate)?
            .with_timezone(&Utc);
            
        // 创建结果
        let result = InventoryAllocationResult {
            allocation_id: response.allocation_id,
            order_id: OrderId::from_string(&response.order_id)
                .map_err(|_| InventoryAdapterError::InvalidOrderId(response.order_id))?,
            status,
            items,
            warehouse_id: response.warehouse_id,
            allocation_date,
            errors,
        };
        
        Ok(result)
    }
}

// 契约测试
#[cfg(test)]
mod contract_tests {
    use super::*;
    use mockito::{mock, server_url};
    
    #[tokio::test]
    async fn test_payment_gateway_contract() {
        // 创建模拟服务器
        let mock_server = mock("POST", "/v1/payments")
            .with_status(200)
            .with_header("content-type", "application/json")
            .with_body(r#"{
                "success": true,
                "transaction_id": "test-tx-123",
                "gateway_reference": "gateway-ref-456",
                "status": "succeeded",
                "error_code": null,
                "error_message": null,
                "created_at": "2023-01-15T12:34:56Z"
            }"#)
            .create();
            
        // 创建适配器
        let adapter = PaymentGatewayAdapter {
            client: reqwest::Client::new(),
            base_url: server_url(),
            merchant_id: "test-merchant".to_string(),
            api_key: "test-api-key".to_string(),
            validator: PaymentGatewayContractValidator,
        };
        
        // 创建测试支付
        let payment = Payment {
            id: PaymentId::new(),
            customer_id: CustomerId::new(),
            order_id: Some(OrderId::new()),
            amount: Money::new_usd(100.0).unwrap(),
            payment_method: PaymentMethod::CreditCard(CreditCard {
                number: "4111111111111111".to_string(),
                expiry_month: 12,
                expiry_year: 25,
                cvv: "123".to_string(),
                holder_name: "Test User".to_string(),
            }),
            billing_address: Some(Address {
                street_line1: "123 Test St".to_string(),
                street_line2: "".to_string(),
                city: "Test City".to_string(),
                state: "TS".to_string(),
                postal_code: "12345".to_string(),
                country: "US".to_string(),
            }),
            status: PaymentStatus::Pending,
            created_at: Utc::now(),
        };
        
        // 测试处理支付
        let result = adapter.process_payment(&payment).await;
        
        // 验证模拟服务器被调用
        mock_server.assert();
        
        // 验证结果
        assert!(result.is_ok());
        let payment_result = result.unwrap();
        assert_eq!(payment_result.status, PaymentStatus::Succeeded);
        assert_eq!(payment_result.transaction_id, "test-tx-123");
        assert_eq!(payment_result.provider_reference, "gateway-ref-456");
    }
}
```

**映射分析**:

- 明确定义外部系统契约（请求/响应结构）
- 实现契约验证器确保数据一致性
- 适配器模式隔离外部系统变化
- 契约测试验证集成正确性

### 3.4 业务与技术关注点分离

使用适配器模式将业务逻辑与技术实现分离：

```rust
// 领域层 - 纯业务概念
pub trait NotificationService {
    fn send_notification(&self, notification: &Notification) -> Result<NotificationResult, NotificationError>;
}

#[derive(Debug, Clone)]
pub struct Notification {
    pub id: NotificationId,
    pub recipient: NotificationRecipient,
    pub template_id: String,
    pub context: HashMap<String, String>,
    pub priority: NotificationPriority,
    pub scheduled_at: Option<DateTime<Utc>>,
}

// 应用层 - 编排业务与基础设施
pub struct OrderNotificationUseCase {
    notification_service: Arc<dyn NotificationService>,
    order_repository: Arc<dyn OrderRepository>,
    template_repository: Arc<dyn TemplateRepository>,
}

impl OrderNotificationUseCase {
    pub async fn notify_order_confirmation(
        &self,
        order_id: &OrderId,
    ) -> Result<(), ApplicationError> {
        // 获取订单
        let order = self.order_repository.find_by_id(order_id).await?
            .ok_or_else(|| ApplicationError::EntityNotFound(format!("Order {}", order_id)))?;
            
        // 获取客户联系信息
        let customer = self.customer_repository.find_by_id(&order.customer_id).await?
            .ok_or_else(|| ApplicationError::EntityNotFound(format!("Customer {}", order.customer_id)))?;
            
        // 创建通知内容上下文
        let context = self.create_order_context(&order);
        
        // 创建通知
        let notification = Notification {
            id: NotificationId::new(),
            recipient: NotificationRecipient::Email(customer.email.clone()),
            template_id: "order_confirmation".to_string(),
            context,
            priority: NotificationPriority::Normal,
            scheduled_at: None,
        };
        
        // 发送通知
        self.notification_service.send_notification(&notification)
            .await
            .map_err(|e| ApplicationError::NotificationError(e.to_string()))?;
            
        Ok(())
    }
    
    fn create_order_context(&self, order: &Order) -> HashMap<String, String> {
        let mut context = HashMap::new();
        
        context.insert("order_id".to_string(), order.id.to_string());
        context.insert("order_date".to_string(), order.created_at.to_rfc3339());
        context.insert("customer_name".to_string(), order.customer_name.clone());
        context.insert("total_amount".to_string(), order.total_amount.to_string());
        
        // 添加订单项信息
        let items_json = serde_json::to_string(&order.items).unwrap_or_default();
        context.insert("order_items".to_string(), items_json);
        
        // 添加配送信息
        if let Some(shipping) = &order.shipping_info {
            context.insert("shipping_method".to_string(), shipping.method.clone());
            context.insert("tracking_number".to_string(), shipping.tracking_number.clone().unwrap_or_default());
            context.insert("estimated_delivery".to_string(), shipping.estimated_delivery
                .map(|d| d.to_rfc3339())
                .unwrap_or_default());
        }
        
        context
    }
}

// 基础设施层 - 技术实现
// 电子邮件通知适配器
pub struct EmailNotificationAdapter {
    email_client: Arc<dyn EmailClient>,
    template_engine: Arc<dyn TemplateEngine>,
    config: EmailConfig,
    logger: Arc<dyn Logger>,
}

impl NotificationService for EmailNotificationAdapter {
    async fn send_notification(
        &self, 
        notification: &Notification
    ) -> Result<NotificationResult, NotificationError> {
        // 提取收件人电子邮件
        let recipient_email = match &notification.recipient {
            NotificationRecipient::Email(email) => email,
            _ => return Err(NotificationError::UnsupportedRecipientType(
                "EmailAdapter只支持电子邮件收件人".to_string()
            )),
        };
        
        // 获取模板
        let template = self.template_engine.get_template(&notification.template_id)
            .await
            .map_err(|e| NotificationError::TemplateError(e.to_string()))?;
            
        // 渲染模板
        let subject = self.template_engine.render_string(&template.subject, &notification.context)
            .map_err(|e| NotificationError::TemplateRenderError(e.to_string()))?;
            
        let body_html = self.template_engine.render(&template.body_html, &notification.context)
            .map_err(|e| NotificationError::TemplateRenderError(e.to_string()))?;
            
        let body_text = self.template_engine.render(&template.body_text, &notification.context)
            .map_err(|e| NotificationError::TemplateRenderError(e.to_string()))?;
            
        // 创建邮件
        let email = Email {
            from: self.config.sender_email.clone(),
            to: recipient_email.clone(),
            subject,
            body_html: Some(body_html),
            body_text: Some(body_text),
            reply_to: self.config.reply_to.clone(),
            attachments: vec![],
        };
        
        // 发送邮件
        let result = self.email_client.send_email(&email)
            .await
            .map_err(|e| {
                // 记录错误
                self.logger.error(&format!(
                    "Failed to send email notification: {}, notification_id: {}", 
                    e, notification.id
                ));
                
                NotificationError::DeliveryError(e.to_string())
            })?;
            
        // 创建结果
        let notification_result = NotificationResult {
            notification_id: notification.id.clone(),
            provider_id: result.message_id,
            status: NotificationStatus::Sent,
            sent_at: Utc::now(),
        };
        
        Ok(notification_result)
    }
}

// 短信通知适配器
pub struct SmsNotificationAdapter {
    sms_client: Arc<dyn SmsClient>,
    template_engine: Arc<dyn TemplateEngine>,
    config: SmsConfig,
    logger: Arc<dyn Logger>,
}

impl NotificationService for SmsNotificationAdapter {
    async fn send_notification(
        &self, 
        notification: &Notification
    ) -> Result<NotificationResult, NotificationError> {
        // 提取收件人电话号码
        let recipient_phone = match &notification.recipient {
            NotificationRecipient::Phone(phone) => phone,
            _ => return Err(NotificationError::UnsupportedRecipientType(
                "SmsAdapter只支持电话号码收件人".to_string()
            )),
        };
        
        // 获取模板
        let template = self.template_engine.get_template(&notification.template_id)
            .await
            .map_err(|e| NotificationError::TemplateError(e.to_string()))?;
            
        // 渲染模板（仅文本）
        let message = self.template_engine.render(&template.body_text, &notification.context)
            .map_err(|e| NotificationError::TemplateRenderError(e.to_string()))?;
            
        // 检查短信长度
        if message.len() > self.config.max_sms_length {
            return Err(NotificationError::ContentTooLong(
                format!("SMS长度超过最大值: {} > {}", 
                    message.len(), self.config.max_sms_length)
            ));
        }
        
        // 创建短信
        let sms = Sms {
            from: self.config.sender_number.clone(),
            to: recipient_phone.clone(),
            message,
        };
        
        // 发送短信
        let result = self.sms_client.send_sms(&sms)
            .await
            .map_err(|e| {
                // 记录错误
                self.logger.error(&format!(
                    "Failed to send SMS notification: {}, notification_id: {}", 
                    e, notification.id
                ));
                
                NotificationError::DeliveryError(e.to_string())
            })?;
            
        // 创建结果
        let notification_result = NotificationResult {
            notification_id: notification.id.clone(),
            provider_id: result.message_id,
            status: NotificationStatus::Sent,
            sent_at: Utc::now(),
        };
        
        Ok(notification_result)
    }
}

// 多渠道组合适配器
pub struct MultiChannelNotificationAdapter {
    adapters: HashMap<NotificationChannel, Arc<dyn NotificationService>>,
    channel_selector: Arc<dyn ChannelSelector>,
}

impl NotificationService for MultiChannelNotificationAdapter {
    async fn send_notification(
        &self, 
        notification: &Notification
    ) -> Result<NotificationResult, NotificationError> {
        // 确定最佳发送渠道
        let channel = self.channel_selector.select_channel(notification)
            .await
            .map_err(|e| NotificationError::ChannelSelectionError(e.to_string()))?;
            
        // 获取相应的适配器
        let adapter = self.adapters.get(&channel)
            .ok_or_else(|| NotificationError::ChannelNotAvailable(channel.to_string()))?;
            
        // 通过选定的渠道发送通知
        adapter.send_notification(notification).await
    }
}
```

**映射分析**:

- 领域层定义纯粹的通知抽象，不涉及技术细节
- 应用层协调业务流程，将领域概念转化为具体实现
- 基础设施层提供不同渠道的适配器实现
- 在运行时可灵活组合不同实现，同时保持业务逻辑独立

### 3.5 映射验证与测试策略

全面的测试策略确保映射正确性：

```rust
// 多层次测试策略
// 1. 领域模型单元测试
#[cfg(test)]
mod order_domain_tests {
    use super::*;
    
    #[test]
    fn test_add_item_to_draft_order() {
        // 创建草稿订单
        let mut order = Order::new(
            OrderId::new(),
            CustomerId::new(),
            vec![],
            None,
        );
        
        // 创建订单项
        let item = OrderItem {
            id: OrderItemId::new(),
            product_id: ProductId::new(),
            name: "Test Product".to_string(),
            unit_price: 10.0,
            quantity: 2,
            total_price: 20.0,
        };
        
        // 添加项目
        let result = order.add_item(item.clone());
        
        // 验证结果
        assert!(result.is_ok());
        assert_eq!(order.items.len(), 1);
        assert_eq!(order.items[0].quantity, 2);
        assert_eq!(order.items[0].total_price, 20.0);
    }
    
    #[test]
    fn test_add_item_to_submitted_order_fails() {
        // 创建订单
        let mut order = Order::new(
            OrderId::new(),
            CustomerId::new(),
            vec![],
            Some(Address::default()),
        );
        
        // 提交订单
        let submit_result = order.submit();
        assert!(submit_result.is_ok());
        
        // 尝试添加项目
        let item = OrderItem {
            id: OrderItemId::new(),
            product_id: ProductId::new(),
            name: "Test Product".to_string(),
            unit_price: 10.0,
            quantity: 2,
            total_price: 20.0,
        };
        
        let result = order.add_item(item);
        
        // 验证失败
        assert!(result.is_err());
        match result {
            Err(OrderError::InvalidStateTransition(msg)) => {
                assert!(msg.contains("草稿状态"));
            },
            _ => panic!("Expected InvalidStateTransition error"),
        }
    }
    
    // 更多领域测试...
}

// 2. 集成测试 - 验证应用服务与仓储
#[cfg(test)]
mod order_application_tests {
    use super::*;
    use mockall::predicate::*;
    
    // 生成模拟仓储
    mockall::mock! {
        OrderRepository {}
        
        impl OrderRepository for OrderRepository {
            fn find_by_id(&self, id: &OrderId) -> Result<Option<Order>, RepositoryError>;
            fn save(&self, order: &Order) -> Result<(), RepositoryError>;
            fn find_by_customer(&self, customer_id: &CustomerId) -> Result<Vec<Order>, RepositoryError>;
        }
    }
    
    // 生成模拟服务
    mockall::mock! {
        InventoryService {}
        
        impl InventoryService for InventoryService {
            fn get_product(&self, product_id: &ProductId) -> Result<Product, InventoryServiceError>;
            fn allocate_stock(&self, order: &Order) -> Result<(), InventoryServiceError>;
        }
    }
    
    mockall::mock! {
        PaymentService {}
        
        impl PaymentService for PaymentService {
            async fn process_payment(&self, request: &PaymentRequest) -> Result<PaymentResult, PaymentServiceError>;
            async fn refund_payment(&self, transaction_id: &str, amount: Money) -> Result<RefundResult, PaymentServiceError>;
        }
    }
    
    mockall::mock! {
        NotificationService {}
        
        impl NotificationService for NotificationService {
            fn send_notification(&self, notification: &Notification) -> Result<NotificationResult, NotificationError>;
        }
    }
    
    #[tokio::test]
    async fn test_create_order_success() {
        // 设置模拟
        let mut mock_order_repo = MockOrderRepository::new();
        mock_order_repo
            .expect_save()
            .times(1)
            .returning(|_| Ok(()));
            
        let mut mock_inventory = MockInventoryService::new();
        let product = Product {
            id: ProductId::new(),
            name: "Test Product".to_string(),
            price: Money::new_usd(10.0).unwrap(),
            // 其他产品字段...
        };
        
        mock_inventory
            .expect_get_product()
            .times(1)
            .returning(move |_| Ok(product.clone()));
            
        let mut mock_notification = MockNotificationService::new();
        mock_notification
            .expect_send_notification()
            .times(1)
            .returning(|_| Ok(NotificationResult {
                notification_id: NotificationId::new(),
                provider_id: "msg-123".to_string(),
                status: NotificationStatus::Sent,
                sent_at: Utc::now(),
            }));
            
        // 创建应用服务
        let service = OrderApplicationService {
            order_repository: Arc::new(mock_order_repo),
            inventory_service: Arc::new(mock_inventory),
            payment_service: Arc::new(MockPaymentService::new()),
            notification_service: Arc::new(mock_notification),
        };
        
        // 执行测试
        let result = service.create_order(
            CustomerId::new(),
            vec![OrderItemDto {
                product_id: ProductId::new(),
                quantity: 2,
            }],
            Some(AddressDto {
                street_line1: "123 Test St".to_string(),
                city: "Test City".to_string(),
                state: "TS".to_string(),
                postal_code: "12345".to_string(),
                country: "US".to_string(),
                // 其他地址字段...
            }),
        ).await;
        
        // 验证结果
        assert!(result.is_ok());
    }
    
    // 更多应用服务测试...
}

// 3. 适配器测试 - 验证与外部系统的映射
#[cfg(test)]
mod repository_adapter_tests {
    use super::*;
    use sqlx::{postgres::PgPoolOptions, PgPool, Row};
    use testcontainers::{clients, Docker, images::postgres::Postgres};
    
    // PostgreSQL数据库仓储测试
    #[tokio::test]
    async fn test_order_repository_find_by_id() {
        // 设置测试容器
        let docker = clients::Cli::default();
        let postgres = docker.run(Postgres::default());
        let connection_string = format!(
            "postgres://postgres:postgres@127.0.0.1:{}/postgres",
            postgres.get_host_port_ipv4(5432)
        );
        
        // 创建数据库连接池
        let pool = PgPoolOptions::new()
            .max_connections(5)
            .connect(&connection_string)
            .await
            .expect("Failed to connect to Postgres");
            
        // 创建测试架构
        setup_test_schema(&pool).await;
        
        // 插入测试数据
        let order_id = insert_test_order(&pool).await;
        
        // 创建仓储
        let repository = SqlOrderRepository { pool };
        
        // 测试查找订单
        let result = repository.find_by_id(&order_id).await;
        
        // 验证结果
        assert!(result.is_ok());
        let order_option = result.unwrap();
        assert!(order_option.is_some());
        
        let order = order_option.unwrap();
        assert_eq!(order.id, order_id);
        assert_eq!(order.items.len(), 2);
    }
    
    async fn setup_test_schema(pool

```rust
    async fn setup_test_schema(pool: &PgPool) {
        // 创建必要的表结构
        sqlx::query(r#"
            CREATE TABLE IF NOT EXISTS orders (
                id UUID PRIMARY KEY,
                customer_id UUID NOT NULL,
                status VARCHAR(50) NOT NULL,
                created_at TIMESTAMP WITH TIME ZONE NOT NULL,
                updated_at TIMESTAMP WITH TIME ZONE NOT NULL
            )
        "#).execute(pool).await.expect("Failed to create orders table");
        
        sqlx::query(r#"
            CREATE TABLE IF NOT EXISTS order_items (
                id UUID PRIMARY KEY,
                order_id UUID NOT NULL REFERENCES orders(id),
                product_id UUID NOT NULL,
                name VARCHAR(255) NOT NULL,
                unit_price DECIMAL(10, 2) NOT NULL,
                quantity INTEGER NOT NULL,
                total_price DECIMAL(10, 2) NOT NULL
            )
        "#).execute(pool).await.expect("Failed to create order_items table");
        
        sqlx::query(r#"
            CREATE TABLE IF NOT EXISTS addresses (
                id UUID PRIMARY KEY,
                entity_id UUID NOT NULL,
                entity_type VARCHAR(50) NOT NULL,
                street_line1 VARCHAR(255) NOT NULL,
                street_line2 VARCHAR(255),
                city VARCHAR(100) NOT NULL,
                state VARCHAR(100) NOT NULL,
                postal_code VARCHAR(20) NOT NULL,
                country VARCHAR(2) NOT NULL,
                UNIQUE(entity_id, entity_type)
            )
        "#).execute(pool).await.expect("Failed to create addresses table");
    }
    
    async fn insert_test_order(pool: &PgPool) -> OrderId {
        let order_id = OrderId::new();
        let customer_id = CustomerId::new();
        
        // 插入订单
        sqlx::query(r#"
            INSERT INTO orders (id, customer_id, status, created_at, updated_at)
            VALUES ($1, $2, $3, $4, $5)
        "#)
        .bind(order_id.to_uuid())
        .bind(customer_id.to_uuid())
        .bind("DRAFT")
        .bind(Utc::now())
        .bind(Utc::now())
        .execute(pool)
        .await
        .expect("Failed to insert test order");
        
        // 插入订单项
        let item1_id = OrderItemId::new();
        let product1_id = ProductId::new();
        
        sqlx::query(r#"
            INSERT INTO order_items (id, order_id, product_id, name, unit_price, quantity, total_price)
            VALUES ($1, $2, $3, $4, $5, $6, $7)
        "#)
        .bind(item1_id.to_uuid())
        .bind(order_id.to_uuid())
        .bind(product1_id.to_uuid())
        .bind("Test Product 1")
        .bind(10.0)
        .bind(2)
        .bind(20.0)
        .execute(pool)
        .await
        .expect("Failed to insert first order item");
        
        let item2_id = OrderItemId::new();
        let product2_id = ProductId::new();
        
        sqlx::query(r#"
            INSERT INTO order_items (id, order_id, product_id, name, unit_price, quantity, total_price)
            VALUES ($1, $2, $3, $4, $5, $6, $7)
        "#)
        .bind(item2_id.to_uuid())
        .bind(order_id.to_uuid())
        .bind(product2_id.to_uuid())
        .bind("Test Product 2")
        .bind(15.0)
        .bind(1)
        .bind(15.0)
        .execute(pool)
        .await
        .expect("Failed to insert second order item");
        
        // 插入地址
        let address_id = Uuid::new_v4();
        
        sqlx::query(r#"
            INSERT INTO addresses (id, entity_id, entity_type, street_line1, street_line2, city, state, postal_code, country)
            VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9)
        "#)
        .bind(address_id)
        .bind(order_id.to_uuid())
        .bind("ORDER")
        .bind("123 Test St")
        .bind("")
        .bind("Test City")
        .bind("TS")
        .bind("12345")
        .bind("US")
        .execute(pool)
        .await
        .expect("Failed to insert address");
        
        order_id
    }
}

// 4. 端到端测试 - 验证整个系统流程
#[cfg(test)]
mod end_to_end_tests {
    use super::*;
    use testcontainers::{clients, Docker, images};
    use actix_web::{test, App, web};
    
    #[actix_web::test]
    async fn test_create_and_process_order() {
        // 设置测试容器
        let docker = clients::Cli::default();
        
        // PostgreSQL
        let postgres = docker.run(images::postgres::Postgres::default());
        let db_connection_string = format!(
            "postgres://postgres:postgres@127.0.0.1:{}/postgres",
            postgres.get_host_port_ipv4(5432)
        );
        
        // Redis (用于缓存)
        let redis = docker.run(images::redis::Redis::default());
        let redis_connection_string = format!(
            "redis://127.0.0.1:{}/",
            redis.get_host_port_ipv4(6379)
        );
        
        // 设置数据库连接池
        let pool = PgPoolOptions::new()
            .max_connections(5)
            .connect(&db_connection_string)
            .await
            .expect("Failed to connect to Postgres");
            
        // 设置测试架构
        setup_test_schema(&pool).await;
        
        // 设置必要的依赖
        let order_repository = Arc::new(SqlOrderRepository { pool: pool.clone() });
        let customer_repository = Arc::new(SqlCustomerRepository { pool: pool.clone() });
        let product_repository = Arc::new(SqlProductRepository { pool: pool.clone() });
        
        // 使用模拟外部服务
        let payment_gateway = Arc::new(MockPaymentGateway::new());
        let email_service = Arc::new(MockEmailService::new());
        
        // 创建应用服务
        let order_service = Arc::new(OrderApplicationService {
            order_repository: order_repository.clone(),
            inventory_service: Arc::new(WarehouseInventoryService::new(
                "http://mock-warehouse-api"
            )),
            payment_service: Arc::new(StripePaymentAdapter {
                client: reqwest::Client::new(),
                gateway: payment_gateway.clone(),
            }),
            notification_service: Arc::new(EmailNotificationAdapter {
                client: email_service.clone(),
            }),
        });
        
        // 创建控制器
        let order_controller = OrderController {
            order_service: order_service.clone(),
        };
        
        // 设置测试用户
        let customer_id = insert_test_customer(&pool).await;
        
        // 设置测试产品
        let product_id = insert_test_product(&pool).await;
        
        // 创建测试应用
        let app = test::init_service(
            App::new()
                .app_data(web::Data::new(order_controller))
                .route("/orders", web::post().to(OrderController::create_order))
                .route("/orders/{id}/payments", web::post().to(OrderController::process_payment))
        ).await;
        
        // 测试创建订单
        let create_request = CreateOrderRequest {
            items: vec![OrderItemDto {
                product_id,
                quantity: 2,
            }],
            shipping_address: Some(AddressDto {
                street_line1: "123 Test St".to_string(),
                street_line2: "".to_string(),
                city: "Test City".to_string(),
                state: "TS".to_string(),
                postal_code: "12345".to_string(),
                country: "US".to_string(),
            }),
        };
        
        let create_resp = test::TestRequest::post()
            .uri("/orders")
            .set_json(&create_request)
            .header("X-Customer-ID", customer_id.to_string())
            .send_request(&app)
            .await;
            
        assert_eq!(create_resp.status(), 201);
        
        let order: OrderDto = test::read_body_json(create_resp).await;
        assert_eq!(order.status, "DRAFT");
        
        // 测试处理支付
        let payment_request = ProcessPaymentRequest {
            payment_method: PaymentMethodDto::CreditCard(CreditCardDto {
                number: "4242424242424242".to_string(),
                expiry_month: 12,
                expiry_year: 25,
                cvv: "123".to_string(),
                holder_name: "Test User".to_string(),
            }),
        };
        
        let payment_resp = test::TestRequest::post()
            .uri(&format!("/orders/{}/payments", order.id))
            .set_json(&payment_request)
            .header("X-Customer-ID", customer_id.to_string())
            .send_request(&app)
            .await;
            
        assert_eq!(payment_resp.status(), 200);
        
        let payment_result: PaymentResultDto = test::read_body_json(payment_resp).await;
        assert_eq!(payment_result.status, "SUCCEEDED");
        
        // 验证订单状态已更新
        let updated_order = order_repository.find_by_id(&OrderId::from_string(&order.id).unwrap())
            .await
            .unwrap()
            .unwrap();
            
        assert_eq!(updated_order.status, OrderStatus::Paid);
        
        // 验证通知已发送
        assert!(email_service.has_email_for(&updated_order.customer_id.to_string()));
    }
    
    // 辅助函数...
}

// 5. 属性测试 - 验证特定属性在各种输入下保持不变
#[cfg(test)]
mod property_tests {
    use super::*;
    use proptest::prelude::*;
    
    // 生成有效的订单项
    fn order_item_strategy() -> impl Strategy<Value = OrderItem> {
        (
            any::<u64>(),    // 用于生成ID
            any::<u64>(),    // 用于生成产品ID
            "\\PC{1,50}",    // 产品名称
            1.0..10000.0,    // 单价
            1u32..100,       // 数量
        ).prop_map(|(id_seed, product_seed, name, unit_price, quantity)| {
            let id = OrderItemId::from_uuid(Uuid::from_u64_pair(id_seed, 0));
            let product_id = ProductId::from_uuid(Uuid::from_u64_pair(product_seed, 0));
            let total_price = unit_price * quantity as f64;
            
            OrderItem {
                id,
                product_id,
                name,
                unit_price,
                quantity,
                total_price,
            }
        })
    }
    
    // 生成有效的订单
    fn order_strategy() -> impl Strategy<Value = Order> {
        (
            any::<u64>(),    // 用于生成订单ID
            any::<u64>(),    // 用于生成客户ID
            proptest::collection::vec(order_item_strategy(), 0..10),  // 0-10个订单项
        ).prop_map(|(order_seed, customer_seed, items)| {
            let id = OrderId::from_uuid(Uuid::from_u64_pair(order_seed, 0));
            let customer_id = CustomerId::from_uuid(Uuid::from_u64_pair(customer_seed, 0));
            
            Order::new(
                id,
                customer_id,
                items,
                None,
            )
        })
    }
    
    proptest! {
        // 属性：添加项目后，订单总金额等于所有项目金额之和
        #[test]
        fn test_order_total_equals_sum_of_items(
            mut order in order_strategy(),
            item in order_item_strategy()
        ) {
            // 跳过非草稿状态的订单
            if order.status != OrderStatus::Draft {
                return Ok(());
            }
            
            let initial_total = order.calculate_total();
            let item_price = Money::new_usd(item.total_price).unwrap();
            
            // 添加新项目
            let result = order.add_item(item);
            prop_assert!(result.is_ok());
            
            // 计算新总额
            let new_total = order.calculate_total();
            
            // 验证总额增加了正确的金额
            prop_assert_eq!(new_total.value(), initial_total.value() + item_price.value());
        }
        
        // 属性：订单提交后不能修改
        #[test]
        fn test_submitted_order_is_immutable(
            mut order in order_strategy(),
            item in order_item_strategy()
        ) {
            // 确保订单有配送地址和至少一个商品
            if order.items.is_empty() {
                let result = order.add_item(item);
                prop_assert!(result.is_ok());
            }
            
            if order.shipping_address.is_none() {
                order.shipping_address = Some(Address::default());
            }
            
            // 提交订单
            let submit_result = order.submit();
            prop_assert!(submit_result.is_ok());
            prop_assert_eq!(order.status, OrderStatus::Submitted);
            
            // 保存订单状态
            let submitted_status = order.status.clone();
            let items_count = order.items.len();
            
            // 尝试添加新项目（应该失败）
            let add_result = order.add_item(item);
            prop_assert!(add_result.is_err());
            
            // 验证状态未改变
            prop_assert_eq!(order.status, submitted_status);
            prop_assert_eq!(order.items.len(), items_count);
        }
    }
}

// 6. 映射验证器 - 自动验证映射的一致性
pub struct MappingValidator;

impl MappingValidator {
    // 验证领域对象到DTO的映射保持标识符一致性
    pub fn validate_identity_preservation<T, DTO, ID>(
        domain_object: &T,
        dto: &DTO,
        domain_id_extractor: fn(&T) -> &ID,
        dto_id_extractor: fn(&DTO) -> &str,
        id_to_string: fn(&ID) -> String,
    ) -> Result<(), MappingValidationError> {
        let domain_id = domain_id_extractor(domain_object);
        let domain_id_str = id_to_string(domain_id);
        let dto_id = dto_id_extractor(dto);
        
        if domain_id_str != dto_id {
            return Err(MappingValidationError::IdentityMismatch {
                expected: domain_id_str,
                actual: dto_id.to_string(),
            });
        }
        
        Ok(())
    }
    
    // 验证DTO到领域对象的映射保持标识符一致性
    pub fn validate_dto_to_domain_identity<T, DTO, ID>(
        dto: &DTO,
        domain_object: &T,
        dto_id_extractor: fn(&DTO) -> &str,
        domain_id_extractor: fn(&T) -> &ID,
        id_to_string: fn(&ID) -> String,
    ) -> Result<(), MappingValidationError> {
        Self::validate_identity_preservation(
            domain_object,
            dto,
            domain_id_extractor,
            dto_id_extractor,
            id_to_string,
        )
    }
    
    // 验证金额映射的一致性
    pub fn validate_money_mapping<T, DTO>(
        domain_object: &T,
        dto: &DTO,
        domain_money_extractor: fn(&T) -> &Money,
        dto_amount_extractor: fn(&DTO) -> f64,
        dto_currency_extractor: fn(&DTO) -> &str,
    ) -> Result<(), MappingValidationError> {
        let domain_money = domain_money_extractor(domain_object);
        let dto_amount = dto_amount_extractor(dto);
        let dto_currency = dto_currency_extractor(dto);
        
        // 检查金额
        if (domain_money.value() - dto_amount).abs() > 0.001 {
            return Err(MappingValidationError::AmountMismatch {
                expected: domain_money.value(),
                actual: dto_amount,
            });
        }
        
        // 检查货币
        if domain_money.currency().code() != dto_currency {
            return Err(MappingValidationError::CurrencyMismatch {
                expected: domain_money.currency().code().to_string(),
                actual: dto_currency.to_string(),
            });
        }
        
        Ok(())
    }
    
    // 验证集合映射的一致性
    pub fn validate_collection_mapping<T, DTO, TItem, DTOItem, TID>(
        domain_object: &T,
        dto: &DTO,
        domain_collection_extractor: fn(&T) -> &Vec<TItem>,
        dto_collection_extractor: fn(&DTO) -> &Vec<DTOItem>,
        domain_item_id_extractor: fn(&TItem) -> &TID,
        dto_item_id_extractor: fn(&DTOItem) -> &str,
        id_to_string: fn(&TID) -> String,
    ) -> Result<(), MappingValidationError> {
        let domain_items = domain_collection_extractor(domain_object);
        let dto_items = dto_collection_extractor(dto);
        
        // 检查集合大小
        if domain_items.len() != dto_items.len() {
            return Err(MappingValidationError::CollectionSizeMismatch {
                expected: domain_items.len(),
                actual: dto_items.len(),
            });
        }
        
        // 创建域对象ID到索引的映射
        let mut domain_id_map = HashMap::new();
        for (index, item) in domain_items.iter().enumerate() {
            let id = id_to_string(domain_item_id_extractor(item));
            domain_id_map.insert(id, index);
        }
        
        // 验证每个DTO项目都有匹配的域对象项目
        for dto_item in dto_items {
            let dto_id = dto_item_id_extractor(dto_item);
            if !domain_id_map.contains_key(dto_id) {
                return Err(MappingValidationError::ItemNotFound(dto_id.to_string()));
            }
        }
        
        Ok(())
    }
}

// 映射验证测试
#[cfg(test)]
mod mapping_tests {
    use super::*;
    
    #[test]
    fn test_order_dto_mapping() {
        // 创建域对象
        let order_id = OrderId::new();
        let customer_id = CustomerId::new();
        
        let item1 = OrderItem {
            id: OrderItemId::new(),
            product_id: ProductId::new(),
            name: "Product 1".to_string(),
            unit_price: 10.0,
            quantity: 2,
            total_price: 20.0,
        };
        
        let item2 = OrderItem {
            id: OrderItemId::new(),
            product_id: ProductId::new(),
            name: "Product 2".to_string(),
            unit_price: 15.0,
            quantity: 1,
            total_price: 15.0,
        };
        
        let order = Order {
            id: order_id.clone(),
            customer_id,
            items: vec![item1.clone(), item2.clone()],
            status: OrderStatus::Draft,
            shipping_address: Some(Address {
                street_line1: "123 Test St".to_string(),
                street_line2: "".to_string(),
                city: "Test City".to_string(),
                state: "TS".to_string(),
                postal_code: "12345".to_string(),
                country: "US".to_string(),
            }),
            payment_status: PaymentStatus::Pending,
            created_at: Utc::now(),
            updated_at: Utc::now(),
        };
        
        // 转换为DTO
        let order_dto = OrderDto::from_domain(&order);
        
        // 验证身份映射
        let result = MappingValidator::validate_identity_preservation(
            &order,
            &order_dto,
            |o| &o.id,
            |dto| &dto.id,
            |id| id.to_string(),
        );
        
        assert!(result.is_ok());
        
        // 验证集合映射
        let result = MappingValidator::validate_collection_mapping(
            &order,
            &order_dto,
            |o| &o.items,
            |dto| &dto.items,
            |item| &item.id,
            |dto_item| &dto_item.id,
            |id| id.to_string(),
        );
        
        assert!(result.is_ok());
        
        // 验证总金额映射
        let result = MappingValidator::validate_money_mapping(
            &order,
            &order_dto,
            |o| &o.calculate_total(),
            |dto| dto.total_amount,
            |dto| &dto.currency,
        );
        
        assert!(result.is_ok());
    }
}
```

## 4. 现实世界映射的挑战与解决方案

### 4.1 处理模型差异与不一致

针对不同领域抽象级别的差异解决方案：

```rust
// 模型不一致挑战示例
// 内部领域模型
#[derive(Debug, Clone)]
pub struct Customer {
    id: CustomerId,
    name: String,
    email: Email,
    phone: Option<PhoneNumber>,
    address: Option<Address>,
    customer_type: CustomerType,
    status: CustomerStatus,
    created_at: DateTime<Utc>,
    preferences: CustomerPreferences,
}

// 第三方CRM系统模型
#[derive(Debug, Serialize, Deserialize)]
pub struct CrmContact {
    contact_id: String,
    first_name: String,
    last_name: String,
    email_address: String,
    mobile_phone: Option<String>,
    work_phone: Option<String>,
    addresses: Vec<CrmAddress>,
    segment: String,
    is_active: bool,
    creation_date: String,
    custom_fields: HashMap<String, serde_json::Value>,
}

// 适配器解决方案
pub struct CrmSynchronizer {
    crm_client: Arc<dyn CrmClient>,
    customer_repository: Arc<dyn CustomerRepository>,
    sync_log_repository: Arc<dyn SyncLogRepository>,
}

impl CrmSynchronizer {
    pub async fn sync_customer_to_crm(
        &self,
        customer_id: &CustomerId,
    ) -> Result<SyncResult, SyncError> {
        // 获取客户
        let customer = self.customer_repository.find_by_id(customer_id).await?
            .ok_or_else(|| SyncError::EntityNotFound(format!("Customer {}", customer_id)))?;
            
        // 检查是否需要与CRM系统同步
        if !self.should_sync_with_crm(&customer) {
            return Ok(SyncResult::Skipped { reason: "Customer not eligible for CRM sync".into() });
        }
            
        // 转换为CRM联系人格式
        let crm_contact = self.map_customer_to_crm_contact(&customer)?;
        
        // 检查CRM中是否已存在
        let existing_contact = self.crm_client.find_contact_by_email(&customer.email.value()).await?;
        
        let result = if let Some(existing) = existing_contact {
            // 更新现有联系人
            let updated_contact = self.crm_client.update_contact(&existing.contact_id, &crm_contact).await?;
            SyncResult::Updated { external_id: updated_contact.contact_id }
        } else {
            // 创建新联系人
            let new_contact = self.crm_client.create_contact(&crm_contact).await?;
            SyncResult::Created { external_id: new_contact.contact_id }
        };
        
        // 记录同步结果
        self.log_sync_result(customer_id, &result).await?;
        
        Ok(result)
    }
    
    pub async fn sync_from_crm_to_customer(
        &self,
        crm_contact_id: &str,
    ) -> Result<SyncResult, SyncError> {
        // 从CRM获取联系人
        let crm_contact = self.crm_client.get_contact(crm_contact_id).await?;
        
        // 尝试查找已存在的客户
        let existing_customer = self.customer_repository
            .find_by_email(&Email::try_from(crm_contact.email_address.clone())?)
            .await?;
            
        // 将CRM联系人映射到客户
        let mut customer = self.map_crm_contact_to_customer(&crm_contact, existing_customer.as_ref())?;
        
        // 保存客户
        let result = if existing_customer.is_some() {
            self.customer_repository.update(&customer).await?;
            SyncResult::Updated { external_id: customer.id.to_string() }
        } else {
            self.customer_repository.create(&customer).await?;
            SyncResult::Created { external_id: customer.id.to_string() }
        };
        
        // 记录同步结果
        self.log_sync_result(&customer.id, &result).await?;
        
        Ok(result)
    }
    
    fn should_sync_with_crm(&self, customer: &Customer) -> bool {
        // 基于一些业务规则决定是否同步
        // 例如，只同步活跃客户
        if customer.status != CustomerStatus::Active {
            return false;
        }
        
        // 确保有电子邮件
        if customer.email.value().is_empty() {
            return false;
        }
        
        // 根据客户类型决定
        match customer.customer_type {
            CustomerType::Individual | CustomerType::Business => true,
            CustomerType::Guest => false,
            CustomerType::Internal => false,
        }
    }
    
    fn map_customer_to_crm_contact(&self, customer: &Customer) -> Result<CrmContact, SyncError> {
        // 分解全名为姓和名
        let (first_name, last_name) = self.split_full_name(&customer.name);
        
        // 转换地址
        let addresses = if let Some(address) = &customer.address {
            vec![CrmAddress {
                address_type: "PRIMARY".to_string(),
                street1: address.street_line1.clone(),
                street2: address.street_line2.clone(),
                city: address.city.clone(),
                state: address.state.clone(),
                postal_code: address.postal_code.clone(),
                country: address.country.clone(),
                is_default: true,
            }]
        } else {
            vec![]
        };
        
        // 转换客户类型为CRM细分市场
        let segment = match customer.customer_type {
            CustomerType::Individual => "CONSUMER".to_string(),
            CustomerType::Business => "BUSINESS".to_string(),
            CustomerType::Guest => "PROSPECT".to_string(),
            CustomerType::Internal => "EMPLOYEE".to_string(),
        };
        
        // 客户偏好转换为自定义字段
        let mut custom_fields = HashMap::new();
        
        if let Some(marketing_pref) = &customer.preferences.marketing_preferences {
            custom_fields.insert(
                "marketing_consent".to_string(),
                serde_json::Value::Bool(marketing_pref.has_consent)
            );
            
            custom_fields.insert(
                "preferred_channels".to_string(),
                serde_json::Value::String(marketing_pref.preferred_channels.join(","))
            );
        }
        
        if let Some(communication_pref) = &customer.preferences.communication_preferences {
            custom_fields.insert(
                "preferred_language".to_string(),
                serde_json::Value::String(communication_pref.preferred_language.clone())
            );
            
            custom_fields.insert(
                "communication_frequency".to_string(),
                serde_json::Value::String(communication_pref.frequency.to_string())
            );
        }
        
        // 构建CRM联系人
        let crm_contact = CrmContact {
            contact_id: "".to_string(), // 新联系人留空
            first_name,
            last_name,
            email_address: customer.email.value(),
            mobile_phone: customer.phone.as_ref().map(|p| p.value()),
            work_phone: None, // 我们的内部模型没有工作电话
            addresses,
            segment,
            is_active: customer.status == CustomerStatus::Active,
            creation_date: customer.created_at.to_rfc3339(),
            custom_fields,
        };
        
        Ok(crm_contact)
    }
    
    fn map_crm_contact_to_customer(
        &self,
        contact: &CrmContact,
        existing: Option<&Customer>,
    ) -> Result<Customer, SyncError> {
        // 合并姓名
        let name = format!("{} {}", contact.first_name, contact.last_name);
        
        // 电子邮件验证
        let email = Email::try_from(contact.email_address.clone())?;
        
        // 电话处理
        let phone = contact.mobile_phone.as_ref()
            .or(contact.work_phone.as_ref())
            .map(|p| PhoneNumber::try_from(p.clone()))
            .transpose()?;
            
        // 地址处理
        let address = contact.addresses.iter()
            .find(|addr| addr.is_default || addr.address_type == "PRIMARY")
            .map(|addr| Address {
                street_line1: addr.street1.clone(),
                street_line2: addr.street2.clone(),
                city: addr.city.clone(),
                state: addr.state.clone(),
                postal_code: addr.postal_code.clone(),
                country: addr.country.clone(),
            });
            
        // 客户类型映射
        let customer_type = match contact.segment.as_str() {
            "CONSUMER" => CustomerType::Individual,
            "BUSINESS" => CustomerType::Business,
            "PROSPECT" => CustomerType::Guest,
            "EMPLOYEE" => CustomerType::Internal,
            _ => CustomerType::Individual, // 默认
        };
        
        // 状态映射
        let status = if contact.is_active {
            CustomerStatus::Active
        } else {
            CustomerStatus::Inactive
        };
        
        // 处理自定义字段
        let mut preferences = CustomerPreferences::default();
        
        if let Some(marketing_consent) = contact.custom_fields.get("marketing_consent") {
            if let Some(consent) = marketing_consent.as_bool() {
                let preferred_channels = contact.custom_fields.get("preferred_channels")
                    .and_then(|v| v.as_str())
                    .map(|s| s.split(',').map(String::from).collect())
                    .unwrap_or_else(Vec::new);
                    
                preferences.marketing_preferences = Some(MarketingPreferences {
                    has_consent: consent,
                    consent_date: Utc::now(), // 我们没有这个信息，使用当前时间
                    preferred_channels,
                });
            }
        }
        
        if let Some(language) = contact.custom_fields.get("preferred_language").and_then(|v| v.as_str()) {
            let frequency = contact.custom_fields.get("communication_frequency")
                .and_then(|v| v.as_str())
                .map(|s| CommunicationFrequency::from_string(s))
                .unwrap_or(CommunicationFrequency::Normal);
                
            preferences.communication_preferences = Some(CommunicationPreferences {
                preferred_language: language.to_string(),
                frequency,
            });
        }
        
        // 创建或更新客户
        let customer = Customer {
            id: existing.map(|c| c.id.clone()).unwrap_or_else(CustomerId::new),
            name,
            email,
            phone,
            address,
            customer_type,
            status,
            created_at: existing.map(|c| c.created_at).unwrap_or_else(Utc::now),
            preferences,
        };
        
        Ok(customer)
    }
    
    fn split_full_name(&self, full_name: &str) -> (String, String) {
        let parts: Vec<&str> = full_name.split_whitespace().collect();
        
        if parts.is_empty() {
            return ("".to_string(), "".to_string());
        }
        
        if parts.len() == 1 {
            return (parts[0].to_string(), "".to_string());
        }
        
        let first_name = parts[0].to_string();
        let last_name = parts[1..].join(" ");
        
        (first_name, last_name)
    }
    
    async fn log_sync_result(
        &self,
        entity_id: &CustomerId,
        result: &SyncResult,
    ) -> Result<(), SyncError> {
        let log_entry = SyncLogEntry {
            id: SyncLogId::new(),
            entity_id: entity_id.to_string(),
            entity_type: "Customer".to_string(),
            sync_type: match result {
                SyncResult::Created { .. } => SyncType::Create,
                SyncResult::Updated { .. } => SyncType::Update,
                SyncResult::Skipped { .. } => SyncType::Skip,
            },
            external_id: match result {
                SyncResult::Created { external_id } => Some(external_id.clone()),
                SyncResult::Updated { external_id } => Some(external_id.clone()),
                SyncResult::Skipped { .. } => None,
            },
            result_details: match result {
                SyncResult::Skipped { reason } => Some(reason.clone()),
                _ => None,
            },
            timestamp: Utc::now(),
        };
        
        self.sync_log_repository.save(&log_entry).await?;
        
        Ok(())
    }
}
```

**映射分析**:

- 使用专门的同步器处理不同系统间的数据映射
- 实现双向映射功能，支持模型差异调和
- 添加数据转换和验证逻辑处理格式差异
- 跟踪同步历史记录支持故障分析和排除

### 4.2 处理演化与兼容性

处理模型和接口随时间演化的挑战：

```rust
// 版本化的API模型
mod v1 {
    use serde::{Serialize, Deserialize};
    
    #[derive(Debug, Serialize, Deserialize)]
    pub struct ProductDto {
        pub id: String,
        pub name: String,
        pub description: String,
        pub price: f64,
        pub category: String,
        pub in_stock: bool,
    }
}

mod v2 {
    use serde::{Serialize, Deserialize};
    use chrono::{DateTime, Utc};
    
    #[derive(Debug, Serialize, Deserialize)]
    pub struct ProductDto {
        pub id: String,
        pub name: String,
        pub description: String,
        pub pricing: PricingInfo,
        pub categories: Vec<String>,
        pub inventory: InventoryInfo,
        pub attributes: std::collections::HashMap<String, String>,
        pub created_at: DateTime<Utc>,
        pub updated_at: DateTime<Utc>,
    }
    
    #[derive(Debug, Serialize, Deserialize)]
    pub struct PricingInfo {
        pub base_price: f64,
        pub currency: String,
        pub discount_percent: Option<f64>,
        pub tax_rate: Option<f64>,
    }
    
    #[derive(Debug, Serialize, Deserialize)]
    pub struct InventoryInfo {
        pub in_stock: bool,
        pub quantity: u32,
        pub warehouse_location: Option<String>,
        pub restock

```rust
        pub restock_date: Option<DateTime<Utc>>,
        pub minimum_order_quantity: Option<u32>,
    }
}

// 版本适配器 - 处理API版本之间的转换
pub struct ProductVersionAdapter {
    product_repository: Arc<dyn ProductRepository>,
}

impl ProductVersionAdapter {
    // 从内部模型转换为V1 API模型
    pub fn to_v1_dto(&self, product: &Product) -> v1::ProductDto {
        v1::ProductDto {
            id: product.id.to_string(),
            name: product.name.clone(),
            description: product.description.clone(),
            price: product.price.value(),
            category: product.categories.first()
                .map(|c| c.name.clone())
                .unwrap_or_else(|| "Uncategorized".to_string()),
            in_stock: product.inventory_status == InventoryStatus::InStock,
        }
    }
    
    // 从内部模型转换为V2 API模型
    pub fn to_v2_dto(&self, product: &Product) -> v2::ProductDto {
        // 准备分类列表
        let categories = product.categories.iter()
            .map(|c| c.name.clone())
            .collect();
            
        // 准备属性映射
        let attributes = product.attributes.iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
            
        // 准备价格信息
        let pricing = v2::PricingInfo {
            base_price: product.price.value(),
            currency: product.price.currency().code().to_string(),
            discount_percent: product.discount_rate,
            tax_rate: product.tax_rate,
        };
        
        // 准备库存信息
        let inventory = v2::InventoryInfo {
            in_stock: product.inventory_status == InventoryStatus::InStock,
            quantity: product.stock_quantity,
            warehouse_location: product.warehouse_location.clone(),
            restock_date: product.restock_date,
            minimum_order_quantity: product.minimum_order_quantity,
        };
        
        v2::ProductDto {
            id: product.id.to_string(),
            name: product.name.clone(),
            description: product.description.clone(),
            pricing,
            categories,
            inventory,
            attributes,
            created_at: product.created_at,
            updated_at: product.updated_at,
        }
    }
    
    // 从V1 API模型转换为内部模型
    pub fn from_v1_dto(
        &self,
        dto: v1::ProductDto,
        existing: Option<&Product>,
    ) -> Result<Product, DtoConversionError> {
        let now = Utc::now();
        
        // 创建单个分类
        let category = ProductCategory {
            id: ProductCategoryId::new(),
            name: dto.category,
        };
        
        // 处理价格
        let price = Money::new(
            dto.price,
            existing.map(|p| p.price.currency().clone()).unwrap_or(Currency::USD),
        )?;
        
        // 创建或更新产品
        let product = Product {
            id: existing.map(|p| p.id.clone()).unwrap_or_else(ProductId::new),
            name: dto.name,
            description: dto.description,
            price,
            categories: vec![category],
            inventory_status: if dto.in_stock {
                InventoryStatus::InStock
            } else {
                InventoryStatus::OutOfStock
            },
            stock_quantity: existing.map(|p| p.stock_quantity).unwrap_or(0),
            warehouse_location: existing.map(|p| p.warehouse_location.clone()).unwrap_or(None),
            restock_date: existing.map(|p| p.restock_date).unwrap_or(None),
            minimum_order_quantity: existing.map(|p| p.minimum_order_quantity).unwrap_or(None),
            discount_rate: existing.map(|p| p.discount_rate).unwrap_or(None),
            tax_rate: existing.map(|p| p.tax_rate).unwrap_or(None),
            attributes: existing.map(|p| p.attributes.clone()).unwrap_or_default(),
            created_at: existing.map(|p| p.created_at).unwrap_or(now),
            updated_at: now,
        };
        
        Ok(product)
    }
    
    // 从V2 API模型转换为内部模型
    pub fn from_v2_dto(
        &self,
        dto: v2::ProductDto,
        existing: Option<&Product>,
    ) -> Result<Product, DtoConversionError> {
        let now = Utc::now();
        
        // 处理分类
        let categories = dto.categories.into_iter()
            .map(|name| ProductCategory {
                id: ProductCategoryId::new(),
                name,
            })
            .collect();
            
        // 处理价格
        let price = Money::new(
            dto.pricing.base_price,
            Currency::from_code(&dto.pricing.currency)?,
        )?;
        
        // 创建或更新产品
        let product = Product {
            id: existing.map(|p| p.id.clone()).unwrap_or_else(ProductId::new),
            name: dto.name,
            description: dto.description,
            price,
            categories,
            inventory_status: if dto.inventory.in_stock {
                InventoryStatus::InStock
            } else {
                InventoryStatus::OutOfStock
            },
            stock_quantity: dto.inventory.quantity,
            warehouse_location: dto.inventory.warehouse_location,
            restock_date: dto.inventory.restock_date,
            minimum_order_quantity: dto.inventory.minimum_order_quantity,
            discount_rate: dto.pricing.discount_percent,
            tax_rate: dto.pricing.tax_rate,
            attributes: dto.attributes,
            created_at: existing.map(|p| p.created_at).unwrap_or(dto.created_at),
            updated_at: now,
        };
        
        Ok(product)
    }
    
    // 根据请求版本获取产品
    pub async fn get_product_by_version(
        &self,
        product_id: &ProductId,
        version: ApiVersion,
    ) -> Result<serde_json::Value, ProductApiError> {
        // 获取产品
        let product = self.product_repository.find_by_id(product_id).await?
            .ok_or_else(|| ProductApiError::NotFound(product_id.to_string()))?;
            
        // 根据请求的版本返回不同格式
        match version {
            ApiVersion::V1 => {
                let dto = self.to_v1_dto(&product);
                Ok(serde_json::to_value(dto)?)
            },
            ApiVersion::V2 => {
                let dto = self.to_v2_dto(&product);
                Ok(serde_json::to_value(dto)?)
            },
        }
    }
    
    // 根据版本更新产品
    pub async fn update_product_by_version(
        &self,
        product_id: &ProductId,
        data: serde_json::Value,
        version: ApiVersion,
    ) -> Result<serde_json::Value, ProductApiError> {
        // 获取现有产品
        let existing = self.product_repository.find_by_id(product_id).await?;
        
        // 转换输入数据并更新
        let updated_product = match version {
            ApiVersion::V1 => {
                let dto: v1::ProductDto = serde_json::from_value(data)?;
                self.from_v1_dto(dto, existing.as_ref())?
            },
            ApiVersion::V2 => {
                let dto: v2::ProductDto = serde_json::from_value(data)?;
                self.from_v2_dto(dto, existing.as_ref())?
            },
        };
        
        // 保存更新后的产品
        self.product_repository.save(&updated_product).await?;
        
        // 返回更新后的产品，使用请求的版本格式
        match version {
            ApiVersion::V1 => {
                let dto = self.to_v1_dto(&updated_product);
                Ok(serde_json::to_value(dto)?)
            },
            ApiVersion::V2 => {
                let dto = self.to_v2_dto(&updated_product);
                Ok(serde_json::to_value(dto)?)
            },
        }
    }
}

// 数据库模式迁移
#[derive(Debug, Clone)]
pub struct DatabaseMigrator {
    pool: PgPool,
    logger: Arc<dyn Logger>,
}

impl DatabaseMigrator {
    pub async fn migrate(&self) -> Result<(), MigrationError> {
        // 检查当前版本
        let current_version = self.get_current_version().await?;
        self.logger.info(&format!("Current database version: {}", current_version));
        
        // 应用所有未应用的迁移
        for version in (current_version + 1)..=LATEST_VERSION {
            self.logger.info(&format!("Migrating to version {}", version));
            self.apply_migration(version).await?;
            self.update_version(version).await?;
        }
        
        Ok(())
    }
    
    async fn get_current_version(&self) -> Result<i32, MigrationError> {
        // 检查版本表是否存在
        let version_table_exists = sqlx::query(
            "SELECT EXISTS (
                SELECT FROM pg_tables 
                WHERE schemaname = 'public' 
                AND tablename = 'schema_version'
            )"
        )
        .fetch_one(&self.pool)
        .await?
        .get::<bool, _>(0);
        
        if !version_table_exists {
            // 创建版本表
            sqlx::query(
                "CREATE TABLE schema_version (
                    version INTEGER PRIMARY KEY,
                    applied_at TIMESTAMP WITH TIME ZONE NOT NULL
                )"
            )
            .execute(&self.pool)
            .await?;
            
            return Ok(0); // 初始版本
        }
        
        // 获取当前版本
        let result = sqlx::query("SELECT MAX(version) FROM schema_version")
            .fetch_one(&self.pool)
            .await?;
            
        let current_version: Option<i32> = result.get(0);
        Ok(current_version.unwrap_or(0))
    }
    
    async fn update_version(&self, version: i32) -> Result<(), MigrationError> {
        sqlx::query(
            "INSERT INTO schema_version (version, applied_at) VALUES ($1, $2)"
        )
        .bind(version)
        .bind(Utc::now())
        .execute(&self.pool)
        .await?;
        
        Ok(())
    }
    
    async fn apply_migration(&self, version: i32) -> Result<(), MigrationError> {
        // 事务处理迁移
        let mut tx = self.pool.begin().await?;
        
        match version {
            1 => {
                // 初始架构
                sqlx::query(
                    "CREATE TABLE products (
                        id UUID PRIMARY KEY,
                        name VARCHAR(255) NOT NULL,
                        description TEXT,
                        price DECIMAL(10, 2) NOT NULL,
                        category VARCHAR(100) NOT NULL,
                        in_stock BOOLEAN NOT NULL DEFAULT FALSE,
                        created_at TIMESTAMP WITH TIME ZONE NOT NULL,
                        updated_at TIMESTAMP WITH TIME ZONE NOT NULL
                    )"
                )
                .execute(&mut tx)
                .await?;
            },
            2 => {
                // 添加新字段
                sqlx::query(
                    "ALTER TABLE products 
                    ADD COLUMN stock_quantity INTEGER NOT NULL DEFAULT 0,
                    ADD COLUMN currency VARCHAR(3) NOT NULL DEFAULT 'USD'"
                )
                .execute(&mut tx)
                .await?;
            },
            3 => {
                // 拆分类别到单独的表
                sqlx::query(
                    "CREATE TABLE product_categories (
                        id UUID PRIMARY KEY,
                        name VARCHAR(100) NOT NULL,
                        UNIQUE(name)
                    )"
                )
                .execute(&mut tx)
                .await?;
                
                sqlx::query(
                    "CREATE TABLE product_category_mappings (
                        product_id UUID NOT NULL REFERENCES products(id) ON DELETE CASCADE,
                        category_id UUID NOT NULL REFERENCES product_categories(id) ON DELETE CASCADE,
                        PRIMARY KEY(product_id, category_id)
                    )"
                )
                .execute(&mut tx)
                .await?;
                
                // 迁移现有数据
                sqlx::query(
                    "INSERT INTO product_categories (id, name)
                    SELECT gen_random_uuid(), DISTINCT category FROM products"
                )
                .execute(&mut tx)
                .await?;
                
                sqlx::query(
                    "INSERT INTO product_category_mappings (product_id, category_id)
                    SELECT p.id, c.id 
                    FROM products p
                    JOIN product_categories c ON p.category = c.name"
                )
                .execute(&mut tx)
                .await?;
            },
            4 => {
                // 添加高级库存和定价字段
                sqlx::query(
                    "ALTER TABLE products 
                    ADD COLUMN warehouse_location VARCHAR(100),
                    ADD COLUMN restock_date TIMESTAMP WITH TIME ZONE,
                    ADD COLUMN minimum_order_quantity INTEGER,
                    ADD COLUMN discount_rate DECIMAL(5, 2),
                    ADD COLUMN tax_rate DECIMAL(5, 2)"
                )
                .execute(&mut tx)
                .await?;
            },
            5 => {
                // 添加属性表支持自定义属性
                sqlx::query(
                    "CREATE TABLE product_attributes (
                        product_id UUID NOT NULL REFERENCES products(id) ON DELETE CASCADE,
                        key VARCHAR(100) NOT NULL,
                        value TEXT NOT NULL,
                        PRIMARY KEY(product_id, key)
                    )"
                )
                .execute(&mut tx)
                .await?;
            },
            _ => return Err(MigrationError::UnknownVersion(version)),
        }
        
        // 提交事务
        tx.commit().await?;
        
        Ok(())
    }
}

// API控制器 - 处理不同版本的请求
pub struct ProductApiController {
    version_adapter: Arc<ProductVersionAdapter>,
}

impl ProductApiController {
    // 使用内容协商处理版本化请求
    pub async fn get_product(
        &self,
        product_id: web::Path<String>,
        request: HttpRequest,
    ) -> Result<HttpResponse, ApiError> {
        // 解析产品ID
        let product_id = ProductId::from_string(&product_id)?;
        
        // 从Accept头获取版本
        let version = Self::extract_version_from_request(&request);
        
        // 获取产品
        let product_json = self.version_adapter
            .get_product_by_version(&product_id, version)
            .await?;
            
        // 返回适当的Content-Type
        let content_type = match version {
            ApiVersion::V1 => "application/vnd.myapi.product.v1+json",
            ApiVersion::V2 => "application/vnd.myapi.product.v2+json",
        };
        
        Ok(HttpResponse::Ok()
            .content_type(content_type)
            .json(product_json))
    }
    
    // 使用URL路径处理版本化请求
    pub async fn get_product_by_path_version(
        &self,
        path: web::Path<(String, String)>,
    ) -> Result<HttpResponse, ApiError> {
        let (version_str, product_id) = path.into_inner();
        
        // 解析版本和产品ID
        let version = match version_str.as_str() {
            "v1" => ApiVersion::V1,
            "v2" => ApiVersion::V2,
            _ => return Err(ApiError::UnsupportedVersion(version_str)),
        };
        
        let product_id = ProductId::from_string(&product_id)?;
        
        // 获取产品
        let product_json = self.version_adapter
            .get_product_by_version(&product_id, version)
            .await?;
            
        Ok(HttpResponse::Ok().json(product_json))
    }
    
    // 处理更新请求
    pub async fn update_product(
        &self,
        product_id: web::Path<String>,
        data: web::Json<serde_json::Value>,
        request: HttpRequest,
    ) -> Result<HttpResponse, ApiError> {
        // 解析产品ID
        let product_id = ProductId::from_string(&product_id)?;
        
        // 从Content-Type头获取版本
        let version = Self::extract_version_from_content_type(&request);
        
        // 更新产品
        let updated_json = self.version_adapter
            .update_product_by_version(&product_id, data.into_inner(), version)
            .await?;
            
        Ok(HttpResponse::Ok().json(updated_json))
    }
    
    fn extract_version_from_request(request: &HttpRequest) -> ApiVersion {
        let accept_header = request
            .headers()
            .get("Accept")
            .and_then(|h| h.to_str().ok())
            .unwrap_or("");
            
        if accept_header.contains("application/vnd.myapi.product.v2") {
            ApiVersion::V2
        } else {
            ApiVersion::V1 // 默认版本
        }
    }
    
    fn extract_version_from_content_type(request: &HttpRequest) -> ApiVersion {
        let content_type = request
            .headers()
            .get("Content-Type")
            .and_then(|h| h.to_str().ok())
            .unwrap_or("");
            
        if content_type.contains("application/vnd.myapi.product.v2") {
            ApiVersion::V2
        } else {
            ApiVersion::V1 // 默认版本
        }
    }
}
```

**映射分析**:

- 使用版本化模型定义不同版本的API接口
- 实现版本适配器处理不同版本间的转换
- 提供数据库迁移确保架构兼容性
- API控制器支持内容协商实现灵活的版本处理

### 4.3 分布式系统中的一致性

确保分布式环境中的一致性映射：

```rust
// 分布式系统中的实体标识和一致性管理
// 全局唯一标识符生成
pub struct DistributedIdGenerator {
    node_id: u16,
    sequence: AtomicU32,
    last_timestamp: AtomicI64,
}

impl DistributedIdGenerator {
    pub fn new(node_id: u16) -> Self {
        Self {
            node_id,
            sequence: AtomicU32::new(0),
            last_timestamp: AtomicI64::new(0),
        }
    }
    
    // 生成雪花ID（Snowflake ID）
    pub fn generate_id(&self) -> Result<u64, IdGenerationError> {
        const EPOCH: i64 = 1609459200000; // 2021-01-01 作为自定义纪元起点
        const NODE_ID_BITS: u32 = 10;
        const SEQUENCE_BITS: u32 = 12;
        
        const MAX_NODE_ID: u16 = (1 << NODE_ID_BITS) - 1;
        const MAX_SEQUENCE: u32 = (1 << SEQUENCE_BITS) - 1;
        
        const TIMESTAMP_SHIFT: u32 = NODE_ID_BITS + SEQUENCE_BITS;
        const NODE_ID_SHIFT: u32 = SEQUENCE_BITS;
        
        // 验证节点ID
        if self.node_id > MAX_NODE_ID {
            return Err(IdGenerationError::InvalidNodeId(self.node_id, MAX_NODE_ID));
        }
        
        // 获取当前时间
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|_| IdGenerationError::ClockError)?
            .as_millis() as i64 - EPOCH;
        
        // 处理时钟回退和序列溢出
        let mut last = self.last_timestamp.load(Ordering::Acquire);
        let mut sequence = 0;
        
        loop {
            if timestamp < last {
                // 时钟回退情况
                return Err(IdGenerationError::ClockMovedBackwards(last - timestamp));
            }
            
            if timestamp == last {
                // 同一毫秒，增加序列
                sequence = self.sequence.fetch_add(1, Ordering::AcqRel) + 1;
                
                if sequence > MAX_SEQUENCE {
                    // 序列溢出，等待下一毫秒
                    std::thread::sleep(Duration::from_micros(100));
                    break;
                }
            } else {
                // 新的毫秒，重置序列
                sequence = 0;
                if self.last_timestamp.compare_exchange(
                    last, timestamp, Ordering::AcqRel, Ordering::Relaxed
                ).is_ok() {
                    self.sequence.store(sequence, Ordering::Release);
                    break;
                }
                
                // 如果CAS失败，重试
                last = self.last_timestamp.load(Ordering::Acquire);
            }
        }
        
        // 组合ID各部分
        let id = ((timestamp as u64) << TIMESTAMP_SHIFT)
            | ((self.node_id as u64) << NODE_ID_SHIFT)
            | (sequence as u64);
            
        Ok(id)
    }
}

// 分布式事件处理与一致性
pub struct EventProcessor {
    event_store: Arc<dyn EventStore>,
    outbox_publisher: Arc<dyn OutboxPublisher>,
    snapshot_repository: Arc<dyn SnapshotRepository>,
    command_validator: Arc<dyn CommandValidator>,
}

impl EventProcessor {
    // 处理命令并产生事件
    pub async fn process_command(
        &self,
        aggregate_id: &str,
        command: Command,
    ) -> Result<CommandResult, CommandProcessingError> {
        // 获取乐观锁
        let lock = self.event_store.acquire_lock(aggregate_id).await?;
        
        // 验证命令
        self.command_validator.validate(&command).await?;
        
        // 加载聚合根当前状态
        let (aggregate, last_sequence) = self.load_aggregate(aggregate_id).await?;
        
        // 执行命令
        let events = command.execute(aggregate)?;
        
        // 保存事件到存储
        let saved_events = self.event_store.save_events(
            aggregate_id,
            last_sequence + 1,
            &events,
            lock,
        ).await?;
        
        // 发布事件到消息队列（使用出站消息表模式确保一致性）
        self.outbox_publisher.publish_events(&saved_events).await?;
        
        // 创建快照（如果需要）
        self.maybe_create_snapshot(aggregate_id).await?;
        
        Ok(CommandResult {
            aggregate_id: aggregate_id.to_string(),
            events_count: events.len(),
            sequence: last_sequence + events.len() as u64,
        })
    }
    
    // 加载聚合根状态
    async fn load_aggregate(&self, aggregate_id: &str) -> Result<(Aggregate, u64), CommandProcessingError> {
        // 首先尝试从快照加载
        let (mut aggregate, mut last_sequence) = match self.snapshot_repository.load(aggregate_id).await? {
            Some(snapshot) => (snapshot.aggregate, snapshot.sequence),
            None => (Aggregate::new(aggregate_id), 0),
        };
        
        // 加载快照之后的增量事件
        let events = self.event_store.load_events(aggregate_id, last_sequence + 1).await?;
        
        // 应用增量事件
        for event in &events {
            aggregate.apply(event);
            last_sequence = event.sequence;
        }
        
        Ok((aggregate, last_sequence))
    }
    
    // 可能创建快照
    async fn maybe_create_snapshot(&self, aggregate_id: &str) -> Result<(), CommandProcessingError> {
        const SNAPSHOT_THRESHOLD: u64 = 100; // 每100个事件创建一次快照
        
        // 检查事件数量
        let event_count = self.event_store.get_event_count(aggregate_id).await?;
        
        // 获取上次快照序列号
        let last_snapshot = self.snapshot_repository.load(aggregate_id).await?;
        let last_snapshot_sequence = last_snapshot.map(|s| s.sequence).unwrap_or(0);
        
        // 如果新事件数量超过阈值，创建新快照
        if event_count - last_snapshot_sequence >= SNAPSHOT_THRESHOLD {
            // 加载最新状态
            let (aggregate, sequence) = self.load_aggregate(aggregate_id).await?;
            
            // 创建快照
            let snapshot = Snapshot {
                aggregate_id: aggregate_id.to_string(),
                aggregate,
                sequence,
                created_at: Utc::now(),
            };
            
            // 保存快照
            self.snapshot_repository.save(&snapshot).await?;
        }
        
        Ok(())
    }
}

// 出站消息表发布者，确保事件发布与存储的一致性
pub struct OutboxPublisher {
    outbox_repository: Arc<dyn OutboxRepository>,
    message_broker: Arc<dyn MessageBroker>,
    clock: Arc<dyn Clock>,
    executor: Arc<TaskExecutor>,
}

impl OutboxPublisher {
    // 发布事件到出站消息表
    pub async fn publish_events(&self, events: &[DomainEvent]) -> Result<(), OutboxError> {
        // 将事件转换为出站消息
        let messages = events.iter()
            .map(|event| OutboxMessage {
                id: Uuid::new_v4().to_string(),
                aggregate_id: event.aggregate_id.clone(),
                event_type: event.event_type.clone(),
                payload: serde_json::to_string(event)?,
                created_at: self.clock.now(),
                status: OutboxStatus::Pending,
                retries: 0,
                last_attempt: None,
                next_attempt: Some(self.clock.now()),
            })
            .collect::<Vec<_>>();
            
        // 保存到出站消息表
        self.outbox_repository.save_messages(&messages).await?;
        
        // 触发处理器（异步处理，不影响命令响应时间）
        self.executor.spawn(self.process_outbox());
        
        Ok(())
    }
    
    // 定期处理出站消息表
    pub async fn process_outbox(&self) -> Result<(), OutboxError> {
        // 获取待处理消息
        let pending = self.outbox_repository.find_pending_messages(100).await?;
        
        if pending.is_empty() {
            return Ok(());
        }
        
        for message in pending {
            // 尝试发布到消息代理
            let result = self.message_broker.publish(
                &message.event_type,
                &message.payload,
                &HashMap::from([
                    ("aggregate_id".to_string(), message.aggregate_id.clone()),
                    ("event_id".to_string(), message.id.clone()),
                ]),
            ).await;
            
            match result {
                Ok(_) => {
                    // 标记为已处理
                    self.outbox_repository.mark_as_processed(&message.id).await?;
                },
                Err(e) => {
                    // 记录失败并调度重试
                    let mut updated_message = message.clone();
                    updated_message.retries += 1;
                    updated_message.last_attempt = Some(self.clock.now());
                    
                    // 计算下次重试时间（指数退避）
                    let delay = std::cmp::min(
                        30, // 最大30分钟
                        2_u64.pow(updated_message.retries.min(10) as u32), // 指数退避
                    );
                    updated_message.next_attempt = Some(
                        self.clock.now() + Duration::minutes(delay as i64)
                    );
                    
                    // 更新消息状态
                    if updated_message.retries >= 10 {
                        updated_message.status = OutboxStatus::Failed;
                    }
                    
                    self.outbox_repository.update_message(&updated_message).await?;
                    
                    // 记录错误
                    log::error!(
                        "Failed to publish outbox message {}: {}. Retry {}/10",
                        message.id, e, updated_message.retries
                    );
                }
            }
        }
        
        Ok(())
    }
}

// 分布式锁服务
pub struct DistributedLockService {
    redis_client: redis::Client,
    node_id: String,
}

impl DistributedLockService {
    // 获取分布式锁
    pub async fn acquire_lock(
        &self,
        resource_id: &str,
        ttl_seconds: u64,
    ) -> Result<Lock, LockError> {
        let lock_id = format!("{}:{}", self.node_id, Uuid::new_v4());
        let key = format!("lock:{}", resource_id);
        
        let mut conn = self.redis_client.get_async_connection().await?;
        
        // 使用SET NX获取锁
        let result: bool = redis::cmd("SET")
            .arg(&key)
            .arg(&lock_id)
            .arg("NX") // 仅当键不存在时设置
            .arg("EX") // 设置过期时间
            .arg(ttl_seconds)
            .query_async(&mut conn)
            .await?;
            
        if !result {
            return Err(LockError::ResourceLocked(resource_id.to_string()));
        }
        
        // 创建锁对象
        let lock = Lock {
            resource_id: resource_id.to_string(),
            lock_id,
            ttl_seconds,
            acquired_at: Utc::now(),
        };
        
        Ok(lock)
    }
    
    // 释放分布式锁（使用Lua脚本确保原子性）
    pub async fn release_lock(&self, lock: &Lock) -> Result<bool, LockError> {
        let mut conn = self.redis_client.get_async_connection().await?;
        let key = format!("lock:{}", lock.resource_id);
        
        // Lua脚本：仅当锁仍然被同一客户端持有时才删除
        let script = r#"
            if redis.call('GET', KEYS[1]) == ARGV[1] then
                return redis.call('DEL', KEYS[1])
            else
                return 0
            end
        "#;
        
        // 执行脚本
        let result: i32 = redis::Script::new(script)
            .key(&key)
            .arg(&lock.lock_id)
            .invoke_async(&mut conn)
            .await?;
            
        Ok(result == 1)
    }
    
    // 续期锁
    pub async fn extend_lock(&self, lock: &Lock, ttl_seconds: u64) -> Result<bool, LockError> {
        let mut conn = self.redis_client.get_async_connection().await?;
        let key = format!("lock:{}", lock.resource_id);
        
        // Lua脚本：仅当锁仍然被同一客户端持有时才延长TTL
        let script = r#"
            if redis.call('GET', KEYS[1]) == ARGV[1] then
                return redis.call('EXPIRE', KEYS[1], ARGV[2])
            else
                return 0
            end
        "#;
        
        // 执行脚本
        let result: i32 = redis::Script::new(script)
            .key(&key)
            .arg(&lock.lock_id)
            .arg(ttl_seconds)
            .invoke_async(&mut conn)
            .await?;
            
        Ok(result == 1)
    }
}
```

**映射分析**:

- 使用分布式ID生成器确保全局唯一标识
- 实现事件溯源和快照机制支持一致性恢复
- 采用出站消息表模式保证事件发布的可靠性
- 使用分布式锁服务防止并发冲突

### 4.4 性能优化与缓存策略

性能优化的映射实现：

```rust
// 缓存管理服务
pub struct CacheManager<T> {
    cache_client: Arc<dyn CacheClient>,
    serializer: Arc<dyn Serializer<T>>,
    key_prefix: String,
    ttl: Duration,
}

impl<T: Send + Sync + 'static> CacheManager<T> {
    // 从缓存获取数据，如果不存在则从源加载
    pub async fn get_or_load<F>(
        &self,
        key: &str,
        loader: F,
    ) -> Result<T, CacheError>
    where
        F: FnOnce() -> Pin<Box<dyn Future<Output = Result<T, anyhow::Error>> + Send>>,
    {
        let cache_key = self.build_key(key);
        
        // 尝试从缓存获取
        match self.cache_client.get(&cache_key).await? {
            Some(data) => {
                // 反序列化缓存的数据
                let value = self.serializer.deserialize(&data)?;
                Ok(value)
            },
            None => {
                // 从源加载数据
                let value = loader().await.map_err(|e| CacheError::SourceError(e.to_string()))?;
                
                // 序列化并存储到缓存
                let serialized = self.serializer.serialize(&value)?;
                self.cache_client.set(&cache_key, &serialized, Some(self.ttl)).await?;
                
                Ok(value)
            }
        }
    }
    
    // 将数据保存到缓存
    pub async fn set(&self, key: &str, value: &T) -> Result<(), CacheError> {
        let cache_key = self.build_key(key);
        let serialized = self.serializer.serialize(value)?;
        self.cache_client.set(&cache_key, &serialized, Some(self.ttl)).await?;
        Ok(())
    }
    
    // 从缓存删除数据
    pub async fn invalidate(&self, key: &str) -> Result<(), CacheError> {
        let cache_key = self.build_key(key);
        self.cache_client.delete(&cache_key).await?;
        Ok(())
    }
    
    // 批量获取缓存数据
    pub async fn multi_get<F>(
        &self,
        keys: &[String],
        loader: F,
    ) -> Result<HashMap<String, T>, CacheError>
    where
        F: FnOnce(Vec<String>) -> Pin<Box<dyn Future<Output = Result<HashMap<String, T>, anyhow::Error>> + Send>>,
    {
        // 构建缓存键
        let cache_keys: Vec<String> = keys.iter()
            .map(|k| self.build_key(k))
            .collect();
            
        // 批量从缓存获取
        let cached_data = self.cache_client.multi_get(&cache_keys).await?;
        
        // 处理命中和未命中的情况
        let mut result = HashMap::new();
        let mut missing_keys = Vec::new();
        
        for (i, key) in keys.iter().enumerate() {
            let cache_key = &cache_keys[i];
            
            if let Some(data) = cached_data.get(cache_key) {
                match self.serializer.deserialize(data) {
                    Ok(value) => {
                        result.insert(key.clone(), value);
                    },
                    Err(e) => {
                        //

```rust
                    Err(e) => {
                        // 序列化错误，视为缓存未命中
                        log::warn!("Failed to deserialize cached data for key {}: {}", key, e);
                        missing_keys.push(key.clone());
                    }
                }
            } else {
                missing_keys.push(key.clone());
            }
        }
        
        // 如果有未命中的键，从源加载
        if !missing_keys.is_empty() {
            let loaded_data = loader(missing_keys.clone()).await
                .map_err(|e| CacheError::SourceError(e.to_string()))?;
                
            // 更新缓存并合并结果
            for (key, value) in &loaded_data {
                let cache_key = self.build_key(key);
                let serialized = self.serializer.serialize(value)?;
                
                // 异步更新缓存，不阻塞响应
                let cache_client = self.cache_client.clone();
                let serialized_clone = serialized.clone();
                let cache_key_clone = cache_key.clone();
                let ttl = self.ttl;
                
                tokio::spawn(async move {
                    if let Err(e) = cache_client.set(&cache_key_clone, &serialized_clone, Some(ttl)).await {
                        log::error!("Failed to update cache for key {}: {}", cache_key_clone, e);
                    }
                });
                
                result.insert(key.clone(), loaded_data[key].clone());
            }
        }
        
        Ok(result)
    }
    
    // 批量更新缓存
    pub async fn multi_set(&self, values: &HashMap<String, T>) -> Result<(), CacheError> {
        let mut cache_entries = HashMap::with_capacity(values.len());
        
        for (key, value) in values {
            let cache_key = self.build_key(key);
            let serialized = self.serializer.serialize(value)?;
            cache_entries.insert(cache_key, serialized);
        }
        
        self.cache_client.multi_set(&cache_entries, Some(self.ttl)).await?;
        
        Ok(())
    }
    
    // 生成缓存键
    fn build_key(&self, key: &str) -> String {
        format!("{}:{}", self.key_prefix, key)
    }
}

// 多级缓存实现
pub struct MultilevelCache {
    local_cache: Arc<LocalCache>,
    distributed_cache: Arc<dyn CacheClient>,
    metrics_collector: Arc<dyn MetricsCollector>,
}

impl MultilevelCache {
    pub async fn get<T: DeserializeOwned + Serialize + Clone + Send + Sync>(
        &self,
        key: &str,
        namespace: &str,
    ) -> Result<Option<T>, CacheError> {
        let full_key = format!("{}:{}", namespace, key);
        
        // 计时器开始
        let timer = Instant::now();
        
        // 首先检查本地缓存
        if let Some(value) = self.local_cache.get::<T>(&full_key) {
            // 记录本地缓存命中
            self.metrics_collector.increment_counter("cache.local.hit", 1);
            self.metrics_collector.record_timing("cache.local.get_time", timer.elapsed());
            
            return Ok(Some(value));
        }
        
        // 本地缓存未命中，记录指标
        self.metrics_collector.increment_counter("cache.local.miss", 1);
        
        // 检查分布式缓存
        let dist_timer = Instant::now();
        let result = self.distributed_cache.get(&full_key).await?;
        
        if let Some(data) = &result {
            // 分布式缓存命中
            self.metrics_collector.increment_counter("cache.distributed.hit", 1);
            self.metrics_collector.record_timing("cache.distributed.get_time", dist_timer.elapsed());
            
            // 反序列化
            match serde_json::from_slice::<T>(data) {
                Ok(value) => {
                    // 更新本地缓存
                    self.local_cache.set(&full_key, &value);
                    
                    return Ok(Some(value));
                },
                Err(e) => {
                    // 反序列化错误
                    self.metrics_collector.increment_counter("cache.deserialization.error", 1);
                    log::error!("Failed to deserialize cache data: {}", e);
                    
                    // 删除可能损坏的缓存条目
                    self.distributed_cache.delete(&full_key).await?;
                    
                    return Err(CacheError::DeserializationError(e.to_string()));
                }
            }
        }
        
        // 分布式缓存也未命中
        self.metrics_collector.increment_counter("cache.distributed.miss", 1);
        self.metrics_collector.record_timing("cache.get_time", timer.elapsed());
        
        Ok(None)
    }
    
    pub async fn set<T: Serialize + Send + Sync>(
        &self,
        key: &str,
        namespace: &str,
        value: &T,
        ttl: Option<Duration>,
    ) -> Result<(), CacheError> {
        let full_key = format!("{}:{}", namespace, key);
        
        // 序列化值
        let serialized = serde_json::to_vec(value)
            .map_err(|e| CacheError::SerializationError(e.to_string()))?;
            
        // 更新本地缓存
        self.local_cache.set(&full_key, value);
        
        // 更新分布式缓存
        self.distributed_cache.set(&full_key, &serialized, ttl).await?;
        
        // 记录缓存写入
        self.metrics_collector.increment_counter("cache.set", 1);
        
        Ok(())
    }
    
    pub async fn invalidate(&self, key: &str, namespace: &str) -> Result<(), CacheError> {
        let full_key = format!("{}:{}", namespace, key);
        
        // 从本地缓存删除
        self.local_cache.delete(&full_key);
        
        // 从分布式缓存删除
        self.distributed_cache.delete(&full_key).await?;
        
        // 记录缓存失效
        self.metrics_collector.increment_counter("cache.invalidate", 1);
        
        Ok(())
    }
    
    // 缓存预热
    pub async fn warm_up<F, T>(
        &self,
        keys: &[String],
        namespace: &str,
        loader: F,
    ) -> Result<(), CacheError>
    where
        F: Fn(Vec<String>) -> Pin<Box<dyn Future<Output = Result<HashMap<String, T>, anyhow::Error>> + Send>>,
        T: Serialize + DeserializeOwned + Clone + Send + Sync + 'static,
    {
        // 检查哪些键需要加载
        let mut keys_to_load = Vec::new();
        
        for key in keys {
            let full_key = format!("{}:{}", namespace, key);
            
            // 检查本地缓存
            if self.local_cache.contains_key(&full_key) {
                continue;
            }
            
            // 检查分布式缓存
            if self.distributed_cache.get(&full_key).await?.is_some() {
                continue;
            }
            
            keys_to_load.push(key.clone());
        }
        
        if keys_to_load.is_empty() {
            return Ok(());
        }
        
        // 记录需要预热的键数量
        self.metrics_collector.increment_counter("cache.warmup.keys", keys_to_load.len() as u64);
        
        // 批量加载数据
        let loaded_data = loader(keys_to_load).await
            .map_err(|e| CacheError::SourceError(e.to_string()))?;
            
        // 更新缓存
        for (key, value) in &loaded_data {
            let full_key = format!("{}:{}", namespace, key);
            
            // 更新本地缓存
            self.local_cache.set(&full_key, value);
            
            // 更新分布式缓存
            let serialized = serde_json::to_vec(value)
                .map_err(|e| CacheError::SerializationError(e.to_string()))?;
                
            self.distributed_cache.set(&full_key, &serialized, None).await?;
        }
        
        // 记录预热完成
        self.metrics_collector.increment_counter("cache.warmup.completed", 1);
        
        Ok(())
    }
}

// 本地内存缓存实现
pub struct LocalCache {
    cache: DashMap<String, CacheEntry>,
    max_size: usize,
    default_ttl: Duration,
    metrics_collector: Arc<dyn MetricsCollector>,
    eviction_policy: EvictionPolicy,
}

struct CacheEntry {
    value: Vec<u8>,
    created_at: Instant,
    expires_at: Option<Instant>,
    access_count: AtomicU64,
    last_accessed: AtomicCell<Instant>,
}

enum EvictionPolicy {
    LRU,
    LFU,
    FIFO,
}

impl LocalCache {
    pub fn new(
        max_size: usize,
        default_ttl: Duration,
        eviction_policy: EvictionPolicy,
        metrics_collector: Arc<dyn MetricsCollector>,
    ) -> Self {
        let cache = Self {
            cache: DashMap::with_capacity(max_size),
            max_size,
            default_ttl,
            metrics_collector,
            eviction_policy,
        };
        
        // 启动定期清理过期项目的任务
        let cache_clone = Arc::new(cache);
        
        std::thread::spawn(move || {
            let cache = cache_clone;
            loop {
                std::thread::sleep(Duration::from_secs(60));
                cache.cleanup_expired();
            }
        });
        
        cache
    }
    
    pub fn get<T: DeserializeOwned>(&self, key: &str) -> Option<T> {
        let result = self.cache.get(key);
        
        if let Some(entry) = result {
            // 检查是否过期
            if let Some(expires_at) = entry.expires_at {
                if expires_at <= Instant::now() {
                    // 已过期，删除并返回None
                    self.cache.remove(key);
                    self.metrics_collector.increment_counter("cache.local.expired", 1);
                    return None;
                }
            }
            
            // 更新访问统计
            entry.access_count.fetch_add(1, Ordering::Relaxed);
            entry.last_accessed.store(Instant::now());
            
            // 反序列化
            match serde_json::from_slice(&entry.value) {
                Ok(value) => Some(value),
                Err(e) => {
                    log::error!("Failed to deserialize cached value: {}", e);
                    self.cache.remove(key);
                    None
                }
            }
        } else {
            None
        }
    }
    
    pub fn set<T: Serialize>(&self, key: &str, value: &T) -> bool {
        let serialized = match serde_json::to_vec(value) {
            Ok(data) => data,
            Err(e) => {
                log::error!("Failed to serialize value for caching: {}", e);
                return false;
            }
        };
        
        // 检查缓存大小，如果已满则执行淘汰
        if self.cache.len() >= self.max_size && !self.cache.contains_key(key) {
            self.evict_entry();
        }
        
        let now = Instant::now();
        let expires_at = now + self.default_ttl;
        
        // 创建缓存条目
        let entry = CacheEntry {
            value: serialized,
            created_at: now,
            expires_at: Some(expires_at),
            access_count: AtomicU64::new(0),
            last_accessed: AtomicCell::new(now),
        };
        
        // 插入或更新缓存
        self.cache.insert(key.to_string(), entry);
        true
    }
    
    pub fn delete(&self, key: &str) -> bool {
        self.cache.remove(key).is_some()
    }
    
    pub fn contains_key(&self, key: &str) -> bool {
        if let Some(entry) = self.cache.get(key) {
            // 检查是否过期
            if let Some(expires_at) = entry.expires_at {
                if expires_at <= Instant::now() {
                    // 已过期，删除并返回false
                    self.cache.remove(key);
                    return false;
                }
            }
            true
        } else {
            false
        }
    }
    
    // 清理过期条目
    fn cleanup_expired(&self) {
        let now = Instant::now();
        let mut expired_count = 0;
        
        self.cache.retain(|_, entry| {
            if let Some(expires_at) = entry.expires_at {
                if expires_at <= now {
                    expired_count += 1;
                    false // 删除
                } else {
                    true // 保留
                }
            } else {
                true // 永不过期，保留
            }
        });
        
        if expired_count > 0 {
            self.metrics_collector.increment_counter("cache.local.cleanup", expired_count);
        }
    }
    
    // 根据策略淘汰条目
    fn evict_entry(&self) {
        match self.eviction_policy {
            EvictionPolicy::LRU => self.evict_lru(),
            EvictionPolicy::LFU => self.evict_lfu(),
            EvictionPolicy::FIFO => self.evict_fifo(),
        }
    }
    
    // 最近最少使用淘汰
    fn evict_lru(&self) {
        let mut oldest_key = None;
        let mut oldest_time = Instant::now();
        
        for item in self.cache.iter() {
            let last_accessed = item.last_accessed.load();
            if last_accessed < oldest_time {
                oldest_time = last_accessed;
                oldest_key = Some(item.key().clone());
            }
        }
        
        if let Some(key) = oldest_key {
            self.cache.remove(&key);
            self.metrics_collector.increment_counter("cache.local.eviction.lru", 1);
        }
    }
    
    // 最不常使用淘汰
    fn evict_lfu(&self) {
        let mut least_used_key = None;
        let mut least_count = u64::MAX;
        
        for item in self.cache.iter() {
            let count = item.access_count.load(Ordering::Relaxed);
            if count < least_count {
                least_count = count;
                least_used_key = Some(item.key().clone());
            }
        }
        
        if let Some(key) = least_used_key {
            self.cache.remove(&key);
            self.metrics_collector.increment_counter("cache.local.eviction.lfu", 1);
        }
    }
    
    // 先进先出淘汰
    fn evict_fifo(&self) {
        let mut oldest_key = None;
        let mut oldest_time = Instant::now();
        
        for item in self.cache.iter() {
            if item.created_at < oldest_time {
                oldest_time = item.created_at;
                oldest_key = Some(item.key().clone());
            }
        }
        
        if let Some(key) = oldest_key {
            self.cache.remove(&key);
            self.metrics_collector.increment_counter("cache.local.eviction.fifo", 1);
        }
    }
}

// 缓存一致性管理
pub struct CacheConsistencyManager {
    cache: Arc<MultilevelCache>,
    event_subscriber: Arc<dyn EventSubscriber>,
}

impl CacheConsistencyManager {
    pub fn new(
        cache: Arc<MultilevelCache>,
        event_subscriber: Arc<dyn EventSubscriber>,
    ) -> Self {
        Self {
            cache,
            event_subscriber,
        }
    }
    
    // 启动缓存一致性监听器
    pub async fn start(&self) -> Result<(), CacheError> {
        // 订阅实体变更事件
        self.event_subscriber.subscribe(&["entity.created", "entity.updated", "entity.deleted"])
            .await?;
            
        // 处理事件循环
        let cache = self.cache.clone();
        
        tokio::spawn(async move {
            while let Some(event) = cache.event_subscriber.receive().await {
                if let Err(e) = Self::handle_entity_event(&cache, &event).await {
                    log::error!("Failed to handle cache invalidation for event: {}", e);
                }
            }
        });
        
        Ok(())
    }
    
    // 处理实体事件，更新或失效缓存
    async fn handle_entity_event(
        cache: &MultilevelCache,
        event: &Event,
    ) -> Result<(), CacheError> {
        // 解析事件类型和实体ID
        let entity_type = event.metadata.get("entity_type")
            .ok_or_else(|| CacheError::InvalidEvent("Missing entity_type in event metadata".into()))?;
            
        let entity_id = event.metadata.get("entity_id")
            .ok_or_else(|| CacheError::InvalidEvent("Missing entity_id in event metadata".into()))?;
            
        // 根据事件类型处理
        match event.event_type.as_str() {
            "entity.deleted" => {
                // 实体删除，直接失效缓存
                cache.invalidate(entity_id, entity_type).await?;
                log::debug!("Invalidated cache for deleted {}: {}", entity_type, entity_id);
            },
            "entity.updated" => {
                // 实体更新，可以选择失效或更新缓存
                if let Some(entity_data) = &event.payload {
                    // 如果事件包含完整实体数据，更新缓存
                    match entity_type.as_str() {
                        "product" => {
                            if let Ok(product) = serde_json::from_value::<Product>(entity_data.clone()) {
                                cache.set(entity_id, "product", &product, None).await?;
                                log::debug!("Updated cache for product: {}", entity_id);
                            } else {
                                // 解析失败，直接失效
                                cache.invalidate(entity_id, "product").await?;
                            }
                        },
                        "order" => {
                            if let Ok(order) = serde_json::from_value::<Order>(entity_data.clone()) {
                                cache.set(entity_id, "order", &order, None).await?;
                                log::debug!("Updated cache for order: {}", entity_id);
                            } else {
                                cache.invalidate(entity_id, "order").await?;
                            }
                        },
                        "customer" => {
                            if let Ok(customer) = serde_json::from_value::<Customer>(entity_data.clone()) {
                                cache.set(entity_id, "customer", &customer, None).await?;
                                log::debug!("Updated cache for customer: {}", entity_id);
                            } else {
                                cache.invalidate(entity_id, "customer").await?;
                            }
                        },
                        // 其他实体类型...
                        _ => {
                            // 未知类型，直接失效
                            cache.invalidate(entity_id, entity_type).await?;
                        }
                    }
                } else {
                    // 没有实体数据，直接失效缓存
                    cache.invalidate(entity_id, entity_type).await?;
                }
            },
            "entity.created" => {
                // 实体创建，通常不需要直接操作缓存，因为还没有被缓存
                // 但如果有关联缓存（如列表），可能需要失效
                if let Some(related_keys) = event.metadata.get("related_cache_keys") {
                    if let Ok(keys) = serde_json::from_str::<Vec<String>>(related_keys) {
                        for key in keys {
                            let parts: Vec<&str> = key.split(':').collect();
                            if parts.len() == 2 {
                                cache.invalidate(parts[1], parts[0]).await?;
                                log::debug!("Invalidated related cache: {}", key);
                            }
                        }
                    }
                }
            },
            _ => {
                log::warn!("Unhandled event type for cache consistency: {}", event.event_type);
            }
        }
        
        Ok(())
    }
}

// 查询结果缓存
pub struct QueryCache {
    cache: Arc<MultilevelCache>,
    repository: Arc<dyn Repository>,
    query_parser: Arc<dyn QueryParser>,
}

impl QueryCache {
    // 执行带缓存的查询
    pub async fn execute_query<T: DeserializeOwned + Serialize + Clone + Send + Sync + 'static>(
        &self,
        query: &Query,
    ) -> Result<QueryResult<T>, QueryError> {
        // 解析查询并生成缓存键
        let cache_key = self.query_parser.generate_cache_key(query)?;
        let entity_type = self.query_parser.get_entity_type(query)?;
        
        // 检查是否可缓存
        if !self.query_parser.is_cacheable(query) {
            // 直接执行查询
            return self.repository.execute_query(query).await;
        }
        
        // 尝试从缓存获取
        if let Some(cached_result) = self.cache.get::<QueryResult<T>>(&cache_key, entity_type).await? {
            return Ok(cached_result);
        }
        
        // 缓存未命中，执行查询
        let result = self.repository.execute_query(query).await?;
        
        // 确定缓存TTL
        let ttl = match self.query_parser.get_query_type(query)? {
            QueryType::Lookup => Duration::from_secs(3600), // 单个实体查询缓存1小时
            QueryType::List { .. } => Duration::from_secs(300), // 列表查询缓存5分钟
            QueryType::Search { .. } => Duration::from_secs(60), // 搜索查询缓存1分钟
            QueryType::Aggregate { .. } => Duration::from_secs(600), // 聚合查询缓存10分钟
        };
        
        // 缓存结果
        self.cache.set(&cache_key, entity_type, &result, Some(ttl)).await?;
        
        Ok(result)
    }
}
```

**映射分析**:

- 实现多级缓存系统提高性能和扩展性
- 支持不同缓存淘汰策略（LRU、LFU、FIFO）
- 添加缓存一致性管理确保数据同步
- 实现查询结果缓存优化频繁查询

## 5. 总结与最佳实践

### 5.1 映射策略选择指南

针对不同场景的映射策略建议：

```rust
// 映射策略选择示例
// 1. 简单值对象映射
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CustomerId(String);

impl CustomerId {
    pub fn new() -> Self {
        Self(Uuid::new_v4().to_string())
    }
    
    pub fn from_string(id: &str) -> Result<Self, ValidationError> {
        // 验证ID格式
        if id.is_empty() {
            return Err(ValidationError::new("Customer ID cannot be empty"));
        }
        
        Ok(Self(id.to_string()))
    }
    
    pub fn value(&self) -> &str {
        &self.0
    }
}

impl Display for CustomerId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Serialize for CustomerId {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(&self.0)
    }
}

impl<'de> Deserialize<'de> for CustomerId {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        Ok(Self(s))
    }
}

// 2. 复杂值对象映射
#[derive(Debug, Clone, PartialEq)]
pub struct Money {
    amount: Decimal,
    currency: Currency,
}

impl Money {
    pub fn new(amount: f64, currency: Currency) -> Result<Self, ValidationError> {
        if amount.is_nan() || amount.is_infinite() {
            return Err(ValidationError::new("Money amount must be a valid number"));
        }
        
        Ok(Self {
            amount: Decimal::from_f64(amount).ok_or_else(|| {
                ValidationError::new("Failed to convert amount to Decimal")
            })?,
            currency,
        })
    }
    
    pub fn new_usd(amount: f64) -> Result<Self, ValidationError> {
        Self::new(amount, Currency::USD)
    }
    
    pub fn zero(currency: Currency) -> Self {
        Self {
            amount: Decimal::ZERO,
            currency,
        }
    }
    
    pub fn value(&self) -> f64 {
        self.amount.to_f64().unwrap_or(0.0)
    }
    
    pub fn currency(&self) -> &Currency {
        &self.currency
    }
    
    pub fn add(&self, other: &Money) -> Result<Money, MoneyError> {
        if self.currency != other.currency {
            return Err(MoneyError::CurrencyMismatch(
                format!("Cannot add {} to {}", self.currency, other.currency)
            ));
        }
        
        Ok(Money {
            amount: self.amount + other.amount,
            currency: self.currency.clone(),
        })
    }
    
    pub fn subtract(&self, other: &Money) -> Result<Money, MoneyError> {
        if self.currency != other.currency {
            return Err(MoneyError::CurrencyMismatch(
                format!("Cannot subtract {} from {}", other.currency, self.currency)
            ));
        }
        
        Ok(Money {
            amount: self.amount - other.amount,
            currency: self.currency.clone(),
        })
    }
    
    pub fn multiply(&self, factor: f64) -> Result<Money, MoneyError> {
        if factor.is_nan() || factor.is_infinite() {
            return Err(MoneyError::InvalidOperation("Invalid multiplication factor".into()));
        }
        
        let factor_decimal = Decimal::from_f64(factor).ok_or_else(|| {
            MoneyError::InvalidOperation("Failed to convert factor to Decimal".into())
        })?;
        
        Ok(Money {
            amount: self.amount * factor_decimal,
            currency: self.currency.clone(),
        })
    }
}

impl std::ops::Add for Money {
    type Output = Money;
    
    fn add(self, rhs: Self) -> Self::Output {
        self.add(&rhs).unwrap_or_else(|_| self)
    }
}

impl std::ops::Mul<f64> for Money {
    type Output = Money;
    
    fn mul(self, rhs: f64) -> Self::Output {
        self.multiply(rhs).unwrap_or_else(|_| self)
    }
}

impl Serialize for Money {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut state = serializer.serialize_struct("Money", 2)?;
        state.serialize_field("amount", &self.amount.to_string())?;
        state.serialize_field("currency", &self.currency.code())?;
        state.end()
    }
}

impl<'de> Deserialize<'de> for Money {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        #[derive(Deserialize)]
        struct MoneyHelper {
            amount: String,
            currency: String,
        }
        
        let helper = MoneyHelper::deserialize(deserializer)?;
        
        let amount = helper.amount.parse::<Decimal>()
            .map_err(|e| serde::de::Error::custom(format!("Invalid amount: {}", e)))?;
            
        let currency = Currency::from_code(&helper.currency)
            .map_err(|e| serde::de::Error::custom(format!("Invalid currency: {}", e)))?;
            
        Ok(Money {
            amount,
            currency,
        })
    }
}

// 3. 实体映射
// 领域实体
#[derive(Debug, Clone)]
pub struct Order {
    id: OrderId,
    customer_id: CustomerId,
    items: Vec<OrderItem>,
    status: OrderStatus,
    shipping_address: Option<Address>,
    payment_status: PaymentStatus,
    created_at: DateTime<Utc>,
    updated_at: DateTime<Utc>,
}

// DTO映射
#[derive(Debug, Serialize, Deserialize)]
pub struct OrderDto {
    pub id: String,
    pub customer_id: String,
    pub items: Vec<OrderItemDto>,
    pub status: String,
    pub shipping_address: Option<AddressDto>,
    pub payment_status: String,
    pub total_amount: f64,
    pub currency: String,
    pub created_at: String,
    pub updated_at: String,
}

impl OrderDto {
    // 从领域实体到DTO的映射
    pub fn from_domain(order: &Order) -> Self {
        let total = order.calculate_total();
        
        Self {
            id: order.id.to_string(),
            customer_id: order.customer_id.to_string(),
            items: order.items.iter().map(OrderItemDto::from_domain).collect(),
            status: order.status.to_string(),
            shipping_address: order.shipping_address.as_ref().map(AddressDto::from_domain),
            payment_status: order.payment_status.to_string(),
            total_amount: total.value(),
            currency: total.currency().code().to_string(),
            created_at: order.created_at.to_rfc3339(),
            updated_at: order.updated_at.to_rfc3339(),
        }
    }
    
    // 从DTO到领域实体的映射
    pub fn to_domain(&self) -> Result<Order, DtoMappingError> {
        let order_id = OrderId::from_string(&self.id)?;
        let customer_id = CustomerId::from_string(&self.customer_id)?;
        
        let items = self.items.iter()
            .map(|item| item.to_domain())
            .collect::<Result<Vec<_>, _>>()?;
            
        let status = OrderStatus::from_string(&self.status)?;
        let payment_status = PaymentStatus::from_string(&self.payment_status)?;
        
        let shipping_address = if let Some(addr) = &self.shipping_address {
            Some(addr.to_domain()?)
        } else {
            None
        };
        
        let created_at = DateTime::parse_from_rfc3339(&self.created_at)
            .map_err(|e| DtoMappingError::DateParseError(e.to_string()))?
            .with_timezone(&Utc);
            
        let updated_at = DateTime::parse_from_rfc3339(&self.updated_at)
            .map_err(|e| DtoMappingError::DateParseError(e.to_string()))?
            .with_timezone(&Utc);
            
        Ok(Order {
            id: order_id,
            customer_id,
            items,
            status,
            shipping_address,
            payment_status,
            created_at,
            updated_at,
        })
    }
}

// 4. 聚合根映射
// 领域聚合根
#[derive(Debug, Clone)]
pub struct Cart {
    id: CartId,
    customer_id: Option<CustomerId>,
    items: Vec<CartItem>,
    created_at: DateTime<Utc>,
    updated_at: DateTime<Utc>,
    coupon_code: Option<String>,
    shipping_method: Option<ShippingMethod>,
}

impl Cart {
    // 领域逻辑方法...
    pub fn add_item(&mut self, product_id: ProductId, quantity: u32, unit_price: Money) -> Result<(), CartError> {
        // 验证商品数量
        if quantity == 0 {
            return Err(CartError::InvalidQuantity);
        }
        
        // 检查是否已有该商品
        if let Some(existing_item) = self.items.iter_mut()
            .find(|item| item.product_id == product_id)
        {
            // 更新现有商品数量
            existing_item.quantity += quantity;
            existing_item.total_price = existing_item.unit_price.clone() * existing_item.quantity as f64;
        } else {
            // 添加新商品
            let total_price = unit_price.clone() * quantity as f64;
            
            self.items.push(CartItem {
                id: CartItemId::new(),
                product_id,
                quantity,
                unit_price,
                total_price,
                added_at: Utc::now(),
            });
        }
        
        self.updated_at = Utc::now();
        
        Ok(())
    }
    
    pub fn remove_item(&mut self, product_id: &ProductId) -> Result<(), CartError> {
        let initial_len = self.items.len();
        
        self.items.retain(|item| item.product_id != *product_id);
        
        if self.items.len() == initial_len {
            return Err(CartError::ItemNotFound);
        }
        
        self.updated_at = Utc::now();
        
        Ok(())
    }
    
    pub fn update_quantity(&mut self, product_id: &ProductId, quantity: u32) -> Result<(), CartError> {
        if quantity == 0 {
            return self.remove_item(product_id);
        }
        
        let item = self.items.iter_mut()
            .find(|item| item.product_id == *product_id)
            .ok_or(CartError::ItemNotFound)?;
            
        item.quantity = quantity;
        item.total_price = item.unit_price.clone() * quantity as f64;
        
        self.updated_at = Utc::now();
        
        Ok(())
    }
    
    pub fn apply_coupon(&mut self, coupon_code: String) -> Result<(), CartError> {
        // 此处应验证优惠券，但为简化示例，仅存储代码
        self.coupon_code = Some(coupon_code);
        self.updated_at = Utc::now();
        
        Ok(())
    }
    
    pub fn select_shipping_method(&mut self, method: ShippingMethod) -> Result<(), CartError> {
        self.shipping_method = Some(method);
        self.updated_at = Utc::now();
        
        Ok(())
    }
    
    pub fn calculate_subtotal(&self) -> Money {
        self.items.iter()
            .fold(Money::zero(Currency::USD), |acc, item| {
                acc + item.total_price.clone()
            })
    }
    
    pub fn calculate_total(&self) -> Money {
        let subtotal = self.calculate_subtotal();
        
        // 添加运费
        let with_shipping = if let Some(shipping) = &self.shipping_method {
            subtotal.clone() + shipping.cost.clone()
        } else {
            subtotal.clone()
        };
        

```rust
        // 应用优惠券折扣
        let with_discount = if let Some(_coupon) = &self.coupon_code {
            // 简化示例：固定10%折扣
            with_shipping.multiply(0.9).unwrap_or(with_shipping.clone())
        } else {
            with_shipping
        };
        
        with_discount
    }
    
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }
    
    pub fn item_count(&self) -> usize {
        self.items.len()
    }
    
    pub fn total_quantity(&self) -> u32 {
        self.items.iter().map(|item| item.quantity).sum()
    }
}

// 存储模型 - 数据访问对象
#[derive(Debug, Serialize, Deserialize)]
pub struct CartEntity {
    pub id: String,
    pub customer_id: Option<String>,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
    pub coupon_code: Option<String>,
    pub shipping_method: Option<ShippingMethodEntity>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct CartItemEntity {
    pub id: String,
    pub cart_id: String,
    pub product_id: String,
    pub quantity: u32,
    pub unit_price: f64,
    pub unit_currency: String,
    pub total_price: f64,
    pub added_at: DateTime<Utc>,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct ShippingMethodEntity {
    pub code: String,
    pub name: String,
    pub cost: f64,
    pub currency: String,
    pub estimated_days: u32,
}

// 仓储实现，处理聚合与存储之间的映射
pub struct CartRepository {
    db_client: Arc<PgPool>,
}

impl CartRepository {
    // 从存储加载购物车聚合
    pub async fn find_by_id(&self, id: &CartId) -> Result<Option<Cart>, RepositoryError> {
        // 获取购物车主记录
        let cart_entity = sqlx::query_as::<_, CartEntity>(
            "SELECT id, customer_id, created_at, updated_at, coupon_code, 
                    shipping_method_code, shipping_method_name, 
                    shipping_cost, shipping_currency, shipping_estimated_days
             FROM carts WHERE id = $1"
        )
        .bind(id.to_string())
        .fetch_optional(&*self.db_client)
        .await?;
        
        let cart_entity = match cart_entity {
            Some(entity) => entity,
            None => return Ok(None),
        };
        
        // 获取购物车项目
        let item_entities = sqlx::query_as::<_, CartItemEntity>(
            "SELECT id, cart_id, product_id, quantity, unit_price, unit_currency, 
                    total_price, added_at
             FROM cart_items WHERE cart_id = $1"
        )
        .bind(id.to_string())
        .fetch_all(&*self.db_client)
        .await?;
        
        // 将存储实体映射为领域聚合
        let customer_id = if let Some(cid) = cart_entity.customer_id {
            Some(CustomerId::from_string(&cid)?)
        } else {
            None
        };
        
        // 映射购物车项目
        let mut items = Vec::with_capacity(item_entities.len());
        
        for entity in item_entities {
            let product_id = ProductId::from_string(&entity.product_id)?;
            let currency = Currency::from_code(&entity.unit_currency)?;
            
            let unit_price = Money::new(entity.unit_price, currency.clone())?;
            let total_price = Money::new(entity.total_price, currency)?;
            
            items.push(CartItem {
                id: CartItemId::from_string(&entity.id)?,
                product_id,
                quantity: entity.quantity,
                unit_price,
                total_price,
                added_at: entity.added_at,
            });
        }
        
        // 映射配送方式
        let shipping_method = if let Some(method) = cart_entity.shipping_method {
            let currency = Currency::from_code(&method.currency)?;
            let cost = Money::new(method.cost, currency)?;
            
            Some(ShippingMethod {
                code: method.code,
                name: method.name,
                cost,
                estimated_days: method.estimated_days,
            })
        } else {
            None
        };
        
        // 构建完整聚合
        let cart = Cart {
            id: CartId::from_string(&cart_entity.id)?,
            customer_id,
            items,
            created_at: cart_entity.created_at,
            updated_at: cart_entity.updated_at,
            coupon_code: cart_entity.coupon_code,
            shipping_method,
        };
        
        Ok(Some(cart))
    }
    
    // 保存购物车聚合到存储
    pub async fn save(&self, cart: &Cart) -> Result<(), RepositoryError> {
        // 开始事务
        let mut tx = self.db_client.begin().await?;
        
        // 准备购物车主记录
        let shipping_method_code = cart.shipping_method.as_ref().map(|m| m.code.clone());
        let shipping_method_name = cart.shipping_method.as_ref().map(|m| m.name.clone());
        let shipping_cost = cart.shipping_method.as_ref().map(|m| m.cost.value());
        let shipping_currency = cart.shipping_method.as_ref().map(|m| m.cost.currency().code().to_string());
        let shipping_days = cart.shipping_method.as_ref().map(|m| m.estimated_days);
        
        // 更新购物车主记录
        sqlx::query(
            "INSERT INTO carts (id, customer_id, created_at, updated_at, coupon_code,
                  shipping_method_code, shipping_method_name, shipping_cost, 
                  shipping_currency, shipping_estimated_days)
             VALUES ($1, $2, $3, $4, $5, $6, $7, $8, $9, $10)
             ON CONFLICT (id) DO UPDATE SET
                customer_id = EXCLUDED.customer_id,
                updated_at = EXCLUDED.updated_at,
                coupon_code = EXCLUDED.coupon_code,
                shipping_method_code = EXCLUDED.shipping_method_code,
                shipping_method_name = EXCLUDED.shipping_method_name,
                shipping_cost = EXCLUDED.shipping_cost,
                shipping_currency = EXCLUDED.shipping_currency,
                shipping_estimated_days = EXCLUDED.shipping_estimated_days"
        )
        .bind(cart.id.to_string())
        .bind(cart.customer_id.as_ref().map(|id| id.to_string()))
        .bind(cart.created_at)
        .bind(cart.updated_at)
        .bind(&cart.coupon_code)
        .bind(shipping_method_code)
        .bind(shipping_method_name)
        .bind(shipping_cost)
        .bind(shipping_currency)
        .bind(shipping_days)
        .execute(&mut tx)
        .await?;
        
        // 删除现有的购物车项目（简化实现，实际可以优化为更新）
        sqlx::query("DELETE FROM cart_items WHERE cart_id = $1")
            .bind(cart.id.to_string())
            .execute(&mut tx)
            .await?;
            
        // 插入所有购物车项目
        for item in &cart.items {
            sqlx::query(
                "INSERT INTO cart_items (id, cart_id, product_id, quantity, 
                      unit_price, unit_currency, total_price, added_at)
                 VALUES ($1, $2, $3, $4, $5, $6, $7, $8)"
            )
            .bind(item.id.to_string())
            .bind(cart.id.to_string())
            .bind(item.product_id.to_string())
            .bind(item.quantity)
            .bind(item.unit_price.value())
            .bind(item.unit_price.currency().code())
            .bind(item.total_price.value())
            .bind(item.added_at)
            .execute(&mut tx)
            .await?;
        }
        
        // 提交事务
        tx.commit().await?;
        
        Ok(())
    }
}

// 5. 领域事件映射
// 领域事件定义
#[derive(Debug, Clone)]
pub struct OrderPlacedEvent {
    pub id: EventId,
    pub order_id: OrderId,
    pub customer_id: CustomerId,
    pub total_amount: Money,
    pub occurred_at: DateTime<Utc>,
}

// 事件存储模型
#[derive(Debug, Serialize, Deserialize)]
pub struct EventEntity {
    pub id: String,
    pub aggregate_id: String,
    pub aggregate_type: String,
    pub event_type: String,
    pub payload: serde_json::Value,
    pub metadata: serde_json::Value,
    pub occurred_at: DateTime<Utc>,
    pub version: i64,
}

// 事件映射逻辑
pub trait DomainEvent: Send + Sync {
    fn event_id(&self) -> &EventId;
    fn event_type(&self) -> &'static str;
    fn aggregate_id(&self) -> String;
    fn aggregate_type(&self) -> &'static str;
    fn occurred_at(&self) -> DateTime<Utc>;
    fn to_payload(&self) -> Result<serde_json::Value, EventError>;
    fn metadata(&self) -> HashMap<String, String>;
}

impl DomainEvent for OrderPlacedEvent {
    fn event_id(&self) -> &EventId {
        &self.id
    }
    
    fn event_type(&self) -> &'static str {
        "order.placed"
    }
    
    fn aggregate_id(&self) -> String {
        self.order_id.to_string()
    }
    
    fn aggregate_type(&self) -> &'static str {
        "order"
    }
    
    fn occurred_at(&self) -> DateTime<Utc> {
        self.occurred_at
    }
    
    fn to_payload(&self) -> Result<serde_json::Value, EventError> {
        let payload = json!({
            "order_id": self.order_id.to_string(),
            "customer_id": self.customer_id.to_string(),
            "total_amount": self.total_amount.value(),
            "currency": self.total_amount.currency().code(),
        });
        
        Ok(payload)
    }
    
    fn metadata(&self) -> HashMap<String, String> {
        let mut metadata = HashMap::new();
        metadata.insert("source".to_string(), "order_service".to_string());
        metadata
    }
}

// 事件存储 - 领域事件与存储之间的映射
pub struct EventStore {
    db_client: Arc<PgPool>,
}

impl EventStore {
    // 保存领域事件
    pub async fn save_event<T: DomainEvent>(&self, event: &T) -> Result<(), EventStoreError> {
        // 转换为存储模型
        let payload = event.to_payload()?;
        let metadata = serde_json::to_value(event.metadata())?;
        
        // 获取当前版本号
        let current_version = self.get_current_version(event.aggregate_type(), &event.aggregate_id()).await?;
        let new_version = current_version + 1;
        
        // 插入事件
        sqlx::query(
            "INSERT INTO events (id, aggregate_id, aggregate_type, event_type, 
                  payload, metadata, occurred_at, version)
             VALUES ($1, $2, $3, $4, $5, $6, $7, $8)"
        )
        .bind(event.event_id().to_string())
        .bind(event.aggregate_id())
        .bind(event.aggregate_type())
        .bind(event.event_type())
        .bind(payload)
        .bind(metadata)
        .bind(event.occurred_at())
        .bind(new_version)
        .execute(&*self.db_client)
        .await?;
        
        Ok(())
    }
    
    // 获取聚合的事件流
    pub async fn get_events(&self, aggregate_type: &str, aggregate_id: &str) -> Result<Vec<EventEntity>, EventStoreError> {
        let events = sqlx::query_as::<_, EventEntity>(
            "SELECT id, aggregate_id, aggregate_type, event_type, payload, metadata, occurred_at, version
             FROM events
             WHERE aggregate_type = $1 AND aggregate_id = $2
             ORDER BY version ASC"
        )
        .bind(aggregate_type)
        .bind(aggregate_id)
        .fetch_all(&*self.db_client)
        .await?;
        
        Ok(events)
    }
    
    // 获取当前版本号
    async fn get_current_version(&self, aggregate_type: &str, aggregate_id: &str) -> Result<i64, EventStoreError> {
        let result = sqlx::query!(
            "SELECT MAX(version) as max_version
             FROM events
             WHERE aggregate_type = $1 AND aggregate_id = $2",
            aggregate_type,
            aggregate_id
        )
        .fetch_one(&*self.db_client)
        .await?;
        
        Ok(result.max_version.unwrap_or(0))
    }
}

// 映射策略选择指南
pub mod mapping_guidelines {
    // 不同映射策略的适用场景
    pub enum MappingStrategy {
        /// 直接映射：简单1:1映射，适用于数据结构基本一致的情况
        DirectMapping,
        
        /// 适配器映射：用于处理结构差异较大的模型之间的转换
        AdapterMapping,
        
        /// 转换器映射：提供双向转换能力，适用于需要往返转换的场景
        ConverterMapping,
        
        /// 装配器映射：组合多个来源的数据，构建复杂对象
        AssemblerMapping,
        
        /// 投影映射：创建原对象的简化视图，常用于DTO创建
        ProjectionMapping,
    }
    
    pub fn select_mapping_strategy(context: &MappingContext) -> MappingStrategy {
        match context {
            // 简单值对象或基本数据类型映射
            MappingContext::SimpleValueObject => MappingStrategy::DirectMapping,
            
            // 领域实体到DTO的映射（展示层）
            MappingContext::EntityToDto { is_nested: false } => MappingStrategy::ProjectionMapping,
            MappingContext::EntityToDto { is_nested: true } => MappingStrategy::AdapterMapping,
            
            // 存储模型到领域模型的映射（持久化层）
            MappingContext::StorageToEntity { complexity } => {
                match complexity {
                    ComplexityLevel::Simple => MappingStrategy::DirectMapping,
                    ComplexityLevel::Medium => MappingStrategy::ConverterMapping,
                    ComplexityLevel::Complex => MappingStrategy::AssemblerMapping,
                }
            },
            
            // 外部系统集成映射
            MappingContext::ExternalSystem { bi_directional } => {
                if *bi_directional {
                    MappingStrategy::ConverterMapping
                } else {
                    MappingStrategy::AdapterMapping
                }
            },
            
            // 领域事件映射
            MappingContext::DomainEvent => MappingStrategy::AdapterMapping,
            
            // 聚合根映射
            MappingContext::Aggregate => MappingStrategy::AssemblerMapping,
        }
    }
    
    pub enum MappingContext {
        SimpleValueObject,
        EntityToDto { is_nested: bool },
        StorageToEntity { complexity: ComplexityLevel },
        ExternalSystem { bi_directional: bool },
        DomainEvent,
        Aggregate,
    }
    
    pub enum ComplexityLevel {
        Simple,   // 1:1映射，结构基本一致
        Medium,   // 需要一些转换逻辑，但结构相似
        Complex,  // 复杂组合，可能涉及多个来源
    }
    
    // 映射策略最佳实践建议
    pub struct MappingGuidelines;
    
    impl MappingGuidelines {
        // 值对象映射最佳实践
        pub fn value_object_guidelines() -> Vec<&'static str> {
            vec![
                "使用内部类型保持不可变性和验证",
                "提供辅助构造方法以简化常见用例",
                "实现Display和基本操作符以提高可用性",
                "提供验证逻辑确保值对象一致性",
                "使用newtype模式增强类型安全性",
            ]
        }
        
        // DTO映射最佳实践
        pub fn dto_mapping_guidelines() -> Vec<&'static str> {
            vec![
                "保持DTO简单，专注于数据传输而非业务逻辑",
                "仅包含必要字段，减少不必要的数据传输",
                "使用静态工厂方法实现映射逻辑",
                "考虑版本化以支持API演化",
                "使用构建器模式处理复杂嵌套DTO",
                "在DTO和领域模型之间保持清晰的边界",
            ]
        }
        
        // 存储映射最佳实践
        pub fn storage_mapping_guidelines() -> Vec<&'static str> {
            vec![
                "将映射逻辑封装在仓储实现中",
                "使用事务确保聚合持久化的原子性",
                "考虑延迟加载优化性能",
                "处理存储和领域模型之间的版本差异",
                "使用投影优化查询性能",
                "考虑缓存减少数据库访问",
            ]
        }
        
        // 外部系统集成映射最佳实践
        pub fn external_system_guidelines() -> Vec<&'static str> {
            vec![
                "使用防腐层隔离外部系统变化",
                "实现明确的错误映射策略",
                "使用重试和熔断提高集成可靠性",
                "考虑幂等性确保安全重试",
                "使用契约测试验证集成正确性",
                "记录映射过程以便调试",
            ]
        }
        
        // 事件映射最佳实践
        pub fn event_mapping_guidelines() -> Vec<&'static str> {
            vec![
                "保持事件不可变，确保事件溯源完整性",
                "包含足够上下文以便正确处理",
                "使用版本控制支持事件结构演化",
                "考虑序列化格式的兼容性",
                "添加元数据支持调试和监控",
                "考虑事件重放场景",
            ]
        }
    }
}

// 示例：选择适当的映射策略
pub fn demonstrate_mapping_strategy_selection() {
    use mapping_guidelines::*;
    
    // 示例1：简单值对象
    let strategy1 = select_mapping_strategy(&MappingContext::SimpleValueObject);
    println!("对于简单值对象，建议使用：{:?}", strategy1);
    
    // 示例2：实体到DTO的映射
    let strategy2 = select_mapping_strategy(&MappingContext::EntityToDto { is_nested: false });
    println!("对于实体到DTO的映射，建议使用：{:?}", strategy2);
    
    // 示例3：复杂存储到实体的映射
    let strategy3 = select_mapping_strategy(&MappingContext::StorageToEntity { 
        complexity: ComplexityLevel::Complex 
    });
    println!("对于复杂存储到实体的映射，建议使用：{:?}", strategy3);
    
    // 示例4：外部系统双向集成
    let strategy4 = select_mapping_strategy(&MappingContext::ExternalSystem { 
        bi_directional: true 
    });
    println!("对于外部系统双向集成，建议使用：{:?}", strategy4);
    
    // 示例5：聚合根映射
    let strategy5 = select_mapping_strategy(&MappingContext::Aggregate);
    println!("对于聚合根映射，建议使用：{:?}", strategy5);
    
    // 获取映射最佳实践
    let dto_guidelines = MappingGuidelines::dto_mapping_guidelines();
    println!("DTO映射最佳实践: {:?}", dto_guidelines);
}
```

### 5.2 避免常见陷阱

常见映射问题的解决方案：

```rust
// 常见映射陷阱及避免方法
pub mod mapping_pitfalls {
    // 问题：对象图遍历深度问题
    pub fn demonstrate_object_graph_traversal_issue() {
        // 问题代码：无限递归风险
        #[allow(dead_code)]
        fn problematic_mapping(entity: &Entity) -> EntityDto {
            let children_dtos = entity.children.iter()
                .map(|child| problematic_mapping(child)) // 可能导致无限递归
                .collect();
                
            EntityDto {
                id: entity.id.clone(),
                name: entity.name.clone(),
                children: children_dtos,
            }
        }
        
        // 解决方案：限制遍历深度
        #[allow(dead_code)]
        fn improved_mapping(entity: &Entity, max_depth: u32) -> EntityDto {
            let children_dtos = if max_depth > 0 {
                entity.children.iter()
                    .map(|child| improved_mapping(child, max_depth - 1))
                    .collect()
            } else {
                Vec::new() // 到达最大深度，不再递归
            };
            
            EntityDto {
                id: entity.id.clone(),
                name: entity.name.clone(),
                children: children_dtos,
            }
        }
    }
    
    // 问题：映射中的副作用
    pub fn demonstrate_side_effects_issue() {
        // 问题代码：在映射过程中执行数据库查询
        #[allow(dead_code)]
        async fn problematic_mapping(order: &Order, db: &PgPool) -> OrderDto {
            let mut order_dto = OrderDto {
                id: order.id.to_string(),
                // ...其他字段映射
                items: Vec::new(),
            };
            
            // 错误：在映射函数中执行副作用操作
            for item in &order.items {
                // 在映射过程中查询数据库获取产品详情
                let product = sqlx::query_as::<_, Product>(
                    "SELECT * FROM products WHERE id = $1"
                )
                .bind(&item.product_id)
                .fetch_one(db)
                .await
                .unwrap();
                
                order_dto.items.push(OrderItemDto {
                    id: item.id.to_string(),
                    product_name: product.name, // 使用查询结果
                    // ...其他字段
                });
            }
            
            order_dto
        }
        
        // 解决方案：使用装配器模式，预先加载所有必要数据
        #[allow(dead_code)]
        struct OrderAssembler {
            db: PgPool,
        }
        
        #[allow(dead_code)]
        impl OrderAssembler {
            // 预加载所有必要数据
            async fn load_order_with_details(&self, order_id: &OrderId) -> Result<OrderWithDetails, anyhow::Error> {
                // 加载订单
                let order = sqlx::query_as::<_, Order>(
                    "SELECT * FROM orders WHERE id = $1"
                )
                .bind(order_id.to_string())
                .fetch_one(&self.db)
                .await?;
                
                // 加载订单项
                let items = sqlx::query_as::<_, OrderItem>(
                    "SELECT * FROM order_items WHERE order_id = $1"
                )
                .bind(order_id.to_string())
                .fetch_all(&self.db)
                .await?;
                
                // 收集所有产品ID
                let product_ids: Vec<String> = items.iter()
                    .map(|item| item.product_id.to_string())
                    .collect();
                
                // 批量加载所有产品
                let products = sqlx::query_as::<_, Product>(
                    "SELECT * FROM products WHERE id = ANY($1)"
                )
                .bind(product_ids)
                .fetch_all(&self.db)
                .await?;
                
                // 构建产品ID到产品的映射
                let product_map: HashMap<String, Product> = products.into_iter()
                    .map(|p| (p.id.to_string(), p))
                    .collect();
                
                Ok(OrderWithDetails {
                    order,
                    items,
                    product_map,
                })
            }
            
            // 无副作用的纯映射函数
            fn to_dto(&self, details: &OrderWithDetails) -> OrderDto {
                let items_dto = details.items.iter()
                    .map(|item| {
                        let product = details.product_map.get(&item.product_id.to_string())
                            .expect("Product should be in map");
                            
                        OrderItemDto {
                            id: item.id.to_string(),
                            product_name: product.name.clone(),
                            // ...其他字段
                        }
                    })
                    .collect();
                    
                OrderDto {
                    id: details.order.id.to_string(),
                    // ...其他字段映射
                    items: items_dto,
                }
            }
        }
    }
    
    // 问题：类型转换安全性
    pub fn demonstrate_type_conversion_issue() {
        // 问题代码：不安全的类型转换
        #[allow(dead_code)]
        fn problematic_parsing(dto: &OrderDto) -> Order {
            let order_id = OrderId::from_string(&dto.id).unwrap(); // 可能panic
            let customer_id = CustomerId::from_string(&dto.customer_id).unwrap(); // 可能panic
            
            let items = dto.items.iter()
                .map(|item_dto| {
                    let item_id = OrderItemId::from_string(&item_dto.id).unwrap(); // 可能panic
                    let product_id = ProductId::from_string(&item_dto.product_id).unwrap(); // 可能panic
                    let quantity: u32 = item_dto.quantity.parse().unwrap(); // 可能panic
                    
                    OrderItem {
                        id: item_id,
                        product_id,
                        quantity,
                        // ...其他字段
                    }
                })
                .collect();
                
            Order {
                id: order_id,
                customer_id,
                items,
                // ...其他字段
            }
        }
        
        // 解决方案：合适的错误处理
        #[allow(dead_code)]
        fn improved_parsing(dto: &OrderDto) -> Result<Order, MappingError> {
            let order_id = OrderId::from_string(&dto.id)
                .map_err(|e| MappingError::InvalidId(format!("Invalid order ID: {}", e)))?;
                
            let customer_id = CustomerId::from_string(&dto.customer_id)
                .map_err(|e| MappingError::InvalidId(format!("Invalid customer ID: {}", e)))?;
                
            let mut items = Vec::new();
            
            for item_dto in &dto.items {
                let item_id = OrderItemId::from_string(&item_dto.id)
                    .map_err(|e| MappingError::InvalidId(format!("Invalid item ID: {}", e)))?;
                    
                let product_id = ProductId::from_string(&item_dto.product_id)
                    .map_err(|e| MappingError::InvalidId(format!("Invalid product ID: {}", e)))?;
                    
                let quantity: u32 = item_dto.quantity.parse()
                    .map_err(|e| MappingError::InvalidFormat(format!("Invalid quantity: {}", e)))?;
                    
                items.push(OrderItem {
                    id: item_id,
                    product_id,
                    quantity,
                    // ...其他字段
                });
            }
            
            Ok(Order {
                id: order_id,
                customer_id,
                items,
                // ...其他字段
            })
        }
    }
    
    // 问题：忽略版本差异
    pub fn demonstrate_version_mismatch_issue() {
        // 问题代码：没有处理版本差异
        #[allow(dead_code)]
        fn problematic_conversion(v1_dto: v1::ProductDto) -> Product {
            Product {
                id: ProductId::from_string(&v1_dto.id).unwrap(),
                name: v1_dto.name,
                description: v1_dto.description,
                price: Money::new(v1_dto.price, Currency::USD).unwrap(),
                // v2属性缺失，使用默认值
                categories: vec![v1_dto.category].into_iter()
                    .map(|name| ProductCategory { 
                        id: ProductCategoryId::new(), 
                        name 
                    })
                    .collect(),
                attributes: HashMap::new(), // v1中不存在
                created_at: Utc::now(), // 无法从v1中获取
                updated_at: Utc::now(), // 无法从v1中获取
            }
        }
        
        // 解决方案：版本适配器
        #[allow(dead_code)]
        struct ProductVersionAdapter;
        
        #[allow(dead_code)]
        impl ProductVersionAdapter {
            fn v1_to_domain(v1_dto: v1::ProductDto, existing: Option<&Product>) -> Result<Product, MappingError> {
                // 使用现有产品的属性作为默认值
                let created_at = existing.map(|p| p.created_at).unwrap_or_else(Utc::now);
                let attributes = existing.map(|p| p.attributes.clone()).unwrap_or_default();
                
                // 将v1分类转换为v2格式
                let categories = vec![v1_dto.category].into_iter()
                    .map(|name| ProductCategory { 
                        id: ProductCategoryId::new(), 
                        name 
                    })
                    .collect();
                    
                Ok(Product {
                    id: ProductId::from_string(&v1_dto.id)
                        .map_err(|e| MappingError::InvalidId(e.to_string()))?,
                    name: v1_dto.name,
                    description: v1_dto.description,
                    price: Money::new(v1_dto.price, Currency::USD)
                        .map_err(|e| MappingError::InvalidData(e.to_string()))?,
                    categories,
                    attributes,
                    created_at,
                    updated_at: Utc::now(),
                })
            }
            
            fn v2_to_domain(v2_dto: v2::ProductDto) -> Result<Product, MappingError> {
                // 从v2 DTO提取所有字段
                let price = Money::new(
                    v2_dto.pricing.base_price,
                    Currency::from_code(&v2_dto.pricing.currency)
                        .map_err(|e| MappingError::InvalidData(e.to_string()))?
                ).map_err(|e| MappingError::InvalidData(e.to_string()))?;
                
                let categories = v2_dto.categories.into_iter()
                    .map(|name| ProductCategory { 
                        id: ProductCategoryId::new(), 
                        name 
                    })
                    .collect();
                    
                Ok(Product {
                    id: ProductId::from_string(&v2_dto.id)
                        .map_err(|e| MappingError::InvalidId(e.to_string()))?,
                    name: v2_dto.name,
                    description: v2_dto.description,
                    price,
                    categories,
                    attributes: v2_dto.attributes,
                    created_at: v2_dto.created_at,
                    updated_at: v2_dto.updated_at,
                })
            }
            
            // 智能选择适当的版本转换器
            fn to_domain(&self, dto: serde_json::Value, existing: Option<&Product>) -> Result<Product, MappingError> {
                // 尝试解析为v2格式
                if let Ok(v2_dto) = serde_json::from_value::<v2::ProductDto>(dto.clone()) {
                    return Self::v2_to_domain(v2_dto);
                }
                
                // 尝试解析为v1格式
                if let Ok(v1_dto) = serde_json::from_value::<v1::ProductDto>(dto.clone()) {
                    return Self::v1_to_domain(v1_dto, existing);
                }
                
                Err(MappingError::UnknownFormat("Could not parse as any known version".into()))
            }
        }
    }
}

// 映射陷阱的避免策略总结
pub struct MappingPitfallAvoidanceStrategies;

impl MappingPitfallAvoidanceStrategies {
    pub fn get_strategies() -> HashMap<&'static str, Vec<&'static str>> {
        let mut strategies = HashMap::new();
        
        strategies.insert("对象图遍历深度问题", vec![
            "限制递归深度，使用参数控制最大深度",
            "使用迭代而非递归处理深层结构",
            "考虑懒加载或分页加载大型对象图",
            "序列化时使用引用或ID代替完整对象",
        ]);
        
        strategies.insert("映射中的副作用", vec![
            "使用装配器模式预加载所有必要数据",
            "保持映射函数纯粹，仅处理转换逻辑",
            "在映射之前完成所有IO操作",
            "使用缓存优化频繁的数据访问",
        ]);
        
        strategies.insert("类型转换安全性", vec![
            "始终处理转换错误，避免unwrap和expect",
            "返回Result而非直接panic",
            "在集合映射中，使用collect::<Result<_, _>>()",
            "提供有意义的错误消息以便调试",
        ]);
        
        strategies.insert("版本差异处理", vec![
            "实现专门的版本适配器处理不同版本",
            "使用默认值处理缺失字段",
            "保持向后兼容性",
            "添加版本检测和自适应解析",
        ]);
        
        strategies.insert("性能问题", vec![
            "避免N+1查询问题，使用批量加载",
            "考虑延迟加载不常用字段",
            "对热点路径的映射使用缓存",
            "在高性能场景考虑手动优化而非通用映射",
        ]);
        
        strategies.insert("内存泄漏", vec![
            "避免循环引用",
            "使用弱引用处理父子关系",
            "小心处理闭包中的捕获",
            "对大型对象流使用增量处理",
        ]);
        
        strategies
    }
}
```

### 5.3 测试映射的最佳实践

映射测试策略：

```rust
// 映射测试最佳实践
#[cfg(test)]
mod mapping_tests {
    use super::*;
    use proptest::prelude::*;
    
    // 

```rust
    // 1. 单元测试：验证特定映射场景
    #[test]
    fn test_order_dto_mapping() {
        // 准备测试数据
        let order_id = OrderId::new();
        let customer_id = CustomerId::new();
        
        let item1 = OrderItem {
            id: OrderItemId::new(),
            product_id: ProductId::new(),
            name: "Product 1".to_string(),
            unit_price: 10.0,
            quantity: 2,
            total_price: 20.0,
        };
        
        let item2 = OrderItem {
            id: OrderItemId::new(),
            product_id: ProductId::new(),
            name: "Product 2".to_string(),
            unit_price: 15.0,
            quantity: 1,
            total_price: 15.0,
        };
        
        let shipping_address = Address {
            street_line1: "123 Test St".to_string(),
            street_line2: "".to_string(),
            city: "Test City".to_string(),
            state: "TS".to_string(),
            postal_code: "12345".to_string(),
            country: "US".to_string(),
        };
        
        let order = Order {
            id: order_id,
            customer_id,
            items: vec![item1, item2],
            status: OrderStatus::Draft,
            shipping_address: Some(shipping_address),
            payment_status: PaymentStatus::Pending,
            created_at: Utc::now(),
            updated_at: Utc::now(),
        };
        
        // 执行映射
        let dto = OrderDto::from_domain(&order);
        
        // 验证基本属性映射
        assert_eq!(dto.id, order.id.to_string());
        assert_eq!(dto.customer_id, order.customer_id.to_string());
        assert_eq!(dto.status, order.status.to_string());
        assert_eq!(dto.payment_status, order.payment_status.to_string());
        
        // 验证集合映射
        assert_eq!(dto.items.len(), order.items.len());
        assert_eq!(dto.items[0].id, order.items[0].id.to_string());
        assert_eq!(dto.items[0].quantity, order.items[0].quantity as i32);
        
        // 验证嵌套对象映射
        assert!(dto.shipping_address.is_some());
        let address_dto = dto.shipping_address.unwrap();
        assert_eq!(address_dto.city, order.shipping_address.unwrap().city);
        
        // 验证计算字段
        let expected_total = order.items.iter()
            .map(|item| item.total_price)
            .sum::<f64>();
        assert_eq!(dto.total_amount, expected_total);
    }
    
    // 2. 往返映射测试：验证双向转换的一致性
    #[test]
    fn test_bidirectional_mapping_consistency() {
        // 准备测试数据
        let customer = Customer {
            id: CustomerId::new(),
            name: "Test Customer".to_string(),
            email: Email::try_from("test@example.com".to_string()).unwrap(),
            phone: Some(PhoneNumber::try_from("+1234567890".to_string()).unwrap()),
            address: Some(Address {
                street_line1: "123 Test St".to_string(),
                street_line2: "".to_string(),
                city: "Test City".to_string(),
                state: "TS".to_string(),
                postal_code: "12345".to_string(),
                country: "US".to_string(),
            }),
            customer_type: CustomerType::Individual,
            status: CustomerStatus::Active,
            created_at: Utc::now(),
            preferences: CustomerPreferences::default(),
        };
        
        // 从领域对象到DTO
        let dto = CustomerDto::from_domain(&customer);
        
        // 验证基本映射
        assert_eq!(dto.id, customer.id.to_string());
        assert_eq!(dto.name, customer.name);
        assert_eq!(dto.email, customer.email.value());
        
        // 从DTO回到领域对象
        let result = dto.to_domain();
        assert!(result.is_ok());
        let mapped_customer = result.unwrap();
        
        // 验证一致性
        assert_eq!(mapped_customer.id, customer.id);
        assert_eq!(mapped_customer.name, customer.name);
        assert_eq!(mapped_customer.email, customer.email);
        assert_eq!(mapped_customer.status, customer.status);
        
        // 验证嵌套对象
        if let Some(original_address) = customer.address.as_ref() {
            assert!(mapped_customer.address.is_some());
            let mapped_address = mapped_customer.address.unwrap();
            assert_eq!(mapped_address.street_line1, original_address.street_line1);
            assert_eq!(mapped_address.city, original_address.city);
            assert_eq!(mapped_address.postal_code, original_address.postal_code);
        }
    }
    
    // 3. 属性测试：使用生成的测试数据验证映射属性
    proptest! {
        #[test]
        fn test_money_mapping_properties(amount in 0.01..100000.0) {
            // 创建Money值对象
            let money = Money::new_usd(amount).unwrap();
            
            // 序列化为JSON
            let json = serde_json::to_string(&money).unwrap();
            
            // 反序列化回Money
            let deserialized: Money = serde_json::from_str(&json).unwrap();
            
            // 验证属性：序列化和反序列化应保持值的一致性
            // 使用近似相等处理浮点数精度问题
            prop_assert!((deserialized.value() - money.value()).abs() < 0.001);
            prop_assert_eq!(deserialized.currency(), money.currency());
        }
        
        #[test]
        fn test_order_item_dto_mapping(
            quantity in 1u32..100,
            unit_price in 0.01..1000.0,
            name in "\\PC{1,50}" // 生成1-50个可打印字符的字符串
        ) {
            // 创建订单项
            let id = OrderItemId::new();
            let product_id = ProductId::new();
            let total_price = unit_price * quantity as f64;
            
            let item = OrderItem {
                id: id.clone(),
                product_id: product_id.clone(),
                name: name.clone(),
                unit_price,
                quantity,
                total_price,
            };
            
            // 映射到DTO
            let dto = OrderItemDto::from_domain(&item);
            
            // 验证映射结果
            prop_assert_eq!(dto.id, id.to_string());
            prop_assert_eq!(dto.product_id, product_id.to_string());
            prop_assert_eq!(dto.name, name);
            prop_assert_eq!(dto.quantity, quantity as i32);
            prop_assert!((dto.unit_price - unit_price).abs() < 0.001);
            prop_assert!((dto.total_price - total_price).abs() < 0.001);
            
            // 从DTO映射回领域对象
            let result = dto.to_domain();
            prop_assert!(result.is_ok());
            
            let mapped_item = result.unwrap();
            prop_assert_eq!(mapped_item.id, id);
            prop_assert_eq!(mapped_item.product_id, product_id);
            prop_assert_eq!(mapped_item.name, name);
            prop_assert_eq!(mapped_item.quantity, quantity);
            prop_assert!((mapped_item.unit_price - unit_price).abs() < 0.001);
            prop_assert!((mapped_item.total_price - total_price).abs() < 0.001);
        }
    }
    
    // 4. 边界条件测试：验证特殊情况处理
    #[test]
    fn test_address_mapping_edge_cases() {
        // 测试空地址
        let empty_address = Address {
            street_line1: "".to_string(),
            street_line2: "".to_string(),
            city: "".to_string(),
            state: "".to_string(),
            postal_code: "".to_string(),
            country: "".to_string(),
        };
        
        let dto = AddressDto::from_domain(&empty_address);
        
        // 验证空字段处理
        assert_eq!(dto.street_line1, "");
        assert_eq!(dto.city, "");
        
        // 映射回领域对象
        let result = dto.to_domain();
        assert!(result.is_ok());
        
        // 测试超长字段
        let long_string = "a".repeat(1000);
        let long_address = Address {
            street_line1: long_string.clone(),
            street_line2: "".to_string(),
            city: "Test City".to_string(),
            state: "TS".to_string(),
            postal_code: "12345".to_string(),
            country: "US".to_string(),
        };
        
        let dto = AddressDto::from_domain(&long_address);
        
        // 验证长字段处理（假设DTO实现了截断）
        assert!(dto.street_line1.len() <= 255);
        
        // 测试特殊字符
        let special_address = Address {
            street_line1: "123 Test St, Apt #1".to_string(),
            street_line2: "Building \"North\" (2nd Floor)".to_string(),
            city: "O'Connor".to_string(),
            state: "TS".to_string(),
            postal_code: "12345-6789".to_string(),
            country: "US".to_string(),
        };
        
        let dto = AddressDto::from_domain(&special_address);
        let result = dto.to_domain();
        assert!(result.is_ok());
        
        let mapped_address = result.unwrap();
        assert_eq!(mapped_address.street_line1, special_address.street_line1);
        assert_eq!(mapped_address.street_line2, special_address.street_line2);
        assert_eq!(mapped_address.city, special_address.city);
    }
    
    // 5. 集成测试：验证与存储层的映射
    #[tokio::test]
    async fn test_cart_repository_mapping() {
        // 设置测试数据库
        let pool = setup_test_database().await;
        
        // 创建购物车
        let cart_id = CartId::new();
        let customer_id = CustomerId::new();
        
        let item1 = CartItem {
            id: CartItemId::new(),
            product_id: ProductId::new(),
            quantity: 2,
            unit_price: Money::new_usd(10.0).unwrap(),
            total_price: Money::new_usd(20.0).unwrap(),
            added_at: Utc::now(),
        };
        
        let item2 = CartItem {
            id: CartItemId::new(),
            product_id: ProductId::new(),
            quantity: 1,
            unit_price: Money::new_usd(15.0).unwrap(),
            total_price: Money::new_usd(15.0).unwrap(),
            added_at: Utc::now(),
        };
        
        let shipping = ShippingMethod {
            code: "express".to_string(),
            name: "Express Shipping".to_string(),
            cost: Money::new_usd(5.0).unwrap(),
            estimated_days: 2,
        };
        
        let cart = Cart {
            id: cart_id.clone(),
            customer_id: Some(customer_id),
            items: vec![item1.clone(), item2.clone()],
            created_at: Utc::now(),
            updated_at: Utc::now(),
            coupon_code: Some("SAVE10".to_string()),
            shipping_method: Some(shipping),
        };
        
        // 创建仓储
        let repository = CartRepository {
            db_client: Arc::new(pool.clone()),
        };
        
        // 保存购物车
        let save_result = repository.save(&cart).await;
        assert!(save_result.is_ok());
        
        // 加载购物车
        let loaded_result = repository.find_by_id(&cart_id).await;
        assert!(loaded_result.is_ok());
        
        let loaded_cart_option = loaded_result.unwrap();
        assert!(loaded_cart_option.is_some());
        
        let loaded_cart = loaded_cart_option.unwrap();
        
        // 验证基本属性
        assert_eq!(loaded_cart.id, cart.id);
        assert_eq!(loaded_cart.customer_id, cart.customer_id);
        assert_eq!(loaded_cart.coupon_code, cart.coupon_code);
        
        // 验证集合
        assert_eq!(loaded_cart.items.len(), cart.items.len());
        
        // 验证项目
        let loaded_item1 = loaded_cart.items.iter()
            .find(|i| i.id == item1.id)
            .expect("Item 1 should be present");
        
        assert_eq!(loaded_item1.product_id, item1.product_id);
        assert_eq!(loaded_item1.quantity, item1.quantity);
        assert_eq!(loaded_item1.unit_price.value(), item1.unit_price.value());
        
        // 验证复杂对象
        assert!(loaded_cart.shipping_method.is_some());
        let loaded_shipping = loaded_cart.shipping_method.unwrap();
        assert_eq!(loaded_shipping.code, shipping.code);
        assert_eq!(loaded_shipping.cost.value(), shipping.cost.value());
    }
    
    // 6. 异常情况测试：验证错误处理
    #[test]
    fn test_customer_dto_mapping_validation() {
        // 无效电子邮件
        let invalid_dto = CustomerDto {
            id: Uuid::new_v4().to_string(),
            name: "Test Customer".to_string(),
            email: "not-an-email".to_string(),
            phone: Some("+1234567890".to_string()),
            status: "active".to_string(),
            // ...其他字段
        };
        
        let result = invalid_dto.to_domain();
        assert!(result.is_err());
        
        match result {
            Err(DtoMappingError::ValidationError(msg)) => {
                assert!(msg.contains("email"));
            },
            _ => panic!("Expected ValidationError for invalid email"),
        }
        
        // 无效电话号码
        let invalid_phone_dto = CustomerDto {
            id: Uuid::new_v4().to_string(),
            name: "Test Customer".to_string(),
            email: "test@example.com".to_string(),
            phone: Some("invalid-phone".to_string()),
            status: "active".to_string(),
            // ...其他字段
        };
        
        let result = invalid_phone_dto.to_domain();
        assert!(result.is_err());
        
        // 无效状态
        let invalid_status_dto = CustomerDto {
            id: Uuid::new_v4().to_string(),
            name: "Test Customer".to_string(),
            email: "test@example.com".to_string(),
            phone: Some("+1234567890".to_string()),
            status: "not-a-status".to_string(),
            // ...其他字段
        };
        
        let result = invalid_status_dto.to_domain();
        assert!(result.is_err());
        
        match result {
            Err(DtoMappingError::InvalidEnumValue(field, value)) => {
                assert_eq!(field, "status");
                assert_eq!(value, "not-a-status");
            },
            _ => panic!("Expected InvalidEnumValue for invalid status"),
        }
    }
    
    // 7. 性能测试：验证映射效率
    #[test]
    fn test_mapping_performance() {
        use std::time::Instant;
        
        // 生成大量测试数据
        const NUM_ITEMS: usize = 1000;
        let mut orders = Vec::with_capacity(NUM_ITEMS);
        
        for _ in 0..NUM_ITEMS {
            let order_id = OrderId::new();
            let customer_id = CustomerId::new();
            
            let item1 = OrderItem {
                id: OrderItemId::new(),
                product_id: ProductId::new(),
                name: "Product 1".to_string(),
                unit_price: 10.0,
                quantity: 2,
                total_price: 20.0,
            };
            
            let item2 = OrderItem {
                id: OrderItemId::new(),
                product_id: ProductId::new(),
                name: "Product 2".to_string(),
                unit_price: 15.0,
                quantity: 1,
                total_price: 15.0,
            };
            
            let order = Order {
                id: order_id,
                customer_id,
                items: vec![item1, item2],
                status: OrderStatus::Draft,
                shipping_address: None,
                payment_status: PaymentStatus::Pending,
                created_at: Utc::now(),
                updated_at: Utc::now(),
            };
            
            orders.push(order);
        }
        
        // 测量批量映射性能
        let start = Instant::now();
        
        let dtos: Vec<OrderDto> = orders.iter()
            .map(OrderDto::from_domain)
            .collect();
            
        let duration = start.elapsed();
        
        // 验证结果
        assert_eq!(dtos.len(), NUM_ITEMS);
        
        // 输出性能数据
        println!("Mapped {} orders in {:?} ({:?} per order)",
            NUM_ITEMS, duration, duration / NUM_ITEMS as u32);
            
        // 确保映射速度合理
        // 这是一个相对宽松的上限，实际性能会因环境而异
        assert!(duration.as_millis() < 1000, "Mapping took too long: {:?}", duration);
    }
    
    // 辅助函数
    async fn setup_test_database() -> PgPool {
        // 这里应该连接测试数据库或使用内存数据库
        // 为了简化，返回模拟的连接池
        PgPool::connect("postgres://postgres:postgres@localhost/test_db")
            .await
            .expect("Failed to connect to test database")
    }
}

// 映射测试最佳实践总结
pub struct MappingTestBestPractices;

impl MappingTestBestPractices {
    pub fn get_practices() -> HashMap<&'static str, Vec<&'static str>> {
        let mut practices = HashMap::new();
        
        practices.insert("单元测试", vec![
            "测试从领域对象到DTO的基本映射",
            "验证所有字段的正确映射",
            "测试嵌套对象和集合的映射",
            "验证计算字段和导出值",
        ]);
        
        practices.insert("往返映射测试", vec![
            "验证双向转换的一致性",
            "测试从领域对象到DTO再回到领域对象的过程",
            "确保没有信息丢失或错误转换",
            "验证嵌套对象和集合的往返映射",
        ]);
        
        practices.insert("属性测试", vec![
            "使用生成的测试数据验证映射属性",
            "测试不同范围的数值和字符串输入",
            "验证映射不变量在随机输入下的保持",
            "使用proptest或类似框架自动生成测试用例",
        ]);
        
        practices.insert("边界条件测试", vec![
            "测试空值和默认值处理",
            "验证长字符串和大数值的处理",
            "测试特殊字符和非ASCII字符的映射",
            "验证最小和最大值处理",
        ]);
        
        practices.insert("异常情况测试", vec![
            "验证无效输入的错误处理",
            "测试类型转换的异常情况",
            "验证错误消息的明确性",
            "测试验证逻辑的正确应用",
        ]);
        
        practices.insert("集成测试", vec![
            "验证与存储层的完整映射",
            "测试从数据库到领域模型的映射",
            "验证领域模型到数据库的保存",
            "测试事务处理和并发情况",
        ]);
        
        practices.insert("性能测试", vec![
            "衡量批量映射的性能",
            "验证映射速度在可接受范围内",
            "识别和优化性能瓶颈",
            "比较不同映射实现的性能",
        ]);
        
        practices
    }
}
```

### 5.4 映射的自动化和代码生成

自动化映射实现：

```rust
// 自动化映射实现
// 基于宏的映射生成
#[macro_export]
macro_rules! derive_dto_mapping {
    // 从实体到DTO的映射
    (entity_to_dto, $entity:ty, $dto:ty, {
        $(
            $entity_field:ident => $dto_field:ident $(, transform: $transform:expr)?
        ),*
        $(,)?
    }) => {
        impl $dto {
            pub fn from_domain(entity: &$entity) -> Self {
                Self {
                    $(
                        $dto_field: derive_dto_mapping!(@transform_field entity.$entity_field $(, $transform)?),
                    )*
                }
            }
        }
    };
    
    // 从DTO到实体的映射
    (dto_to_entity, $dto:ty, $entity:ty, {
        $(
            $dto_field:ident => $entity_field:ident $(, transform: $transform:expr)?
        ),*
        $(,)?
    }) => {
        impl $dto {
            pub fn to_domain(&self) -> Result<$entity, DtoMappingError> {
                Ok($entity {
                    $(
                        $entity_field: derive_dto_mapping!(@transform_field_result self.$dto_field $(, $transform)?),
                    )*
                })
            }
        }
    };
    
    // 双向映射
    (bidirectional, $entity:ty, $dto:ty, {
        $(
            $entity_field:ident <=> $dto_field:ident $(,
                to_dto: $to_dto:expr, 
                to_entity: $to_entity:expr
            )?
        ),*
        $(,)?
    }) => {
        impl $dto {
            pub fn from_domain(entity: &$entity) -> Self {
                Self {
                    $(
                        $dto_field: derive_dto_mapping!(@transform_field entity.$entity_field $(, $to_dto)?),
                    )*
                }
            }
            
            pub fn to_domain(&self) -> Result<$entity, DtoMappingError> {
                Ok($entity {
                    $(
                        $entity_field: derive_dto_mapping!(@transform_field_result self.$dto_field $(, $to_entity)?),
                    )*
                })
            }
        }
    };
    
    // 用于处理转换表达式的内部规则
    (@transform_field $field:expr) => { $field.clone() };
    (@transform_field $field:expr, $transform:expr) => { $transform($field) };
    
    (@transform_field_result $field:expr) => { $field.clone() };
    (@transform_field_result $field:expr, $transform:expr) => { 
        $transform($field).map_err(|e| DtoMappingError::ValidationError(e.to_string()))?
    };
}

// 使用宏生成映射示例
#[derive(Debug, Clone)]
struct Product {
    id: ProductId,
    name: String,
    description: String,
    price: Money,
    categories: Vec<ProductCategory>,
}

#[derive(Debug, Serialize, Deserialize)]
struct ProductDto {
    id: String,
    name: String,
    description: String,
    price: f64,
    currency: String,
    categories: Vec<String>,
}

// 使用宏自动生成映射
derive_dto_mapping!(bidirectional, Product, ProductDto, {
    id <=> id,
        to_dto: |id: &ProductId| id.to_string(),
        to_entity: |id: &str| ProductId::from_string(id),
    name <=> name,
    description <=> description,
    price <=> price,
        to_dto: |price: &Money| price.value(),
        to_entity: |price: &f64| {
            let currency = Currency::from_code(&self.currency)?;
            Money::new(*price, currency)
        },
    categories <=> categories,
        to_dto: |cats: &[ProductCategory]| cats.iter().map(|c| c.name.clone()).collect(),
        to_entity: |cat_names: &[String]| {
            cat_names.iter().map(|name| ProductCategory {
                id: ProductCategoryId::new(),
                name: name.clone(),
            }).collect()
        },
});

// 特征映射框架
// 定义映射特征
pub trait Mapper<From, To> {
    fn map(&self, from: &From) -> To;
}

pub trait TryMapper<From, To, Error> {
    fn try_map(&self, from: &From) -> Result<To, Error>;
}

// 组合多个映射器
pub struct MapperChain<From, Intermediate, To> {
    first: Box<dyn Mapper<From, Intermediate>>,
    second: Box<dyn Mapper<Intermediate, To>>,
}

impl<From, Intermediate, To> MapperChain<From, Intermediate, To> {
    pub fn new<M1, M2>(first: M1, second: M2) -> Self
    where
        M1: Mapper<From, Intermediate> + 'static,
        M2: Mapper<Intermediate, To> + 'static,
    {
        Self {
            first: Box::new(first),
            second: Box::new(second),
        }
    }
}

impl<From, Intermediate, To> Mapper<From, To> for MapperChain<From, Intermediate, To> {
    fn map(&self, from: &From) -> To {
        let intermediate = self.first.map(from);
        self.second.map(&intermediate)
    }
}

// 具体映射器实现示例
pub struct OrderToOrderDtoMapper;

impl Mapper<Order, OrderDto> for OrderToOrderDtoMapper {
    fn map(&self, order: &Order) -> OrderDto {
        OrderDto {
            id: order.id.to_string(),
            customer_id: order.customer_id.to_string(),
            items: order.items.iter()
                .map(|item| OrderItemDto {
                    id: item.id.to_string(),
                    product_id: item.product_id.to_string(),
                    name: item.name.clone(),
                    quantity: item.quantity as i32,
                    unit_price: item.unit_price,
                    total_price: item.total_price,
                })
                .collect(),
            status: order.status.to_string(),
            shipping_address: order.shipping_address.as_ref()
                .map(|addr| AddressDto {
                    street_line1: addr.street_line1.clone(),
                    street_line2: addr.street_line2.clone(),
                    city: addr.city.clone(),
                    state: addr.state.clone(),
                    postal_code: addr.postal_code.clone(),
                    country: addr.country.clone(),
                }),
            payment_status: order.payment_status.to_string(),
            total_amount: order.calculate_total().value(),
            currency: order.calculate_total().currency().code().to_string(),
            created_at: order.created_at.to_rfc3339(),
            updated_at: order.updated_at.to_rfc3339(),
        }
    }
}

pub struct OrderDtoToOrderMapper;

impl TryMapper<OrderDto, Order, DtoMappingError> for OrderDtoToOrderMapper {
    fn try_map(&self, dto: &OrderDto) -> Result<Order, DtoMappingError> {
        let order_id = OrderId::from_string(&dto.id)?;
        let customer_id = CustomerId::from_string(&dto.customer_id)?;
        
        let items = dto.items.iter()
            .map(|item_dto| {
                let item_id = OrderItemId::from_string(&item_dto.id)?;
                let product_id = ProductId::from_string(&item_dto.product_id)?;
                
                Ok(OrderItem {
                    id: item_id,
                    product_id,
                    name: item_dto.name.clone(),
                    unit_price: item_dto.unit_price,
                    quantity: item_dto.quantity as u32,
                    total_price: item_dto.total_price,
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
            
        let status = OrderStatus::from_string(&dto.status)?;
        let payment_status = PaymentStatus::from_string(&dto.payment_status)?;
        
        let shipping_address = if let Some(addr_dto) = &dto.shipping_address {
            Some(Address {
                street_line1: addr_dto.street_line1.clone(),
                street_line2: addr_dto.street_line2.clone(),
                city: addr_dto.city.clone(),
                state: addr_dto.state.clone(),
                postal_code: addr_dto.postal_code.clone(),
                country: addr_dto.country.clone(),
            })
        } else {
            None
        };
        
        let created_at = DateTime::parse_from_rfc3339(&dto.created_at)
            .map_err(|e| DtoMappingError::DateParseError(e.to_string()))?
            .with_timezone(&Utc);
            
        let updated_at = DateTime::parse_from_rfc3339(&dto.updated_at)
            .map_err(|e| DtoMappingError::DateParseError(e.to_string()))?
            .with_timezone(&Utc);
            
        Ok(Order {
            id: order_id,
            customer_id,
            items,
            status,
            shipping_address,
            payment_status,
            created_at,
            updated_at,
        })
    }
}

// 依赖注入工厂
pub struct MapperFactory {
    mappers: HashMap<TypeId, Box<dyn Any>>,
}

impl MapperFactory {
    pub fn new() -> Self {
        Self {
            mappers: HashMap::new(),
        }
    }
    
    pub fn register<From, To, M>(&mut self, mapper: M)
    where
        From: 'static,
        To: 'static,
        M: Mapper<From, To> + 'static,
    {
        let type_id = TypeId::of::<(TypeId, TypeId)>();
        let key = (TypeId::of::<From>(), TypeId::of::<To>());
        self.mappers.insert(type_id, Box::new(mapper));
    }
    
    pub fn register_try<From, To, Error, M>(&mut self, mapper: M)
    where
        From: 'static,
        To: 'static,
        Error: 'static,
        M: TryMapper<From, To, Error> + 'static,
    {
        let type_id = TypeId::of::<(TypeId, TypeId, TypeId)>();
        let key = (TypeId::of::<From>(), TypeId::of::<To>(), TypeId::of::<Error>());
        self.mappers.insert(type_id, Box::new(mapper));
    }
    
    pub fn get<From, To>(&self) -> Option<&dyn Mapper<From, To>>
    where
        From: 'static,
        To: 'static,
    {
        let type_id = TypeId::of::<(TypeId, TypeId)>();
        let key = (TypeId::of::<From>(), TypeId::of::<To>());
        
        self.mappers.get(&type_id)
            .and_then(|boxed| boxed.downcast_ref::<dyn Mapper<From, To>>())
    }
    
    pub fn get_try<From, To, Error>(&self) -> Option<&dyn TryMapper<From, To, Error>>
    where
        From: 'static,
        To: 'static,
        Error: 'static,
    {
        let type_id = TypeId::of::<(TypeId, TypeId, TypeId)>();
        let key = (TypeId::of::<From>(), TypeId::of::<To>(), TypeId::of::<Error>());
        
        self.mappers.get(&type_id)
            .and_then(|boxed| boxed.downcast_ref::<dyn TryMapper<From, To, Error>>())
    }
}
```

### 5.5 结论与实践建议

关于映射实现的综合建议：

```rust
// 映射实践总结
pub struct MappingBestPractices;

impl MappingBestPractices {
    pub fn get_principles() -> Vec<(&'static str, &'static str)> {
        vec![
            ("单一职责原则", "每个映射类应该只负责一对类型之间的转换，保持映射逻辑清晰和可测试。"),
            ("明确边界", "在架构层次间定义清晰的数据传输对象，避免领域模型泄漏到外层。"),
            ("防腐层模式", "使用适配器隔离外部系统变化，保护核心领域模型不受外部影响。"),
            ("层次映射", "根据架构层次定义不同的映射策略，从领域到应用、存储和表示层各有侧重。"),
            ("验证与错误处理", "在映射过程中进行数据验证，提供清晰的错误信息和类型安全的结果。"),
            ("测试驱动", "用单元测试和属性测试验证映射行为，特别关注边界情况和双向转换。"),
            ("性能优化", "对关键路径进行性能优化，考虑缓存、懒加载和批处理等策略。"),
            ("可维护性", "选择适当的自动化工具减少样板代码，但保持逻辑透明和可调试。"),
        ]
    }
    
    pub fn decision_matrix() -> HashMap<&'static str, Vec<(&'static str, u8)>> {
        let mut matrix = HashMap::new();
        
        // 手动映射
        matrix.insert("手动映射", vec![
            ("控制精度", 5),
            ("性能优化", 5),
            ("调试简易性", 4),
            ("代码体积", 2),
            ("维护成本", 1),
            ("开发速度", 1),
        ]);
        
        // 宏生成映射
        matrix.insert("宏生成", vec![
            ("控制精度", 4),
            ("性能优化", 4),
            ("调试简易性", 2),
            ("代码体积", 3),
            ("维护成本", 3),
            ("开发速度", 4),
        ]);
        
        // 特征框架映射
        matrix.insert("特征框架", vec![
            ("控制精度", 3),
            ("性能优化", 3),
            ("调试简易性", 3),
            ("代码体积", 4),
            ("维护成本", 4),
            ("开发速度", 4),
        ]);
        
        // 代码生成工具
        matrix.insert("代码生成", vec![
            ("控制精度", 2),
            ("性能优化", 2),
            ("调试简易性", 1),
            ("代码体积", 5),
            ("维护成本", 5),
            ("开发速度", 5),
        ]);
        
        matrix
    }
    
    pub fn select_strategy_for_scenario(scenario: &MappingScenario) -> &'static str {
        match scenario {
            MappingScenario::SimpleDtoMapping => "宏生成或代码生成是效率最高的选择，因为这些映射通常是直接的字段对应。",
            MappingScenario::ComplexDomainMapping => "手动映射提供最好的控制性和明确性，对于复杂的领域逻辑转换至关重要。",
            MappingScenario::ExternalSystemIntegration => "使用特征框架结合防腐层模式，隔离外部系统变化，便于适配和测试。",
            MappingScenario::HighPerformanceMapping => "手动映射配合性能优化技术，如懒加载、批处理和缓存，针对热点路径定制。",
            MappingScenario::LargeScaleApplication => "结合特征框架和代码生成，对简单映射自动化，复杂映射手动实现，平衡效率和灵活性。",
            MappingScenario::RapidPrototyping => "代码生成工具可以快速建立映射骨架，适合原型验证阶段，后续可以逐步优化关键部分。",
        }
    }
    
    pub fn common_pitfalls() -> Vec<(&'static str, &'static str)> {
        vec![
            (
                "过度映射", 
                "不必要地在每层间创建不同的模型和映射，增加代码复杂性而没有带来实际价值。应该根据实际需求决定是否需要单独的模型。"
            ),
            (
                "忽略验证", 
                "在映射过程中没有执行适当的验证，导致无效数据传递到系统深处。应在边界处进行充分验证。"
            ),
            (
                "循环依赖", 
                "在对象图映射中创建循环引用，导致无限递归或内存泄漏。应该使用ID引用或限制递归深度解决。"
            ),
            (
                "性能问题", 
                "在映射过程中执行昂贵的操作，如数据库查询或网络请求，导致性能瓶颈。应该使用批量加载和装配器模式优化。"
            ),
            (
                "丢失异常", 
                "吞掉映射过程中的异常或使用默认值掩盖错误，导致排错困难。应该提供明确的错误处理和日志记录。"
            ),
            (
                "工具滥用", 
                "过度依赖自动映射工具而不理解底层实现，导致意外行为和难以调试的问题。应该理解工具的限制和实现机制。"
            ),
            (
                "一刀切思维", 
                "对所有类型的映射使用同一种方法，忽略不同场景的特殊需求。应该根据具体需求选择适当的映射策略。"
            ),
        ]
    }
    
    pub fn implementation_checklist() -> Vec<&'static str> {
        vec![
            "所有映射都有单元测试覆盖，包括边界情况",
            "映射逻辑与业务逻辑分离，避免在映射中执行业务操作",
            "双向映射已验证一致性和往返转换稳定性",
            "关键路径映射已进行性能优化和测试",
            "实现了合适的错误处理和验证逻辑",
            "映射代码可读性良好，有必要的文档说明",
            "考虑了版本兼容性和未来演化需求",
            "大型集合使用了高效的批量处理方式",
            "配置了监控和日志记录以便问题排查",
            "团队已就映射策略达成共识并形成规范",
        ]
    }
}

pub enum MappingScenario {
    SimpleDtoMapping,
    ComplexDomainMapping,
    ExternalSystemIntegration,
    HighPerformanceMapping,
    LargeScaleApplication,
    RapidPrototyping,
}

// 领域特定的映射策略实践
pub struct DomainSpecificMappingPractices;

impl DomainSpecificMappingPractices {
    pub fn financial_domain_practices() -> Vec<&'static str> {
        vec![
            "货币金额使用高精度数值类型，避免浮点数精度损失",
            "交易数据保持不可变性，确保审计跟踪完整",
            "实现严格的跨币种转换验证和汇率管理",
            "保存金额的币种信息，而不仅仅是数值",
            "实现特定的舍入策略，符合金融计算规则",
            "记录时间戳精确到毫秒并包含时区信息",
            "对敏感财务数据实施额外的验证和安全措施",
        ]
    }
    
    pub fn healthcare_domain_practices() -> Vec<&'static str> {
        vec![
            "实现对患者敏感数据的隐私保护和脱敏映射",
            "遵循医疗数据标准(如HL7, FHIR)的映射规范",
            "保持完整的数据来源和权限信息",
            "实现医疗编码系统(如ICD, CPT)的精确映射",
            "处理时间序列医疗数据的特殊需求",
            "支持多语言医疗术语的标准化映射",
            "满足监管合规性要求的数据转换和追踪",
        ]
    }
    
    pub fn ecommerce_domain_practices() -> Vec<&'static str> {
        vec![
            "产品目录信息的多级缓存和懒加载策略",
            "订单状态流转的安全映射和历史记录",
            "用户购物车的高频读写优化",
            "价格计算逻辑与显示格式的分离",
            "多货币和国际化支持的一致性处理",
            "促销规则和折扣计算的可追溯映射",
            "库存数量和可用性的实时映射",
        ]
    }
    
    pub fn iot_domain_practices() -> Vec<&'static str> {
        vec![
            "设备遥测数据的高效批量处理",
            "时间序列数据的压缩和聚合策略",
            "边缘计算和云端数据格式的转换",
            "设备状态更新的冲突解决策略",
            "处理间歇性连接和数据同步",
            "传感器数据的单位转换和标准化",
            "支持设备固件和协议版本差异",
        ]
    }
}

// 映射模式与反模式
pub struct MappingPatternsAndAntipatterns;

impl MappingPatternsAndAntipatterns {
    pub fn effective_patterns() -> HashMap<&'static str, &'static str> {
        let mut patterns = HashMap::new();
        
        patterns.insert("装配器模式", 
            "预先加载所有必要数据，然后在内存中进行组装，避免N+1查询问题。");
            
        patterns.insert("投影器模式", 
            "创建专门的视图模型，仅包含特定用例所需的字段，减少数据传输量。");
            
        patterns.insert("两步映射模式", 
            "将复杂映射分解为两个或多个简单映射步骤，提高可维护性和测试性。");
            
        patterns.insert("上下文感知映射", 
            "根据使用上下文调整映射策略，如详细视图vs列表视图。");
            
        patterns.insert("缓存结果模式", 
            "缓存频繁使用的映射结果，特别是计算成本高的转换。");
            
        patterns.insert("映射策略模式", 
            "在运行时选择不同的映射实现，适应不同的需求和优化路径。");
            
        patterns.insert("即时映射模式", 
            "仅在实际需要时执行映射，避免不必要的转换开销。");
            
        patterns.insert("版本化映射模式", 
            "支持不同版本的模型之间的映射，实现向前和向后兼容性。");
            
        patterns
    }
    
    pub fn antipatterns() -> HashMap<&'static str, &'static str> {
        let mut antipatterns = HashMap::new();
        
        antipatterns.insert("万能映射器", 
            "试图创建一个处理所有类型映射的通用解决方案，导致复杂性过高且难以维护。");
            
        antipatterns.insert("深度复制", 
            "无差别地复制所有字段和嵌套对象，包括不需要的数据，导致性能问题。");
            
        antipatterns.insert("映射中的业务逻辑", 
            "在映射过程中包含业务规则和决策逻辑，破坏了关注点分离原则。");
            
        antipatterns.insert("串联映射", 
            "创建长链的连续映射转换，而不考虑中间步骤的必要性和性能影响。");
            
        antipatterns.insert("无验证映射", 
            "映射过程中忽略数据验证，假设输入总是有效的，导致错误传播。");
            
        antipatterns.insert("影子复制", 
            "在不同层创建几乎相同的模型结构，增加了维护负担而没有实际价值。");
            
        antipatterns.insert("内联数据库查询", 
            "在映射过程中执行数据库查询或其他IO操作，导致性能问题和难以测试。");
            
        antipatterns
    }
    
    pub fn refactoring_strategies() -> HashMap<&'static str, Vec<&'static str>> {
        let mut strategies = HashMap::new();
        
        strategies.insert("从万能映射器到专用映射器", vec![
            "识别不同类型的映射需求并按功能分组",
            "为每组创建专门的映射器实现",
            "使用工厂模式或依赖注入管理这些专用映射器",
            "逐步迁移代码使用新的专用映射器",
        ]);
        
        strategies.insert("解决N+1查询问题", vec![
            "识别映射过程中的数据库查询",
            "重构为使用批量加载预取所有需要的数据",
            "创建装配器将预加载的数据组合到最终对象中",
            "添加性能测试验证改进",
        ]);
        
        strategies.insert("提取业务逻辑", vec![
            "识别映射中嵌入的业务规则",
            "将这些规则移动到专门的领域服务或策略类",
            "在映射之前或之后应用这些业务规则",
            "确保映射保持纯粹的数据转换职责",
        ]);
        
        strategies.insert("优化过度映射", vec![
            "审查项目中的所有模型类并识别相似结构",
            "合并不必要的中间模型",
            "为特定视图创建专门的投影，而不是通用转换",
            "使用部分映射仅转换必要的字段",
        ]);
        
        strategies
    }
}

// 最终实践指南与建议
pub fn mapping_implementation_guide() -> String {
    let principles = MappingBestPractices::get_principles();
    let decision_matrix = MappingBestPractices::decision_matrix();
    let pitfalls = MappingBestPractices::common_pitfalls();
    let checklist = MappingBestPractices::implementation_checklist();
    
    let patterns = MappingPatternsAndAntipatterns::effective_patterns();
    let antipatterns = MappingPatternsAndAntipatterns::antipatterns();
    
    let mut guide = String::new();
    
    guide.push_str("# 映射实现最佳实践指南\n\n");
    
    guide.push_str("## 核心原则\n\n");
    for (name, description) in principles {
        guide.push_str(&format!("- **{}**: {}\n", name, description));
    }
    
    guide.push_str("\n## 选择合适的映射策略\n\n");
    guide.push_str("根据不同场景选择合适的映射实现方式：\n\n");
    
    guide.push_str("| 场景 | 推荐策略 |\n");
    guide.push_str("|------|----------|\n");
    guide.push_str(&format!("| 简单DTO映射 | {} |\n", MappingBestPractices::select_strategy_for_scenario(&MappingScenario::SimpleDtoMapping)));
    guide.push_str(&format!("| 复杂领域映射 | {} |\n", MappingBestPractices::select_strategy_for_scenario(&MappingScenario::ComplexDomainMapping)));
    guide.push_str(&format!("| 外部系统集成 | {} |\n", MappingBestPractices::select_strategy_for_scenario(&MappingScenario::ExternalSystemIntegration)));
    guide.push_str(&format!("| 高性能要求 | {} |\n", MappingBestPractices::select_strategy_for_scenario(&MappingScenario::HighPerformanceMapping)));
    guide.push_str(&format!("| 大型应用 | {} |\n", MappingBestPractices::select_strategy_for_scenario(&MappingScenario::LargeScaleApplication)));
    guide.push_str(&format!("| 快速原型 | {} |\n", MappingBestPractices::select_strategy_for_scenario(&MappingScenario::RapidPrototyping)));
    
    guide.push_str("\n## 有效模式\n\n");
    for (name, description) in patterns {
        guide.push_str(&format!("- **{}**: {}\n", name, description));
    }
    
    guide.push_str("\n## 常见反模式（避免这些）\n\n");
    for (name, description) in antipatterns {
        guide.push_str(&format!("- **{}**: {}\n", name, description));
    }
    
    guide.push_str("\n## 避免的常见陷阱\n\n");
    for (name, description) in pitfalls {
        guide.push_str(&format!("- **{}**: {}\n", name, description));
    }
    
    guide.push_str("\n## 实现检查清单\n\n");
    for item in checklist {
        guide.push_str(&format!("- [ ] {}\n", item));
    }
    
    guide.push_str("\n## 实际案例建议\n\n");
    guide.push_str("### 从不同层次进行设计\n\n");
    guide.push_str("1. **领域层映射**：专注于保持领域概念的完整性和业务规则，使用值对象和实体的精确映射。\n");
    guide.push_str("2. **应用层映射**：关注用例和服务边界，创建适合特定应用场景的DTOs和装配器。\n");
    guide.push_str("3. **基础设施层映射**：处理技术细节，如数据库映射、序列化和外部系统集成的适配器。\n");
    guide.push_str("4. **表示层映射**：优化为UI需求，创建视图模型和投影，处理格式化和本地化。\n\n");
    
    guide.push_str("### 性能优化技巧\n\n");
    guide.push_str("1. 使用批量获取替代逐个查询，避免N+1问题\n");
    guide.push_str("2. 对热点路径实现缓存策略\n");
    guide.push_str("3. 考虑延迟加载不常用的大型集合或嵌套对象\n");
    guide.push_str("4. 使用投影只返回必要字段，减少数据传输量\n");
    guide.push_str("5. 对大型列表考虑分页映射\n\n");
    
    guide.push_str("### 测试策略建议\n\n");
    guide.push_str("1. 单元测试每个映射器，验证所有字段正确转换\n");
    guide.push_str("2. 使用属性测试验证映射不变量在随机输入下保持\n");
    guide.push_str("3. 特别测试边界情况：空值、最大值、特殊字符等\n");
    guide.push_str("4. 对双向映射执行往返测试，确保转换一致性\n");
    guide.push_str("5. 包含性能测试验证大量数据的映射效率\n\n");
    
    guide
}
```

## 总结

本文全面探讨了概念模型到实现代码的映射问题，从理论基础到实践策略，涵盖了不同层次和场景下的映射挑战与解决方案。
通过Rust语言示例，展示了类型系统如何有效地表达领域概念，以及映射过程中需要注意的各种细节与优化策略。

核心要点包括：

1. **映射原则与策略**：根据不同场景选择合适的映射实现方式，包括手动映射、宏生成、特征框架和代码生成工具。

2. **不同层次的映射处理**：在领域层、应用层、基础设施层和表示层，映射关注点各有不同，需要针对性处理。

3. **常见挑战的解决方案**：解决对象图遍历、副作用隔离、类型转换安全性、版本差异等常见问题。

4. **性能优化与测试策略**：通过批量加载、缓存、懒加载等技术优化映射性能，并通过全面的测试确保映射行为正确。

5. **领域特定实践**：根据不同业务领域（金融、医疗、电商、物联网等）调整映射策略，满足特定需求。

这些指导原则和最佳实践可以帮助开发者在设计映射时做出更明智的决策，实现概念模型到代码实现的高质量转换，
同时保持系统的灵活性、可测试性和性能。
