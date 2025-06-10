# Rust实现IOT工作流系统的全面设计与分析

## 目录

- [Rust实现IOT工作流系统的全面设计与分析](#rust实现iot工作流系统的全面设计与分析)
  - [目录](#目录)
  - [I. IOT领域概念与规范基础](#i-iot领域概念与规范基础)
    - [1. IOT领域概念模型](#1-iot领域概念模型)
    - [2. IOT行业规范整合](#2-iot行业规范整合)
      - [2.1 协议标准](#21-协议标准)
      - [2.2 行业标准](#22-行业标准)
  - [II. IOT工作流系统领域模型设计](#ii-iot工作流系统领域模型设计)
    - [1. 核心领域模型](#1-核心领域模型)
    - [2. IOT设备管理与集成](#2-iot设备管理与集成)
    - [3. 数字孪生与资产建模](#3-数字孪生与资产建模)
  - [III. IOT工作流系统架构设计](#iii-iot工作流系统架构设计)
    - [1. 分层架构设计](#1-分层架构设计)
    - [2. 组件间通信与集成](#2-组件间通信与集成)
    - [3. 设备数据持久化策略](#3-设备数据持久化策略)
    - [4. 边缘计算与云端协同](#4-边缘计算与云端协同)
    - [5. 安全与隐私设计](#5-安全与隐私设计)
  - [IV. IOT工作流系统设计模式与实现](#iv-iot工作流系统设计模式与实现)
    - [1. 设备状态管理与工作流集成](#1-设备状态管理与工作流集成)
    - [2. 设备命令处理工作流](#2-设备命令处理工作流)
    - [3. 遥测数据处理与异常检测](#3-遥测数据处理与异常检测)
    - [4. 固件更新工作流实现](#4-固件更新工作流实现)
  - [设备预更新准备流程设计](#设备预更新准备流程设计)
  - [设备预更新准备工作流](#设备预更新准备工作流)
  - [设备预更新准备功能实现](#设备预更新准备功能实现)
  - [工作流调用集成](#工作流调用集成)
  - [设备预更新准备工作流的好处](#设备预更新准备工作流的好处)
  - [设备更新状态跟踪机制](#设备更新状态跟踪机制)
  - [更新状态数据模型](#更新状态数据模型)
  - [更新状态管理服务](#更新状态管理服务)
  - [更新后验证流程](#更新后验证流程)
  - [更新后验证工作流定义](#更新后验证工作流定义)
  - [更新后验证功能实现](#更新后验证功能实现)
  - [固件回滚流程设计](#固件回滚流程设计)
  - [回滚请求和处理流程](#回滚请求和处理流程)
  - [回滚工作流功能实现](#回滚工作流功能实现)
  - [总结](#总结)
  - [1. 设备预更新准备流程](#1-设备预更新准备流程)
  - [2. 更新状态跟踪机制](#2-更新状态跟踪机制)
  - [3. 更新后验证流程](#3-更新后验证流程)
  - [4. 固件回滚流程](#4-固件回滚流程)
  - [关键设计特点](#关键设计特点)

## I. IOT领域概念与规范基础

### 1. IOT领域概念模型

IOT（物联网）系统通常包含以下核心概念：

```rust
/// 设备 - 表示物理IOT设备
pub struct Device {
    pub id: DeviceId,                              // 设备唯一标识符
    pub name: String,                              // 设备名称
    pub device_type: DeviceType,                   // 设备类型
    pub manufacturer: String,                      // 制造商
    pub model: String,                             // 型号
    pub firmware_version: SemanticVersion,         // 固件版本
    pub capabilities: HashSet<Capability>,         // 设备能力
    pub properties: HashMap<String, PropertyValue>,// 设备属性
    pub metadata: HashMap<String, Value>,          // 元数据
    pub status: DeviceStatus,                      // 设备状态
    pub created_at: DateTime<Utc>,                 // 创建时间
    pub last_connected_at: Option<DateTime<Utc>>,  // 最后连接时间
}

/// 设备连接类型
pub enum ConnectionType {
    DirectConnect,     // 直接连接
    Gateway { gateway_id: DeviceId }, // 通过网关连接
    LPWAN,             // 低功耗广域网
    Cellular,          // 蜂窝网络
    Ethernet,          // 以太网
    WiFi,              // WiFi
    Bluetooth,         // 蓝牙
    ZigBee,            // ZigBee
    Custom(String),    // 自定义连接类型
}

/// 消息 - 设备与系统间交换的数据
pub struct DeviceMessage {
    pub id: MessageId,                      // 消息ID
    pub device_id: DeviceId,                // 设备ID
    pub message_type: MessageType,          // 消息类型
    pub payload: Value,                     // 消息内容
    pub qos: QoSLevel,                      // 服务质量级别
    pub timestamp: DateTime<Utc>,           // 消息时间戳
    pub correlation_id: Option<String>,     // 关联ID
    pub metadata: HashMap<String, Value>,   // 元数据
}

/// 遥测数据 - 设备报告的测量数据
pub struct Telemetry {
    pub device_id: DeviceId,                   // 设备ID
    pub timestamp: DateTime<Utc>,              // 测量时间
    pub metrics: HashMap<String, MetricValue>, // 测量值
    pub sequence_number: u64,                  // 序列号
    pub location: Option<GeoLocation>,         // 地理位置
    pub quality: Option<DataQuality>,          // 数据质量
}

/// 命令 - 发送给设备的指令
pub struct DeviceCommand {
    pub id: CommandId,                     // 命令ID
    pub device_id: DeviceId,               // 目标设备ID
    pub command_type: String,              // 命令类型
    pub parameters: Value,                 // 命令参数
    pub timeout: Duration,                 // 超时时间
    pub priority: CommandPriority,         // 优先级
    pub created_at: DateTime<Utc>,         // 创建时间
    pub status: CommandStatus,             // 命令状态
    pub response: Option<CommandResponse>, // 命令响应
}

/// 资产 - 表示与设备相关的业务实体
pub struct Asset {
    pub id: AssetId,                              // 资产ID 
    pub name: String,                             // 资产名称
    pub asset_type: String,                       // 资产类型
    pub devices: Vec<DeviceId>,                   // 相关设备
    pub parent_asset_id: Option<AssetId>,         // 父资产ID
    pub location: Option<GeoLocation>,            // 地理位置
    pub properties: HashMap<String, PropertyValue>,// 资产属性
    pub metadata: HashMap<String, Value>,         // 元数据
}
```

### 2. IOT行业规范整合

#### 2.1 协议标准

```rust
/// 支持的IOT协议
pub enum IotProtocol {
    MQTT(MqttVersion),         // MQTT协议
    CoAP(CoAPVersion),         // CoAP协议
    AMQP(AMQPVersion),         // AMQP协议
    HTTP(HttpVersion),         // HTTP/HTTPS
    WebSocket(WsVersion),      // WebSocket
    DDS(DDSVersion),           // 数据分发服务
    OPC_UA(OpcUaVersion),      // OPC统一架构
    LWM2M(Lwm2mVersion),       // 轻量级M2M
    Custom(String),            // 自定义协议
}

/// MQTT协议版本
pub enum MqttVersion {
    V3_1_1,                    // MQTT 3.1.1
    V5_0,                      // MQTT 5.0
}
```

#### 2.2 行业标准

```rust
/// IOT行业标准
pub enum IndustryStandard {
    ISO27001,                 // 安全管理标准
    IEC62443,                 // 工业自动化安全
    NISTIR8259,               // IOT设备安全基线
    ETSI303645,               // 消费级IOT安全
    OCFR,                     // 开放连接基金会规范
    OCF,                      // 开放连接基金会
    Thread,                   // Thread网络标准
    ODVA,                     // 开放DeviceNet供应商协会
    WoT,                      // Web of Things (W3C)
}

/// 数据模型标准
pub enum DataModelStandard {
    DTDL,                     // 数字孪生定义语言 (Microsoft)
    OMA,                      // 开放移动联盟
    IPSO,                     // IP智能对象
    OneM2M,                   // oneM2M规范
    OCF,                      // 开放连接基金会数据模型
    W3C_WoT_TD,               // W3C WoT Thing Description
    Custom(String),           // 自定义数据模型
}
```

## II. IOT工作流系统领域模型设计

### 1. 核心领域模型

```rust
/// IOT工作流领域模型
pub mod iot_workflow_domain {
    /// 设备工作流 - 管理设备生命周期的工作流
    pub struct DeviceWorkflow {
        pub id: WorkflowId,
        pub name: String,
        pub device_type: DeviceType,
        pub triggers: Vec<WorkflowTrigger>,
        pub steps: Vec<WorkflowStep>,
        pub conditions: Vec<WorkflowCondition>,
        pub version: SemanticVersion,
        pub status: WorkflowStatus,
    }
    
    /// 工作流触发器
    pub enum WorkflowTrigger {
        DeviceEvent {                      // 设备事件触发
            event_type: String,
            filter: Option<DeviceFilter>,
        },
        Telemetry {                        // 遥测数据触发
            metric_name: String,
            condition: TelemetryCondition,
        },
        Schedule {                         // 定时触发
            schedule: CronExpression,
            timezone: String,
        },
        CommandResponse {                  // 命令响应触发
            command_type: String,
            status: CommandStatus,
        },
        ExternalSystem {                   // 外部系统触发
            system_id: String,
            event_type: String,
        },
        Manual {                           // 手动触发
            roles: Vec<String>,
        },
        DeviceState {                      // 设备状态变化触发
            from_state: Option<DeviceStatus>,
            to_state: DeviceStatus,
        },
    }
    
    /// 工作流步骤
    pub enum WorkflowStep {
        DeviceCommand {                    // 发送设备命令
            id: String,
            command_type: String,
            parameters_template: String,
            timeout: Duration,
            retry_policy: RetryPolicy,
        },
        DataTransformation {               // 数据转换
            id: String,
            transformer_type: String,
            input_mapping: HashMap<String, String>,
            output_mapping: HashMap<String, String>,
        },
        EnrichmentLookup {                 // 数据丰富化
            id: String,
            source: DataSource,
            lookup_key: String,
            output_mapping: HashMap<String, String>,
        },
        Notification {                     // 发送通知
            id: String,
            notification_type: String,
            recipients: Vec<String>,
            template: String,
            priority: NotificationPriority,
        },
        Integration {                      // 外部系统集成
            id: String,
            system_id: String,
            operation: String,
            input_mapping: HashMap<String, String>,
            output_mapping: HashMap<String, String>,
        },
        Gateway {                          // 决策网关
            id: String,
            gateway_type: GatewayType,
            conditions: Vec<WorkflowCondition>,
        },
        SubWorkflow {                      // 子工作流
            id: String,
            workflow_id: WorkflowId,
            input_mapping: HashMap<String, String>,
            output_mapping: HashMap<String, String>,
        },
        StateTransition {                  // 状态转换
            id: String,
            target_state: String,
            validation: Option<String>,
        },
        DigitalTwin {                      // 数字孪生操作
            id: String,
            twin_id: String,
            operation: TwinOperation,
            property_mapping: HashMap<String, String>,
        },
    }
    
    /// 工作流条件
    pub enum WorkflowCondition {
        DeviceProperty {                  // 设备属性条件
            property_name: String,
            operator: Operator,
            value: Value,
        },
        TelemetryThreshold {              // 遥测阈值条件
            metric_name: String,
            operator: Operator,
            threshold: f64,
            window: Option<Duration>,
        },
        TimeWindow {                      // 时间窗口条件
            start_time: TimeExpression,
            end_time: TimeExpression,
        },
        DeviceState {                     // 设备状态条件
            expected_state: DeviceStatus,
        },
        LogicalExpression {               // 逻辑表达式条件
            operator: LogicalOperator,
            operands: Vec<WorkflowCondition>,
        },
        CustomExpression {                // 自定义表达式条件
            expression: String,
        },
    }
    
    /// 工作流执行上下文
    pub struct WorkflowContext {
        pub workflow_id: WorkflowId,
        pub instance_id: String,
        pub device_id: Option<DeviceId>,
        pub asset_id: Option<AssetId>,
        pub trigger_event: Value,
        pub variables: HashMap<String, Value>,
        pub telemetry_cache: HashMap<String, Vec<MetricValue>>,
        pub execution_path: Vec<String>,
        pub started_at: DateTime<Utc>,
        pub step_results: HashMap<String, StepResult>,
        pub tags: HashMap<String, String>,
    }
}
```

### 2. IOT设备管理与集成

```rust
/// 设备注册与生命周期管理
pub mod device_management {
    /// 设备配置
    pub struct DeviceConfiguration {
        pub device_id: DeviceId,
        pub configuration_type: String,
        pub content: Value,
        pub version: u64,
        pub applied_at: Option<DateTime<Utc>>,
        pub status: ConfigurationStatus,
    }
    
    /// 设备生命周期事件
    pub enum DeviceLifecycleEvent {
        Provisioned {                          // 设备预配
            device_id: DeviceId,
            credentials: DeviceCredentials,
        },
        Registered {                           // 设备注册
            device_id: DeviceId,
            registration_info: RegistrationInfo,
        },
        Connected {                            // 设备连接
            device_id: DeviceId,
            connection_info: ConnectionInfo,
        },
        Disconnected {                         // 设备断开
            device_id: DeviceId,
            reason: DisconnectReason,
        },
        ConfigurationUpdated {                 // 配置更新
            device_id: DeviceId,
            configuration_type: String,
            version: u64,
        },
        FirmwareUpdateStarted {                // 固件更新开始
            device_id: DeviceId,
            firmware_version: SemanticVersion,
        },
        FirmwareUpdateCompleted {              // 固件更新完成
            device_id: DeviceId,
            firmware_version: SemanticVersion,
            status: UpdateStatus,
        },
        StatusChanged {                        // 状态变更
            device_id: DeviceId,
            previous_status: DeviceStatus,
            new_status: DeviceStatus,
        },
        Decommissioned {                       // 设备解除
            device_id: DeviceId,
            reason: String,
        },
    }
    
    /// 设备认证策略
    pub enum AuthenticationStrategy {
        SymmetricKey {                        // 对称密钥
            primary_key: SecretString,
            secondary_key: Option<SecretString>,
        },
        X509Certificate {                     // X.509证书
            thumbprint: String,
            certificate_info: CertificateInfo,
        },
        SASToken {                            // SAS令牌
            token_provider: String,
            expiry: DateTime<Utc>,
        },
        OAuth2 {                              // OAuth2
            client_id: String,
            scope: String,
            auth_server: String,
        },
    }
}
```

### 3. 数字孪生与资产建模

```rust
/// 数字孪生模型
pub mod digital_twin {
    /// 数字孪生
    pub struct DigitalTwin {
        pub id: TwinId,
        pub entity_id: String,
        pub entity_type: EntityType,
        pub model_id: ModelId,
        pub properties: HashMap<String, PropertyValue>,
        pub relationships: Vec<TwinRelationship>,
        pub components: HashMap<String, ComponentInstance>,
        pub history: VecDeque<TwinHistoryEntry>,
        pub metadata: HashMap<String, Value>,
    }
    
    /// 孪生关系
    pub struct TwinRelationship {
        pub name: String,
        pub target_twin_id: TwinId,
        pub properties: HashMap<String, Value>,
    }
    
    /// 数字孪生模型
    pub struct TwinModel {
        pub id: ModelId,
        pub namespace: String,
        pub name: String,
        pub version: SemanticVersion,
        pub description: Option<String>,
        pub base_model_ids: Vec<ModelId>,
        pub properties: Vec<PropertyDefinition>,
        pub relationships: Vec<RelationshipDefinition>,
        pub components: Vec<ComponentDefinition>,
    }
    
    /// 属性定义
    pub struct PropertyDefinition {
        pub name: String,
        pub schema_type: SchemaType,
        pub writable: bool,
        pub unit: Option<String>,
        pub description: Option<String>,
        pub default_value: Option<Value>,
        pub constraints: Vec<PropertyConstraint>,
    }
    
    /// 孪生操作
    pub enum TwinOperation {
        ReadProperty {                      // 读取属性
            property_path: String,
        },
        WriteProperty {                     // 写入属性
            property_path: String,
            value_expression: String,
        },
        InvokeCommand {                     // 调用命令
            command_name: String,
            parameters: Value,
        },
        AddRelationship {                   // 添加关系
            relationship_name: String,
            target_twin_id: String,
            properties: HashMap<String, String>,
        },
        RemoveRelationship {                // 移除关系
            relationship_name: String,
            target_twin_id: String,
        },
        QueryTwins {                        // 查询孪生
            query: String,
            result_mapping: String,
        },
    }
}
```

## III. IOT工作流系统架构设计

### 1. 分层架构设计

```text
┌───────────────────────────────────────────────────────────────┐
│                      设备与集成层 (Device & Integration)        │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────────────┐  │
│  │ 设备连接管理  │  │ 协议适配器   │  │ 边缘集成             │  │
│  └──────────────┘  └──────────────┘  └──────────────────────┘  │
├───────────────────────────────────────────────────────────────┤
│                      核心服务层 (Core Services)                │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────────────┐  │
│  │ 设备注册管理  │  │ 数字孪生服务 │  │ 遥测处理引擎         │  │
│  └──────────────┘  └──────────────┘  └──────────────────────┘  │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────────────┐  │
│  │ 命令处理服务  │  │ 规则引擎     │  │ 事件处理服务         │  │
│  └──────────────┘  └──────────────┘  └──────────────────────┘  │
├───────────────────────────────────────────────────────────────┤
│                      工作流引擎层 (Workflow Engine)            │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────────────┐  │
│  │ 工作流定义器  │  │ 工作流执行器 │  │ 工作流调度器         │  │
│  └──────────────┘  └──────────────┘  └──────────────────────┘  │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────────────┐  │
│  │ 活动处理器   │  │ 状态管理器   │  │ 错误处理与恢复        │  │
│  └──────────────┘  └──────────────┘  └──────────────────────┘  │
├───────────────────────────────────────────────────────────────┤
│                      集成与应用层 (Integration & Applications) │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────────────┐  │
│  │ 业务系统集成  │  │ 分析与报表   │  │ 应用API              │  │
│  └──────────────┘  └──────────────┘  └──────────────────────┘  │
├───────────────────────────────────────────────────────────────┤
│                      基础设施层 (Infrastructure)               │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────────────┐  │
│  │ 消息总线     │  │ 事件存储     │  │ 分布式缓存           │  │
│  └──────────────┘  └──────────────┘  └──────────────────────┘  │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────────────┐  │
│  │ 安全服务     │  │ 监控与遥测   │  │ 分布式锁             │  │
│  └──────────────┘  └──────────────┘  └──────────────────────┘  │
└───────────────────────────────────────────────────────────────┘
```

### 2. 组件间通信与集成

```rust
/// 设备和工作流引擎的集成
pub struct IotWorkflowIntegration {
    /// 设备连接管理器
    device_connection_manager: Arc<dyn DeviceConnectionManager>,
    
    /// 工作流引擎
    workflow_engine: Arc<HighPerformanceWorkflowEngine>,
    
    /// 数字孪生服务
    digital_twin_service: Arc<dyn DigitalTwinService>,
    
    /// 遥测处理引擎
    telemetry_processor: Arc<dyn TelemetryProcessor>,
    
    /// 消息总线
    message_bus: Arc<dyn HighPerformanceEventBus>,
}

impl IotWorkflowIntegration {
    /// 初始化IOT工作流集成
    pub async fn initialize(&self) -> Result<(), Error> {
        // 注册设备事件处理器
        self.register_device_event_handlers().await?;
        
        // 注册遥测事件处理器
        self.register_telemetry_handlers().await?;
        
        // 注册命令响应处理器
        self.register_command_response_handlers().await?;
        
        // 注册数字孪生事件处理器
        self.register_digital_twin_handlers().await?;
        
        Ok(())
    }
    
    /// 注册设备事件处理器
    async fn register_device_event_handlers(&self) -> Result<(), Error> {
        // 监听设备连接事件
        self.message_bus.subscribe("device.events.connected", Box::new(|event| {
            let engine = self.workflow_engine.clone();
            
            async move {
                // 提取设备信息
                let device_id = event.metadata.get("device_id")
                    .and_then(|v| v.as_str())
                    .ok_or_else(|| Error::InvalidData("缺少device_id".into()))?;
                
                // 触发设备连接工作流
                self.trigger_device_lifecycle_workflow(
                    device_id, 
                    "device_connected",
                    event.data.clone()
                ).await?;
                
                Ok(())
            }
        })).await?;
        
        // 监听设备断开连接事件
        // ... 其他设备事件处理器
        
        Ok(())
    }
    
    /// 触发设备生命周期工作流
    async fn trigger_device_lifecycle_workflow(
        &self,
        device_id: &str,
        event_type: &str,
        event_data: Value,
    ) -> Result<(), Error> {
        // 查找匹配的工作流定义
        let matching_workflows = self.find_matching_device_workflows(
            device_id, 
            event_type
        ).await?;
        
        for workflow_def in matching_workflows {
            // 为每个匹配的工作流创建输入数据
            let input_data = json!({
                "device_id": device_id,
                "event_type": event_type,
                "event_data": event_data,
                "timestamp": Utc::now(),
            });
            
            // 启动工作流实例
            let options = StartWorkflowOptions {
                workflow_id: None,
                created_by: Some("system".to_string()),
                metadata: Some(json!({
                    "source": "device_event",
                    "device_id": device_id,
                    "event_type": event_type,
                })),
                priority: Some(self.determine_priority(event_type)),
                execution_deadline: None,
            };
            
            self.workflow_engine.start_workflow(
                &workflow_def.id, 
                input_data, 
                options
            ).await?;
        }
        
        Ok(())
    }
    
    /// 确定工作流优先级
    fn determine_priority(&self, event_type: &str) -> ExecutionPriority {
        match event_type {
            // 关键事件使用高优先级
            "device_alert" | "security_event" | "error_critical" => ExecutionPriority::High,
            
            // 普通操作事件使用正常优先级
            "device_connected" | "device_disconnected" | "configuration_changed" => ExecutionPriority::Normal,
            
            // 低重要性事件使用低优先级
            "periodic_report" | "debug_info" => ExecutionPriority::Low,
            
            // 默认使用正常优先级
            _ => ExecutionPriority::Normal,
        }
    }
}
```

### 3. 设备数据持久化策略

```rust
/// IOT数据持久化策略
pub struct IotDataPersistenceStrategy {
    // 热数据存储 - 时间序列数据库(例如 TimescaleDB, InfluxDB)
    hot_storage: Arc<dyn TimeSeriesStorage>,
    
    // 温数据存储 - 结构化数据库(例如 PostgreSQL)
    warm_storage: Arc<dyn RelationalStorage>,
    
    // 冷数据存储 - 对象存储(例如 S3, MinIO)
    cold_storage: Arc<dyn ObjectStorage>,
    
    // 事件存储 - 用于工作流状态和审计
    event_store: Arc<dyn EventStore>,
    
    // 分布式缓存 - 用于频繁访问的数据
    distributed_cache: Arc<dyn DistributedCache>,
    
    // 数据生命周期策略
    lifecycle_policies: HashMap<DataCategory, LifecyclePolicy>,
    
    // 数据保留策略
    retention_policies: HashMap<DataCategory, RetentionPolicy>,
}

impl IotDataPersistenceStrategy {
    /// 存储遥测数据
    pub async fn store_telemetry(&self, telemetry: &Telemetry) -> Result<(), Error> {
        // 1. 存储到热存储进行实时分析
        self.hot_storage.insert_telemetry(telemetry).await?;
        
        // 2. 更新设备最新状态到分布式缓存
        self.update_device_latest_state(telemetry).await?;
        
        // 3. 检查数据生命周期策略
        self.apply_lifecycle_policy(DataCategory::Telemetry, telemetry.device_id.clone()).await?;
        
        Ok(())
    }
    
    /// 应用数据生命周期策略
    async fn apply_lifecycle_policy(&self, category: DataCategory, device_id: DeviceId) -> Result<(), Error> {
        if let Some(policy) = self.lifecycle_policies.get(&category) {
            match policy {
                LifecyclePolicy::TimeBasedMigration { hot_period, warm_period, archive_period } => {
                    // 热存储到温存储的迁移
                    let hot_threshold = Utc::now() - *hot_period;
                    self.migrate_data(
                        &device_id,
                        category,
                        StorageTier::Hot,
                        StorageTier::Warm,
                        hot_threshold
                    ).await?;
                    
                    // 温存储到冷存储的迁移
                    let warm_threshold = Utc::now() - *warm_period;
                    self.migrate_data(
                        &device_id,
                        category,
                        StorageTier::Warm,
                        StorageTier::Cold,
                        warm_threshold
                    ).await?;
                    
                    // 应用保留策略
                    if let Some(retention) = self.retention_policies.get(&category) {
                        match retention {
                            RetentionPolicy::Delete { after_period } => {
                                let delete_threshold = Utc::now() - *after_period;
                                self.delete_old_data(&device_id, category, delete_threshold).await?;
                            },
                            // 其他保留策略...
                        }
                    }
                },
                // 其他生命周期策略...
            }
        }
        
        Ok(())
    }
}

/// 数据分类
pub enum DataCategory {
    Telemetry,           // 遥测数据
    Events,              // 事件数据
    Commands,            // 命令数据
    State,               // 状态数据
    Configuration,       // 配置数据
    Diagnostics,         // 诊断数据
}

/// 存储层级
pub enum StorageTier {
    Hot,                 // 热存储(高性能，高成本)
    Warm,                // 温存储(中等性能和成本)
    Cold,                // 冷存储(低性能，低成本)
}

/// 生命周期策略
pub enum LifecyclePolicy {
    TimeBasedMigration {  // 基于时间的数据迁移
        hot_period: Duration,
        warm_period: Duration,
        archive_period: Duration,
    },
    AccessBasedMigration { // 基于访问频率的数据迁移
        access_threshold: u64,
        check_period: Duration,
    },
    VolumeBasedTiering {   // 基于数据量的分层
        hot_storage_limit: u64,
        warm_storage_limit: u64,
    },
}

///
# Rust实现IOT工作流系统的全面设计与分析（续）

## III. IOT工作流系统架构设计（续）

### 3. 设备数据持久化策略（续）

```rust
/// 保留策略
pub enum RetentionPolicy {
    Delete {                 // 删除策略
        after_period: Duration,
    },
    Aggregate {              // 聚合策略
        aggregation_rules: Vec<AggregationRule>,
        delete_raw_after: Duration,
    },
    Compress {               // 压缩策略
        compression_algorithm: CompressionAlgorithm,
        after_period: Duration,
    },
    LegalHold {              // 法律保留
        hold_period: Duration,
        compliance_type: ComplianceType,
    },
}

/// 聚合规则
pub struct AggregationRule {
    pub time_window: Duration,       // 聚合时间窗口
    pub aggregation_functions: Vec<AggregationFunction>,  // 聚合函数
    pub metrics: Option<Vec<String>>,  // 要聚合的指标(None表示全部)
}

/// 聚合函数
pub enum AggregationFunction {
    Min,
    Max,
    Avg,
    Sum,
    Count,
    Percentile(f64),
    StandardDeviation,
    Custom(String),
}

/// 压缩算法
pub enum CompressionAlgorithm {
    Gzip(CompressionLevel),
    Snappy,
    Lz4,
    Zstd(CompressionLevel),
    Delta,
    RLE,
    Custom(String),
}
```

### 4. 边缘计算与云端协同

```rust
/// 边缘计算架构
pub mod edge_computing {
    /// 边缘节点
    pub struct EdgeNode {
        pub id: EdgeNodeId,
        pub name: String,
        pub status: EdgeNodeStatus,
        pub capabilities: EdgeCapabilities,
        pub connected_devices: Vec<DeviceId>,
        pub deployed_modules: HashMap<String, EdgeModuleStatus>,
        pub resources: EdgeResources,
        pub network_info: NetworkInfo,
        pub location: Option<GeoLocation>,
    }
    
    /// 边缘工作流引擎
    pub struct EdgeWorkflowEngine {
        /// 本地工作流定义存储
        local_workflow_repository: EdgeWorkflowRepository,
        
        /// 限制版工作流执行器
        workflow_executor: LimitedWorkflowExecutor,
        
        /// 遥测预处理器
        telemetry_preprocessor: TelemetryPreprocessor,
        
        /// 本地规则引擎
        local_rule_engine: EdgeRuleEngine,
        
        /// 边云同步管理器
        sync_manager: EdgeCloudSyncManager,
        
        /// 边缘安全模块
        security_manager: EdgeSecurityManager,
    }
    
    /// 边云协同策略
    pub enum EdgeCloudCollaborationStrategy {
        /// 离线优先 - 边缘节点优先本地处理
        OfflineFirst {
            sync_interval: Duration,
            max_offline_period: Duration,
        },
        
        /// 云端优先 - 优先将数据发送到云端处理
        CloudFirst {
            local_buffer_size: usize,
            retry_strategy: RetryStrategy,
        },
        
        /// 自适应策略 - 根据网络状况和负载动态调整
        Adaptive {
            network_quality_threshold: f64,
            load_threshold: f64,
            decision_rules: Vec<AdaptiveRule>,
        },
        
        /// 分流策略 - 明确定义哪些工作流在边缘执行，哪些在云端执行
        Partitioned {
            edge_workflows: Vec<String>,
            cloud_workflows: Vec<String>,
            hybrid_workflows: Vec<HybridWorkflowConfig>,
        },
    }
    
    /// 混合工作流配置
    pub struct HybridWorkflowConfig {
        pub workflow_id: String,
        pub edge_steps: Vec<String>,
        pub cloud_steps: Vec<String>,
        pub decision_points: Vec<HybridDecisionPoint>,
    }
    
    /// 混合决策点
    pub struct HybridDecisionPoint {
        pub step_id: String,
        pub decision_logic: String,
        pub fallback_location: ExecutionLocation,
    }
    
    /// 边缘云同步管理器
    pub struct EdgeCloudSyncManager {
        pub node_id: EdgeNodeId,
        pub cloud_endpoint: String,
        pub sync_strategy: SyncStrategy,
        pub connection_manager: EdgeConnectionManager,
        pub data_buffer: CircularBuffer<SyncItem>,
        pub last_sync_status: SyncStatus,
    }
    
    impl EdgeCloudSyncManager {
        /// 同步遥测数据
        pub async fn sync_telemetry(&mut self, data: &[Telemetry]) -> Result<SyncResult, Error> {
            // 1. 应用压缩和批处理
            let compressed_batch = self.compress_telemetry_batch(data)?;
            
            // 2. 根据网络状态决定同步策略
            let network_status = self.connection_manager.get_network_status().await?;
            
            match network_status.connectivity {
                Connectivity::Connected => {
                    // 有网络连接，尝试立即同步
                    match self.connection_manager.send_data(
                        "telemetry", 
                        &compressed_batch,
                        QoSLevel::AtLeastOnce
                    ).await {
                        Ok(_) => {
                            // 同步成功，清除已确认的数据
                            self.last_sync_status = SyncStatus::success(Utc::now());
                            Ok(SyncResult::Synced { count: data.len() })
                        },
                        Err(e) => {
                            // 同步失败，缓存数据
                            log::warn!("同步遥测数据失败: {}, 将缓存数据", e);
                            self.buffer_data(SyncItemType::Telemetry, compressed_batch)?;
                            self.last_sync_status = SyncStatus::failed(Utc::now(), e.to_string());
                            Ok(SyncResult::Buffered { count: data.len() })
                        }
                    }
                },
                Connectivity::Disconnected | Connectivity::Unstable => {
                    // 无网络连接或不稳定，缓存数据
                    log::info!("网络连接不可用，缓存遥测数据");
                    self.buffer_data(SyncItemType::Telemetry, compressed_batch)?;
                    self.last_sync_status = SyncStatus::pending(Utc::now());
                    Ok(SyncResult::Buffered { count: data.len() })
                }
            }
        }
        
        /// 同步工作流结果
        pub async fn sync_workflow_results(&mut self, results: &[EdgeWorkflowResult]) -> Result<SyncResult, Error> {
            // 类似遥测同步的处理逻辑...
            Ok(SyncResult::Synced { count: results.len() })
        }
        
        /// 启动后台同步任务
        pub fn start_background_sync(&self) -> JoinHandle<()> {
            let sync_manager = self.clone();
            
            tokio::spawn(async move {
                let mut interval = tokio::time::interval(sync_manager.sync_strategy.interval);
                
                loop {
                    interval.tick().await;
                    
                    // 尝试同步缓冲区中的数据
                    if let Err(e) = sync_manager.try_sync_buffered_data().await {
                        log::error!("同步缓冲数据失败: {}", e);
                    }
                    
                    // 尝试同步工作流状态
                    if let Err(e) = sync_manager.sync_workflow_states().await {
                        log::error!("同步工作流状态失败: {}", e);
                    }
                    
                    // 尝试同步配置和定义
                    if let Err(e) = sync_manager.sync_configurations().await {
                        log::error!("同步配置失败: {}", e);
                    }
                }
            })
        }
    }
}
```

### 5. 安全与隐私设计

```rust
/// IOT工作流安全架构
pub mod security {
    /// 设备安全管理器
    pub struct DeviceSecurityManager {
        pub certificate_manager: CertificateManager,
        pub key_management_service: Arc<dyn KeyManagementService>,
        pub auth_service: Arc<dyn DeviceAuthService>,
        pub policy_enforcer: Arc<dyn SecurityPolicyEnforcer>,
        pub anomaly_detector: Arc<dyn AnomalyDetector>,
    }
    
    /// 工作流安全策略
    pub struct WorkflowSecurityPolicy {
        pub id: String,
        pub name: String,
        pub description: Option<String>,
        pub permissions: Vec<WorkflowPermission>,
        pub data_access_controls: Vec<DataAccessControl>,
        pub command_restrictions: Vec<CommandRestriction>,
        pub audit_requirements: AuditRequirements,
    }
    
    /// 工作流权限
    pub struct WorkflowPermission {
        pub action: WorkflowAction,
        pub resource_type: WorkflowResourceType,
        pub resource_id_pattern: String,
        pub conditions: Option<PermissionCondition>,
    }
    
    /// 数据访问控制
    pub struct DataAccessControl {
        pub data_category: DataCategory,
        pub access_level: AccessLevel,
        pub field_restrictions: Option<FieldLevelSecurity>,
        pub retention_requirement: Option<RetentionRequirement>,
    }
    
    /// 字段级安全
    pub struct FieldLevelSecurity {
        pub included_fields: Option<Vec<String>>,
        pub excluded_fields: Option<Vec<String>>,
        pub masking_rules: Vec<DataMaskingRule>,
        pub encryption_rules: Vec<FieldEncryptionRule>,
    }
    
    /// 数据掩码规则
    pub struct DataMaskingRule {
        pub field_pattern: String,
        pub masking_type: MaskingType,
        pub exemption_roles: Vec<String>,
    }
    
    /// 掩码类型
    pub enum MaskingType {
        FullMask,                // 完全掩码
        PartialMask { show_last: usize }, // 部分掩码(显示最后n个字符)
        HashValue,               // 哈希值
        Tokenize,                // 令牌化
        Redact,                  // 编辑
    }
    
    /// 设备命令限制
    pub struct CommandRestriction {
        pub command_type: String,
        pub allowed_parameters: Option<Vec<String>>,
        pub parameter_constraints: HashMap<String, ParameterConstraint>,
        pub approval_required: bool,
        pub rate_limit: Option<RateLimit>,
    }
    
    /// 审计需求
    pub struct AuditRequirements {
        pub audit_level: AuditLevel,
        pub required_events: Vec<String>,
        pub retention_period: Duration,
        pub data_sovereignty: Option<DataSovereignty>,
    }
    
    /// 审计级别
    pub enum AuditLevel {
        None,       // 无审计
        Basic,      // 基本审计
        Standard,   // 标准审计
        Detailed,   // 详细审计
        Forensic,   // 取证级审计
    }
    
    /// 安全事件处理工作流
    pub struct SecurityEventHandler {
        pub event_categorizer: SecurityEventCategorizer,
        pub risk_assessor: RiskAssessor,
        pub response_orchestrator: ResponseOrchestrator,
        pub notification_dispatcher: NotificationDispatcher,
    }
    
    impl SecurityEventHandler {
        /// 处理安全事件
        pub async fn handle_security_event(&self, event: SecurityEvent) -> Result<SecurityResponse, Error> {
            // 1. 对事件进行分类
            let category = self.event_categorizer.categorize(&event).await?;
            
            // 2. 评估风险级别
            let risk_assessment = self.risk_assessor.assess_risk(&event, &category).await?;
            
            // 3. 记录安全事件
            self.log_security_event(&event, &category, &risk_assessment).await?;
            
            // 4. 根据风险级别确定响应策略
            let response_actions = match risk_assessment.risk_level {
                RiskLevel::Critical | RiskLevel::High => {
                    // 高风险: 触发紧急响应工作流
                    self.response_orchestrator.orchestrate_critical_response(&event, &risk_assessment).await?
                },
                RiskLevel::Medium => {
                    // 中等风险: 采取标准响应措施
                    self.response_orchestrator.orchestrate_standard_response(&event, &risk_assessment).await?
                },
                RiskLevel::Low => {
                    // 低风险: 仅记录和监控
                    self.response_orchestrator.orchestrate_monitoring_response(&event, &risk_assessment).await?
                },
            };
            
            // 5. 发送通知
            if risk_assessment.risk_level >= RiskLevel::Medium {
                self.notification_dispatcher.dispatch_security_notification(
                    &event,
                    &risk_assessment,
                    &response_actions
                ).await?;
            }
            
            // 6. 返回响应结果
            Ok(SecurityResponse {
                event_id: event.id,
                category,
                risk_assessment,
                response_actions,
                timestamp: Utc::now(),
            })
        }
    }
}
```

## IV. IOT工作流系统设计模式与实现

### 1. 设备状态管理与工作流集成

```rust
/// 设备状态管理
pub struct DeviceStateManager {
    /// 设备状态存储
    state_store: Arc<dyn DeviceStateStore>,
    
    /// 状态变更处理器
    state_change_handlers: Vec<Box<dyn StateChangeHandler>>,
    
    /// 工作流引擎
    workflow_engine: Arc<HighPerformanceWorkflowEngine>,
    
    /// 数字孪生服务
    digital_twin_service: Arc<dyn DigitalTwinService>,
    
    /// 状态更新节流设置
    throttle_settings: HashMap<DeviceType, ThrottleSettings>,
}

impl DeviceStateManager {
    /// 更新设备状态
    pub async fn update_device_state(
        &self,
        device_id: &DeviceId,
        property_updates: HashMap<String, PropertyValue>,
        source: StateUpdateSource,
    ) -> Result<StateUpdateResult, Error> {
        // 1. 获取当前设备状态
        let current_state = self.state_store.get_device_state(device_id).await?;
        
        // 2. 应用节流策略
        let throttled_updates = self.apply_throttling(
            device_id,
            &current_state,
            property_updates,
        )?;
        
        if throttled_updates.is_empty() {
            return Ok(StateUpdateResult {
                device_id: device_id.clone(),
                applied_updates: HashMap::new(),
                throttled_updates: 0,
                version: current_state.version,
                timestamp: Utc::now(),
            });
        }
        
        // 3. 构建新状态
        let mut new_state = current_state.clone();
        new_state.properties.extend(throttled_updates.clone());
        new_state.last_updated = Utc::now();
        new_state.version += 1;
        new_state.update_source = source;
        
        // 4. 保存新状态
        self.state_store.save_device_state(&new_state).await?;
        
        // 5. 触发状态变更事件
        let changes = self.calculate_state_changes(&current_state, &new_state);
        self.trigger_state_change_events(device_id, &changes).await?;
        
        // 6. 更新数字孪生
        if let Err(e) = self.update_digital_twin(device_id, &throttled_updates).await {
            log::warn!("更新数字孪生失败: {}", e);
        }
        
        // 7. 触发状态变更工作流
        self.trigger_state_change_workflows(device_id, &changes).await?;
        
        // 8. 返回结果
        Ok(StateUpdateResult {
            device_id: device_id.clone(),
            applied_updates: throttled_updates,
            throttled_updates: property_updates.len() - throttled_updates.len(),
            version: new_state.version,
            timestamp: new_state.last_updated,
        })
    }
    
    /// 触发状态变更工作流
    async fn trigger_state_change_workflows(
        &self,
        device_id: &DeviceId,
        changes: &[StateChange],
    ) -> Result<(), Error> {
        if changes.is_empty() {
            return Ok(());
        }
        
        // 查找与状态变更相关的工作流
        let state_workflows = self.find_state_change_workflows(device_id, changes).await?;
        
        for workflow_def in state_workflows {
            // 创建工作流输入
            let input_data = json!({
                "device_id": device_id,
                "state_changes": changes,
                "timestamp": Utc::now(),
            });
            
            // 启动工作流
            let options = StartWorkflowOptions {
                workflow_id: None,
                created_by: Some("device_state_manager".to_string()),
                metadata: Some(json!({
                    "source": "state_change",
                    "device_id": device_id,
                    "change_count": changes.len(),
                })),
                priority: Some(ExecutionPriority::Normal),
                execution_deadline: None,
            };
            
            self.workflow_engine.start_workflow(
                &workflow_def.id,
                input_data,
                options,
            ).await?;
        }
        
        Ok(())
    }
    
    /// 查找与状态变更相关的工作流
    async fn find_state_change_workflows(
        &self,
        device_id: &DeviceId,
        changes: &[StateChange],
    ) -> Result<Vec<WorkflowDefinition>, Error> {
        // 获取设备信息
        let device = self.state_store.get_device(device_id).await?;
        
        // 准备匹配条件
        let change_properties: HashSet<String> = changes.iter()
            .map(|c| c.property_name.clone())
            .collect();
        
        // 查询匹配的工作流
        self.workflow_engine.query_workflow_definitions(|def| {
            // 检查工作流是否包含状态变更触发器
            if let Some(triggers) = def.metadata.get("triggers") {
                if let Some(triggers_array) = triggers.as_array() {
                    for trigger in triggers_array {
                        if let Some(trigger_obj) = trigger.as_object() {
                            // 检查是否是状态变更触发器
                            if trigger_obj.get("type").and_then(|t| t.as_str()) == Some("device_state_change") {
                                // 检查设备类型是否匹配
                                if let Some(device_types) = trigger_obj.get("device_types").and_then(|dt| dt.as_array()) {
                                    if !device_types.iter().any(|dt| dt.as_str() == Some(&device.device_type.to_string())) {
                                        continue;
                                    }
                                }
                                
                                // 检查属性是否匹配
                                if let Some(properties) = trigger_obj.get("properties").and_then(|p| p.as_array()) {
                                    let trigger_props: HashSet<String> = properties.iter()
                                        .filter_map(|p| p.as_str().map(|s| s.to_string()))
                                        .collect();
                                    
                                    // 如果有交集，则匹配
                                    if !trigger_props.is_empty() && trigger_props.intersection(&change_properties).count() > 0 {
                                        return true;
                                    }
                                } else {
                                    // 未指定属性，匹配所有状态变更
                                    return true;
                                }
                            }
                        }
                    }
                }
            }
            
            false
        }).await
    }
}

/// 状态变更
pub struct StateChange {
    pub property_name: String,
    pub old_value: Option<PropertyValue>,
    pub new_value: PropertyValue,
    pub change_type: ChangeType,
}

/// 变更类型
pub enum ChangeType {
    Added,     // 添加新属性
    Modified,  // 修改现有属性
    Removed,   // 移除属性
}

/// 状态更新源
pub enum StateUpdateSource {
    Telemetry,        // 遥测数据更新
    Command,          // 命令导致的更新
    UserAction,       // 用户操作导致的更新
    Workflow,         // 工作流导致的更新
    ExternalSystem,   // 外部系统更新
    Rule,             // 规则引擎更新
}
```

### 2. 设备命令处理工作流

```rust
/// 设备命令处理工作流活动
pub struct DeviceCommandWorkflow {
    /// 命令管理器
    command_manager: Arc<dyn DeviceCommandManager>,
    
    /// 设备状态管理器
    state_manager: Arc<DeviceStateManager>,
    
    /// 工作流引擎
    workflow_engine: Arc<HighPerformanceWorkflowEngine>,
    
    /// 设备认证服务
    auth_service: Arc<dyn DeviceAuthService>,
    
    /// 规则引擎
    rule_engine: Arc<dyn RuleEngine>,
}

impl DeviceCommandWorkflow {
    /// 创建命令工作流
    pub async fn create_command_workflow(&self, device_type: &DeviceType) -> Result<WorkflowDefinition, Error> {
        // 获取设备类型的命令能力
        let command_capabilities = self.get_device_type_commands(device_type).await?;
        
        // 构建工作流定义
        let mut workflow_def = WorkflowDefinition::new(
            format!("device_command_workflow_{}", device_type),
            format!("{}设备命令工作流", device_type),
            SemanticVersion { major: 1, minor: 0, patch: 0 },
        );
        
        // 添加起始节点
        workflow_def.add_node(WorkflowNode {
            id: "start".to_string(),
            name: "开始".to_string(),
            node_type: NodeType::Event,
            metadata: json!({
                "event_type": "start"
            }),
        });
        
        // 添加设备验证节点
        workflow_def.add_node(WorkflowNode {
            id: "validate_device".to_string(),
            name: "验证设备".to_string(),
            node_type: NodeType::Activity,
            metadata: json!({
                "activity_type": "device_validation_activity",
                "timeout_seconds": 10,
                "retry_count": 3,
            }),
        });
        
        // 添加命令授权节点
        workflow_def.add_node(WorkflowNode {
            id: "authorize_command".to_string(),
            name: "授权命令".to_string(),
            node_type: NodeType::Activity,
            metadata: json!({
                "activity_type": "command_authorization_activity",
                "timeout_seconds": 5,
                "fail_on_unauthorized": true,
            }),
        });
        
        // 为每个命令能力添加命令节点
        for (idx, capability) in command_capabilities.iter().enumerate() {
            // 添加命令选择网关
            if idx == 0 {
                workflow_def.add_node(WorkflowNode {
                    id: "command_selector".to_string(),
                    name: "命令选择器".to_string(),
                    node_type: NodeType::Gateway,
                    metadata: json!({
                        "gateway_type": "exclusive"
                    }),
                });
            }
            
            // 添加命令执行节点
            let command_id = format!("execute_{}", capability.command_name.to_lowercase());
            workflow_def.add_node(WorkflowNode {
                id: command_id.clone(),
                name: format!("执行{}命令", capability.command_name),
                node_type: NodeType::Activity,
                metadata: json!({
                    "activity_type": "device_command_activity",
                    "command_name": capability.command_name,
                    "timeout_seconds": capability.timeout_seconds,
                    "retry_policy": {
                        "max_retries": capability.retry_count,
                        "backoff_factor": 1.5,
                        "max_backoff_seconds": 60
                    },
                    "required_parameters": capability.required_parameters,
                    "optional_parameters": capability.optional_parameters,
                }),
            });
            
            // 添加命令结果处理节点
            workflow_def.add_node(WorkflowNode {
                id: format!("{}_result_handler", command_id),
                name: format!("{}命令结果处理", capability.command_name),
                node_type: NodeType::Activity,
                metadata: json!({
                    "activity_type": "command_result_handler_activity",
                    "update_device_state": capability.updates_device_state,
                    "result_mapping": capability.result_mapping,
                }),
            });
            
            // 添加从命令选择器到命令执行的转换
            workflow_def.add_transition(Transition {
                source_id: "command_selector".to_string(),
                target_id: command_id.clone(),
                condition: Some(format!("{{{{ command_type == '{}' }}}}", capability.command_name)),
            });
            
            // 添加从命令执行到结果处理的转换
            workflow_def.add_transition(Transition {
                source_id: command_id,
                target_id: format!("{}_result_handler", command_id),
                condition: None,
            });
            
            // 从结果处理到结束节点的转换
            workflow_def.add_transition(Transition {
                source_id: format!("{}_result_handler", command_id),
                target_id: "end".to_string(),
                condition: None,
            });
        }
        
        // 添加结束节点
        workflow_def.add_node(WorkflowNode {
            id: "end".to_string(),
            name: "结束".to_string(),
            node_type: NodeType::Event,
            metadata: json!({
                "event_type": "end"
            }),
        });
        
        // 添加从开始到设备验证的转换
        workflow_def.add_transition(Transition {
            source_id: "start".to_string(),
            target_id: "validate_device".to_string(),
            condition: None,
        });
        
        // 添加从设备验证到命令授权的转换
        workflow_def.add_transition(Transition {
            source_id: "validate_device".to_string(),
            target_id: "authorize_command".to_string(),
            condition: None,
        });
        
        // 添加从命令授权到命令选择器的转换
        workflow_def.add_transition(Transition {
            source_id: "authorize_command".to_string(),
            target_id: "command_selector".to_string(),
            condition: None,
        });
        
        // 保存工作流定义
        self.workflow_engine.save_workflow_definition(&workflow_def).await?;
        
        Ok(workflow_def)
    }
    
    /// 处理设备命令请求
    pub async fn process_command_request(
        &self,
        request: DeviceCommandRequest,
    ) -> Result<CommandRequestResponse, Error> {
        // 1. 验证请求
        self.validate_command_request(&request).await?;
        
        // 2. 创建命令ID
        let command_id = Uuid::new_v4().to_string();
        
        // 3. 确定对应的工作流类型
        let device = self.state_manager.get_device(&request.device_id).await?;
        let workflow_type = format!("device_command_workflow_{}", device.device_type);
        
        // 4. 构建工作流输入数据
        let input_data = json!({
            "command_id": command_id,
            "device_id": request.device_id,
            "command_type": request.command_type,
            "parameters": request.parameters,
            "metadata": request.metadata,
            "user_id": request.user_id,
            "priority": request.priority,
            "timeout": request.timeout.map(|t| t.as_secs()),
        });
        
        // 5. 启动命令工作流
        let options = StartWorkflowOptions {
            workflow_id: Some(format!("cmd_{}_{}", request.device_id, command_id)),
            created_by: request.user_id.
# Rust实现IOT工作流系统的全面设计与分析（续）

## IV. IOT工作流系统设计模式与实现（续）

### 2. 设备命令处理工作流（续）

```rust
/// 设备命令处理工作流活动（续）
impl DeviceCommandWorkflow {
    /// 处理设备命令请求（续）
    pub async fn process_command_request(
        &self,
        request: DeviceCommandRequest,
    ) -> Result<CommandRequestResponse, Error> {
        // 前面部分...
        
        // 5. 启动命令工作流
        let options = StartWorkflowOptions {
            workflow_id: Some(format!("cmd_{}_{}", request.device_id, command_id)),
            created_by: request.user_id.clone(),
            metadata: Some(json!({
                "source": "command_request",
                "device_id": request.device_id,
                "command_type": request.command_type,
            })),
            priority: Some(self.determine_command_priority(&request)),
            execution_deadline: request.timeout.map(|t| Utc::now() + chrono::Duration::from_std(t).unwrap_or_default()),
        };
        
        let workflow_id = self.workflow_engine.start_workflow(
            &workflow_type,
            input_data,
            options,
        ).await?;
        
        // 6. 创建命令追踪记录
        let command = DeviceCommand {
            id: CommandId(command_id.clone()),
            device_id: request.device_id.clone(),
            command_type: request.command_type.clone(),
            parameters: request.parameters.clone(),
            timeout: request.timeout.unwrap_or(Duration::from_secs(30)),
            priority: request.priority.unwrap_or(CommandPriority::Normal),
            created_at: Utc::now(),
            status: CommandStatus::Pending,
            response: None,
            workflow_id: Some(workflow_id.clone()),
        };
        
        self.command_manager.register_command(command).await?;
        
        // 7. 返回响应
        Ok(CommandRequestResponse {
            command_id,
            workflow_id,
            status: CommandStatus::Pending,
            estimated_completion: Some(Utc::now() + chrono::Duration::seconds(5)), // 简单估计
            tracking_url: Some(format!("/api/commands/{}", command_id)),
        })
    }
    
    /// 确定命令优先级
    fn determine_command_priority(&self, request: &DeviceCommandRequest) -> ExecutionPriority {
        match request.priority {
            Some(CommandPriority::Emergency) => ExecutionPriority::High,
            Some(CommandPriority::High) => ExecutionPriority::High,
            Some(CommandPriority::Normal) => ExecutionPriority::Normal,
            Some(CommandPriority::Low) => ExecutionPriority::Low,
            None => {
                // 根据命令类型确定默认优先级
                match request.command_type.as_str() {
                    "reboot" | "reset" | "emergency_stop" => ExecutionPriority::High,
                    "update_firmware" | "configure" => ExecutionPriority::Normal,
                    "get_diagnostics" | "read_logs" => ExecutionPriority::Low,
                    _ => ExecutionPriority::Normal,
                }
            }
        }
    }
    
    /// 验证命令请求
    async fn validate_command_request(&self, request: &DeviceCommandRequest) -> Result<(), Error> {
        // 1. 检查设备是否存在
        let device = match self.state_manager.get_device(&request.device_id).await {
            Ok(device) => device,
            Err(Error::NotFound(_)) => {
                return Err(Error::InvalidRequest(format!("设备 {} 不存在", request.device_id)));
            },
            Err(e) => return Err(e),
        };
        
        // 2. 检查设备状态是否允许命令
        if device.status == DeviceStatus::Offline {
            return Err(Error::InvalidState(format!("设备 {} 当前离线", request.device_id)));
        }
        
        if device.status == DeviceStatus::Disabled || device.status == DeviceStatus::Maintenance {
            return Err(Error::InvalidState(format!("设备 {} 当前状态为 {:?}, 不接受命令", request.device_id, device.status)));
        }
        
        // 3. 验证命令类型是否支持
        let command_capabilities = self.get_device_commands(&device).await?;
        let command_supported = command_capabilities.iter()
            .any(|c| c.command_name == request.command_type);
            
        if !command_supported {
            return Err(Error::UnsupportedOperation(format!(
                "设备 {} 不支持命令类型 {}", 
                request.device_id, 
                request.command_type
            )));
        }
        
        // 4. 验证用户权限
        if let Some(user_id) = &request.user_id {
            let authorized = self.auth_service.authorize_device_command(
                user_id,
                &request.device_id,
                &request.command_type,
            ).await?;
            
            if !authorized {
                return Err(Error::Unauthorized(format!(
                    "用户 {} 没有执行设备 {} 命令 {} 的权限",
                    user_id, request.device_id, request.command_type
                )));
            }
        }
        
        // 5. 验证命令参数
        let command_spec = command_capabilities.iter()
            .find(|c| c.command_name == request.command_type)
            .unwrap(); // 上面已检查存在性
            
        // 检查必要参数
        for required_param in &command_spec.required_parameters {
            if !request.parameters.contains_key(required_param) {
                return Err(Error::InvalidRequest(format!(
                    "命令 {} 缺少必要参数 {}",
                    request.command_type, required_param
                )));
            }
        }
        
        // 6. 应用命令规则
        let rule_result = self.rule_engine.evaluate_command_rules(
            &device,
            &request.command_type,
            &request.parameters,
        ).await?;
        
        if !rule_result.allowed {
            return Err(Error::RuleViolation(format!(
                "命令违反规则: {}", 
                rule_result.reason.unwrap_or_else(|| "未指定原因".to_string())
            )));
        }
        
        Ok(())
    }
}

/// 设备命令请求
pub struct DeviceCommandRequest {
    pub device_id: DeviceId,
    pub command_type: String,
    pub parameters: HashMap<String, Value>,
    pub user_id: Option<String>,
    pub priority: Option<CommandPriority>,
    pub timeout: Option<Duration>,
    pub metadata: HashMap<String, Value>,
}

/// 命令请求响应
pub struct CommandRequestResponse {
    pub command_id: String,
    pub workflow_id: String,
    pub status: CommandStatus,
    pub estimated_completion: Option<DateTime<Utc>>,
    pub tracking_url: Option<String>,
}
```

### 3. 遥测数据处理与异常检测

```rust
/// 遥测处理工作流
pub struct TelemetryProcessingWorkflow {
    /// 遥测处理引擎
    telemetry_processor: Arc<dyn TelemetryProcessor>,
    
    /// 异常检测器
    anomaly_detector: Arc<dyn AnomalyDetector>,
    
    /// 时间序列存储
    time_series_storage: Arc<dyn TimeSeriesStorage>,
    
    /// 状态管理器
    state_manager: Arc<DeviceStateManager>,
    
    /// 工作流引擎
    workflow_engine: Arc<HighPerformanceWorkflowEngine>,
    
    /// 规则引擎
    rule_engine: Arc<dyn RuleEngine>,
    
    /// 通知服务
    notification_service: Arc<dyn NotificationService>,
}

impl TelemetryProcessingWorkflow {
    /// 处理设备遥测数据
    pub async fn process_telemetry(&self, telemetry: Vec<Telemetry>) -> Result<TelemetryProcessingResult, Error> {
        if telemetry.is_empty() {
            return Ok(TelemetryProcessingResult {
                processed_count: 0,
                anomalies_detected: 0,
                rules_triggered: 0,
                state_updates: 0,
                processing_time_ms: 0,
            });
        }
        
        let start_time = Instant::now();
        
        // 1. 按设备分组
        let mut telemetry_by_device: HashMap<DeviceId, Vec<Telemetry>> = HashMap::new();
        for item in telemetry {
            telemetry_by_device
                .entry(item.device_id.clone())
                .or_insert_with(Vec::new)
                .push(item);
        }
        
        let mut anomalies_detected = 0;
        let mut rules_triggered = 0;
        let mut state_updates = 0;
        let mut total_processed = 0;
        
        // 2. 并行处理每个设备的遥测数据
        let mut processing_tasks = Vec::new();
        
        for (device_id, device_telemetry) in telemetry_by_device {
            let processor = self.clone();
            let device_id_clone = device_id.clone();
            let task = tokio::spawn(async move {
                let result = processor.process_device_telemetry(
                    &device_id_clone,
                    device_telemetry,
                ).await;
                
                (device_id_clone, result)
            });
            
            processing_tasks.push(task);
        }
        
        // 3. 等待所有处理任务完成
        for task in processing_tasks {
            match task.await {
                Ok((device_id, result)) => {
                    match result {
                        Ok(device_result) => {
                            total_processed += device_result.processed_count;
                            anomalies_detected += device_result.anomalies.len();
                            rules_triggered += device_result.triggered_rules.len();
                            state_updates += device_result.state_updates;
                            
                            // 处理检测到的异常
                            if !device_result.anomalies.is_empty() {
                                self.handle_anomalies(&device_id, &device_result.anomalies).await?;
                            }
                            
                            // 处理触发的规则
                            if !device_result.triggered_rules.is_empty() {
                                self.handle_triggered_rules(&device_id, &device_result.triggered_rules).await?;
                            }
                        },
                        Err(e) => {
                            log::error!("处理设备 {} 的遥测数据失败: {}", device_id, e);
                            // 继续处理其他设备的数据
                        }
                    }
                },
                Err(e) => {
                    log::error!("遥测处理任务失败: {}", e);
                    // 继续处理其他设备的数据
                }
            }
        }
        
        let processing_time_ms = start_time.elapsed().as_millis() as u64;
        
        // 4. 返回总体处理结果
        Ok(TelemetryProcessingResult {
            processed_count: total_processed,
            anomalies_detected,
            rules_triggered,
            state_updates,
            processing_time_ms,
        })
    }
    
    /// 处理单个设备的遥测数据
    async fn process_device_telemetry(
        &self,
        device_id: &DeviceId,
        telemetry: Vec<Telemetry>,
    ) -> Result<DeviceTelemetryResult, Error> {
        // 初始化结果
        let mut result = DeviceTelemetryResult {
            device_id: device_id.clone(),
            processed_count: telemetry.len(),
            anomalies: Vec::new(),
            triggered_rules: Vec::new(),
            state_updates: 0,
        };
        
        // 1. 检查设备是否存在
        let device = match self.state_manager.get_device(device_id).await {
            Ok(device) => device,
            Err(Error::NotFound(_)) => {
                log::warn!("收到未知设备 {} 的遥测数据", device_id);
                // 可以选择拒绝数据或自动注册设备
                return Err(Error::NotFound(format!("设备 {} 不存在", device_id)));
            },
            Err(e) => return Err(e),
        };
        
        // 2. 预处理和验证遥测数据
        let validated_telemetry = self.validate_telemetry(&device, telemetry)?;
        
        // 3. 存储遥测数据
        self.time_series_storage.store_telemetry(&validated_telemetry).await?;
        
        // 4. 异常检测
        let anomalies = self.detect_anomalies(&device, &validated_telemetry).await?;
        result.anomalies = anomalies;
        
        // 5. 应用规则引擎
        let triggered_rules = self.apply_telemetry_rules(&device, &validated_telemetry).await?;
        result.triggered_rules = triggered_rules;
        
        // 6. 更新设备状态
        if !validated_telemetry.is_empty() {
            // 从遥测中提取要更新的设备属性
            let property_updates = self.extract_state_updates(&device, &validated_telemetry);
            
            if !property_updates.is_empty() {
                let update_result = self.state_manager.update_device_state(
                    device_id,
                    property_updates,
                    StateUpdateSource::Telemetry,
                ).await?;
                
                result.state_updates = update_result.applied_updates.len();
            }
        }
        
        Ok(result)
    }
    
    /// 检测异常
    async fn detect_anomalies(
        &self,
        device: &Device,
        telemetry: &[Telemetry],
    ) -> Result<Vec<Anomaly>, Error> {
        let mut anomalies = Vec::new();
        
        // 1. 获取设备的异常检测配置
        let detection_configs = self.get_anomaly_detection_configs(device).await?;
        
        if detection_configs.is_empty() || telemetry.is_empty() {
            return Ok(anomalies);
        }
        
        // 2. 应用异常检测算法
        for config in detection_configs {
            // 提取目标指标
            let metrics: Vec<_> = telemetry.iter()
                .filter_map(|t| {
                    t.metrics.get(&config.metric_name).map(|value| {
                        (t.timestamp, value.clone())
                    })
                })
                .collect();
                
            if metrics.is_empty() {
                continue;
            }
            
            // 应用检测算法
            match config.detection_algorithm {
                AnomalyDetectionAlgorithm::ThresholdBased { min, max } => {
                    // 阈值检测
                    for (timestamp, value) in &metrics {
                        if let Some(min_threshold) = min {
                            if value.as_f64().unwrap_or(0.0) < min_threshold {
                                anomalies.push(Anomaly {
                                    device_id: device.id.clone(),
                                    anomaly_type: AnomalyType::BelowThreshold,
                                    metric_name: config.metric_name.clone(),
                                    detected_value: value.clone(),
                                    threshold: PropertyValue::Number(min_threshold),
                                    severity: config.severity,
                                    timestamp: *timestamp,
                                    confidence: 1.0, // 阈值检测具有100%的置信度
                                });
                            }
                        }
                        
                        if let Some(max_threshold) = max {
                            if value.as_f64().unwrap_or(0.0) > max_threshold {
                                anomalies.push(Anomaly {
                                    device_id: device.id.clone(),
                                    anomaly_type: AnomalyType::AboveThreshold,
                                    metric_name: config.metric_name.clone(),
                                    detected_value: value.clone(),
                                    threshold: PropertyValue::Number(max_threshold),
                                    severity: config.severity,
                                    timestamp: *timestamp,
                                    confidence: 1.0,
                                });
                            }
                        }
                    }
                },
                AnomalyDetectionAlgorithm::ZScore { window_size, threshold } => {
                    // Z-Score 检测
                    if metrics.len() >= window_size {
                        // 获取历史数据
                        let historical_data = self.time_series_storage.query_metric(
                            &device.id,
                            &config.metric_name,
                            Utc::now() - chrono::Duration::minutes(window_size as i64),
                            Utc::now(),
                        ).await?;
                        
                        // 计算均值和标准差
                        let values: Vec<f64> = historical_data.iter()
                            .map(|(_, value)| value.as_f64().unwrap_or(0.0))
                            .collect();
                            
                        if !values.is_empty() {
                            let mean = values.iter().sum::<f64>() / values.len() as f64;
                            let variance = values.iter()
                                .map(|x| (*x - mean).powi(2))
                                .sum::<f64>() / values.len() as f64;
                            let std_dev = variance.sqrt();
                            
                            // 检测异常
                            for (timestamp, value) in &metrics {
                                let value_f64 = value.as_f64().unwrap_or(0.0);
                                let z_score = if std_dev > 0.0 { (value_f64 - mean) / std_dev } else { 0.0 };
                                
                                if z_score.abs() > threshold {
                                    anomalies.push(Anomaly {
                                        device_id: device.id.clone(),
                                        anomaly_type: if z_score > 0.0 { AnomalyType::StatisticalHigh } else { AnomalyType::StatisticalLow },
                                        metric_name: config.metric_name.clone(),
                                        detected_value: value.clone(),
                                        threshold: PropertyValue::Number(if z_score > 0.0 { mean + threshold * std_dev } else { mean - threshold * std_dev }),
                                        severity: config.severity,
                                        timestamp: *timestamp,
                                        confidence: (z_score.abs() - threshold) / threshold, // 置信度基于Z-Score超过阈值的程度
                                    });
                                }
                            }
                        }
                    }
                },
                // 其他算法...
                _ => {}
            }
        }
        
        Ok(anomalies)
    }
    
    /// 处理检测到的异常
    async fn handle_anomalies(
        &self,
        device_id: &DeviceId,
        anomalies: &[Anomaly],
    ) -> Result<(), Error> {
        if anomalies.is_empty() {
            return Ok(());
        }
        
        // 1. 查找与异常相关的工作流
        let anomaly_workflows = self.find_anomaly_workflows(device_id, anomalies).await?;
        
        // 2. 触发相关工作流
        for workflow_def in anomaly_workflows {
            // 创建工作流输入
            let input_data = json!({
                "device_id": device_id,
                "anomalies": anomalies,
                "timestamp": Utc::now(),
                "severity": anomalies.iter().map(|a| a.severity).max().unwrap_or(AnomalySeverity::Low),
            });
            
            // 确定优先级
            let max_severity = anomalies.iter().map(|a| a.severity).max().unwrap_or(AnomalySeverity::Low);
            let priority = match max_severity {
                AnomalySeverity::Critical => ExecutionPriority::High,
                AnomalySeverity::High => ExecutionPriority::High,
                AnomalySeverity::Medium => ExecutionPriority::Normal,
                AnomalySeverity::Low => ExecutionPriority::Low,
            };
            
            // 启动工作流
            let options = StartWorkflowOptions {
                workflow_id: None,
                created_by: Some("anomaly_detector".to_string()),
                metadata: Some(json!({
                    "source": "anomaly_detection",
                    "device_id": device_id,
                    "anomaly_count": anomalies.len(),
                    "max_severity": format!("{:?}", max_severity),
                })),
                priority: Some(priority),
                execution_deadline: None,
            };
            
            self.workflow_engine.start_workflow(
                &workflow_def.id,
                input_data,
                options,
            ).await?;
        }
        
        // 3. 发送紧急通知（对于严重异常）
        let critical_anomalies: Vec<_> = anomalies.iter()
            .filter(|a| a.severity == AnomalySeverity::Critical || a.severity == AnomalySeverity::High)
            .collect();
            
        if !critical_anomalies.is_empty() {
            // 获取设备信息
            let device = self.state_manager.get_device(device_id).await?;
            
            // 准备通知内容
            let notification = Notification {
                id: Uuid::new_v4().to_string(),
                title: format!("设备 {} 检测到严重异常", device.name),
                body: format!(
                    "检测到 {} 个严重异常。首个异常: {} {} 值: {}",
                    critical_anomalies.len(),
                    critical_anomalies[0].metric_name,
                    format!("{:?}", critical_anomalies[0].anomaly_type),
                    critical_anomalies[0].detected_value.to_string(),
                ),
                severity: NotificationSeverity::High,
                category: NotificationCategory::Anomaly,
                timestamp: Utc::now(),
                source: "anomaly_detector".to_string(),
                metadata: json!({
                    "device_id": device_id,
                    "device_name": device.name,
                    "anomaly_count": critical_anomalies.len(),
                }),
                actions: vec![
                    NotificationAction {
                        name: "view_details".to_string(),
                        title: "查看详情".to_string(),
                        url: Some(format!("/devices/{}/anomalies", device_id)),
                    },
                    NotificationAction {
                        name: "acknowledge".to_string(),
                        title: "确认".to_string(),
                        url: None,
                    },
                ],
            };
            
            // 发送通知
            self.notification_service.send_notification(
                notification,
                &self.get_anomaly_notification_targets(&device, &critical_anomalies).await?,
            ).await?;
        }
        
        Ok(())
    }
}

/// 遥测处理结果
pub struct TelemetryProcessingResult {
    pub processed_count: usize,
    pub anomalies_detected: usize,
    pub rules_triggered: usize,
    pub state_updates: usize,
    pub processing_time_ms: u64,
}

/// 设备遥测处理结果
pub struct DeviceTelemetryResult {
    pub device_id: DeviceId,
    pub processed_count: usize,
    pub anomalies: Vec<Anomaly>,
    pub triggered_rules: Vec<TriggeredRule>,
    pub state_updates: usize,
}

/// 异常
pub struct Anomaly {
    pub device_id: DeviceId,
    pub anomaly_type: AnomalyType,
    pub metric_name: String,
    pub detected_value: PropertyValue,
    pub threshold: PropertyValue,
    pub severity: AnomalySeverity,
    pub timestamp: DateTime<Utc>,
    pub confidence: f64,
}

/// 异常类型
pub enum AnomalyType {
    AboveThreshold,       // 高于阈值
    BelowThreshold,       // 低于阈值
    StatisticalHigh,      // 统计显著高值
    StatisticalLow,       // 统计显著低值
    RateOfChange,         // 变化率异常
    PatternChange,        // 模式变化
    OutOfBounds,          // 超出范围
    SensorMalfunction,    // 传感器故障
    CommunicationIssue,   // 通信问题
    Custom(String),       // 自定义异常
}

/// 异常严重性
pub enum AnomalySeverity {
    Critical,      // 紧急
    High,          // 高
    Medium,        // 中
    Low,           // 低
}

/// 异常检测算法
pub enum AnomalyDetectionAlgorithm {
    ThresholdBased {            // 基于阈值
        min: Option<f64>,
        max: Option<f64>,
    },
    ZScore {                    // 基于Z分数
        window_size: usize,
        threshold: f64,
    },
    MovingAverage {             // 移动平均
        window_size: usize,
        deviation_factor: f64,
    },
    SeasonalDecomposition {     // 季节性分解
        period: usize,
        deviation_threshold: f64,
    },
    MachineLearning {           // 机器学习
        model_id: String,
        confidence_threshold: f64,
    },
    Custom {                    // 自定义算法
        algorithm_name: String,
        parameters: HashMap<String, Value>,
    },
}
```

### 4. 固件更新工作流实现

```rust
/// 固件更新工作流
pub struct FirmwareUpdateWorkflow {
    /// 设备管理服务
    device_service: Arc<dyn DeviceService>,
    
    /// 固件管理器
    firmware_manager: Arc<dyn FirmwareManager>,
    
    /// 命令管理器
    command_manager: Arc<dyn DeviceCommandManager>,
    
    /// 工作流引擎
    workflow_engine: Arc<HighPerformanceWorkflowEngine>,
    
    /// 通知服务
    notification_service: Arc<dyn NotificationService>,
    
    /// 状态管理器
    state_manager: Arc<DeviceStateManager>,
}

impl FirmwareUpdateWorkflow {
    /// 创建固件更新工作流定义
    pub fn create_firmware_update_workflow() -> WorkflowDefinition {
        let mut workflow_def = WorkflowDefinition::new(
            "firmware_update_workflow",
            "设备固件更新工作流",
            SemanticVersion { major: 1, minor: 0, patch: 0 },
        );
        
        // 添加开始节点
        workflow_def.add_node(WorkflowNode {
            id: "start".to_string(),
            name: "开始".to_string(),
            node_type: NodeType::Event,
            metadata: json!({
                "event_type": "start"
            }),
        });
        
        // 添加设备资格验证
        workflow_def.add_node(WorkflowNode {
            id: "validate_device_eligibility".to_string(),
            name: "验证设备资格".to_string(),
            node_type: NodeType::Activity,
            metadata: json!({
                "activity_type": "device_eligibility_check",
                "timeout_seconds": 30,
                "retries": 2,
            }),
        });
        
        // 添加固件验证
        workflow_def.add_node(WorkflowNode {
            id: "verify_firmware".to_string(),
            name: "验证固件".to_string(),
            node_type: NodeType::Activity,
            metadata: json!({
                "activity_type": "firmware_verification",
                "timeout_seconds": 60,
                "verify_signature": true,
                "verify_compatibility": true,
            }),
        });
        
        // 添加备份当前固件
        workflow_def.add_node(WorkflowNode {
            id: "backup_current_firmware".to_string(),
            name: "备份当前固件".to_string(),
            node_type: NodeType::Activity,
            metadata: json!({
                "activity_type": "firmware_backup",
                "timeout_seconds": 300,
                "retry_count": 1,
            }),
        });
        
        // 添加通知用户
        workflow_def.add_node(WorkflowNode {
            id: "notify_update_start".to_string(),
            name: "通知更新开始".to_string(),
            node_type: NodeType::Activity,
            metadata: json!({
                "activity_type": "notification_activity",
                "notification_type": "firmware_update_start",
                "priority": "normal",
            }),
        });
        
        // 添加设备预更新准备
        workflow_def.add_node(WorkflowNode {
            id: "prepare_device".to_string(),
```

## 设备预更新准备流程设计

接下来，我们将设计设备预更新准备流程，这是固件更新过程中的关键步骤。此流程确保设备在接收固件更新前处于最佳状态，提高更新成功率。

## 设备预更新准备工作流

```rust
pub fn create_device_pre_update_workflow() -> WorkflowDefinition {
    let mut workflow = WorkflowDefinition::new(
        "device_pre_update_workflow",
        "设备固件更新准备流程",
        "在推送固件更新前准备设备的工作流程",
    );

    // 添加工作流节点
    workflow.add_node(WorkflowNode {
        id: "check_device_status".to_string(),
        name: "检查设备状态".to_string(),
        node_type: NodeType::Function,
        function: "check_device_status".to_string(),
        next_nodes: vec!["check_battery_level".to_string()],
        error_node: Some("notify_status_error".to_string()),
        timeout_seconds: 30,
    });

    workflow.add_node(WorkflowNode {
        id: "check_battery_level".to_string(),
        name: "检查电池电量".to_string(),
        node_type: NodeType::Function,
        function: "check_battery_level".to_string(),
        next_nodes: vec!["check_storage_space".to_string()],
        error_node: Some("notify_battery_error".to_string()),
        timeout_seconds: 30,
    });

    workflow.add_node(WorkflowNode {
        id: "check_storage_space".to_string(),
        name: "检查存储空间".to_string(),
        node_type: NodeType::Function,
        function: "check_storage_space".to_string(),
        next_nodes: vec!["backup_critical_data".to_string()],
        error_node: Some("notify_storage_error".to_string()),
        timeout_seconds: 30,
    });

    workflow.add_node(WorkflowNode {
        id: "backup_critical_data".to_string(),
        name: "备份关键数据".to_string(),
        node_type: NodeType::Function,
        function: "backup_critical_data".to_string(),
        next_nodes: vec!["notify_ready_for_update".to_string()],
        error_node: Some("notify_backup_error".to_string()),
        timeout_seconds: 120,
    });

    workflow.add_node(WorkflowNode {
        id: "notify_ready_for_update".to_string(),
        name: "通知设备准备就绪".to_string(),
        node_type: NodeType::Function,
        function: "notify_device_ready".to_string(),
        next_nodes: vec!["end".to_string()],
        error_node: None,
        timeout_seconds: 30,
    });

    // 添加错误处理节点
    workflow.add_node(WorkflowNode {
        id: "notify_status_error".to_string(),
        name: "状态检查错误通知".to_string(),
        node_type: NodeType::Function,
        function: "notify_preparation_error".to_string(),
        next_nodes: vec!["end".to_string()],
        error_node: None,
        timeout_seconds: 30,
    });

    // 其他错误节点类似...

    workflow.add_node(WorkflowNode {
        id: "end".to_string(),
        name: "结束".to_string(),
        node_type: NodeType::End,
        function: "".to_string(),
        next_nodes: vec![],
        error_node: None,
        timeout_seconds: 0,
    });

    workflow
}
```

## 设备预更新准备功能实现

下面是各个节点对应的功能实现：

```rust
/// 检查设备当前状态是否适合进行更新
pub async fn check_device_status(context: &WorkflowContext) -> Result<NodeOutput, WorkflowError> {
    let device_id = context.get_param("device_id")
        .ok_or_else(|| WorkflowError::MissingParameter("device_id".to_string()))?;
    
    // 获取设备状态
    let device = device_repository::get_device_by_id(device_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法获取设备信息: {}", e)))?;
    
    // 检查设备是否在线
    if device.status != DeviceStatus::Online {
        return Err(WorkflowError::ExecutionError(
            format!("设备不在线，当前状态: {:?}", device.status)
        ));
    }
    
    // 检查设备是否处于维护模式
    if device.maintenance_mode {
        return Err(WorkflowError::ExecutionError("设备处于维护模式，无法进行更新".to_string()));
    }
    
    // 检查设备是否有正在运行的关键任务
    let active_tasks = task_repository::get_active_critical_tasks(device_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法检查设备任务: {}", e)))?;
    
    if !active_tasks.is_empty() {
        return Err(WorkflowError::ExecutionError(
            format!("设备有{}个正在运行的关键任务，无法进行更新", active_tasks.len())
        ));
    }
    
    Ok(NodeOutput::new())
}

/// 检查设备电池电量是否足够完成更新
pub async fn check_battery_level(context: &WorkflowContext) -> Result<NodeOutput, WorkflowError> {
    let device_id = context.get_param("device_id")
        .ok_or_else(|| WorkflowError::MissingParameter("device_id".to_string()))?;
    
    // 获取设备最新的电量遥测数据
    let battery_telemetry = telemetry_repository::get_latest_battery_telemetry(device_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法获取电池电量信息: {}", e)))?;
    
    // 获取更新所需的最低电量
    let firmware_id = context.get_param("firmware_id")
        .ok_or_else(|| WorkflowError::MissingParameter("firmware_id".to_string()))?;
    
    let firmware = firmware_repository::get_firmware(firmware_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法获取固件信息: {}", e)))?;
    
    let required_battery = firmware.min_battery_level.unwrap_or(30.0); // 默认30%电量
    
    // 检查电量是否足够
    if battery_telemetry.value < required_battery {
        return Err(WorkflowError::ExecutionError(
            format!(
                "设备电量不足，当前电量: {}%，更新需要至少: {}%",
                battery_telemetry.value, required_battery
            )
        ));
    }
    
    // 如果是电池供电设备，还需要检查是否已连接充电器
    let device = device_repository::get_device_by_id(device_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法获取设备信息: {}", e)))?;
    
    if device.power_type == PowerType::Battery {
        let charging_status = telemetry_repository::get_latest_charging_status(device_id).await
            .map_err(|e| WorkflowError::ExecutionError(format!("无法获取充电状态: {}", e)))?;
        
        if !charging_status.is_charging && battery_telemetry.value < 75.0 {
            return Err(WorkflowError::ExecutionError(
                "建议在更新前连接电源，以防更新过程中电量耗尽".to_string()
            ));
        }
    }
    
    let mut output = NodeOutput::new();
    output.add_data("battery_level", battery_telemetry.value);
    Ok(output)
}

/// 检查设备是否有足够的存储空间进行更新
pub async fn check_storage_space(context: &WorkflowContext) -> Result<NodeOutput, WorkflowError> {
    let device_id = context.get_param("device_id")
        .ok_or_else(|| WorkflowError::MissingParameter("device_id".to_string()))?;
    
    let firmware_id = context.get_param("firmware_id")
        .ok_or_else(|| WorkflowError::MissingParameter("firmware_id".to_string()))?;
    
    // 获取固件大小
    let firmware = firmware_repository::get_firmware(firmware_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法获取固件信息: {}", e)))?;
    
    // 获取设备存储信息
    let storage_info = device_command_service::query_storage_info(device_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法获取设备存储信息: {}", e)))?;
    
    // 计算需要的空间 (固件大小 + 安全余量)
    let required_space = firmware.size_bytes + (firmware.size_bytes / 2); // 额外50%作为安全余量
    
    if storage_info.free_bytes < required_space {
        return Err(WorkflowError::ExecutionError(
            format!(
                "设备存储空间不足，可用空间: {} MB，需要至少: {} MB",
                storage_info.free_bytes / (1024 * 1024),
                required_space / (1024 * 1024)
            )
        ));
    }
    
    let mut output = NodeOutput::new();
    output.add_data("free_space_mb", storage_info.free_bytes / (1024 * 1024));
    output.add_data("required_space_mb", required_space / (1024 * 1024));
    Ok(output)
}

/// 备份设备关键数据
pub async fn backup_critical_data(context: &WorkflowContext) -> Result<NodeOutput, WorkflowError> {
    let device_id = context.get_param("device_id")
        .ok_or_else(|| WorkflowError::MissingParameter("device_id".to_string()))?;
    
    // 获取设备配置
    let device = device_repository::get_device_by_id(device_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法获取设备信息: {}", e)))?;
    
    // 创建备份任务
    let backup_request = BackupRequest {
        device_id: device_id.to_string(),
        backup_type: BackupType::PreUpdate,
        include_settings: true,
        include_user_data: device.backup_user_data_on_update,
        retention_days: 30, // 保留30天
    };
    
    // 执行备份
    let backup_result = backup_service::create_backup(backup_request).await
        .map_err(|e| WorkflowError::ExecutionError(format!("创建备份失败: {}", e)))?;
    
    // 验证备份是否成功
    if !backup_result.success {
        return Err(WorkflowError::ExecutionError(
            format!("备份失败: {}", backup_result.error.unwrap_or_default())
        ));
    }
    
    // 记录备份ID，以便后续回滚时使用
    let mut output = NodeOutput::new();
    output.add_data("backup_id", backup_result.backup_id);
    output.add_data("backup_size_bytes", backup_result.backup_size_bytes);
    output.add_data("backup_timestamp", backup_result.created_at.to_rfc3339());
    
    Ok(output)
}

/// 通知设备准备就绪，可以进行更新
pub async fn notify_device_ready(context: &WorkflowContext) -> Result<NodeOutput, WorkflowError> {
    let device_id = context.get_param("device_id")
        .ok_or_else(|| WorkflowError::MissingParameter("device_id".to_string()))?;
    
    // 更新设备状态为"准备更新"
    device_repository::update_device_update_status(device_id, UpdateStatus::ReadyForUpdate).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法更新设备状态: {}", e)))?;
    
    // 可选：发送命令让设备进入更新准备模式
    let prepare_cmd = PrepareForUpdateCommand {
        mode: UpdateMode::Safe,
        timeout_seconds: 300, // 5分钟超时
    };
    
    device_command_service::send_prepare_update_command(device_id, prepare_cmd).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法发送准备更新命令: {}", e)))?;
    
    // 更新工作流状态
    let mut output = NodeOutput::new();
    output.add_data("preparation_complete", true);
    output.add_data("ready_timestamp", Utc::now().to_rfc3339());
    
    Ok(output)
}

/// 处理准备过程中的错误
pub async fn notify_preparation_error(context: &WorkflowContext) -> Result<NodeOutput, WorkflowError> {
    let device_id = context.get_param("device_id")
        .ok_or_else(|| WorkflowError::MissingParameter("device_id".to_string()))?;
    
    let error_message = context.get_error_message()
        .unwrap_or("未知错误".to_string());
    
    let error_node = context.get_error_node()
        .unwrap_or("unknown".to_string());
    
    // 记录错误
    log::error!(
        "设备 {} 更新准备阶段失败，节点: {}, 原因: {}", 
        device_id, error_node, error_message
    );
    
    // 更新设备状态
    device_repository::update_device_update_status(device_id, UpdateStatus::PreparationFailed).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法更新设备状态: {}", e)))?;
    
    // 发送通知
    let notification = NotificationRequest {
        level: NotificationLevel::Warning,
        category: NotificationCategory::DeviceUpdate,
        title: format!("设备 {} 更新准备失败", device_id),
        message: format!("在 {} 阶段失败: {}", error_node, error_message),
        related_entity: Some(EntityReference {
            entity_type: EntityType::Device,
            entity_id: device_id.to_string(),
        }),
        actions: vec![
            NotificationAction {
                label: "重试".to_string(),
                action_type: ActionType::Workflow,
                action_data: "retry_device_preparation".to_string(),
            },
            NotificationAction {
                label: "查看详情".to_string(),
                action_type: ActionType::Url,
                action_data: format!("/devices/{}/updates", device_id),
            },
        ],
        expiration: Some(Utc::now() + Duration::days(1)),
    };
    
    notification_service::send_notification(notification).await
        .map_err(|e| WorkflowError::ExecutionError(format!("发送通知失败: {}", e)))?;
    
    // 返回错误信息
    let mut output = NodeOutput::new();
    output.add_data("preparation_failed", true);
    output.add_data("error_node", error_node);
    output.add_data("error_message", error_message);
    
    Ok(output)
}
```

## 工作流调用集成

以下是如何在固件更新工作流程中集成设备预更新准备流程：

```rust
pub async fn initiate_firmware_update(
    device_id: &str,
    firmware_id: &str,
    options: FirmwareUpdateOptions,
) -> Result<String, ServiceError> {
    // 验证设备和固件
    // ...
    
    // 创建工作流实例
    let workflow_instance_id = generate_unique_id();
    
    // 首先创建设备预更新准备工作流
    let pre_update_workflow = create_device_pre_update_workflow();
    
    // 设置工作流参数
    let mut workflow_params = HashMap::new();
    workflow_params.insert("device_id".to_string(), device_id.to_string());
    workflow_params.insert("firmware_id".to_string(), firmware_id.to_string());
    workflow_params.insert("force_update".to_string(), options.force.to_string());
    workflow_params.insert("skip_verification".to_string(), options.skip_verification.to_string());
    workflow_params.insert("scheduled_time".to_string(), options.scheduled_time.map_or_else(
        || Utc::now().to_rfc3339(),
        |t| t.to_rfc3339()
    ));
    
    // 启动预更新准备工作流
    let pre_update_instance_id = workflow_engine::start_workflow(
        &pre_update_workflow.id,
        &workflow_instance_id,
        workflow_params.clone(),
    ).await?;
    
    // 创建固件更新工作流，并在预更新工作流完成后启动
    let update_workflow = create_firmware_update_workflow();
    
    // 注册工作流完成回调
    workflow_engine::register_completion_callback(
        &pre_update_instance_id,
        Box::new(move |result| {
            if result.is_success() {
                // 预更新准备成功，启动实际更新工作流
                workflow_engine::start_workflow(
                    &update_workflow.id,
                    &(workflow_instance_id.clone() + "_update"),
                    workflow_params.clone(),
                ).await?;
            } else {
                // 预更新准备失败，记录错误并通知
                log::error!(
                    "设备 {} 预更新准备失败，无法继续更新: {}", 
                    device_id, 
                    result.error.unwrap_or_default()
                );
                
                // 通知用户更新失败
                // ...
            }
            
            Ok(())
        }),
    ).await?;
    
    // 返回工作流实例ID
    Ok(workflow_instance_id)
}
```

## 设备预更新准备工作流的好处

1. **提高更新成功率**：通过预先检查设备状态、电池电量和存储空间，减少更新过程中的失败率

2. **数据安全保障**：自动备份关键数据，避免更新失败导致的数据丢失

3. **状态监控与恢复**：详细记录预更新各阶段的状态，便于问题诊断和恢复

4. **设备资源考量**：考虑到电池供电设备的特殊需求，确保更新过程不会因电量不足而中断

5. **用户体验优化**：在更新前完成所有准备工作，减少用户等待时间，提供更可靠的更新体验

接下来，我们可以继续讨论设备更新状态跟踪机制和更新后的验证流程，您希望我继续哪个部分？

## 设备更新状态跟踪机制

设备更新状态跟踪是IoT系统中确保固件更新透明度和可靠性的关键组成部分。下面我们将设计一个全面的状态跟踪机制。

## 更新状态数据模型

```rust
/// 设备更新状态枚举
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum UpdateStatus {
    NotStarted,             // 更新尚未开始
    PreparationInProgress,  // 预更新准备进行中
    PreparationFailed,      // 预更新准备失败
    ReadyForUpdate,         // 准备就绪，可以更新
    DownloadingFirmware,    // 正在下载固件
    DownloadFailed,         // 固件下载失败
    VerifyingFirmware,      // 正在验证固件
    VerificationFailed,     // 固件验证失败
    InstallingFirmware,     // 正在安装固件
    InstallationFailed,     // 安装失败
    Rebooting,              // 设备重启中
    VerifyingInstallation,  // 验证安装结果
    UpdateSuccessful,       // 更新成功
    UpdateFailed,           // 更新最终失败
    RollingBack,            // 正在回滚
    RollbackSuccessful,     // 回滚成功
    RollbackFailed,         // 回滚失败
}

/// 更新记录实体
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeviceUpdateRecord {
    pub id: String,
    pub device_id: String,
    pub firmware_id: String,
    pub workflow_instance_id: String,
    pub status: UpdateStatus,
    pub progress_percentage: f32,
    pub started_at: DateTime<Utc>,
    pub completed_at: Option<DateTime<Utc>>,
    pub error_message: Option<String>,
    pub backup_id: Option<String>,
    pub current_step: String,
    pub steps_history: Vec<UpdateStepRecord>,
    pub estimated_completion_time: Option<DateTime<Utc>>,
    pub initiated_by: String,
    pub is_scheduled: bool,
    pub scheduled_time: Option<DateTime<Utc>>,
    pub metadata: HashMap<String, String>,
}

/// 更新步骤记录
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UpdateStepRecord {
    pub step_id: String,
    pub step_name: String,
    pub status: StepStatus,
    pub started_at: DateTime<Utc>,
    pub completed_at: Option<DateTime<Utc>>,
    pub duration_seconds: Option<u64>,
    pub error_message: Option<String>,
    pub retry_count: u32,
    pub output: Option<HashMap<String, Value>>,
}

/// 步骤状态枚举
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum StepStatus {
    NotStarted,
    InProgress,
    Completed,
    Failed,
    Skipped,
}
```

## 更新状态管理服务

```rust
pub struct UpdateStatusService {
    update_repository: Arc<dyn UpdateRepository>,
    device_repository: Arc<dyn DeviceRepository>,
    notification_service: Arc<dyn NotificationService>,
    telemetry_service: Arc<dyn TelemetryService>,
}

impl UpdateStatusService {
    pub fn new(
        update_repository: Arc<dyn UpdateRepository>,
        device_repository: Arc<dyn DeviceRepository>,
        notification_service: Arc<dyn NotificationService>,
        telemetry_service: Arc<dyn TelemetryService>,
    ) -> Self {
        Self {
            update_repository,
            device_repository,
            notification_service,
            telemetry_service,
        }
    }
    
    /// 创建新的更新记录
    pub async fn create_update_record(
        &self,
        device_id: &str,
        firmware_id: &str,
        workflow_instance_id: &str,
        initiated_by: &str,
        scheduled_time: Option<DateTime<Utc>>,
    ) -> Result<String, ServiceError> {
        let now = Utc::now();
        
        let update_record = DeviceUpdateRecord {
            id: generate_unique_id(),
            device_id: device_id.to_string(),
            firmware_id: firmware_id.to_string(),
            workflow_instance_id: workflow_instance_id.to_string(),
            status: if scheduled_time.is_some() && scheduled_time.unwrap() > now {
                UpdateStatus::NotStarted
            } else {
                UpdateStatus::PreparationInProgress
            },
            progress_percentage: 0.0,
            started_at: now,
            completed_at: None,
            error_message: None,
            backup_id: None,
            current_step: "初始化中".to_string(),
            steps_history: Vec::new(),
            estimated_completion_time: self.calculate_estimated_completion_time(device_id, firmware_id).await?,
            initiated_by: initiated_by.to_string(),
            is_scheduled: scheduled_time.is_some(),
            scheduled_time,
            metadata: HashMap::new(),
        };
        
        // 保存更新记录
        let record_id = self.update_repository.save_update_record(&update_record).await?;
        
        // 更新设备状态
        self.device_repository.update_device_update_status(
            device_id, 
            if update_record.is_scheduled {
                UpdateStatus::NotStarted
            } else {
                UpdateStatus::PreparationInProgress
            }
        ).await?;
        
        // 发送通知
        if update_record.is_scheduled {
            self.send_scheduled_update_notification(&update_record).await?;
        } else {
            self.send_update_started_notification(&update_record).await?;
        }
        
        Ok(record_id)
    }
    
    /// 更新状态
    pub async fn update_status(
        &self,
        update_id: &str,
        status: UpdateStatus,
        progress: Option<f32>,
        current_step: Option<String>,
        error_message: Option<String>,
    ) -> Result<(), ServiceError> {
        // 获取当前记录
        let mut record = self.update_repository.get_update_record(update_id).await?;
        
        // 更新状态
        record.status = status;
        
        // 更新进度
        if let Some(progress) = progress {
            record.progress_percentage = progress;
        }
        
        // 更新当前步骤
        if let Some(step) = current_step {
            record.current_step = step;
        }
        
        // 更新错误信息
        if let Some(error) = error_message {
            record.error_message = Some(error);
        }
        
        // 如果是最终状态，设置完成时间
        if self.is_final_status(&status) {
            record.completed_at = Some(Utc::now());
        }
        
        // 保存更新后的记录
        self.update_repository.update_record(&record).await?;
        
        // 更新设备状态
        self.device_repository.update_device_update_status(&record.device_id, status.clone()).await?;
        
        // 发送状态更新通知
        self.send_status_update_notification(&record).await?;
        
        // 记录遥测数据
        self.log_update_telemetry(&record).await?;
        
        Ok(())
    }
    
    /// 添加步骤记录
    pub async fn add_step_record(
        &self,
        update_id: &str,
        step_record: UpdateStepRecord,
    ) -> Result<(), ServiceError> {
        let mut record = self.update_repository.get_update_record(update_id).await?;
        
        // 添加步骤记录
        record.steps_history.push(step_record.clone());
        
        // 如果步骤完成，计算进度百分比
        if step_record.status == StepStatus::Completed {
            let total_steps = self.get_total_steps_for_update(&record).await?;
            let completed_steps = record.steps_history.iter()
                .filter(|s| s.status == StepStatus::Completed)
                .count();
            
            record.progress_percentage = (completed_steps as f32 / total_steps as f32) * 100.0;
        }
        
        // 更新当前步骤
        if step_record.status == StepStatus::InProgress {
            record.current_step = step_record.step_name.clone();
        }
        
        // 保存更新后的记录
        self.update_repository.update_record(&record).await?;
        
        Ok(())
    }
    
    /// 记录备份ID
    pub async fn record_backup_id(
        &self,
        update_id: &str,
        backup_id: &str,
    ) -> Result<(), ServiceError> {
        let mut record = self.update_repository.get_update_record(update_id).await?;
        record.backup_id = Some(backup_id.to_string());
        self.update_repository.update_record(&record).await?;
        Ok(())
    }
    
    /// 获取设备最新的更新记录
    pub async fn get_latest_device_update(
        &self,
        device_id: &str,
    ) -> Result<Option<DeviceUpdateRecord>, ServiceError> {
        self.update_repository.get_latest_device_update(device_id).await
    }
    
    /// 获取设备的所有更新记录
    pub async fn get_device_update_history(
        &self,
        device_id: &str,
        limit: usize,
        offset: usize,
    ) -> Result<Vec<DeviceUpdateRecord>, ServiceError> {
        self.update_repository.get_device_update_history(device_id, limit, offset).await
    }
    
    /// 计算预计完成时间
    async fn calculate_estimated_completion_time(
        &self,
        device_id: &str,
        firmware_id: &str,
    ) -> Result<Option<DateTime<Utc>>, ServiceError> {
        // 获取设备历史更新的平均时间
        let avg_duration = self.update_repository.get_average_update_duration(device_id).await?;
        
        // 获取固件大小和复杂度
        let firmware = firmware_repository::get_firmware(firmware_id).await?;
        
        // 获取设备连接类型和网络状况
        let device = self.device_repository.get_device(device_id).await?;
        let network_status = self.telemetry_service.get_latest_network_status(device_id).await?;
        
        // 基于历史数据、固件大小和网络状况估算时间
        let base_duration = avg_duration.unwrap_or(chrono::Duration::minutes(15));
        
        // 调整时间基于固件大小
        let size_factor = (firmware.size_bytes as f64 / 1_000_000.0).max(1.0);
        
        // 调整时间基于网络状况
        let network_factor = match (device.connection_type, network_status.signal_strength) {
            (ConnectionType::Ethernet, _) => 0.8,
            (ConnectionType::WiFi, s) if s > 80.0 => 1.0,
            (ConnectionType::WiFi, s) if s > 50.0 => 1.2,
            (ConnectionType::WiFi, _) => 1.5,
            (ConnectionType::Cellular, s) if s > 80.0 => 1.3,
            (ConnectionType::Cellular, s) if s > 50.0 => 1.7,
            (ConnectionType::Cellular, _) => 2.2,
            _ => 1.5,
        };
        
        // 计算最终预计时间
        let estimated_seconds = (base_duration.num_seconds() as f64 * size_factor * network_factor) as i64;
        let estimated_duration = chrono::Duration::seconds(estimated_seconds);
        
        Ok(Some(Utc::now() + estimated_duration))
    }
    
    // 辅助方法
    fn is_final_status(&self, status: &UpdateStatus) -> bool {
        matches!(
            status,
            UpdateStatus::UpdateSuccessful | 
            UpdateStatus::UpdateFailed | 
            UpdateStatus::RollbackSuccessful |
            UpdateStatus::RollbackFailed
        )
    }
    
    async fn get_total_steps_for_update(&self, record: &DeviceUpdateRecord) -> Result<usize, ServiceError> {
        // 可以从工作流定义中获取总步骤数
        // 简化实现，实际应从工作流系统获取
        let base_steps = 10; // 基本步骤数
        
        // 获取固件信息，判断是否有额外步骤
        let firmware = firmware_repository::get_firmware(&record.firmware_id).await?;
        let extra_steps = if firmware.requires_special_handling { 2 } else { 0 };
        
        Ok(base_steps + extra_steps)
    }
    
    async fn send_status_update_notification(&self, record: &DeviceUpdateRecord) -> Result<(), ServiceError> {
        // 根据不同状态发送不同的通知
        let (level, title, message) = match record.status {
            UpdateStatus::ReadyForUpdate => (
                NotificationLevel::Info,
                format!("设备 {} 准备就绪，可以开始更新", record.device_id),
                "设备已完成预更新准备，可以开始固件安装过程。".to_string()
            ),
            UpdateStatus::UpdateSuccessful => (
                NotificationLevel::Success,
                format!("设备 {} 更新成功", record.device_id),
                format!("固件 {} 已成功安装并验证。", record.firmware_id)
            ),
            UpdateStatus::UpdateFailed => (
                NotificationLevel::Error,
                format!("设备 {} 更新失败", record.device_id),
                format!("在 {} 阶段失败: {}",
                    record.current_step,
                    record.error_message.clone().unwrap_or("未知错误".to_string())
                )
            ),
            UpdateStatus::RollingBack => (
                NotificationLevel::Warning,
                format!("设备 {} 正在回滚", record.device_id),
                "更新失败，正在恢复到之前的固件版本。".to_string()
            ),
            UpdateStatus::RollbackSuccessful => (
                NotificationLevel::Warning,
                format!("设备 {} 已成功回滚", record.device_id),
                "更新失败，但已成功恢复到之前的固件版本。".to_string()
            ),
            UpdateStatus::RollbackFailed => (
                NotificationLevel::Error,
                format!("设备 {} 回滚失败", record.device_id),
                "更新失败，并且无法恢复到之前的固件版本。设备可能需要手动干预。".to_string()
            ),
            _ => return Ok(()), // 其他状态不发送通知
        };
        
        let notification = NotificationRequest {
            level,
            category: NotificationCategory::DeviceUpdate,
            title,
            message,
            related_entity: Some(EntityReference {
                entity_type: EntityType::Device,
                entity_id: record.device_id.clone(),
            }),
            actions: vec![
                NotificationAction {
                    label: "查看详情".to_string(),
                    action_type: ActionType::Url,
                    action_data: format!("/devices/{}/updates/{}", record.device_id, record.id),
                },
            ],
            expiration: Some(Utc::now() + Duration::days(3)),
        };
        
        self.notification_service.send_notification(notification).await?;
        
        Ok(())
    }
    
    async fn send_scheduled_update_notification(&self, record: &DeviceUpdateRecord) -> Result<(), ServiceError> {
        if let Some(scheduled_time) = record.scheduled_time {
            let notification = NotificationRequest {
                level: NotificationLevel::Info,
                category: NotificationCategory::DeviceUpdate,
                title: format!("设备 {} 更新已计划", record.device_id),
                message: format!(
                    "设备将在 {} 自动更新到固件版本 {}。",
                    scheduled_time.format("%Y-%m-%d %H:%M"),
                    record.firmware_id
                ),
                related_entity: Some(EntityReference {
                    entity_type: EntityType::Device,
                    entity_id: record.device_id.clone(),
                }),
                actions: vec![
                    NotificationAction {
                        label: "查看详情".to_string(),
                        action_type: ActionType::Url,
                        action_data: format!("/devices/{}/updates/{}", record.device_id, record.id),
                    },
                    NotificationAction {
                        label: "取消更新".to_string(),
                        action_type: ActionType::Api,
                        action_data: format!("/api/devices/{}/updates/{}/cancel", record.device_id, record.id),
                    },
                ],
                expiration: Some(scheduled_time),
            };
            
            self.notification_service.send_notification(notification).await?;
        }
        
        Ok(())
    }
    
    async fn send_update_started_notification(&self, record: &DeviceUpdateRecord) -> Result<(), ServiceError> {
        let notification = NotificationRequest {
            level: NotificationLevel::Info,
            category: NotificationCategory::DeviceUpdate,
            title: format!("设备 {} 更新已开始", record.device_id),
            message: format!(
                "正在准备更新设备到固件版本 {}。预计完成时间: {}。",
                record.firmware_id,
                record.estimated_completion_time
                    .map_or("未知".to_string(), |t| t.format("%H:%M:%S").to_string())
            ),
            related_entity: Some(EntityReference {
                entity_type: EntityType::Device,
                entity_id: record.device_id.clone(),
            }),
            actions: vec![
                NotificationAction {
                    label: "查看进度".to_string(),
                    action_type: ActionType::Url,
                    action_data: format!("/devices/{}/updates/{}", record.device_id, record.id),
                },
            ],
            expiration: record.estimated_completion_time.map(|t| t + Duration::hours(1)),
        };
        
        self.notification_service.send_notification(notification).await?;
        
        Ok(())
    }
    
    async fn log_update_telemetry(&self, record: &DeviceUpdateRecord) -> Result<(), ServiceError> {
        // 记录更新进度作为设备遥测数据
        let telemetry = TelemetryData {
            device_id: record.device_id.clone(),
            timestamp: Utc::now(),
            measurements: vec![
                Measurement {
                    name: "update_progress".to_string(),
                    value: record.progress_percentage as f64,
                    unit: Some("percent".to_string()),
                },
                Measurement {
                    name: "update_status".to_string(),
                    value: 0.0, // 占位值
                    unit: None,
                    text_value: Some(format!("{:?}", record.status)),
                },
            ],
            metadata: HashMap::from([
                ("update_id".to_string(), record.id.clone()),
                ("firmware_id".to_string(), record.firmware_id.clone()),
                ("current_step".to_string(), record.current_step.clone()),
            ]),
        };
        
        self.telemetry_service.save_telemetry(telemetry).await?;
        
        Ok(())
    }
}
```

## 更新后验证流程

更新后验证是确保设备固件更新后正常运行的关键步骤。我们将设计一个全面的验证流程，确保更新成功并且设备功能正常。

## 更新后验证工作流定义

```rust
pub fn create_post_update_verification_workflow() -> WorkflowDefinition {
    let mut workflow = WorkflowDefinition::new(
        "post_update_verification_workflow",
        "更新后验证流程",
        "在固件更新后验证设备功能和性能的工作流程",
    );

    // 添加工作流节点
    workflow.add_node(WorkflowNode {
        id: "verify_device_online".to_string(),
        name: "验证设备在线".to_string(),
        node_type: NodeType::Function,
        function: "verify_device_online".to_string(),
        next_nodes: vec!["verify_firmware_version".to_string()],
        error_node: Some("handle_device_offline".to_string()),
        timeout_seconds: 300, // 5分钟
    });

    workflow.add_node(WorkflowNode {
        id: "verify_firmware_version".to_string(),
        name: "验证固件版本".to_string(),
        node_type: NodeType::Function,
        function: "verify_firmware_version".to_string(),
        next_nodes: vec!["verify_core_functions".to_string()],
        error_node: Some("handle_firmware_mismatch".to_string()),
        timeout_seconds: 60,
    });

    workflow.add_node(WorkflowNode {
        id: "verify_core_functions".to_string(),
        name: "验证核心功能".to_string(),
        node_type: NodeType::Function,
        function: "verify_core_functions".to_string(),
        next_nodes: vec!["collect_performance_metrics".to_string()],
        error_node: Some("handle_function_verification_failure".to_string()),
        timeout_seconds: 180,
    });

    workflow.add_node(WorkflowNode {
        id: "collect_performance_metrics".to_string(),
        name: "收集性能指标".to_string(),
        node_type: NodeType::Function,
        function: "collect_performance_metrics".to_string(),
        next_nodes: vec!["analyze_metrics".to_string()],
        error_node: None, // 允许性能指标收集失败，但继续执行
        timeout_seconds: 120,
    });

    workflow.add_node(WorkflowNode {
        id: "analyze_metrics".to_string(),
        name: "分析性能指标".to_string(),
        node_type: NodeType::Function,
        function: "analyze_performance_metrics".to_string(),
        next_nodes: vec!["restore_device_settings".to_string()],
        error_node: Some("handle_performance_issues".to_string()),
        timeout_seconds: 60,
    });

    workflow.add_node(WorkflowNode {
        id: "restore_device_settings".to_string(),
        name: "恢复设备设置".to_string(),
        node_type: NodeType::Function,
        function: "restore_device_settings".to_string(),
        next_nodes: vec!["verify_connectivity".to_string()],
        error_node: Some("handle_settings_restore_failure".to_string()),
        timeout_seconds: 120,
    });

    workflow.add_node(WorkflowNode {
        id: "verify_connectivity".to_string(),
        name: "验证连接性".to_string(),
        node_type: NodeType::Function,
        function: "verify_connectivity".to_string(),
        next_nodes: vec!["mark_update_successful".to_string()],
        error_node: Some("handle_connectivity_issues".to_string()),
        timeout_seconds: 120,
    });

    workflow.add_node(WorkflowNode {
        id: "mark_update_successful".to_string(),
        name: "标记更新成功".to_string(),
        node_type: NodeType::Function,
        function: "mark_update_successful".to_string(),
        next_nodes: vec!["end".to_string()],
        error_node: None,
        timeout_seconds: 30,
    });

    // 添加错误处理节点
    workflow.add_node(WorkflowNode {
        id: "handle_device_offline".to_string(),
        name: "处理设备离线情况".to_string(),
        node_type: NodeType::Function,
        function: "handle_device_offline".to_string(),
        next_nodes: vec!["retry_verification".to_string()],
        error_node: None,
        timeout_seconds: 60,
    });
    
    workflow.add_node(WorkflowNode {
        id: "retry_verification".to_string(),
        name: "重试验证".to_string(),
        node_type: NodeType::Decision,
        function: "should_retry_verification".to_string(),
        next_nodes: vec!["verify_device_online".to_string(), "initiate_rollback".to_string()],
        error_node: None,
        timeout_seconds: 30,
    });

    workflow.add_node(WorkflowNode {
        id: "initiate_rollback".to_string(),
        name: "启动回滚流程".to_string(),
        node_type: NodeType::Function,
        function: "initiate_rollback".to_string(),
        next_nodes: vec!["end".to_string()],
        error_node: None,
        timeout_seconds: 60,
    });

    // 添加其他错误处理节点...

    workflow.add_node(WorkflowNode {
        id: "end".to_string(),
        name: "结束".to_string(),
        node_type: NodeType::End,
        function: "".to_string(),
        next_nodes: vec![],
        error_node: None,
        timeout_seconds: 0,
    });

    workflow
}
```

## 更新后验证功能实现

下面是与更新后验证工作流相关的功能实现：

```rust
/// 验证设备是否在线
pub async fn verify_device_online(context: &WorkflowContext) -> Result<NodeOutput, WorkflowError> {
    let device_id = context.get_param("device_id")
        .ok_or_else(|| WorkflowError::MissingParameter("device_id".to_string()))?;
    
    let max_attempts = 10;
    let retry_interval_seconds = 30;
    
    for attempt in 1..=max_attempts {
        log::info!("尝试 {}/{} 验证设备 {} 是否在线", attempt, max_attempts, device_id);
        
        // 检查设备连接状态
        match device_service::check_device_online(device_id).await {
            Ok(true) => {
                log::info!("设备 {} 已上线", device_id);
                let mut output = NodeOutput::new();
                output.add_data("device_online", true);
                output.add_data("verification_attempts", attempt);
                return Ok(output);
            },
            Ok(false) => {
                log::info!("设备 {} 仍然离线，等待下一次检查", device_id);
            },
            Err(e) => {
                log::warn!("检查设备 {} 在线状态时发生错误: {}", device_id, e);
            }
        }
        
        if attempt < max_attempts {
            tokio::time::sleep(Duration::from_secs(retry_interval_seconds)).await;
        }
    }
    
    Err(WorkflowError::ExecutionError(format!(
        "在 {} 次尝试后，设备 {} 仍然未上线",
        max_attempts, device_id
    )))
}

/// 验证固件版本是否匹配
pub async fn verify_firmware_version(context: &WorkflowContext) -> Result<NodeOutput, WorkflowError> {
    let device_id = context.get_param("device_id")
        .ok_or_else(|| WorkflowError::MissingParameter("device_id".to_string()))?;
    
    let expected_firmware_id = context.get_param("firmware_id")
        .ok_or_else(|| WorkflowError::MissingParameter("firmware_id".to_string()))?;
    
    // 获取预期的固件版本
    let expected_firmware = firmware_repository::get_firmware(expected_firmware_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法获取预期固件信息: {}", e)))?;
    
    // 获取设备当前固件版本
    let device_info = device_command_service::get_device_info(device_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法获取设备信息: {}", e)))?;
    
    // 验证固件版本
    if device_info.firmware_version != expected_firmware.version {
        return Err(WorkflowError::ExecutionError(format!(
            "固件版本不匹配。预期: {}，实际: {}",
            expected_firmware.version, device_info.firmware_version
        )));
    }
    
    // 验证固件校验和（如果可用）
    if let (Some(expected_checksum), Some(device_checksum)) = 
        (&expected_firmware.checksum, &device_info.firmware_checksum) {
        if expected_checksum != device_checksum {
            return Err(WorkflowError::ExecutionError(format!(
                "固件校验和不匹配。预期: {}，实际: {}",
                expected_checksum, device_checksum
            )));
        }
    }
    
    let mut output = NodeOutput::new();
    output.add_data("firmware_version_verified", true);
    output.add_data("firmware_version", device_info.firmware_version);
    
    Ok(output)
}

/// 验证设备核心功能
pub async fn verify_core_functions(context: &WorkflowContext) -> Result<NodeOutput, WorkflowError> {
    let device_id = context.get_param("device_id")
        .ok_or_else(|| WorkflowError::MissingParameter("device_id".to_string()))?;
    
    // 获取设备类型和模型，确定需要验证的核心功能
    let device = device_repository::get_device_by_id(device_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法获取设备信息: {}", e)))?;
    
    // 获取此设备类型的核心功能检查列表
    let verification_checks = device_verification_service::get_core_function_checks(
        &device.device_type,
        &device.model
    ).await.map_err(|e| WorkflowError::ExecutionError(format!("无法获取核心功能检查列表: {}", e)))?;
    
    let mut verification_results = Vec::new();
    let mut failed_checks = Vec::new();
    
    // 执行每项功能验证
    for check in verification_checks {
        log::info!("执行功能检查 '{}' 为设备 {}", check.name, device_id);
        
        match device_verification_service::execute_function_check(device_id, &check).await {
            Ok(result) => {
                verification_results.push((check.name.clone(), "成功".to_string()));
                log::info!("设备 {} 的功能检查 '{}' 通过", device_id, check.name);
            },
            Err(e) => {
                let error_msg = format!("失败: {}", e);
                verification_results.push((check.name.clone(), error_msg.clone()));
                failed_checks.push((check.name.clone(), error_msg));
                log::warn!("设备 {} 的功能检查 '{}' 失败: {}", device_id, check.name, e);
            }
        }
    }
    
    let mut output = NodeOutput::new();
    output.add_data("verification_results", verification_results);
    
    if !failed_checks.is_empty() {
        return Err(WorkflowError::ExecutionError(format!(
            "核心功能验证失败。失败项: {}",
            serde_json::to_string(&failed_checks).unwrap_or_default()
        )));
    }
    
    output.add_data("core_functions_verified", true);
    Ok(output)
}

/// 收集设备性能指标
pub async fn collect_performance_metrics(context: &WorkflowContext) -> Result<NodeOutput, WorkflowError> {
    let device_id = context.get_param("device_id")
        .ok_or_else(|| WorkflowError::MissingParameter("device_id".to_string()))?;
    
    log::info!("开始收集设备 {} 的性能指标", device_id);
    
    // 定义要收集的性能指标
    let metrics = vec![
        "cpu_usage", "memory_usage", "storage_usage", "network_latency",
        "battery_drain_rate", "signal_strength", "response_time"
    ];
    
    let mut collected_metrics = HashMap::new();
    let mut failed_metrics = Vec::new();
    
    // 收集各项指标
    for metric in metrics {
        match performance_service::collect_metric(device_id, metric).await {
            Ok(value) => {
                collected_metrics.insert(metric.to_string(), value);
                log::info!("设备 {} 的 {} 指标值: {}", device_id, metric, value);
            },
            Err(e) => {
                log::warn!("无法收集设备 {} 的 {} 指标: {}", device_id, metric, e);
                failed_metrics.push((metric.to_string(), e.to_string()));
            }
        }
    }
    
    // 获取更新前基准性能数据
    let baseline_metrics = match context.get_data("baseline_performance_metrics") {
        Some(baseline) => baseline.clone(),
        None => {
            log::warn!("未找到设备 {} 的基准性能数据，将使用默认值", device_id);
            // 获取设备类型的默认性能基准
            performance_service::get_default_performance_baseline(device_id).await
                .map_err(|e| WorkflowError::ExecutionError(format!("无法获取性能基准数据: {}", e)))?
        }
    };
    
    let mut output = NodeOutput::new();
    output.add_data("performance_metrics", collected_metrics);
    output.add_data("baseline_metrics", baseline_metrics);
    output.add_data("failed_metrics", failed_metrics);
    
    Ok(output)
}

/// 分析性能指标
pub async fn analyze_performance_metrics(context: &WorkflowContext) -> Result<NodeOutput, WorkflowError> {
    // 获取已收集的性能指标
    let metrics: HashMap<String, f64> = context.get_data("performance_metrics")
        .ok_or_else(|| WorkflowError::MissingParameter("performance_metrics".to_string()))?
        .clone();
    
    // 获取基准性能指标
    let baseline: HashMap<String, f64> = context.get_data("baseline_metrics")
        .ok_or_else(|| WorkflowError::MissingParameter("baseline_metrics".to_string()))?
        .clone();
    
    let mut analysis_results = HashMap::new();
    let mut performance_issues = Vec::new();
    
    // 设定可接受的性能变化阈值（百分比）
    let threshold = 20.0; // 20%
    
    // 分析各项指标
    for (metric, current_value) in &metrics {
        if let Some(baseline_value) = baseline.get(metric) {
            // 计算性能变化百分比
            let change_percent = (*current_value - *baseline_value) / *baseline_value * 100.0;
            
            // 记录分析结果
            analysis_results.insert(
                metric.clone(),
                PerformanceAnalysis {
                    name: metric.clone(),
                    current_value: *current_value,
                    baseline_value: *baseline_value,
                    change_percent,
                    is_degraded: metric_is_degraded(metric, change_percent, threshold),
                }
            );
            
            // 检查是否出现性能下降
            if metric_is_degraded(metric, change_percent, threshold) {
                performance_issues.push(PerformanceIssue {
                    metric: metric.clone(),
                    current_value: *current_value,
                    baseline_value: *baseline_value,
                    change_percent,
                    severity: if change_percent.abs() > threshold * 2.0 {
                        IssueSeverity::High
                    } else {
                        IssueSeverity::Medium
                    },
                });
            }
        }
    }
    
    let mut output = NodeOutput::new();
    output.add_data("performance_analysis", analysis_results);
    output.add_data("performance_issues", performance_issues.clone());
    
    // 检查是否有严重性能问题
    let has_critical_issues = performance_issues.iter()
        .any(|issue| issue.severity == IssueSeverity::High);
    
    if has_critical_issues {
        return Err(WorkflowError::ExecutionError(format!(
            "设备性能存在严重下降。发现 {} 个性能问题",
            performance_issues.len()
        )));
    }
    
    output.add_data("performance_acceptable", true);
    output.add_data("has_minor_issues", !performance_issues.is_empty());
    
    Ok(output)
}

/// 确定指标是否降级
fn metric_is_degraded(metric: &str, change_percent: f64, threshold: f64) -> bool {
    // 对于不同指标，性能下降的方向不同
    match metric {
        // 这些指标增加表示性能下降
        "cpu_usage" | "memory_usage" | "storage_usage" | 
        "battery_drain_rate" | "network_latency" | "response_time" =>
            change_percent > threshold,
        
        // 这些指标减少表示性能下降
        "signal_strength" | "throughput" | "battery_life" =>
            change_percent < -threshold,
            
        // 其他指标使用默认规则
        _ => change_percent.abs() > threshold,
    }
}

/// 恢复设备设置
pub async fn restore_device_settings(context: &WorkflowContext) -> Result<NodeOutput, WorkflowError> {
    let device_id = context.get_param("device_id")
        .ok_or_else(|| WorkflowError::MissingParameter("device_id".to_string()))?;
    
    let backup_id = context.get_param("backup_id")
        .ok_or_else(|| WorkflowError::MissingParameter("backup_id".to_string()))?;
    
    log::info!("开始恢复设备 {} 的设置，使用备份 {}", device_id, backup_id);
    
    // 获取备份信息
    let backup = backup_service::get_backup(backup_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法获取备份信息: {}", e)))?;
    
    // 仅恢复设置，不恢复用户数据
    let restore_request = RestoreRequest {
        device_id: device_id.to_string(),
        backup_id: backup_id.to_string(),
        restore_type: RestoreType::SettingsOnly,
        ignore_version_mismatch: true,
    };
    
    // 执行设置恢复
    let restore_result = backup_service::restore_from_backup(restore_request).await
        .map_err(|e| WorkflowError::ExecutionError(format!("恢复设置失败: {}", e)))?;
    
    if !restore_result.success {
        return Err(WorkflowError::ExecutionError(format!(
            "恢复设置失败: {}",
            restore_result.error.unwrap_or_default()
        )));
    }
    
    // 验证关键设置是否已恢复
    let settings_verified = device_command_service::verify_settings_restored(device_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法验证设置恢复: {}", e)))?;
    
    if !settings_verified {
        return Err(WorkflowError::ExecutionError(
            "设备设置未正确恢复".to_string()
        ));
    }
    
    let mut output = NodeOutput::new();
    output.add_data("settings_restored", true);
    output.add_data("restore_timestamp", Utc::now().to_rfc3339());
    
    Ok(output)
}

/// 验证设备连接性
pub async fn verify_connectivity(context: &WorkflowContext) -> Result<NodeOutput, WorkflowError> {
    let device_id = context.get_param("device_id")
        .ok_or_else(|| WorkflowError::MissingParameter("device_id".to_string()))?;
    
    log::info!("验证设备 {} 的连接性", device_id);
    
    // 获取设备连接类型
    let device = device_repository::get_device_by_id(device_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法获取设备信息: {}", e)))?;
    
    // 验证各种连接
    let mut connectivity_results = HashMap::new();
    let mut failed_checks = Vec::new();
    
    // 检查基本连接
    match device_command_service::check_base_connectivity(device_id).await {
        Ok(true) => {
            connectivity_results.insert("basic_connectivity".to_string(), true);
        },
        Ok(false) => {
            connectivity_results.insert("basic_connectivity".to_string(), false);
            failed_checks.push(("basic_connectivity".to_string(), "基本连接测试失败".to_string()));
        },
        Err(e) => {
            connectivity_results.insert("basic_connectivity".to_string(), false);
            failed_checks.push(("basic_connectivity".to_string(), e.to_string()));
        }
    }
    
    // 根据设备类型检查不同的连接类型
    if device.has_wifi {
        match device_command_service::check_wifi_connectivity(device_id).await {
            Ok(status) => {
                connectivity_results.insert("wifi_connectivity".to_string(), status.is_connected);
                if !status.is_connected {
                    failed_checks.push((
                        "wifi_connectivity".to_string(),
                        format!("WiFi连接失败，信号强度: {}%, 状态: {}", status.signal_strength, status.status_message)
                    ));
                }
            },
            Err(e) => {
                connectivity_results.insert("wifi_connectivity".to_string(), false);
                failed_checks.push(("wifi_connectivity".to_string(), e.to_string()));
            }
        }
    }
    
    // 其他连接类型检查（蓝牙、LoRa、蜂窝等）
    // ...
    
    // 检查云连接
    match device_command_service::check_cloud_connectivity(device_id).await {
        Ok(status) => {
            connectivity_results.insert("cloud_connectivity".to_string(), status.is_connected);
            if !status.is_connected {
                failed_checks.push((
                    "cloud_connectivity".to_string(),
                    format!("云连接失败: {}", status.status_message)
                ));
            }
        },
        Err(e) => {
            connectivity_results.insert("cloud_connectivity".to_string(), false);
            failed_checks.push(("cloud_connectivity".to_string(), e.to_string()));
        }
    }
    
    let mut output = NodeOutput::new();
    output.add_data("connectivity_results", connectivity_results);
    
    if !failed_checks.is_empty() {
        return Err(WorkflowError::ExecutionError(format!(
            "连接性验证失败。失败项: {}",
            serde_json::to_string(&failed_checks).unwrap_or_default()
        )));
    }
    
    output.add_data("connectivity_verified", true);
    Ok(output)
}

/// 标记更新成功
pub async fn mark_update_successful(context: &WorkflowContext) -> Result<NodeOutput, WorkflowError> {
    let device_id = context.get_param("device_id")
        .ok_or_else(|| WorkflowError::MissingParameter("device_id".to_string()))?;
    
    let update_id = context.get_param("update_id")
        .ok_or_else(|| WorkflowError::MissingParameter("update_id".to_string()))?;
    
    // 更新设备状态
    device_repository::update_device_update_status(device_id, UpdateStatus::UpdateSuccessful).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法更新设备状态: {}", e)))?;
    
    // 更新固件记录
    let update_service = UpdateStatusService::new(
        Arc::new(update_repository::get_repository()),
        Arc::new(device_repository::get_repository()),
        Arc::new(notification_service::get_service()),
        Arc::new(telemetry_service::get_service()),
    );
    
    update_service.update_status(
        update_id,
        UpdateStatus::UpdateSuccessful,
        Some(100.0),
        Some("更新完成并验证成功".to_string()),
        None,
    ).await.map_err(|e| WorkflowError::ExecutionError(format!("无法更新更新状态: {}", e)))?;
    
    // 获取更新详情
    let update_record = update_service.get_update_record(update_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法获取更新记录: {}", e)))?;
    
    // 发送成功通知
    let device = device_repository::get_device_by_id(device_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法获取设备信息: {}", e)))?;
    
    let firmware = firmware_repository::get_firmware(&update_record.firmware_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法获取固件信息: {}", e)))?;
    
    // 发送详细的成功更新通知
    let notification = NotificationRequest {
        level: NotificationLevel::Success,
        category: NotificationCategory::DeviceUpdate,
        title: format!("设备 {} 更新成功", device.name),
        message: format!(
            "设备已成功更新到固件版本 {}。所有功能验证和性能检查均已通过。",
            firmware.version
        ),
        related_entity: Some(EntityReference {
            entity_type: EntityType::Device,
            entity_id: device_id.to_string(),
        }),
        actions: vec![
            NotificationAction {
                label: "查看详情".to_string(),
                action_type: ActionType::Url,
                action_data: format!("/devices/{}/updates/{}", device_id, update_id),
            },
        ],
        expiration: Some(Utc::now() + Duration::days(7)),
    };
    
    notification_service::send_notification(notification).await
        .map_err(|e| WorkflowError::ExecutionError(format!("发送通知失败: {}", e)))?;
    
    let mut output = NodeOutput::new();
    output.add_data("update_successful", true);
    output.add_data("completion_time", Utc::now().to_rfc3339());
    
    Ok(output)
}

/// 处理设备离线情况
pub async fn handle_device_offline(context: &WorkflowContext) -> Result<NodeOutput, WorkflowError> {
    let device_id = context.get_param("device_id")
        .ok_or_else(|| WorkflowError::MissingParameter("device_id".to_string()))?;
    
    let update_id = context.get_param("update_id")
        .ok_or_else(|| WorkflowError::MissingParameter("update_id".to_string()))?;
    
    // 记录设备离线事件
    log::warn!("设备 {} 在更新后验证时离线", device_id);
    
    // 获取当前重试次数
    let retry_count = context.get_data("offline_retry_count")
        .map(|v| v.clone())
        .unwrap_or(0);
    
    let mut output = NodeOutput::new();
    output.add_data("offline_retry_count", retry_count + 1);
    output.add_data("last_offline_time", Utc::now().to_rfc3339());
    
    // 发送设备离线警告通知
    let notification = NotificationRequest {
        level: NotificationLevel::Warning,
        category: NotificationCategory::DeviceUpdate,
        title: format!("设备 {} 更新后离线", device_id),
        message: format!(
            "设备在固件更新后无法连接。系统将尝试等待设备上线，这可能需要一些时间。"
        ),
        related_entity: Some(EntityReference {
            entity_type: EntityType::Device,
            entity_id: device_id.to_string(),
        }),
        actions: vec![
            NotificationAction {
                label: "查看详情".to_string(),
                action_type: ActionType::Url,
                action_data: format!("/devices/{}/updates/{}", device_id, update_id),
            },
        ],
        expiration: Some(Utc::now() + Duration::hours(24)),
    };
    
    notification_service::send_notification(notification).await
        .map_err(|e| WorkflowError::ExecutionError(format!("发送通知失败: {}", e)))?;
    
    Ok(output)
}

/// 决定是否应该重试验证
pub async fn should_retry_verification(context: &WorkflowContext) -> Result<DecisionOutput, WorkflowError> {
    let retry_count: u32 = context.get_data("offline_retry_count")
        .map(|v| v.clone())
        .unwrap_or(0);
    
    let max_retries = 5; // 最大重试次数
    
    if retry_count < max_retries {
        // 继续重试
        Ok(DecisionOutput::new(0))
    } else {
        // 放弃重试，启动回滚
        log::error!("达到最大重试次数 ({}), 将启动固件回滚", max_retries);
        Ok(DecisionOutput::new(1))
    }
}

/// 启动回滚流程
pub async fn initiate_rollback(context: &WorkflowContext) -> Result<NodeOutput, WorkflowError> {
    let device_id = context.get_param("device_id")
        .ok_or_else(|| WorkflowError::MissingParameter("device_id".to_string()))?;
    
    let update_id = context.get_param("update_id")
        .ok_or_else(|| WorkflowError::MissingParameter("update_id".to_string()))?;
    
    let backup_id = context.get_param("backup_id")
        .ok_or_else(|| WorkflowError::MissingParameter("backup_id".to_string()))?;
    
    log::info!("为设备 {} 启动固件回滚流程", device_id);
    
    // 创建回滚请求
    let rollback_request = RollbackRequest {
        device_id: device_id.to_string(),
        update_id: update_id.to_string(),
        backup_id: backup_id.to_string(),
        reason: "设备在固件更新后无法连接或验证失败".to_string(),
        force: true, // 强制回滚
    };
    
    // 启动回滚工作流
    rollback_service::initiate_rollback(rollback_request).await
        .map_err(|e| WorkflowError::ExecutionError(format!("启动回滚失败: {}", e)))?;
    
    // 更新设备状态
    device_repository::update_device_update_status(device_id, UpdateStatus::RollingBack).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法更新设备状态: {}", e)))?;
    
    // 更新更新记录状态
    let update_service = UpdateStatusService::new(
        Arc::new(update_repository::get_repository()),
        Arc::new(device_repository::get_repository()),
        Arc::new(notification_service::get_service()),
        Arc::new(telemetry_service::get_service()),
    );
    
    update_service.update_status(
        update_id,
        UpdateStatus::RollingBack,
        None,
        Some("启动回滚流程".to_string()),
        Some("更新后验证失败，设备离线或功能异常".to_string()),
    ).await.map_err(|e| WorkflowError::ExecutionError(format!("无法更新更新状态: {}", e)))?;
    
    let mut output = NodeOutput::new();
    output.add_data("rollback_initiated", true);
    output.add_data("rollback_time", Utc::now().to_rfc3339());
    
    Ok(output)
}
```

## 固件回滚流程设计

最后，我们将设计固件回滚流程，确保在更新失败或功能异常时能安全地将设备恢复到之前的固件版本。

## 回滚请求和处理流程

```rust
/// 回滚请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RollbackRequest {
    pub device_id: String,
    pub update_id: String,
    pub backup_id: String,
    pub reason: String,
    pub force: bool,
}

/// 回滚服务
pub struct RollbackService {
    device_repository: Arc<dyn DeviceRepository>,
    update_repository: Arc<dyn UpdateRepository>,
    backup_repository: Arc<dyn BackupRepository>,
    workflow_engine: Arc<dyn WorkflowEngine>,
    notification_service: Arc<dyn NotificationService>,
}

impl RollbackService {
    pub fn new(
        device_repository: Arc<dyn DeviceRepository>,
        update_repository: Arc<dyn UpdateRepository>,
        backup_repository: Arc<dyn BackupRepository>,
        workflow_engine: Arc<dyn WorkflowEngine>,
        notification_service: Arc<dyn NotificationService>,
    ) -> Self {
        Self {
            device_repository,
            update_repository,
            backup_repository,
            workflow_engine,
            notification_service,
        }
    }
    
    /// 启动回滚流程
    pub async fn initiate_rollback(&self, request: RollbackRequest) -> Result<String, ServiceError> {
        // 验证设备、更新和备份
        let device = self.device_repository.get_device(&request.device_id).await?;
        let update = self.update_repository.get_update_record(&request.update_id).await?;
        let backup = self.backup_repository.get_backup(&request.backup_id).await?;
        
        // 验证备份与设备匹配
        if backup.device_id != request.device_id {
            return Err(ServiceError::ValidationError(
                format!("备份 ID {} 不属于设备 {}", request.backup_id, request.device_id)
            ));
        }
        
        // 创建回滚工作流实例
        let workflow_def = self.create_rollback_workflow();
        let workflow_instance_id = generate_unique_id();
        
        // 设置工作流参数
        let mut workflow_params = HashMap::new();
        workflow_params.insert("device_id".to_string(), request.device_id.clone());
        workflow_params.insert("update_id".to_string(), request.update_id.clone());
        workflow_params.insert("backup_id".to_string(), request.backup_id.clone());
        workflow_params.insert("reason".to_string(), request.reason.clone());
        workflow_params.insert("force".to_string(), request.force.to_string());
        
        // 启动回滚工作流
        self.workflow_engine.start_workflow(
            &workflow_def.id,
            &workflow_instance_id,
            workflow_params,
        ).await?;
        
        // 通知用户回滚已启动
        let notification = NotificationRequest {
            level: NotificationLevel::Warning,
            category: NotificationCategory::DeviceUpdate,
            title: format!("设备 {} 回滚已启动", device.name),
            message: format!(
                "由于更新验证失败，系统正在将设备回滚到先前的固件版本。原因：{}",
                request.reason
            ),
            related_entity: Some(EntityReference {
                entity_type: EntityType::Device,
                entity_id: request.device_id.clone(),
            }),
            actions: vec![
                NotificationAction {
                    label: "查看详情".to_string(),
                    action_type: ActionType::Url,
                    action_data: format!("/devices/{}/updates/{}", request.device_id, request.update_id),
                },
            ],
            expiration: Some(Utc::now() + Duration::hours(24)),
        };
        
        self.notification_service.send_notification(notification).await?;
        
        Ok(workflow_instance_id)
    }
    
    /// 创建回滚工作流定义
    fn create_rollback_workflow(&self) -> WorkflowDefinition {
        let mut workflow = WorkflowDefinition::new(
            "firmware_rollback_workflow",
            "固件回滚流程",
            "将设备恢复到先前固件版本的工作流",
        );
        
        // 添加工作流节点
        workflow.add_node(WorkflowNode {
            id: "prepare_device_for_rollback".to_string(),
            name: "准备设备回滚".to_string(),
            node_type: NodeType::Function,
            function: "prepare_device_for_rollback".to_string(),
            next_nodes: vec!["check_recovery_mode".to_string()],
            error_node: Some("handle_preparation_error".to_string()),
            timeout_seconds: 180,
        });
        
        workflow.add_node(WorkflowNode {
            id: "check_recovery_mode".to_string(),
            name: "检查恢复模式".to_string(),
            node_type: NodeType::Function,
            function: "check_device_recovery_mode".to_string(),
            next_nodes: vec!["restore_previous_firmware".to_string(), "
```rust
            next_nodes: vec!["restore_previous_firmware".to_string(), "force_recovery_mode".to_string()],
            error_node: Some("handle_recovery_check_error".to_string()),
            timeout_seconds: 120,
        });
        
        workflow.add_node(WorkflowNode {
            id: "force_recovery_mode".to_string(),
            name: "强制进入恢复模式".to_string(),
            node_type: NodeType::Function,
            function: "force_device_recovery_mode".to_string(),
            next_nodes: vec!["restore_previous_firmware".to_string()],
            error_node: Some("handle_recovery_mode_error".to_string()),
            timeout_seconds: 300,
        });
        
        workflow.add_node(WorkflowNode {
            id: "restore_previous_firmware".to_string(),
            name: "恢复之前的固件".to_string(),
            node_type: NodeType::Function,
            function: "restore_previous_firmware".to_string(),
            next_nodes: vec!["wait_for_device_reboot".to_string()],
            error_node: Some("handle_restore_error".to_string()),
            timeout_seconds: 600,
        });
        
        workflow.add_node(WorkflowNode {
            id: "wait_for_device_reboot".to_string(),
            name: "等待设备重启".to_string(),
            node_type: NodeType::Function,
            function: "wait_for_device_reboot".to_string(),
            next_nodes: vec!["restore_device_settings".to_string()],
            error_node: Some("handle_reboot_timeout".to_string()),
            timeout_seconds: 300,
        });
        
        workflow.add_node(WorkflowNode {
            id: "restore_device_settings".to_string(),
            name: "恢复设备设置".to_string(),
            node_type: NodeType::Function,
            function: "restore_device_settings".to_string(),
            next_nodes: vec!["verify_rollback".to_string()],
            error_node: Some("handle_settings_restore_error".to_string()),
            timeout_seconds: 180,
        });
        
        workflow.add_node(WorkflowNode {
            id: "verify_rollback".to_string(),
            name: "验证回滚结果".to_string(),
            node_type: NodeType::Function,
            function: "verify_rollback".to_string(),
            next_nodes: vec!["finalize_rollback".to_string()],
            error_node: Some("handle_verification_error".to_string()),
            timeout_seconds: 180,
        });
        
        workflow.add_node(WorkflowNode {
            id: "finalize_rollback".to_string(),
            name: "完成回滚流程".to_string(),
            node_type: NodeType::Function,
            function: "finalize_rollback".to_string(),
            next_nodes: vec!["end".to_string()],
            error_node: None,
            timeout_seconds: 60,
        });
        
        // 添加错误处理节点
        workflow.add_node(WorkflowNode {
            id: "handle_preparation_error".to_string(),
            name: "处理准备错误".to_string(),
            node_type: NodeType::Function,
            function: "handle_rollback_error".to_string(),
            next_nodes: vec!["assess_recovery_options".to_string()],
            error_node: None,
            timeout_seconds: 60,
        });
        
        // 其他错误处理节点...
        
        workflow.add_node(WorkflowNode {
            id: "assess_recovery_options".to_string(),
            name: "评估恢复选项".to_string(),
            node_type: NodeType::Decision,
            function: "assess_recovery_options".to_string(),
            next_nodes: vec!["attempt_emergency_recovery".to_string(), "notify_manual_intervention".to_string()],
            error_node: None,
            timeout_seconds: 60,
        });
        
        workflow.add_node(WorkflowNode {
            id: "attempt_emergency_recovery".to_string(),
            name: "尝试紧急恢复".to_string(),
            node_type: NodeType::Function,
            function: "attempt_emergency_recovery".to_string(),
            next_nodes: vec!["end".to_string()],
            error_node: Some("notify_manual_intervention".to_string()),
            timeout_seconds: 300,
        });
        
        workflow.add_node(WorkflowNode {
            id: "notify_manual_intervention".to_string(),
            name: "通知手动干预".to_string(),
            node_type: NodeType::Function,
            function: "notify_manual_intervention".to_string(),
            next_nodes: vec!["end".to_string()],
            error_node: None,
            timeout_seconds: 60,
        });
        
        workflow.add_node(WorkflowNode {
            id: "end".to_string(),
            name: "结束".to_string(),
            node_type: NodeType::End,
            function: "".to_string(),
            next_nodes: vec![],
            error_node: None,
            timeout_seconds: 0,
        });
        
        workflow
    }
}
```

## 回滚工作流功能实现

```rust
/// 准备设备进行回滚
pub async fn prepare_device_for_rollback(context: &WorkflowContext) -> Result<NodeOutput, WorkflowError> {
    let device_id = context.get_param("device_id")
        .ok_or_else(|| WorkflowError::MissingParameter("device_id".to_string()))?;
    
    log::info!("准备设备 {} 进行固件回滚", device_id);
    
    // 获取设备信息
    let device = device_repository::get_device_by_id(device_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法获取设备信息: {}", e)))?;
    
    // 尝试通知设备准备回滚
    let prep_result = match device_command_service::send_prepare_rollback_command(device_id).await {
        Ok(_) => {
            log::info!("成功发送回滚准备命令到设备 {}", device_id);
            true
        },
        Err(e) => {
            log::warn!("无法发送回滚准备命令到设备 {}: {}", device_id, e);
            false
        }
    };
    
    // 停止所有设备上的关键任务
    let stop_result = task_service::stop_device_tasks(device_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法停止设备任务: {}", e)))?;
    
    log::info!("已停止设备 {} 上的 {} 个任务", device_id, stop_result.stopped_tasks_count);
    
    // 更新设备状态
    device_repository::update_device_status(
        device_id,
        DeviceStatus::Maintenance,
        Some("正在进行固件回滚".to_string()),
    ).await.map_err(|e| WorkflowError::ExecutionError(format!("无法更新设备状态: {}", e)))?;
    
    // 更新更新记录状态
    let update_id = context.get_param("update_id")
        .ok_or_else(|| WorkflowError::MissingParameter("update_id".to_string()))?;
    
    let update_service = UpdateStatusService::new(
        Arc::new(update_repository::get_repository()),
        Arc::new(device_repository::get_repository()),
        Arc::new(notification_service::get_service()),
        Arc::new(telemetry_service::get_service()),
    );
    
    update_service.update_status(
        update_id,
        UpdateStatus::RollingBack,
        Some(10.0),
        Some("正在准备设备进行回滚".to_string()),
        None,
    ).await.map_err(|e| WorkflowError::ExecutionError(format!("无法更新更新状态: {}", e)))?;
    
    let mut output = NodeOutput::new();
    output.add_data("device_notified", prep_result);
    output.add_data("tasks_stopped", stop_result.stopped_tasks_count);
    output.add_data("preparation_time", Utc::now().to_rfc3339());
    
    Ok(output)
}

/// 检查设备是否处于恢复模式
pub async fn check_device_recovery_mode(context: &WorkflowContext) -> Result<DecisionOutput, WorkflowError> {
    let device_id = context.get_param("device_id")
        .ok_or_else(|| WorkflowError::MissingParameter("device_id".to_string()))?;
    
    log::info!("检查设备 {} 是否处于恢复模式", device_id);
    
    // 检查设备模式
    let device_mode = device_command_service::check_device_mode(device_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法检查设备模式: {}", e)))?;
    
    match device_mode {
        DeviceMode::Normal => {
            log::info!("设备 {} 处于正常模式，需要切换到恢复模式", device_id);
            Ok(DecisionOutput::new(1)) // 选择分支1：强制进入恢复模式
        },
        DeviceMode::Recovery | DeviceMode::Bootloader | DeviceMode::DFU => {
            log::info!("设备 {} 已处于 {:?} 模式，可以直接恢复固件", device_id, device_mode);
            Ok(DecisionOutput::new(0)) // 选择分支0：直接恢复固件
        },
        _ => {
            log::warn!("设备 {} 处于未预期的模式: {:?}，尝试强制进入恢复模式", device_id, device_mode);
            Ok(DecisionOutput::new(1)) // 选择分支1：强制进入恢复模式
        }
    }
}

/// 强制设备进入恢复模式
pub async fn force_device_recovery_mode(context: &WorkflowContext) -> Result<NodeOutput, WorkflowError> {
    let device_id = context.get_param("device_id")
        .ok_or_else(|| WorkflowError::MissingParameter("device_id".to_string()))?;
    
    log::info!("强制设备 {} 进入恢复模式", device_id);
    
    // 获取设备信息
    let device = device_repository::get_device_by_id(device_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法获取设备信息: {}", e)))?;
    
    // 根据设备类型选择进入恢复模式的方法
    let method = if device.supports_remote_recovery_mode {
        RecoveryMethod::RemoteCommand
    } else if device.has_physical_reset {
        RecoveryMethod::SimulatedReset
    } else {
        RecoveryMethod::SoftwareReboot
    };
    
    // 执行进入恢复模式的操作
    let recovery_result = device_command_service::enter_recovery_mode(device_id, method).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法进入恢复模式: {}", e)))?;
    
    if !recovery_result.success {
        return Err(WorkflowError::ExecutionError(format!(
            "无法使设备进入恢复模式: {}",
            recovery_result.error_message.unwrap_or_default()
        )));
    }
    
    // 等待设备重新连接并确认模式
    log::info!("等待设备 {} 在恢复模式下重新连接", device_id);
    
    let max_attempts = 10;
    let retry_interval_seconds = 15;
    
    for attempt in 1..=max_attempts {
        tokio::time::sleep(Duration::from_secs(retry_interval_seconds)).await;
        
        match device_command_service::check_device_mode(device_id).await {
            Ok(mode) if mode == DeviceMode::Recovery || mode == DeviceMode::Bootloader || mode == DeviceMode::DFU => {
                log::info!("设备 {} 已成功进入 {:?} 模式", device_id, mode);
                
                let mut output = NodeOutput::new();
                output.add_data("recovery_mode", format!("{:?}", mode));
                output.add_data("recovery_method", format!("{:?}", method));
                output.add_data("attempts", attempt);
                
                return Ok(output);
            },
            Ok(mode) => {
                log::warn!("设备 {} 仍处于 {:?} 模式，等待切换到恢复模式", device_id, mode);
            },
            Err(e) => {
                log::warn!("检查设备 {} 模式时出错: {}，这在恢复过程中是预期的", device_id, e);
                // 在恢复模式切换过程中，设备可能暂时无法响应，这是正常的
            }
        }
    }
    
    Err(WorkflowError::ExecutionError(format!(
        "在 {} 次尝试后，设备 {} 未能进入恢复模式",
        max_attempts, device_id
    )))
}

/// 恢复先前的固件
pub async fn restore_previous_firmware(context: &WorkflowContext) -> Result<NodeOutput, WorkflowError> {
    let device_id = context.get_param("device_id")
        .ok_or_else(|| WorkflowError::MissingParameter("device_id".to_string()))?;
    
    let update_id = context.get_param("update_id")
        .ok_or_else(|| WorkflowError::MissingParameter("update_id".to_string()))?;
    
    log::info!("开始为设备 {} 恢复先前的固件", device_id);
    
    // 获取更新记录以找到先前的固件版本
    let update_record = update_repository::get_update_record(update_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法获取更新记录: {}", e)))?;
    
    // 获取设备的更新历史
    let update_history = update_repository::get_device_update_history(device_id, 5, 0).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法获取设备更新历史: {}", e)))?;
    
    // 找到当前更新之前的成功更新记录
    let previous_successful_update = update_history.iter()
        .filter(|record| 
            record.id != update_id && 
            record.status == UpdateStatus::UpdateSuccessful &&
            record.completed_at.is_some() &&
            record.completed_at.unwrap() < update_record.started_at
        )
        .max_by_key(|record| record.completed_at);
    
    // 获取要恢复的固件版本
    let firmware_id = if let Some(prev_update) = previous_successful_update {
        log::info!("从之前的成功更新中恢复固件版本 {}", prev_update.firmware_id);
        prev_update.firmware_id.clone()
    } else {
        // 如果没有找到之前的成功更新，尝试获取设备的出厂固件
        log::warn!("没有找到之前的成功更新记录，尝试恢复到出厂固件");
        
        let device = device_repository::get_device_by_id(device_id).await
            .map_err(|e| WorkflowError::ExecutionError(format!("无法获取设备信息: {}", e)))?;
        
        device.factory_firmware_id.ok_or_else(|| 
            WorkflowError::ExecutionError("无法确定要恢复的固件版本".to_string())
        )?
    };
    
    // 获取固件二进制文件
    let firmware = firmware_repository::get_firmware(&firmware_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法获取固件信息: {}", e)))?;
    
    let firmware_binary = firmware_repository::get_firmware_binary(&firmware_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法获取固件二进制文件: {}", e)))?;
    
    // 更新恢复进度
    let update_service = UpdateStatusService::new(
        Arc::new(update_repository::get_repository()),
        Arc::new(device_repository::get_repository()),
        Arc::new(notification_service::get_service()),
        Arc::new(telemetry_service::get_service()),
    );
    
    update_service.update_status(
        update_id,
        UpdateStatus::RollingBack,
        Some(40.0),
        Some(format!("正在恢复到固件版本 {}", firmware.version)),
        None,
    ).await.map_err(|e| WorkflowError::ExecutionError(format!("无法更新更新状态: {}", e)))?;
    
    // 发送固件到设备
    log::info!("开始将固件 {} 发送到设备 {}", firmware_id, device_id);
    
    let flash_result = device_command_service::flash_firmware(
        device_id,
        &firmware_binary,
        FlashOptions {
            force: true,
            skip_verification: false,
            timeout_seconds: 600,
        }
    ).await.map_err(|e| WorkflowError::ExecutionError(format!("固件闪存失败: {}", e)))?;
    
    if !flash_result.success {
        return Err(WorkflowError::ExecutionError(format!(
            "固件恢复失败: {}",
            flash_result.error_message.unwrap_or_default()
        )));
    }
    
    log::info!("固件 {} 已成功闪存到设备 {}", firmware_id, device_id);
    
    let mut output = NodeOutput::new();
    output.add_data("firmware_id", firmware_id);
    output.add_data("firmware_version", firmware.version);
    output.add_data("flash_time", Utc::now().to_rfc3339());
    
    Ok(output)
}

/// 等待设备重启
pub async fn wait_for_device_reboot(context: &WorkflowContext) -> Result<NodeOutput, WorkflowError> {
    let device_id = context.get_param("device_id")
        .ok_or_else(|| WorkflowError::MissingParameter("device_id".to_string()))?;
    
    let update_id = context.get_param("update_id")
        .ok_or_else(|| WorkflowError::MissingParameter("update_id".to_string()))?;
    
    log::info!("等待设备 {} 重启", device_id);
    
    // 更新更新状态
    let update_service = UpdateStatusService::new(
        Arc::new(update_repository::get_repository()),
        Arc::new(device_repository::get_repository()),
        Arc::new(notification_service::get_service()),
        Arc::new(telemetry_service::get_service()),
    );
    
    update_service.update_status(
        update_id,
        UpdateStatus::RollingBack,
        Some(60.0),
        Some("等待设备重启".to_string()),
        None,
    ).await.map_err(|e| WorkflowError::ExecutionError(format!("无法更新更新状态: {}", e)))?;
    
    // 重启设备（如果尚未自动重启）
    match device_command_service::reboot_device(device_id).await {
        Ok(_) => log::info!("已发送重启命令到设备 {}", device_id),
        Err(e) => log::info!("无法发送重启命令，设备可能已在重启: {}", e),
    }
    
    // 等待设备离线（重启过程的一部分）
    log::info!("等待设备 {} 离线（重启过程）", device_id);
    
    let offline_timeout = Duration::from_secs(60);
    let offline_start = Instant::now();
    
    while offline_start.elapsed() < offline_timeout {
        match device_service::check_device_online(device_id).await {
            Ok(false) => {
                log::info!("设备 {} 已离线，等待重新上线", device_id);
                break;
            },
            Ok(true) => {
                log::info!("设备 {} 仍在线，继续等待离线", device_id);
            },
            Err(_) => {
                log::info!("无法连接到设备 {}，假定已离线", device_id);
                break;
            }
        }
        
        tokio::time::sleep(Duration::from_secs(5)).await;
    }
    
    // 等待设备重新上线
    log::info!("等待设备 {} 重新上线", device_id);
    
    let max_attempts = 20;
    let retry_interval_seconds = 15;
    
    for attempt in 1..=max_attempts {
        log::info!("尝试 {}/{} 检查设备 {} 是否已上线", attempt, max_attempts, device_id);
        
        match device_service::check_device_online(device_id).await {
            Ok(true) => {
                log::info!("设备 {} 已重新上线", device_id);
                
                // 检查设备是否已退出恢复模式
                match device_command_service::check_device_mode(device_id).await {
                    Ok(DeviceMode::Normal) => {
                        log::info!("设备 {} 已恢复到正常模式", device_id);
                        
                        let mut output = NodeOutput::new();
                        output.add_data("reboot_success", true);
                        output.add_data("reboot_attempts", attempt);
                        output.add_data("reboot_time", Utc::now().to_rfc3339());
                        
                        return Ok(output);
                    },
                    Ok(mode) => {
                        log::warn!("设备 {} 上线但处于 {:?} 模式，等待切换到正常模式", device_id, mode);
                    },
                    Err(e) => {
                        log::warn!("检查设备 {} 模式时出错: {}", device_id, e);
                    }
                }
            },
            Ok(false) => {
                log::info!("设备 {} 仍然离线，等待重新连接", device_id);
            },
            Err(e) => {
                log::warn!("检查设备 {} 在线状态时发生错误: {}", device_id, e);
            }
        }
        
        if attempt < max_attempts {
            tokio::time::sleep(Duration::from_secs(retry_interval_seconds)).await;
        }
    }
    
    Err(WorkflowError::ExecutionError(format!(
        "在 {} 次尝试后，设备 {} 未能成功重启并上线",
        max_attempts, device_id
    )))
}

/// 验证回滚结果
pub async fn verify_rollback(context: &WorkflowContext) -> Result<NodeOutput, WorkflowError> {
    let device_id = context.get_param("device_id")
        .ok_or_else(|| WorkflowError::MissingParameter("device_id".to_string()))?;
    
    let update_id = context.get_param("update_id")
        .ok_or_else(|| WorkflowError::MissingParameter("update_id".to_string()))?;
    
    let firmware_id = context.get_data("firmware_id")
        .ok_or_else(|| WorkflowError::MissingParameter("firmware_id".to_string()))?
        .clone();
    
    log::info!("验证设备 {} 的回滚结果", device_id);
    
    // 更新回滚状态
    let update_service = UpdateStatusService::new(
        Arc::new(update_repository::get_repository()),
        Arc::new(device_repository::get_repository()),
        Arc::new(notification_service::get_service()),
        Arc::new(telemetry_service::get_service()),
    );
    
    update_service.update_status(
        update_id,
        UpdateStatus::RollingBack,
        Some(80.0),
        Some("验证回滚结果".to_string()),
        None,
    ).await.map_err(|e| WorkflowError::ExecutionError(format!("无法更新更新状态: {}", e)))?;
    
    // 验证设备固件版本
    let device_info = device_command_service::get_device_info(device_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法获取设备信息: {}", e)))?;
    
    // 获取预期的固件版本
    let firmware = firmware_repository::get_firmware(&firmware_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法获取固件信息: {}", e)))?;
    
    if device_info.firmware_version != firmware.version {
        return Err(WorkflowError::ExecutionError(format!(
            "固件版本不匹配。预期: {}，实际: {}",
            firmware.version, device_info.firmware_version
        )));
    }
    
    // 验证设备基本功能
    let basic_check_result = device_verification_service::perform_basic_functionality_check(device_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("基本功能检查失败: {}", e)))?;
    
    if !basic_check_result.success {
        return Err(WorkflowError::ExecutionError(format!(
            "设备基本功能检查失败: {}",
            basic_check_result.error_message.unwrap_or_default()
        )));
    }
    
    log::info!("设备 {} 回滚验证成功", device_id);
    
    let mut output = NodeOutput::new();
    output.add_data("rollback_verified", true);
    output.add_data("verification_time", Utc::now().to_rfc3339());
    
    Ok(output)
}

/// 完成回滚流程
pub async fn finalize_rollback(context: &WorkflowContext) -> Result<NodeOutput, WorkflowError> {
    let device_id = context.get_param("device_id")
        .ok_or_else(|| WorkflowError::MissingParameter("device_id".to_string()))?;
    
    let update_id = context.get_param("update_id")
        .ok_or_else(|| WorkflowError::MissingParameter("update_id".to_string()))?;
    
    log::info!("完成设备 {} 的回滚流程", device_id);
    
    // 恢复设备到正常状态
    device_repository::update_device_status(
        device_id,
        DeviceStatus::Online,
        None,
    ).await.map_err(|e| WorkflowError::ExecutionError(format!("无法更新设备状态: {}", e)))?;
    
    // 更新更新记录状态
    let update_service = UpdateStatusService::new(
        Arc::new(update_repository::get_repository()),
        Arc::new(device_repository::get_repository()),
        Arc::new(notification_service::get_service()),
        Arc::new(telemetry_service::get_service()),
    );
    
    update_service.update_status(
        update_id,
        UpdateStatus::RollbackSuccessful,
        Some(100.0),
        Some("回滚完成".to_string()),
        None,
    ).await.map_err(|e| WorkflowError::ExecutionError(format!("无法更新更新状态: {}", e)))?;
    
    // 发送回滚成功通知
    let firmware_id = context.get_data("firmware_id")
        .ok_or_else(|| WorkflowError::MissingParameter("firmware_id".to_string()))?
        .clone();
    
    let firmware = firmware_repository::get_firmware(&firmware_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法获取固件信息: {}", e)))?;
    
    let device = device_repository::get_device_by_id(device_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法获取设备信息: {}", e)))?;
    
    let notification = NotificationRequest {
        level: NotificationLevel::Success,
        category: NotificationCategory::DeviceUpdate,
        title: format!("设备 {} 回滚成功", device.name),
        message: format!(
            "设备已成功回滚到固件版本 {}。设备现在处于正常运行状态。",
            firmware.version
        ),
        related_entity: Some(EntityReference {
            entity_type: EntityType::Device,
            entity_id: device_id.to_string(),
```rust
            entity_id: device_id.to_string(),
        }),
        actions: vec![
            NotificationAction {
                label: "查看详情".to_string(),
                action_type: ActionType::Url,
                action_data: format!("/devices/{}/updates/{}", device_id, update_id),
            },
        ],
        expiration: Some(Utc::now() + Duration::days(7)),
    };
    
    notification_service::send_notification(notification).await
        .map_err(|e| WorkflowError::ExecutionError(format!("发送通知失败: {}", e)))?;
    
    let mut output = NodeOutput::new();
    output.add_data("rollback_successful", true);
    output.add_data("completion_time", Utc::now().to_rfc3339());
    
    Ok(output)
}

/// 处理回滚错误
pub async fn handle_rollback_error(context: &WorkflowContext) -> Result<NodeOutput, WorkflowError> {
    let device_id = context.get_param("device_id")
        .ok_or_else(|| WorkflowError::MissingParameter("device_id".to_string()))?;
    
    let update_id = context.get_param("update_id")
        .ok_or_else(|| WorkflowError::MissingParameter("update_id".to_string()))?;
    
    let error_message = context.get_error_message()
        .unwrap_or("未知错误".to_string());
    
    let error_node = context.get_error_node()
        .unwrap_or("unknown".to_string());
    
    log::error!(
        "设备 {} 回滚过程中出错，节点: {}, 错误: {}", 
        device_id, error_node, error_message
    );
    
    // 更新设备状态为错误状态
    device_repository::update_device_status(
        device_id,
        DeviceStatus::Error,
        Some(format!("回滚失败: {}", error_message)),
    ).await.map_err(|e| WorkflowError::ExecutionError(format!("无法更新设备状态: {}", e)))?;
    
    // 更新更新记录状态
    let update_service = UpdateStatusService::new(
        Arc::new(update_repository::get_repository()),
        Arc::new(device_repository::get_repository()),
        Arc::new(notification_service::get_service()),
        Arc::new(telemetry_service::get_service()),
    );
    
    update_service.update_status(
        update_id,
        UpdateStatus::RollbackFailed,
        None,
        Some(format!("回滚失败: {}", error_node)),
        Some(error_message.clone()),
    ).await.map_err(|e| WorkflowError::ExecutionError(format!("无法更新更新状态: {}", e)))?;
    
    let mut output = NodeOutput::new();
    output.add_data("error_node", error_node);
    output.add_data("error_message", error_message);
    output.add_data("error_time", Utc::now().to_rfc3339());
    
    Ok(output)
}

/// 评估恢复选项
pub async fn assess_recovery_options(context: &WorkflowContext) -> Result<DecisionOutput, WorkflowError> {
    let device_id = context.get_param("device_id")
        .ok_or_else(|| WorkflowError::MissingParameter("device_id".to_string()))?;
    
    // 获取设备信息
    let device = device_repository::get_device_by_id(device_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法获取设备信息: {}", e)))?;
    
    // 检查设备是否支持紧急恢复
    if device.supports_emergency_recovery {
        log::info!("设备 {} 支持紧急恢复，将尝试紧急恢复流程", device_id);
        Ok(DecisionOutput::new(0)) // 选择分支0：尝试紧急恢复
    } else {
        log::warn!("设备 {} 不支持紧急恢复，需要手动干预", device_id);
        Ok(DecisionOutput::new(1)) // 选择分支1：通知手动干预
    }
}

/// 尝试紧急恢复
pub async fn attempt_emergency_recovery(context: &WorkflowContext) -> Result<NodeOutput, WorkflowError> {
    let device_id = context.get_param("device_id")
        .ok_or_else(|| WorkflowError::MissingParameter("device_id".to_string()))?;
    
    log::info!("为设备 {} 尝试紧急恢复流程", device_id);
    
    // 获取设备信息
    let device = device_repository::get_device_by_id(device_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法获取设备信息: {}", e)))?;
    
    // 获取恢复固件
    let recovery_firmware_id = device.recovery_firmware_id
        .ok_or_else(|| WorkflowError::ExecutionError("设备没有指定恢复固件".to_string()))?;
    
    let recovery_firmware = firmware_repository::get_firmware(&recovery_firmware_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法获取恢复固件信息: {}", e)))?;
    
    let recovery_binary = firmware_repository::get_firmware_binary(&recovery_firmware_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法获取恢复固件二进制文件: {}", e)))?;
    
    // 尝试使用紧急恢复协议
    log::info!("尝试使用紧急恢复协议向设备 {} 发送恢复固件", device_id);
    
    let emergency_result = device_command_service::emergency_firmware_recovery(
        device_id,
        &recovery_binary,
        EmergencyRecoveryOptions {
            timeout_seconds: 900, // 15分钟超时
            retry_attempts: 3,
            force_recovery_mode: true,
        }
    ).await.map_err(|e| WorkflowError::ExecutionError(format!("紧急恢复失败: {}", e)))?;
    
    if !emergency_result.success {
        return Err(WorkflowError::ExecutionError(format!(
            "紧急恢复失败: {}",
            emergency_result.error_message.unwrap_or_default()
        )));
    }
    
    log::info!("设备 {} 紧急恢复成功", device_id);
    
    // 更新设备状态
    device_repository::update_device_status(
        device_id,
        DeviceStatus::Maintenance,
        Some("紧急恢复完成，需要手动验证".to_string()),
    ).await.map_err(|e| WorkflowError::ExecutionError(format!("无法更新设备状态: {}", e)))?;
    
    // 更新更新记录
    let update_id = context.get_param("update_id")
        .ok_or_else(|| WorkflowError::MissingParameter("update_id".to_string()))?;
    
    let update_service = UpdateStatusService::new(
        Arc::new(update_repository::get_repository()),
        Arc::new(device_repository::get_repository()),
        Arc::new(notification_service::get_service()),
        Arc::new(telemetry_service::get_service()),
    );
    
    update_service.update_status(
        update_id,
        UpdateStatus::RollbackFailed,
        None,
        Some("常规回滚失败，紧急恢复成功".to_string()),
        None,
    ).await.map_err(|e| WorkflowError::ExecutionError(format!("无法更新更新状态: {}", e)))?;
    
    // 发送通知
    let notification = NotificationRequest {
        level: NotificationLevel::Warning,
        category: NotificationCategory::DeviceUpdate,
        title: format!("设备 {} 紧急恢复成功", device.name),
        message: format!(
            "设备回滚失败，但紧急恢复成功。设备当前运行恢复固件版本 {}。请手动验证设备功能并考虑重新更新。",
            recovery_firmware.version
        ),
        related_entity: Some(EntityReference {
            entity_type: EntityType::Device,
            entity_id: device_id.to_string(),
        }),
        actions: vec![
            NotificationAction {
                label: "查看详情".to_string(),
                action_type: ActionType::Url,
                action_data: format!("/devices/{}/updates/{}", device_id, update_id),
            },
            NotificationAction {
                label: "验证设备".to_string(),
                action_type: ActionType::Url,
                action_data: format!("/devices/{}/diagnostics", device_id),
            },
        ],
        expiration: Some(Utc::now() + Duration::days(7)),
    };
    
    notification_service::send_notification(notification).await
        .map_err(|e| WorkflowError::ExecutionError(format!("发送通知失败: {}", e)))?;
    
    let mut output = NodeOutput::new();
    output.add_data("emergency_recovery_successful", true);
    output.add_data("recovery_firmware_id", recovery_firmware_id);
    output.add_data("recovery_time", Utc::now().to_rfc3339());
    
    Ok(output)
}

/// 通知需要手动干预
pub async fn notify_manual_intervention(context: &WorkflowContext) -> Result<NodeOutput, WorkflowError> {
    let device_id = context.get_param("device_id")
        .ok_or_else(|| WorkflowError::MissingParameter("device_id".to_string()))?;
    
    let update_id = context.get_param("update_id")
        .ok_or_else(|| WorkflowError::MissingParameter("update_id".to_string()))?;
    
    log::error!("设备 {} 需要手动干预", device_id);
    
    // 获取错误信息
    let error_message = context.get_data("error_message")
        .map(|v| v.clone())
        .unwrap_or_else(|| "未知错误".to_string());
    
    // 获取设备信息
    let device = device_repository::get_device_by_id(device_id).await
        .map_err(|e| WorkflowError::ExecutionError(format!("无法获取设备信息: {}", e)))?;
    
    // 更新设备状态
    device_repository::update_device_status(
        device_id,
        DeviceStatus::Error,
        Some("固件回滚失败，需要手动干预".to_string()),
    ).await.map_err(|e| WorkflowError::ExecutionError(format!("无法更新设备状态: {}", e)))?;
    
    // 更新更新记录状态
    let update_service = UpdateStatusService::new(
        Arc::new(update_repository::get_repository()),
        Arc::new(device_repository::get_repository()),
        Arc::new(notification_service::get_service()),
        Arc::new(telemetry_service::get_service()),
    );
    
    update_service.update_status(
        update_id,
        UpdateStatus::RollbackFailed,
        None,
        Some("回滚失败，需要手动干预".to_string()),
        Some(error_message.clone()),
    ).await.map_err(|e| WorkflowError::ExecutionError(format!("无法更新更新状态: {}", e)))?;
    
    // 创建严重事件
    let incident = IncidentCreationRequest {
        title: format!("设备 {} 固件更新和回滚失败", device.name),
        description: format!(
            "设备 {} (ID: {}) 的固件更新失败，随后的回滚尝试也失败。\n\n错误: {}\n\n设备当前处于错误状态，需要手动干预。",
            device.name, device.id, error_message
        ),
        severity: IncidentSeverity::High,
        category: IncidentCategory::DeviceUpdate,
        affected_entities: vec![
            EntityReference {
                entity_type: EntityType::Device,
                entity_id: device_id.to_string(),
            }
        ],
        recommended_actions: vec![
            "检查设备物理连接状态".to_string(),
            "尝试手动重启设备".to_string(),
            "使用设备制造商提供的恢复工具".to_string(),
            "如果设备支持，尝试通过USB或串行连接进行恢复".to_string(),
        ],
        auto_resolve: false,
    };
    
    let incident_id = incident_service::create_incident(incident).await
        .map_err(|e| WorkflowError::ExecutionError(format!("创建事件失败: {}", e)))?;
    
    // 发送紧急通知
    let notification = NotificationRequest {
        level: NotificationLevel::Error,
        category: NotificationCategory::DeviceUpdate,
        title: format!("设备 {} 需要紧急手动干预", device.name),
        message: format!(
            "设备固件更新和回滚均失败。设备当前可能处于不可用状态。\n\n错误: {}\n\n已创建事件 #{} 以跟踪此问题。请联系技术支持或现场工程师进行手动恢复。",
            error_message, incident_id
        ),
        related_entity: Some(EntityReference {
            entity_type: EntityType::Device,
            entity_id: device_id.to_string(),
        }),
        actions: vec![
            NotificationAction {
                label: "查看事件".to_string(),
                action_type: ActionType::Url,
                action_data: format!("/incidents/{}", incident_id),
            },
            NotificationAction {
                label: "恢复指南".to_string(),
                action_type: ActionType::Url,
                action_data: format!("/devices/{}/recovery-guide", device_id),
            },
        ],
        expiration: None, // 不过期，需要手动处理
    };
    
    notification_service::send_notification(notification).await
        .map_err(|e| WorkflowError::ExecutionError(format!("发送通知失败: {}", e)))?;
    
    let mut output = NodeOutput::new();
    output.add_data("manual_intervention_required", true);
    output.add_data("incident_id", incident_id);
    output.add_data("notification_time", Utc::now().to_rfc3339());
    
    Ok(output)
}
```

## 总结

在本设计中，我们构建了一个全面的IoT固件更新系统，包括以下关键组件：

## 1. 设备预更新准备流程

- 设备状态检查
- 电池电量和存储空间验证
- 关键数据备份
- 设备设置准备

## 2. 更新状态跟踪机制

- 详细的更新状态模型
- 进度实时追踪
- 自动通知和告警
- 性能指标分析

## 3. 更新后验证流程

- 在线状态验证
- 固件版本验证
- 核心功能测试
- 性能指标对比分析
- 设备设置恢复
- 连接性验证

## 4. 固件回滚流程

- 自动故障检测
- 多级恢复机制（正常回滚和紧急恢复）
- 恢复后验证
- 手动干预流程

## 关键设计特点

1. **高可靠性**：通过预检查、备份、验证和回滚流程确保设备不会因更新失败而无法运行

2. **可观测性**：详细的状态跟踪和遥测数据收集，使管理员能实时了解更新进展

3. **容错设计**：多级恢复机制，包括自动回滚、紧急恢复和手动干预流程

4. **用户友好**：自动通知系统，及时向用户提供更新进度、结果和任何需要注意的问题

5. **灵活性**：工作流定义允许针对不同设备类型和固件版本自定义流程

6. **全方位安全**：验证固件完整性，备份和恢复机制，以及对更新失败的安全处理

这个IoT固件更新系统设计全面考虑了实际应用中的各种复杂场景，保证了设备更新过程的可靠性和安全性，同时提供了灵活的配置选项和详细的状态反馈。
