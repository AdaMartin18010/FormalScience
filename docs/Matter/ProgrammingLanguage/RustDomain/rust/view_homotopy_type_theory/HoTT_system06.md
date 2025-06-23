# IOT分布式工作流系统设计与实现

```text
<think>
我需要设计一个针对IOT物联网行业的分布式系统架构和工作流框架，
基于之前讨论的分布式系统架构原则，以Rust语言实现。
我将创建一个结构化的Markdown文档，包含详细的目录和文本形式的思维导图。

主要内容应当包括：

1. 引言和背景
2. 系统架构概览
3. 核心组件设计
4. 类型安全和版本兼容性
5. 自适应演化机制
6. 性能优化策略
7. 与开源软件集成
8. 具体IOT场景应用
9. 部署和运维指南
10. 未来发展方向

思维导图应该展示这些组件及其相互关系。

文档应该强调Rust语言的优势，如内存安全、类型系统、并发安全等，以及如何利用这些特性构建可靠的IOT系统。

我还需要考虑IOT系统特有的挑战，如设备异构性、资源受限、连接不稳定、大规模管理和安全问题。
</think>
```

## 目录

- [IOT分布式工作流系统设计与实现](#iot分布式工作流系统设计与实现)
  - [目录](#目录)
  - [引言](#引言)
    - [背景与挑战](#背景与挑战)
    - [设计目标](#设计目标)
    - [为什么选择Rust](#为什么选择rust)
  - [系统架构概览](#系统架构概览)
    - [总体架构](#总体架构)
    - [层次结构](#层次结构)
    - [核心设计原则](#核心设计原则)
  - [核心组件](#核心组件)
    - [设备连接层](#设备连接层)
      - [协议适配器](#协议适配器)
      - [安全通信模块](#安全通信模块)
      - [设备注册与发现](#设备注册与发现)
    - [数据处理层](#数据处理层)
      - [遥测数据流](#遥测数据流)
      - [事件处理引擎](#事件处理引擎)
      - [时序数据管理](#时序数据管理)
    - [工作流引擎](#工作流引擎)
      - [工作流定义DSL](#工作流定义dsl)
      - [有状态处理器](#有状态处理器)
      - [触发器系统](#触发器系统)
    - [分布式协调](#分布式协调)
      - [共识机制](#共识机制)
      - [状态同步](#状态同步)
      - [分区策略](#分区策略)
  - [结论与未来方向](#结论与未来方向)
    - [1. 主要贡献](#1-主要贡献)
      - [共识协议](#共识协议)
      - [分区管理](#分区管理)
      - [服务发现](#服务发现)
      - [状态管理](#状态管理)
      - [分布式跟踪](#分布式跟踪)
    - [2. 架构特点](#2-架构特点)
      - [类型安全与可组合性](#类型安全与可组合性)
      - [异步编程模型](#异步编程模型)
      - [分层设计](#分层设计)
      - [可观测性](#可观测性)
    - [3. 实用价值](#3-实用价值)
    - [4. 未来研究方向](#4-未来研究方向)
      - [自适应分区策略](#自适应分区策略)
      - [混合共识协议](#混合共识协议)
      - [高级状态压缩](#高级状态压缩)
      - [机器学习集成](#机器学习集成)
      - [跨语言接口](#跨语言接口)
    - [5. 总结](#5-总结)
  - [系统架构概览图](#系统架构概览图)

## 引言

### 背景与挑战

物联网(IoT)领域正面临前所未有的增长和挑战。
随着连接设备数量呈指数级增长，分布式系统架构成为管理这一复杂生态系统的关键。
现代IoT系统需要处理的主要挑战包括：

- **设备异构性**：管理具有不同能力、协议和资源约束的设备
- **规模与性能**：支持数百万设备的数据收集和处理
- **可靠性**：在不稳定网络和设备故障的情况下保持系统功能
- **实时处理需求**：及时响应关键事件和数据
- **安全威胁**：保护设备和数据免受不断演变的威胁
- **系统演化**：在不中断服务的情况下适应新需求和技术

### 设计目标

我们的IoT分布式工作流框架旨在解决上述挑战，具有以下关键设计目标：

1. **类型安全与形式化验证**：利用Rust的类型系统确保系统状态转换的正确性和数据完整性
2. **自适应演化**：支持系统组件的无停机升级和版本兼容性
3. **分布式协调**：跨边缘和云环境提供一致的状态和处理
4. **高性能处理**：优化数据流和工作流执行以满足实时要求
5. **可扩展性**：从小型部署无缝扩展到数百万设备
6. **开源兼容性**：与现有IoT开源生态系统无缝集成
7. **资源效率**：最小化计算和存储需求，尤其在边缘设备上

### 为什么选择Rust

Rust语言为实现这些目标提供了独特优势：

- **内存安全**：无需垃圾收集的内存安全，适合资源受限的环境
- **并发模型**：基于所有权的并发安全，减少运行时错误
- **零成本抽象**：高级抽象而不牺牲性能
- **强类型系统**：支持复杂类型约束和编译时验证
- **跨平台**：从微控制器到服务器的广泛支持
- **异步编程**：高效的异步I/O处理大量并发连接
- **FFI支持**：轻松集成现有C/C++库和系统组件

## 系统架构概览

### 总体架构

我们的IoT分布式工作流系统采用分层多级架构，包括边缘层、中间层和云层，以实现灵活的处理策略和故障隔离。

边缘层负责设备连接、初步数据处理和本地决策。
中间层提供区域协调和数据聚合。云层处理全局分析、长期存储和系统管理。

关键设计包括：

- **基于事件的通信**：使用发布/订阅模式实现松耦合组件
- **状态化工作流**：支持长时间运行的处理任务，具有检查点和恢复能力
- **多层数据处理**：在边缘执行时间敏感的处理，在云端执行资源密集型分析
- **分层控制平面**：用于设备管理、更新和配置的分布式控制系统

### 层次结构

```text
┌───────────────────────────────────────┐
│            应用服务层                  │
│ ┌─────────┐ ┌─────────┐ ┌──────────┐  │
│ │数据可视化│ │分析应用  │ │业务集成  │  │
│ └─────────┘ └─────────┘ └──────────┘  │
├───────────────────────────────────────┤
│            工作流编排层                │
│ ┌─────────┐ ┌─────────┐ ┌──────────┐  │
│ │工作流定义│ │状态管理  │ │任务调度  │  │
│ └─────────┘ └─────────┘ └──────────┘  │
├───────────────────────────────────────┤
│            数据处理层                  │
│ ┌─────────┐ ┌─────────┐ ┌──────────┐  │
│ │流处理    │ │时序分析 │ │事件检测   │  │
│ └─────────┘ └─────────┘ └──────────┘  │
├───────────────────────────────────────┤
│            分布式协调层                │
│ ┌─────────┐ ┌─────────┐ ┌──────────┐  │
│ │共识协议  │ │状态复制  │ │分区容错  │  │
│ └─────────┘ └─────────┘ └──────────┘  │
├───────────────────────────────────────┤
│            设备连接层                  │
│ ┌─────────┐ ┌─────────┐ ┌──────────┐  │
│ │协议适配  │ │设备管理  │ │安全通信  │  │
│ └─────────┘ └─────────┘ └──────────┘  │
└───────────────────────────────────────┘
```

### 核心设计原则

1. **组合式架构**：系统由可独立发展的小型、专注组件构建
2. **类型驱动设计**：利用类型系统确保正确的状态转换和数据流
3. **边缘优先策略**：优先在靠近数据源的地方处理数据
4. **不可变数据流**：使用不可变数据结构简化并发和状态管理
5. **分层版本控制**：各组件独立版本化，支持渐进式升级
6. **故障隔离**：通过隔离边界限制故障传播
7. **资源自适应**：根据可用资源动态调整处理策略
8. **可观测性优先**：内置全面的监控和调试能力

## 核心组件

### 设备连接层

设备连接层是系统的基础，负责管理与物联网设备的通信。
它支持多种协议，提供统一的抽象，并确保安全通信。

#### 协议适配器

```rust
// 协议适配器特征
#[async_trait]
pub trait ProtocolAdapter: Send + Sync {
    async fn connect(&self) -> Result<(), ConnectionError>;
    async fn subscribe(&self, topics: &[String]) -> Result<(), SubscriptionError>;
    async fn publish(&self, topic: &str, payload: &[u8], qos: QosLevel) -> Result<(), PublishError>;
    async fn receive(&self) -> Option<Message>;
}

// MQTT协议适配器
pub struct MqttAdapter {
    client: AsyncClient,
    options: MqttOptions,
    message_rx: mpsc::Receiver<Message>,
    metrics: Arc<ProtocolMetrics>,
}

impl MqttAdapter {
    pub async fn new(broker: &str, client_id: &str, credentials: Option<Credentials>) -> Result<Self, ConnectionError> {
        // 初始化MQTT客户端
        let mut options = MqttOptions::new(client_id, broker, 1883);
        
        if let Some(creds) = credentials {
            options.set_credentials(creds.username, creds.password);
        }
        
        options.set_keep_alive(Duration::from_secs(30));
        options.set_clean_session(true);
        
        let (client, mut eventloop) = AsyncClient::new(options.clone(), 100);
        let (tx, rx) = mpsc::channel(100);
        
        let metrics = Arc::new(ProtocolMetrics::new("mqtt"));
        let metrics_clone = metrics.clone();
        
        // 启动消息处理循环
        tokio::spawn(async move {
            while let Ok(event) = eventloop.poll().await {
                match event {
                    Event::Incoming(Packet::Publish(publish)) => {
                        let message = Message {
                            topic: publish.topic.clone(),
                            payload: publish.payload.to_vec(),
                            qos: publish.qos.into(),
                            retain: publish.retain,
                        };
                        
                        metrics_clone.record_received_message(publish.payload.len());
                        
                        if let Err(e) = tx.send(message).await {
                            log::error!("Failed to forward MQTT message: {}", e);
                        }
                    }
                    Event::Outgoing(Packet::PubAck(ack)) => {
                        metrics_clone.record_ack();
                    }
                    _ => {}
                }
            }
        });
        
        Ok(Self {
            client,
            options,
            message_rx: rx,
            metrics,
        })
    }
}

#[async_trait]
impl ProtocolAdapter for MqttAdapter {
    async fn connect(&self) -> Result<(), ConnectionError> {
        // 实现连接逻辑
    }
    
    async fn subscribe(&self, topics: &[String]) -> Result<(), SubscriptionError> {
        // 实现订阅逻辑
    }
    
    async fn publish(&self, topic: &str, payload: &[u8], qos: QosLevel) -> Result<(), PublishError> {
        // 实现发布逻辑
    }
    
    async fn receive(&self) -> Option<Message> {
        // 实现接收逻辑
    }
}

// 协议工厂 - 支持多种协议的统一创建
pub struct ProtocolFactory {
    registry: Arc<TypeRegistry>,
}

impl ProtocolFactory {
    pub fn create(&self, config: ProtocolConfig) -> Result<Box<dyn ProtocolAdapter>, AdapterError> {
        match config.protocol_type {
            ProtocolType::MQTT => {
                let adapter = MqttAdapter::new(
                    &config.endpoint,
                    &config.client_id,
                    config.credentials,
                ).await?;
                Ok(Box::new(adapter))
            },
            ProtocolType::CoAP => {
                // 创建CoAP适配器
            },
            ProtocolType::AMQP => {
                // 创建AMQP适配器
            },
            ProtocolType::HTTP => {
                // 创建HTTP/WebHook适配器
            },
        }
    }
}
```

#### 安全通信模块

```rust
// 设备证书管理
pub struct DeviceCertManager {
    ca_cert: Arc<Certificate>,
    private_key: Arc<PrivateKey>,
    cert_store: Arc<CertificateStore>,
}

impl DeviceCertManager {
    pub fn new(ca_path: &Path, private_key_path: &Path) -> Result<Self, CertError> {
        // 加载CA证书和私钥
        let ca_cert = Certificate::from_pem_file(ca_path)?;
        let private_key = PrivateKey::from_pem_file(private_key_path)?;
        
        // 初始化证书存储
        let cert_store = CertificateStore::new();
        
        Ok(Self {
            ca_cert: Arc::new(ca_cert),
            private_key: Arc::new(private_key),
            cert_store: Arc::new(cert_store),
        })
    }
    
    pub async fn issue_device_certificate(
        &self,
        device_id: &str,
        csr: &CertificateSigningRequest,
    ) -> Result<Certificate, CertError> {
        // 验证CSR
        if !csr.verify() {
            return Err(CertError::InvalidCsr);
        }
        
        // 检查设备权限
        self.verify_device_permission(device_id).await?;
        
        // 签发证书
        let cert = self.ca_cert.sign_csr(csr, &self.private_key, Duration::from_days(365))?;
        
        // 存储证书
        self.cert_store.store(device_id, &cert).await?;
        
        Ok(cert)
    }
    
    pub async fn revoke_certificate(&self, device_id: &str) -> Result<(), CertError> {
        // 撤销证书
        let cert = self.cert_store.get(device_id).await?;
        self.cert_store.revoke(device_id, RevocationReason::Superseded).await?;
        
        // 更新撤销列表
        self.update_crl().await?;
        
        Ok(())
    }
    
    async fn update_crl(&self) -> Result<(), CertError> {
        // 生成新的CRL并发布
    }
}

// TLS配置生成器
pub struct TlsConfigBuilder {
    ca_cert: Option<Certificate>,
    client_cert: Option<Certificate>,
    private_key: Option<PrivateKey>,
    cipher_suites: Vec<CipherSuite>,
    verify_peer: bool,
}

impl TlsConfigBuilder {
    pub fn new() -> Self {
        Self {
            ca_cert: None,
            client_cert: None,
            private_key: None,
            cipher_suites: vec![
                CipherSuite::TLS_AES_128_GCM_SHA256,
                CipherSuite::TLS_AES_256_GCM_SHA384,
            ],
            verify_peer: true,
        }
    }
    
    pub fn with_ca_cert(mut self, cert: Certificate) -> Self {
        self.ca_cert = Some(cert);
        self
    }
    
    pub fn with_client_cert(mut self, cert: Certificate, key: PrivateKey) -> Self {
        self.client_cert = Some(cert);
        self.private_key = Some(key);
        self
    }
    
    pub fn build_client_config(&self) -> Result<ClientTlsConfig, TlsError> {
        // 构建TLS客户端配置
    }
    
    pub fn build_server_config(&self) -> Result<ServerTlsConfig, TlsError> {
        // 构建TLS服务器配置
    }
}
```

#### 设备注册与发现

```rust
// 设备数据模型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Device {
    id: String,
    name: String,
    device_type: DeviceType,
    manufacturer: String,
    model: String,
    firmware_version: Version,
    capabilities: Vec<Capability>,
    status: DeviceStatus,
    created_at: DateTime<Utc>,
    updated_at: DateTime<Utc>,
    tags: HashMap<String, String>,
}

// 设备注册表
pub struct DeviceRegistry {
    store: Arc<dyn DeviceStore>,
    event_publisher: Arc<EventPublisher>,
    indexer: Arc<DeviceIndexer>,
}

impl DeviceRegistry {
    pub async fn register_device(&self, device: Device) -> Result<(), RegistryError> {
        // 验证设备信息
        self.validate_device(&device)?;
        
        // 检查设备是否已存在
        if let Ok(_) = self.store.get(&device.id).await {
            return Err(RegistryError::DeviceAlreadyExists(device.id));
        }
        
        // 存储设备
        self.store.put(&device).await?;
        
        // 索引设备属性
        self.indexer.index_device(&device).await?;
        
        // 发布设备注册事件
        self.event_publisher.publish(
            "device.registered",
            &EventPayload::DeviceRegistered { device_id: device.id.clone() },
        ).await?;
        
        Ok(())
    }
    
    pub async fn update_device(&self, device_id: &str, updates: DeviceUpdates) -> Result<Device, RegistryError> {
        // 获取当前设备
        let mut device = self.store.get(device_id).await?;
        
        // 应用更新
        if let Some(name) = updates.name {
            device.name = name;
        }
        
        if let Some(firmware_version) = updates.firmware_version {
            device.firmware_version = firmware_version;
        }
        
        if let Some(status) = updates.status {
            device.status = status;
        }
        
        // 更新时间戳
        device.updated_at = Utc::now();
        
        // 存储更新后的设备
        self.store.put(&device).await?;
        
        // 重新索引
        self.indexer.index_device(&device).await?;
        
        // 发布设备更新事件
        self.event_publisher.publish(
            "device.updated",
            &EventPayload::DeviceUpdated { device_id: device.id.clone() },
        ).await?;
        
        Ok(device)
    }
    
    pub async fn search_devices(&self, query: DeviceQuery) -> Result<Vec<Device>, RegistryError> {
        // 执行设备搜索
        let device_ids = self.indexer.search(&query).await?;
        
        // 获取设备详情
        let mut devices = Vec::with_capacity(device_ids.len());
        for id in device_ids {
            if let Ok(device) = self.store.get(&id).await {
                devices.push(device);
            }
        }
        
        Ok(devices)
    }
}

// 设备发现服务
pub struct DeviceDiscoveryService {
    registry: Arc<DeviceRegistry>,
    protocol_adapters: HashMap<ProtocolType, Box<dyn ProtocolAdapter>>,
    discovery_interval: Duration,
}

impl DeviceDiscoveryService {
    pub async fn start_discovery(&self) -> Result<(), DiscoveryError> {
        // 启动设备发现循环
        for (protocol, adapter) in &self.protocol_adapters {
            let registry = self.registry.clone();
            let adapter_clone = adapter.clone_box();
            let interval = self.discovery_interval;
            
            tokio::spawn(async move {
                let mut interval_timer = tokio::time::interval(interval);
                
                loop {
                    interval_timer.tick().await;
                    
                    // 执行发现过程
                    match Self::discover_devices(&adapter_clone).await {
                        Ok(devices) => {
                            for device in devices {
                                if let Err(e) = registry.register_device(device).await {
                                    if !matches!(e, RegistryError::DeviceAlreadyExists(_)) {
                                        log::error!("Failed to register discovered device: {}", e);
                                    }
                                }
                            }
                        }
                        Err(e) => {
                            log::error!("Device discovery failed for protocol {:?}: {}", protocol, e);
                        }
                    }
                }
            });
        }
        
        Ok(())
    }
    
    async fn discover_devices(adapter: &Box<dyn ProtocolAdapter>) -> Result<Vec<Device>, DiscoveryError> {
        // 发送发现请求
        adapter.publish(
            "discovery/request",
            serde_json::to_vec(&DiscoveryRequest {
                request_id: Uuid::new_v4().to_string(),
                timestamp: Utc::now(),
            })?,
            QosLevel::AtLeastOnce,
        ).await?;
        
        // 收集响应
        let mut devices = Vec::new();
        let timeout = Duration::from_secs(30);
        let deadline = Instant::now() + timeout;
        
        while Instant::now() < deadline {
            if let Some(message) = adapter.receive().await {
                if message.topic.starts_with("discovery/response") {
                    if let Ok(response) = serde_json::from_slice::<DiscoveryResponse>(&message.payload) {
                        devices.push(response.device);
                    }
                }
            }
            
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
        
        Ok(devices)
    }
}
```

### 数据处理层

数据处理层负责接收、处理和转换IoT设备生成的数据流。它包括实时处理、事件检测和时序数据管理组件。

#### 遥测数据流

```rust
// 遥测数据处理框架
pub struct TelemetryProcessor {
    input_stream: DataStream<RawTelemetry>,
    processor_chain: Vec<Box<dyn TelemetryTransformer>>,
    output_sink: Box<dyn TelemetrySink>,
    metrics: Arc<TelemetryMetrics>,
}

impl TelemetryProcessor {
    pub fn new(input: DataStream<RawTelemetry>, sink: Box<dyn TelemetrySink>) -> Self {
        Self {
            input_stream: input,
            processor_chain: Vec::new(),
            output_sink: sink,
            metrics: Arc::new(TelemetryMetrics::new()),
        }
    }
    
    pub fn add_transformer(&mut self, transformer: Box<dyn TelemetryTransformer>) -> &mut Self {
        self.processor_chain.push(transformer);
        self
    }
    
    pub async fn start(&self) -> Result<(), ProcessorError> {
        // 处理遥测数据流
        let mut stream = self.input_stream.clone();
        
        let metrics = self.metrics.clone();
        let processor_chain = self.processor_chain.clone();
        let sink = self.output_sink.clone_box();
        
        tokio::spawn(async move {
            while let Some(telemetry) = stream.next().await {
                let start_time = Instant::now();
                metrics.record_received();
                
                // 应用处理链
                let mut processed_telemetry = telemetry;
                for transformer in &processor_chain {
                    match transformer.transform(processed_telemetry).await {
                        Ok(transformed) => {
                            processed_telemetry = transformed;
                        }
                        Err(e) => {
                            metrics.record_error();
                            log::error!("Telemetry transformation error: {}", e);
                            continue;
                        }
                    }
                }
                
                // 发送到输出
                if let Err(e) = sink.send(processed_telemetry).await {
                    metrics.record_error();
                    log::error!("Failed to send telemetry to sink: {}", e);
                } else {
                    metrics.record_processed(start_time.elapsed());
                }
            }
        });
        
        Ok(())
    }
}

// 遥测转换器特征
#[async_trait]
pub trait TelemetryTransformer: Send + Sync {
    async fn transform(&self, telemetry: RawTelemetry) -> Result<RawTelemetry, TransformerError>;
    fn name(&self) -> &str;
}

// 数据清理转换器
pub struct DataCleaningTransformer {
    rules: Vec<CleaningRule>,
}

#[async_trait]
impl TelemetryTransformer for DataCleaningTransformer {
    async fn transform(&self, mut telemetry: RawTelemetry) -> Result<RawTelemetry, TransformerError> {
        // 应用数据清理规则
        for rule in &self.rules {
            if let Some(field) = telemetry.payload.get_mut(&rule.field_name) {
                match rule.rule_type {
                    CleaningRuleType::OutlierRemoval { min, max } => {
                        if let Value::Number(n) = field {
                            let value = n.as_f64().unwrap_or(0.0);
                            if value < min || value > max {
                                // 替换异常值
                                *field = match rule.replacement {
                                    ReplacementStrategy::FixedValue(val) => Value::Number(val.into()),
                                    ReplacementStrategy::Null => Value::Null,
                                    ReplacementStrategy::Skip => {
                                        return Err(TransformerError::SkippedRecord);
                                    }
                                };
                            }
                        }
                    },
                    CleaningRuleType::NullHandling => {
                        if field.is_null() {
                            // 处理空值
                            *field = match rule.replacement {
                                ReplacementStrategy::FixedValue(val) => Value::Number(val.into()),
                                ReplacementStrategy::Null => Value::Null,
                                ReplacementStrategy::Skip => {
                                    return Err(TransformerError::SkippedRecord);
                                }
                            };
                        }
                    },
                    // 其他清理规则...
                }
            }
        }
        
        Ok(telemetry)
    }
    
    fn name(&self) -> &str {
        "data-cleaning"
    }
}

// 单位转换器
pub struct UnitConversionTransformer {
    conversions: HashMap<String, UnitConversion>,
}

#[async_trait]
impl TelemetryTransformer for UnitConversionTransformer {
    async fn transform(&self, mut telemetry: RawTelemetry) -> Result<RawTelemetry, TransformerError> {
        // 应用单位转换
        for (field, conversion) in &self.conversions {
            if let Some(Value::Number(n)) = telemetry.payload.get(field) {
                let value = n.as_f64().unwrap_or(0.0);
                let converted = match conversion {
                    UnitConversion::Linear { scale, offset } => value * scale + offset,
                    UnitConversion::Custom(func) => func(value),
                };
                
                telemetry.payload[field] = Value::Number(converted.into());
            }
        }
        
        Ok(telemetry)
    }
    
    fn name(&self) -> &str {
        "unit-conversion"
    }
}
```

#### 事件处理引擎

```rust
// 事件定义
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Event {
    id: String,
    event_type: String,
    source: String,
    timestamp: DateTime<Utc>,
    data: HashMap<String, Value>,
    metadata: HashMap<String, String>,
}

// 事件规则引擎
pub struct EventRuleEngine {
    rules: Vec<EventRule>,
    action_executor: Arc<ActionExecutor>,
    event_store: Arc<dyn EventStore>,
    metrics: Arc<EventMetrics>,
}

impl EventRuleEngine {
    pub fn new(
        action_executor: Arc<ActionExecutor>,
        event_store: Arc<dyn EventStore>,
    ) -> Self {
        Self {
            rules: Vec::new(),
            action_executor,
            event_store,
            metrics: Arc::new(EventMetrics::new()),
        }
    }
    
    pub fn add_rule(&mut self, rule: EventRule) -> &mut Self {
        self.rules.push(rule);
        self
    }
    
    pub async fn process_event(&self, event: Event) -> Result<Vec<ActionResult>, RuleEngineError> {
        let mut results = Vec::new();
        let start_time = Instant::now();
        
        // 存储事件
        self.event_store.store(&event).await?;
        self.metrics.record_event_received();
        
        // 评估规则
        for rule in &self.rules {
            if self.evaluate_condition(&rule.condition, &event).await? {
                // 规则匹配，执行操作
                self.metrics.record_rule_matched(&rule.name);
                
                for action in &rule.actions {
                    match self.action_executor.execute(action, &event).await {
                        Ok(result) => {
                            results.push(result);
                            self.metrics.record_action_executed(&action.action_type);
                        }
                        Err(e) => {
                            self.metrics.record_action_failed(&action.action_type);
                            log::error!("Failed to execute action: {}", e);
                        }
                    }
                }
            }
        }
        
        self.metrics.record_processing_time(start_time.elapsed());
        Ok(results)
    }
    
    async fn evaluate_condition(&self, condition: &Condition, event: &Event) -> Result<bool, RuleEngineError> {
        match condition {
            Condition::EventType(event_type) => {
                Ok(event.event_type == *event_type)
            },
            Condition::SourceMatch(pattern) => {
                let regex = Regex::new(pattern)
                    .map_err(|e| RuleEngineError::InvalidRegex(e.to_string()))?;
                Ok(regex.is_match(&event.source))
            },
            Condition::PropertyEquals { property, value } => {
                if let Some(prop_value) = event.data.get(property) {
                    Ok(prop_value == value)
                } else {
                    Ok(false)
                }
            },
            Condition::PropertyRange { property, min, max } => {
                if let Some(Value::Number(n)) = event.data.get(property) {
                    let value = n.as_f64().unwrap_or(f64::MIN);
                    Ok(value >= *min && value <= *max)
                } else {
                    Ok(false)
                }
            },
            Condition::And(conditions) => {
                let mut result = true;
                for cond in conditions {
                    if !self.evaluate_condition(cond, event).await? {
                        result = false;
                        break;
                    }
                }
                Ok(result)
            },
            Condition::Or(conditions) => {
                let mut result = false;
                for cond in conditions {
                    if self.evaluate_condition(cond, event).await? {
                        result = true;
                        break;
                    }
                }
                Ok(result)
            },
            Condition::Not(sub_condition) => {
                let result = self.evaluate_condition(sub_condition, event).await?;
                Ok(!result)
            },
            Condition::Sequence { events, window } => {
                // 检查事件序列
                let sequence_events = self.event_store.query(
                    EventQuery::new()
                        .source(event.source.clone())
                        .time_range(event.timestamp - *window, event.timestamp)
                        .limit(events.len() as u32 + 1)
                ).await?;
                
                if sequence_events.len() < events.len() {
                    return Ok(false);
                }
                
                // 检查事件序列是否匹配
                for (i, event_type) in events.iter().enumerate() {
                    if sequence_events[i].event_type != *event_type {
                        return Ok(false);
                    }
                }
                
                Ok(true)
            },
        }
    }
}

// 动作执行器
pub struct ActionExecutor {
    action_handlers: HashMap<String, Box<dyn ActionHandler>>,
}

impl ActionExecutor {
    pub fn new() -> Self {
        Self {
            action_handlers: HashMap::new(),
        }
    }
    
    pub fn register_handler(&mut self, action_type: &str, handler: Box<dyn ActionHandler>) -> &mut Self {
        self.action_handlers.insert(action_type.to_string(), handler);
        self
    }
    
    pub async fn execute(&self, action: &Action, event: &Event) -> Result<ActionResult, ActionError> {
        if let Some(handler) = self.action_handlers.get(&action.action_type) {
            handler.execute(action, event).await
        } else {
            return Err(ActionError::UnknownActionType(action.action_type.clone()));
        }
    }
}

// 动作处理器特征
#[async_trait]
pub trait ActionHandler: Send + Sync {
    async fn execute(&self, action: &Action, event: &Event) -> Result<ActionResult, ActionError>;
    fn action_type(&self) -> &str;
}

// 通知动作处理器
pub struct NotificationHandler {
    notification_service: Arc<dyn NotificationService>,
}

#[async_trait]
impl ActionHandler for NotificationHandler {
    async fn execute(&self, action: &Action, event: &Event) -> Result<ActionResult, ActionError> {
        // 解析通知配置
        let config = action.config.get("notification")
            .ok_or(ActionError::MissingConfig("notification".to_string()))?;
            
        let notification = Notification {
            recipient: config.get("recipient")
                .and_then(|v| v.as_str())
                .ok_or(ActionError::InvalidConfig("recipient must be a string".to_string()))?
                .to_string(),
            subject: config.get("subject")
                .and_then(|v| v.as_str())
                .unwrap_or(&format!("Event: {}", event.event_type))
                .to_string(),
            message: config.get("message")
                .and_then(|v| v.as_str())
                .unwrap_or(&serde_json::to_string_pretty(event).unwrap_or_default())
                .to_string(),
            importance: config.get("importance")
                .and_then(|v| v.as_str())
                .map(|s| match s {
                    "high" => NotificationImportance::High,
                    "low" => NotificationImportance::Low,
                    _ => NotificationImportance::Normal,
                })
                .unwrap_or(NotificationImportance::Normal),
        };
        
        // 发送通知
        let notification_id = self.notification_service.send_notification(notification).await?;
        
        Ok(ActionResult {
            action_id: Uuid::new_v4().to_string(),
            action_type: action.action_type.clone(),
            status: ActionStatus::Success,
            result_data: serde_json::json!({
                "notification_id": notification_id
            }),
        })
    }
    
    fn action_type(&self) -> &str {
        "notification"
    }
}

// 命令动作处理器
pub struct CommandHandler {
    device_registry: Arc<DeviceRegistry>,
    command_sender: Arc<CommandSender>,
}

#[async_trait]
impl ActionHandler for CommandHandler {
    async fn execute(&self, action: &Action, event: &Event) -> Result<ActionResult, ActionError> {
        // 解析命令配置
        let config = action.config.get("command")
            .ok_or(ActionError::MissingConfig("command".to_string()))?;
            
        let device_id = config.get("device_id")
            .and_then(|v| v.as_str())
            .ok_or(ActionError::InvalidConfig("device_id must be a string".to_string()))?;
            
        let command_type = config.get("type")
            .and_then(|v| v.as_str())
            .ok_or(ActionError::InvalidConfig("command type must be a string".to_string()))?;
            
        let command_params = config.get("parameters")
            .and_then(|v| v.as_object().cloned())
            .unwrap_or_default();
            
        // 获取设备信息
        let device = self.device_registry.get_device(device_id).await
            .map_err(|e| ActionError::DeviceNotFound(device_id.to_string()))?;
            
        // 创建命令
        let command = DeviceCommand {
            id: Uuid::new_v4().to_string(),
            device_id: device_id.to_string(),
            command_type: command_type.to_string(),
            parameters: command_params,
            created_at: Utc::now(),
            expires_at: Utc::now() + Duration::from_secs(300), // 5分钟过期
            status: CommandStatus::Pending,
            result: None,
        };
        
        // 发送命令
        let command_result = self.command_sender.send_command(command).await?;
        
        Ok(ActionResult {
            action_id: Uuid::new_v4().to_string(),
            action_type: action.action_type.clone(),
            status: ActionStatus::Success,
            result_data: serde_json::json!({
                "command_id": command_result.command_id,
                "status": command_result.status.to_string(),
            }),
        })
    }
    
    fn action_type(&self) -> &str {
        "command"
    }
}
```

#### 时序数据管理

```rust
// 时序数据模型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TimeSeriesPoint {
    timestamp: DateTime<Utc>,
    device_id: String,
    metric: String,
    value: f64,
    tags: HashMap<String, String>,
}

// 时序数据查询
#[derive(Debug, Clone)]
pub struct TimeSeriesQuery {
    devices: Vec<String>,
    metrics: Vec<String>,
    start_time: DateTime<Utc>,
    end_time: DateTime<Utc>,
    aggregation: Option<Aggregation>,
    filter: Option<Box<Condition>>,
    limit: Option<usize>,
}

impl TimeSeriesQuery {
    pub fn new() -> Self {
        Self {
            devices: Vec::new(),
            metrics: Vec::new(),
            start_time: Utc::now() - Duration::from_days(1),
            end_time: Utc::now(),
            aggregation: None,
            filter: None,
            limit: None,
        }
    }
    
    pub fn device(mut self, device_id: String) -> Self {
        self.devices.push(device_id);
        self
    }
    
    pub fn metric(mut self, metric: String) -> Self {
        self.metrics.push(metric);
        self
    }
    
    pub fn time_range(mut self, start: DateTime<Utc>, end: DateTime<Utc>) -> Self {
        self.start_time = start;
        self.end_time = end;
        self
    }
    
    pub fn aggregate(mut self, aggregation: Aggregation) -> Self {
        self.aggregation = Some(aggregation);
        self
    }
    
    pub fn filter(mut self, condition: Condition) -> Self {
        self.filter = Some(Box::new(condition));
        self
    }
    
    pub fn limit(mut self, limit: usize) -> Self {
        self.limit = Some(limit);
        self
    }
}

// 时序数据聚合
#[derive(Debug, Clone)]
pub enum Aggregation {
    Average { window: Duration },
    Sum { window: Duration },
    Min { window: Duration },
    Max { window: Duration },
    Count { window: Duration },
    Percentile { window: Duration, percentile: f64 },
    Custom { name: String, function: AggregationFunction },
}

// 时序数据管理器
pub struct TimeSeriesManager {
    writer: Arc<dyn TimeSeriesWriter>,
    reader: Arc<dyn TimeSeriesReader>,
    downsampler: Arc<TimeSeriesDownsampler>,
    retention_policy: RetentionPolicy,
    metrics: Arc<TimeSeriesMetrics>,
}

impl TimeSeriesManager {
    pub fn new(
        writer: Arc<dyn TimeSeriesWriter>,
        reader: Arc<dyn TimeSeriesReader>,
        retention_policy: RetentionPolicy,
    ) -> Self {
        let downsampler = Arc::new(TimeSeriesDownsampler::new(writer.clone()));
        let metrics = Arc::new(TimeSeriesMetrics::new());
        
        Self {
            writer,
            reader,
            downsampler,
            retention_policy,
            metrics,
        }
    }
    
    pub async fn write_points(&self, points: Vec<TimeSeriesPoint>) -> Result<(), TimeSeriesError> {
        let start = Instant::now();
        let count = points.len();
        
        // 写入数据点
        let result = self.writer.write(points).await;
        
        // 更新指标
        if result.is_ok() {
            self.metrics.record_write_success(count, start.elapsed());
        } else {
            self.metrics.record_write_failure(count);
        }
        
        result
    }
    
    pub async fn query(&self, query: TimeSeriesQuery) -> Result<TimeSeriesResult, TimeSeriesError> {
        let start = Instant::now();
        
        // 执行查询
        let result = self.reader.query(query).await;
        
        // 更新指标
        if let Ok(ref data) = result {
            self.metrics.record_query_success(
                data.points.len(),
                start.elapsed(),
            );
        } else {
            self.metrics.record_query_failure();
        }
        
        result
    }
    
    pub async fn start_maintenance(&self) -> Result<(), TimeSeriesError> {
        // 启动后台维护任务
        let writer = self.writer.clone();
        let downsampler = self.downsampler.clone();
        let retention = self.retention_policy.clone();
        
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(retention.maintenance_interval);
            
            loop {
                interval.tick().await;
                
                // 执行降采样
                if let Err(e) = downsampler.downsample().await {
                    log::error!("Error during downsampling: {}", e);
                }
                
                // 执行数据保留策略
                if let Err(e) = Self::enforce_retention(writer.as_ref(), &retention).await {
                    log::error!("Error enforcing retention policy: {}", e);
                }
            }
        });
        
        Ok(())
    }
    
    async fn enforce_retention(
        writer: &dyn TimeSeriesWriter,
        policy: &RetentionPolicy,
    ) -> Result<(), TimeSeriesError> {
        let cutoff = Utc::now() - policy.raw_data_ttl;
        
        // 删除过期数据
        writer.delete_before(cutoff).await?;
        
        Ok(())
    }
}

// 时序数据降采样器
pub struct TimeSeriesDownsampler {
    writer: Arc<dyn TimeSeriesWriter>,
    downsampling_rules: Vec<DownsamplingRule>,
}

impl TimeSeriesDownsampler {
    pub fn new(writer: Arc<dyn TimeSeriesWriter>) -> Self {
        Self {
            writer,
            downsampling_rules: Vec::new(),
        }
    }
    
    pub fn add_rule(&mut self, rule: DownsamplingRule) -> &mut Self {
        self.downsampling_rules.push(rule);
        self
    }
    
    pub async fn downsample(&self) -> Result<(), TimeSeriesError> {
        for rule in &self.downsampling_rules {
            let now = Utc::now();
            let start_time = now - rule.lookback_window;
            
            // 查询原始数据
            let query = TimeSeriesQuery::new()
                .metric(rule.source_metric.clone())
                .time_range(start_time, now);
                
            let data = self.writer.as_reader().query(query).await?;
            
            // 分组并聚合
            let aggregated_points = self.aggregate_points(&data.points, &rule.aggregation)?;
            
            // 写入降采样数据
            if !aggregated_points.is_empty() {
                self.writer.write(aggregated_points).await?;
            }
        }
        
        Ok(())
    }
    
    fn aggregate_points(
        &self,
        points: &[TimeSeriesPoint],
        aggregation: &Aggregation,
    ) -> Result<Vec<TimeSeriesPoint>, TimeSeriesError> {
        // 实现时间窗口聚合
        match aggregation {
            Aggregation::Average { window } => {
                // 按设备和窗口分组
                let mut groups: HashMap<(String, DateTime<Utc>), (f64, usize)> = HashMap::new();
                
                for point in points {
                    let window_start = Self::window_start(point.timestamp, *window);
                    let key = (point.device_id.clone(), window_start);
                    
                    let entry = groups.entry(key).or_insert((0.0, 0));
                    entry.0 += point.value;
                    entry.1 += 1;
                }
                
                // 计算每个组的平均值
                let mut result = Vec::with_capacity(groups.len());
                for ((device_id, timestamp), (sum, count)) in groups {
                    if count > 0 {
                        result.push(TimeSeriesPoint {
                            timestamp,
                            device_id,
                            metric: format!("{}.avg", points[0].metric),
                            value: sum / count as f64,
                            tags: points[0].tags.clone(),
                        });
                    }
                }
                
                Ok(result)
            },
            // 其他聚合类型...
            _ => Err(TimeSeriesError::UnsupportedAggregation(format!("{:?}", aggregation))),
        }
    }
    
    fn window_start(timestamp: DateTime<Utc>, window: Duration) -> DateTime<Utc> {
        let secs = timestamp.timestamp();
        let window_secs = window.as_secs() as i64;
        let window_start_secs = (secs / window_secs) * window_secs;
        
        Utc.timestamp_opt(window_start_secs, 0).unwrap()
    }
}
```

### 工作流引擎

工作流引擎是系统的核心，它协调任务执行、管理状态转换并响应事件。它允许定义复杂的自动化流程，处理IoT场景中的各种业务逻辑。

#### 工作流定义DSL

```rust
// 工作流定义
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkflowDefinition {
    id: String,
    name: String,
    version: Version,
    description: Option<String>,
    triggers: Vec<WorkflowTrigger>,
    states: HashMap<String, WorkflowState>,
    initial_state: String,
    variables: Vec<WorkflowVariable>,
    error_handler: Option<ErrorHandler>,
    metadata: HashMap<String, String>,
}

// 工作流变量
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkflowVariable {
    name: String,
    var_type: VariableType,
    default_value: Option<Value>,
    description: Option<String>,
}

// 工作流状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkflowState {
    name: String,
    state_type: StateType,
    actions: Vec<StateAction>,
    transitions: Vec<StateTransition>,
    timeout: Option<Duration>,
    retry: Option<RetryPolicy>,
}

// 状态类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum StateType {
    Task,
    Choice,
    Parallel,
    Map,
    Wait,
    Succeed,
    Fail,
}

// 工作流触发器
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkflowTrigger {
    trigger_type: TriggerType,
    condition: Option<Condition>,
    config: HashMap<String, Value>,
}

// 触发器类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TriggerType {
    Event { event_type: String },
    Schedule { cron: String },
    Api,
    DeviceState { device_id: String, state: String },
    MessageReceived { topic: String },
}

// 工作流解析器
pub struct WorkflowParser {
    registry: Arc<WorkflowRegistry>,
    validator: WorkflowValidator,
}

impl WorkflowParser {
    pub fn new(registry: Arc<WorkflowRegistry>) -> Self {
        Self {
            registry,
            validator: WorkflowValidator::new(),
        }
    }
    
    pub async fn parse_yaml(&self, yaml: &str) -> Result<WorkflowDefinition, WorkflowError> {
        // 解析YAML
        let definition: WorkflowDefinition = serde_yaml::from_str(yaml)
            .map_err(|e| WorkflowError::ParseError(e.to_string()))?;
            
        // 验证工作流定义
        self.validator.validate(&definition)?;
        
        Ok(definition)
    }
    
    pub async fn parse_json(&self, json: &str) -> Result<WorkflowDefinition, WorkflowError> {
        // 解析JSON
        let definition: WorkflowDefinition = serde_json::from_str(json)
            .map_err(|e| WorkflowError::ParseError(e.to_string()))?;
            
        // 验证工作流定义
        self.validator.validate(&definition)?;
        
        Ok(definition)
    }
    
    pub fn to_yaml(&self, definition: &WorkflowDefinition) -> Result<String, WorkflowError> {
        serde_yaml::to_string(definition)
            .map_err(|e| WorkflowError::SerializationError(e.to_string()))
    }
    
    pub fn to_json(&self, definition: &WorkflowDefinition) -> Result<String, WorkflowError> {
        serde_json::to_string_pretty(definition)
            .map_err(|e| WorkflowError::SerializationError(e.to_string()))
    }
}

// 工作流验证器
pub struct WorkflowValidator {
    validators: Vec<Box<dyn WorkflowValidationRule>>,
}

impl WorkflowValidator {
    pub fn new() -> Self {
        let mut validator = Self {
            validators: Vec::new(),
        };
        
        // 添加默认验证规则
        validator.add_rule(Box::new(InitialStateValidator));
        validator.add_rule(Box::new(NoUnreachableStatesValidator));
        validator.add_rule(Box::new(NoCircularDependenciesValidator));
        
        validator
    }
    
    pub fn add_rule(&mut self, rule: Box<dyn WorkflowValidationRule>) -> &mut Self {
        self.validators.push(rule);
        self
    }
    
    pub fn validate(&self, definition: &WorkflowDefinition) -> Result<(), WorkflowError> {
        // 应用所有验证规则
        for validator in &self.validators {
            validator.validate(definition)?;
        }
        
        Ok(())
    }
}

// 工作流验证规则特征
pub trait WorkflowValidationRule {
    fn validate(&self, definition: &WorkflowDefinition) -> Result<(), WorkflowError>;
    fn name(&self) -> &str;
}

// 初始状态验证器
pub struct InitialStateValidator;

impl WorkflowValidationRule for InitialStateValidator {
    fn validate(&self, definition: &WorkflowDefinition) -> Result<(), WorkflowError> {
        // 检查初始状态是否存在
        if !definition.states.contains_key(&definition.initial_state) {
            return Err(WorkflowError::ValidationError(
                format!("Initial state '{}' not found in workflow states", definition.initial_state)
            ));
        }
        
        Ok(())
    }
    
    fn name(&self) -> &str {
        "initial-state-validator"
    }
}

// 无不可达状态验证器
pub struct NoUnreachableStatesValidator;

impl WorkflowValidationRule for NoUnreachableStatesValidator {
    fn validate(&self, definition: &WorkflowDefinition) -> Result<(), WorkflowError> {
        // 从初始状态开始执行可达性分析
        let mut reachable = HashSet::new();
        let mut queue = VecDeque::new();
        
        // 添加初始状态
        queue.push_back(definition.initial_state.clone());
        reachable.insert(definition.initial_state.clone());
        
        // 广度优先搜索
        while let Some(state_name) = queue.pop_front() {
            if let Some(state) = definition.states.get(&state_name) {
                for transition in &state.transitions {
                    if !reachable.contains(&transition.target) {
                        reachable.insert(transition.target.clone());
                        queue.push_back(transition.target.clone());
                    }
                }
            }
        }
        
        // 检查是否有不可达状态
        for state_name in definition.states.keys() {
            if !reachable.contains(state_name) {
                return Err(WorkflowError::ValidationError(
                    format!("State '{}' is unreachable from initial state", state_name)
                ));
            }
        }
        
        Ok(())
    }
    
    fn name(&self) -> &str {
        "no-unreachable-states-validator"
    }
}

// 无循环依赖验证器
pub struct NoCircularDependenciesValidator;

impl WorkflowValidationRule for NoCircularDependenciesValidator {
    fn validate(&self, definition: &WorkflowDefinition) -> Result<(), WorkflowError> {
        let mut visiting = HashSet::new();
        let mut visited = HashSet::new();
        
        // 对每个状态执行DFS，检测循环
        for state_name in definition.states.keys() {
            if !visited.contains(state_name) {
                self.check_cycles(
                    state_name,
                    &definition.states,
                    &mut visiting,
                    &mut visited,
                )?;
            }
        }
        
        Ok(())
    }
    
    fn name(&self) -> &str {
        "no-circular-dependencies-validator"
    }
}

impl NoCircularDependenciesValidator {
    fn check_cycles(
        &self,
        current: &str,
        states: &HashMap<String, WorkflowState>,
        visiting: &mut HashSet<String>,
        visited: &mut HashSet<String>,
    ) -> Result<(), WorkflowError> {
        // 检查是否有循环
        if visiting.contains(current) {
            return Err(WorkflowError::ValidationError(
                format!("Circular dependency detected involving state '{}'", current)
            ));
        }
        
        // 标记当前正在访问
        visiting.insert(current.to_string());
        
        // 访问所有后继状态
        if let Some(state) = states.get(current) {
            for transition in &state.transitions {
                if !visited.contains(&transition.target) {
                    self.check_cycles(
                        &transition.target,
                        states,
                        visiting,
                        visited,
                    )?;
                }
            }
        }
        
        // 完成访问
        visiting.remove(current);
        visited.insert(current.to_string());
        
        Ok(())
    }
}

// 工作流DSL示例
pub fn create_device_monitoring_workflow() -> WorkflowDefinition {
    WorkflowDefinition {
        id: "device-monitoring".to_string(),
        name: "设备监控工作流".to_string(),
        version: Version::parse("1.0.0").unwrap(),
        description: Some("监控设备状态并在异常时触发警报".to_string()),
        triggers: vec![
            WorkflowTrigger {
                trigger_type: TriggerType::Event { 
                    event_type: "device.telemetry".to_string() 
                },
                condition: Some(Condition::PropertyRange {
                    property: "temperature".to_string(),
                    min: 0.0,
                    max: 100.0,
                }),
                config: HashMap::new(),
            },
        ],
        states: {
            let mut states = HashMap::new();
            
            states.insert("start".to_string(), WorkflowState {
                name: "开始".to_string(),
                state_type: StateType::Task,
                actions: vec![
                    StateAction {
                        action_type: "log".to_string(),
                        config: serde_json::json!({
                            "message": "开始设备监控工作流",
                            "level": "info"
                        }),
                    },
                ],
                transitions: vec![
                    StateTransition {
                        target: "check_temperature".to_string(),
                        condition: None,
                    },
                ],
                timeout: None,
                retry: None,
            });
            
            states.insert("check_temperature".to_string(), WorkflowState {
                name: "检查温度".to_string(),
                state_type: StateType::Choice,
                actions: vec![],
                transitions: vec![
                    StateTransition {
                        target: "high_temperature_alert".to_string(),
                        condition: Some(Condition::PropertyRange {
                            property: "temperature".to_string(),
                            min: 80.0,
                            max: f64::MAX,
                        }),
                    },
                    StateTransition {
                        target: "normal_operation".to_string(),
                        condition: Some(Condition::PropertyRange {
                            property: "temperature".to_string(),
                            min: 10.0,
                            max: 80.0,
                        }),
                    },
                    StateTransition {
                        target: "low_temperature_alert".to_string(),
                        condition: Some(Condition::PropertyRange {
                            property: "temperature".to_string(),
                            min: f64::MIN,
                            max: 10.0,
                        }),
                    },
                ],
                timeout: None,
                retry: None,
            });
            
            states.insert("high_temperature_alert".to_string(), WorkflowState {
                name: "高温警报".to_string(),
                state_type: StateType::Task,
                actions: vec![
                    StateAction {
                        action_type: "notification".to_string(),
                        config: serde_json::json!({
                            "notification": {
                                "recipient": "admin@example.com",
                                "subject": "设备高温警报",
                                "message": "设备 {{device_id}} 温度过高: {{temperature}}°C",
                                "importance": "high"
                            }
                        }),
                    },
                    StateAction {
                        action_type: "command".to_string(),
                        config: serde_json::json!({
                            "command": {
                                "device_id": "{{device_id}}",
                                "type": "cooling",
                                "parameters": {
                                    "mode": "max"
                                }
                            }
                        }),
                    },
                ],
                transitions: vec![
                    StateTransition {
                        target: "wait_for_cooldown".to_string(),
                        condition: None,
                    },
                ],
                timeout: Some(Duration::from_secs(60)),
                retry: Some(RetryPolicy {
                    max_attempts: 3,
                    delay: Duration::from_secs(5),
                    multiplier: 2.0,
                }),
            });
            
            // 省略其他状态...
            
            states
        },
        initial_state: "start".to_string(),
        variables: vec![
            WorkflowVariable {
                name: "device_id".to_string(),
                var_type: VariableType::String,
                default_value: None,
                description: Some("设备ID".to_string()),
            },
            WorkflowVariable {
                name: "temperature".to_string(),
                var_type: VariableType::Number,
                default_value: None,
                description: Some("设备温度读数".to_string()),
            },
        ],
        error_handler: Some(ErrorHandler {
            action: StateAction {
                action_type: "notification".to_string(),
                config: serde_json::json!({
                    "notification": {
                        "recipient": "errors@example.com",
                        "subject": "设备监控工作流错误",
                        "message": "设备 {{device_id}} 监控发生错误: {{error}}",
                        "importance": "high"
                    }
                }),
            },
            result_state: "error".to_string(),
        }),
        metadata: HashMap::new(),
    }
}
```

#### 有状态处理器

```rust
// 工作流实例
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkflowInstance {
    id: String,
    workflow_id: String,
    workflow_version: Version,
    current_state: String,
    variables: HashMap<String, Value>,
    status: WorkflowStatus,
    execution_history: Vec<StateExecution>,
    created_at: DateTime<Utc>,
    updated_at: DateTime<Utc>,
    correlation_id: Option<String>,
    metadata: HashMap<String, String>,
}

// 工作流状态
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum WorkflowStatus {
    Created,
    Running,
    Waiting,
    Succeeded,
    Failed,
    Terminated,
}

// 状态执行记录
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StateExecution {
    state_name: String,
    entered_at: DateTime<Utc>,
    exited_at: Option<DateTime<Utc>>,
    actions_results: Vec<ActionResult>,
    next_state: Option<String>,
    variables: HashMap<String, Value>,
    error: Option<StateError>,
}

// 工作流引擎
pub struct WorkflowEngine {
    registry: Arc<WorkflowRegistry>,
    instance_store: Arc<dyn WorkflowInstanceStore>,
    action_executor: Arc<ActionExecutor>,
    template_engine: Arc<TemplateEngine>,
    metrics: Arc<WorkflowMetrics>,
}

impl WorkflowEngine {
    pub fn new(
        registry: Arc<WorkflowRegistry>,
        instance_store: Arc<dyn WorkflowInstanceStore>,
        action_executor: Arc<ActionExecutor>,
    ) -> Self {
        Self {
            registry,
            instance_store,
            action_executor,
            template_engine: Arc::new(TemplateEngine::new()),
            metrics: Arc::new(WorkflowMetrics::new()),
        }
    }
    
    pub async fn start_workflow(
        &self,
        workflow_id: &str,
        variables: HashMap<String, Value>,
        correlation_id: Option<String>,
    ) -> Result<WorkflowInstance, WorkflowError> {
        let start_time = Instant::now();
        self.metrics.record_workflow_start(workflow_id);
        
        // 获取工作流定义
        let definition = self.registry.get_latest_version(workflow_id).await?;
        
        // 创建工作流实例
        let instance_id = Uuid::new_v4().to_string();
        let instance = WorkflowInstance {
            id: instance_id,
            workflow_id: definition.id.clone(),
            workflow_version: definition.version.clone(),
            current_state: definition.initial_state.clone(),
            variables,
            status: WorkflowStatus::Created,
            execution_history: Vec::new(),
            created_at: Utc::now(),
            updated_at: Utc::now(),
            correlation_id,
            metadata: HashMap::new(),
        };
        
        // 存储工作流实例
        self.instance_store.create(&instance).await?;
        
        // 开始执行工作流
        let mut running_instance = instance.clone();
        running_instance.status = WorkflowStatus::Running;
        
        self.instance_store.update(&running_instance).await?;
        
        // 异步执行工作流
        let engine = self.clone();
        let instance_id_clone = instance.id.clone();
        
        tokio::spawn(async move {
            if let Err(e) = engine.execute_workflow(&instance_id_clone).await {
                log::error!("Error executing workflow {}: {}", instance_id_clone, e);
            }
        });
        
        self.metrics.record_workflow_start_completed(workflow_id, start_time.elapsed());
        Ok(instance)
    }
    
    pub async fn execute_workflow(&self, instance_id: &str) -> Result<WorkflowInstance, WorkflowError> {
        // 加载工作流实例
        let mut instance = self.instance_store.get(instance_id).await?;
        
        // 检查实例状态
        if instance.status != WorkflowStatus::Running && instance.status != WorkflowStatus::Created {
            return Err(WorkflowError::InvalidState(format!(
                "Workflow instance is not in a runnable state: {:?}",
                instance.status
            )));
        }
        
        // 获取工作流定义
        let definition = self.registry.get_version(
            &instance.workflow_id,
            &instance.workflow_version,
        ).await?;
        
        // 执行当前状态
        while instance.status == WorkflowStatus::Running {
            let execution_start = Instant::now();
            
            // 获取当前状态
            let current_state_name = instance.current_state.clone();
            let current_state = definition.states.get(&current_state_name)
                .ok_or(WorkflowError::StateNotFound(current_state_name.clone()))?;
                
            self.metrics.record_state_entry(&definition.id, &current_state_name);
            
            // 创建状态执行记录
            let mut state_execution = StateExecution {
                state_name: current_state_name.clone(),
                entered_at: Utc::now(),
                exited_at: None,
                actions_results: Vec::new(),
                next_state: None,
                variables: instance.variables.clone(),
                error: None,
            };
            
            let mut next_state = None;
            
            // 执行状态动作
            match self.execute_state_actions(current_state, &mut instance, &mut state_execution).await {
                Ok(_) => {
                    // 确定下一个状态
                    match current_state.state_type {
                        StateType::Choice => {
                            // 选择分支
                            next_state = self.evaluate_transitions(
                                &current_state.transitions,
                                &instance.variables,
                            ).await?;
                        },
                        StateType::Succeed => {
                            // 成功终止
                            instance.status = WorkflowStatus::Succeeded;
                        },
                        StateType::Fail => {
                            // 失败终止
                            instance.status = WorkflowStatus::Failed;
                        },
                        _ => {
                            // 默认取第一个转换
                            if let Some(transition) = current_state.transitions.first() {
                                next_state = Some(transition.target.clone());
                            } else {
                                // 没有下一个状态，工作流完成
                                instance.status = WorkflowStatus::Succeeded;
                            }
                        }
                    }
                },
                Err(e) => {
                    // 处理错误
                    log::error!("Error executing state {}: {}", current_state_name, e);
                    state_execution.error = Some(StateError {
                        error_type: "ActionExecutionError".to_string(),
                        message: e.to_string(),
                        timestamp: Utc::now(),
                    });
                    
                    self.metrics.record_state_error(&definition.id, &current_state_name);
                    
                    // 使用错误处理程序
                    if let Some(ref error_handler) = definition.error_handler {
                        match self.action_executor.execute(&error_handler.action, &ActionContext {
                            workflow_instance: &instance,
                            variables: &instance.variables,
                            error: Some(e.to_string()),
                        }).await {
                            Ok(result) => {
                                state_execution.actions_results.push(result);
                            },
                            Err(action_err) => {
                                log::error!("Error handler failed: {}", action_err);
                            }
                        }
                        
                        next_state = Some(error_handler.result_state.clone());
                    } else {
                        // 没有错误处理程序，工作流失败
                        instance.status = WorkflowStatus::Failed;
                    }
                }
            }
            
            // 更新状态执行记录
            state_execution.exited_at = Some(Utc::now());
            state_execution.next_state = next_state.clone();
            
            // 添加到执行历史
            instance.execution_history.push(state_execution);
            
            // 更新当前状态
            if let Some(next) = next_state {
                instance.current_state = next;
            }

            // 更新工作流实例
            instance.updated_at = Utc::now();
            self.instance_store.update(&instance).await?;
            
            self.metrics.record_state_execution(&definition.id, &current_state_name, execution_start.elapsed());
            
            // 如果工作流已完成或失败，退出循环
            if instance.status != WorkflowStatus::Running {
                break;
            }
        }
        
        Ok(instance)
    }
    
    async fn execute_state_actions(
        &self,
        state: &WorkflowState,
        instance: &mut WorkflowInstance,
        execution: &mut StateExecution,
    ) -> Result<(), WorkflowError> {
        for action in &state.actions {
            // 准备上下文
            let context = ActionContext {
                workflow_instance: instance,
                variables: &instance.variables,
                error: None,
            };
            
            // 执行动作
            let result = match self.action_executor.execute(action, &context).await {
                Ok(result) => result,
                Err(e) => {
                    // 尝试重试
                    if let Some(retry_policy) = &state.retry {
                        let mut retry_count = 0;
                        let mut delay = retry_policy.delay;
                        
                        while retry_count < retry_policy.max_attempts {
                            // 等待重试延迟
                            tokio::time::sleep(delay).await;
                            retry_count += 1;
                            
                            // 重试执行
                            match self.action_executor.execute(action, &context).await {
                                Ok(retry_result) => {
                                    execution.actions_results.push(retry_result.clone());
                                    return Ok(());
                                },
                                Err(retry_error) => {
                                    log::warn!(
                                        "Retry {} failed for action {} in state {}: {}",
                                        retry_count, action.action_type, state.name, retry_error
                                    );
                                    
                                    // 增加重试延迟
                                    delay = Duration::from_secs(
                                        (delay.as_secs() as f64 * retry_policy.multiplier) as u64
                                    );
                                }
                            }
                        }
                    }
                    
                    // 重试失败或无重试策略，返回错误
                    return Err(WorkflowError::ActionExecutionError(
                        action.action_type.clone(),
                        e.to_string(),
                    ));
                }
            };
            
            // 保存执行结果
            execution.actions_results.push(result.clone());
            
            // 更新工作流变量
            if let Some(obj) = result.result_data.as_object() {
                for (key, value) in obj {
                    instance.variables.insert(format!("result.{}", key), value.clone());
                }
            }
        }
        
        Ok(())
    }
    
    async fn evaluate_transitions(
        &self,
        transitions: &[StateTransition],
        variables: &HashMap<String, Value>,
    ) -> Result<Option<String>, WorkflowError> {
        // 评估条件转换
        for transition in transitions {
            match &transition.condition {
                Some(condition) => {
                    if self.evaluate_condition(condition, variables).await? {
                        return Ok(Some(transition.target.clone()));
                    }
                },
                None => {
                    // 无条件转换作为默认路径
                    return Ok(Some(transition.target.clone()));
                }
            }
        }
        
        // 没有匹配的转换
        Ok(None)
    }
    
    async fn evaluate_condition(
        &self,
        condition: &Condition,
        variables: &HashMap<String, Value>,
    ) -> Result<bool, WorkflowError> {
        match condition {
            Condition::PropertyEquals { property, value } => {
                // 获取变量值
                let variable_value = variables.get(property);
                
                // 比较值
                Ok(variable_value.map_or(false, |v| v == value))
            },
            Condition::PropertyRange { property, min, max } => {
                // 获取变量值
                if let Some(Value::Number(n)) = variables.get(property) {
                    let value = n.as_f64().unwrap_or(f64::MIN);
                    Ok(value >= *min && value <= *max)
                } else {
                    Ok(false)
                }
            },
            Condition::And(conditions) => {
                // 所有条件都必须为真
                for cond in conditions {
                    if !self.evaluate_condition(cond, variables).await? {
                        return Ok(false);
                    }
                }
                Ok(true)
            },
            Condition::Or(conditions) => {
                // 至少一个条件为真
                for cond in conditions {
                    if self.evaluate_condition(cond, variables).await? {
                        return Ok(true);
                    }
                }
                Ok(false)
            },
            Condition::Not(sub_condition) => {
                // 对子条件取反
                let result = self.evaluate_condition(sub_condition, variables).await?;
                Ok(!result)
            },
            _ => Err(WorkflowError::UnsupportedCondition(
                format!("Condition type not supported in workflow transitions: {:?}", condition)
            )),
        }
    }
}

// 动作上下文
pub struct ActionContext<'a> {
    workflow_instance: &'a WorkflowInstance,
    variables: &'a HashMap<String, Value>,
    error: Option<String>,
}

// 模板引擎
pub struct TemplateEngine {
    environment: tera::Tera,
}

impl TemplateEngine {
    pub fn new() -> Self {
        let mut tera = tera::Tera::default();
        
        // 注册自定义过滤器和函数
        tera.register_filter("json_escape", Self::json_escape_filter);
        
        Self { environment: tera }
    }
    
    pub fn render(
        &self,
        template: &str,
        variables: &HashMap<String, Value>,
    ) -> Result<String, TemplateError> {
        // 转换变量为Tera上下文
        let mut context = tera::Context::new();
        
        for (key, value) in variables {
            context.insert(key, value);
        }
        
        // 渲染模板
        self.environment.render_str(template, &context)
            .map_err(|e| TemplateError::RenderError(e.to_string()))
    }
    
    // JSON转义过滤器
    fn json_escape_filter(
        value: &tera::Value,
        _args: &std::collections::HashMap<String, tera::Value>,
    ) -> tera::Result<tera::Value> {
        let s = tera::to_string(value)?;
        Ok(tera::Value::String(Self::escape_json_string(&s)))
    }
    
    fn escape_json_string(s: &str) -> String {
        let mut result = String::with_capacity(s.len() + 2);
        for c in s.chars() {
            match c {
                '"' => result.push_str("\\\""),
                '\\' => result.push_str("\\\\"),
                '/' => result.push_str("\\/"),
                '\b' => result.push_str("\\b"),
                '\f' => result.push_str("\\f"),
                '\n' => result.push_str("\\n"),
                '\r' => result.push_str("\\r"),
                '\t' => result.push_str("\\t"),
                _ => result.push(c),
            }
        }
        result
    }
}

// 工作流克隆支持
impl Clone for WorkflowEngine {
    fn clone(&self) -> Self {
        Self {
            registry: self.registry.clone(),
            instance_store: self.instance_store.clone(),
            action_executor: self.action_executor.clone(),
            template_engine: self.template_engine.clone(),
            metrics: self.metrics.clone(),
        }
    }
}
```

#### 触发器系统

```rust
// 工作流触发器管理器
pub struct WorkflowTriggerManager {
    registry: Arc<WorkflowRegistry>,
    engine: Arc<WorkflowEngine>,
    event_bus: Arc<dyn EventBus>,
    triggers: RwLock<HashMap<String, Vec<RegisteredTrigger>>>,
    scheduler: Arc<TaskScheduler>,
    metrics: Arc<TriggerMetrics>,
}

// 注册的触发器
struct RegisteredTrigger {
    workflow_id: String,
    workflow_version: Version,
    trigger: WorkflowTrigger,
}

impl WorkflowTriggerManager {
    pub fn new(
        registry: Arc<WorkflowRegistry>,
        engine: Arc<WorkflowEngine>,
        event_bus: Arc<dyn EventBus>,
        scheduler: Arc<TaskScheduler>,
    ) -> Self {
        Self {
            registry,
            engine,
            event_bus,
            triggers: RwLock::new(HashMap::new()),
            scheduler,
            metrics: Arc::new(TriggerMetrics::new()),
        }
    }
    
    pub async fn start(&self) -> Result<(), TriggerError> {
        // 加载所有工作流定义
        let definitions = self.registry.list_all_versions().await?;
        
        // 注册所有触发器
        for definition in definitions {
            self.register_workflow_triggers(&definition).await?;
        }
        
        // 订阅事件总线
        let event_bus_clone = self.event_bus.clone();
        let manager = Arc::new(self.clone());
        
        tokio::spawn(async move {
            let mut event_stream = event_bus_clone.subscribe_all().await.unwrap();
            
            while let Some(event) = event_stream.next().await {
                if let Err(e) = manager.handle_event(&event).await {
                    log::error!("Error handling event: {}", e);
                }
            }
        });
        
        Ok(())
    }
    
    pub async fn register_workflow_triggers(
        &self,
        definition: &WorkflowDefinition,
    ) -> Result<(), TriggerError> {
        let mut all_triggers = self.triggers.write().unwrap();
        
        for trigger in &definition.triggers {
            match &trigger.trigger_type {
                TriggerType::Event { event_type } => {
                    // 注册事件触发器
                    let triggers = all_triggers
                        .entry(event_type.clone())
                        .or_insert_with(Vec::new);
                        
                    triggers.push(RegisteredTrigger {
                        workflow_id: definition.id.clone(),
                        workflow_version: definition.version.clone(),
                        trigger: trigger.clone(),
                    });
                    
                    self.metrics.record_trigger_registered(&definition.id, "event");
                },
                TriggerType::Schedule { cron } => {
                    // 注册计划任务触发器
                    let workflow_id = definition.id.clone();
                    let workflow_version = definition.version.clone();
                    let trigger_clone = trigger.clone();
                    let engine = self.engine.clone();
                    let metrics = self.metrics.clone();
                    
                    self.scheduler.schedule_task(
                        cron,
                        move || {
                            let engine = engine.clone();
                            let trigger = trigger_clone.clone();
                            let workflow_id = workflow_id.clone();
                            let workflow_version = workflow_version.clone();
                            let metrics = metrics.clone();
                            
                            async move {
                                log::debug!("Scheduled trigger for workflow {}", workflow_id);
                                metrics.record_trigger_fired(&workflow_id, "schedule");
                                
                                let variables = HashMap::new();
                                match engine.start_workflow(&workflow_id, variables, None).await {
                                    Ok(instance) => {
                                        log::info!(
                                            "Started workflow instance {} from schedule",
                                            instance.id
                                        );
                                    },
                                    Err(e) => {
                                        log::error!(
                                            "Failed to start workflow from schedule: {}",
                                            e
                                        );
                                    }
                                }
                            }
                        }
                    )?;
                    
                    self.metrics.record_trigger_registered(&definition.id, "schedule");
                },
                TriggerType::Api => {
                    // API触发器由API端点处理，不需要在这里注册
                    self.metrics.record_trigger_registered(&definition.id, "api");
                },
                TriggerType::DeviceState { device_id, state } => {
                    // 注册设备状态触发器
                    let event_type = format!("device.state_changed.{}", device_id);
                    let triggers = all_triggers
                        .entry(event_type)
                        .or_insert_with(Vec::new);
                        
                    triggers.push(RegisteredTrigger {
                        workflow_id: definition.id.clone(),
                        workflow_version: definition.version.clone(),
                        trigger: trigger.clone(),
                    });
                    
                    self.metrics.record_trigger_registered(&definition.id, "device_state");
                },
                TriggerType::MessageReceived { topic } => {
                    // 注册消息触发器
                    let event_type = format!("message.received.{}", topic);
                    let triggers = all_triggers
                        .entry(event_type)
                        .or_insert_with(Vec::new);
                        
                    triggers.push(RegisteredTrigger {
                        workflow_id: definition.id.clone(),
                        workflow_version: definition.version.clone(),
                        trigger: trigger.clone(),
                    });
                    
                    self.metrics.record_trigger_registered(&definition.id, "message");
                },
            }
        }
        
        Ok(())
    }
    
    pub async fn handle_event(&self, event: &Event) -> Result<(), TriggerError> {
        let start_time = Instant::now();
        let all_triggers = self.triggers.read().unwrap();
        
        // 查找与事件类型匹配的触发器
        if let Some(triggers) = all_triggers.get(&event.event_type) {
            for trigger in triggers {
                if self.evaluate_trigger_condition(&trigger.trigger, event).await? {
                    self.metrics.record_trigger_fired(&trigger.workflow_id, "event");
                    
                    // 从事件构建变量
                    let mut variables = HashMap::new();
                    variables.insert("event".to_string(), serde_json::to_value(event)?);
                    
                    for (key, value) in &event.data {
                        variables.insert(format!("event.data.{}", key), value.clone());
                    }
                    
                    // 启动工作流
                    match self.engine.start_workflow(
                        &trigger.workflow_id,
                        variables,
                        Some(event.id.clone()),
                    ).await {
                        Ok(instance) => {
                            log::info!(
                                "Started workflow instance {} from event {}",
                                instance.id, event.id
                            );
                        },
                        Err(e) => {
                            log::error!(
                                "Failed to start workflow from event: {}",
                                e
                            );
                            self.metrics.record_trigger_error(&trigger.workflow_id, "event");
                        }
                    }
                }
            }
        }
        
        self.metrics.record_event_processing_time(event.event_type.clone(), start_time.elapsed());
        Ok(())
    }
    
    async fn evaluate_trigger_condition(
        &self,
        trigger: &WorkflowTrigger,
        event: &Event,
    ) -> Result<bool, TriggerError> {
        if let Some(ref condition) = trigger.condition {
            match condition {
                Condition::EventType(event_type) => {
                    Ok(event.event_type == *event_type)
                },
                Condition::PropertyEquals { property, value } => {
                    if let Some(event_value) = Self::get_property_from_event(event, property) {
                        Ok(event_value == *value)
                    } else {
                        Ok(false)
                    }
                },
                Condition::PropertyRange { property, min, max } => {
                    if let Some(Value::Number(n)) = Self::get_property_from_event(event, property) {
                        if let Some(value) = n.as_f64() {
                            Ok(value >= *min && value <= *max)
                        } else {
                            Ok(false)
                        }
                    } else {
                        Ok(false)
                    }
                },
                Condition::And(conditions) => {
                    for cond in conditions {
                        if !self.evaluate_trigger_condition(&WorkflowTrigger {
                            trigger_type: trigger.trigger_type.clone(),
                            condition: Some(cond.clone()),
                            config: trigger.config.clone(),
                        }, event).await? {
                            return Ok(false);
                        }
                    }
                    Ok(true)
                },
                Condition::Or(conditions) => {
                    for cond in conditions {
                        if self.evaluate_trigger_condition(&WorkflowTrigger {
                            trigger_type: trigger.trigger_type.clone(),
                            condition: Some(cond.clone()),
                            config: trigger.config.clone(),
                        }, event).await? {
                            return Ok(true);
                        }
                    }
                    Ok(false)
                },
                Condition::Not(sub_condition) => {
                    let result = self.evaluate_trigger_condition(&WorkflowTrigger {
                        trigger_type: trigger.trigger_type.clone(),
                        condition: Some((*sub_condition).clone()),
                        config: trigger.config.clone(),
                    }, event).await?;
                    Ok(!result)
                },
                _ => Err(TriggerError::UnsupportedCondition(
                    format!("Condition type not supported in workflow triggers: {:?}", condition)
                )),
            }
        } else {
            // 无条件表示总是触发
            Ok(true)
        }
    }
    
    fn get_property_from_event(event: &Event, property: &str) -> Option<Value> {
        if property.starts_with("data.") {
            let data_key = &property[5..];
            event.data.get(data_key).cloned()
        } else if property == "source" {
            Some(Value::String(event.source.clone()))
        } else if property == "timestamp" {
            Some(Value::String(event.timestamp.to_rfc3339()))
        } else {
            None
        }
    }
}

// 任务调度器
pub struct TaskScheduler {
    scheduler: tokio_cron_scheduler::JobScheduler,
}

impl TaskScheduler {
    pub fn new() -> Result<Self, SchedulerError> {
        let scheduler = tokio_cron_scheduler::JobScheduler::new()
            .map_err(|e| SchedulerError::InitializationError(e.to_string()))?;
            
        Ok(Self { scheduler })
    }
    
    pub fn schedule_task<F, Fut>(
        &self,
        cron: &str,
        task: F,
    ) -> Result<(), SchedulerError>
    where
        F: Fn() -> Fut + Send + Sync + 'static,
        Fut: Future<Output = ()> + Send + 'static,
    {
        let job = tokio_cron_scheduler::Job::new(cron, move |_uuid, _lock| {
            let future = task();
            tokio::spawn(future);
        })
        .map_err(|e| SchedulerError::JobCreationError(e.to_string()))?;
        
        self.scheduler
            .add(job)
            .map_err(|e| SchedulerError::JobRegistrationError(e.to_string()))?;
            
        Ok(())
    }
    
    pub fn start(&self) -> Result<(), SchedulerError> {
        self.scheduler
            .start()
            .map_err(|e| SchedulerError::StartError(e.to_string()))?;
            
        Ok(())
    }
    
    pub async fn shutdown(&self) -> Result<(), SchedulerError> {
        self.scheduler
            .shutdown()
            .await
            .map_err(|e| SchedulerError::ShutdownError(e.to_string()))?;
            
        Ok(())
    }
}

// 工作流管理器
pub struct WorkflowManager {
    registry: Arc<WorkflowRegistry>,
    engine: Arc<WorkflowEngine>,
    trigger_manager: Arc<WorkflowTriggerManager>,
    instance_store: Arc<dyn WorkflowInstanceStore>,
}

impl WorkflowManager {
    pub fn new(
        registry: Arc<WorkflowRegistry>,
        engine: Arc<WorkflowEngine>,
        trigger_manager: Arc<WorkflowTriggerManager>,
        instance_store: Arc<dyn WorkflowInstanceStore>,
    ) -> Self {
        Self {
            registry,
            engine,
            trigger_manager,
            instance_store,
        }
    }
    
    pub async fn deploy_workflow(
        &self,
        definition: WorkflowDefinition,
    ) -> Result<(), WorkflowError> {
        // 验证工作流定义
        let validator = WorkflowValidator::new();
        validator.validate(&definition)?;
        
        // 添加到注册表
        self.registry.register_workflow(definition.clone()).await?;
        
        // 注册触发器
        self.trigger_manager.register_workflow_triggers(&definition).await?;
        
        log::info!(
            "Deployed workflow {} version {}",
            definition.id,
            definition.version
        );
        
        Ok(())
    }
    
    pub async fn undeploy_workflow(
        &self,
        workflow_id: &str,
        version: Option<&Version>,
    ) -> Result<(), WorkflowError> {
        // 从注册表中移除
        match version {
            Some(ver) => {
                self.registry.remove_workflow_version(workflow_id, ver).await?;
                log::info!("Undeployed workflow {} version {}", workflow_id, ver);
            },
            None => {
                self.registry.remove_workflow(workflow_id).await?;
                log::info!("Undeployed all versions of workflow {}", workflow_id);
            }
        }
        
        // 触发器会在下次启动时刷新
        
        Ok(())
    }
    
    pub async fn start_workflow(
        &self,
        workflow_id: &str,
        variables: HashMap<String, Value>,
        correlation_id: Option<String>,
    ) -> Result<WorkflowInstance, WorkflowError> {
        self.engine.start_workflow(workflow_id, variables, correlation_id).await
    }
    
    pub async fn terminate_workflow(
        &self,
        instance_id: &str,
        reason: &str,
    ) -> Result<WorkflowInstance, WorkflowError> {
        // 获取工作流实例
        let mut instance = self.instance_store.get(instance_id).await?;
        
        // 检查实例是否可以终止
        if instance.status != WorkflowStatus::Running && instance.status != WorkflowStatus::Waiting {
            return Err(WorkflowError::InvalidState(format!(
                "Cannot terminate workflow in state: {:?}",
                instance.status
            )));
        }
        
        // 更新实例状态
        instance.status = WorkflowStatus::Terminated;
        instance.updated_at = Utc::now();
        
        // 添加终止原因到元数据
        instance.metadata.insert("termination_reason".to_string(), reason.to_string());
        
        // 存储更新后的实例
        self.instance_store.update(&instance).await?;
        
        log::info!("Terminated workflow instance {}: {}", instance_id, reason);
        
        Ok(instance)
    }
    
    pub async fn list_workflow_instances(
        &self,
        workflow_id: Option<&str>,
        status: Option<WorkflowStatus>,
        limit: Option<usize>,
    ) -> Result<Vec<WorkflowInstance>, WorkflowError> {
        self.instance_store.list(workflow_id, status, limit).await
    }
    
    pub async fn get_workflow_instance(
        &self,
        instance_id: &str,
    ) -> Result<WorkflowInstance, WorkflowError> {
        self.instance_store.get(instance_id).await
    }
}
```

### 分布式协调

分布式协调层提供了跨节点的状态共享、一致性保证和任务分配机制，确保系统在分布式环境中可靠运行。

#### 共识机制

```rust
// 分布式共识接口
#[async_trait]
pub trait ConsensusProtocol: Send + Sync {
    async fn submit_entry(&self, data: Vec<u8>) -> Result<LogIndex, ConsensusError>;
    async fn read_entry(&self, index: LogIndex) -> Result<Option<LogEntry>, ConsensusError>;
    async fn get_leader(&self) -> Result<NodeId, ConsensusError>;
    async fn get_last_index(&self) -> Result<LogIndex, ConsensusError>;
    async fn subscribe(&self) -> Result<LogStream, ConsensusError>;
}

// 日志索引类型
pub type LogIndex = u64;

// 节点ID类型
pub type NodeId = String;

// 日志条目
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LogEntry {
    index: LogIndex,
    term: u64,
    data: Vec<u8>,
    timestamp: DateTime<Utc>,
}

// 日志流
pub struct LogStream {
    receiver: mpsc::Receiver<LogEntry>,
}

impl LogStream {
    pub fn new(receiver: mpsc::Receiver<LogEntry>) -> Self {
        Self { receiver }
    }
    
    pub async fn next(&mut self) -> Option<LogEntry> {
        self.receiver.recv().await
    }
}

// 基于Raft的共识实现
pub struct RaftConsensus {
    node_id: NodeId,
    peers: Vec<NodeId>,
    state: Arc<RwLock<RaftState>>,
    log: Arc<dyn LogStore>,
    transport: Arc<dyn RpcTransport>,
    notification_tx: mpsc::Sender<LogEntry>,
    timeout_config: RaftTimeoutConfig,
    metrics: Arc<ConsensusMetrics>,
}

// Raft状态
#[derive(Debug)]
struct RaftState {
    // 持久化状态
    current_term: u64,
    voted_for: Option<NodeId>,
    
    // 易失性状态
    commit_index: LogIndex,
    last_applied: LogIndex,
    role: RaftRole,
    leader_id: Option<NodeId>,
    
    // 领导者状态
    next_index: HashMap<NodeId, LogIndex>,
    match_index: HashMap<NodeId, LogIndex>,
    
    // 选举状态
    election_timer: Instant,
}

// Raft角色
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum RaftRole {
    Follower,
    Candidate,
    Leader,
}

// Raft超时配置
#[derive(Debug, Clone)]
struct RaftTimeoutConfig {
    election_timeout_min: Duration,
    election_timeout_max: Duration,
    heartbeat_interval: Duration,
}

impl RaftConsensus {
    pub async fn new(
        node_id: NodeId,
        peers: Vec<NodeId>,
        log_store: Arc<dyn LogStore>,
        transport: Arc<dyn RpcTransport>,
        timeout_config: RaftTimeoutConfig,
    ) -> Result<Self, ConsensusError> {
        // 创建通知通道
        let (notification_tx, notification_rx) = mpsc::channel(100);
        
        // 初始化Raft状态
        let state = Arc::new(RwLock::new(RaftState {
            current_term: 0,
            voted_for: None,
            commit_index: 0,
            last_applied: 0,
            role: RaftRole::Follower,
            leader_id: None,
            next_index: peers.iter().map(|p| (p.clone(), 1)).collect(),
            match_index: peers.iter().map(|p| (p.clone(), 0)).collect(),
            election_timer: Instant::now(),
        }));
        
        let metrics = Arc::new(ConsensusMetrics::new(&node_id));
        
        let consensus = Self {
            node_id,
            peers,
            state,
            log: log_store,
            transport,
            notification_tx,
            timeout_config,
            metrics,
        };
        
        // 启动Raft主循环
        let consensus_clone = consensus.clone();
        tokio::spawn(async move {
            consensus_clone.run().await;
        });
        
        Ok(consensus)
    }
    
    async fn run(&self) {
        let mut election_timer = tokio::time::interval(
            self.timeout_config.election_timeout_min / 2
        );
        
        let mut heartbeat_timer = tokio::time::interval(
            self.timeout_config.heartbeat_interval
        );
        
        loop {
            tokio::select! {
                _ = election_timer.tick() => {
                    self.check_election_timeout().await;
                }
                _ = heartbeat_timer.tick() => {
                    self.send_heartbeat_if_leader().await;
                }
                Some(rpc) = self.transport.receive() => {
                    self.handle_rpc(rpc).await;
                }
            }
        }
    }
    
    async fn check_election_timeout(&self) {
        let mut state = self.state.write().unwrap();
        
        // 只有追随者和候选人需要检查选举超时
        if state.role != RaftRole::Leader {
            let now = Instant::now();
            let timeout = rand::thread_rng().gen_range(
                self.timeout_config.election_timeout_min..self.timeout_config.election_timeout_max
            );
            
            if now.duration_since(state.election_timer) >= timeout {
                // 选举超时，转换为候选人并开始新的选举
                state.current_term += 1;
                state.role = RaftRole::Candidate;
                state.voted_for = Some(self.node_id.clone());
                state.election_timer = now;
                
                self.metrics.record_role_change("candidate");
                self.metrics.record_term_change(state.current_term);
                
                let term = state.current_term;
                drop(state); // 释放锁
                
                // 开始选举
                self.start_election(term).await;
            }
        }
    }
    
    async fn start_election(&self, term: u64) {
        log::info!("Starting election for term {}", term);
        
        // 请求选票
        let last_log_index = self.log.get_last_index().await.unwrap_or(0);
        let last_log_term = if last_log_index > 0 {
            self.log.get_entry(last_log_index).await
                .map(|entry| entry.map_or(0, |e| e.term))
                .unwrap_or(0)
        } else {
            0
        };
        
        let mut votes_received = 1; // 包括自己的投票
        let votes_needed = (self.peers.len() + 1) / 2 + 1; // 多数
        
        // 向所有对等节点请求投票
        let mut vote_futures = Vec::new();
        
        for peer in &self.peers {
            let request = RequestVoteRequest {
                term,
                candidate_id: self.node_id.clone(),
                last_log_index,
                last_log_term,
            };
            
            let peer_clone = peer.clone();
            let transport = self.transport.clone();
            let metrics = self.metrics.clone();
            
            let vote_future = tokio::spawn(async move {
                match transport.send_rpc(&peer_clone, RaftRpc::RequestVote(request.clone())).await {
                    Ok(RaftRpc::RequestVoteResponse(response)) => {
                        if response.vote_granted {
                            metrics.record_vote_received(&peer_clone);
                            Ok(true)
                        } else {
                            // 如果对方任期更高，可能需要转为跟随者
                            if response.term > term {
                                Err(response.term)
                            } else {
                                Ok(false)
                            }
                        }
                    }
                    Ok(_) => Ok(false), // 收到错误类型的响应
                    Err(e) => {
                        log::error!("Failed to request vote from {}: {}", peer_clone, e);
                        Ok(false)
                    }
                }
            });
            
            vote_futures.push(vote_future);
        }
        
        // 收集投票
        for vote_future in vote_futures {
            match vote_future.await {
                Ok(Ok(vote_granted)) => {
                    if vote_granted {
                        votes_received += 1;
                        
                        // 检查是否已获得多数票
                        if votes_received >= votes_needed {
                            self.become_leader().await;
                            return;
                        }
                    }
                }
                Ok(Err(higher_term)) => {
                    // 收到更高任期，转为跟随者
                    self.step_down(higher_term).await;
                    return;
                }
                Err(e) => {
                    log::error!("Vote future failed: {}", e);
                }
            }
        }
        
        // 如果没有获得足够的票，保持候选人状态，等待下一次选举超时
        log::info!("Election for term {} failed, received {} votes", term, votes_received);
    }
    
    async fn become_leader(&self) {
        let mut state = self.state.write().unwrap();
        
        // 确保我们仍然是候选人
        if state.role == RaftRole::Candidate {
            log::info!("Node {} becoming leader for term {}", self.node_id, state.current_term);
            
            state.role = RaftRole::Leader;
            state.leader_id = Some(self.node_id.clone());
            
            // 重置领导者状态
            let last_log_index = self.log.get_last_index().await.unwrap_or(0);
            
            for peer in &self.peers {
                state.next_index.insert(peer.clone(), last_log_index + 1);
                state.match_index.insert(peer.clone(), 0);
            }
            
            self.metrics.record_role_change("leader");
            self.metrics.record_leader_change(&self.node_id);
            
            // 立即发送心跳，建立领导权
            drop(state);
            self.send_heartbeat().await;
        }
    }
    
    async fn step_down(&self, term: u64) {
        let mut state = self.state.write().unwrap();
        
        // 如果新任期高于当前任期，更新任期并转为跟随者
        if term > state.current_term {
            log::info!("Stepping down to follower: observed term {} > current term {}", term, state.current_term);
            
            state.current_term = term;
            state.role = RaftRole::Follower;
            state.voted_for = None;
            state.leader_id = None;
            state.election_timer = Instant::now(); // 重置选举计时器
            
            self.metrics.record_role_change("follower");
            self.metrics.record_term_change(term);
        }
    }
    
    async fn send_heartbeat_if_leader(&self) {
        let state = self.state.read().unwrap();
        
        if state.role == RaftRole::Leader {
            drop(state);
            self.send_heartbeat().await;
        }
    }
    
    async fn send_heartbeat(&self) {
        let state = self.state.read().unwrap();
        let term = state.current_term;
        let commit_index = state.commit_index;
        drop(state);
        
        for peer in &self.peers {
            let next_index = self.state.read().unwrap().next_index.get(peer).cloned().unwrap_or(1);
            
            // 准备附加条目请求（心跳是空的附加条目请求）
            let prev_log_index = next_index - 1;
            let prev_log_term = if prev_log_index > 0 {
                match self.log.get_entry(prev_log_index).await {
                    Ok(Some(entry)) => entry.term,
                    _ => 0,
                }
            } else {
                0
            };
            
            // 准备要发送的日志条目（如果有）
            let entries = match self.log.get_entries(next_index, 100).await {
                Ok(entries) => entries,
                Err(e) => {
                    log::error!("Failed to get log entries: {}", e);
                    Vec::new()
                }
            };
            
            // 创建附加条目请求
            let request = AppendEntriesRequest {
                term,
                leader_id: self.node_id.clone(),
                prev_log_index,
                prev_log_term,
                entries,
                leader_commit: commit_index,
            };
            
            let peer_clone = peer.clone();
            let transport = self.transport.clone();
            let metrics = self.metrics.clone();
            let self_clone = self.clone();
            
            // 异步发送心跳
            tokio::spawn(async move {
                metrics.record_heartbeat_sent(&peer_clone);
                
                match transport.send_rpc(&peer_clone, RaftRpc::AppendEntries(request.clone())).await {
                    Ok(RaftRpc::AppendEntriesResponse(response)) => {
                        self_clone.handle_append_entries_response(
                            &peer_clone,
                            request,
                            response,
                        ).await;
                    }
                    Ok(_) => {
                        log::warn!("Received unexpected RPC response type");
                    }
                    Err(e) => {
                        log::error!("Failed to send heartbeat to {}: {}", peer_clone, e);
                        metrics.record_heartbeat_failed(&peer_clone);
                    }
                }
            });
        }
    }
    
    async fn handle_append_entries_response(
        &self,
        peer: &str,
        request: AppendEntriesRequest,
        response: AppendEntriesResponse,
    ) {
        // 如果收到更高的任期，转为跟随者
        if response.term > request.term {
            self.step_down(response.term).await;
            return;
        }
        
        // 仅当我们仍然是领导者时才处理响应
        let mut state = self.state.write().unwrap();
        if state.role != RaftRole::Leader || state.current_term != request.term {
            return;
        }
        
        if response.success {
            // 更新匹配索引和下一个索引
            let match_index = request.prev_log_index + request.entries.len() as u64;
            let next_index = match_index + 1;
            
            state.match_index.insert(peer.to_string(), match_index);
            state.next_index.insert(peer.to_string(), next_index);
            
            // 更新提交索引
            self.update_commit_index(&mut state).await;
        } else {
            // 附加失败，减小下一个索引并重试
            let next_index = state.next_index.get(peer).cloned().unwrap_or(1);
            if next_index > 1 {
                state.next_index.insert(peer.to_string(), next_index - 1);
            }
            
            // 在下一个心跳周期重试
        }
    }
    
    async fn update_commit_index(&self, state: &mut RaftState) {
        // 计算可以安全提交的新索引
        let last_log_index = match self.log.get_last_index().await {
            Ok(index) => index,
            Err(_) => return,
        };
        
        // 收集所有匹配索引，包括自己的
        let mut match_indices = state.match_index.values().cloned().collect::<Vec<_>>();
        match_indices.push(last_log_index);
        
        // 排序并取中位数
        match_indices.sort_unstable();
        let median_index = match_indices[match_indices.len() / 2];
        
        // 确保中位数索引的任期与当前任期匹配
        if median_index > state.commit_index {
            match self.log.get_entry(median_index).await {
                Ok(Some(entry)) if entry.term == state.current_term => {
                    // 更新提交索引
                    let old_commit_index = state.commit_index;
                    state.commit_index = median_index;
                    
                    if median_index > old_commit_index {
                        self.metrics.record_commit_index_change(median_index);
                        
                        // 通知新提交的条目
                        let entries = match self.log.get_entries(old_commit_index + 1, median_index - old_commit_index as usize + 1).await {
                            Ok(entries) => entries,
                            Err(_) => Vec::new(),
                        };
                        
                        for entry in entries {
                            if let Err(e) = self.notification_tx.send(entry.clone()).await {
                                log::error!("Failed to send committed entry notification: {}", e);
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }
    
    async fn handle_rpc(&self, rpc: RaftRpc) -> Result<RaftRpc, ConsensusError> {
        match rpc {
            RaftRpc::AppendEntries(request) => {
                Ok(RaftRpc::AppendEntriesResponse(self.handle_append_entries(request).await?))
            }
            RaftRpc::RequestVote(request) => {
                Ok(RaftRpc::RequestVoteResponse(self.handle_request_vote(request).await?))
            }
            _ => Err(ConsensusError::InvalidRpc),
        }
    }
    
    async fn handle_append_entries(
        &self,
        request: AppendEntriesRequest,
    ) -> Result<AppendEntriesResponse, ConsensusError> {
        let mut state = self.state.write().unwrap();
        
        // 回复失败如果领导者任期小于当前任期
        if request.term < state.current_term {
            return Ok(AppendEntriesResponse {
                term: state.current_term,
                success: false,
            });
        }
        
        // 如果收到更高任期，更新当前任期并转为跟随者
        if request.term > state.current_term {
            state.current_term = request.term;
            state.role = RaftRole::Follower;
            state.voted_for = None;
            
            self.metrics.record_term_change(request.term);
            self.metrics.record_role_change("follower");
        }
        
        // 更新领导者信息并重置选举计时器
        state.leader_id = Some(request.leader_id.clone());
        state.election_timer = Instant::now();
        
        self.metrics.record_heartbeat_received(&request.leader_id);
        
        // 检查日志一致性
        let prev_log_exists = if request.prev_log_index == 0 {
            true
        } else {
            match self.log.get_entry(request.prev_log_index).await {
                Ok(Some(entry)) => entry.term == request.prev_log_term,
                _ => false,
            }
        };
        
        if !prev_log_exists {
            return Ok(AppendEntriesResponse {
                term: state.current_term,
                success: false,
            });
        }
        
        // 附加新条目
        if !request.entries.is_empty() {
            // 删除冲突的现有条目
            let mut conflict_index = None;
            
            for (i, entry) in request.entries.iter().enumerate() {
                let log_index = request.prev_log_index + 1 + i as u64;
                
                match self.log.get_entry(log_index).await {
                    Ok(Some(existing_entry)) if existing_entry.term != entry.term => {
                        conflict_index = Some(log_index);
                        break;
                    }
                    Ok(None) => break, // 到达日志末尾
                    _ => {}
                }
            }
            
            // 如果有冲突，截断日志
            if let Some(index) = conflict_index {
                if let Err(e) = self.log.truncate(index).await {
                    log::error!("Failed to truncate log: {}", e);
                    return Ok(AppendEntriesResponse {
                        term: state.current_term,
                        success: false,
                    });
                }
            }
            
            // 追加新条目
            if let Err(e) = self.log.append_entries(&request.entries).await {
                log::error!("Failed to append entries: {}", e);
                return Ok(AppendEntriesResponse {
                    term: state.current_term,
                    success: false,
                });
            }
        }
        
        // 更新提交索引
        if request.leader_commit > state.commit_index {
            let last_new_index = request.prev_log_index + request.entries.len() as u64;
            state.commit_index = std::cmp::min(request.leader_commit, last_new_index);
            
            self.metrics.record_commit_index_change(state.commit_index);
            
            // 通知新提交的条目
            let entries = match self.log.get_entries(state.last_applied + 1, (state.commit_index - state.last_applied) as usize).await {
                Ok(entries) => entries,
                Err(_) => Vec::new(),
            };
            
            for entry in entries {
                if let Err(e) = self.notification_tx.send(entry.clone()).await {
                    log::error!("Failed to send committed entry notification: {}", e);
                }
                state.last_applied += 1;
            }
        }
        
        Ok(AppendEntriesResponse {
            term: state.current_term,
            success: true,
        })
    }
    
    async fn handle_request_vote(
        &self,
        request: RequestVoteRequest,
    ) -> Result<RequestVoteResponse, ConsensusError> {
        let mut state = self.state.write().unwrap();
        
        // 如果请求任期小于当前任期，拒绝投票
        if request.term < state.current_term {
            return Ok(RequestVoteResponse {
                term: state.current_term,
                vote_granted: false,
            });
        }
        
        // 如果收到更高任期，更新当前任期并转为跟随者
        if request.term > state.current_term {
            state.current_term = request.term;
            state.role = RaftRole::Follower;
            state.voted_for = None;
            
            self.metrics.record_term_change(request.term);
            self.metrics.record_role_change("follower");
        }
        
        // 检查是否可以投票
        let can_vote = match &state.voted_for {
            None => true,
            Some(candidate_id) => candidate_id == &request.candidate_id,
        };
        
        // 检查日志是否至少与自己的一样新
        let last_log_index = self.log.get_last_index().await.unwrap_or(0);
        let last_log_term = if last_log_index > 0 {
            match self.log.get_entry(last_log_index).await {
                Ok(Some(entry)) => entry.term,
                _ => 0,
            }
        } else {
            0
        };
        
        let log_is_up_to_date = (request.last_log_term > last_log_term) ||
            (request.last_log_term == last_log_term && request.last_log_index >= last_log_index);
            
        // 决定是否授予投票
        let vote_granted = can_vote && log_is_up_to_date;
        
        if vote_granted {
            // 更新投票信息并重置选举计时器
            state.voted_for = Some(request.candidate_id.clone());
            state.election_timer = Instant::now();
            
            self.metrics.record_vote_granted(&request.candidate_id);
        }
        
        Ok(RequestVoteResponse {
            term: state.current_term,
            vote_granted,
        })
    }
}

// 实现ConsensusProtocol特征
#[async_trait]
impl ConsensusProtocol for RaftConsensus {
    async fn submit_entry(&self, data: Vec<u8>) -> Result<LogIndex, ConsensusError> {
        let state = self.state.read().unwrap();
        
        // 只有领导者可以提交条目
        if state.role != RaftRole::Leader {
            return Err(ConsensusError::NotLeader);
        }
        
        let term = state.current_term;
        drop(state);
        
        // 创建日志条目
        let last_index = self.log.get_last_index().await?;
        let entry = LogEntry {
            index: last_index + 1,
            term,
            data,
            timestamp: Utc::now(),
        };
        
        // 追加到本地日志
        self.log.append_entry(&entry).await?;
        
        // 异步复制到其他节点
        self.send_heartbeat().await;
        
        Ok(entry.index)
    }
    
    async fn read_entry(&self, index: LogIndex) -> Result<Option<LogEntry>, ConsensusError> {
        // 读取指定索引的日志条目
        let state = self.state.read().unwrap();
        
        // 只有当索引已提交时才返回条目
        if index <= state.commit_index {
            drop(state);
            return self.log.get_entry(index).await
                .map_err(|e| ConsensusError::StorageError(e.to_string()));
        }
        
        Err(ConsensusError::EntryNotCommitted)
    }
    
    async fn get_leader(&self) -> Result<NodeId, ConsensusError> {
        let state = self.state.read().unwrap();
        
        if let Some(leader_id) = &state.leader_id {
            Ok(leader_id.clone())
        } else {
            Err(ConsensusError::NoLeader)
        }
    }
    
    async fn get_last_index(&self) -> Result<LogIndex, ConsensusError> {
        self.log.get_last_index().await
            .map_err(|e| ConsensusError::StorageError(e.to_string()))
    }
    
    async fn subscribe(&self) -> Result<LogStream, ConsensusError> {
        // 创建新的通知通道
        let (tx, rx) = mpsc::channel(100);
        
        // 复制当前通知发送器
        let mut current_tx = self.notification_tx.clone();
        
        // 创建转发任务
        tokio::spawn(async move {
            while let Some(entry) = current_tx.recv().await {
                if let Err(_) = tx.send(entry).await {
                    break; // 订阅者已断开连接
                }
            }
        });
        
        Ok(LogStream::new(rx))
    }
}

// 日志存储接口
#[async_trait]
pub trait LogStore: Send + Sync {
    async fn append_entry(&self, entry: &LogEntry) -> Result<(), LogStoreError>;
    async fn append_entries(&self, entries: &[LogEntry]) -> Result<(), LogStoreError>;
    async fn get_entry(&self, index: LogIndex) -> Result<Option<LogEntry>, LogStoreError>;
    async fn get_entries(&self, start: LogIndex, limit: usize) -> Result<Vec<LogEntry>, LogStoreError>;
    async fn get_last_index(&self) -> Result<LogIndex, LogStoreError>;
    async fn truncate(&self, index: LogIndex) -> Result<(), LogStoreError>;
}

// RPC传输接口
#[async_trait]
pub trait RpcTransport: Send + Sync {
    async fn send_rpc(&self, target: &str, rpc: RaftRpc) -> Result<RaftRpc, RpcError>;
    async fn receive(&self) -> Option<RaftRpc>;
}

// Raft RPC消息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RaftRpc {
    AppendEntries(AppendEntriesRequest),
    AppendEntriesResponse(AppendEntriesResponse),
    RequestVote(RequestVoteRequest),
    RequestVoteResponse(RequestVoteResponse),
}

// 附加条目请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AppendEntriesRequest {
    term: u64,
    leader_id: NodeId,
    prev_log_index: LogIndex,
    prev_log_term: u64,
    entries: Vec<LogEntry>,
    leader_commit: LogIndex,
}

// 附加条目响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AppendEntriesResponse {
    term: u64,
    success: bool,
}

// 请求投票请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RequestVoteRequest {
    term: u64,
    candidate_id: NodeId,
    last_log_index: LogIndex,
    last_log_term: u64,
}

// 请求投票响应
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RequestVoteResponse {
    term: u64,
    vote_granted: bool,
}

// 共识服务
pub struct ConsensusService {
    consensus: Arc<dyn ConsensusProtocol>,
    state_machine: Arc<dyn StateMachine>,
}

impl ConsensusService {
    pub fn new(
        consensus: Arc<dyn ConsensusProtocol>,
        state_machine: Arc<dyn StateMachine>,
    ) -> Self {
        Self {
            consensus,
            state_machine,
        }
    }
    
    pub async fn start(&self) -> Result<(), ConsensusError> {
        // 订阅日志流
        let mut log_stream = self.consensus.subscribe().await?;
        
        // 启动应用循环
        tokio::spawn({
            let state_machine = self.state_machine.clone();
            
            async move {
                while let Some(entry) = log_stream.next().await {
                    // 应用日志条目到状态机
                    if let Err(e) = state_machine.apply(&entry).await {
                        log::error!("Failed to apply log entry: {}", e);
                    }
                }
            }
        });
        
        Ok(())
    }
    
    pub async fn submit_command(&self, command: Vec<u8>) -> Result<LogIndex, ConsensusError> {
        self.consensus.submit_entry(command).await
    }
    
    pub async fn query<Q, R>(&self, query: Q) -> Result<R, ConsensusError>
    where
        Q: Serialize + Send + Sync,
        R: DeserializeOwned + Send + Sync,
    {
        // 序列化查询
        let query_bytes = serde_json::to_vec(&query)
            .map_err(|e| ConsensusError::SerializationError(e.to_string()))?;
            
        // 执行只读查询
        let result_bytes = self.state_machine.query(&query_bytes).await
            .map_err(|e| ConsensusError::StateMachineError(e.to_string()))?;
            
        // 反序列化结果
        serde_json::from_slice(&result_bytes)
            .map_err(|e| ConsensusError::DeserializationError(e.to_string()))
    }
    
    pub async fn get_leader(&self) -> Result<NodeId, ConsensusError> {
        self.consensus.get_leader().await
    }
}

// 状态机接口
#[async_trait]
pub trait StateMachine: Send + Sync {
    async fn apply(&self, entry: &LogEntry) -> Result<(), StateMachineError>;
    async fn query(&self, query: &[u8]) -> Result<Vec<u8>, StateMachineError>;
    async fn snapshot(&self) -> Result<Vec<u8>, StateMachineError>;
    async fn restore(&self, snapshot: &[u8]) -> Result<(), StateMachineError>;
}
```

#### 状态同步

```rust
// 分布式状态管理器
pub struct DistributedStateManager {
    consensus: Arc<dyn ConsensusProtocol>,
    local_store: Arc<dyn StateStore>,
    cache: Arc<Cache>,
    serializer: Arc<dyn StateSerializer>,
    metrics: Arc<StateMetrics>,
}

// 状态商店接口
#[async_trait]
pub trait StateStore: Send + Sync {
    async fn get<T: DeserializeOwned>(&self, key: &str) -> Result<Option<T>, StateError>;
    async fn put<T: Serialize>(&self, key: &str, value: &T) -> Result<(), StateError>;
    async fn delete(&self, key: &str) -> Result<(), StateError>;
    async fn list_keys(&self, prefix: &str) -> Result<Vec<String>, StateError>;
}

// 状态序列化器接口
pub trait StateSerializer: Send + Sync {
    fn serialize<T: Serialize>(&self, value: &T) -> Result<Vec<u8>, StateError>;
    fn deserialize<T: DeserializeOwned>(&self, data: &[u8]) -> Result<T, StateError>;
}

// 缓存实现
pub struct Cache {
    inner: Mutex<lru::LruCache<String, Arc<Vec<u8>>>>,
    ttl_map: Mutex<HashMap<String, Instant>>,
    default_ttl: Duration,
}

impl Cache {
    pub fn new(capacity: usize, default_ttl: Duration) -> Self {
        Self {
            inner: Mutex::new(lru::LruCache::new(capacity)),
            ttl_map: Mutex::new(HashMap::new()),
            default_ttl,
        }
    }
    
    pub fn get(&self, key: &str) -> Option<Arc<Vec<u8>>> {
        let mut cache = self.inner.lock().unwrap();
        let ttl_map = self.ttl_map.lock().unwrap();
        
        // 检查TTL
        if let Some(expiry) = ttl_map.get(key) {
            if expiry.elapsed() > Duration::from_secs(0) {
                // 已过期，移除缓存
                cache.pop(key);
                return None;
            }
        }
        
        cache.get(key).cloned()
    }
    
    pub fn put(&self, key: &str, value: Vec<u8>, ttl: Option<Duration>) {
        let mut cache = self.inner.lock().unwrap();
        let mut ttl_map = self.ttl_map.lock().unwrap();
        
        // 设置过期时间
        let expiry = Instant::now() + ttl.unwrap_or(self.default_ttl);
        ttl_map.insert(key.to_string(), expiry);
        
        // 存储值
        cache.put(key.to_string(), Arc::new(value));
    }
    
    pub fn invalidate(&self, key: &str) {
        let mut cache = self.inner.lock().unwrap();
        let mut ttl_map = self.ttl_map.lock().unwrap();
        
        cache.pop(key);
        ttl_map.remove(key);
    }
    
    pub fn invalidate_prefix(&self, prefix: &str) {
        let mut cache = self.inner.lock().unwrap();
        let mut ttl_map = self.ttl_map.lock().unwrap();
        
        // 查找并移除所有匹配前缀的键
        let keys_to_remove: Vec<String> = cache.iter()
            .filter_map(|(k, _)| if k.starts_with(prefix) { Some(k.clone()) } else { None })
            .collect();
            
        for key in &keys_to_remove {
            cache.pop(key);
            ttl_map.remove(key);
        }
    }
}

impl DistributedStateManager {
    pub fn new(
        consensus: Arc<dyn ConsensusProtocol>,
        local_store: Arc<dyn StateStore>,
        cache_capacity: usize,
        default_ttl: Duration,
    ) -> Self {
        Self {
            consensus,
            local_store,
            cache: Arc::new(Cache::new(cache_capacity, default_ttl)),
            serializer: Arc::new(JsonSerializer),
            metrics: Arc::new(StateMetrics::new()),
        }
    }
    
    pub async fn set<T: Serialize + Send + Sync>(
        &self,
        key: &str,
        value: T,
        options: StateOptions,
    ) -> Result<(), StateError> {
        let start = Instant::now();
        
        // 序列化值
        let serialized = self.serializer.serialize(&value)?;
        
        // 构建状态更新命令
        let command = StateCommand::Set {
            key: key.to_string(),
            value: serialized.clone(),
            ttl: options.ttl,
        };
        
        // 提交到共识模块
        let command_bytes = self.serializer.serialize(&command)?;
        
        match self.consensus.submit_entry(command_bytes).await {
            Ok(_) => {
                // 更新本地存储
                if options.local_cache {
                    // 更新缓存
                    self.cache.put(key, serialized, options.ttl);
                }
                
                // 如果配置了本地存储
                if options.local_store {
                    match self.local_store.put(key, &value).await {
                        Ok(_) => {},
                        Err(e) => {
                            log::warn!("Failed to update local store for key {}: {}", key, e);
                        }
                    }
                }
                
                self.metrics.record_set_success(start.elapsed());
                Ok(())
            },
            Err(e) => {
                self.metrics.record_set_failure();
                Err(StateError::ConsensusError(e.to_string()))
            }
        }
    }
    
    pub async fn get<T: DeserializeOwned + Send + Sync>(
        &self,
        key: &str,
        options: StateOptions,
    ) -> Result<Option<T>, StateError> {
        let start = Instant::now();
        
        // 首先检查缓存
        if options.local_cache {
            if let Some(cached) = self.cache.get(key) {
                match self.serializer.deserialize::<T>(&cached) {
                    Ok(value) => {
                        self.metrics.record_cache_hit();
                        self.metrics.record_get_success(start.elapsed());
                        return Ok(Some(value));
                    }
                    Err(e) => {
                        log::warn!("Failed to deserialize cached value for key {}: {}", key, e);
                        // 继续尝试其他获取方式
                    }
                }
            }
        }
        
        // 检查本地存储
        if options.local_store {
            match self.local_store.get::<T>(key).await {
                Ok(Some(value)) => {
                    // 更新缓存
                    if options.local_cache {
                        match self.serializer.serialize(&value) {
                            Ok(serialized) => {
                                self.cache.put(key, serialized, options.ttl);
                            }
                            Err(e) => {
                                log::warn!("Failed to serialize value for caching: {}", e);
                            }
                        }
                    }
                    
                    self.metrics.record_local_hit();
                    self.metrics.record_get_success(start.elapsed());
                    return Ok(Some(value));
                }
                Ok(None) => {
                    // 键不存在
                    self.metrics.record_get_miss();
                    self.metrics.record_get_success(start.elapsed());
                    return Ok(None);
                }
                Err(e) => {
                    log::warn!("Failed to get from local store for key {}: {}", key, e);
                    // 继续尝试从共识模块获取
                }
            }
        }
        
        // 从共识模块查询
        let query = StateQuery::Get { key: key.to_string() };
        let query_bytes = self.serializer.serialize(&query)?;
        
        match self.consensus.query::<Vec<u8>, Option<Vec<u8>>>(query_bytes).await {
            Ok(Some(data)) => {
                // 反序列化值
                let value = self.serializer.deserialize::<T>(&data)?;
                
                // 更新缓存
                if options.local_cache {
                    self.cache.put(key, data, options.ttl);
                }
                
                // 更新本地存储
                if options.local_store {
                    match self.local_store.put(key, &value).await {
                        Ok(_) => {},
                        Err(e) => {
                            log::warn!("Failed to update local store for key {}: {}", key, e);
                        }
                    }
                }
                
                self.metrics.record_consensus_hit();
                self.metrics.record_get_success(start.elapsed());
                Ok(Some(value))
            }
            Ok(None) => {
                self.metrics.record_get_miss();
                self.metrics.record_get_success(start.elapsed());
                Ok(None)
            }
            Err(e) => {
                self.metrics.record_get_failure();
                Err(StateError::ConsensusError(e.to_string()))
            }
        }
    }
    
    pub async fn delete(
        &self,
        key: &str,
        options: StateOptions,
    ) -> Result<(), StateError> {
        let start = Instant::now();
        
        // 构建删除命令
        let command = StateCommand::Delete {
            key: key.to_string(),
        };
        
        // 提交到共识模块
        let command_bytes = self.serializer.serialize(&command)?;
        
        match self.consensus.submit_entry(command_bytes).await {
            Ok(_) => {
                // 清除缓存
                if options.local_cache {
                    self.cache.invalidate(key);
                }
                
                // 从本地存储删除
                if options.local_store {
                    match self.local_store.delete(key).await {
                        Ok(_) => {},
                        Err(e) => {
                            log::warn!("Failed to delete from local store for key {}: {}", key, e);
                        }
                    }
                }
                
                self.metrics.record_delete_success(start.elapsed());
                Ok(())
            },
            Err(e) => {
                self.metrics.record_delete_failure();
                Err(StateError::ConsensusError(e.to_string()))
            }
        }
    }
    
    pub async fn list_keys(
        &self,
        prefix: &str,
    ) -> Result<Vec<String>, StateError> {
        // 从共识模块查询键列表
        let query = StateQuery::ListKeys { prefix: prefix.to_string() };
        let query_bytes = self.serializer.serialize(&query)?;
        
        match self.consensus.query::<Vec<u8>, Vec<String>>(query_bytes).await {
            Ok(keys) => Ok(keys),
            Err(e) => Err(StateError::ConsensusError(e.to_string())),
        }
    }
    
    pub async fn watch(
        &self,
        key_prefix: &str,
    ) -> Result<StateChangeStream, StateError> {
        // 创建状态变更流
        let (tx, rx) = mpsc::channel(100);
        
        // 订阅共识日志
        let mut log_stream = self.consensus.subscribe().await
            .map_err(|e| StateError::ConsensusError(e.to_string()))?;
            
        // 启动监视循环
        let prefix = key_prefix.to_string();
        let serializer = self.serializer.clone();
        
        tokio::spawn(async move {
            while let Some(entry) = log_stream.next().await {
                // 尝试反序列化为状态命令
                match serializer.deserialize::<StateCommand>(&entry.data) {
                    Ok(command) => {
                        match command {
                            StateCommand::Set { key, value, .. } => {
                                if key.starts_with(&prefix) {
                                    let event = StateChangeEvent {
                                        key,
                                        event_type: StateChangeType::Set,
                                        value: Some(value),
                                        timestamp: entry.timestamp,
                                    };
                                    
                                    if tx.send(event).await.is_err() {
                                        break; // 接收者已断开连接
                                    }
                                }
                            },
                            StateCommand::Delete { key } => {
                                if key.starts_with(&prefix) {
                                    let event = StateChangeEvent {
                                        key,
                                        event_type: StateChangeType::Delete,
                                        value: None,
                                        timestamp: entry.timestamp,
                                    };
                                    
                                    if tx.send(event).await.is_err() {
                                        break; // 接收者已断开连接
                                    }
                                }
                            },
                        }
                    },
                    Err(_) => {
                        // 不是状态命令，忽略
                    }
                }
            }
        });
        
        Ok(StateChangeStream { receiver: rx })
    }
}

// 状态选项
#[derive(Debug, Clone)]
pub struct StateOptions {
    pub ttl: Option<Duration>,
    pub local_cache: bool,
    pub local_store: bool,
}

impl Default for StateOptions {
    fn default() -> Self {
        Self {
            ttl: None,
            local_cache: true,
            local_store: true,
        }
    }
}

// 状态命令
#[derive(Debug, Clone, Serialize, Deserialize)]
enum StateCommand {
    Set {
        key: String,
        value: Vec<u8>,
        ttl: Option<Duration>,
    },
    Delete {
        key: String,
    },
}

// 状态查询
#[derive(Debug, Clone, Serialize, Deserialize)]
enum StateQuery {
    Get { key: String },
    ListKeys { prefix: String },
}

// 状态变更流
pub struct StateChangeStream {
    receiver: mpsc::Receiver<StateChangeEvent>,
}

impl StateChangeStream {
    pub async fn next(&mut self) -> Option<StateChangeEvent> {
        self.receiver.recv().await
    }
}

// 状态变更事件
#[derive(Debug, Clone)]
pub struct StateChangeEvent {
    pub key: String,
    pub event_type: StateChangeType,
    pub value: Option<Vec<u8>>,
    pub timestamp: DateTime<Utc>,
}

// 状态变更类型
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StateChangeType {
    Set,
    Delete,
}

// JSON序列化器实现
pub struct JsonSerializer;

impl StateSerializer for JsonSerializer {
    fn serialize<T: Serialize>(&self, value: &T) -> Result<Vec<u8>, StateError> {
        serde_json::to_vec(value).map_err(|e| StateError::SerializationError(e.to_string()))
    }
    
    fn deserialize<T: DeserializeOwned>(&self, data: &[u8]) -> Result<T, StateError> {
        serde_json::from_slice(data).map_err(|e| StateError::DeserializationError(e.to_string()))
    }
}
```

#### 分区策略

```rust
// 分区管理器
pub struct PartitionManager {
    node_id: NodeId,
    cluster: Arc<ClusterManager>,
    partition_assignments: RwLock<HashMap<String, PartitionAssignment>>,
    partition_strategies: HashMap<String, Box<dyn PartitionStrategy>>,
    partition_states: Arc<RwLock<HashMap<PartitionId, PartitionState>>>,
    rebalance_lock: Mutex<()>,
    metrics: Arc<PartitionMetrics>,
}

// 分区ID类型
pub type PartitionId = String;

// 分区分配信息
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PartitionAssignment {
    pub partition_id: PartitionId,
    pub owner_node: NodeId,
    pub replica_nodes: Vec<NodeId>,
    pub version: u64,
    pub last_updated: DateTime<Utc>,
}

// 分区状态
#[derive(Clone, Debug, PartialEq)]
pub enum PartitionState {
    Inactive,
    Loading,
    Active,
    Transferring { target_node: NodeId },
    ReadOnly,
}

// 分区策略特征
pub trait PartitionStrategy: Send + Sync {
    fn name(&self) -> &str;
    
    fn assign_partitions(
        &self,
        partitions: &[PartitionId],
        nodes: &[NodeId],
        current_assignments: &HashMap<PartitionId, PartitionAssignment>,
    ) -> HashMap<PartitionId, PartitionAssignment>;
}

// 一致性哈希分区策略
pub struct ConsistentHashStrategy {
    virtual_nodes: usize,
    hash_ring: RwLock<Option<HashRing>>,
}

struct HashRing {
    ring: BTreeMap<u64, NodeId>,
    node_points: HashMap<NodeId, Vec<u64>>,
}

impl ConsistentHashStrategy {
    pub fn new(virtual_nodes: usize) -> Self {
        Self {
            virtual_nodes,
            hash_ring: RwLock::new(None),
        }
    }
    
    fn build_ring(&self, nodes: &[NodeId]) -> HashRing {
        let mut ring = BTreeMap::new();
        let mut node_points = HashMap::new();
        
        for node in nodes {
            let points = self.generate_points(node);
            
            for &point in &points {
                ring.insert(point, node.clone());
            }
            
            node_points.insert(node.clone(), points);
        }
        
        HashRing { ring, node_points }
    }
    
    fn generate_points(&self, node: &str) -> Vec<u64> {
        let mut points = Vec::with_capacity(self.virtual_nodes);
        
        for i in 0..self.virtual_nodes {
            let key = format!("{}:{}", node, i);
            let point = self.hash(&key);
            points.push(point);
        }
        
        points
    }
    
    fn hash(&self, key: &str) -> u64 {
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        hasher.finish()
    }
    
    fn get_node(&self, partition: &str) -> Option<NodeId> {
        let ring_guard = self.hash_ring.read().unwrap();
        let ring = ring_guard.as_ref()?;
        
        let hash = self.hash(partition);
        
        // 找到大于等于哈希值的第一个点
        if let Some((&point, node)) = ring.ring.range(hash..).next() {
            return Some(node.clone());
        }
        
        // 如果没有找到，返回环的第一个点
        if let Some((&point, node)) = ring.ring.iter().next() {
            return Some(node.clone());
        }
        
        None
    }
}

impl PartitionStrategy for ConsistentHashStrategy {
    fn name(&self) -> &str {
        "consistent-hash"
    }
    
    fn assign_partitions(
        &self,
        partitions: &[PartitionId],
        nodes: &[NodeId],
        current_assignments: &HashMap<PartitionId, PartitionAssignment>,
    ) -> HashMap<PartitionId, PartitionAssignment> {
        if nodes.is_empty() {
            return HashMap::new();
        }
        
        // 构建一致性哈希环
        let ring = self.build_ring(nodes);
        *self.hash_ring.write().unwrap() = Some(ring);
        
        let mut assignments = HashMap::new();
        
        for partition in partitions {
            let owner = match self.get_node(partition) {
                Some(node) => node,
                None => continue, // 不应该发生，但为了安全
            };
            
            // 为每个分区分配副本
            let mut replicas = Vec::new();
            let mut remaining_nodes: Vec<_> = nodes.iter()
                .filter(|&node| node != &owner)
                .cloned()
                .collect();
                
            // 从剩余节点中随机选择副本
            let replica_count = std::cmp::min(2, remaining_nodes.len());
            remaining_nodes.shuffle(&mut rand::thread_rng());
            
            for i in 0..replica_count {
                replicas.push(remaining_nodes[i].clone());
            }
            
            // 创建分区分配
            let assignment = if let Some(current) = current_assignments.get(partition) {
                // 保留版本信息
                PartitionAssignment {
                    partition_id: partition.clone(),
                    owner_node: owner,
                    replica_nodes: replicas,
                    version: current.version + 1,
                    last_updated: Utc::now(),
                }
            } else {
                PartitionAssignment {
                    partition_id: partition.clone(),
                    owner_node: owner,
                    replica_nodes: replicas,
                    version: 1,
                    last_updated: Utc::now(),
                }
            };
            
            assignments.insert(partition.clone(), assignment);
        }
        
        assignments
    }
}

// 均衡分区策略
pub struct BalancedPartitionStrategy;

impl PartitionStrategy for BalancedPartitionStrategy {
    fn name(&self) -> &str {
        "balanced"
    }
    
    fn assign_partitions(
        &self,
        partitions: &[PartitionId],
        nodes: &[NodeId],
        current_assignments: &HashMap<PartitionId, PartitionAssignment>,
    ) -> HashMap<PartitionId, PartitionAssignment> {
        if nodes.is_empty() {
            return HashMap::new();
        }
        
        // 计算每个节点应该分配的分区数
        let partition_count = partitions.len();
        let node_count = nodes.len();
        let base_per_node = partition_count / node_count;
        let mut extra = partition_count % node_count;
        
        // 初始化节点的分区计数
        let mut node_partition_counts = HashMap::new();
        for node in nodes {
            node_partition_counts.insert(node.clone(), 0);
        }
        
        // 统计当前分配情况
        for assignment in current_assignments.values() {
            if let Some(count) = node_partition_counts.get_mut(&assignment.owner_node) {
                *count += 1;
            }
        }
        
        // 按照当前分区数排序节点
        let mut sorted_nodes: Vec<_> = nodes.to_vec();
        sorted_nodes.sort_by_key(|node| node_partition_counts.get(node).unwrap_or(&0));
        
        // 计算目标分配
        let mut target_counts = HashMap::new();
        for (i, node) in sorted_nodes.iter().enumerate() {
            let target = base_per_node + if i < extra { 1 } else { 0 };
            target_counts.insert(node.clone(), target);
        }
        
        // 收集需要重新分配的分区
        let mut to_assign = Vec::new();
        let mut assigned = HashMap::new();
        
        // 首先尝试保留当前分配的分区
        for partition in partitions {
            if let Some(current) = current_assignments.get(partition) {
                let owner = &current.owner_node;
                
                if nodes.contains(owner) {
                    // 检查该节点是否已经超出其目标分配数
                    let current_count = *node_partition_counts.get(owner).unwrap_or(&0);
                    let target = *target_counts.get(owner).unwrap_or(&0);
                    
                    if current_count <= target {
                        // 继续将此分区分配给当前所有者
                        let mut replicas = Vec::new();
                        let mut remaining_nodes: Vec<_> = nodes.iter()
                            .filter(|&node| node != owner)
                            .cloned()
                            .collect();
                            
                        // 从剩余节点中随机选择副本
                        let replica_count = std::cmp::min(2, remaining_nodes.len());
                        remaining_nodes.shuffle(&mut rand::thread_rng());
                        
                        for i in 0..replica_count {
                            replicas.push(remaining_nodes[i].clone());
                        }
                        
                        let assignment = PartitionAssignment {
                            partition_id: partition.clone(),
                            owner_node: owner.clone(),
                            replica_nodes: replicas,
                            version: current.version + 1,
                            last_updated: Utc::now(),
                        };
                        
                        assigned.insert(partition.clone(), assignment);
                        
                        // 更新计数
                        if let Some(count) = node_partition_counts.get_mut(owner) {
                            *count += 1;
                        }
                        
                        continue;
                    }
                }
            }
            
            // 需要重新分配的分区
            to_assign.push(partition.clone());
        }
        
        // 重新分配剩余分区
        for partition in to_assign {
            // 选择分区数量最少的节点
            sorted_nodes.sort_by_key(|node| node_partition_counts.get(node).unwrap_or(&0));
            let owner = &sorted_nodes[0];
            
            // 为分区分配副本
            let mut replicas = Vec::new();
            let mut remaining_nodes: Vec<_> = nodes.iter()
                .filter(|&node| node != owner)
                .cloned()
                .collect();
                
            // 从剩余节点中随机选择副本
            let replica_count = std::cmp::min(2, remaining_nodes.len());
            remaining_nodes.shuffle(&mut rand::thread_rng());
            
            for i in 0..replica_count {
                replicas.push(remaining_nodes[i].clone());
            }
            
            // 创建分区分配
            let assignment = if let Some(current) = current_assignments.get(&partition) {
                // 保留版本信息
                PartitionAssignment {
                    partition_id: partition.clone(),
                    owner_node: owner.clone(),
                    replica_nodes: replicas,
                    version: current.version + 1,
                    last_updated: Utc::now(),
                }
            } else {
                PartitionAssignment {
                    partition_id: partition.clone(),
                    owner_node: owner.clone(),
                    replica_nodes: replicas,
                    version: 1,
                    last_updated: Utc::now(),
                }
            };
            
            assigned.insert(partition.clone(), assignment);
            
            // 更新计数
            if let Some(count) = node_partition_counts.get_mut(owner) {
                *count += 1;
            }
        }
        
        assigned
    }
}

impl PartitionManager {
    pub fn new(
        node_id: NodeId,
        cluster: Arc<ClusterManager>,
    ) -> Self {
        let mut strategies = HashMap::new();
        strategies.insert(
            "consistent-hash".to_string(),
            Box::new(ConsistentHashStrategy::new(10)) as Box<dyn PartitionStrategy>,
        );
        strategies.insert(
            "balanced".to_string(),
            Box::new(BalancedPartitionStrategy) as Box<dyn PartitionStrategy>,
        );
        
        Self {
            node_id,
            cluster,
            partition_assignments: RwLock::new(HashMap::new()),
            partition_strategies: strategies,
            partition_states: Arc::new(RwLock::new(HashMap::new())),
            rebalance_lock: Mutex::new(()),
            metrics: Arc::new(PartitionMetrics::new()),
        }
    }
    
    pub async fn start(&self) -> Result<(), PartitionError> {
        // 加载当前分区分配
        self.load_assignments().await?;
        
        // 初始化分区状态
        let assignments = self.partition_assignments.read().unwrap();
        let mut states = self.partition_states.write().unwrap();
        
        for (partition_id, assignment) in assignments.iter() {
            if assignment.owner_node == self.node_id {
                states.insert(partition_id.clone(), PartitionState::Loading);
            }
        }
        
        // 启动分区监视器
        self.start_partition_monitor();
        
        // 启动重平衡任务
        self.start_rebalance_task();
        
        Ok(())
    }
    
    async fn load_assignments(&self) -> Result<(), PartitionError> {
        // 从分布式状态存储加载分区分配
        // 这里假设有一个共识服务可用于查询
        // 实际实现可能需要根据具体存储机制调整
        
        // 模拟从状态存储中加载
        let mut assignments = HashMap::new();
        
        // 在实际实现中，这里应该从分布式存储中读取
        
        *self.partition_assignments.write().unwrap() = assignments;
        
        Ok(())
    }
    
    fn start_partition_monitor(&self) {
        let partition_states = self.partition_states.clone();
        let assignments = self.partition_assignments.clone();
        let node_id = self.node_id.clone();
        let metrics = self.metrics.clone();
        
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_secs(5));
            
            loop {
                interval.tick().await;
                
                // 监控分区状态
                let assignments_guard = assignments.read().unwrap();
                let states_guard = partition_states.read().unwrap();
                
                let owned_partitions: Vec<_> = assignments_guard.values()
                    .filter(|a| a.owner_node == node_id)
                    .map(|a| a.partition_id.clone())
                    .collect();
                    
                let active_count = states_guard.iter()
                    .filter(|(_, &ref state)| state == &PartitionState::Active)
                    .count();
                    
                let loading_count = states_guard.iter()
                    .filter(|(_, &ref state)| state == &PartitionState::Loading)
                    .count();
                    
                let transferring_count = states_guard.iter()
                    .filter(|(_, &ref state)| 
                        matches!(state, PartitionState::Transferring { .. })
                    )
                    .count();
                    
                // 更新指标
                metrics.record_owned_partitions(owned_partitions.len());
                metrics.record_active_partitions(active_count);
                metrics.record_loading_partitions(loading_count);
                metrics.record_transferring_partitions(transferring_count);
                
                // 检查是否有需要处理的事件，例如：
                // - 从Loading状态转换到Active状态
                // - 处理传输完成的分区
                // 实际实现可能需要根据具体业务逻辑调整
            }
        });
    }
    
    fn start_rebalance_task(&self) {
        let self_clone = Arc::new(self.clone());
        
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_secs(60));
            
            loop {
                interval.tick().await;
                
                // 尝试进行分区重平衡
                if let Err(e) = self_clone.rebalance_partitions().await {
                    log::warn!("Partition rebalance failed: {}", e);
                }
            }
        });
    }
    
    pub async fn rebalance_partitions(&self) -> Result<(), PartitionError> {
        // 获取重平衡锁，确保同一时间只有一个重平衡过程
        let _guard = match self.rebalance_lock.try_lock() {
            Ok(guard) => guard,
            Err(_) => {
                // 已经有重平衡任务在运行
                return Ok(());
            }
        };
        
        log::info!("Starting partition rebalance");
        
        // 获取集群节点列表
        let nodes = self.cluster.get_active_nodes().await?;
        
        if nodes.is_empty() {
            return Err(PartitionError::NoActiveNodes);
        }
        
        // 获取所有分区
        let partitions = self.list_all_partitions().await?;
        
        // 获取当前分配
        let current_assignments = self.partition_assignments.read().unwrap().clone();
        
        // 使用默认策略进行重新分配
        let strategy = self.partition_strategies.get("balanced")
            .ok_or(PartitionError::StrategyNotFound)?;
            
        let new_assignments = strategy.assign_partitions(
            &partitions,
            &nodes,
            &current_assignments,
        );
        
        // 应用新的分配
        self.apply_new_assignments(new_assignments).await?;
        
        log::info!("Partition rebalance completed");
        
        Ok(())
    }
    
    async fn list_all_partitions(&self) -> Result<Vec<PartitionId>, PartitionError> {
        // 在实际实现中，这里应该从服务注册表或配置中获取所有分区
        // 为了简化示例，这里返回一个模拟的分区列表
        
        Ok(vec![
            "partition-1".to_string(),
            "partition-2".to_string(),
            "partition-3".to_string(),
            // 更多分区...
        ])
    }
    
    async fn apply_new_assignments(
        &self,
        new_assignments: HashMap<PartitionId, PartitionAssignment>,
    ) -> Result<(), PartitionError> {
        // 获取当前分配
        let current = self.partition_assignments.read().unwrap().clone();
        
        // 找出发生变化的分配
        let mut changes = Vec::new();
        
        for (partition_id, new_assignment) in &new_assignments {
            match current.get(partition_id) {
                Some(current_assignment) => {
                    if current_assignment.owner_node != new_assignment.owner_node {
                        // 所有权变更
                        changes.push((
                            partition_id.clone(),
                            Some(current_assignment.clone()),
                            new_assignment.clone(),
                        ));
                    }
                }
                None => {
                    // 新分配
                    changes.push((
                        partition_id.clone(),
                        None,
                        new_assignment.clone(),
                    ));
                }
            }
        }
        
        // 处理每个变更
        for (partition_id, old, new) in changes {
            // 保存新的分配到分布式存储
            self.save_assignment(&new).await?;
            
            // 如果旧的所有者是当前节点，更新状态为Transferring
            if let Some(old_assignment) = old {
                if old_assignment.owner_node == self.node_id {
                    let mut states = self.partition_states.write().unwrap();
                    states.insert(
                        partition_id.clone(),
                        PartitionState::Transferring { target_node: new.owner_node.clone() },
                    );
                    
                    // 启动传输过程
                    self.start_partition_transfer(&partition_id, &new.owner_node).await?;
                }
            }
            
            // 如果新的所有者是当前节点，更新状态为Loading
            if new.owner_node == self.node_id {
                let mut states = self.partition_states.write().unwrap();
                states.insert(
                    partition_id.clone(),
                    PartitionState::Loading,
                );
                
                // 开始加载分区
                self.start_partition_loading(&partition_id).await?;
            }
        }
        
        // 更新本地分配缓存
        *self.partition_assignments.write().unwrap() = new_assignments;
        
        Ok(())
    }
    
    async fn save_assignment(
        &self,
        assignment: &PartitionAssignment,
    ) -> Result<(), PartitionError> {
        // 保存分配到分布式存储
        // 在实际实现中，这通常会涉及到共识协议或分布式KV存储
        
        // 模拟保存操作
        log::info!("Saving assignment for partition {}: owner={}",
            assignment.partition_id, assignment.owner_node);
            
        Ok(())
    }
    
    async fn start_partition_transfer(
        &self,
        partition_id: &str,
        target_node: &str,
    ) -> Result<(), PartitionError> {
        // 开始将分区数据传输到目标节点
        // 在实际实现中，这可能涉及到发送快照或增量更新
        
        log::info!("Starting transfer of partition {} to node {}", partition_id, target_node);
        
        // 模拟传输过程
        let partition_id = partition_id.to_string();
        let target_node = target_node.to_string();
        let states = self.partition_states.clone();
        
        tokio::spawn(async move {
            // 模拟传输延迟
            tokio::time::sleep(Duration::from_secs(5)).await;
            
            // 传输完成，更新状态
            let mut states = states.write().unwrap();
            states.insert(partition_id.clone(), PartitionState::Inactive);
            
            log::info!("Completed transfer of partition {} to node {}", partition_id, target_node);
        });
        
        Ok(())
    }
    
    async fn start_partition_loading(
        &self,
        partition_id: &str,
    ) -> Result<(), PartitionError> {
        // 开始加载分区数据
        // 在实际实现中，这可能涉及到从其他节点获取快照或回放日志
        
        log::info!("Starting loading of partition {}", partition_id);
        
        // 模拟加载过程
        let partition_id = partition_id.to_string();
        let states = self.partition_states.clone();
        
        tokio::spawn(async move {
            // 模拟加载延迟
            tokio::time::sleep(Duration::from_secs(3)).await;
            
            // 加载完成，更新状态
            let mut states = states.write().unwrap();
            states.insert(partition_id.clone(), PartitionState::Active);
            
            log::info!("Completed loading of partition {}", partition_id);
        });
        
        Ok(())
    }
    
    pub async fn get_partition_owner(
        &self,
        partition_id: &str,
    ) -> Result<NodeId, PartitionError> {
        let assignments = self.partition_assignments.read().unwrap();
        
        match assignments.get(partition_id) {
            Some(assignment) => Ok(assignment.owner_node.clone()),
            None => Err(PartitionError::PartitionNotFound),
        }
    }
    
    pub async fn get_partition_state(
        &self,
        partition_id: &str,
    ) -> Result<PartitionState, PartitionError> {
        let states = self.partition_states.read().unwrap();
        
        match states.get(partition_id) {
            Some(state) => Ok(state.clone()),
            None => Err(PartitionError::PartitionNotFound),
        }
    }
    
    pub async fn is_partition_owner(
        &self,
        partition_id: &str,
    ) -> Result<bool, PartitionError> {
        let owner = self.get_partition_owner(partition_id).await?;
        Ok(owner == self.node_id)
    }
}

// 分区错误
#[derive(Debug, thiserror::Error)]
pub enum PartitionError {
    #[error("Partition not found")]
    PartitionNotFound,
    
    #[error("No active nodes in cluster")]
    NoActiveNodes,
    
    #[error("Partition strategy not found")]
    StrategyNotFound,
    
    #[error("Cluster error: {0}")]
    ClusterError(String),
    
    #[error("Storage error: {0}")]
    StorageError(String),
    
    #[error("Other partition error: {0}")]
    Other(String),
}

// 分区指标
pub struct PartitionMetrics {
    owned_partitions: AtomicUsize,
    active_partitions: AtomicUsize,
    loading_partitions: AtomicUsize,
    transferring_partitions: AtomicUsize,
    rebalance_count: AtomicUsize,
    partition_transfer_duration: Histogram,
    partition_load_duration: Histogram,
}

impl PartitionMetrics {
    pub fn new() -> Self {
        Self {
            owned_partitions: AtomicUsize::new(0),
            active_partitions: AtomicUsize::new(0),
            loading_partitions: AtomicUsize::new(0),
            transferring_partitions: AtomicUsize::new(0),
            rebalance_count: AtomicUsize::new(0),
            partition_transfer_duration: Histogram::new(),
            partition_load_duration: Histogram::new(),
        }
    }
    
    pub fn record_owned_partitions(&self, count: usize) {
        self.owned_partitions.store(count, Ordering::Relaxed);
    }
    
    pub fn record_active_partitions(&self, count: usize) {
        self.active_partitions.store(count, Ordering::Relaxed);
    }
    
    pub fn record_loading_partitions(&self, count: usize) {
        self.loading_partitions.store(count, Ordering::Relaxed);
    }
    
    pub fn record_transferring_partitions(&self, count: usize) {
        self.transferring_partitions.store(count, Ordering::Relaxed);
    }
    
    pub fn record_rebalance(&self) {
        self.rebalance_count.fetch_add(1, Ordering::Relaxed);
    }
    
    pub fn record_transfer_duration(&self, duration: Duration) {
        self.partition_transfer_duration.record(duration.as_millis() as u64);
    }
    
    pub fn record_load_duration(&self, duration: Duration) {
        self.partition_load_duration.record(duration.as_millis() as u64);
    }
}

// 简单的直方图实现
#[derive(Debug)]
pub struct Histogram {
    counts: Mutex<BTreeMap<u64, u64>>,
    count: AtomicU64,
    sum: AtomicU64,
}

impl Histogram {
    pub fn new() -> Self {
        Self {
            counts: Mutex::new(BTreeMap::new()),
            count: AtomicU64::new(0),
            sum: AtomicU64::new(0),
        }
    }
    
    pub fn record(&self, value: u64) {
        let mut counts = self.counts.lock().unwrap();
        *counts.entry(value).or_insert(0) += 1;
        
        self.count.fetch_add(1, Ordering::Relaxed);
        self.sum.fetch_add(value, Ordering::Relaxed);
    }
    
    pub fn count(&self) -> u64 {
        self.count.load(Ordering::Relaxed)
    }
    
    pub fn sum(&self) -> u64 {
        self.sum.load(Ordering::Relaxed)
    }
    
    pub fn mean(&self) -> Option<f64> {
        let count = self.count();
        if count == 0 {
            return None;
        }
        
        let sum = self.sum();
        Some(sum as f64 / count as f64)
    }
    
    pub fn percentile(&self, p: f64) -> Option<u64> {
        assert!(p >= 0.0 && p <= 1.0);
        
        let count = self.count();
        if count == 0 {
            return None;
        }
        
        let target_rank = (p * (count as f64)).round() as u64;
        let mut current_rank = 0;
        
        let counts = self.counts.lock().unwrap();
        
        for (&value, &value_count) in counts.iter() {
            current_rank += value_count;
            if current_rank >= target_rank {
                return Some(value);
            }
        }
        
        // 如果我们到达这里，返回最大值
        counts.keys().next_back().copied()
    }
}

// 集群管理器
pub struct ClusterManager {
    node_id: NodeId,
    nodes: RwLock<HashMap<NodeId, NodeInfo>>,
    heartbeat_interval: Duration,
    node_timeout: Duration,
    transport: Arc<dyn RpcTransport>,
    metrics: Arc<ClusterMetrics>,
}

// 节点信息
#[derive(Clone, Debug)]
pub struct NodeInfo {
    pub node_id: NodeId,
    pub address: String,
    pub status: NodeStatus,
    pub tags: HashMap<String, String>,
    pub last_heartbeat: DateTime<Utc>,
}

// 节点状态
#[derive(Clone, Debug, PartialEq)]
pub enum NodeStatus {
    Unknown,
    Joining,
    Active,
    Leaving,
    Down,
}

impl ClusterManager {
    pub fn new(
        node_id: NodeId,
        transport: Arc<dyn RpcTransport>,
        heartbeat_interval: Duration,
        node_timeout: Duration,
    ) -> Self {
        Self {
            node_id,
            nodes: RwLock::new(HashMap::new()),
            heartbeat_interval,
            node_timeout,
            transport,
            metrics: Arc::new(ClusterMetrics::new()),
        }
    }
    
    pub async fn start(&self, initial_peers: Vec<String>) -> Result<(), ClusterError> {
        // 初始化自身节点信息
        let self_info = NodeInfo {
            node_id: self.node_id.clone(),
            address: "localhost:8080".to_string(), // 在实际实现中，这应该是可配置的
            status: NodeStatus::Joining,
            tags: HashMap::new(),
            last_heartbeat: Utc::now(),
        };
        
        {
            let mut nodes = self.nodes.write().unwrap();
            nodes.insert(self.node_id.clone(), self_info);
        }
        
        // 加入集群
        self.join_cluster(initial_peers).await?;
        
        // 启动心跳发送任务
        self.start_heartbeat_task();
        
        // 启动节点状态监控任务
        self.start_node_monitor_task();
        
        // 更新自身状态为活跃
        {
            let mut nodes = self.nodes.write().unwrap();
            if let Some(info) = nodes.get_mut(&self.node_id) {
                info.status = NodeStatus::Active;
            }
        }
        
        Ok(())
    }
    
    async fn join_cluster(&self, peers: Vec<String>) -> Result<(), ClusterError> {
        if peers.is_empty() {
            log::info!("No initial peers provided, starting new cluster");
            return Ok(());
        }
        
        // 连接到至少一个对等节点
        let mut joined = false;
        
        for peer in &peers {
            match self.join_peer(peer).await {
                Ok(_) => {
                    joined = true;
                    break;
                }
                Err(e) => {
                    log::warn!("Failed to join peer {}: {}", peer, e);
                }
            }
        }
        
        if !joined && !peers.is_empty() {
            return Err(ClusterError::JoinFailed);
        }
        
        log::info!("Successfully joined cluster");
        
        Ok(())
    }
    
    async fn join_peer(&self, peer: &str) -> Result<(), ClusterError> {
        // 发送加入请求
        // 在实际实现中，这将使用RpcTransport发送请求
        
        log::info!("Joining cluster via peer {}", peer);
        
        // 模拟加入请求
        tokio::time::sleep(Duration::from_millis(100)).await;
        
        // 在实际实现中，应该接收并处理对等节点的响应
        // 包括当前的集群成员列表
        
        Ok(())
    }
    
    fn start_heartbeat_task(&self) {
        let heartbeat_interval = self.heartbeat_interval;
        let node_id = self.node_id.clone();
        let transport = self.transport.clone();
        let nodes = self.nodes.clone();
        let metrics = self.metrics.clone();
        
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(heartbeat_interval);
            
            loop {
                interval.tick().await;
                
                // 发送心跳到所有活跃节点
                let node_list = {
                    let nodes_guard = nodes.read().unwrap();
                    nodes_guard.values()
                        .filter(|info| info.status == NodeStatus::Active && info.node_id != node_id)
                        .map(|info| (info.node_id.clone(), info.address.clone()))
                        .collect::<Vec<_>>()
                };
                
                for (peer_id, address) in node_list {
                    // 发送心跳
                    // 在实际实现中，这将使用RpcTransport发送请求
                    
                    // 模拟心跳发送
                    log::debug!("Sending heartbeat to node {}", peer_id);
                    
                    // 更新指标
                    metrics.record_heartbeat_sent();
                }
            }
        });
    }
    
    fn start_node_monitor_task(&self) {
        let node_timeout = self.node_timeout;
        let nodes = self.nodes.clone();
        let metrics = self.metrics.clone();
        
        tokio::spawn(async move {
            let check_interval = node_timeout / 2;
            let mut interval = tokio::time::interval(check_interval);
            
            loop {
                interval.tick().await;
                
                // 检查节点状态
                let now = Utc::now();
                let mut down_nodes = Vec::new();
                
                {
                    let nodes_guard = nodes.read().unwrap();
                    
                    for (node_id, info) in nodes_guard.iter() {
                        if info.status == NodeStatus::Active {
                            let elapsed = now.signed_duration_since(info.last_heartbeat);
                            
                            if elapsed > chrono::Duration::from_std(node_timeout).unwrap() {
                                down_nodes.push(node_id.clone());
                            }
                        }
                    }
                }
                
                // 更新状态
                if !down_nodes.is_empty() {
                    let mut nodes_guard = nodes.write().unwrap();
                    
                    for node_id in down_nodes {
                        if let Some(info) = nodes_guard.get_mut(&node_id) {
                            log::warn!("Node {} is down", node_id);
                            info.status = NodeStatus::Down;
                            metrics.record_node_down();
                        }
                    }
                }
                
                // 更新指标
                let nodes_guard = nodes.read().unwrap();
                
                let active_count = nodes_guard.values()
                    .filter(|info| info.status == NodeStatus::Active)
                    .count();
                    
                let down_count = nodes_guard.values()
                    .filter(|info| info.status == NodeStatus::Down)
                    .count();
                    
                metrics.record_active_nodes(active_count);
                metrics.record_down_nodes(down_count);
            }
        });
    }
    
    pub async fn get_active_nodes(&self) -> Result<Vec<NodeId>, ClusterError> {
        let nodes_guard = self.nodes.read().unwrap();
        
        let active_nodes = nodes_guard.values()
            .filter(|info| info.status == NodeStatus::Active)
            .map(|info| info.node_id.clone())
            .collect();
            
        Ok(active_nodes)
    }
    
    pub async fn get_node_info(&self, node_id: &str) -> Result<NodeInfo, ClusterError> {
        let nodes_
<think>我需要继续上次被截断的内容，具体是完成 ClusterManager 的 get_node_info 方法实现和随后的代码。看起来是分布式系统的集群管理部分，我会继续写这部分的实现，并可能进入新的主题。根据前面的代码，这是一个用 Rust 实现的分布式系统框架，包含了分区管理、集群管理等基础设施。</think>```rust
    pub async fn get_node_info(&self, node_id: &str) -> Result<NodeInfo, ClusterError> {
        let nodes_guard = self.nodes.read().unwrap();
        
        match nodes_guard.get(node_id) {
            Some(info) => Ok(info.clone()),
            None => Err(ClusterError::NodeNotFound),
        }
    }
    
    pub async fn handle_heartbeat(&self, from_node: &str) -> Result<(), ClusterError> {
        let mut nodes_guard = self.nodes.write().unwrap();
        
        if let Some(info) = nodes_guard.get_mut(from_node) {
            info.last_heartbeat = Utc::now();
            
            // 如果节点之前被标记为宕机，现在恢复活跃状态
            if info.status == NodeStatus::Down {
                info.status = NodeStatus::Active;
                self.metrics.record_node_up();
                log::info!("Node {} is back online", from_node);
            }
        } else {
            // 未知节点，可能是新加入的
            log::warn!("Received heartbeat from unknown node: {}", from_node);
        }
        
        self.metrics.record_heartbeat_received();
        
        Ok(())
    }
    
    pub async fn leave_cluster(&self) -> Result<(), ClusterError> {
        log::info!("Leaving cluster");
        
        // 更新自身状态为正在离开
        {
            let mut nodes_guard = self.nodes.write().unwrap();
            if let Some(info) = nodes_guard.get_mut(&self.node_id) {
                info.status = NodeStatus::Leaving;
            }
        }
        
        // 通知其他节点
        let node_list = {
            let nodes_guard = self.nodes.read().unwrap();
            nodes_guard.values()
                .filter(|info| info.status == NodeStatus::Active && info.node_id != self.node_id)
                .map(|info| (info.node_id.clone(), info.address.clone()))
                .collect::<Vec<_>>()
        };
        
        for (node_id, address) in node_list {
            // 发送离开通知
            // 在实际实现中，这将使用RpcTransport发送请求
            
            log::debug!("Notifying node {} of departure", node_id);
        }
        
        Ok(())
    }
}

// 集群错误
#[derive(Debug, thiserror::Error)]
pub enum ClusterError {
    #[error("Failed to join cluster")]
    JoinFailed,
    
    #[error("Node not found")]
    NodeNotFound,
    
    #[error("RPC error: {0}")]
    RpcError(String),
    
    #[error("Other cluster error: {0}")]
    Other(String),
}

// 集群指标
pub struct ClusterMetrics {
    active_nodes: AtomicUsize,
    down_nodes: AtomicUsize,
    heartbeats_sent: AtomicU64,
    heartbeats_received: AtomicU64,
    node_up_events: AtomicU64,
    node_down_events: AtomicU64,
}

impl ClusterMetrics {
    pub fn new() -> Self {
        Self {
            active_nodes: AtomicUsize::new(0),
            down_nodes: AtomicUsize::new(0),
            heartbeats_sent: AtomicU64::new(0),
            heartbeats_received: AtomicU64::new(0),
            node_up_events: AtomicU64::new(0),
            node_down_events: AtomicU64::new(0),
        }
    }
    
    pub fn record_active_nodes(&self, count: usize) {
        self.active_nodes.store(count, Ordering::Relaxed);
    }
    
    pub fn record_down_nodes(&self, count: usize) {
        self.down_nodes.store(count, Ordering::Relaxed);
    }
    
    pub fn record_heartbeat_sent(&self) {
        self.heartbeats_sent.fetch_add(1, Ordering::Relaxed);
    }
    
    pub fn record_heartbeat_received(&self) {
        self.heartbeats_received.fetch_add(1, Ordering::Relaxed);
    }
    
    pub fn record_node_up(&self) {
        self.node_up_events.fetch_add(1, Ordering::Relaxed);
    }
    
    pub fn record_node_down(&self) {
        self.node_down_events.fetch_add(1, Ordering::Relaxed);
    }
}

// 服务发现
pub struct ServiceDiscovery {
    cluster: Arc<ClusterManager>,
    services: RwLock<HashMap<String, Vec<ServiceInstance>>>,
    health_check_interval: Duration,
    metrics: Arc<ServiceDiscoveryMetrics>,
}

// 服务实例
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ServiceInstance {
    pub id: String,
    pub service_name: String,
    pub node_id: NodeId,
    pub address: String,
    pub port: u16,
    pub metadata: HashMap<String, String>,
    pub status: ServiceStatus,
    pub health_check: Option<HealthCheck>,
    pub last_check: Option<DateTime<Utc>>,
}

// 服务状态
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ServiceStatus {
    Unknown,
    Starting,
    Healthy,
    Unhealthy,
    Stopping,
}

// 健康检查配置
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct HealthCheck {
    pub endpoint: String,
    pub interval: Duration,
    pub timeout: Duration,
    pub failure_threshold: u32,
    pub success_threshold: u32,
}

impl ServiceDiscovery {
    pub fn new(
        cluster: Arc<ClusterManager>,
        health_check_interval: Duration,
    ) -> Self {
        Self {
            cluster,
            services: RwLock::new(HashMap::new()),
            health_check_interval,
            metrics: Arc::new(ServiceDiscoveryMetrics::new()),
        }
    }
    
    pub async fn start(&self) -> Result<(), ServiceDiscoveryError> {
        // 启动健康检查任务
        self.start_health_check_task();
        
        // 启动服务监控任务
        self.start_service_monitor_task();
        
        Ok(())
    }
    
    fn start_health_check_task(&self) {
        let services = self.services.clone();
        let interval = self.health_check_interval;
        let metrics = self.metrics.clone();
        
        tokio::spawn(async move {
            let mut check_interval = tokio::time::interval(interval);
            
            loop {
                check_interval.tick().await;
                
                // 获取所有需要检查的服务实例
                let instances_to_check = {
                    let services_guard = services.read().unwrap();
                    let mut to_check = Vec::new();
                    
                    for service_instances in services_guard.values() {
                        for instance in service_instances {
                            if let Some(check) = &instance.health_check {
                                to_check.push(instance.clone());
                            }
                        }
                    }
                    
                    to_check
                };
                
                // 执行健康检查
                for instance in instances_to_check {
                    // 异步执行健康检查
                    let instance_clone = instance.clone();
                    let services_clone = services.clone();
                    let metrics_clone = metrics.clone();
                    
                    tokio::spawn(async move {
                        if let Some(check) = &instance_clone.health_check {
                            let result = perform_health_check(&instance_clone, check).await;
                            
                            // 更新服务状态
                            let mut services_guard = services_clone.write().unwrap();
                            
                            if let Some(service_instances) = services_guard.get_mut(&instance_clone.service_name) {
                                if let Some(stored_instance) = service_instances.iter_mut()
                                    .find(|i| i.id == instance_clone.id) {
                                    
                                    let old_status = stored_instance.status.clone();
                                    stored_instance.last_check = Some(Utc::now());
                                    
                                    if result {
                                        // 健康检查成功
                                        if stored_instance.status != ServiceStatus::Healthy {
                                            stored_instance.status = ServiceStatus::Healthy;
                                            metrics_clone.record_service_healthy();
                                            log::info!("Service instance {} is now healthy", stored_instance.id);
                                        }
                                    } else {
                                        // 健康检查失败
                                        if stored_instance.status == ServiceStatus::Healthy {
                                            stored_instance.status = ServiceStatus::Unhealthy;
                                            metrics_clone.record_service_unhealthy();
                                            log::warn!("Service instance {} is now unhealthy", stored_instance.id);
                                        }
                                    }
                                    
                                    // 记录状态变更
                                    if old_status != stored_instance.status {
                                        metrics_clone.record_status_change();
                                    }
                                }
                            }
                        }
                    });
                }
                
                // 更新指标
                metrics.record_health_check_run();
            }
        });
    }
    
    fn start_service_monitor_task(&self) {
        let services = self.services.clone();
        let metrics = self.metrics.clone();
        
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_secs(30));
            
            loop {
                interval.tick().await;
                
                // 监控服务实例数量和状态
                let services_guard = services.read().unwrap();
                
                let mut total_instances = 0;
                let mut healthy_instances = 0;
                let mut unhealthy_instances = 0;
                
                for (service_name, instances) in services_guard.iter() {
                    total_instances += instances.len();
                    
                    let service_healthy = instances.iter()
                        .filter(|i| i.status == ServiceStatus::Healthy)
                        .count();
                        
                    let service_unhealthy = instances.iter()
                        .filter(|i| i.status == ServiceStatus::Unhealthy)
                        .count();
                        
                    healthy_instances += service_healthy;
                    unhealthy_instances += service_unhealthy;
                    
                    // 更新每个服务的指标
                    metrics.record_service_instances(service_name, instances.len());
                    metrics.record_service_healthy_instances(service_name, service_healthy);
                }
                
                // 更新总体指标
                metrics.record_total_instances(total_instances);
                metrics.record_healthy_instances(healthy_instances);
                metrics.record_unhealthy_instances(unhealthy_instances);
            }
        });
    }
    
    pub async fn register_service(
        &self,
        instance: ServiceInstance,
    ) -> Result<(), ServiceDiscoveryError> {
        let mut services_guard = self.services.write().unwrap();
        
        // 获取服务实例列表，如果不存在则创建
        let instances = services_guard
            .entry(instance.service_name.clone())
            .or_insert_with(Vec::new);
            
        // 检查是否已存在相同ID的实例
        if let Some(existing) = instances.iter_mut().find(|i| i.id == instance.id) {
            // 更新现有实例
            *existing = instance.clone();
            log::info!("Updated service instance: {}", instance.id);
        } else {
            // 添加新实例
            instances.push(instance.clone());
            log::info!("Registered new service instance: {}", instance.id);
            
            self.metrics.record_service_registered();
        }
        
        Ok(())
    }
    
    pub async fn deregister_service(
        &self,
        service_name: &str,
        instance_id: &str,
    ) -> Result<(), ServiceDiscoveryError> {
        let mut services_guard = self.services.write().unwrap();
        
        if let Some(instances) = services_guard.get_mut(service_name) {
            let before_len = instances.len();
            instances.retain(|i| i.id != instance_id);
            
            if before_len > instances.len() {
                log::info!("Deregistered service instance: {}", instance_id);
                self.metrics.record_service_deregistered();
                
                // 如果没有实例，移除整个服务
                if instances.is_empty() {
                    services_guard.remove(service_name);
                    log::info!("Removed service with no instances: {}", service_name);
                }
                
                return Ok(());
            }
        }
        
        Err(ServiceDiscoveryError::ServiceInstanceNotFound)
    }
    
    pub async fn discover_service(
        &self,
        service_name: &str,
    ) -> Result<Vec<ServiceInstance>, ServiceDiscoveryError> {
        let services_guard = self.services.read().unwrap();
        
        match services_guard.get(service_name) {
            Some(instances) => Ok(instances.clone()),
            None => Err(ServiceDiscoveryError::ServiceNotFound),
        }
    }
    
    pub async fn discover_healthy_service(
        &self,
        service_name: &str,
    ) -> Result<Vec<ServiceInstance>, ServiceDiscoveryError> {
        let services_guard = self.services.read().unwrap();
        
        match services_guard.get(service_name) {
            Some(instances) => {
                let healthy = instances.iter()
                    .filter(|i| i.status == ServiceStatus::Healthy)
                    .cloned()
                    .collect::<Vec<_>>();
                    
                if healthy.is_empty() {
                    Err(ServiceDiscoveryError::NoHealthyInstances)
                } else {
                    Ok(healthy)
                }
            }
            None => Err(ServiceDiscoveryError::ServiceNotFound),
        }
    }
    
    pub async fn select_instance(
        &self,
        service_name: &str,
        selector: &dyn ServiceSelector,
    ) -> Result<ServiceInstance, ServiceDiscoveryError> {
        let instances = self.discover_healthy_service(service_name).await?;
        
        match selector.select(&instances) {
            Some(instance) => Ok(instance.clone()),
            None => Err(ServiceDiscoveryError::NoHealthyInstances),
        }
    }
    
    pub async fn watch_service(
        &self,
        service_name: &str,
    ) -> Result<ServiceWatcher, ServiceDiscoveryError> {
        // 创建服务监视器
        let (tx, rx) = mpsc::channel(100);
        
        // 将监视器添加到服务通知列表
        // 在实际实现中，这需要更复杂的机制来处理服务变更通知
        
        Ok(ServiceWatcher { receiver: rx })
    }
}

// 执行健康检查
async fn perform_health_check(
    instance: &ServiceInstance,
    check: &HealthCheck,
) -> bool {
    // 在实际实现中，这里将执行HTTP请求、TCP连接等检查
    // 为简化示例，我们使用随机模拟结果
    
    tokio::time::sleep(Duration::from_millis(100)).await;
    
    // 模拟95%的成功率
    let success = rand::random::<u8>() < 240;
    
    success
}

// 服务选择器特征
pub trait ServiceSelector: Send + Sync {
    fn select<'a>(&self, instances: &'a [ServiceInstance]) -> Option<&'a ServiceInstance>;
}

// 随机服务选择器
pub struct RandomSelector;

impl ServiceSelector for RandomSelector {
    fn select<'a>(&self, instances: &'a [ServiceInstance]) -> Option<&'a ServiceInstance> {
        if instances.is_empty() {
            return None;
        }
        
        let index = rand::thread_rng().gen_range(0..instances.len());
        Some(&instances[index])
    }
}

// 轮询服务选择器
pub struct RoundRobinSelector {
    counter: AtomicUsize,
}

impl RoundRobinSelector {
    pub fn new() -> Self {
        Self {
            counter: AtomicUsize::new(0),
        }
    }
}

impl ServiceSelector for RoundRobinSelector {
    fn select<'a>(&self, instances: &'a [ServiceInstance]) -> Option<&'a ServiceInstance> {
        if instances.is_empty() {
            return None;
        }
        
        let count = self.counter.fetch_add(1, Ordering::Relaxed);
        let index = count % instances.len();
        
        Some(&instances[index])
    }
}

// 服务监视器
pub struct ServiceWatcher {
    receiver: mpsc::Receiver<ServiceEvent>,
}

impl ServiceWatcher {
    pub async fn next(&mut self) -> Option<ServiceEvent> {
        self.receiver.recv().await
    }
}

// 服务事件
#[derive(Debug, Clone)]
pub enum ServiceEvent {
    Registered(ServiceInstance),
    Updated(ServiceInstance),
    Deregistered(String, String), // service_name, instance_id
    StatusChanged(ServiceInstance, ServiceStatus),
}

// 服务发现错误
#[derive(Debug, thiserror::Error)]
pub enum ServiceDiscoveryError {
    #[error("Service not found")]
    ServiceNotFound,
    
    #[error("Service instance not found")]
    ServiceInstanceNotFound,
    
    #[error("No healthy instances available")]
    NoHealthyInstances,
    
    #[error("Other service discovery error: {0}")]
    Other(String),
}

// 服务发现指标
pub struct ServiceDiscoveryMetrics {
    total_instances: AtomicUsize,
    healthy_instances: AtomicUsize,
    unhealthy_instances: AtomicUsize,
    services_registered: AtomicU64,
    services_deregistered: AtomicU64,
    health_checks_run: AtomicU64,
    services_became_healthy: AtomicU64,
    services_became_unhealthy: AtomicU64,
    status_changes: AtomicU64,
    service_instances: Mutex<HashMap<String, usize>>,
    service_healthy_instances: Mutex<HashMap<String, usize>>,
}

impl ServiceDiscoveryMetrics {
    pub fn new() -> Self {
        Self {
            total_instances: AtomicUsize::new(0),
            healthy_instances: AtomicUsize::new(0),
            unhealthy_instances: AtomicUsize::new(0),
            services_registered: AtomicU64::new(0),
            services_deregistered: AtomicU64::new(0),
            health_checks_run: AtomicU64::new(0),
            services_became_healthy: AtomicU64::new(0),
            services_became_unhealthy: AtomicU64::new(0),
            status_changes: AtomicU64::new(0),
            service_instances: Mutex::new(HashMap::new()),
            service_healthy_instances: Mutex::new(HashMap::new()),
        }
    }
    
    pub fn record_total_instances(&self, count: usize) {
        self.total_instances.store(count, Ordering::Relaxed);
    }
    
    pub fn record_healthy_instances(&self, count: usize) {
        self.healthy_instances.store(count, Ordering::Relaxed);
    }
    
    pub fn record_unhealthy_instances(&self, count: usize) {
        self.unhealthy_instances.store(count, Ordering::Relaxed);
    }
    
    pub fn record_service_registered(&self) {
        self.services_registered.fetch_add(1, Ordering::Relaxed);
    }
    
    pub fn record_service_deregistered(&self) {
        self.services_deregistered.fetch_add(1, Ordering::Relaxed);
    }
    
    pub fn record_health_check_run(&self) {
        self.health_checks_run.fetch_add(1, Ordering::Relaxed);
    }
    
    pub fn record_service_healthy(&self) {
        self.services_became_healthy.fetch_add(1, Ordering::Relaxed);
    }
    
    pub fn record_service_unhealthy(&self) {
        self.services_became_unhealthy.fetch_add(1, Ordering::Relaxed);
    }
    
    pub fn record_status_change(&self) {
        self.status_changes.fetch_add(1, Ordering::Relaxed);
    }
    
    pub fn record_service_instances(&self, service_name: &str, count: usize) {
        let mut map = self.service_instances.lock().unwrap();
        map.insert(service_name.to_string(), count);
    }
    
    pub fn record_service_healthy_instances(&self, service_name: &str, count: usize) {
        let mut map = self.service_healthy_instances.lock().unwrap();
        map.insert(service_name.to_string(), count);
    }
}

// 分布式跟踪
pub struct TracingManager {
    service_name: String,
    tracer: Arc<dyn Tracer>,
    propagator: Arc<dyn Propagator>,
    sampler: Arc<dyn Sampler>,
    metrics: Arc<TracingMetrics>,
}

// 跟踪器特征
#[async_trait]
pub trait Tracer: Send + Sync {
    async fn start_span(&self, name: &str, parent: Option<&SpanContext>) -> Box<dyn Span>;
    async fn start_span_with_attributes(&self, name: &str, parent: Option<&SpanContext>, attributes: HashMap<String, Value>) -> Box<dyn Span>;
    async fn export_spans(&self, spans: Vec<Box<dyn Span>>) -> Result<(), TracingError>;
}

// 传播器特征
pub trait Propagator: Send + Sync {
    fn inject<W: Inject>(&self, span_context: &SpanContext, carrier: &mut W);
    fn extract<R: Extract>(&self, carrier: &R) -> Option<SpanContext>;
}

// 采样器特征
pub trait Sampler: Send + Sync {
    fn should_sample(&self, trace_id: &TraceId, name: &str) -> bool;
    fn description(&self) -> String;
}

// 注入器特征
pub trait Inject {
    fn set(&mut self, key: &str, value: &str);
}

// 提取器特征
pub trait Extract {
    fn get(&self, key: &str) -> Option<&str>;
    fn keys(&self) -> Vec<&str>;
}

// 跨度特征
#[async_trait]
pub trait Span: Send + Sync {
    fn context(&self) -> &SpanContext;
    fn name(&self) -> &str;
    
    fn set_attribute(&mut self, key: &str, value: Value);
    fn set_attributes(&mut self, attributes: HashMap<String, Value>);
    
    fn add_event(&mut self, name: &str, timestamp: Option<DateTime<Utc>>);
    fn add_event_with_attributes(&mut self, name: &str, attributes: HashMap<String, Value>, timestamp: Option<DateTime<Utc>>);
    
    fn set_status(&mut self, status: SpanStatus);
    
    async fn end(&mut self);
    
    fn is_recording(&self) -> bool;
    
    fn duration(&self) -> Option<Duration>;
}

// 跨度上下文
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpanContext {
    pub trace_id: TraceId,
    pub span_id: SpanId,
    pub trace_flags: TraceFlags,
    pub is_remote: bool,
}

// 跟踪ID
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TraceId([u8; 16]);

// 跨度ID
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpanId([u8; 8]);

// 跟踪标志
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TraceFlags(u8);

// 跨度状态
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SpanStatus {
    Unset,
    Ok,
    Error { description: Option<String> },
}

// 属性值
#[derive(Clone, Debug)]
pub enum Value {
    String(String),
    Int(i64),
    Float(f64),
    Bool(bool),
    Array(Vec<Value>),
}

// 跟踪错误
#[derive(Debug, thiserror::Error)]
pub enum TracingError {
    #[error("Export error: {0}")]
    ExportError(String),
    
    #[error("Other tracing error: {0}")]
    Other(String),
}

// 跟踪指标
pub struct TracingMetrics {
    spans_started: AtomicU64,
    spans_ended: AtomicU64,
    spans_exported: AtomicU64,
    export_errors: AtomicU64,
    sampling_rate: AtomicU64,
    span_duration: Histogram,
}

impl TracingMetrics {
    pub fn new() -> Self {
        Self {
            spans_started: AtomicU64::new(0),
            spans_ended: AtomicU64::new(0),
            spans_exported: AtomicU64::new(0),
            export_errors: AtomicU64::new(0),
            sampling_rate: AtomicU64::new(0),
            span_duration: Histogram::new(),
        }
    }
    
    pub fn record_span_started(&self) {
        self.spans_started.fetch_add(1, Ordering::Relaxed);
    }
    
    pub fn record_span_ended(&self) {
        self.spans_ended.fetch_add(1, Ordering::Relaxed);
    }
    
    pub fn record_spans_exported(&self, count: u64) {
        self.spans_exported.fetch_add(count, Ordering::Relaxed);
    }
    
    pub fn record_export_error(&self) {
        self.export_errors.fetch_add(1, Ordering::Relaxed);
    }
    
    pub fn record_sampling_decision(&self, sampled: bool) {
        if sampled {
            let current = self.sampling_rate.load(Ordering::Relaxed);
            let total = self.spans_started.load(Ordering::Relaxed);
            
            if total > 0 {
                let new_rate = ((current * (total - 1)) + 100) / total;
                self.sampling_rate.store(new_rate, Ordering::Relaxed);
            }
        } else {
            let current = self.sampling_rate.load(Ordering::Relaxed);
            let total = self.spans_started.load(Ordering::Relaxed);
            
            if total > 0 {
                let new_rate = (current * (total - 1)) / total;
                self.sampling_rate.store(new_rate, Ordering::Relaxed);
            }
        }
    }
    
    pub fn record_span_duration(&self, duration: Duration) {
        self.span_duration.record(duration.as_millis() as u64);
    }
}

impl TracingManager {
    pub fn new(
        service_name: String,
        tracer: Arc<dyn Tracer>,
        propagator: Arc<dyn Propagator>,
        sampler: Arc<dyn Sampler>,
    ) -> Self {
        Self {
            service_name,
            tracer,
            propagator,
            sampler,
            metrics: Arc::new(TracingMetrics::new()),
        }
    }
    
    pub async fn start_span(
        &self,
        name: &str,
        parent: Option<&SpanContext>,
    ) -> Result<Box<dyn Span>, TracingError> {
        self.metrics.record_span_started();
        
        let span = self.tracer.start_span(name, parent).await;
        
        // 记录采样决策
        let sampled = span.context().trace_flags.0 & 0x01 == 0x01;
        self.metrics.record_sampling_decision(sampled);
        
        Ok(span)
    }
    
    pub async fn start_span_with_attributes(
        &self,
        name: &str,
        parent: Option<&SpanContext>,
        attributes: HashMap<String, Value>,
    ) -> Result<Box<dyn Span>, TracingError> {
        self.metrics.record_span_started();
        
        let span = self.tracer.start_span_with_attributes(name, parent, attributes).await;
        
        // 记录采样决策
        let sampled = span.context().trace_flags.0 & 0x01 == 0x01;
        self.metrics.record_sampling_decision(sampled);
        
        Ok(span)
    }
    
    pub fn inject<W: Inject>(&self, span: &Box<dyn Span>, carrier: &mut W) {
        self.propagator.inject(span.context(), carrier);
    }
    
    pub fn extract<R: Extract>(&self, carrier: &R) -> Option<SpanContext> {
        self.propagator.extract(carrier)
    }
    
    pub async fn end_span(&self, mut span: Box<dyn Span>) -> Result<(), TracingError> {
        let start_time = Utc::now();
        
        span.end().await;
        
        self.metrics.record_span_ended();
        
        if let Some(duration) = span.duration() {
            self.metrics.record_span_duration(duration);
        }
        
        Ok(())
    }
}

// 主类应用入口
pub struct DistributedSystemApp {
    node_id: NodeId,
    cluster: Arc<ClusterManager>,
    partition_manager: Arc<PartitionManager>,
    service_discovery: Arc<ServiceDiscovery>,
    state_manager: Arc<DistributedStateManager>,
    consensus: Arc<dyn ConsensusProtocol>,
    tracing: Arc<TracingManager>,
}

impl DistributedSystemApp {
    pub async fn new(config: AppConfig) -> Result<Self, AppError> {
        // 初始化RPC传输
        let transport = Arc::new(HttpRpcTransport::new(&config.node_address)?);
        
        // 初始化集群管理器
        let cluster = Arc::new(ClusterManager::new(
            config.node_id.clone(),
            transport.clone(),
            Duration::from_secs(5),
            Duration::from_secs(15),
        ));
        
        // 初始化共识协议
        let log_store = Arc::new(FileLogStore::new(&config.log_store_path)?);
        let consensus = Arc::new(RaftConsensus::new(
            config.node_id.clone(),
            config.raft_config,
            transport.clone(),
            log_store,
        ));
        
        // 初始化分区管理器
        let partition_manager = Arc::new(PartitionManager::new(
            config.node_id.clone(),
            cluster.clone(),
        ));
        
        // 初始化服务发现
        let service_discovery = Arc::new(ServiceDiscovery::new(
            cluster.clone(),
            Duration::from_secs(10),
        ));
        
        // 初始化状态管理器
        let local_store = Arc::new(LevelDbStore::new(&config.state_store_path)?);
        let state_manager = Arc::new(DistributedStateManager::new(
            consensus.clone(),
            local_store,
            10000,
            Duration::from_secs(300),
        ));
        
        // 初始化跟踪
        let tracer = Arc::new(JaegerTracer::new(&config.tracing_config)?);
        let propagator = Arc::new(W3CPropagator::new());
        let sampler = Arc::new(RateLimitingSampler::new(config.tracing_config.sampling_rate));
        
        let tracing = Arc::new(TracingManager::new(
            config.service_name.clone(),
            tracer,
            propagator,
            sampler,
        ));
        
        Ok(Self {
            node_id: config.node_id,
            cluster,
            partition_manager,
            service_discovery,
            state_manager,
            consensus,
            tracing,
        })
    }
    
    pub async fn start(&self) -> Result<(), AppError> {
        // 启动集群管理
        self.cluster.start(self.config.initial_peers.clone()).await
            .map_err(|e| AppError::ClusterError(e.to_string()))?;
            
        // 启动共识协议
        self.consensus.start().await
            .map_err(|e| AppError::ConsensusError(e.to_string()))?;
            
        // 启动分区管理
        self.partition_manager.start().await
            .map_err(|e| AppError::PartitionError(e.to_string()))?;
            
        // 启动服务发现
        self.service_discovery.start().await
            .map_err(|e| AppError::ServiceDiscoveryError(e.to_string()))?;
            
        // 注册自身服务
        self.register_self_service().await?;
            
        log::info!("Distributed system application started successfully");
        
        Ok(())
    }
    
    async fn register_self_service(&self) -> Result<(), AppError> {
        // 创建服务实例
        let instance = ServiceInstance {
            id: format!("{}-{}", self.config.service_name, self.node_id),
            service_name: self.config.service_name.clone(),
            node_id: self.node_id.clone(),
            address: self.config.node_address.split(':').next().unwrap_or("127.0.0.1").to_string(),
            port: self.config.node_address.split(':').nth(1).unwrap_or("8080").parse().unwrap_or(8080),
            metadata: HashMap::new(),
            status: ServiceStatus::Starting,
            health_check: Some(HealthCheck {
                endpoint: format!("http://{}/health", self.config.node_address),
                interval: Duration::from_secs(10),
                timeout: Duration::from_secs(2),
                failure_threshold: 3,
                success_threshold: 1,
            }),
            last_check: None,
        };
        
        // 注册服务
        self.service_discovery.register_service(instance).await
            .map_err(|e| AppError::ServiceDiscoveryError(e.to_string()))
    }
    
    pub async fn shutdown(&self) -> Result<(), AppError> {
        // 离开集群
        self.cluster.leave_cluster().await
            .map_err(|e| AppError::ClusterError(e.to_string()))?;
            
        // 停止共识协议
        // ...
        
        log::info!("Distributed system application shutdown successfully");
        
        Ok(())
    }
}

// 应用错误
#[derive(Debug, thiserror::Error)]
pub enum AppError {
    #[error("Configuration error: {0}")]
    ConfigError(String),
    
    #[error("Cluster error: {0}")]
    ClusterError(String),
    
    #[error("Consensus error: {0}")]
    ConsensusError(String),
    
    #[error("Partition error: {0}")]
    PartitionError(String),
    
    #[error("Service discovery error: {0}")]
    ServiceDiscoveryError(String),
    
    #[error("State error: {0}")]
    StateError(String),
    
    #[error("Tracing error: {0}")]
    TracingError(String),
    
    #[error("Other error: {0}")]
    Other(String),
}

// 应用配置
#[derive(Clone, Debug)]
pub struct AppConfig {
    pub node_id: String,
    pub service_name: String,
    pub node_address: String,
    pub initial_peers: Vec<String>,
    pub log_store_path: String,
    pub state_store_path: String,
    pub raft_config: RaftConfig,
    pub tracing_config: TracingConfig,
}

// 结束
```

## 结论与未来方向

本文详细介绍了一个基于Rust的高可用分布式系统框架，以实现适用于物联网、微服务和边缘计算等场景的分布式工作流系统。
该系统通过整合一系列关键组件，提供了一个强大而灵活的解决方案：

### 1. 主要贡献

#### 共识协议

我们基于Raft算法实现了健壮的共识机制，确保了系统状态在多节点间的一致性。
通过细致处理日志复制、领导者选举和成员变更，提供了高可用的共识基础。

#### 分区管理

系统引入了智能分区策略，通过一致性哈希和均衡分配算法，实现了数据的合理分布和负载均衡，同时提供了平滑的分区迁移机制。

#### 服务发现

基于健康检查实现的服务发现机制，使系统能够自动识别、注册和监控服务实例，提高了系统的弹性和可观测性。

#### 状态管理

分布式状态管理层提供了一致性保证的数据访问模式，
结合本地缓存优化了读取性能，同时支持状态变更通知，实现了系统组件间的松耦合协作。

#### 分布式跟踪

集成的跟踪系统使开发者能够监控和分析跨多个节点的请求链路，帮助诊断性能瓶颈和系统故障。

### 2. 架构特点

#### 类型安全与可组合性

充分利用Rust的类型系统，实现了安全的组件组合和状态转换，降低了运行时错误的可能性。

#### 异步编程模型

基于Tokio的异步运行时，使系统能够高效处理大量并发连接，同时简化了复杂异步工作流的表达。

#### 分层设计

明确的接口边界与抽象层次，使系统能够适应不同的存储后端、传输协议和部署环境。

#### 可观测性

内置的指标收集和跟踪能力，使系统运行状态透明可见，便于性能优化和问题排查。

### 3. 实用价值

本框架特别适合构建以下类型的分布式应用：

- **物联网数据处理管道**：可靠地收集、处理和存储来自大量分散设备的数据
- **微服务协调系统**：管理跨多个服务的工作流执行和状态转换
- **边缘计算平台**：在靠近数据源的位置高效处理数据，同时维持与中心系统的一致性

### 4. 未来研究方向

#### 自适应分区策略

研究基于访问模式和节点负载的智能分区调整算法，进一步优化数据分布和系统性能。

#### 混合共识协议

探索在不同场景下切换共识算法的可能性，
例如在高吞吐量需求下使用BFT类算法，在低冲突环境下使用更轻量的协议。

#### 高级状态压缩

开发更高效的状态压缩和快照机制，减少存储占用并加速节点恢复。

#### 机器学习集成

将机器学习模型引入系统决策过程，
例如预测服务实例健康状况、优化资源分配或检测异常模式。

#### 跨语言接口

拓展系统的接口能力，使用Protocol Buffers或其他序列化机制实现与非Rust服务的无缝集成。

### 5. 总结

本文展示的分布式系统框架代表了利用Rust语言构建高性能、可靠且可维护分布式系统的一种现代方法。
通过提供一系列经过精心设计的模块和抽象，
该框架使开发者能够专注于业务逻辑，而将分布式系统的复杂性留给框架处理。
随着边缘计算和物联网应用的不断增长，
这类强调安全性、性能和可靠性的分布式系统框架将变得越来越重要。

## 系统架构概览图

```text
┌─────────────────────────────────────────────────────────────────┐
│                      分布式系统应用程序                           │
└───────────────┬─────────────────┬───────────────┬───────────────┘
                │                 │               │
    ┌───────────▼─────┐   ┌───────▼───────┐   ┌───▼───────────┐
    │   集群管理子系统 │   │  共识协议层    │   │  服务发现      │
    └───────────┬─────┘   └───────┬───────┘   └───┬───────────┘
                │                 │               │
                └────────┬────────┘               │
                         │                        │
              ┌──────────▼──────────┐   ┌─────────▼─────────┐
              │    分区管理子系统    │   │    分布式状态管理   │
              └──────────┬──────────┘   └─────────┬─────────┘
                         │                        │
                         └────────────┬───────────┘
                                      │
                            ┌─────────▼─────────┐
                            │   分布式跟踪系统   │
                            └───────────────────┘
```

该框架通过这些紧密集成的组件，
为开发者提供了构建复杂分布式系统所需的全部基础设施，
同时保持了Rust语言的安全性、性能和可维护性优势。
未来的工作将进一步增强系统的自适应能力、跨平台兼容性和与现代计算模式的整合。
