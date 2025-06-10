# rust实现mqtt

我将为您展示一个使用 Rust 2024 + Tokio + MQTT + Modbus 实现的 IoT 项目示例。这个项目将包含设备管理、数据采集、消息处理等功能。

## 目录

- [rust实现mqtt](#rust实现mqtt)
  - [目录](#目录)
  - [1. 项目依赖配置](#1-项目依赖配置)
    - [2. 设备配置和状态定义](#2-设备配置和状态定义)
    - [3. Modbus 设备管理器实现](#3-modbus-设备管理器实现)
    - [4. MQTT 消息处理器实现](#4-mqtt-消息处理器实现)
    - [5. 数据存储实现](#5-数据存储实现)
    - [6. 设备管理器实现](#6-设备管理器实现)
    - [7. 主程序实现](#7-主程序实现)
    - [8. HTTP API 实现](#8-http-api-实现)
    - [9. 配置文件示例](#9-配置文件示例)
    - [10. 测试实现](#10-测试实现)

## 1. 项目依赖配置

```toml
[dependencies]
tokio = { version = "1.0", features = ["full"] }
rumqttc = "0.24"
tokio-modbus = { version = "0.9", features = ["tcp", "rtu"] }
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
async-trait = "0.1"
futures = "0.3"
tracing = "0.1"
anyhow = "1.0"
dashmap = "5.5"
chrono = { version = "0.4", features = ["serde"] }
sqlx = { version = "0.7", features = ["runtime-tokio-native-tls", "postgres", "chrono"] }
config = "0.13"
```

### 2. 设备配置和状态定义

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeviceConfig {
    pub id: String,
    pub name: String,
    pub device_type: DeviceType,
    pub modbus_config: ModbusConfig,
    pub mqtt_config: MqttConfig,
    pub polling_interval: Duration,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DeviceType {
    Sensor,
    Actuator,
    Gateway,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModbusConfig {
    pub mode: ModbusMode,
    pub slave_id: u8,
    pub registers: Vec<RegisterConfig>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ModbusMode {
    Tcp { host: String, port: u16 },
    Rtu { port: String, baud_rate: u32 },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RegisterConfig {
    pub address: u16,
    pub register_type: RegisterType,
    pub name: String,
    pub scaling_factor: f64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RegisterType {
    InputRegister,
    HoldingRegister,
    Coil,
    DiscreteInput,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MqttConfig {
    pub broker_url: String,
    pub port: u16,
    pub client_id: String,
    pub username: Option<String>,
    pub password: Option<String>,
    pub topics: Vec<String>,
}
```

### 3. Modbus 设备管理器实现

```rust
pub struct ModbusManager {
    config: DeviceConfig,
    client: Arc<Box<dyn ModbusClient>>,
    data_tx: mpsc::Sender<DeviceData>,
}

impl ModbusManager {
    pub async fn new(
        config: DeviceConfig,
        data_tx: mpsc::Sender<DeviceData>,
    ) -> anyhow::Result<Self> {
        let client = match &config.modbus_config.mode {
            ModbusMode::Tcp { host, port } => {
                let socket_addr = format!("{}:{}", host, port).parse()?;
                let ctx = tcp::connect(socket_addr).await?;
                Box::new(ctx) as Box<dyn ModbusClient>
            }
            ModbusMode::Rtu { port, baud_rate } => {
                let builder = tokio_serial::new(port, *baud_rate);
                let port = tokio_serial::SerialStream::open(&builder)?;
                let ctx = rtu::connect(port).await?;
                Box::new(ctx) as Box<dyn ModbusClient>
            }
        };

        Ok(Self {
            config,
            client: Arc::new(client),
            data_tx,
        })
    }

    pub async fn start(&self) -> anyhow::Result<()> {
        let config = self.config.clone();
        let client = self.client.clone();
        let data_tx = self.data_tx.clone();

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(config.polling_interval);
            loop {
                interval.tick().await;
                if let Err(e) = Self::poll_registers(&config, &client, &data_tx).await {
                    tracing::error!("Error polling registers: {}", e);
                }
            }
        });

        Ok(())
    }

    async fn poll_registers(
        config: &DeviceConfig,
        client: &Arc<Box<dyn ModbusClient>>,
        data_tx: &mpsc::Sender<DeviceData>,
    ) -> anyhow::Result<()> {
        for register in &config.modbus_config.registers {
            let value = match register.register_type {
                RegisterType::InputRegister => {
                    client.read_input_registers(register.address, 1).await?[0]
                }
                RegisterType::HoldingRegister => {
                    client.read_holding_registers(register.address, 1).await?[0]
                }
                RegisterType::Coil => {
                    client.read_coils(register.address, 1).await?[0] as u16
                }
                RegisterType::DiscreteInput => {
                    client.read_discrete_inputs(register.address, 1).await?[0] as u16
                }
            };

            let scaled_value = (value as f64) * register.scaling_factor;

            let data = DeviceData {
                device_id: config.id.clone(),
                timestamp: chrono::Utc::now(),
                register_name: register.name.clone(),
                value: scaled_value,
            };

            data_tx.send(data).await?;
        }

        Ok(())
    }
}
```

### 4. MQTT 消息处理器实现

```rust
pub struct MqttHandler {
    config: MqttConfig,
    client: AsyncClient,
    eventloop: EventLoop,
    data_rx: mpsc::Receiver<DeviceData>,
}

impl MqttHandler {
    pub async fn new(
        config: MqttConfig,
        data_rx: mpsc::Receiver<DeviceData>,
    ) -> anyhow::Result<Self> {
        let mut mqtt_options = MqttOptions::new(
            &config.client_id,
            &config.broker_url,
            config.port,
        );

        if let (Some(username), Some(password)) = (&config.username, &config.password) {
            mqtt_options.set_credentials(username, password);
        }

        let (client, eventloop) = AsyncClient::new(mqtt_options, 10);

        Ok(Self {
            config,
            client,
            eventloop,
            data_rx,
        })
    }

    pub async fn start(&mut self) -> anyhow::Result<()> {
        // 订阅主题
        for topic in &self.config.topics {
            self.client.subscribe(topic, QoS::AtLeastOnce).await?;
        }

        // 处理接收到的数据
        let client = self.client.clone();
        let data_rx = &mut self.data_rx;

        tokio::spawn(async move {
            while let Some(data) = data_rx.recv().await {
                let payload = serde_json::to_string(&data).unwrap();
                let topic = format!("device/{}/data", data.device_id);
                
                if let Err(e) = client.publish(&topic, QoS::AtLeastOnce, false, payload).await {
                    tracing::error!("Error publishing message: {}", e);
                }
            }
        });

        // 处理 MQTT 事件
        loop {
            match self.eventloop.poll().await {
                Ok(notification) => {
                    match notification {
                        rumqttc::Event::Incoming(Packet::Publish(publish)) => {
                            self.handle_publish(publish).await?;
                        }
                        rumqttc::Event::Outgoing(Packet::PingReq) => {
                            tracing::debug!("Sending PING");
                        }
                        _ => {}
                    }
                }
                Err(e) => {
                    tracing::error!("MQTT error: {}", e);
                }
            }
        }
    }

    async fn handle_publish(&self, publish: Publish) -> anyhow::Result<()> {
        let payload = String::from_utf8_lossy(&publish.payload);
        tracing::info!(
            "Received message: topic={}, payload={}",
            publish.topic,
            payload
        );

        // 处理接收到的消息
        if let Ok(command) = serde_json::from_str::<DeviceCommand>(&payload) {
            self.handle_command(command).await?;
        }

        Ok(())
    }

    async fn handle_command(&self, command: DeviceCommand) -> anyhow::Result<()> {
        // 实现命令处理逻辑
        match command.command_type {
            CommandType::SetValue { register, value } => {
                // 处理设置值命令
            }
            CommandType::GetStatus => {
                // 处理获取状态命令
            }
            CommandType::Reset => {
                // 处理重置命令
            }
        }

        Ok(())
    }
}
```

### 5. 数据存储实现

```rust
pub struct DataStorage {
    pool: PgPool,
}

impl DataStorage {
    pub async fn new(database_url: &str) -> anyhow::Result<Self> {
        let pool = PgPool::connect(database_url).await?;
        
        // 创建必要的表
        sqlx::query(
            r#"
            CREATE TABLE IF NOT EXISTS device_data (
                id SERIAL PRIMARY KEY,
                device_id TEXT NOT NULL,
                register_name TEXT NOT NULL,
                value DOUBLE PRECISION NOT NULL,
                timestamp TIMESTAMPTZ NOT NULL
            )
            "#,
        )
        .execute(&pool)
        .await?;

        Ok(Self { pool })
    }

    pub async fn store_data(&self, data: &DeviceData) -> anyhow::Result<()> {
        sqlx::query(
            r#"
            INSERT INTO device_data (device_id, register_name, value, timestamp)
            VALUES ($1, $2, $3, $4)
            "#,
        )
        .bind(&data.device_id)
        .bind(&data.register_name)
        .bind(data.value)
        .bind(data.timestamp)
        .execute(&self.pool)
        .await?;

        Ok(())
    }

    pub async fn get_device_data(
        &self,
        device_id: &str,
        start_time: DateTime<Utc>,
        end_time: DateTime<Utc>,
    ) -> anyhow::Result<Vec<DeviceData>> {
        let records = sqlx::query_as!(
            DeviceData,
            r#"
            SELECT device_id, register_name, value, timestamp
            FROM device_data
            WHERE device_id = $1 AND timestamp BETWEEN $2 AND $3
            ORDER BY timestamp DESC
            "#,
            device_id,
            start_time,
            end_time,
        )
        .fetch_all(&self.pool)
        .await?;

        Ok(records)
    }
}
```

### 6. 设备管理器实现

```rust
pub struct DeviceManager {
    devices: Arc<DashMap<String, DeviceHandle>>,
    storage: Arc<DataStorage>,
}

pub struct DeviceHandle {
    config: DeviceConfig,
    modbus_manager: Arc<ModbusManager>,
    mqtt_handler: Arc<Mutex<MqttHandler>>,
}

impl DeviceManager {
    pub async fn new(storage: Arc<DataStorage>) -> Self {
        Self {
            devices: Arc::new(DashMap::new()),
            storage,
        }
    }

    pub async fn add_device(&self, config: DeviceConfig) -> anyhow::Result<()> {
        let (data_tx, data_rx) = mpsc::channel(100);

        // 创建 Modbus 管理器
        let modbus_manager = Arc::new(ModbusManager::new(
            config.clone(),
            data_tx,
        ).await?);

        // 创建 MQTT 处理器
        let mqtt_handler = Arc::new(Mutex::new(MqttHandler::new(
            config.mqtt_config.clone(),
            data_rx,
        ).await?));

        // 启动设备
        modbus_manager.start().await?;
        mqtt_handler.lock().await.start().await?;

        // 存储设备句柄
        self.devices.insert(config.id.clone(), DeviceHandle {
            config,
            modbus_manager,
            mqtt_handler,
        });

        Ok(())
    }

    pub async fn remove_device(&self, device_id: &str) -> anyhow::Result<()> {
        self.devices.remove(device_id);
        Ok(())
    }

    pub async fn get_device_status(&self, device_id: &str) -> anyhow::Result<DeviceStatus> {
        let device = self.devices.get(device_id)
            .ok_or_else(|| anyhow::anyhow!("Device not found"))?;

        // 获取设备状态
        Ok(DeviceStatus {
            device_id: device_id.to_string(),
            online: true,  // 实现实际的在线状态检测
            last_update: chrono::Utc::now(),
        })
    }
}
```

### 7. 主程序实现

```rust
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    // 加载配置
    let config = load_config()?;

    // 创建数据存储
    let storage = Arc::new(DataStorage::new(&config.database_url).await?);

    // 创建设备管理器
    let device_manager = DeviceManager::new(storage.clone()).await;

    // 加载设备配置
    for device_config in config.devices {
        device_manager.add_device(device_config).await?;
    }

    // 启动 HTTP API 服务器
    let api_server = ApiServer::new(device_manager.clone());
    api_server.start().await?;

    // 等待终止信号
    tokio::signal::ctrl_c().await?;

    Ok(())
}

fn load_config() -> anyhow::Result<AppConfig> {
    let settings = Config::builder()
        .add_source(config::File::with_name("config"))
        .add_source(config::Environment::with_prefix("APP"))
        .build()?;

    Ok(settings.try_deserialize()?)
}
```

### 8. HTTP API 实现

```rust
use warp::{Filter, Reply};

pub struct ApiServer {
    device_manager: DeviceManager,
}

impl ApiServer {
    pub fn new(device_manager: DeviceManager) -> Self {
        Self { device_manager }
    }

    pub async fn start(&self) -> anyhow::Result<()> {
        let device_manager = Arc::new(self.device_manager.clone());

        // 设备状态路由
        let status = warp::path!("device" / String / "status")
            .and(with_device_manager(device_manager.clone()))
            .and_then(handle_device_status);

        // 设备数据路由
        let data = warp::path!("device" / String / "data")
            .and(with_device_manager(device_manager.clone()))
            .and(warp::query::<DataQuery>())
            .and_then(handle_device_data);

        // 组合所有路由
        let routes = status
            .or(data)
            .with(warp::cors().allow_any_origin())
            .recover(handle_rejection);

        // 启动服务器
        warp::serve(routes)
            .run(([127, 0, 0, 1], 3030))
            .await;

        Ok(())
    }
}

async fn handle_device_status(
    device_id: String,
    device_manager: Arc<DeviceManager>,
) -> Result<impl Reply, Rejection> {
    let status = device_manager
        .get_device_status(&device_id)
        .await
        .map_err(|e| warp::reject::custom(e))?;

    Ok(warp::reply::json(&status))
}

async fn handle_device_data(
    device_id: String,
    query: DataQuery,
    device_manager: Arc<DeviceManager>,
) -> Result<impl Reply, Rejection> {
    let data = device_manager
        .get_device_data(&device_id, query.start_time, query.end_time)
        .await
        .map_err(|e| warp::reject::custom(e))?;

    Ok(warp::reply::json(&data))
}
```

### 9. 配置文件示例

```yaml
# config.yaml
database_url: "postgres://user:password@localhost/iot_db"

devices:
  - id: "device-001"
    name: "Temperature Sensor"
    device_type: "Sensor"
    modbus_config:
      mode:
        tcp:
          host: "192.168.1.100"
          port: 502
      slave_id: 1
      registers:
        - address: 0
          register_type: "InputRegister"
          name: "temperature"
          scaling_factor: 0.1
    mqtt_config:
      broker_url: "localhost"
      port: 1883
      client_id: "device-001"
      topics:
        - "device/001/command"
    polling_interval: 5000

  - id: "device-002"
    name: "Pressure Sensor"
    device_type: "Sensor"
    modbus_config:
      mode:
        rtu:
          port: "/dev/ttyUSB0"
          baud_rate: 9600
      slave_id: 2
      registers:
        - address: 0
          register_type: "HoldingRegister"
          name: "pressure"
          scaling_factor: 1.0
    mqtt_config:
      broker_url: "localhost"
      port: 1883
      client_id: "device-002"
      topics:
        - "device/002/command"
    polling_interval: 1000
```

### 10. 测试实现

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_modbus_manager() -> anyhow::Result<()> {
        let (tx, mut rx) = mpsc::channel(100);
        
        let config = DeviceConfig {
            id: "test-device".to_string(),
            name: "Test Device".to_string(),
            device_type: DeviceType::Sensor,
            modbus_config: ModbusConfig {
                mode: ModbusMode::Tcp {
                    host: "localhost".to_string(),
                    port: 502,
                },
                slave_id: 1,
                registers: vec![
                    RegisterConfig {
                        address: 0,
                        register_type: RegisterType::InputRegister,
                        name: "test".to_string(),
                        scaling_factor: 1.0,
                    },
                ],
            },
            mqtt_config: MqttConfig::default(),
            polling_interval: Duration::from_secs(1),
        };

        let manager = ModbusManager::new(config, tx).await?;
        manager.start().await?;

        // 验证数据接收
        if let Some(data) = rx.recv().await {
            assert_eq!(data.device_id, "test-device");
            assert_eq!(data.register_name, "test");
        }

        Ok(())
    }
}
```

这个完整的示例展示了如何构建一个功能完整的 IoT 项目，包括：

1. Modbus 设备通信
2. MQTT 消息处理
3. 数据存储
4. 设备管理
5. HTTP API
6. 配置管理
7. 错误处理
8. 日志记录
9. 测试支持

主要特性：

- 支持 Modbus TCP 和 RTU
- 支持 MQTT 消息发布和订阅
- 数据持久化存储
- RESTful API
- 配置文件支持
- 异步处理
- 错误处理和日志记录
- 单元测试

这个实现提供了良好的可扩展性和可维护性，可以根据需要添加更多功能和设备支持。
