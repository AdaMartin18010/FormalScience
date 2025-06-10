# Rust实现mqtt

下面是一个使用 Tokio 实现的多线程组合模式组件示例，支持 MQTT 消息订阅和命令模式：

## 目录

- [Rust实现mqtt](#rust实现mqtt)
  - [目录](#目录)
  - [1. 项目依赖配置](#1-项目依赖配置)
    - [2. 组件接口定义](#2-组件接口定义)
    - [3. 基础组件实现](#3-基础组件实现)
    - [4. MQTT 组件实现](#4-mqtt-组件实现)
    - [5. 命令处理器实现](#5-命令处理器实现)
    - [6. 消息处理器实现](#6-消息处理器实现)
    - [7. 组合组件实现](#7-组合组件实现)
    - [8. 自定义消息处理器示例](#8-自定义消息处理器示例)
    - [9. 自定义命令处理器示例](#9-自定义命令处理器示例)
    - [10. 使用示例](#10-使用示例)

## 1. 项目依赖配置

```toml
[dependencies]
tokio = { version = "1.0", features = ["full"] }
rumqttc = "0.24"
async-trait = "0.1"
futures = "0.3"
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
anyhow = "1.0"
tracing = "0.1"
uuid = { version = "1.0", features = ["v4"] }
```

### 2. 组件接口定义

```rust
use async_trait::async_trait;
use std::sync::Arc;
use tokio::sync::broadcast;

#[async_trait]
pub trait Component: Send + Sync {
    async fn start(&self) -> anyhow::Result<()>;
    async fn stop(&self) -> anyhow::Result<()>;
    fn add_child(&mut self, component: Box<dyn Component>);
    fn remove_child(&mut self, id: &str);
    fn get_id(&self) -> &str;
}

#[async_trait]
pub trait MessageHandler: Send + Sync {
    async fn handle_message(&self, topic: &str, payload: &[u8]) -> anyhow::Result<()>;
}

#[async_trait]
pub trait CommandHandler: Send + Sync {
    async fn execute(&self, command: Command) -> anyhow::Result<()>;
}
```

### 3. 基础组件实现

```rust
pub struct BaseComponent {
    id: String,
    children: Vec<Box<dyn Component>>,
    message_tx: broadcast::Sender<Message>,
    command_tx: broadcast::Sender<Command>,
}

impl BaseComponent {
    pub fn new(id: &str) -> (Self, broadcast::Receiver<Message>, broadcast::Receiver<Command>) {
        let (message_tx, message_rx) = broadcast::channel(100);
        let (command_tx, command_rx) = broadcast::channel(100);
        
        (
            Self {
                id: id.to_string(),
                children: Vec::new(),
                message_tx,
                command_tx,
            },
            message_rx,
            command_rx,
        )
    }

    pub fn broadcast_message(&self, message: Message) {
        let _ = self.message_tx.send(message);
    }

    pub fn send_command(&self, command: Command) {
        let _ = self.command_tx.send(command);
    }
}

#[async_trait]
impl Component for BaseComponent {
    async fn start(&self) -> anyhow::Result<()> {
        for child in &self.children {
            child.start().await?;
        }
        Ok(())
    }

    async fn stop(&self) -> anyhow::Result<()> {
        for child in &self.children {
            child.stop().await?;
        }
        Ok(())
    }

    fn add_child(&mut self, component: Box<dyn Component>) {
        self.children.push(component);
    }

    fn remove_child(&mut self, id: &str) {
        self.children.retain(|c| c.get_id() != id);
    }

    fn get_id(&self) -> &str {
        &self.id
    }
}
```

### 4. MQTT 组件实现

```rust
pub struct MqttComponent {
    base: BaseComponent,
    client: AsyncClient,
    event_loop: EventLoop,
    subscriptions: Arc<Mutex<HashMap<String, Vec<Box<dyn MessageHandler>>>>>,
}

impl MqttComponent {
    pub async fn new(
        id: &str,
        broker_url: &str,
        port: u16,
    ) -> anyhow::Result<Self> {
        let mut options = MqttOptions::new(id, broker_url, port);
        options.set_keep_alive(Duration::from_secs(5));

        let (client, event_loop) = AsyncClient::new(options, 10);
        let (base, _, _) = BaseComponent::new(id);

        Ok(Self {
            base,
            client,
            event_loop,
            subscriptions: Arc::new(Mutex::new(HashMap::new())),
        })
    }

    pub async fn subscribe(
        &self,
        topic: &str,
        handler: Box<dyn MessageHandler>,
    ) -> anyhow::Result<()> {
        self.client.subscribe(topic, QoS::AtLeastOnce).await?;
        
        let mut subs = self.subscriptions.lock().await;
        subs.entry(topic.to_string())
            .or_insert_with(Vec::new)
            .push(handler);
            
        Ok(())
    }

    async fn handle_mqtt_events(&self) {
        while let Ok(notification) = self.event_loop.poll().await {
            if let rumqttc::Event::Incoming(Packet::Publish(publish)) = notification {
                let topic = publish.topic;
                let payload = publish.payload;
                
                let subs = self.subscriptions.lock().await;
                if let Some(handlers) = subs.get(&topic) {
                    for handler in handlers {
                        if let Err(e) = handler.handle_message(&topic, &payload).await {
                            tracing::error!("Error handling message: {}", e);
                        }
                    }
                }
            }
        }
    }
}

#[async_trait]
impl Component for MqttComponent {
    async fn start(&self) -> anyhow::Result<()> {
        self.base.start().await?;
        
        let self_clone = self.clone();
        tokio::spawn(async move {
            self_clone.handle_mqtt_events().await;
        });
        
        Ok(())
    }

    async fn stop(&self) -> anyhow::Result<()> {
        self.base.stop().await?;
        self.client.disconnect().await?;
        Ok(())
    }

    // ... other Component trait implementations
}
```

### 5. 命令处理器实现

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Command {
    Start { component_id: String },
    Stop { component_id: String },
    Subscribe { topic: String },
    Unsubscribe { topic: String },
    Custom { name: String, payload: Value },
}

pub struct CommandProcessor {
    handlers: HashMap<String, Box<dyn CommandHandler>>,
}

impl CommandProcessor {
    pub fn new() -> Self {
        Self {
            handlers: HashMap::new(),
        }
    }

    pub fn register_handler(
        &mut self,
        command_type: &str,
        handler: Box<dyn CommandHandler>,
    ) {
        self.handlers.insert(command_type.to_string(), handler);
    }

    pub async fn process_command(&self, command: Command) -> anyhow::Result<()> {
        match &command {
            Command::Custom { name, .. } => {
                if let Some(handler) = self.handlers.get(name) {
                    handler.execute(command).await?;
                }
            }
            _ => {
                self.handle_system_command(command).await?;
            }
        }
        Ok(())
    }

    async fn handle_system_command(&self, command: Command) -> anyhow::Result<()> {
        match command {
            Command::Start { component_id } => {
                // Handle start command
            }
            Command::Stop { component_id } => {
                // Handle stop command
            }
            Command::Subscribe { topic } => {
                // Handle subscribe command
            }
            Command::Unsubscribe { topic } => {
                // Handle unsubscribe command
            }
            _ => {}
        }
        Ok(())
    }
}
```

### 6. 消息处理器实现

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Message {
    pub topic: String,
    pub payload: Value,
    pub timestamp: DateTime<Utc>,
}

pub struct MessageProcessor {
    handlers: Vec<Box<dyn MessageHandler>>,
}

impl MessageProcessor {
    pub fn new() -> Self {
        Self {
            handlers: Vec::new(),
        }
    }

    pub fn add_handler(&mut self, handler: Box<dyn MessageHandler>) {
        self.handlers.push(handler);
    }

    pub async fn process_message(&self, topic: &str, payload: &[u8]) -> anyhow::Result<()> {
        for handler in &self.handlers {
            handler.handle_message(topic, payload).await?;
        }
        Ok(())
    }
}
```

### 7. 组合组件实现

```rust
pub struct CompositeComponent {
    base: BaseComponent,
    mqtt: Arc<MqttComponent>,
    command_processor: Arc<CommandProcessor>,
    message_processor: Arc<MessageProcessor>,
}

impl CompositeComponent {
    pub async fn new(
        id: &str,
        mqtt_config: MqttConfig,
    ) -> anyhow::Result<Self> {
        let (base, message_rx, command_rx) = BaseComponent::new(id);
        
        let mqtt = Arc::new(MqttComponent::new(
            &format!("{}_mqtt", id),
            &mqtt_config.broker_url,
            mqtt_config.port,
        ).await?);

        let command_processor = Arc::new(CommandProcessor::new());
        let message_processor = Arc::new(MessageProcessor::new());

        let component = Self {
            base,
            mqtt,
            command_processor,
            message_processor,
        };

        component.setup_message_handling(message_rx);
        component.setup_command_handling(command_rx);

        Ok(component)
    }

    fn setup_message_handling(&self, mut message_rx: broadcast::Receiver<Message>) {
        let message_processor = self.message_processor.clone();
        
        tokio::spawn(async move {
            while let Ok(message) = message_rx.recv().await {
                if let Err(e) = message_processor
                    .process_message(&message.topic, &serde_json::to_vec(&message.payload).unwrap())
                    .await
                {
                    tracing::error!("Error processing message: {}", e);
                }
            }
        });
    }

    fn setup_command_handling(&self, mut command_rx: broadcast::Receiver<Command>) {
        let command_processor = self.command_processor.clone();
        
        tokio::spawn(async move {
            while let Ok(command) = command_rx.recv().await {
                if let Err(e) = command_processor.process_command(command).await {
                    tracing::error!("Error processing command: {}", e);
                }
            }
        });
    }
}

#[async_trait]
impl Component for CompositeComponent {
    async fn start(&self) -> anyhow::Result<()> {
        self.base.start().await?;
        self.mqtt.start().await?;
        Ok(())
    }

    async fn stop(&self) -> anyhow::Result<()> {
        self.mqtt.stop().await?;
        self.base.stop().await?;
        Ok(())
    }

    // ... other Component trait implementations
}
```

### 8. 自定义消息处理器示例

```rust
pub struct CustomMessageHandler {
    name: String,
}

#[async_trait]
impl MessageHandler for CustomMessageHandler {
    async fn handle_message(&self, topic: &str, payload: &[u8]) -> anyhow::Result<()> {
        let message = String::from_utf8_lossy(payload);
        tracing::info!("[{}] Received message on {}: {}", self.name, topic, message);
        Ok(())
    }
}
```

### 9. 自定义命令处理器示例

```rust
pub struct CustomCommandHandler {
    name: String,
}

#[async_trait]
impl CommandHandler for CustomCommandHandler {
    async fn execute(&self, command: Command) -> anyhow::Result<()> {
        match command {
            Command::Custom { name, payload } => {
                tracing::info!("[{}] Executing command {}: {:?}", self.name, name, payload);
                // 处理自定义命令
                Ok(())
            }
            _ => Ok(()),
        }
    }
}
```

### 10. 使用示例

```rust
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    // 创建组合组件
    let mqtt_config = MqttConfig {
        broker_url: "localhost".to_string(),
        port: 1883,
    };

    let mut composite = CompositeComponent::new("main", mqtt_config).await?;

    // 添加消息处理器
    composite.message_processor.add_handler(Box::new(CustomMessageHandler {
        name: "handler1".to_string(),
    }));

    // 添加命令处理器
    composite.command_processor.register_handler(
        "custom_command",
        Box::new(CustomCommandHandler {
            name: "handler1".to_string(),
        }),
    );

    // 订阅主题
    composite.mqtt.subscribe(
        "test/topic",
        Box::new(CustomMessageHandler {
            name: "mqtt_handler".to_string(),
        }),
    ).await?;

    // 启动组件
    composite.start().await?;

    // 发送命令
    composite.base.send_command(Command::Custom {
        name: "custom_command".to_string(),
        payload: json!({ "action": "test" }),
    });

    // 等待信号
    tokio::signal::ctrl_c().await?;

    // 停止组件
    composite.stop().await?;

    Ok(())
}
```

这个完整的示例展示了如何：

1. 实现组件接口和基础组件
2. 创建 MQTT 组件处理消息订阅
3. 实现命令处理系统
4. 使用组合模式组织组件
5. 处理异步消息和命令
6. 实现自定义处理器
7. 管理组件生命周期

通过这种方式，您可以构建一个灵活的、可扩展的异步组件系统，支持 MQTT 消息订阅和命令模式。
