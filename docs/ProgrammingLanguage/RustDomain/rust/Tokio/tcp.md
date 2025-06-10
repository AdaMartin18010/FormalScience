# rust Tcp IM

我将为您展示一个使用 Rust 2024 实现的完整 IM (即时通讯) 系统，包含 TCP/UDP 服务端和客户端。

## 目录

- [rust Tcp IM](#rust-tcp-im)
  - [目录](#目录)
  - [1. 项目依赖配置](#1-项目依赖配置)
  - [2. 消息协议定义](#2-消息协议定义)
  - [3. TCP 服务端实现](#3-tcp-服务端实现)
  - [4. TCP 客户端实现](#4-tcp-客户端实现)
  - [5. UDP 消息广播实现](#5-udp-消息广播实现)
  - [6. 消息存储实现](#6-消息存储实现)
  - [7. 错误处理实现](#7-错误处理实现)
  - [8. 指标收集实现](#8-指标收集实现)
  - [9. 主程序实现](#9-主程序实现)
  - [10. 测试实现](#10-测试实现)

## 1. 项目依赖配置

```toml
[dependencies]
tokio = { version = "1.0", features = ["full"] }
futures = "0.3"
bytes = "1.0"
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
tracing = "0.1"
anyhow = "1.0"
thiserror = "1.0"
async-trait = "0.1"
dashmap = "5.5"
uuid = { version = "1.0", features = ["v4"] }
tokio-util = { version = "0.7", features = ["codec"] }
tokio-stream = "0.1"
quinn = "0.10"  # QUIC 协议支持
parking_lot = "0.12"
backoff = { version = "0.4", features = ["tokio"] }
metrics = "0.21"
```

## 2. 消息协议定义

```rust
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Message {
    // 认证消息
    Auth {
        user_id: String,
        token: String,
    },
    AuthResponse {
        success: bool,
        error: Option<String>,
    },
    
    // 聊天消息
    Chat {
        message_id: String,
        from: String,
        to: String,
        content: String,
        timestamp: i64,
    },
    
    // 消息确认
    Ack {
        message_id: String,
        status: AckStatus,
    },
    
    // 心跳消息
    Ping,
    Pong,
    
    // 状态更新
    Presence {
        user_id: String,
        status: UserStatus,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AckStatus {
    Received,
    Delivered,
    Read,
    Failed(String),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum UserStatus {
    Online,
    Away,
    Offline,
}

// 消息编解码器
pub struct MessageCodec;

impl Encoder<Message> for MessageCodec {
    type Error = anyhow::Error;

    fn encode(&mut self, item: Message, dst: &mut BytesMut) -> Result<(), Self::Error> {
        let json = serde_json::to_string(&item)?;
        dst.extend_from_slice(json.as_bytes());
        dst.extend_from_slice(b"\n");
        Ok(())
    }
}

impl Decoder for MessageCodec {
    type Item = Message;
    type Error = anyhow::Error;

    fn decode(&mut self, src: &mut BytesMut) -> Result<Option<Self::Item>, Self::Error> {
        if let Some(i) = src.iter().position(|&b| b == b'\n') {
            let line = src.split_to(i + 1);
            let json = String::from_utf8(line.to_vec())?;
            let message = serde_json::from_str(&json)?;
            Ok(Some(message))
        } else {
            Ok(None)
        }
    }
}
```

## 3. TCP 服务端实现

```rust
pub struct ImServer {
    clients: Arc<DashMap<String, ConnectedClient>>,
    message_store: Arc<MessageStore>,
}

struct ConnectedClient {
    user_id: String,
    tx: mpsc::UnboundedSender<Message>,
    status: UserStatus,
    last_ping: Arc<AtomicI64>,
}

impl ImServer {
    pub fn new() -> Self {
        Self {
            clients: Arc::new(DashMap::new()),
            message_store: Arc::new(MessageStore::new()),
        }
    }

    pub async fn run(&self, addr: SocketAddr) -> anyhow::Result<()> {
        let listener = TcpListener::bind(addr).await?;
        tracing::info!("Server listening on {}", addr);

        // 启动心跳检查
        self.start_heartbeat_checker();

        while let Ok((stream, addr)) = listener.accept().await {
            let clients = self.clients.clone();
            let message_store = self.message_store.clone();

            tokio::spawn(async move {
                if let Err(e) = Self::handle_connection(stream, addr, clients, message_store).await {
                    tracing::error!("Connection error: {}", e);
                }
            });
        }

        Ok(())
    }

    async fn handle_connection(
        stream: TcpStream,
        addr: SocketAddr,
        clients: Arc<DashMap<String, ConnectedClient>>,
        message_store: Arc<MessageStore>,
    ) -> anyhow::Result<()> {
        let (mut writer, mut reader) = Framed::new(stream, MessageCodec).split();

        // 等待认证
        let auth = match reader.next().await {
            Some(Ok(Message::Auth { user_id, token })) => {
                if Self::validate_token(&token) {
                    Some(user_id)
                } else {
                    writer.send(Message::AuthResponse {
                        success: false,
                        error: Some("Invalid token".to_string()),
                    }).await?;
                    None
                }
            }
            _ => None,
        };

        if let Some(user_id) = auth {
            let (tx, mut rx) = mpsc::unbounded_channel();
            
            // 注册客户端
            clients.insert(user_id.clone(), ConnectedClient {
                user_id: user_id.clone(),
                tx,
                status: UserStatus::Online,
                last_ping: Arc::new(AtomicI64::new(chrono::Utc::now().timestamp())),
            });

            // 发送离线消息
            let offline_messages = message_store.get_offline_messages(&user_id).await?;
            for msg in offline_messages {
                writer.send(msg).await?;
            }

            // 处理消息
            loop {
                tokio::select! {
                    Some(msg) = reader.next() => {
                        match msg? {
                            Message::Chat { message_id, from, to, content, timestamp } => {
                                // 存储消息
                                message_store.store_message(Message::Chat {
                                    message_id: message_id.clone(),
                                    from: from.clone(),
                                    to: to.clone(),
                                    content,
                                    timestamp,
                                }).await?;

                                // 发送消息给目标用户
                                if let Some(client) = clients.get(&to) {
                                    let _ = client.tx.send(Message::Chat {
                                        message_id,
                                        from,
                                        to,
                                        content,
                                        timestamp,
                                    });
                                }
                            }
                            Message::Ping => {
                                if let Some(client) = clients.get(&user_id) {
                                    client.last_ping.store(
                                        chrono::Utc::now().timestamp(),
                                        Ordering::SeqCst,
                                    );
                                }
                                writer.send(Message::Pong).await?;
                            }
                            _ => {}
                        }
                    }
                    Some(msg) = rx.recv() => {
                        writer.send(msg).await?;
                    }
                    else => break,
                }
            }

            // 清理客户端
            clients.remove(&user_id);
        }

        Ok(())
    }

    fn start_heartbeat_checker(&self) {
        let clients = self.clients.clone();
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_secs(30));
            loop {
                interval.tick().await;
                let now = chrono::Utc::now().timestamp();
                
                clients.retain(|_, client| {
                    now - client.last_ping.load(Ordering::SeqCst) < 90
                });
            }
        });
    }
}
```

## 4. TCP 客户端实现

```rust
pub struct ImClient {
    user_id: String,
    token: String,
    connection: Option<ClientConnection>,
    config: ClientConfig,
    message_handlers: Vec<Box<dyn MessageHandler>>,
}

struct ClientConnection {
    writer: SplitSink<Framed<TcpStream, MessageCodec>, Message>,
    reader_task: JoinHandle<()>,
}

#[derive(Clone)]
pub struct ClientConfig {
    server_addr: SocketAddr,
    reconnect_interval: Duration,
    max_reconnect_attempts: u32,
}

impl ImClient {
    pub fn new(
        user_id: String,
        token: String,
        config: ClientConfig,
    ) -> Self {
        Self {
            user_id,
            token,
            connection: None,
            config,
            message_handlers: Vec::new(),
        }
    }

    pub async fn connect(&mut self) -> anyhow::Result<()> {
        let backoff = ExponentialBackoff {
            initial_interval: self.config.reconnect_interval,
            max_interval: Duration::from_secs(60),
            multiplier: 2.0,
            max_elapsed_time: Some(Duration::from_secs(300)),
            ..Default::default()
        };

        backoff::future::retry(backoff, || async {
            match self.try_connect().await {
                Ok(()) => Ok(()),
                Err(e) => {
                    tracing::warn!("Connection failed, retrying: {}", e);
                    Err(backoff::Error::Transient(e))
                }
            }
        })
        .await?;

        Ok(())
    }

    async fn try_connect(&mut self) -> anyhow::Result<()> {
        let stream = TcpStream::connect(self.config.server_addr).await?;
        let (writer, reader) = Framed::new(stream, MessageCodec).split();

        // 发送认证消息
        writer.send(Message::Auth {
            user_id: self.user_id.clone(),
            token: self.token.clone(),
        }).await?;

        // 启动心跳
        let (heartbeat_tx, heartbeat_rx) = mpsc::channel(1);
        self.start_heartbeat(heartbeat_tx);

        // 启动消息读取任务
        let handlers = self.message_handlers.clone();
        let reader_task = tokio::spawn(async move {
            Self::handle_messages(reader, handlers, heartbeat_rx).await
        });

        self.connection = Some(ClientConnection {
            writer,
            reader_task,
        });

        Ok(())
    }

    async fn handle_messages(
        mut reader: SplitStream<Framed<TcpStream, MessageCodec>>,
        handlers: Vec<Box<dyn MessageHandler>>,
        mut heartbeat_rx: mpsc::Receiver<()>,
    ) {
        loop {
            tokio::select! {
                Some(msg) = reader.next() => {
                    match msg {
                        Ok(message) => {
                            for handler in &handlers {
                                handler.handle_message(&message).await;
                            }
                        }
                        Err(e) => {
                            tracing::error!("Error reading message: {}", e);
                            break;
                        }
                    }
                }
                _ = heartbeat_rx.recv() => {
                    if let Err(e) = reader.send(Message::Ping).await {
                        tracing::error!("Error sending heartbeat: {}", e);
                        break;
                    }
                }
                else => break,
            }
        }
    }

    pub async fn send_message(
        &mut self,
        to: String,
        content: String,
    ) -> anyhow::Result<String> {
        let message_id = Uuid::new_v4().to_string();
        let message = Message::Chat {
            message_id: message_id.clone(),
            from: self.user_id.clone(),
            to,
            content,
            timestamp: chrono::Utc::now().timestamp(),
        };

        if let Some(conn) = &mut self.connection {
            conn.writer.send(message).await?;
        } else {
            return Err(anyhow::anyhow!("Not connected"));
        }

        Ok(message_id)
    }

    fn start_heartbeat(&self, tx: mpsc::Sender<()>) {
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_secs(30));
            loop {
                interval.tick().await;
                if tx.send(()).await.is_err() {
                    break;
                }
            }
        });
    }
}
```

## 5. UDP 消息广播实现

```rust
pub struct BroadcastServer {
    socket: UdpSocket,
    clients: Arc<DashMap<SocketAddr, UserInfo>>,
}

impl BroadcastServer {
    pub async fn new(addr: SocketAddr) -> anyhow::Result<Self> {
        let socket = UdpSocket::bind(addr).await?;
        Ok(Self {
            socket,
            clients: Arc::new(DashMap::new()),
        })
    }

    pub async fn run(&self) -> anyhow::Result<()> {
        let mut buf = vec![0u8; 65536];
        
        loop {
            let (size, addr) = self.socket.recv_from(&mut buf).await?;
            let message = String::from_utf8_lossy(&buf[..size]);
            
            // 广播消息给所有客户端
            for client in self.clients.iter() {
                if *client.key() != addr {
                    self.socket.send_to(&buf[..size], client.key()).await?;
                }
            }
        }
    }
}

pub struct BroadcastClient {
    socket: UdpSocket,
    server_addr: SocketAddr,
}

impl BroadcastClient {
    pub async fn new(
        local_addr: SocketAddr,
        server_addr: SocketAddr,
    ) -> anyhow::Result<Self> {
        let socket = UdpSocket::bind(local_addr).await?;
        Ok(Self {
            socket,
            server_addr,
        })
    }

    pub async fn send_broadcast(&self, message: &str) -> anyhow::Result<()> {
        self.socket.send_to(message.as_bytes(), self.server_addr).await?;
        Ok(())
    }

    pub async fn receive_broadcasts(&self) -> anyhow::Result<impl Stream<Item = String>> {
        let socket = self.socket.clone();
        let stream = async_stream::stream! {
            let mut buf = vec![0u8; 65536];
            loop {
                match socket.recv_from(&mut buf).await {
                    Ok((size, _)) => {
                        if let Ok(message) = String::from_utf8(buf[..size].to_vec()) {
                            yield message;
                        }
                    }
                    Err(e) => {
                        tracing::error!("Error receiving broadcast: {}", e);
                        break;
                    }
                }
            }
        };

        Ok(stream)
    }
}
```

## 6. 消息存储实现

```rust
pub struct MessageStore {
    messages: Arc<DashMap<String, Vec<Message>>>,
    db: Arc<Database>,
}

impl MessageStore {
    pub fn new() -> Self {
        Self {
            messages: Arc::new(DashMap::new()),
            db: Arc::new(Database::new()),
        }
    }

    pub async fn store_message(&self, message: Message) -> anyhow::Result<()> {
        if let Message::Chat { to, .. } = &message {
            self.messages
                .entry(to.clone())
                .or_default()
                .push(message.clone());
            
            self.db.store_message(&message).await?;
        }
        Ok(())
    }

    pub async fn get_offline_messages(&self, user_id: &str) -> anyhow::Result<Vec<Message>> {
        let messages = self.db.get_offline_messages(user_id).await?;
        Ok(messages)
    }

    pub async fn mark_messages_delivered(&self, user_id: &str, message_ids: &[String]) -> anyhow::Result<()> {
        self.db.mark_messages_delivered(user_id, message_ids).await?;
        Ok(())
    }
}
```

## 7. 错误处理实现

```rust
#[derive(Debug, thiserror::Error)]
pub enum ImError {
    #[error("Network error: {0}")]
    Network(#[from] std::io::Error),

    #[error("Authentication failed: {0}")]
    Auth(String),

    #[error("Message error: {0}")]
    Message(String),

    #[error("Connection error: {0}")]
    Connection(String),

    #[error("Database error: {0}")]
    Database(#[from] sqlx::Error),

    #[error("Timeout error")]
    Timeout,
}

impl From<ImError> for backoff::Error<ImError> {
    fn from(error: ImError) -> Self {
        match error {
            ImError::Network(_) | ImError::Connection(_) => backoff::Error::Transient(error),
            _ => backoff::Error::Permanent(error),
        }
    }
}
```

## 8. 指标收集实现

```rust
pub struct ImMetrics {
    connected_clients: Gauge,
    messages_sent: Counter,
    messages_received: Counter,
    message_latency: Histogram,
}

impl ImMetrics {
    pub fn new() -> Self {
        Self {
            connected_clients: Gauge::new("im_connected_clients", "Number of connected clients"),
            messages_sent: Counter::new("im_messages_sent", "Number of messages sent"),
            messages_received: Counter::new("im_messages_received", "Number of messages received"),
            message_latency: Histogram::new("im_message_latency", "Message latency in milliseconds"),
        }
    }

    pub fn record_client_connected(&self) {
        self.connected_clients.inc();
    }

    pub fn record_client_disconnected(&self) {
        self.connected_clients.dec();
    }

    pub fn record_message_sent(&self) {
        self.messages_sent.inc();
    }

    pub fn record_message_received(&self) {
        self.messages_received.inc();
    }

    pub fn record_message_latency(&self, latency: Duration) {
        self.message_latency.observe(latency.as_millis() as f64);
    }
}
```

## 9. 主程序实现

```rust
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    // 初始化指标收集
    let metrics = Arc::new(ImMetrics::new());

    // 创建服务器
    let server = ImServer::new();
    let broadcast_server = BroadcastServer::new("0.0.0.0:8001".parse()?).await?;

    // 启动服务器
    let server_handle = tokio::spawn(async move {
        server.run("0.0.0.0:8000".parse()?).await
    });

    let broadcast_handle = tokio::spawn(async move {
        broadcast_server.run().await
    });

    // 等待服务器终止
    tokio::select! {
        result = server_handle => {
            if let Err(e) = result? {
                tracing::error!("Server error: {}", e);
            }
        }
        result = broadcast_handle => {
            if let Err(e) = result? {
                tracing::error!("Broadcast server error: {}", e);
            }
        }
    }

    Ok(())
}
```

## 10. 测试实现

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_client_connection() -> anyhow::Result<()> {
        let mut client = ImClient::new(
            "test-user".to_string(),
            "test-token".to_string(),
            ClientConfig {
                server_addr: "127.0.0.1:8000".parse()?,
                reconnect_interval: Duration::from_secs(1),
                max_reconnect_attempts: 3,
            },
        );

        client.connect().await?;
        
        let message_id = client.send_message(
            "test-recipient".to_string(),
            "Hello, world!".to_string(),
        ).await?;

        assert!(!message_id.is_empty());
        Ok(())
    }

    #[tokio::test]
    async fn test_broadcast() -> anyhow::Result<()> {
        let client = BroadcastClient::new(
            "127.0.0.1:0".parse()?,
            "127.0.0.1:8001".parse()?,
        ).await?;

        client.send_broadcast("Test broadcast message").await?;

        let mut broadcasts = client.receive_broadcasts().await?;
        if let Some(message) = broadcasts.next().await {
            assert_eq!(message, "Test broadcast message");
        }

        Ok(())
    }
}
```

这个完整的示例展示了如何构建一个功能完整的 IM 系统，包括：

1. TCP 消息服务
2. UDP 广播服务
3. 消息存储
4. 重连机制
5. 心跳检测
6. 错误处理
7. 指标收集
8. 测试支持

主要特性：

- 异步处理
- 消息可靠性
- 连接管理
- 广播支持
- 离线消息
- 心跳检测
- 重连机制
- 错误处理
- 指标收集
- 单元测试

这个实现提供了良好的可扩展性和可靠性，可以根据需要添加更多功能和特性。
