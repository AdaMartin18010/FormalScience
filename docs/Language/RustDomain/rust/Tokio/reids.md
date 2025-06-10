# rust redis

我将展示如何使用 Rust 和 tokio 与 Redis 进行交互的详细示例。我们将使用 `redis` crate 并展示各种功能。
首先创建项目并添加依赖：

```toml
[package]
name = "redis-example"
version = "0.1.0"
edition = "2021"

[dependencies]
tokio = { version = "1.36", features = ["full"] }
redis = { version = "0.24", features = ["tokio-comp", "connection-manager"] }
futures = "0.3"
anyhow = "1.0"
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
async-stream = "0.3"
```

以下是完整的示例代码：

```rust:src/main.rs
use redis::{AsyncCommands, RedisResult, Value};
use serde::{Deserialize, Serialize};
use std::time::Duration;
use async_stream::try_stream;
use futures::StreamExt;

#[derive(Debug, Serialize, Deserialize)]
struct User {
    id: i32,
    name: String,
    age: i32,
}

// Redis 连接管理器
struct RedisManager {
    client: redis::Client,
}

impl RedisManager {
    async fn new(url: &str) -> RedisResult<Self> {
        let client = redis::Client::open(url)?;
        Ok(Self { client })
    }

    async fn get_connection(&self) -> RedisResult<redis::aio::Connection> {
        self.client.get_async_connection().await
    }
}

// 实现各种 Redis 操作的结构体
struct RedisOperations {
    conn: redis::aio::Connection,
}

impl RedisOperations {
    async fn new(conn: redis::aio::Connection) -> Self {
        Self { conn }
    }

    // 基本的字符串操作
    async fn string_operations(&mut self) -> RedisResult<()> {
        println!("=== 字符串操作 ===");
        
        // 设置值
        self.conn.set("key1", "value1").await?;
        
        // 设置带过期时间的值
        self.conn.set_ex("key2", "value2", 60).await?;
        
        // 获取值
        let value: String = self.conn.get("key1").await?;
        println!("key1的值: {}", value);

        // 自增操作
        let _: i32 = self.conn.incr("counter", 1).await?;
        let counter: i32 = self.conn.get("counter").await?;
        println!("计数器值: {}", counter);

        Ok(())
    }

    // Hash操作
    async fn hash_operations(&mut self) -> RedisResult<()> {
        println!("\n=== Hash操作 ===");
        
        let user = User {
            id: 1,
            name: "张三".to_string(),
            age: 25,
        };

        // 存储hash
        self.conn.hset("user:1", "id", user.id).await?;
        self.conn.hset("user:1", "name", &user.name).await?;
        self.conn.hset("user:1", "age", user.age).await?;

        // 获取整个hash
        let values: HashMap<String, String> = self.conn.hgetall("user:1").await?;
        println!("用户信息: {:?}", values);

        Ok(())
    }

    // 列表操作
    async fn list_operations(&mut self) -> RedisResult<()> {
        println!("\n=== 列表操作 ===");
        
        // 推入元素
        self.conn.rpush("list1", "item1").await?;
        self.conn.rpush("list1", "item2").await?;
        self.conn.lpush("list1", "item0").await?;

        // 获取列表范围
        let items: Vec<String> = self.conn.lrange("list1", 0, -1).await?;
        println!("列表内容: {:?}", items);

        Ok(())
    }

    // 集合操作
    async fn set_operations(&mut self) -> RedisResult<()> {
        println!("\n=== 集合操作 ===");
        
        // 添加元素
        self.conn.sadd("set1", "member1").await?;
        self.conn.sadd("set1", "member2").await?;
        self.conn.sadd("set1", "member3").await?;

        // 判断元素是否存在
        let exists: bool = self.conn.sismember("set1", "member1").await?;
        println!("member1是否存在: {}", exists);

        // 获取所有成员
        let members: Vec<String> = self.conn.smembers("set1").await?;
        println!("集合成员: {:?}", members);

        Ok(())
    }

    // 有序集合操作
    async fn sorted_set_operations(&mut self) -> RedisResult<()> {
        println!("\n=== 有序集合操作 ===");
        
        // 添加成员和分数
        self.conn.zadd("scores", "player1", 100).await?;
        self.conn.zadd("scores", "player2", 200).await?;
        self.conn.zadd("scores", "player3", 150).await?;

        // 获取分数范围内的成员
        let players: Vec<String> = self.conn.zrangebyscore("scores", 100, 200).await?;
        println!("得分在100-200之间的玩家: {:?}", players);

        Ok(())
    }

    // 发布订阅示例
    async fn pub_sub_example(&mut self) -> RedisResult<()> {
        println!("\n=== 发布订阅示例 ===");
        
        // 创建一个新的连接用于订阅
        let mut pubsub = self.client.get_async_connection().await?.into_pubsub();
        pubsub.subscribe("channel1").await?;

        // 在另一个任务中处理消息
        tokio::spawn(async move {
            let mut stream = pubsub.on_message();
            while let Some(msg) = stream.next().await {
                let payload: String = msg.get_payload().unwrap();
                println!("收到消息: {}", payload);
            }
        });

        // 发布消息
        self.conn.publish("channel1", "Hello Redis!").await?;

        Ok(())
    }

    // 使用生成器扫描键
    async fn scan_keys(&mut self, pattern: &str) -> impl Stream<Item = RedisResult<String>> {
        let pattern = pattern.to_string();
        let mut conn = self.conn.clone();

        try_stream! {
            let mut cursor = 0;
            loop {
                let (next_cursor, keys): (i64, Vec<String>) = redis::cmd("SCAN")
                    .arg(cursor)
                    .arg("MATCH")
                    .arg(&pattern)
                    .arg("COUNT")
                    .arg(10)
                    .query_async(&mut conn)
                    .await?;

                for key in keys {
                    yield key;
                }

                if next_cursor == 0 {
                    break;
                }
                cursor = next_cursor;
            }
        }
    }

    // Pipeline 批量操作
    async fn pipeline_operations(&mut self) -> RedisResult<()> {
        println!("\n=== Pipeline操作 ===");
        
        let mut pipe = redis::pipe();
        pipe.set("pipe_key1", "value1")
            .set("pipe_key2", "value2")
            .get("pipe_key1")
            .get("pipe_key2");

        let results: Vec<Value> = pipe.query_async(&mut self.conn).await?;
        println!("Pipeline结果: {:?}", results);

        Ok(())
    }

    // 事务操作
    async fn transaction_operations(&mut self) -> RedisResult<()> {
        println!("\n=== 事务操作 ===");
        
        let mut pipe = redis::pipe();
        pipe.atomic()
            .set("tx_key1", "value1")
            .set("tx_key2", "value2")
            .get("tx_key1")
            .get("tx_key2");

        let results: Vec<Value> = pipe.query_async(&mut self.conn).await?;
        println!("事务结果: {:?}", results);

        Ok(())
    }
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 创建Redis连接管理器
    let manager = RedisManager::new("redis://127.0.0.1/").await?;
    let conn = manager.get_connection().await?;
    
    let mut redis_ops = RedisOperations::new(conn).await;

    // 执行各种操作
    redis_ops.string_operations().await?;
    redis_ops.hash_operations().await?;
    redis_ops.list_operations().await?;
    redis_ops.set_operations().await?;
    redis_ops.sorted_set_operations().await?;
    redis_ops.pub_sub_example().await?;
    redis_ops.pipeline_operations().await?;
    redis_ops.transaction_operations().await?;

    // 使用生成器扫描键
    println!("\n=== 使用生成器扫描键 ===");
    let mut keys_stream = redis_ops.scan_keys("key*").await;
    while let Some(key) = keys_stream.next().await {
        match key {
            Ok(k) => println!("找到键: {}", k),
            Err(e) => println!("错误: {}", e),
        }
    }

    Ok(())
}
```

这个示例展示了以下主要功能：

1. **基本连接管理**：
   - 创建连接池
   - 异步连接处理

2. **数据类型操作**：
   - 字符串操作
   - Hash操作
   - 列表操作
   - 集合操作
   - 有序集合操作

3. **高级特性**：
   - 发布订阅
   - Pipeline批量操作
   - 事务处理
   - 键扫描生成器

4. **实用工具**：
   - 序列化/反序列化
   - 错误处理
   - 连接管理

要运行这个示例，需要先启动Redis服务。可以使用Docker快速启动：

```bash
docker run --name redis-server -d -p 6379:6379 redis
```

使用建议：

1. 在生产环境中，建议使用连接池来管理Redis连接
2. 对于大量数据的操作，使用Pipeline可以显著提高性能
3. 使用事务确保操作的原子性
4. 对于大键的扫描，使用生成器模式避免内存占用过大
5. 合理设置超时和重试策略

您可以根据实际需求调整代码，比如：

- 添加重试机制
- 实现更复杂的连接池
- 添加监控和日志
- 实现更多的Redis命令封装

这个示例提供了一个良好的起点，您可以基于此进行扩展和定制。
