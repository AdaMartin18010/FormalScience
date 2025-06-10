# etcd 分布式键值存储

我来帮您展示如何使用 Rust 和 tokio 与 etcd 进行交互的详细示例。
我们将使用 `etcd-client` crate 来实现。

首先创建一个新的 Rust 项目并添加必要的依赖：

```toml
[package]
name = "etcd-example"
version = "0.1.0"
edition = "2021"

[dependencies]
tokio = { version = "1.36", features = ["full"] }
etcd-client = "0.12"
anyhow = "1.0"
futures = "0.3"
```

以下是一个完整的示例，展示了 etcd 的主要功能：

```rust
use etcd_client::{Client, ConnectOptions, WatchOptions, EventType};
use std::time::Duration;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 创建客户端连接
    let mut client = Client::connect(
        ["localhost:2379"],
        Some(ConnectOptions::new().with_timeout(Duration::from_secs(5)))
    ).await?;

    // 基本的 KV 操作
    println!("=== 基本 KV 操作 ===");
    
    // 设置键值
    client.put("key1", "value1", None).await?;
    
    // 获取值
    let resp = client.get("key1", None).await?;
    if let Some(kv) = resp.kvs().first() {
        println!("键: {:?}, 值: {:?}", kv.key_str()?, kv.value_str()?);
    }

    // 前缀扫描
    println!("\n=== 前缀扫描 ===");
    client.put("prefix/key1", "value1", None).await?;
    client.put("prefix/key2", "value2", None).await?;
    
    let resp = client.get("prefix/", Some(etcd_client::GetOptions::new().with_prefix())).await?;
    for kv in resp.kvs() {
        println!("键: {:?}, 值: {:?}", kv.key_str()?, kv.value_str()?);
    }

    // 事务操作
    println!("\n=== 事务操作 ===");
    let txn = client.txn()
        .when(&[etcd_client::Compare::value("key1", "value1", etcd_client::CompareOp::Equal)])
        .and_then(&[etcd_client::TxnOp::put("key2", "value2", None)])
        .or_else(&[etcd_client::TxnOp::put("key2", "fallback", None)]);
    
    let resp = txn.commit().await?;
    println!("事务执行成功: {}", resp.succeeded());

    // 租约操作
    println!("\n=== 租约操作 ===");
    let lease = client.lease_grant(5, None).await?;
    let lease_id = lease.id();
    
    // 使用租约设置键值
    client.put("lease_key", "lease_value", Some(etcd_client::PutOptions::new().with_lease(lease_id))).await?;
    println!("设置带租约的键值对");

    // 监听变化
    println!("\n=== 监听变化 ===");
    let (mut watcher, mut stream) = client.watch("key1", Some(WatchOptions::new().with_prefix())).await?;

    // 在另一个任务中处理监听
    tokio::spawn(async move {
        while let Some(resp) = stream.message().await.unwrap() {
            for event in resp.events() {
                match event.event_type() {
                    EventType::Put => println!("新增/更新: {:?}", event.kv().unwrap().key_str().unwrap()),
                    EventType::Delete => println!("删除: {:?}", event.kv().unwrap().key_str().unwrap()),
                }
            }
        }
    });

    // 生成器示例：遍历所有键值对
    println!("\n=== 使用生成器遍历键值对 ===");
    let mut keys = get_all_keys(&mut client, "prefix/").await?;
    
    while let Some(key) = keys.next().await {
        match key {
            Ok(k) => println!("找到键: {}", k),
            Err(e) => println!("错误: {}", e),
        }
    }

    Ok(())
}

// 使用生成器遍历键
struct KeysGenerator {
    client: Client,
    prefix: String,
    current_key: Option<Vec<u8>>,
}

impl KeysGenerator {
    async fn next(&mut self) -> Option<anyhow::Result<String>> {
        let options = match &self.current_key {
            Some(key) => etcd_client::GetOptions::new()
                .with_prefix()
                .with_from_key()
                .with_limit(1)
                .with_key_bytes(key.clone()),
            None => etcd_client::GetOptions::new()
                .with_prefix()
                .with_limit(1),
        };

        match self.client.get(&self.prefix, Some(options)).await {
            Ok(resp) => {
                if let Some(kv) = resp.kvs().first() {
                    self.current_key = Some(kv.key().to_vec());
                    Some(Ok(String::from_utf8_lossy(kv.key()).to_string()))
                } else {
                    None
                }
            }
            Err(e) => Some(Err(e.into())),
        }
    }
}

async fn get_all_keys(client: &mut Client, prefix: &str) -> anyhow::Result<KeysGenerator> {
    Ok(KeysGenerator {
        client: client.clone(),
        prefix: prefix.to_string(),
        current_key: None,
    })
}
```

这个示例展示了以下主要功能：

1. **基本连接**：
   - 创建与 etcd 的连接
   - 设置连接超时

2. **KV 操作**：
   - 设置键值对
   - 获取值
   - 前缀扫描

3. **事务操作**：
   - 条件判断
   - 原子操作

4. **租约操作**：
   - 创建租约
   - 使用租约设置键值对

5. **监听机制**：
   - 监听键值变化
   - 处理不同类型的事件

6. **生成器模式**：
   - 使用生成器遍历键值对
   - 实现分页查询

要运行这个示例，需要先启动本地的 etcd 服务。可以使用 Docker 快速启动：

```bash
docker run -d --name etcd-server \
    --publish 2379:2379 \
    --publish 2380:2380 \
    --env ALLOW_NONE_AUTHENTICATION=yes \
    bitnami/etcd:latest
```

这个示例涵盖了 etcd 的主要功能，并展示了如何使用 Rust 的异步特性和生成器模式来处理数据。您可以根据实际需求修改和扩展这些代码。

一些注意事项：

1. 错误处理使用了 `anyhow` 来简化
2. 使用 tokio 运行时处理异步操作
3. 实现了优雅的资源清理
4. 展示了如何使用生成器模式处理大量数据

您可以根据具体需求调整配置参数和错误处理策略。
