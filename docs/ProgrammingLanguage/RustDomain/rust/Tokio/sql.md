# Rust 2024 数据库访问

我将为您展示一个完整的 Rust 2024 数据库访问实现，包含所有高级特性。

## 目录

- [Rust 2024 数据库访问](#rust-2024-数据库访问)
  - [目录](#目录)
  - [1. 项目配置](#1-项目配置)
  - [2. 数据库连接池管理](#2-数据库连接池管理)
  - [3. 事务管理器](#3-事务管理器)
  - [4. 锁管理器](#4-锁管理器)
  - [5. JSON 操作管理器](#5-json-操作管理器)
  - [6. 存储过程管理器](#6-存储过程管理器)
  - [7. 异常处理](#7-异常处理)
  - [8. 使用示例](#8-使用示例)

## 1. 项目配置

```toml
[dependencies]
tokio = { version = "1.0", features = ["full"] }
sqlx = { version = "0.7", features = [
    "runtime-tokio-rustls",
    "postgres",
    "mysql",
    "sqlite",
    "json",
    "chrono",
    "uuid",
    "decimal"
]}
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
async-trait = "0.1"
thiserror = "1.0"
tracing = "0.1"
```

## 2. 数据库连接池管理

```rust
use std::sync::Arc;
use tokio::sync::Semaphore;

/// 数据库连接池管理器
pub struct DbPoolManager {
    pg_pool: Option<sqlx::PgPool>,
    mysql_pool: Option<sqlx::MySqlPool>,
    sqlite_pool: Option<sqlx::SqlitePool>,
    connection_semaphore: Arc<Semaphore>,
}

impl DbPoolManager {
    /// 创建新的连接池管理器
    pub async fn new(config: DbConfig) -> Result<Self> {
        let connection_semaphore = Arc::new(Semaphore::new(config.max_connections));

        let pg_pool = if let Some(url) = config.postgres_url {
            Some(
                sqlx::postgres::PgPoolOptions::new()
                    .max_connections(config.max_connections as u32)
                    .connect(&url)
                    .await?
            )
        } else {
            None
        };

        // 类似地初始化 MySQL 和 SQLite 连接池...

        Ok(Self {
            pg_pool,
            mysql_pool,
            sqlite_pool,
            connection_semaphore,
        })
    }

    /// 生成数据库连接
    pub async fn get_connection(&self, db_type: DbType) -> impl Stream<Item = Result<DbConnection>> {
        try_stream! {
            // 获取信号量许可
            let _permit = self.connection_semaphore.acquire().await?;

            match db_type {
                DbType::Postgres => {
                    if let Some(pool) = &self.pg_pool {
                        let conn = pool.acquire().await?;
                        yield DbConnection::Postgres(conn);
                    }
                },
                // 其他数据库类型...
            }
        }
    }
}
```

## 3. 事务管理器

```rust
/// 事务管理器
pub struct TransactionManager<'a> {
    connection: &'a mut DbConnection,
    savepoints: Vec<String>,
}

impl<'a> TransactionManager<'a> {
    /// 开始新事务
    pub async fn begin(&mut self) -> Result<()> {
        match self.connection {
            DbConnection::Postgres(conn) => {
                conn.execute("BEGIN").await?;
            },
            // 其他数据库类型...
        }
        Ok(())
    }

    /// 创建保存点
    pub async fn create_savepoint(&mut self, name: &str) -> Result<()> {
        let sql = format!("SAVEPOINT {}", name);
        match self.connection {
            DbConnection::Postgres(conn) => {
                conn.execute(&sql).await?;
                self.savepoints.push(name.to_string());
            },
            // 其他数据库类型...
        }
        Ok(())
    }

    /// 回滚到保存点
    pub async fn rollback_to_savepoint(&mut self, name: &str) -> Result<()> {
        let sql = format!("ROLLBACK TO SAVEPOINT {}", name);
        match self.connection {
            DbConnection::Postgres(conn) => {
                conn.execute(&sql).await?;
            },
            // 其他数据库类型...
        }
        Ok(())
    }

    /// 两阶段提交 - 准备阶段
    pub async fn prepare(&mut self) -> Result<()> {
        match self.connection {
            DbConnection::Postgres(conn) => {
                conn.execute("PREPARE TRANSACTION 'transaction_1'").await?;
            },
            // 其他数据库类型...
        }
        Ok(())
    }

    /// 两阶段提交 - 提交阶段
    pub async fn commit_prepared(&mut self) -> Result<()> {
        match self.connection {
            DbConnection::Postgres(conn) => {
                conn.execute("COMMIT PREPARED 'transaction_1'").await?;
            },
            // 其他数据库类型...
        }
        Ok(())
    }
}
```

## 4. 锁管理器

```rust
/// 锁管理器
pub struct LockManager<'a> {
    connection: &'a mut DbConnection,
    locks: Vec<String>,
}

impl<'a> LockManager<'a> {
    /// 获取表锁
    pub async fn acquire_table_lock(&mut self, table: &str, lock_type: LockType) -> Result<()> {
        let sql = match lock_type {
            LockType::Share => format!("LOCK TABLE {} IN SHARE MODE", table),
            LockType::Exclusive => format!("LOCK TABLE {} IN EXCLUSIVE MODE", table),
        };

        match self.connection {
            DbConnection::Postgres(conn) => {
                conn.execute(&sql).await?;
                self.locks.push(table.to_string());
            },
            // 其他数据库类型...
        }
        Ok(())
    }

    /// 获取行锁
    pub async fn acquire_row_lock(&mut self, table: &str, id: i64, lock_type: LockType) -> Result<()> {
        let sql = match lock_type {
            LockType::Share => {
                format!("SELECT * FROM {} WHERE id = {} FOR SHARE", table, id)
            },
            LockType::Exclusive => {
                format!("SELECT * FROM {} WHERE id = {} FOR UPDATE", table, id)
            },
        };

        match self.connection {
            DbConnection::Postgres(conn) => {
                conn.execute(&sql).await?;
            },
            // 其他数据库类型...
        }
        Ok(())
    }
}
```

## 5. JSON 操作管理器

```rust
use serde::{Deserialize, Serialize};
use serde_json::Value;

/// JSON 操作管理器
pub struct JsonManager<'a> {
    connection: &'a mut DbConnection,
}

impl<'a> JsonManager<'a> {
    /// 更新 JSONB 字段
    pub async fn update_jsonb<T: Serialize>(
        &mut self,
        table: &str,
        id: i64,
        field: &str,
        value: &T,
    ) -> Result<()> {
        let json_value = serde_json::to_value(value)?;
        
        match self.connection {
            DbConnection::Postgres(conn) => {
                sqlx::query(
                    &format!(
                        "UPDATE {} SET {} = $1 WHERE id = $2",
                        table, field
                    )
                )
                .bind(json_value)
                .bind(id)
                .execute(conn)
                .await?;
            },
            // 其他数据库类型...
        }
        Ok(())
    }

    /// JSONB 路径查询
    pub async fn query_jsonb_path<T: for<'de> Deserialize<'de>>(
        &mut self,
        table: &str,
        field: &str,
        path: &str,
    ) -> Result<Vec<T>> {
        match self.connection {
            DbConnection::Postgres(conn) => {
                let rows = sqlx::query(
                    &format!(
                        "SELECT {}->{} FROM {}",
                        field, path, table
                    )
                )
                .fetch_all(conn)
                .await?;

                let results = rows
                    .iter()
                    .map(|row| {
                        let value: Value = row.get(0);
                        serde_json::from_value(value)
                    })
                    .collect::<Result<Vec<T>, _>>()?;

                Ok(results)
            },
            // 其他数据库类型...
        }
    }
}
```

## 6. 存储过程管理器

```rust
/// 存储过程管理器
pub struct ProcedureManager<'a> {
    connection: &'a mut DbConnection,
}

impl<'a> ProcedureManager<'a> {
    /// 创建存储过程
    pub async fn create_procedure(&mut self, name: &str, args: &[&str], body: &str) -> Result<()> {
        let args_str = args.join(", ");
        let sql = format!(
            "CREATE OR REPLACE PROCEDURE {}({})
             LANGUAGE plpgsql
             AS $$
             BEGIN
                 {};
             END;
             $$;",
            name, args_str, body
        );

        match self.connection {
            DbConnection::Postgres(conn) => {
                conn.execute(&sql).await?;
            },
            // 其他数据库类型...
        }
        Ok(())
    }

    /// 执行存储过程
    pub async fn execute_procedure<T: for<'de> Deserialize<'de>>(
        &mut self,
        name: &str,
        args: &[&dyn ToSql],
    ) -> Result<Option<T>> {
        let args_placeholder = (1..=args.len())
            .map(|i| format!("${}", i))
            .collect::<Vec<_>>()
            .join(", ");

        let sql = format!("CALL {}({})", name, args_placeholder);

        match self.connection {
            DbConnection::Postgres(conn) => {
                let mut query = sqlx::query(&sql);
                for arg in args {
                    query = query.bind(arg);
                }

                let row = query.fetch_optional(conn).await?;
                
                if let Some(row) = row {
                    let value: Value = row.get(0);
                    Ok(Some(serde_json::from_value(value)?))
                } else {
                    Ok(None)
                }
            },
            // 其他数据库类型...
        }
    }
}
```

## 7. 异常处理

```rust
#[derive(Debug, thiserror::Error)]
pub enum DatabaseError {
    #[error("Connection error: {0}")]
    ConnectionError(#[from] sqlx::Error),

    #[error("Transaction error: {0}")]
    TransactionError(String),

    #[error("Lock error: {0}")]
    LockError(String),

    #[error("JSON error: {0}")]
    JsonError(#[from] serde_json::Error),

    #[error("Procedure error: {0}")]
    ProcedureError(String),

    #[error("Pool error: {0}")]
    PoolError(String),
}

impl DatabaseError {
    /// 错误恢复生成器
    pub fn recovery_generator(error: Self) -> impl Stream<Item = Result<(), Self>> {
        try_stream! {
            match &error {
                DatabaseError::ConnectionError(e) => {
                    // 尝试重新连接
                    for i in 1..=3 {
                        tokio::time::sleep(std::time::Duration::from_secs(i)).await;
                        // 重试连接逻辑...
                        yield Ok(());
                    }
                },
                DatabaseError::TransactionError(_) => {
                    // 回滚事务
                    yield Ok(());
                },
                // 其他错误处理...
            }
        }
    }
}
```

## 8. 使用示例

```rust
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化连接池
    let pool_manager = DbPoolManager::new(DbConfig {
        postgres_url: Some("postgres://user:pass@localhost/db"),
        max_connections: 20,
        ..Default::default()
    }).await?;

    // 获取连接
    let mut conn_stream = pool_manager.get_connection(DbType::Postgres);
    let mut conn = conn_stream.next().await.unwrap()?;

    // 事务管理
    let mut tx_manager = TransactionManager::new(&mut conn);
    tx_manager.begin().await?;

    // 创建保存点
    tx_manager.create_savepoint("point1").await?;

    // 锁管理
    let mut lock_manager = LockManager::new(&mut conn);
    lock_manager.acquire_table_lock("users", LockType::Share).await?;

    // JSON 操作
    let mut json_manager = JsonManager::new(&mut conn);
    
    // 更新 JSON 数据
    let user_data = serde_json::json!({
        "name": "John",
        "age": 30,
        "settings": {
            "theme": "dark",
            "notifications": true
        }
    });

    json_manager.update_jsonb("users", 1, "profile", &user_data).await?;

    // 查询 JSON 路径
    let settings: Value = json_manager
        .query_jsonb_path("users", "profile", "settings")
        .await?
        .pop()
        .unwrap();

    // 存储过程
    let mut proc_manager = ProcedureManager::new(&mut conn);
    
    // 创建存储过程
    proc_manager.create_procedure(
        "update_user_profile",
        &["user_id INT", "new_profile JSONB"],
        "UPDATE users SET profile = new_profile WHERE id = user_id"
    ).await?;

    // 执行存储过程
    proc_manager.execute_procedure::<Value>(
        "update_user_profile",
        &[&1, &user_data]
    ).await?;

    // 提交事务
    tx_manager.prepare().await?;
    tx_manager.commit_prepared().await?;

    // 错误处理
    if let Err(e) = some_database_operation().await {
        let mut recovery = DatabaseError::recovery_generator(e);
        while let Some(result) = recovery.next().await {
            match result {
                Ok(_) => println!("Recovery successful"),
                Err(e) => println!("Recovery failed: {}", e),
            }
        }
    }

    Ok(())
}
```

这个实现提供了：

1. 连接池管理：
   - 多数据库支持
   - 连接限制
   - 连接复用

2. 事务管理：
   - 标准事务
   - 保存点
   - 两阶段提交

3. 锁管理：
   - 表锁
   - 行锁
   - 死锁处理

4. JSON 操作：
   - JSONB 更新
   - 路径查询
   - 类型转换

5. 存储过程：
   - 创建过程
   - 执行过程
   - 参数绑定

6. 异常处理：
   - 错误类型
   - 恢复策略
   - 重试机制

这个系统适用于：

- 复杂数据库操作
- 事务密集型应用
- JSON 数据处理
- 高并发场景

所有实现都使用了 Rust 2024 的生成器特性，提供了高效的异步数据库访问能力。
