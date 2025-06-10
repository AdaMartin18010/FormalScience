# SQLite 数据库集成

下面介绍两种常用方式，将 SQLite 集成到 Rust 应用中：
使用同步的 [rusqlite](https://crates.io/crates/rusqlite)
或使用异步的 [sqlx](https://crates.io/crates/sqlx)。
下面主要以 rusqlite 为例，展示如何集成 SQLite 以及基本的使用方法。

---

## 1. 使用 rusqlite 集成 SQLite

### 1.1 添加依赖

在项目的 `Cargo.toml` 文件中添加 `rusqlite` 依赖：

```toml:Cargo.toml
[dependencies]
rusqlite = "0.29"
```

### 1.2 编写示例代码

下面代码展示了如何打开 SQLite 数据库、创建表、插入数据以及查询数据。代码示例请保存到 `src/main.rs`：

```rust:src/main.rs
use rusqlite::{params, Connection, Result};

fn main() -> Result<()> {
    // 打开一个 SQLite 数据库连接；这里创建了一个名为 test.db 的数据库文件
    let conn = Connection::open("test.db")?;

    // 创建一个简单的用户表，包含 id 和 name 两个字段
    conn.execute(
        "CREATE TABLE IF NOT EXISTS user (
                  id    INTEGER PRIMARY KEY,
                  name  TEXT NOT NULL
              )",
        [],
    )?;

    // 插入一条数据
    let name = "Alice";
    conn.execute("INSERT INTO user (name) VALUES (?1)", params![name])?;

    // 查询数据
    let mut stmt = conn.prepare("SELECT id, name FROM user")?;
    let user_iter = stmt.query_map([], |row| {
        Ok(User {
            id: row.get(0)?,
            name: row.get(1)?,
        })
    })?;

    // 输出查询结果
    for user in user_iter {
        println!("Found user {:?}", user?);
    }

    Ok(())
}

#[derive(Debug)]
struct User {
    id: i32,
    name: String,
}
```

#### 代码说明

- **建立数据库连接**：通过 `Connection::open("test.db")` 打开或创建一个 SQLite 数据库文件。
- **创建表**：使用 SQL 语句创建用户表，确保表不存在时创建（通过 `IF NOT EXISTS`）。
- **插入与查询**：先插入一条记录，再使用查询映射（`query_map`）遍历结果，将每一行映射为一个 `User` 结构体实例，最后输出。

### 1.3 关于 rusqlite 的说明

- **同步访问**：rusqlite 是以同步方式访问 SQLite，适合对响应速度要求不高、以单线程或同步场景下的应用。
- **事务支持**：rusqlite 支持事务，如果需要执行批量插入或保证操作原子性，可使用 `conn.transaction()` 来处理事务。
- **错误管理**：库中对错误做了相应封装，利用 Rust 的 `Result` 类型来返回成功或者出错信息。

---

## 2. 使用 sqlx 集成 SQLite（异步方式）

如果你希望在异步应用（如基于 Tokio 的应用）中使用 SQLite，可以考虑使用 [sqlx](https://crates.io/crates/sqlx)。其使用方法类似，但需要开启对应的 SQLite 功能。

### 2.1 添加依赖

在 `Cargo.toml` 中添加：

```toml:Cargo.toml
[dependencies]
tokio = { version = "1", features = ["full"] }
sqlx = { version = "0.6", features = [ "sqlite", "runtime-tokio-native-tls", "macros" ] }
```

### 2.2 示例代码

下面的代码展示了如何在 Tokio 异步运行环境下使用 sqlx 操作 SQLite 数据库，该示例同样包括创建表、插入和查询数据：

```rust:src/main.rs
use sqlx::sqlite::SqlitePoolOptions;
use sqlx::Row;

#[tokio::main]
async fn main() -> Result<(), sqlx::Error> {
    // 创建数据库连接池, SQLite 使用 file:: 存储数据库文件
    let pool = SqlitePoolOptions::new()
        .max_connections(5)
        .connect("sqlite://test_async.db")
        .await?;

    // 创建表，如果不存在则创建
    sqlx::query(
        "CREATE TABLE IF NOT EXISTS user (
              id    INTEGER PRIMARY KEY,
              name  TEXT NOT NULL
        )",
    )
    .execute(&pool)
    .await?;

    // 插入一条记录
    let name = "Bob";
    sqlx::query("INSERT INTO user (name) VALUES (?)")
        .bind(name)
        .execute(&pool)
        .await?;

    // 查询并输出数据
    let rows = sqlx::query("SELECT id, name FROM user")
        .fetch_all(&pool)
        .await?;

    for row in rows {
        let id: i32 = row.get("id");
        let name: String = row.get("name");
        println!("Found user: id={}, name={}", id, name);
    }

    Ok(())
}
```

#### *代码说明*

- **异步连接池**：我们使用 `SqlitePoolOptions` 创建一个连接池，这样能提高并发情况下数据库的访问效率。
- **异步执行查询**：所有操作都以异步方式执行，适合在高并发或者异步环境下使用。

---

## *小结*

- 对于同步场景：推荐使用 [rusqlite](https://crates.io/crates/rusqlite)，简单易用，适合大多数桌面或服务端应用。
- 对于异步场景：可以使用 [sqlx](https://crates.io/crates/sqlx) 集成 SQLite，配合 Tokio 等异步运行时构建高性能应用。

两种方式各有侧重，开发者可根据自己的业务场景选择合适的方案来集成 SQLite 到 Rust 项目中。
