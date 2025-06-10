# 基于 Rust 2024 + Generator 的 GraphQL API 与多数据库集成项目

## 目录

- [基于 Rust 2024 + Generator 的 GraphQL API 与多数据库集成项目](#基于-rust-2024--generator-的-graphql-api-与多数据库集成项目)
  - [目录](#目录)
  - [1. 项目配置](#1-项目配置)
  - [2. GraphQL Schema 生成器](#2-graphql-schema-生成器)
  - [3. 数据库模型生成器](#3-数据库模型生成器)
  - [4. 查询解析器生成器](#4-查询解析器生成器)
  - [5. 数据库连接池管理器](#5-数据库连接池管理器)
  - [6. 实体关系管理器](#6-实体关系管理器)
  - [7. 使用示例](#7-使用示例)
  - [1.  项目配置](#1--项目配置)
  - [2. 数据模型定义](#2-数据模型定义)
  - [3. 数据库连接管理器](#3-数据库连接管理器)
  - [4. GraphQL 查询解析器](#4-graphql-查询解析器)
  - [5. GraphQL 变更解析器](#5-graphql-变更解析器)
  - [6. 数据库迁移生成器](#6-数据库迁移生成器)
  - [7.  使用示例](#7--使用示例)

## 1. 项目配置

```toml
[dependencies]
# GraphQL 依赖
async-graphql = "7.0"
async-graphql-actix-web = "7.0"

# 数据库驱动
sqlx = { version = "0.7", features = ["runtime-tokio-rustls", "mysql", "postgres", "sqlite", "json"] }

# 异步运行时
tokio = { version = "1.0", features = ["full"] }
async-stream = "0.3"

# 工具库
serde = { version = "1.0", features = ["derive"] }
tracing = "0.1"
thiserror = "1.0"
```

## 2. GraphQL Schema 生成器

```rust
use async_graphql::*;
use std::pin::Pin;

/// GraphQL Schema 生成器
pub struct SchemaGenerator {
    entities: Vec<Entity>,
    relationships: Vec<Relationship>,
}

/// 实体定义
#[derive(Debug, Clone)]
pub struct Entity {
    name: String,
    fields: Vec<Field>,
    directives: Vec<Directive>,
}

/// 字段定义
#[derive(Debug, Clone)]
pub struct Field {
    name: String,
    field_type: FieldType,
    is_nullable: bool,
    directives: Vec<Directive>,
}

impl SchemaGenerator {
    /// 生成 GraphQL schema
    pub fn generate_schema(&self) -> impl Stream<Item = Result<String>> {
        try_stream! {
            // 生成类型定义
            for entity in &self.entities {
                let type_def = self.generate_type(entity)?;
                yield type_def;
            }

            // 生成查询定义
            let query_def = self.generate_query_type()?;
            yield query_def;

            // 生成变更定义
            let mutation_def = self.generate_mutation_type()?;
            yield mutation_def;

            // 生成订阅定义
            let subscription_def = self.generate_subscription_type()?;
            yield subscription_def;
        }
    }

    /// 生成类型定义
    fn generate_type(&self, entity: &Entity) -> Result<String> {
        let mut type_def = format!("type {} {{\n", entity.name);
        
        // 生成字段定义
        for field in &entity.fields {
            let field_def = format!(
                "  {}: {}{}\n",
                field.name,
                field.field_type.to_string(),
                if field.is_nullable { "" } else { "!" }
            );
            type_def.push_str(&field_def);
        }

        type_def.push_str("}\n");
        Ok(type_def)
    }

    /// 生成查询类型
    fn generate_query_type(&self) -> Result<String> {
        try_stream! {
            let mut query_def = String::from("type Query {\n");

            // 为每个实体生成查询方法
            for entity in &self.entities {
                // 获取单个实体
                query_def.push_str(&format!(
                    "  get{}(id: ID!): {}\n",
                    entity.name,
                    entity.name
                ));

                // 获取实体列表
                query_def.push_str(&format!(
                    "  list{}(limit: Int, offset: Int): [{}!]!\n",
                    entity.name,
                    entity.name
                ));

                // 搜索实体
                query_def.push_str(&format!(
                    "  search{}(query: String!): [{}!]!\n",
                    entity.name,
                    entity.name
                ));
            }

            query_def.push_str("}\n");
            yield query_def;
        }
    }
}
```

## 3. 数据库模型生成器

```rust
/// 数据库模型生成器
pub struct DatabaseModelGenerator {
    entities: Vec<Entity>,
    db_type: DatabaseType,
}

#[derive(Debug, Clone)]
pub enum DatabaseType {
    MySQL,
    Postgres,
    SQLite,
}

impl DatabaseModelGenerator {
    /// 生成数据库模型
    pub fn generate_models(&self) -> impl Stream<Item = Result<String>> {
        try_stream! {
            for entity in &self.entities {
                // 生成表定义
                let table_def = self.generate_table_definition(entity)?;
                yield table_def;

                // 生成模型结构体
                let model_def = self.generate_model_struct(entity)?;
                yield model_def;

                // 生成 CRUD 实现
                let crud_impl = self.generate_crud_implementation(entity)?;
                yield crud_impl;
            }
        }
    }

    /// 生成表定义
    fn generate_table_definition(&self, entity: &Entity) -> Result<String> {
        let sql = match self.db_type {
            DatabaseType::MySQL => {
                format!(
                    "CREATE TABLE IF NOT EXISTS {} (\n  {}\n);",
                    entity.name,
                    self.generate_mysql_columns(entity)?
                )
            }
            DatabaseType::Postgres => {
                format!(
                    "CREATE TABLE IF NOT EXISTS {} (\n  {}\n);",
                    entity.name,
                    self.generate_postgres_columns(entity)?
                )
            }
            DatabaseType::SQLite => {
                format!(
                    "CREATE TABLE IF NOT EXISTS {} (\n  {}\n);",
                    entity.name,
                    self.generate_sqlite_columns(entity)?
                )
            }
        };
        Ok(sql)
    }

    /// 生成模型结构体
    fn generate_model_struct(&self, entity: &Entity) -> Result<String> {
        try_stream! {
            let mut struct_def = format!("#[derive(Debug, Clone, sqlx::FromRow)]\n");
            struct_def.push_str(&format!("pub struct {} {{\n", entity.name));

            for field in &entity.fields {
                struct_def.push_str(&format!(
                    "    pub {}: {},\n",
                    field.name,
                    self.map_field_type(&field.field_type)?
                ));
            }

            struct_def.push_str("}\n");
            yield struct_def;
        }
    }

    /// 生成 CRUD 实现
    fn generate_crud_implementation(&self, entity: &Entity) -> Result<String> {
        try_stream! {
            let impl_def = format!(
                "impl {} {{\n",
                entity.name
            );

            // 创建方法
            let create_method = self.generate_create_method(entity)?;
            yield create_method;

            // 读取方法
            let read_method = self.generate_read_method(entity)?;
            yield read_method;

            // 更新方法
            let update_method = self.generate_update_method(entity)?;
            yield update_method;

            // 删除方法
            let delete_method = self.generate_delete_method(entity)?;
            yield delete_method;

            impl_def.push_str("}\n");
            yield impl_def;
        }
    }
}
```

## 4. 查询解析器生成器

```rust
/// 查询解析器生成器
pub struct QueryResolverGenerator<'a> {
    schema: &'a Schema,
    db_pool: Pool<Any>,
}

impl<'a> QueryResolverGenerator<'a> {
    /// 生成查询解析器
    pub fn generate_resolvers(&self) -> impl Stream<Item = Result<QueryResolver>> {
        try_stream! {
            for type_def in self.schema.types() {
                match type_def {
                    // 生成对象类型解析器
                    TypeDefinition::Object(obj_type) => {
                        let resolver = self.generate_object_resolver(obj_type)?;
                        yield resolver;
                    }
                    // 生成接口类型解析器
                    TypeDefinition::Interface(interface_type) => {
                        let resolver = self.generate_interface_resolver(interface_type)?;
                        yield resolver;
                    }
                    // 生成联合类型解析器
                    TypeDefinition::Union(union_type) => {
                        let resolver = self.generate_union_resolver(union_type)?;
                        yield resolver;
                    }
                }
            }
        }
    }

    /// 生成对象解析器
    fn generate_object_resolver(&self, obj_type: &ObjectType) -> Result<QueryResolver> {
        try_stream! {
            let mut resolver = QueryResolver::new(obj_type.name.clone());

            // 生成字段解析器
            for field in &obj_type.fields {
                let field_resolver = self.generate_field_resolver(field)?;
                resolver.add_field_resolver(field_resolver);
                yield resolver.clone();
            }

            // 生成关系解析器
            for relation in &obj_type.relationships {
                let relation_resolver = self.generate_relation_resolver(relation)?;
                resolver.add_relation_resolver(relation_resolver);
                yield resolver.clone();
            }
        }
    }

    /// 生成字段解析器
    fn generate_field_resolver(&self, field: &Field) -> Result<FieldResolver> {
        try_stream! {
            let resolver = match field.field_type {
                // 标量类型解析器
                FieldType::Scalar(scalar_type) => {
                    self.generate_scalar_resolver(field, scalar_type)?
                }
                // 对象类型解析器
                FieldType::Object(object_type) => {
                    self.generate_object_field_resolver(field, object_type)?
                }
                // 列表类型解析器
                FieldType::List(list_type) => {
                    self.generate_list_resolver(field, list_type)?
                }
            };
            yield resolver;
        }
    }
}
```

## 5. 数据库连接池管理器

```rust
/// 数据库连接池管理器
pub struct DatabasePoolManager {
    mysql_pool: Option<Pool<MySql>>,
    postgres_pool: Option<Pool<Postgres>>,
    sqlite_pool: Option<Pool<Sqlite>>,
}

impl DatabasePoolManager {
    /// 创建新的连接池管理器
    pub async fn new() -> Result<Self> {
        Ok(Self {
            mysql_pool: None,
            postgres_pool: None,
            sqlite_pool: None,
        })
    }

    /// 初始化 MySQL 连接池
    pub async fn init_mysql(&mut self, url: &str) -> Result<()> {
        let pool = MySqlPoolOptions::new()
            .max_connections(5)
            .connect(url)
            .await?;
        self.mysql_pool = Some(pool);
        Ok(())
    }

    /// 初始化 PostgreSQL 连接池
    pub async fn init_postgres(&mut self, url: &str) -> Result<()> {
        let pool = PgPoolOptions::new()
            .max_connections(5)
            .connect(url)
            .await?;
        self.postgres_pool = Some(pool);
        Ok(())
    }

    /// 初始化 SQLite 连接池
    pub async fn init_sqlite(&mut self, url: &str) -> Result<()> {
        let pool = SqlitePoolOptions::new()
            .max_connections(5)
            .connect(url)
            .await?;
        self.sqlite_pool = Some(pool);
        Ok(())
    }

    /// 获取数据库连接生成器
    pub fn get_connection(&self, db_type: DatabaseType) -> impl Stream<Item = Result<DatabaseConnection>> {
        try_stream! {
            match db_type {
                DatabaseType::MySQL => {
                    if let Some(pool) = &self.mysql_pool {
                        let conn = pool.acquire().await?;
                        yield DatabaseConnection::MySQL(conn);
                    }
                }
                DatabaseType::Postgres => {
                    if let Some(pool) = &self.postgres_pool {
                        let conn = pool.acquire().await?;
                        yield DatabaseConnection::Postgres(conn);
                    }
                }
                DatabaseType::SQLite => {
                    if let Some(pool) = &self.sqlite_pool {
                        let conn = pool.acquire().await?;
                        yield DatabaseConnection::SQLite(conn);
                    }
                }
            }
        }
    }
}
```

## 6. 实体关系管理器

```rust
/// 实体关系管理器
pub struct EntityRelationManager {
    relationships: HashMap<String, Vec<Relationship>>,
}

impl EntityRelationManager {
    /// 生成关系查询
    pub fn generate_relation_queries(&self) -> impl Stream<Item = Result<String>> {
        try_stream! {
            for (entity_name, relationships) in &self.relationships {
                for relationship in relationships {
                    match relationship.relation_type {
                        RelationType::OneToOne => {
                            let query = self.generate_one_to_one_query(entity_name, relationship)?;
                            yield query;
                        }
                        RelationType::OneToMany => {
                            let query = self.generate_one_to_many_query(entity_name, relationship)?;
                            yield query;
                        }
                        RelationType::ManyToMany => {
                            let query = self.generate_many_to_many_query(entity_name, relationship)?;
                            yield query;
                        }
                    }
                }
            }
        }
    }

    /// 生成一对一关系查询
    fn generate_one_to_one_query(&self, entity_name: &str, relationship: &Relationship) -> Result<String> {
        let sql = format!(
            "SELECT r.* FROM {} r
             JOIN {} e ON e.{} = r.{}
             WHERE e.id = $1",
            relationship.target_entity,
            entity_name,
            relationship.foreign_key,
            relationship.target_key
        );
        Ok(sql)
    }
}
```

## 7. 使用示例

```rust
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化数据库连接池
    let mut pool_manager = DatabasePoolManager::new().await?;
    
    pool_manager.init_mysql("mysql://user:pass@localhost/db").await?;
    pool_manager.init_postgres("postgres://user:pass@localhost/db").await?;
    pool_manager.init_sqlite("sqlite://local.db").await?;

    // 创建 Schema 生成器
    let schema_gen = SchemaGenerator::new(vec![
        Entity {
            name: "User".to_string(),
            fields: vec![
                Field {
                    name: "id".to_string(),
                    field_type: FieldType::ID,
                    is_nullable: false,
                },
                Field {
                    name: "name".to_string(),
                    field_type: FieldType::String,
                    is_nullable: false,
                },
                Field {
                    name: "email".to_string(),
                    field_type: FieldType::String,
                    is_nullable: false,
                },
            ],
            directives: vec![],
        },
        Entity {
            name: "Post".to_string(),
            fields: vec![
                Field {
                    name: "id".to_string(),
                    field_type: FieldType::ID,
                    is_nullable: false,
                },
                Field {
                    name: "title".to_string(),
                    field_type: FieldType::String,
                    is_nullable: false,
                },
                Field {
                    name: "content".to_string(),
                    field_type: FieldType::String,
                    is_nullable: false,
                },
                Field {
                    name: "author_id".to_string(),
                    field_type: FieldType::ID,
                    is_nullable: false,
                },
            ],
            directives: vec![],
        },
    ]);

    // 生成 GraphQL schema
    let mut schema_stream = schema_gen.generate_schema();
    while let Some(schema_part) = schema_stream.next().await {
        println!("Generated schema part: {}", schema_part?);
    }

    // 生成数据库模型
    let model_gen = DatabaseModelGenerator::new(
        schema_gen.entities.clone(),
        DatabaseType::Postgres,
    );

    let mut model_stream = model_gen.generate_models();
    while let Some(model) = model_stream.next().await {
        println!("Generated model: {}", model?);
    }

    // 创建查询解析器
    let resolver_gen = QueryResolverGenerator::new(&schema, pool_manager);
    let mut resolver_stream = resolver_gen.generate_resolvers();
    
    while let Some(resolver) = resolver_stream.next().await {
        println!("Generated resolver: {:?}", resolver?);
    }

    // 执行查询示例
    let query = "
        query {
            getUser(id: \"1\") {
                id
                name
                email
                posts {
                    id
                    title
                }
            }
        }
    ";

    let schema = Schema::new(
        QueryRoot,
        MutationRoot,
        EmptySubscription,
    );

    let res = schema.execute(query).await;
    println!("Query result: {:?}", res);

    Ok(())
}
```

这个实现提供了：

1. GraphQL 支持：
   - Schema 生成
   - 解析器生成
   - 查询处理

2. 数据库支持：
   - MySQL
   - PostgreSQL
   - SQLite
   - 连接池管理

3. 代码生成：
   - 模型生成
   - 查询生成
   - 关系映射

4. 高级特性：
   - 实体关系
   - 连接池
   - 查询优化

这个系统可以用于构建：

- API 服务器
- 数据查询服务
- 后端系统
- 数据管理平台

所有实现都使用了 Rust 的生成器特性，提供了灵活和高效的代码生成和查询处理能力。

我将为您展示一个完整的 Rust 2024 GraphQL API 实现，支持关系型数据库的 JSON 类型和 NoSQL 数据库。

## 1.  项目配置

```toml
[dependencies]
# GraphQL 相关
async-graphql = { version = "7.0", features = ["chrono", "json"] }
async-graphql-actix-web = "7.0"

# 数据库驱动
sqlx = { version = "0.7", features = ["runtime-tokio-rustls", "mysql", "postgres", "sqlite", "json", "chrono"] }
mongodb = "2.8"
redis = { version = "0.24", features = ["tokio-comp", "json"] }

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# 异步运行时
tokio = { version = "1.0", features = ["full"] }
async-stream = "0.3"

# 工具库
chrono = { version = "0.4", features = ["serde"] }
tracing = "0.1"
```

## 2. 数据模型定义

```rust
use serde::{Deserialize, Serialize};
use async_graphql::*;
use sqlx::types::JsonValue;

/// 用户模型
#[derive(Debug, Clone, Serialize, Deserialize, SimpleObject)]
pub struct User {
    id: String,
    name: String,
    email: String,
    #[graphql(skip)]
    password_hash: String,
    // JSON 类型字段
    #[graphql(name = "profile")]
    profile_data: JsonValue,
    // MongoDB 专用字段
    #[graphql(name = "settings")]
    settings_data: Option<mongodb::bson::Document>,
    created_at: chrono::DateTime<chrono::Utc>,
    updated_at: chrono::DateTime<chrono::Utc>,
}

/// 文章模型
#[derive(Debug, Clone, Serialize, Deserialize, SimpleObject)]
pub struct Post {
    id: String,
    title: String,
    content: String,
    author_id: String,
    // JSON 类型的元数据
    #[graphql(name = "metadata")]
    metadata_json: JsonValue,
    tags: Vec<String>,
    status: PostStatus,
    created_at: chrono::DateTime<chrono::Utc>,
    updated_at: chrono::DateTime<chrono::Utc>,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, Enum)]
pub enum PostStatus {
    Draft,
    Published,
    Archived,
}
```

## 3. 数据库连接管理器

```rust
use std::sync::Arc;

/// 统一数据库连接管理器
pub struct DatabaseManager {
    mysql_pool: Option<sqlx::MySqlPool>,
    pg_pool: Option<sqlx::PgPool>,
    sqlite_pool: Option<sqlx::SqlitePool>,
    mongo_client: Option<mongodb::Client>,
    redis_client: Option<redis::Client>,
}

impl DatabaseManager {
    /// 创建数据库连接生成器
    pub fn connection_generator(&self) -> impl Stream<Item = Result<DatabaseConnection, Error>> {
        try_stream! {
            // MySQL 连接
            if let Some(pool) = &self.mysql_pool {
                let conn = pool.acquire().await?;
                yield DatabaseConnection::MySQL(conn);
            }

            // PostgreSQL 连接
            if let Some(pool) = &self.pg_pool {
                let conn = pool.acquire().await?;
                yield DatabaseConnection::Postgres(conn);
            }

            // SQLite 连接
            if let Some(pool) = &self.sqlite_pool {
                let conn = pool.acquire().await?;
                yield DatabaseConnection::SQLite(conn);
            }

            // MongoDB 连接
            if let Some(client) = &self.mongo_client {
                yield DatabaseConnection::MongoDB(client.clone());
            }

            // Redis 连接
            if let Some(client) = &self.redis_client {
                let conn = client.get_async_connection().await?;
                yield DatabaseConnection::Redis(conn);
            }
        }
    }

    /// JSON 查询生成器
    pub fn json_query_generator<T>(&self) -> impl Stream<Item = Result<T, Error>>
    where
        T: serde::de::DeserializeOwned,
    {
        try_stream! {
            match &self.pg_pool {
                Some(pool) => {
                    // PostgreSQL JSONB 查询
                    let rows = sqlx::query!(
                        "SELECT data FROM json_data WHERE type = $1",
                        "user_profile"
                    )
                    .fetch_all(pool)
                    .await?;

                    for row in rows {
                        let data: T = serde_json::from_value(row.data)?;
                        yield data;
                    }
                }
                None => {}
            }

            // MongoDB JSON 查询
            if let Some(client) = &self.mongo_client {
                let db = client.database("app");
                let collection = db.collection::<mongodb::bson::Document>("json_data");
                
                let mut cursor = collection.find(None, None).await?;
                while let Some(doc) = cursor.next().await {
                    let data: T = mongodb::bson::from_document(doc?)?;
                    yield data;
                }
            }
        }
    }
}
```

## 4. GraphQL 查询解析器

```rust
use async_graphql::*;

pub struct QueryRoot;

#[Object]
impl QueryRoot {
    /// 用户查询解析器
    async fn user(&self, ctx: &Context<'_>, id: ID) -> Result<Option<User>> {
        let db = ctx.data::<Arc<DatabaseManager>>()?;
        
        // 使用生成器查询用户数据
        let mut user_gen = try_stream! {
            // 关系型数据库查询
            let sql_result = sqlx::query_as!(
                UserRow,
                "SELECT * FROM users WHERE id = $1",
                id.as_str()
            )
            .fetch_optional(db.pg_pool.as_ref().unwrap())
            .await?;

            if let Some(row) = sql_result {
                yield User::from(row);
            }

            // MongoDB 查询
            if let Some(client) = &db.mongo_client {
                let users = client.database("app").collection("users");
                if let Some(doc) = users.find_one(
                    doc! { "_id": id.as_str() },
                    None
                ).await? {
                    yield User::from_document(doc)?;
                }
            }

            // Redis 缓存查询
            if let Some(client) = &db.redis_client {
                let mut conn = client.get_async_connection().await?;
                if let Some(data) = conn.get::<_, String>(format!("user:{}", id)).await? {
                    yield serde_json::from_str(&data)?;
                }
            }
        };

        while let Some(user) = user_gen.next().await {
            return Ok(Some(user?));
        }

        Ok(None)
    }

    /// 文章查询解析器
    async fn posts(
        &self,
        ctx: &Context<'_>,
        filter: Option<PostFilter>,
        limit: Option<i32>,
        offset: Option<i32>,
    ) -> Result<Vec<Post>> {
        let db = ctx.data::<Arc<DatabaseManager>>()?;
        
        // 使用生成器查询文章列表
        let mut posts_gen = try_stream! {
            let limit = limit.unwrap_or(10) as i64;
            let offset = offset.unwrap_or(0) as i64;

            // PostgreSQL JSON 查询
            if let Some(pool) = &db.pg_pool {
                let rows = sqlx::query!(
                    r#"
                    SELECT p.*, 
                           p.metadata::jsonb as "metadata!",
                           u.name as author_name
                    FROM posts p
                    JOIN users u ON p.author_id = u.id
                    WHERE ($1::jsonb IS NULL OR p.metadata @> $1)
                    LIMIT $2 OFFSET $3
                    "#,
                    filter.map(|f| serde_json::to_value(f).ok()).unwrap_or_default(),
                    limit,
                    offset
                )
                .fetch_all(pool)
                .await?;

                for row in rows {
                    yield Post::from_row(row)?;
                }
            }

            // MongoDB 聚合查询
            if let Some(client) = &db.mongo_client {
                let posts = client.database("app").collection("posts");
                let mut cursor = posts.aggregate(vec![
                    doc! {
                        "$match": filter.map(|f| bson::to_document(&f).unwrap())
                                      .unwrap_or_else(|| doc! {})
                    },
                    doc! {
                        "$skip": offset
                    },
                    doc! {
                        "$limit": limit
                    }
                ], None).await?;

                while let Some(doc) = cursor.next().await {
                    yield Post::from_document(doc?)?;
                }
            }
        };

        let mut posts = Vec::new();
        while let Some(post) = posts_gen.next().await {
            posts.push(post?);
        }

        Ok(posts)
    }
}
```

## 5. GraphQL 变更解析器

```rust
pub struct MutationRoot;

#[Object]
impl MutationRoot {
    /// 创建用户变更解析器
    async fn create_user(&self, ctx: &Context<'_>, input: CreateUserInput) -> Result<User> {
        let db = ctx.data::<Arc<DatabaseManager>>()?;
        
        // 使用生成器处理用户创建
        let mut create_gen = try_stream! {
            let user = User::new(input);

            // 保存到 PostgreSQL
            if let Some(pool) = &db.pg_pool {
                sqlx::query!(
                    r#"
                    INSERT INTO users (id, name, email, password_hash, profile, created_at, updated_at)
                    VALUES ($1, $2, $3, $4, $5, $6, $7)
                    "#,
                    user.id,
                    user.name,
                    user.email,
                    user.password_hash,
                    serde_json::to_value(&user.profile_data)?,
                    user.created_at,
                    user.updated_at
                )
                .execute(pool)
                .await?;
            }

            // 保存到 MongoDB
            if let Some(client) = &db.mongo_client {
                let users = client.database("app").collection("users");
                users.insert_one(user.to_document()?, None).await?;
            }

            // 缓存到 Redis
            if let Some(client) = &db.redis_client {
                let mut conn = client.get_async_connection().await?;
                let key = format!("user:{}", user.id);
                conn.set_ex(key, serde_json::to_string(&user)?, 3600).await?;
            }

            yield user;
        };

        while let Some(user) = create_gen.next().await {
            return Ok(user?);
        }

        Err("Failed to create user".into())
    }

    /// 更新文章变更解析器
    async fn update_post(&self, ctx: &Context<'_>, id: ID, input: UpdatePostInput) -> Result<Post> {
        let db = ctx.data::<Arc<DatabaseManager>>()?;
        
        // 使用生成器处理文章更新
        let mut update_gen = try_stream! {
            // 更新 PostgreSQL
            if let Some(pool) = &db.pg_pool {
                let row = sqlx::query!(
                    r#"
                    UPDATE posts
                    SET title = COALESCE($1, title),
                        content = COALESCE($2, content),
                        metadata = metadata || $3::jsonb,
                        updated_at = $4
                    WHERE id = $5
                    RETURNING *
                    "#,
                    input.title,
                    input.content,
                    serde_json::to_value(&input.metadata)?,
                    chrono::Utc::now(),
                    id.as_str()
                )
                .fetch_one(pool)
                .await?;

                yield Post::from_row(row)?;
            }

            // 更新 MongoDB
            if let Some(client) = &db.mongo_client {
                let posts = client.database("app").collection("posts");
                let update = doc! {
                    "$set": {
                        "title": input.title,
                        "content": input.content,
                        "metadata": bson::to_bson(&input.metadata)?,
                        "updated_at": chrono::Utc::now()
                    }
                };
                
                posts.update_one(
                    doc! { "_id": id.as_str() },
                    update,
                    None
                ).await?;

                if let Some(doc) = posts.find_one(
                    doc! { "_id": id.as_str() },
                    None
                ).await? {
                    yield Post::from_document(doc)?;
                }
            }
        };

        while let Some(post) = update_gen.next().await {
            return Ok(post?);
        }

        Err("Post not found".into())
    }
}
```

## 6. 数据库迁移生成器

```rust
pub struct DatabaseMigrationGenerator {
    db_manager: Arc<DatabaseManager>,
}

impl DatabaseMigrationGenerator {
    /// 生成数据库迁移
    pub fn generate_migrations(&self) -> impl Stream<Item = Result<(), Error>> {
        try_stream! {
            // PostgreSQL 迁移
            if let Some(pool) = &self.db_manager.pg_pool {
                // 创建用户表
                sqlx::query(
                    r#"
                    CREATE TABLE IF NOT EXISTS users (
                        id TEXT PRIMARY KEY,
                        name TEXT NOT NULL,
                        email TEXT UNIQUE NOT NULL,
                        password_hash TEXT NOT NULL,
                        profile JSONB DEFAULT '{}',
                        created_at TIMESTAMP WITH TIME ZONE NOT NULL,
                        updated_at TIMESTAMP WITH TIME ZONE NOT NULL
                    )
                    "#
                )
                .execute(pool)
                .await?;

                // 创建文章表
                sqlx::query(
                    r#"
                    CREATE TABLE IF NOT EXISTS posts (
                        id TEXT PRIMARY KEY,
                        title TEXT NOT NULL,
                        content TEXT NOT NULL,
                        author_id TEXT REFERENCES users(id),
                        metadata JSONB DEFAULT '{}',
                        tags TEXT[] DEFAULT '{}',
                        status TEXT NOT NULL,
                        created_at TIMESTAMP WITH TIME ZONE NOT NULL,
                        updated_at TIMESTAMP WITH TIME ZONE NOT NULL
                    )
                    "#
                )
                .execute(pool)
                .await?;

                yield ();
            }

            // MongoDB 索引
            if let Some(client) = &self.db_manager.mongo_client {
                let db = client.database("app");
                
                // 用户集合索引
                db.collection("users")
                    .create_index(
                        mongodb::IndexModel::builder()
                            .keys(doc! { "email": 1 })
                            .options(Some(mongodb::options::IndexOptions::builder()
                                .unique(true)
                                .build()))
                            .build(),
                        None
                    )
                    .await?;

                // 文章集合索引
                db.collection("posts")
                    .create_index(
                        mongodb::IndexModel::builder()
                            .keys(doc! { 
                                "author_id": 1,
                                "created_at": -1
                            })
                            .build(),
                        None
                    )
                    .await?;

                yield ();
            }
        }
    }
}
```

## 7.  使用示例

```rust
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化数据库管理器
    let db_manager = Arc::new(DatabaseManager::new(
        "postgresql://localhost/app",
        "mongodb://localhost:27017",
        "redis://localhost",
    ).await?);

    // 运行数据库迁移
    let migration_gen = DatabaseMigrationGenerator::new(db_manager.clone());
    let mut migrations = migration_gen.generate_migrations();
    
    while let Some(result) = migrations.next().await {
        println!("Migration result: {:?}", result);
    }

    // 创建 GraphQL schema
    let schema = Schema::build(QueryRoot, MutationRoot, EmptySubscription)
        .data(db_manager)
        .finish();

    // 示例查询
    let query = r#"
        query {
            user(id: "1") {
                id
                name
                email
                profile
                posts {
                    id
                    title
                    content
                    metadata
                }
            }
        }
    "#;

    let res = schema.execute(query).await;
    println!("Query result: {:#?}", res);

    // 示例变更
    let mutation = r#"
        mutation {
            createUser(input: {
                name: "John Doe",
                email: "john@example.com",
                password: "secret",
                profile: {
                    age: 30,
                    location: "New York"
                }
            }) {
                id
                name
                email
                profile
            }
        }
    "#;

    let res = schema.execute(mutation).await;
    println!("Mutation result: {:#?}", res);

    Ok(())
}
```

这个实现提供了：

1. 数据库支持：
   - PostgreSQL (带 JSONB)
   - MongoDB
   - Redis
   - SQLite

2. GraphQL 功能：
   - 查询解析器
   - 变更解析器
   - JSON 字段支持
   - 过滤和分页

3. 生成器特性：
   - 数据库连接管理
   - 查询生成
   - 迁移生成

4. 高级特性：
   - JSON 查询
   - 缓存集成
   - 数据库迁移
   - 索引管理

这个系统适用于：

- 现代 Web API
- 数据密集型应用
- 微服务架构
- 实时数据处理

所有实现都使用了 Rust 2024 的生成器特性，提供了高效的异步数据处理能力。
