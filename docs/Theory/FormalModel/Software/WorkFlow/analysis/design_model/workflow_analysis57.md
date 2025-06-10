# 工作流架构 - 阶段一：坚实基础 (Rust 生态版)

好的，我们现在基于 Rust 的生态系统来重新设计“阶段一：坚实基础 (Solid Foundation)”。我们将重点放在利用 Rust 的优势（性能、可靠性、内存安全）以及其生态系统中的常用库和模式。

## 目录

- [工作流架构 - 阶段一：坚实基础 (Rust 生态版)](#工作流架构---阶段一坚实基础-rust-生态版)
  - [目录](#目录)
  - [1. 核心原则](#1-核心原则)
  - [2. 架构概览](#2-架构概览)
    - [架构图 (Mermaid)](#架构图-mermaid)
  - [3. 核心组件设计 (Rust 视角)](#3-核心组件设计-rust-视角)
  - [4. API 与事件契约 (Rust 实现)](#4-api-与事件契约-rust-实现)
  - [5. 可观测性设计 (Rust Crates)](#5-可观测性设计-rust-crates)
  - [6. 基础弹性设计 (Rust 实现)](#6-基础弹性设计-rust-实现)
  - [7. 测试策略 (Rust 工具链)](#7-测试策略-rust-工具链)
  - [8. CI/CD 流水线 (Rust 特点)](#8-cicd-流水线-rust-特点)
  - [9. 关键成功指标](#9-关键成功指标)
  - [10. 思维导图 (Text Format)](#10-思维导图-text-format)

## 1. 核心原则

与通用设计相同，保持不变：

1. **价值驱动 (Value-Driven):** 优先实现核心工作流执行能力和保障系统稳定运行的基本要素。
2. **简单性优先 (Simplicity First - KISS):** 采用成熟、简单、易于理解和运维的技术与模式。避免过早引入复杂性。
3. **渐进主义 (Incrementalism):** 构建可独立部署和测试的模块化组件，为后续阶段的演进打下基础。
4. **务实权衡 (Pragmatic Trade-offs):** 接受合理的权衡，例如在初期可能牺牲部分极致性能来换取开发速度和稳定性。
5. **可观测性基础 (Observability Foundation):** 将可观测性作为一等公民，深度融入系统设计。

---

## 2. 架构概览

整体架构模式不变，依然是基于微服务/SOA思想，通过 API 和事件进行通信。
但技术栈和实现细节将围绕 Rust 生态。

### 架构图 (Mermaid)

```mermaid
graph LR
    subgraph 用户/客户端
        UI(用户界面/API客户端)
    end

    subgraph 系统边界
        GW(API网关 - Nginx/Kong 或 Rust Simple Router)
    end

    subgraph 核心服务 (Rust Services)
        Orchestrator(工作流编排器 - Tokio based)
        Worker(任务执行器 - Tokio based)
        StateStore[(状态存储 - PostgreSQL/MySQL)]
        MQ[(消息队列/事件总线 - RabbitMQ/Kafka/NATS)]
    end

    subgraph 支撑服务
        Logging[(日志聚合 - ELK/Loki)]
        Metrics[(指标监控 - Prometheus/Grafana)]
        Tracing[(分布式追踪 - Jaeger/Tempo)]
        CICD(CI/CD流水线 - GitLab CI/GitHub Actions)
    end

    UI --> GW
    GW --> Orchestrator
    GW --> Worker -- (可选) --
    Orchestrator --> MQ -- 发布任务/事件 --
    Orchestrator --> StateStore -- 读写状态 (sqlx/diesel) --
    Worker -- 监听 --> MQ -- 获取任务 (lapin/rdkafka) --
    Worker --> StateStore -- (可选) 更新状态 --
    Worker --> GW -- (可选) 回调/外部API (reqwest) --

    Orchestrator -- Logs/Metrics/Traces (tracing/metrics/opentelemetry) --> Logging & Metrics & Tracing
    Worker -- Logs/Metrics/Traces --> Logging & Metrics & Tracing
    GW -- Logs/Metrics/Traces --> Logging & Metrics & Tracing

    CICD -- 部署 (cargo build, Docker) --> GW & Orchestrator & Worker
```

---

## 3. 核心组件设计 (Rust 视角)

1. **API 网关 (API Gateway):**
    - **职责:** 同通用设计。
    - **Rust 选项:**
        - **推荐:** 继续使用成熟的外部网关 (Nginx, Kong, Envoy) 以获得丰富的功能和稳定性。
        - **可选:** 如果需求简单（如仅路由和基本认证），可以使用 Rust Web 框架（如 `axum`, `actix-web`, `warp`）构建一个轻量级网关/BFF。
    - **关键:** 无论选择哪种，都要确保与 Rust 后端服务的顺畅集成和可观测性数据传递。

2. **工作流编排器 (Workflow Orchestrator):**
    - **职责:** 同通用设计，管理流程状态和驱动任务。
    - **Rust 实现:**
        - **核心运行时:** `tokio` 作为异步运行时。
        - **状态管理:**
            - **数据库中心:** 将流程状态主要持久化到状态存储中（见下文）。状态转换逻辑通过读取状态、执行操作、更新状态来驱动。这是阶段一最简单可靠的方式。
            - **状态机 Crate (可选):** 考虑使用 `machina` 或 `smeli` 等状态机库来更形式化地定义状态转换，但需评估其成熟度和与异步持久化的集成复杂度。
        - **任务分发:** 通过消息队列客户端（如 `lapin`, `rdkafka`）向 MQ 发布任务。
        - **错误处理:** 利用 Rust 的 `Result` 类型和 `thiserror`/`anyhow` 来进行健壮的错误处理。
    - **技术栈:** `tokio`, `serde` (序列化), 数据库客户端 (`sqlx` 或 `diesel`), MQ 客户端 (`lapin`, `rdkafka`), `tracing` (日志/追踪)。

3. **任务执行器 (Task Executor / Worker):**
    - **职责:** 同通用设计，执行具体业务逻辑。
    - **Rust 实现:**
        - **核心运行时:** `tokio`。
        - **任务消费:** 使用 MQ 客户端库（`lapin`, `rdkafka`）监听并消费任务。
        - **业务逻辑:** 实现具体的业务操作，可能需要 HTTP 客户端 (`reqwest`) 调用外部服务。
        - **结果报告:** 通过 MQ 或直接 API 调用（少用）报告结果。
        - **并发控制:** 利用 `tokio` 的任务和信号量等机制控制并发执行的任务数量。
    - **技术栈:** `tokio`, `serde`, MQ 客户端, `reqwest`, `tracing`。

4. **状态存储 (State Store):**
    - **职责:** 可靠持久化工作流状态。
    - **选型:** **PostgreSQL** 或 **MySQL** 是成熟、可靠的选择。
    - **Rust 交互:**
        - **`sqlx`:** 推荐。纯 Rust 实现，编译时 SQL 检查，异步优先，易于使用。
        - **`diesel`:** 流行的 ORM。提供了更高级的抽象，但异步支持仍在发展中，可能需要额外的配置或包装器。
    - **要求:** 同通用设计（高可用、持久、一致）。

5. **消息队列 / 事件总线 (Message Queue / Event Bus):**
    - **职责:** 解耦、缓冲、可靠传递。
    - **选型:** **RabbitMQ** (使用 AMQP), **Kafka**, **NATS JetStream**。
    - **Rust 客户端:**
        - **RabbitMQ:** `lapin` (基于 `tokio`)。
        - **Kafka:** `rdkafka` (基于 `librdkafka` C 库的绑定，成熟稳定)。
        - **NATS:** `async-nats`。
    - **要求:** 同通用设计（高可用、至少一次传递、持久化）。

---

## 4. API 与事件契约 (Rust 实现)

1. **API 设计:**
    - **框架:**
        - **RESTful:** `axum` (推荐，由 `tokio` 团队维护，社区活跃) 或 `actix-web` (成熟，性能高)。
        - **gRPC:** `tonic` (基于 `hyper` 和 `prost`)。
    - **序列化:** `serde` (通过 `serde_json`, `serde_yaml` 等)。
    - **规范:**
        - **OpenAPI:** 使用 `utoipa` 或 `aide` 等 crate，通过宏或代码生成 OpenAPI 规范。
        - **gRPC:** Protobuf 文件定义服务和消息。
    - **数据结构:** 使用 Rust `struct` 定义请求和响应体，利用 `serde` 进行序列化/反序列化，并通过类型系统保证结构正确性。

2. **事件/消息设计:**
    - **格式:** JSON (使用 `serde_json`) 或更高效的二进制格式如 Avro (`apache-avro`) 或 Protobuf (`prost`)。
    - **Schema:**
        - **JSON:** 定义对应的 Rust `struct`，可选择性使用 `jsonschema` crate 生成 JSON Schema。
        - **Avro/Protobuf:** 使用对应的 IDL 文件定义 Schema，并通过构建脚本生成 Rust 代码。
    - **核心字段:** 定义包含通用元数据（`eventId`, `eventType`, `timestamp`, `source`, `correlationId` 等）的基础事件 `struct`，业务数据封装在 `payload` 字段中（可以使用泛型或特定类型）。

---

## 5. 可观测性设计 (Rust Crates)

1. **日志 (Logging):**
    - **核心库:** `tracing`。它是 Rust 生态的事实标准，专为异步和结构化日志设计。
    - **配置与输出:** `tracing-subscriber`。配置日志级别、过滤，并将日志格式化为 **JSON** 输出到 stdout。
    - **集成:** 与 `tokio` 深度集成，自动捕获任务上下文。通过 `#[tracing::instrument]` 宏方便地为函数添加追踪 span。
    - **聚合:** 同通用设计 (Fluentd/Vector -> ELK/Loki)。

2. **指标 (Metrics):**
    - **门面库:** `metrics` crate。提供一个通用的 API。
    - **导出器:** `metrics-exporter-prometheus`。将指标暴露为 Prometheus 可抓取的格式。
    - **集成:** 在 Web 框架中添加 `/metrics` 端点。使用 `metrics` 库提供的宏 (`counter!`, `gauge!`, `histogram!`) 记录指标。
    - **聚合与可视化:** Prometheus + Grafana。

3. **追踪 (Tracing):**
    - **核心库:** `tracing` 配合 `tracing-opentelemetry`。
    - **OTel SDK:** 配置 `opentelemetry` 和 `opentelemetry-otlp` (或其他导出器) crates。设置服务名、导出器端点等。
    - **上下文传播:** 自动（通过 OTel SDK 对 `reqwest` 等库的集成）或手动（从请求头/消息元数据中提取和注入 Trace Context）。`tracing` 的 span 自动关联到 OTel Trace。
    - **后端:** Jaeger, Tempo, Zipkin。

---

## 6. 基础弹性设计 (Rust 实现)

1. **重试 (Retry):**
    - **库:** `backoff` crate。提供了灵活的指数退避和抖动策略。
    - **应用:** 包裹可能失败的操作（如网络请求、数据库查询）。

2. **超时 (Timeout):**
    - **库:** `tokio::time::timeout`。用于为异步操作设置超时。
    - **应用:** 包裹长时间运行的异步任务或外部调用。

3. **熔断器 (Circuit Breaker):**
    - **库:** Rust 生态中成熟、通用的熔断器库相对较少。可以考虑：
        - `circuit` crate (相对简单)。
        - `failsafe-rs` (功能更丰富，仍在发展)。
        - **自定义实现:** 基于 `std::sync::atomic` 和 `tokio::sync` 构建简单的状态机。对于阶段一，如果下游依赖稳定，可以暂时不实现或只实现非常简单的版本。
    - **应用:** 包裹对关键下游服务的调用。

4. **幂等性 (Idempotency):**
    - **实现:** 应用层逻辑，与语言无关。
        - **请求/消息 ID:** 在处理函数入口处检查并记录已处理的 ID（可能需要 Redis 或数据库支持）。
        - **数据库约束:** 利用 `sqlx`/`diesel` 定义 unique constraints。
        - **乐观锁:** 在 `UPDATE` 语句中使用 `WHERE version = old_version`。

---

## 7. 测试策略 (Rust 工具链)

1. **单元测试 (Unit Tests):**
    - **框架:** Rust 内置的 `#[test]` 属性和测试运行器 (`cargo test`)。
    - **异步测试:** 使用 `#[tokio::test]` 宏。
    - **Mocking:** `mockall` 是一个流行的 Mocking 库。对于数据库等交互，也可以使用接口抽象和假的实现。

2. **集成测试 (Integration Tests):**
    - **框架:** Rust 的 `tests` 目录约定 (`src` 同级)。
    - **依赖管理:**
        - `dockertest-rs`: 以编程方式启动和管理 Docker 容器（数据库、MQ）。
        - `sqlx::test`: 用于隔离数据库测试。
    - **策略:** 测试服务与真实（或接近真实）依赖的交互。

3. **契约测试 (Contract Tests):**
    - **库:** `pact-rust` 相关的 crate (如 `pact_consumer`, `pact_verifier_cli`)。
    - **策略:** 验证 Rust 服务作为消费者或生产者时是否遵守 Pact 契约。

4. **端到端测试 (End-to-End Tests):**
    - **工具:** 同通用设计，使用外部工具调用 API 并验证结果。

---

## 8. CI/CD 流水线 (Rust 特点)

1. **代码质量:**
    - `cargo fmt`: 强制执行统一的代码风格。
    - `cargo clippy`: 强大的静态分析工具，检查代码中的常见错误和非惯用写法。**必须**加入 CI。
2. **编译与测试:** `cargo build --release`, `cargo test`。
3. **Docker 构建:**
    - 使用**多阶段构建 (Multi-stage builds)** 减小最终镜像大小：
        - 第一阶段：使用官方 Rust 镜像编译项目 (`cargo build --release`)。
        - 第二阶段：使用一个轻量级的基础镜像（如 `debian:slim` 或 `alpine`），仅复制编译后的二进制文件和必要的运行时依赖。
    - 考虑使用 `musl` target 编译静态链接的二进制文件以获得更小的镜像（需处理依赖兼容性）。
4. **工具:** 同通用设计 (Jenkins, GitLab CI, GitHub Actions)。

---

## 9. 关键成功指标

与通用设计相同，关注核心流程成功率、API 可用性/延迟、CI/CD 效率、测试覆盖率、MTTR 和可观测性覆盖。

---

## 10. 思维导图 (Text Format)

```text
Rust Workflow - Phase 1: Solid Foundation
|-- Core Principles
|   |-- Value-Driven
|   |-- Simplicity First (KISS)
|   |-- Incrementalism
|   |-- Pragmatic Trade-offs
|   |-- Observability Foundation
|-- Architecture Overview
|   |-- Microservices / SOA
|   |-- Async Communication (API, Events)
|   |-- Tech Stack Focus: Rust, Tokio, Mature Infra
|   |-- Diagram (Mermaid)
|-- Core Components (Rust Focus)
|   |-- API Gateway (External Preferred: Nginx/Kong OR Rust-based: Axum/Actix - Simple Routing)
|   |-- Workflow Orchestrator (Custom Rust Logic)
|   |   |-- Runtime: Tokio
|   |   |-- State Management: Database-centric, maybe simple state machine crate
|   |   |-- Async: Tokio tasks/channels
|   |-- Task Executor / Worker (Rust Service)
|   |   |-- Runtime: Tokio
|   |   |-- MQ Clients: lapin, rdkafka
|   |   |-- HTTP Client: reqwest
|   |-- State Store (Database)
|   |   |-- Interaction: sqlx (async), diesel (ORM)
|   |   |-- Choice: PostgreSQL, MySQL
|   |-- Message Queue / Event Bus (External Service)
|   |   |-- Clients: lapin, rdkafka, async-nats
|   |   |-- Choice: RabbitMQ, Kafka, NATS
|-- API & Event Contracts (Rust Implementation)
|   |-- API: REST (Axum/Actix) or gRPC (Tonic)
|   |   |-- Serialization: serde_json
|   |   |-- Specification: OpenAPI (utoipa/aide) / Protobuf
|   |   |-- Data Structures: Rust Structs + Serde
|   |-- Events: JSON or Avro/Protobuf
|   |   |-- Serialization: serde, apache-avro / prost
|   |   |-- Schema: Defined via Structs / IDL
|   |   |-- Base Event Struct: Common metadata + payload
|-- Observability (Rust Crates)
|   |-- Logging: `tracing`, `tracing-subscriber` (JSON output)
|   |-- Metrics: `metrics` facade, `metrics-exporter-prometheus`
|   |-- Tracing: `tracing` + `tracing-opentelemetry`, OTel SDK
|   |-- Aggregation: External (ELK/Loki, Prometheus, Jaeger/Tempo)
|-- Basic Resilience (Rust Crates / Patterns)
|   |-- Retry: `backoff` crate
|   |-- Timeout: `tokio::time::timeout`
|   |-- Circuit Breaker: Custom logic or crates like `circuit`/`failsafe-rs` (evaluate maturity)
|   |-- Idempotency: Application logic (request IDs, DB constraints via sqlx/diesel)
|-- Testing Strategy (Rust Tooling)
|   |-- Unit Tests: `#[test]`, `#[tokio::test]`, `mockall`
|   |-- Integration Tests: `tests` dir, `dockertest-rs`, `sqlx::test`
|   |-- Contract Tests: `pact-rust` implementations
|   |-- E2E Tests: External tools
|-- CI/CD Pipeline (Rust Specifics)
|   |-- Quality Gates: `cargo fmt`, `cargo clippy`
|   |-- Tooling: `cargo build/test`
|   |-- Build: Multi-stage Docker builds (optimize for size)
|   |-- Deployment: Kubernetes / Cloud Services
|-- Key Success Metrics (Same as before)
```
