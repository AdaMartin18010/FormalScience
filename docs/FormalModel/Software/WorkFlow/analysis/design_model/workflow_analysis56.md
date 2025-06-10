# 架构基础

好的，我们来为“阶段一：坚实基础 (Solid Foundation)”设计一个全面且务实的架构方案。
此阶段的目标是构建一个**稳定、可维护、可观测、具备基本弹性且易于迭代**的工作流系统底座。

**核心原则 (Guiding Principles):**

1. **价值驱动:** 优先实现核心工作流执行能力和保障系统稳定运行的基本要素。
2. **简单性优先:** 采用成熟、简单、易于理解和运维的技术与模式。避免过早引入复杂性。
3. **渐进主义:** 构建可独立部署和测试的模块化组件，为后续阶段的演进打下基础。
4. **务实权衡:** 接受合理的权衡，例如在初期可能牺牲部分极致性能来换取开发速度和稳定性。
5. **可观测性基础:** 将可观测性作为一等公民，深度融入系统设计。

**架构概览 (Architecture Overview):**

本阶段采用基于**微服务**或**服务导向架构 (SOA)** 的思想，
将系统拆分为若干**职责单一、边界清晰**的组件。
组件之间通过**定义良好的 API**（同步）和**标准的事件/消息**（异步）进行通信。
技术选型倾向于**成熟稳定、社区活跃、团队熟悉**的技术栈。

```mermaid
graph LR
    subgraph 用户/客户端
        UI(用户界面/API客户端)
    end

    subgraph 系统边界
        GW(API网关)
    end

    subgraph 核心服务
        Orchestrator(工作流编排器)
        Worker(任务执行器)
        StateStore[(状态存储)]
        MQ[(消息队列/事件总线)]
    end

    subgraph 支撑服务
        Logging[(日志聚合)]
        Metrics[(指标监控)]
        Tracing[(分布式追踪)]
        CICD(CI/CD流水线)
    end

    UI --> GW
    GW --> Orchestrator
    GW --> Worker -- 可能直接调用，或通过编排器 --
    Orchestrator --> MQ -- 发布任务/事件 --
    Orchestrator --> StateStore -- 读写流程状态 --
    Worker -- 监听 --> MQ -- 获取任务 --
    Worker --> StateStore -- 更新任务状态(可选) --
    Worker --> GW -- 回调或调用外部API(可选) --

    Orchestrator -- Logs/Metrics/Traces --> Logging & Metrics & Tracing
    Worker -- Logs/Metrics/Traces --> Logging & Metrics & Tracing
    GW -- Logs/Metrics/Traces --> Logging & Metrics & Tracing

    CICD -- 部署 --> GW & Orchestrator & Worker
```

**核心组件设计 (Core Component Design):**

1. **API 网关 (API Gateway):**
    * **核心职责:** 统一入口，处理认证、授权、速率限制、请求路由、基础协议转换。
    * **关键接口:** 面向客户端的 API (RESTful 或 gRPC)，将请求路由到内部服务。
    * **状态管理:** 通常无状态或仅有少量缓存状态。
    * **解耦:** 解耦前端与后端服务，提供稳定的外部接口。
    * **技术选型:** Nginx+Lua, Kong, Spring Cloud Gateway, Envoy 等。

2. **工作流编排器 (Workflow Orchestrator):**
    * **核心职责:** 管理工作流的生命周期（启动、暂停、恢复、终止），根据预定义的流程定义驱动任务执行，维护工作流实例的状态。
    * **关键接口:**
        * 接收来自网关的启动/管理工作流请求的 API。
        * 与状态存储交互以持久化和读取流程状态。
        * 向消息队列发布待执行的任务或流程事件。
        * (可选) 监听来自 Worker 的任务完成事件。
    * **状态管理:** **有状态**服务，核心是工作流实例的状态机。
    * **解耦:** 将流程控制逻辑与具体任务执行逻辑分离。
    * **技术选型:**
        * 自研基于状态机模型。
        * 轻量级嵌入式流程引擎（如 Camunda Zeebe (简单模式), Temporal (入门级部署), Prefect Core, Dagster）。本阶段**避免选择过于重量级或复杂的引擎**。

3. **任务执行器 (Task Executor / Worker):**
    * **核心职责:** 执行由编排器分发的具体业务任务（例如，调用外部 API、执行计算、数据转换等）。
    * **关键接口:**
        * 监听消息队列以获取任务。
        * (可选) 向编排器或消息队列报告任务执行结果（成功/失败/重试）。
        * (可选) 与状态存储交互以记录任务级状态。
        * (可选) 调用外部依赖服务或 API。
    * **状态管理:** 通常**无状态**或仅包含任务执行期间的短暂状态。状态由编排器或外部系统管理。
    * **解耦:** 将具体业务逻辑实现与流程编排分离。易于独立扩展和部署不同类型的 Worker。
    * **技术选型:** 根据业务逻辑选择合适的语言和框架。可部署为独立的微服务、容器或 Serverless Function。

4. **状态存储 (State Store):**
    * **核心职责:** 可靠地持久化工作流实例的状态、任务状态（如果需要）。
    * **关键接口:** 提供 CRUD 操作接口供编排器（主要）和执行器（次要）访问。
    * **选型考量:**
        * **关系型数据库 (如 PostgreSQL, MySQL):** 成熟稳定，支持事务，适合结构化状态数据，初期复杂度可控。
        * **NoSQL 数据库 (如 MongoDB, DynamoDB):** 灵活模式，易于水平扩展，但一致性模型需要仔细考虑。
    * **要求:** **高可用性、数据持久性、一致性**（至少支持单文档/行级别的原子操作）。

5. **消息队列 / 事件总线 (Message Queue / Event Bus):**
    * **核心职责:** 解耦编排器和执行器，提供异步通信机制，缓冲任务，支持重试和可靠传递。
    * **关键接口:** 提供发布 (Publish) 和订阅 (Subscribe) / 消费 (Consume) 接口。
    * **选型考量:** RabbitMQ, Kafka, Pulsar, NATS JetStream, SQS/PubSub (云服务)。
    * **要求:** **高可用性、至少一次传递 (At-Least-Once Delivery) 保证、持久化**（防止消息丢失）。需要考虑消息顺序性（如果业务需要）。

**API 与事件契约 (API & Event Contracts):**

1. **API 设计:**
    * **风格:** 优先选择 **RESTful API** (使用 JSON)，或在需要强类型和高性能场景下考虑 **gRPC**。
    * **规范:** 使用 **OpenAPI (Swagger)** 或 **Protobuf IDL** 定义清晰的 API 规范。
    * **设计原则:** 资源导向，标准 HTTP 方法/状态码，清晰的请求/响应结构，统一的错误处理格式。
    * **版本控制:** 制定简单的 API 版本控制策略（如 URL 路径版本 `/v1/...`）。
    * **文档化:** API 规范即文档，并提供易于访问的文档页面。

2. **事件/消息设计:**
    * **格式:** 使用 **JSON** 或 **Avro/Protobuf** (如果需要强 Schema 和效率)。
    * **Schema 定义:** 定义清晰、版本化的事件 Schema (如使用 JSON Schema)。
    * **核心字段:** 每个事件/消息应包含：
        * `eventId`: 唯一 ID (用于幂等性)。
        * `eventType`: 事件类型/名称 (版本化，如 `order.created.v1`)。
        * `timestamp`: 事件发生时间。
        * `source`: 事件来源服务。
        * `correlationId`: 用于分布式追踪的关联 ID。
        * `payload`: 具体的业务数据。
    * **命名规范:** 制定清晰的 Topic/Queue 命名规范。

**可观测性设计 (Observability Design):**

1. **日志 (Logging):**
    * **格式:** **结构化日志 (JSON)**。
    * **内容:** 每条日志包含时间戳、日志级别、服务名、实例 ID、**Correlation ID**、请求 ID (如有)、日志消息、关键业务字段。
    * **输出:** 标准输出 (stdout/stderr)。
    * **聚合:** 使用 **Fluentd/Fluent Bit/Vector** 等收集日志，发送到集中的日志存储与查询系统 (如 **Elasticsearch/Loki + Kibana/Grafana**)。

2. **指标 (Metrics):**
    * **类型:**
        * **系统指标:** CPU、内存、磁盘 I/O、网络 (由基础设施监控提供)。
        * **应用指标 (RED):** 请求**速率 (Rate)**、**错误 (Errors)**、**延迟 (Duration)**。针对 API 端点、消息处理、数据库调用等。
        * **业务指标:** 工作流启动数、任务完成数、队列长度、特定业务步骤的计数器等。
    * **格式:** **Prometheus Exposition Format** 是事实标准。
    * **采集:** 应用内置 Metrics Endpoint (`/metrics`)，使用标准库 (如 micrometer, prometheus-client)。
    * **聚合与可视化:** **Prometheus** 负责抓取和存储，**Grafana** 负责可视化和告警 (Alertmanager)。

3. **追踪 (Tracing):**
    * **标准:** 遵循 **OpenTelemetry (OTel)** 标准。
    * **实现:** 使用对应语言的 OTel SDK 自动或手动埋点。
    * **上下文传播:** 确保 Trace Context (包含 `traceId`, `spanId`) 通过 HTTP Headers (如 W3C Trace Context) 或消息队列的元数据在服务间传递。
    * **后端:** 将 Trace 数据导出到兼容 OTel 的后端 (如 **Jaeger, Tempo, Zipkin**)。

**基础弹性设计 (Basic Resilience Design):**

1. **重试 (Retry):**
    * **位置:** 主要在客户端（调用下游服务或消息处理失败时）。
    * **策略:** 针对**临时性、网络相关**错误。采用**指数退避 + 抖动 (Exponential Backoff + Jitter)** 策略。配置最大重试次数。
    * **实现:** 使用标准库 (如 Resilience4j, Polly, 或语言内置)。

2. **超时 (Timeout):**
    * **位置:** 客户端（设置请求超时）和服务器端（处理请求超时）。
    * **策略:** 设置合理的超时时间，避免无限等待。超时应产生明确的错误。
    * **实现:** 配置 HTTP Client、数据库连接池、消息处理等。

3. **熔断器 (Circuit Breaker):**
    * **位置:** 客户端，包裹对下游服务的调用。
    * **策略:** 当下游服务错误率超过阈值时，快速失败，阻止请求发送，防止雪崩。一段时间后尝试半开放状态恢复。
    * **实现:** 使用标准库 (如 Resilience4j, Polly)。

4. **幂等性 (Idempotency):**
    * **位置:** 服务器端（API 接口、消息/事件处理器）。
    * **策略:** 保证同一请求/消息被处理多次时，结果与处理一次相同。
    * **实现:**
        * **请求/消息 ID:** 要求客户端传入唯一 ID，服务端记录已处理的 ID 并检查重复。
        * **乐观锁/版本号:** 在状态更新时使用。
        * **数据库唯一约束:** 利用数据库保证。

**测试策略 (Testing Strategy):**

1. **单元测试 (Unit Tests):**
    * **目标:** 测试单个类/函数逻辑的正确性。
    * **工具:** 标准语言测试框架 (JUnit, pytest, Go testing)。
    * **要求:** 高覆盖率，快速执行。Mock 外部依赖。

2. **集成测试 (Integration Tests):**
    * **目标:** 测试组件与其直接依赖（数据库、消息队列、外部 API Mock）的交互。
    * **工具:** 测试框架 + Testcontainers 或本地依赖实例。
    * **要求:** 覆盖关键交互路径。在 CI 中运行。

3. **契约测试 (Contract Tests):**
    * **目标:** 验证服务间（API 或事件）的交互是否符合约定。
    * **工具:** Pact, Spring Cloud Contract。
    * **要求:** 生产者驱动或消费者驱动，确保接口兼容性，尽早发现集成问题。

4. **端到端测试 (End-to-End Tests):**
    * **目标:** 验证关键用户场景流经整个系统的正确性。
    * **策略:** **保持最少数量**，仅覆盖最核心的 Happy Path。因为它们脆弱且执行慢。
    * **工具:** Cypress, Selenium, Playwright (如果涉及 UI)，或 API 测试框架 (Postman/Newman, k6)。

**CI/CD 流水线 (CI/CD Pipeline):**

1. **代码仓库 (Repository):** Git (如 GitHub, GitLab, Bitbucket)。采用合适的分支策略（如 Gitflow 或 GitHub Flow 简化版）。
2. **持续集成 (CI):**
    * **触发:** 代码提交到主干或特性分支。
    * **步骤:** 拉取代码 -> 编译 -> 代码静态分析 (Linting, SonarQube) -> 运行单元测试 -> 运行集成测试 -> (可选)运行契约测试 -> 构建部署物 (如 Docker 镜像) -> 推送镜像到仓库。
3. **持续部署 (CD):**
    * **触发:** CI 成功后，(可选)手动批准。
    * **步骤:** 从镜像仓库拉取镜像 -> 部署到测试/预生产环境 -> (可选)运行少量 E2E 测试 -> 部署到生产环境（蓝绿部署、金丝雀发布等策略将在后续阶段考虑，本阶段可先用滚动更新）。
4. **工具:** Jenkins, GitLab CI, GitHub Actions, Argo CD (用于 Kubernetes)。

**技术选型考量 (Technology Stack Considerations - 示例性):**

* **语言:** Java (Spring Boot), Python (Flask/Django/FastAPI), Go, Node.js (根据团队熟悉度和生态)。
* **API 网关:** Kong, Nginx+Lua, Spring Cloud Gateway。
* **编排器/Worker 框架:** 根据语言选择，或轻量级流程引擎。
* **状态存储:** PostgreSQL, MySQL。
* **消息队列:** RabbitMQ, Kafka (如果需要流处理能力和高吞吐), NATS JetStream。
* **可观测性:** Prometheus, Grafana, OpenTelemetry SDKs, Jaeger/Tempo, ELK/Loki。
* **容器化与编排:** Docker, Kubernetes (或云提供商的容器服务如 ECS, GKE)。

**关键成功指标 (Key Success Metrics for Phase 1):**

* **核心工作流端到端成功率:** > 99.X% (根据业务定义)。
* **核心 API 可用性:** > 99.X% (根据业务定义)。
* **核心 API 平均响应时间 & P99 延迟:** 在可接受范围内。
* **CI/CD 流水线稳定性和执行时间:** 构建和部署快速可靠。
* **单元/集成测试覆盖率:** 达到预定目标 (e.g., 单元测试 > 70-80%)。
* **平均故障恢复时间 (MTTR):** 能够快速发现并恢复基本故障。
* **可观测性数据覆盖率:** 关键组件和路径都有日志、指标和追踪数据。

这个阶段的设计重点在于**稳扎稳打**，构建一个虽不追求极致性能或复杂特性，但**稳定可靠、易于理解、易于排错、易于扩展**的系统底座。这将为后续阶段引入更高级的特性提供坚实的基础和信心。
