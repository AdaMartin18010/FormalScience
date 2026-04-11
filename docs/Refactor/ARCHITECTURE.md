# FormalScience 项目架构文档

> 版本: v4.0.0
> 日期: 2026-04-11
> 状态: FINAL

---

## 1. 整体架构图

```mermaid
flowchart TB
    subgraph Client["客户端层"]
        Web["Web 前端"]
        CLI["CLI 工具"]
        API["API 客户端"]
    end

    subgraph Gateway["网关层"]
        APIGateway["API Gateway<br/>Nginx/Traefik"]
        Auth["认证服务<br/>JWT/OAuth2"]
    end

    subgraph Core["核心服务层"]
        FormalRE["FormalRE 引擎"]
        Concept["概念管理系统"]
        Composed["组合服务"]
        Engine["执行引擎"]
    end

    subgraph Data["数据层"]
        DB[("主数据库<br/>PostgreSQL")]
        Cache[("缓存<br/>Redis")]
        Queue[("消息队列<br/>RabbitMQ")]
    end

    subgraph External["外部集成"]
        AI["AI 服务"]
        Storage["对象存储"]
        Monitor["监控服务"]
    end

    Client --> Gateway
    Gateway --> Core
    Core --> Data
    Core --> External
```

---

## 2. 模块关系图

```mermaid
flowchart LR
    subgraph FormalScience["FormalScience 项目"]
        direction TB

        subgraph Layer1["表示层"]
            View["view/"]
            Docs["docs/"]
        end

        subgraph Layer2["业务层"]
            FormalRE_Mod["FormalRE/"]
            Concept_Mod["Concept/"]
            Composed_Mod["Composed/"]
        end

        subgraph Layer3["支撑层"]
            Tools["tools/"]
            Tech["Tech/"]
            Engineer["Engineer/"]
        end

        subgraph Layer4["基础设施"]
            Research["research/"]
        end
    end

    View --> FormalRE_Mod
    View --> Concept_Mod
    Docs --> FormalRE_Mod

    FormalRE_Mod --> Tools
    Concept_Mod --> Tools
    Composed_Mod --> Tools

    FormalRE_Mod --> Tech
    Concept_Mod --> Tech

    Tools --> Research
    Tech --> Research
    Engineer --> Research
```

### 模块说明

| 模块 | 路径 | 职责 | 依赖 |
|------|------|------|------|
| FormalRE | `FormalRE/` | 形式化规则引擎 | Concept, Tools |
| Concept | `Concept/` | 概念与知识管理 | Tools, Tech |
| Composed | `Composed/` | 组合与编排服务 | FormalRE, Concept |
| Tools | `tools/` | 工具集与公用库 | - |
| Tech | `Tech/` | 技术基础设施 | - |
| Engineer | `Engineer/` | 工程化组件 | Tools |
| View | `view/` | 前端展示层 | Core模块 |
| Docs | `docs/` | 文档系统 | - |
| Research | `research/` | 研究与实验 | - |

---

## 3. 数据流图

### 3.1 请求处理流程

```mermaid
sequenceDiagram
    participant Client as 客户端
    participant Gateway as API网关
    participant Auth as 认证服务
    participant Core as 核心服务
    participant Cache as Redis缓存
    participant DB as 数据库
    participant Queue as 消息队列

    Client->>Gateway: HTTP Request
    Gateway->>Auth: 验证Token
    Auth-->>Gateway: Token有效

    Gateway->>Core: 转发请求

    Core->>Cache: 查询缓存
    alt 缓存命中
        Cache-->>Core: 返回缓存数据
    else 缓存未命中
        Core->>DB: 查询数据
        DB-->>Core: 返回数据
        Core->>Cache: 写入缓存
    end

    Core->>Queue: 异步任务（如需要）
    Core-->>Gateway: 返回结果
    Gateway-->>Client: HTTP Response
```

### 3.2 数据处理流程

```mermaid
flowchart LR
    Input["输入数据"] --> Validate["验证层"]
    Validate --> Transform["转换层"]
    Transform --> Process["处理层"]
    Process --> Store["存储层"]
    Process --> Notify["通知层"]

    subgraph ValidateLayer["验证层"]
        Validate --> Schema["Schema验证"]
        Validate --> AuthCheck["权限检查"]
    end

    subgraph TransformLayer["转换层"]
        Transform --> Normalize["数据规范化"]
        Transform --> Enrich["数据增强"]
    end

    subgraph ProcessLayer["处理层"]
        Process --> Business["业务逻辑"]
        Process --> AI["AI处理"]
    end
```

---

## 4. 技术栈说明

### 4.1 后端技术栈

| 类别 | 技术 | 版本 | 用途 |
|------|------|------|------|
| 运行时 | Node.js | 20.x LTS | JavaScript运行时 |
| 语言 | TypeScript | 5.x | 主要开发语言 |
| Web框架 | Express/Fastify | 4.x/4.x | API服务框架 |
| ORM | Prisma/TypeORM | 5.x | 数据库操作 |
| 验证 | Zod/Joi | 3.x | 数据验证 |
| 测试 | Jest/Vitest | 29.x/1.x | 单元测试 |

### 4.2 前端技术栈

| 类别 | 技术 | 版本 | 用途 |
|------|------|------|------|
| 框架 | React/Vue | 18.x/3.x | UI框架 |
| 构建 | Vite | 5.x | 构建工具 |
| 样式 | Tailwind CSS | 3.x | CSS框架 |
| 状态 | Zustand/Pinia | 4.x | 状态管理 |
| 图表 | D3/ECharts | 7.x/5.x | 数据可视化 |

### 4.3 基础设施

| 类别 | 技术 | 用途 |
|------|------|------|
| 容器化 | Docker & Docker Compose | 应用容器化 |
| 编排 | Kubernetes (可选) | 容器编排 |
| 反向代理 | Nginx/Traefik | 流量网关 |
| 监控 | Prometheus + Grafana | 指标监控 |
| 日志 | ELK Stack/Loki | 日志聚合 |
| CI/CD | GitHub Actions | 持续集成/部署 |

### 4.4 数据存储

| 类型 | 技术 | 用途 |
|------|------|------|
| 关系数据库 | PostgreSQL 16 | 主数据存储 |
| 缓存 | Redis 7 | 会话缓存、热点数据 |
| 消息队列 | RabbitMQ | 异步任务处理 |
| 搜索引擎 | Elasticsearch (可选) | 全文搜索 |
| 对象存储 | MinIO/S3 | 文件存储 |

---

## 5. 部署架构

### 5.1 开发环境

```mermaid
flowchart TB
    subgraph Dev["开发环境"]
        DevApp["应用服务<br/>localhost:3000"]
        DevDB["PostgreSQL<br/>localhost:5432"]
        DevRedis["Redis<br/>localhost:6379"]
    end

    Developer["开发者"] --> DevApp
    DevApp --> DevDB
    DevApp --> DevRedis
```

### 5.2 生产环境

```mermaid
flowchart TB
    subgraph Prod["生产环境"]
        subgraph K8s["Kubernetes Cluster"]
            Ingress["Ingress Controller"]

            subgraph AppLayer["应用层"]
                App1["App Pod 1"]
                App2["App Pod 2"]
                App3["App Pod 3"]
            end

            subgraph ServiceLayer["服务层"]
                Core1["Core Pod 1"]
                Core2["Core Pod 2"]
            end
        end

        subgraph DataLayer["数据层"]
            PG[("PostgreSQL<br/>主从集群")]
            RedisCluster[("Redis Cluster")]
            MQ["RabbitMQ Cluster"]
        end

        subgraph StorageLayer["存储层"]
            MinIO["MinIO对象存储"]
            NFS["NFS共享存储"]
        end
    end

    User["用户"] --> Ingress
    Ingress --> AppLayer
    AppLayer --> ServiceLayer
    ServiceLayer --> DataLayer
    ServiceLayer --> StorageLayer
```

### 5.3 Docker Compose 部署

```yaml
# 简化版 docker-compose.yml 结构
version: '3.8'
services:
  app:
    image: formalscience:latest
    ports:
      - "3000:3000"
    environment:
      - NODE_ENV=production
      - DATABASE_URL=postgresql://...
    depends_on:
      - postgres
      - redis

  postgres:
    image: postgres:16-alpine
    volumes:
      - pgdata:/var/lib/postgresql/data

  redis:
    image: redis:7-alpine
    volumes:
      - redisdata:/data
```

### 5.4 环境配置

| 环境 | 域名 | 资源配置 | 高可用 |
|------|------|----------|--------|
| 开发 | localhost | 单实例 | 否 |
| 测试 | test.formalscience.local | 2核4G x 2 | 基础 |
| 预发布 | staging.formalscience.com | 4核8G x 3 | 是 |
| 生产 | formalscience.com | 8核16G x 3+ | 是 |

---

## 6. 接口规范

### 6.1 REST API 规范

- 基础路径: `/api/v1`
- 认证方式: Bearer Token (JWT)
- 响应格式: JSON
- 状态码遵循 HTTP 标准

### 6.2 WebSocket 接口

- 路径: `/ws`
- 用于实时通信和通知
- 支持房间订阅模式

---

## 7. 安全架构

```mermaid
flowchart TB
    subgraph Security["安全防护层"]
        WAF["WAF防护"]
        DDoS["DDoS防护"]
        SSL["SSL/TLS加密"]
    end

    subgraph Access["访问控制"]
        Auth1["JWT认证"]
        RBAC["RBAC权限"]
        APIKey["API密钥"]
    end

    subgraph DataSecurity["数据安全"]
        Encrypt["数据加密"]
        Backup["定期备份"]
        Audit["审计日志"]
    end
```

---

## 8. 监控与运维

### 8.1 监控指标

- **应用指标**: QPS、响应时间、错误率
- **业务指标**: 活跃用户、任务完成率
- **系统指标**: CPU、内存、磁盘、网络
- **业务告警**: 异常检测、阈值告警

### 8.2 日志规范

```json
{
  "timestamp": "2026-04-11T17:56:51Z",
  "level": "INFO",
  "service": "formalscience",
  "trace_id": "uuid",
  "message": "Operation completed",
  "metadata": {}
}
```

---

## 9. 扩展性设计

- **水平扩展**: 无状态服务设计，支持水平扩容
- **微服务拆分**: 按业务域逐步拆分服务
- **插件系统**: 支持自定义插件扩展功能
- **多租户**: 支持租户隔离的数据模型

---

## 10. 文档维护

- 本文档随版本迭代更新
- 重大架构变更需同步更新
- 变更记录见项目 CHANGELOG
