# FormalScience 项目架构文档

> 版本: v5.0.0
> 日期: 2026-04-11
> 状态: UPDATED

---

## 1. 整体架构图

```mermaid
flowchart TB
    subgraph Client["客户端层"]
        Web["Web 前端"]
        CLI["CLI 工具"]
        API["API 客户端"]
        Notebook["Jupyter/交互式环境"]
    end

    subgraph Gateway["网关层"]
        APIGateway["API Gateway<br/>Nginx/Traefik"]
        Auth["认证服务<br/>JWT/OAuth2"]
        RateLimit["限流服务<br/>Redis"]
    end

    subgraph Core["核心服务层"]
        FormalRE["FormalRE 引擎"]
        Concept["概念管理系统"]
        Composed["组合服务"]
        Engine["执行引擎"]
        DataSci["数据科学引擎"]
        Cognition["认知建模服务"]
    end

    subgraph Data["数据层"]
        DB[("主数据库<br/>PostgreSQL")]
        Cache[("缓存<br/>Redis")]
        Queue[("消息队列<br/>RabbitMQ")]
        TSDB[("时序数据库<br/>InfluxDB")]
        GraphDB[("图数据库<br/>Neo4j")]
    end

    subgraph External["外部集成"]
        AI["AI 服务"]
        Storage["对象存储"]
        Monitor["监控服务"]
        MLflow["MLflow<br/>模型管理"]
    end

    Client --> Gateway
    Gateway --> Core
    Core --> Data
    Core --> External
```

---

## 2. 模块关系图

### 2.1 核心模块架构

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
            DataSci_Mod["DataScience/"]
            Cognition_Mod["Cognition/"]
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
    View --> DataSci_Mod
    Docs --> FormalRE_Mod

    FormalRE_Mod --> Tools
    Concept_Mod --> Tools
    Composed_Mod --> Tools
    DataSci_Mod --> Tools
    Cognition_Mod --> Tools

    FormalRE_Mod --> Tech
    Concept_Mod --> Tech
    DataSci_Mod --> Tech

    Tools --> Research
    Tech --> Research
    Engineer --> Research
```

### 2.2 文档模块架构 (15个知识模块)

```mermaid
flowchart TB
    subgraph Foundation["基础层 Modules 01-02"]
        M01[01_数学基础]
        M02[02_形式语言]
    end

    subgraph Implementation["实现层 Modules 03-04"]
        M03[03_编程范式]
        M04[04_软件工程]
    end

    subgraph Theory["理论层 Modules 05"]
        M05[05_形式化理论]
    end

    subgraph Application["应用层 Modules 06-07"]
        M06[06_调度系统]
        M07[07_交叉视角]
    end

    subgraph DataScience["数据科学层 Modules 09-10"]
        M09[09_统计学]
        M10[10_信息论]
    end

    subgraph SystemScience["系统科学层 Module 11"]
        M11[11_系统科学]
    end

    subgraph CognitiveSocial["认知社会层 Modules 12-15"]
        M12[12_决策与博弈论]
        M13[13_认知科学形式模型]
        M14[14_形式语言学]
        M15[15_社会科学形式化]
    end

    M01 --> M02
    M01 --> M09
    M02 --> M03
    M02 --> M13
    M02 --> M14
    M03 --> M04
    M04 --> M06
    M05 --> M06
    M05 --> M07
    M09 --> M10
    M09 --> M12
    M10 --> M11
    M11 --> M15
    M12 --> M15
    M13 --> M15
    M14 --> M15
    M06 --> M07
```

### 模块说明

| 模块 | 路径 | 职责 | 依赖 | 状态 |
|------|------|------|------|------|
| FormalRE | `FormalRE/` | 形式化规则引擎 | Concept, Tools | 稳定 |
| Concept | `Concept/` | 概念与知识管理 | Tools, Tech | 稳定 |
| Composed | `Composed/` | 组合与编排服务 | FormalRE, Concept | 稳定 |
| DataScience | `DataScience/` | 统计与机器学习服务 | Tools, Tech | 新增 |
| Cognition | `Cognition/` | 认知建模与NLP | Concept, DataScience | 新增 |
| Tools | `tools/` | 工具集与公用库 | Core | 稳定 |
| Tech | `Tech/` | 技术基础设施 | Core | 稳定 |
| Engineer | `Engineer/` | 工程化组件 | Tools | 稳定 |
| View | `view/` | 前端展示层 | Core模块 | 稳定 |
| Docs | `docs/` | 文档系统 | Core | 扩展 |
| Research | `research/` | 研究与实验 | Core | 活跃 |

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
        Process --> Stats["统计分析"]
    end
```

### 3.3 新增：数据科学工作流

```mermaid
flowchart TB
    subgraph DataIngestion["数据摄入"]
        Raw["原始数据"]
        Clean["数据清洗"]
        Transform["特征工程"]
    end

    subgraph Analysis["分析层"]
        Stats["统计分析"]
        ML["机器学习"]
        Viz["可视化"]
    end

    subgraph ModelMgmt["模型管理"]
        Train["训练"]
        Eval["评估"]
        Deploy["部署"]
    end

    subgraph Inference["推理服务"]
        Predict["预测"]
        Explain["解释性"]
        Monitor["监控"]
    end

    Raw --> Clean --> Transform
    Transform --> Stats
    Transform --> ML
    Stats --> Viz
    ML --> Train --> Eval --> Deploy
    Deploy --> Predict
    Predict --> Explain --> Monitor
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
| **科学计算** | **Python/PyData** | **3.11+** | **统计/ML** ⭐新增 |
| **ML框架** | **PyTorch/sklearn** | **2.x/1.x** | **机器学习** ⭐新增 |

### 4.2 前端技术栈

| 类别 | 技术 | 版本 | 用途 |
|------|------|------|------|
| 框架 | React/Vue | 18.x/3.x | UI框架 |
| 构建 | Vite | 5.x | 构建工具 |
| 样式 | Tailwind CSS | 3.x | CSS框架 |
| 状态 | Zustand/Pinia | 4.x | 状态管理 |
| 图表 | D3/ECharts | 7.x/5.x | 数据可视化 |
| **Notebook** | **JupyterLite** | **0.2.x** | **交互式计算** ⭐新增 |

### 4.3 基础设施

| 类别 | 技术 | 用途 |
|------|------|------|
| 容器化 | Docker & Docker Compose | 应用容器化 |
| 编排 | Kubernetes (可选) | 容器编排 |
| 反向代理 | Nginx/Traefik | 流量网关 |
| 监控 | Prometheus + Grafana | 指标监控 |
| 日志 | ELK Stack/Loki | 日志聚合 |
| CI/CD | GitHub Actions | 持续集成/部署 |
| **ML平台** | **MLflow/Kubeflow** | **模型生命周期** ⭐新增 |
| **图数据库** | **Neo4j** | **知识图谱** ⭐新增 |

### 4.4 数据存储

| 类型 | 技术 | 用途 |
|------|------|------|
| 关系数据库 | PostgreSQL 16 | 主数据存储 |
| 缓存 | Redis 7 | 会话缓存、热点数据 |
| 消息队列 | RabbitMQ | 异步任务处理 |
| 搜索引擎 | Elasticsearch (可选) | 全文搜索 |
| 对象存储 | MinIO/S3 | 文件存储 |
| **时序数据库** | **InfluxDB** | **指标数据** ⭐新增 |
| **图数据库** | **Neo4j** | **知识关系** ⭐新增 |
| **向量数据库** | **Pinecone/Milvus** | **语义搜索** ⭐新增 |

---

## 5. 部署架构

### 5.1 开发环境

```mermaid
flowchart TB
    subgraph Dev["开发环境"]
        DevApp["应用服务<br/>localhost:3000"]
        DevDB["PostgreSQL<br/>localhost:5432"]
        DevRedis["Redis<br/>localhost:6379"]
        DevJupyter["Jupyter<br/>localhost:8888"]
    end

    Developer["开发者"] --> DevApp
    Developer --> DevJupyter
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
                ML1["ML Service 1"]
                ML2["ML Service 2"]
            end
        end

        subgraph DataLayer["数据层"]
            PG[("PostgreSQL<br/>主从集群")]
            RedisCluster[("Redis Cluster")]
            MQ["RabbitMQ Cluster"]
            Neo4j[("Neo4j集群")]
            Influx[("InfluxDB")]
        end

        subgraph StorageLayer["存储层"]
            MinIO["MinIO对象存储"]
            NFS["NFS共享存储"]
            MLflow[("MLflow存储")]
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
# 完整版 docker-compose.yml 结构
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

  jupyter:
    image: formalscience/datascience:latest
    ports:
      - "8888:8888"
    volumes:
      - ./notebooks:/home/jovyan/work

  mlflow:
    image: mlflow/mlflow:latest
    ports:
      - "5000:5000"
    depends_on:
      - postgres

  postgres:
    image: postgres:16-alpine
    volumes:
      - pgdata:/var/lib/postgresql/data

  redis:
    image: redis:7-alpine
    volumes:
      - redisdata:/data

  neo4j:
    image: neo4j:5-community
    ports:
      - "7474:7474"
      - "7687:7687"
    volumes:
      - neo4jdata:/data
```

### 5.4 环境配置

| 环境 | 域名 | 资源配置 | 高可用 | 特殊服务 |
|------|------|----------|--------|----------|
| 开发 | localhost | 单实例 | 否 | Jupyter |
| 测试 | test.formalscience.local | 2核4G x 2 | 基础 | - |
| 预发布 | staging.formalscience.com | 4核8G x 3 | 是 | MLflow |
| 生产 | formalscience.com | 8核16G x 3+ | 是 | 全服务 |

---

## 6. 接口规范

### 6.1 REST API 规范

- 基础路径: `/api/v1`
- 认证方式: Bearer Token (JWT)
- 响应格式: JSON
- 状态码遵循 HTTP 标准

### 6.2 新增模块 API

| 模块 | 基础路径 | 主要功能 |
|------|----------|----------|
| 数据科学 | `/api/v1/datascience` | 统计分析、模型训练 |
| 认知建模 | `/api/v1/cognition` | 知识表示、推理 |
| 图查询 | `/api/v1/graph` | 知识图谱查询 |
| ML服务 | `/api/v1/ml` | 预测、解释性 |

### 6.3 WebSocket 接口

- 路径: `/ws`
- 用于实时通信和通知
- 支持房间订阅模式

### 6.4 GraphQL 接口 (新增)

- 路径: `/graphql`
- 用于灵活数据查询
- 支持知识图谱遍历

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
        Privacy["隐私保护"]
    end

    subgraph MLSecurity["ML安全"]
        ModelEncrypt["模型加密"]
        AdvDefense["对抗防御"]
        BiasDetect["偏见检测"]
    end
```

---

## 8. 监控与运维

### 8.1 监控指标

- **应用指标**: QPS、响应时间、错误率
- **业务指标**: 活跃用户、任务完成率
- **系统指标**: CPU、内存、磁盘、网络
- **业务告警**: 异常检测、阈值告警
- **ML指标**: 模型性能、漂移检测 ⭐新增

### 8.2 日志规范

```json
{
  "timestamp": "2026-04-11T17:56:51Z",
  "level": "INFO",
  "service": "formalscience",
  "trace_id": "uuid",
  "message": "Operation completed",
  "module": "datascience",
  "metadata": {}
}
```

---

## 9. 扩展性设计

- **水平扩展**: 无状态服务设计，支持水平扩容
- **微服务拆分**: 按业务域逐步拆分服务
- **插件系统**: 支持自定义插件扩展功能
- **多租户**: 支持租户隔离的数据模型
- **模块化文档**: 新增模块可独立部署和扩展 ⭐新增

---

## 10. 文档架构演进

### 10.1 版本历史

| 版本 | 日期 | 变更内容 |
|------|------|----------|
| v1.0 | 2026-01 | 初始架构 (Modules 01-06) |
| v2.0 | 2026-02 | 添加交叉视角 (Module 07) |
| v3.0 | 2026-03 | 添加附录 (Module 08) |
| v4.0 | 2026-04-11 | 基础架构完成 |
| **v5.0** | **2026-04-11** | **新增Modules 09-15，扩展数据科学、系统科学、认知社会科学** |

### 10.2 模块分类矩阵

| 类别 | 模块编号 | 数量 | 技术重点 |
|------|----------|------|----------|
| 数学基础 | 01 | 1 | 纯数学 |
| 形式方法 | 02, 05 | 2 | 逻辑、类型论 |
| 软件技术 | 03, 04 | 2 | 编程、工程 |
| 系统应用 | 06, 07 | 2 | 调度、统一 |
| **数据智能** | **09, 10** | **2** | **统计、信息论** ⭐新增 |
| **系统科学** | **11** | **1** | **复杂系统** ⭐新增 |
| **认知社会** | **12-15** | **4** | **决策、认知、语言、社会** ⭐新增 |

---

## 11. 文档维护

- 本文档随版本迭代更新
- 重大架构变更需同步更新
- 新增模块需补充架构说明
- 变更记录见项目 CHANGELOG

---

**导航**: [⬆️ 返回顶部](#formalscience-项目架构文档) | [📑 主索引](00_INDEX.md) | [📊 知识地图](00_MAP.md)
