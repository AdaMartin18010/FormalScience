# 依赖关系图

## 文档间依赖关系

```mermaid
graph TD
    %% 根节点
    ROOT[docs/Refactor/]
    
    %% 主要文档分类
    ROOT --> CONCEPT[01_概念定义/]
    ROOT --> STRUCT[02_结构设计/]
    ROOT --> SPEC[03_详细规范/]
    ROOT --> IMPL[04_实现指南/]
    ROOT --> REVIEW[05_审查检查/]
    
    %% 概念定义依赖
    CONCEPT --> C_CORE[核心概念.md]
    CONCEPT --> C_TERM[术语表.md]
    CONCEPT --> C_DOMAIN[领域模型.md]
    
    %% 结构设计依赖
    STRUCT --> S_ARCH[架构设计.md]
    STRUCT --> S_MODULE[模块划分.md]
    STRUCT --> S_API[接口设计.md]
    
    S_ARCH --> S_MODULE
    S_MODULE --> S_API
    
    %% 详细规范依赖
    SPEC --> SP_FMT[格式规范.md]
    SPEC --> SP_NAMING[命名规范.md]
    SPEC --> SP_PROC[流程规范.md]
    
    %% 实现指南依赖
    IMPL --> I_GUIDE[迁移指南.md]
    IMPL --> I_TOOLS[工具使用.md]
    IMPL --> I_EXAMPLE[示例代码.md]
    
    I_GUIDE --> I_EXAMPLE
    SP_FMT --> I_GUIDE
    
    %% 审查检查依赖
    REVIEW --> R_CHECK[检查清单.md]
    REVIEW --> R_QA[常见问题.md]
    REVIEW --> R_LOG[变更日志.md]
    
    %% 跨模块依赖
    C_CORE --> S_ARCH
    C_TERM --> SP_NAMING
    S_API --> I_GUIDE
    S_MODULE --> R_CHECK
```

---

## 概念间引用关系

```mermaid
graph LR
    %% 核心概念
    A[实体 Entity] --> B[属性 Attribute]
    A --> C[关系 Relation]
    A --> D[行为 Behavior]
    
    %% 属性细分
    B --> B1[基本属性]
    B --> B2[派生属性]
    B --> B3[关联属性]
    
    %% 关系细分
    C --> C1[一对一 1:1]
    C --> C2[一对多 1:N]
    C --> C3[多对多 N:M]
    
    %% 行为细分
    D --> D1[创建 Create]
    D --> D2[读取 Read]
    D --> D3[更新 Update]
    D --> D4[删除 Delete]
    
    %% 领域相关
    E[领域 Domain] --> A
    E --> F[限界上下文 Bounded Context]
    F --> G[聚合 Aggregate]
    G --> H[聚合根 Aggregate Root]
    H --> A
```

---

## 模块间接口

### 接口概览

| 模块 | 提供接口 | 依赖接口 | 说明 |
|------|----------|----------|------|
| 概念定义 | `IConcept` | - | 定义核心概念和术语 |
| 结构设计 | `IArchitecture`, `IModule` | `IConcept` | 基于概念进行结构设计 |
| 详细规范 | `ISpecification` | `IArchitecture` | 基于架构制定规范 |
| 实现指南 | `IGuide`, `ITool` | `ISpecification` | 基于规范提供实现指导 |
| 审查检查 | `IChecker` | `IGuide` | 验证实现是否符合规范 |

### 接口详细定义

```mermaid
classDiagram
    class IConcept {
        +String name
        +String definition
        +String[] synonyms
        +getDefinition() String
        +getRelations() IRelation[]
    }
    
    class IArchitecture {
        +String name
        +String description
        +IModule[] modules
        +getModules() IModule[]
        +validate() boolean
    }
    
    class IModule {
        +String name
        +String purpose
        +IInterface[] interfaces
        +getInterfaces() IInterface[]
        +dependsOn(IModule) boolean
    }
    
    class ISpecification {
        +String type
        +String version
        +IRule[] rules
        +validate(Object) boolean
        +getRules() IRule[]
    }
    
    class IGuide {
        +String title
        +String content
        +IExample[] examples
        +apply() void
    }
    
    class IChecker {
        +String checkType
        +check(Object) IResult
        +getReport() IReport
    }
    
    IArchitecture --> IConcept : uses
    IModule --> IArchitecture : belongs to
    ISpecification --> IModule : applies to
    IGuide --> ISpecification : implements
    IChecker --> IGuide : validates
```

---

## 文件引用矩阵

| 文件 | 被引用次数 | 引用其他文件数 | 关键依赖 |
|------|------------|----------------|----------|
| 核心概念.md | 5 | 1 | 术语表.md |
| 架构设计.md | 4 | 2 | 核心概念.md, 领域模型.md |
| 格式规范.md | 3 | 1 | 术语表.md |
| 迁移指南.md | 2 | 2 | 架构设计.md, 格式规范.md |
| 检查清单.md | 1 | 3 | 格式规范.md, 命名规范.md, 流程规范.md |

---

*最后更新: [自动更新日期]*
