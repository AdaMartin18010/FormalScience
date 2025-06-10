# n8n工作流平台全面架构与模式分析

## 目录

- [n8n工作流平台全面架构与模式分析](#n8n工作流平台全面架构与模式分析)
  - [目录](#目录)
  - [引言](#引言)
  - [n8n核心架构剖析](#n8n核心架构剖析)
    - [多层架构设计](#多层架构设计)
    - [事件驱动架构](#事件驱动架构)
    - [微服务兼容性](#微服务兼容性)
    - [插件架构](#插件架构)
  - [工作流设计模式全景图](#工作流设计模式全景图)
    - [基础设计模式](#基础设计模式)
    - [集成模式](#集成模式)
    - [数据处理模式](#数据处理模式)
    - [控制流模式](#控制流模式)
    - [错误处理模式](#错误处理模式)
  - [分布式工作流程系统架构组件](#分布式工作流程系统架构组件)
    - [1. 核心组件](#1-核心组件)
    - [2. 弹性组件](#2-弹性组件)
    - [3. 扩展组件](#3-扩展组件)
    - [4. 管理组件](#4-管理组件)
  - [分布式工作流系统设计考虑因素](#分布式工作流系统设计考虑因素)
    - [1. 可扩展性](#1-可扩展性)
    - [2. 一致性与持久性](#2-一致性与持久性)
    - [3. 故障恢复](#3-故障恢复)
    - [4. 可观测性](#4-可观测性)
    - [5. 安全性](#5-安全性)
  - [当前技术趋势](#当前技术趋势)

## 引言

n8n作为开源工作流自动化平台，提供了丰富的集成能力和灵活的架构设计。本文深入剖析n8n的架构设计、支持的工作流模式及其组合应用，探索其应用边界和局限性，为构建企业级自动化解决方案提供全面指导。

## n8n核心架构剖析

### 多层架构设计

n8n采用清晰的多层架构，每层职责明确，耦合度低：

1. **表现层**：
   - Vue.js前端框架
   - 响应式工作流编辑器
   - 交互式节点配置界面
   - 实时执行监控仪表板

2. **应用层**：
   - REST API服务（Express.js）
   - 认证与授权处理
   - 工作流验证与处理
   - 执行日志与监控

3. **领域层**：
   - 工作流定义模型
   - 节点类型与注册表
   - 执行引擎
   - 触发器管理

4. **基础设施层**：
   - 数据持久化
   - 队列管理
   - 缓存服务
   - 文件存储

多层架构实现代码示例（简化）：

```typescript
// 领域层：工作流执行引擎
export class WorkflowExecutor {
  private readonly nodeTypes: INodeTypes;
  private readonly workflow: Workflow;
  
  constructor(workflow: Workflow, nodeTypes: INodeTypes) {
    this.workflow = workflow;
    this.nodeTypes = nodeTypes;
  }
  
  async execute(workflowData: IWorkflowExecuteData): Promise<IExecuteWorkflowInfo> {
    // 构建执行图
    const runExecutionData = this.buildExecutionData(workflowData);
    
    // 执行工作流节点
    const executionOrder = this.getExecutionOrder();
    for (const nodeName of executionOrder) {
      await this.executeNode(nodeName, runExecutionData);
    }
    
    return this.generateExecutionOutput(runExecutionData);
  }
}

// 应用层：工作流服务
export class WorkflowService {
  private readonly workflowRepository: WorkflowRepository;
  private readonly nodeTypesLoader: NodeTypesLoader;
  
  async executeWorkflow(workflowId: string, inputData?: INodeParameters): Promise<IExecutionResult> {
    // 加载工作流定义
    const workflowData = await this.workflowRepository.get(workflowId);
    
    // 构建工作流执行器
    const nodeTypes = this.nodeTypesLoader.getAll();
    const workflow = new Workflow({ id: workflowId, nodes: workflowData.nodes, connections: workflowData.connections });
    const executor = new WorkflowExecutor(workflow, nodeTypes);
    
    // 执行工作流
    const executionResult = await executor.execute({ inputData });
    
    // 保存执行结果
    await this.workflowRepository.saveExecution(executionResult);
    
    return executionResult;
  }
}
```

### 事件驱动架构

n8n内部采用事件驱动架构，使系统各组件松耦合且可扩展：

1. **事件总线**：
   - 内部事件发布/订阅机制
   - 支持同步和异步事件处理
   - 工作流生命周期事件

2. **核心事件类型**：
   - 工作流事件：创建、更新、删除、激活、停用
   - 执行事件：开始、完成、失败、取消
   - 节点事件：执行前、执行后、执行失败
   - 系统事件：启动、关闭、配置变更

3. **事件处理程序**：
   - 日志记录器
   - 通知发送器
   - 触发器监听器
   - 缓存失效处理器

事件驱动架构示例：

```typescript
// 事件发布器
export class EventBus {
  private static instance: EventBus;
  private eventEmitter = new EventEmitter();
  
  static getInstance(): EventBus {
    if (!EventBus.instance) {
      EventBus.instance = new EventBus();
    }
    return EventBus.instance;
  }
  
  emit(eventName: WorkflowEventType, data: any): void {
    this.eventEmitter.emit(eventName, data);
  }
  
  on(eventName: WorkflowEventType, callback: (data: any) => void): void {
    this.eventEmitter.on(eventName, callback);
  }
}

// 使用事件总线
export class WorkflowExecutionManager {
  private readonly eventBus = EventBus.getInstance();
  
  async executeWorkflow(workflowId: string): Promise<void> {
    try {
      // 发布工作流开始事件
      this.eventBus.emit('workflow.execution.started', { workflowId, timestamp: Date.now() });
      
      // 执行工作流...
      
      // 发布工作流完成事件
      this.eventBus.emit('workflow.execution.completed', { 
        workflowId, 
        timestamp: Date.now(),
        executionTime: executionTime
      });
    } catch (error) {
      // 发布工作流失败事件
      this.eventBus.emit('workflow.execution.failed', { 
        workflowId, 
        timestamp: Date.now(),
        error: error.message
      });
      throw error;
    }
  }
}

// 事件监听器示例
class ExecutionMetricsCollector {
  constructor() {
    const eventBus = EventBus.getInstance();
    
    eventBus.on('workflow.execution.completed', this.recordSuccessMetrics.bind(this));
    eventBus.on('workflow.execution.failed', this.recordFailureMetrics.bind(this));
  }
  
  private recordSuccessMetrics(data: any): void {
    // 记录执行成功指标...
  }
  
  private recordFailureMetrics(data: any): void {
    // 记录执行失败指标...
  }
}
```

### 微服务兼容性

n8n虽然不是原生微服务架构，但设计上兼容微服务生态系统：

1. **服务隔离**：
   - 核心服务可独立部署
   - 执行器服务可水平扩展
   - 触发器处理可独立运行

2. **通信模式**：
   - RESTful API接口
   - 消息队列集成
   - 事件驱动通信

3. **配置管理**：
   - 环境变量配置
   - 文件配置
   - 动态配置

微服务兼容部署配置示例：

```yaml
# 工作流API服务
apiVersion: apps/v1
kind: Deployment
metadata:
  name: n8n-api
spec:
  replicas: 2
  selector:
    matchLabels:
      app: n8n-api
  template:
    metadata:
      labels:
        app: n8n-api
    spec:
      containers:
      - name: n8n-api
        image: n8nio/n8n
        args: ["start", "--apiOnly"]
        env:
        - name: DB_TYPE
          value: "postgresdb"
        - name: DB_POSTGRESDB_HOST
          value: "postgres-service"
        - name: QUEUE_BULL_REDIS_HOST
          value: "redis-service"
---
# 工作流执行器服务
apiVersion: apps/v1
kind: Deployment
metadata:
  name: n8n-worker
spec:
  replicas: 3
  selector:
    matchLabels:
      app: n8n-worker
  template:
    metadata:
      labels:
        app: n8n-worker
    spec:
      containers:
      - name: n8n-worker
        image: n8nio/n8n
        args: ["worker"]
        env:
        - name: DB_TYPE
          value: "postgresdb"
        - name: DB_POSTGRESDB_HOST
          value: "postgres-service"
        - name: QUEUE_BULL_REDIS_HOST
          value: "redis-service"
---
# 触发器服务
apiVersion: apps/v1
kind: Deployment
metadata:
  name: n8n-webhook
spec:
  replicas: 2
  selector:
    matchLabels:
      app: n8n-webhook
  template:
    metadata:
      labels:
        app: n8n-webhook
    spec:
      containers:
      - name: n8n-webhook
        image: n8nio/n8n
        args: ["webhook"]
        env:
        - name: DB_TYPE
          value: "postgresdb"
        - name: DB_POSTGRESDB_HOST
          value: "postgres-service"
        - name: QUEUE_BULL_REDIS_HOST
          value: "redis-service"
```

### 插件架构

n8n采用了高度模块化的插件架构，使扩展和定制变得简单：

1. **节点系统**：
   - 节点类型注册表
   - 动态节点加载
   - 节点版本控制

2. **Community节点**：
   - 自定义节点包
   - npm包管理
   - 社区贡献生态

3. **扩展点**：
   - 自定义认证方式
   - 自定义触发器
   - 自定义数据转换
   - 执行钩子(Hooks)

自定义节点示例：

```typescript
import { IExecuteFunctions } from 'n8n-core';
import { INodeExecutionData, INodeType, INodeTypeDescription } from 'n8n-workflow';

export class CustomAPINode implements INodeType {
  description: INodeTypeDescription = {
    displayName: '自定义API节点',
    name: 'customApiNode',
    icon: 'fa:plug',
    group: ['transform'],
    version: 1,
    description: '调用自定义API并处理响应',
    defaults: {
      name: '自定义API',
    },
    inputs: ['main'],
    outputs: ['main'],
    properties: [
      {
        displayName: 'API URL',
        name: 'url',
        type: 'string',
        default: '',
        placeholder: 'https://api.example.com/data',
        description: 'API的URL地址',
        required: true,
      },
      {
        displayName: '方法',
        name: 'method',
        type: 'options',
        options: [
          { name: 'GET', value: 'GET' },
          { name: 'POST', value: 'POST' },
          { name: 'PUT', value: 'PUT' },
          { name: 'DELETE', value: 'DELETE' },
        ],
        default: 'GET',
        description: 'HTTP请求方法',
      },
      {
        displayName: '请求体',
        name: 'body',
        type: 'json',
        displayOptions: {
          show: {
            method: ['POST', 'PUT'],
          },
        },
        default: '{}',
        description: 'JSON格式的请求数据',
      },
    ],
  };

  async execute(this: IExecuteFunctions): Promise<INodeExecutionData[][]> {
    const items = this.getInputData();
    const returnData: INodeExecutionData[] = [];
    
    // 获取参数
    const url = this.getNodeParameter('url', 0) as string;
    const method = this.getNodeParameter('method', 0) as string;
    
    // 处理每个输入项
    for (let i = 0; i < items.length; i++) {
      try {
        let options: any = {
          method,
          url,
          headers: {
            'Accept': 'application/json',
          },
        };
        
        // 对于POST和PUT请求，添加请求体
        if (['POST', 'PUT'].includes(method)) {
          const body = this.getNodeParameter('body', i) as string;
          options.body = JSON.parse(body);
          options.headers['Content-Type'] = 'application/json';
        }
        
        // 发送请求
        const response = await this.helpers.request(options);
        
        // 处理响应
        returnData.push({
          json: typeof response === 'string' ? JSON.parse(response) : response,
        });
      } catch (error) {
        // 处理错误
        if (this.continueOnFail()) {
          returnData.push({
            json: {
              error: error.message,
            },
          });
          continue;
        }
        throw error;
      }
    }
    
    return [returnData];
  }
}
```

## 工作流设计模式全景图

### 基础设计模式

n8n支持多种基础工作流设计模式：

1. **顺序模式(Sequence)**：
   - 节点按特定顺序执行
   - 每个节点等待前一节点完成
   - 数据线性流动
   - 适用于步骤明确、顺序固定的流程

   ```javascript
   // 顺序工作流示例
   const sequenceWorkflow = {
     nodes: [
       {
         id: "1",
         type: "n8n-nodes-base.HttpRequest",
         parameters: { url: "https://api.example.com/users" }
       },
       {
         id: "2",
         type: "n8n-nodes-base.SplitInBatches",
         parameters: { batchSize: 10 }
       },
       {
         id: "3",
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: "return items.map(item => { item.json.processed = true; return item; });"
         }
       },
       {
         id: "4",
         type: "n8n-nodes-base.EmailSend",
         parameters: {
           to: "admin@example.com",
           subject: "处理完成",
           text: "数据处理已完成，共 {{$json.length}} 条记录"
         }
       }
     ],
     connections: {
       "1": { main: [{ node: "2", type: "main", index: 0 }] },
       "2": { main: [{ node: "3", type: "main", index: 0 }] },
       "3": { main: [{ node: "4", type: "main", index: 0 }] }
     }
   };
   ```

2. **分支模式(Branching)**：
   - 基于条件的路径选择
   - IF节点实现条件分支
   - 多条执行路径
   - 适用于需要决策逻辑的流程

   ```javascript
   // 分支工作流示例
   const branchingWorkflow = {
     nodes: [
       {
         id: "1",
         type: "n8n-nodes-base.HttpRequest",
         parameters: { url: "https://api.example.com/orders" }
       },
       {
         id: "2",
         type: "n8n-nodes-base.IF",
         parameters: {
           conditions: {
             number: [
               {
                 value1: "={{$json.amount}}",
                 operation: "larger",
                 value2: 1000
               }
             ]
           }
         }
       },
       {
         id: "3", // 高价值订单处理
         type: "n8n-nodes-base.EmailSend",
         parameters: {
           to: "vip@example.com",
           subject: "高价值订单通知",
           text: "收到大额订单 {{$json.id}}，金额: {{$json.amount}}"
         }
       },
       {
         id: "4", // 常规订单处理
         type: "n8n-nodes-base.EmailSend",
         parameters: {
           to: "orders@example.com",
           subject: "新订单通知",
           text: "收到新订单 {{$json.id}}，金额: {{$json.amount}}"
         }
       },
       {
         id: "5", // 合并分支
         type: "n8n-nodes-base.Merge",
         parameters: { mode: "passThrough" }
       }
     ],
     connections: {
       "1": { main: [{ node: "2", type: "main", index: 0 }] },
       "2": {
         main: [
           { node: "3", type: "main", index: 0 }, // true 分支
           { node: "4", type: "main", index: 1 }  // false 分支
         ]
       },
       "3": { main: [{ node: "5", type: "main", index: 0 }] },
       "4": { main: [{ node: "5", type: "main", index: 1 }] }
     }
   };
   ```

3. **分割-合并模式(Split-Merge)**：
   - 数据流分割为多个子流
   - 并行处理各子流
   - 最后合并处理结果
   - 适用于需要并行处理的流程

   ```javascript
   // 分割-合并工作流示例
   const splitMergeWorkflow = {
     nodes: [
       {
         id: "1",
         type: "n8n-nodes-base.HttpRequest",
         parameters: { url: "https://api.example.com/customers" }
       },
       {
         id: "2",
         type: "n8n-nodes-base.SplitInBatches",
         parameters: { batchSize: 50 }
       },
       {
         id: "3", // 处理批次1
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: "// 处理第一组客户数据\nreturn items;"
         }
       },
       {
         id: "4", // 处理批次2
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: "// 处理第二组客户数据\nreturn items;"
         }
       },
       {
         id: "5",
         type: "n8n-nodes-base.Merge",
         parameters: { mode: "mergeByPosition" }
       },
       {
         id: "6",
         type: "n8n-nodes-base.Postgres",
         parameters: {
           operation: "insert",
           table: "processed_customers",
           schema: "public"
         }
       }
     ],
     connections: {
       "1": { main: [{ node: "2", type: "main", index: 0 }] },
       "2": {
         main: [
           { node: "3", type: "main", index: 0 },
           { node: "4", type: "main", index: 1 }
         ]
       },
       "3": { main: [{ node: "5", type: "main", index: 0 }] },
       "4": { main: [{ node: "5", type: "main", index: 1 }] },
       "5": { main: [{ node: "6", type: "main", index: 0 }] }
     }
   };
   ```

4. **循环模式(Looping)**：
   - 重复执行特定节点组
   - 基于集合或条件迭代
   - 支持每项循环和批量循环
   - 适用于需要重复处理的流程

   ```javascript
   // 循环工作流示例
   const loopingWorkflow = {
     nodes: [
       {
         id: "1",
         type: "n8n-nodes-base.HttpRequest",
         parameters: { url: "https://api.example.com/tasks" }
       },
       {
         id: "2",
         type: "n8n-nodes-base.SplitInBatches",
         parameters: { batchSize: 1 } // 每次一项
       },
       {
         id: "3",
         type: "n8n-nodes-base.HttpRequest",
         parameters: {
           url: "={{$json.detailUrl}}",
           method: "GET"
         }
       },
       {
         id: "4",
         type: "n8n-nodes-base.NoOp",
         parameters: {}
       },
       {
         id: "5", // 循环节点
         type: "n8n-nodes-base.Loop",
         parameters: {
           maxIterations: 10
         },
         typeVersion: 1
       }
     ],
     connections: {
       "1": { main: [{ node: "2", type: "main", index: 0 }] },
       "2": { main: [{ node: "3", type: "main", index: 0 }] },
       "3": { main: [{ node: "4", type: "main", index: 0 }] },
       "4": { main: [{ node: "5", type: "main", index: 0 }] },
       "5": { main: [{ node: "2", type: "main", index: 0 }] }
     }
   };
   ```

5. **发布-订阅模式(Pub-Sub)**：
   - 事件发布者与订阅者解耦
   - Webhook触发器实现
   - 支持多种订阅机制
   - 适用于事件驱动的异步流程

   ```javascript
   // 发布-订阅工作流示例
   const pubSubWorkflow = {
     nodes: [
       {
         id: "1", // 事件发布者（Webhook触发器）
         type: "n8n-nodes-base.Webhook",
         parameters: {
           path: "event-receiver",
           responseMode: "onReceived",
           responseData: "success"
         }
       },
       {
         id: "2", // 事件路由器
         type: "n8n-nodes-base.Switch",
         parameters: {
           value: "={{ $json.eventType }}",
           rules: [
             { value: "order.created", output: 0 },
             { value: "payment.completed", output: 1 },
             { value: "user.registered", output: 2 }
           ]
         }
       },
       {
         id: "3", // 订单处理订阅者
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: "// 处理新订单事件\nconsole.log('处理订单:', $json);\nreturn items;"
         }
       },
       {
         id: "4", // 支付处理订阅者
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: "// 处理支付完成事件\nconsole.log('处理支付:', $json);\nreturn items;"
         }
       },
       {
         id: "5", // 用户注册订阅者
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: "// 处理用户注册事件\nconsole.log('处理注册:', $json);\nreturn items;"
         }
       }
     ],
     connections: {
       "1": { main: [{ node: "2", type: "main", index: 0 }] },
       "2": {
         main: [
           { node: "3", type: "main", index: 0 },
           { node: "4", type: "main", index: 1 },
           { node: "5", type: "main", index: 2 }
         ]
       }
     }
   };
   ```

### 集成模式

n8n擅长的集成模式包括：

1. **API聚合模式**：
   - 将多个API调用组合为单一工作流
   - 统一不同API的响应格式
   - 处理认证与授权
   - 适用于需要跨系统数据集成的场景

   ```javascript
   // API聚合工作流示例
   const apiAggregationWorkflow = {
     nodes: [
       {
         id: "1", // 触发器
         type: "n8n-nodes-base.HttpRequest",
         parameters: {
           url: "https://api.example.com/customers/{{$json.customerId}}",
           authentication: "customerApiAuth"
         }
       },
       {
         id: "2", // 获取订单
         type: "n8n-nodes-base.HttpRequest",
         parameters: {
           url: "https://orders.example.com/api/customer/{{$json.id}}/orders",
           authentication: "orderApiAuth"
         }
       },
       {
         id: "3", // 获取支付记录
         type: "n8n-nodes-base.HttpRequest",
         parameters: {
           url: "https://payments.example.com/api/records",
           method: "POST",
           authentication: "paymentApiAuth",
           jsonParameters: true,
           bodyParameters: {
             customerId: "={{$node[\"1\"].json.id}}",
             timeframe: "last6months"
           }
         }
       },
       {
         id: "4", // 聚合数据
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             const customer = $node["1"].json;
             const orders = $node["2"].json;
             const payments = $node["3"].json;
             
             return [{
               json: {
                 customer: {
                   id: customer.id,
                   name: customer.name,
                   email: customer.email,
                   createdAt: customer.createdAt
                 },
                 orderHistory: orders.map(order => ({
                   id: order.id,
                   date: order.createdAt,
                   amount: order.totalAmount,
                   status: order.status
                 })),
                 paymentHistory: payments.records.map(payment => ({
                   id: payment.id,
                   date: payment.date,
                   amount: payment.amount,
                   method: payment.method
                 })),
                 summary: {
                   totalOrders: orders.length,
                   totalSpent: payments.records.reduce((sum, p) => sum + p.amount, 0),
                   lastOrderDate: orders.length > 0 ? orders[0].createdAt : null
                 }
               }
             }];
           `
         }
       },
       {
         id: "5", // 输出聚合数据
         type: "n8n-nodes-base.Respond",
         parameters: {
           respondWith: "json",
           responseBody: "={{ $json }}"
         }
       }
     ],
     connections: {
       "1": { main: [{ node: "2", type: "main", index: 0 }] },
       "2": { main: [{ node: "3", type: "main", index: 0 }] },
       "3": { main: [{ node: "4", type: "main", index: 0 }] },
       "4": { main: [{ node: "5", type: "main", index: 0 }] }
     }
   };
   ```

2. **API网关模式**：
   - 作为API前端门户
   - 请求路由与转发
   - 请求/响应转换
   - 速率限制与缓存
   - 适用于API管理场景

   ```javascript
   // API网关工作流示例
   const apiGatewayWorkflow = {
     nodes: [
       {
         id: "1", // API入口点
         type: "n8n-nodes-base.Webhook",
         parameters: {
           path: "api/:service/:endpoint",
           httpMethod: "ANY",
           responseMode: "lastNode"
         }
       },
       {
         id: "2", // 请求验证和限流
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 提取服务和端点信息
             const service = $node["1"].json.params.service;
             const endpoint = $node["1"].json.params.endpoint;
             const requestMethod = $node["1"].json.request.method;
             
             // 简单的限流逻辑（示例）
             const clientIp = $node["1"].json.headers['x-forwarded-for'] || '0.0.0.0';
             const requestKey = \`\${clientIp}:\${service}:\${endpoint}\`;
             
             // 在实际应用中，这里会检查Redis等系统进行限流
             // 这里简化为放行所有请求
             
             return [{
               json: {
                 service,
                 endpoint,
                 method: requestMethod,
                 body: $node["1"].json.body || {},
                 query: $node["1"].json.query || {},
                 headers: $node["1"].json.headers,
                 allowed: true
               }
             }];
           `
         }
       },
       {
         id: "3", // 路由决策
         type: "n8n-nodes-base.Switch",
         parameters: {
           value: "={{ $json.service }}",
           rules: [
             { value: "users", output: 0 },
             { value: "products", output: 1 },
             { value: "orders", output: 2 }
           ]
         }
       },
       {
         id: "4", // 用户服务路由
         type: "n8n-nodes-base.HttpRequest",
         parameters: {
           url: "=https://users-api.internal/{{ $json.endpoint }}",
           method: "={{ $json.method }}",
           sendBody: true,
           bodyParameters: "={{ $json.body }}",
           queryParameters: "={{ $json.query }}",
           options: {
             redirect: { follow: true }
           }
         }
       },
       {
         id: "5", // 产品服务路由
         type: "n8n-nodes-base.HttpRequest",
         parameters: {
           url: "=https://products-api.internal/{{ $json.endpoint }}",
           method: "={{ $json.method }}",
           sendBody: true,
           bodyParameters: "={{ $json.body }}",
           queryParameters: "={{ $json.query }}",
           options: {
             redirect: { follow: true }
           }
         }
       },
       {
         id: "6", // 订单服务路由
         type: "n8n-nodes-base.HttpRequest",
         parameters: {
           url: "=https://orders-api.internal/{{ $json.endpoint }}",
           method: "={{ $json.method }}",
           sendBody: true,
           bodyParameters: "={{ $json.body }}",
           queryParameters: "={{ $json.query }}",
           options: {
             redirect: { follow: true }
           }
         }
       },
       {
         id: "7", // 响应处理
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 添加通用响应头
             const responseHeaders = {
               'X-API-Gateway': 'n8n',
               'Cache-Control': 'no-cache',
               'Content-Type': 'application/json'
             };
             
             // 返回带有头信息的响应
             return [{
               json: $json,
               headers: responseHeaders
             }];
           `
         }
       }
     ],
     connections: {
       "1": { main: [{ node: "2", type: "main", index: 0 }] },
       "2": { main: [{ node: "3", type: "main", index: 0 }] },
       "3": {
         main: [
           { node: "4", type: "main", index: 0 },
           { node: "5", type: "main", index: 1 },
           { node: "6", type: "main", index: 2 }
         ]
       },
       "4": { main: [{ node: "7", type: "main", index: 0 }] },
       "5": { main: [{ node: "7", type: "main", index: 0 }] },
       "6": { main: [{ node: "7", type: "main", index: 0 }] }
     }
   };
   ```

3. **适配器模式**：
   - 转换不兼容接口
   - 数据格式标准化
   - 映射不同系统的字段
   - 适用于系统集成项目

   ```javascript
   // 适配器工作流示例
   const adapterWorkflow = {
     nodes: [
       {
         id: "1", // 源系统数据获取
         type: "n8n-nodes-base.SalesforceNode",
         parameters: {
           resource: "contact",
           operation: "getAll",
           returnAll: true
         }
       },
       {
         id: "2", // 适配器转换
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 将Salesforce联系人格式转换为HubSpot联系人格式
             return items.map(item => {
               return {
                 json: {
                   // HubSpot格式
                   properties: {
                     email: item.json.Email,
                     firstname: item.json.FirstName,
                     lastname: item.json.LastName,
                     phone: item.json.Phone,
                     company: item.json.Account?.Name || "",
                     address: [
                       item.json.MailingStreet || "",
                       item.json.MailingCity || "",
                       item.json.MailingState || "",
                       item.json.MailingPostalCode || "",
                       item.json.MailingCountry || ""
                     ].filter(Boolean).join(", "),
                     // 保存原始ID用于映射
                     salesforce_id: item.json.Id
                   }
                 }
               };
             });
           `
         }
       },
       {
         id: "3", // 目标系统写入
         type: "n8n-nodes-base.HubSpot",
         parameters: {
           resource: "contact",
           operation: "upsert",
           updateBy: "email"
         }
       },
       {
         id: "4", // 创建映射记录
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 创建ID映射记录
             return items.map((item, index) => {
               const originalItem = $node["1"].json[index];
               return {
                 json: {
                   sourceSystem: "Salesforce",
                   sourceId: originalItem.Id,
                   targetSystem: "HubSpot",
                   targetId: item.json.id,
                   mappedAt: new Date().toISOString()
                 }
               };
             });
           `
         }
       },
       {
         id: "5", // 保存映射记录
         type: "n8n-nodes-base.Postgres",
         parameters: {
           operation: "insert",
           schema: "public",
           table: "system_id_mappings",
           columns: "sourceSystem,sourceId,targetSystem,targetId,mappedAt",
           returnFields: "id"
         }
       }
     ],
     connections: {
       "1": { main: [{ node: "2", type: "main", index: 0 }] },
       "2": { main: [{ node: "3", type: "main", index: 0 }] },
       "3": { main: [{ node: "4", type: "main", index: 0 }] },
       "4": { main: [{ node: "5", type: "main", index: 0 }] }
     }
   };
   ```

4. **消息通道模式**：
   - 解耦消息发送者与接收者
   - 支持多种消息格式与通道
   - 消息排队与处理
   - 适用于解耦系统通信

   ```javascript
   // 消息通道工作流示例
   const messageChannelWorkflow = {
     nodes: [
       {
         id: "1", // 消息源（WebHook）
         type: "n8n-nodes-base.Webhook",
         parameters: {
           path: "incoming-message",
           httpMethod: "POST",
           responseMode: "onReceived"
         }
       },
       {
         id: "2", // 消息验证和标准化
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 验证和标准化消息格式
             try {
               const message = {
                 id: uuid(),
                 timestamp: new Date().toISOString(),
                 topic: $json.topic || "default",
                 payload: $json.payload || $json,
                 source: $json.source || "webhook",
                 priority: $json.priority || "normal"
               };
               
               return [{ json: message }];
             } catch (error) {
               return [{ json: { error: "Invalid message format" } }];
             }
             
             function uuid() {
               return 'xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx'.replace(/[xy]/g, c => {
                 const r = Math.random() * 16 | 0;
                 const v = c == 'x' ? r : (r & 0x3 | 0x8);
                 return v.toString(16);
               });
             }
           `
         }
       },
       {
         id: "3", // 消息路由（基于主题）
         type: "n8n-nodes-base.Switch",
         parameters: {
           value: "={{ $json.topic }}",
           rules: [
             { value: "customer", output: 0 },
             { value: "order", output: 1 },
             { value: "product", output: 2 }
           ],
           fallbackOutput: 3 // 默认主题
         }
       },
       {
         id: "4", // 客户消息队列
         type: "n8n-nodes-base.RabbitMQ",
         parameters: {
           operation: "publish",
           queue: "customer-events",
           options: {
             durable: true,
             persistent: true
           },
           content: "={{ $json }}"
         }
       },
       {
         id: "5", // 订单消息队列
         type: "n8n-nodes-base.RabbitMQ",
         parameters: {
           operation: "publish",
           queue: "order-events",
           options: {
             durable: true,
             persistent: true
           },
           content: "={{ $json }}"
         }
       },
       {
         id: "6", // 产品消息队列
         type: "n8n-nodes-base.RabbitMQ",
         parameters: {
           operation: "publish",
           queue: "product-events",
           options: {
             durable: true,
             persistent: true
           },
           content: "={{ $json }}"
         }
       },
       {
         id: "7", // 默认消息队列
         type: "n8n-nodes-base.RabbitMQ",
         parameters: {
           operation: "publish",
           queue: "default-events",
           options: {
             durable: true,
             persistent: true
           },
           content: "={{ $json }}"
         }
       },
       {
         id: "8", // 消息日志记录
         type: "n8n-nodes-base.Postgres",
         parameters: {
           operation: "insert",
           schema: "public",
           table: "message_log",
           columns: "message_id,topic,source,timestamp,payload",
           values: "={{ $json.id }},={{ $json.topic }},={{ $json.source }},={{ $json.timestamp }},={{ JSON.stringify($json.payload) }}"
         }
       }
     ],
     connections: {
       "1": { main: [{ node: "2", type: "main", index: 0 }] },
       "2": { main: [{ node: "3", type: "main", index: 0 }] },
       "3": {
         main: [
           { node: "4", type: "main", index: 0 },
           { node: "5", type: "main", index: 1 },
           { node: "6", type: "main", index: 2 },
           { node: "7", type: "main", index: 3 }
         ]
       },
       "4": { main: [{ node: "8", type: "main", index: 0 }] },
       "5": { main: [{ node: "8", type: "main", index: 0 }] },
       "6": { main: [{ node: "8", type: "main", index: 0 }] },
       "7": { main: [{ node: "8", type: "main", index: 0 }] }
     }
   };
   ```

5. **聚合器模式**：
   - 从多个分散源收集数据
   - 汇总数据以供分析或处理
   - 适用于报表和数据整合场景

   ```javascript
   // 聚合器工作流示例
   const aggregatorWorkflow = {
     nodes: [
       {
         id: "1", // 触发器（定时）
         type: "n8n-nodes-base.Cron",
         parameters: {
           triggerTimes: {
             hour: [0],
             minute: [0]
           }
         }
       },
       {
         id: "2", // 数据源1 - 销售数据
         type: "n8n-nodes-base.Postgres",
         parameters: {
           operation: "executeQuery",
           query: "SELECT * FROM sales WHERE date >= CURRENT_DATE - INTERVAL '1 day'"
         }
       },
       {
         id: "3", // 数据源2 - 网站访问
         type: "n8n-nodes-base.GoogleAnalytics",
         parameters: {
           endpoint: "reports",
           dimensions: [
             { name: "date" },
             { name: "pageTitle" }
           ],
           metrics: [
             { name: "sessions" },
             { name: "pageviews" },
             { name: "uniquePageviews" }
           ],
           dateRanges: [
             {
               startDate: "{{ $today.minus(1, \"days\").format(\"YYYY-MM-DD\") }}",
               endDate: "{{ $today.format(\"YYYY-MM-DD\") }}"
             }
           ]
         }
       },
       {
         id: "4", // 数据源3 - 客户支持
         type: "n8n-nodes-base.HttpRequest",
         parameters: {
           url: "https://support.example.com/api/tickets/daily",
           method: "GET",
           authentication: "genericCredentialType",
           queryParameters: {
             date: "={{ $today.minus(1, \"days\").format(\"YYYY-MM-DD\") }}"
           }
         }
       },
       {
         id: "5", // 数据汇总处理
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 获取昨日数据
             const salesData = $node["2"].json;
             const analyticsData = $node["3"].json;
             const supportData = $node["4"].json;
             
             // 计算销售指标
             const totalSales = salesData.reduce((sum, sale) => sum + parseFloat(sale.amount), 0);
             const orderCount = salesData.length;
             const averageOrderValue = orderCount > 0 ? totalSales / orderCount : 0;
             
             // 计算网站指标
             const totalSessions = analyticsData.reduce((sum, row) => sum + row.sessions, 0);
             const totalPageviews = analyticsData.reduce((sum, row) => sum + row.pageviews, 0);
             
             // 计算支持指标
             const newTickets = supportData.filter(ticket => ticket.status === 'new').length;
             const resolvedTickets = supportData.filter(ticket => ticket.status === 'resolved').length;
             
             // 创建汇总报告
             const dailyReport = {
               date: $today.minus(1, "days").format("YYYY-MM-DD"),
               sales: {
                 total: totalSales,
                 orderCount,
                 averageOrderValue
               },
               website: {
                 sessions: totalSessions,
                 pageviews: totalPageviews
               },
               support: {
                 newTickets,
                 resolvedTickets,
                 resolutionRate: newTickets > 0 ? resolvedTickets / newTickets : 0
               }
             };
             
             return [{ json: dailyReport }];
           `
         }
       },
       {
         id: "6", // 保存汇总报告到数据库
         type: "n8n-nodes-base.Postgres",
         parameters: {
           operation: "insert",
           schema: "public",
           table: "daily_reports",
           columns: "date,report_data",
           values: "={{ $json.date }},={{ JSON.stringify($json) }}"
         }
       },
       {
         id: "7", // 发送汇总报告
         type: "n8n-nodes-base.EmailSend",
         parameters: {
           from: "reports@example.com",
           to: "team@example.com",
           subject: "每日业务报告 - {{ $json.date }}",
           text: `日期: {{ $json.date }}
                    销售摘要:
                    - 总额: {{ $json.sales.total }} 元
                    - 订单数: {{ $json.sales.orderCount }}
                    - 平均订单金额: {{ $json.sales.averageOrderValue }} 元

                    网站摘要:
                    - 会话数: {{ $json.website.sessions }}
                    - 页面浏览量: {{ $json.website.pageviews }}

                    客户支持摘要:
                    - 新工单: {{ $json.support.newTickets }}
                    - 已解决工单: {{ $json.support.resolvedTickets }}
                    - 解决率: {{ Math.round($json.support.resolutionRate * 100) }}%
                            `
                            }
                        }
                        ],
            connections: {
            "1": { main: [{ node: "2", type: "main", index: 0 }] },
            "2": { main: [{ node: "3", type: "main", index: 0 }] },
            "3": { main: [{ node: "4", type: "main", index: 0 }] },
            "4": { main: [{ node: "5", type: "main", index: 0 }] },
            "5": { main: [{ node: "6", type: "main", index: 0 }] },
            "6": { main: [{ node: "7", type: "main", index: 0 }] }
            }
   };

   ```

### 数据处理模式

n8n提供多种数据处理模式：

1. **ETL模式(Extract-Transform-Load)**：
   - 从源系统提取数据
   - 转换和清洗数据
   - 加载到目标系统
   - 适用于数据迁移与仓库建设

   ```javascript
   // ETL工作流示例
   const etlWorkflow = {
     nodes: [
       {
         id: "1", // 触发器（定时）
         type: "n8n-nodes-base.Cron",
         parameters: {
           triggerTimes: {
             hour: [1], // 每天凌晨1点运行
             minute: [0]
           }
         }
       },
       {
         id: "2", // 提取 - 从MySQL提取数据
         type: "n8n-nodes-base.MySql",
         parameters: {
           operation: "executeQuery",
           query: `
             SELECT 
               o.order_id, 
               o.customer_id, 
               o.order_date, 
               o.status,
               c.email,
               c.name as customer_name,
               SUM(oi.quantity * oi.unit_price) as order_total
             FROM orders o
             JOIN customers c ON o.customer_id = c.id
             JOIN order_items oi ON o.order_id = oi.order_id
             WHERE o.order_date >= DATE_SUB(CURRENT_DATE, INTERVAL 1 DAY)
             GROUP BY o.order_id, o.customer_id, o.order_date, o.status, c.email, c.name
           `
         }
       },
       {
         id: "3", // 转换 - 数据清洗和标准化
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 数据转换和清洗
             return items.map(item => {
               // 标准化日期格式
               const orderDate = new Date(item.json.order_date);
               
               // 统一状态值
               let normalizedStatus;
               switch(item.json.status.toLowerCase()) {
                 case 'new':
                 case 'created':
                 case 'pending':
                   normalizedStatus = 'PENDING';
                   break;
                 case 'shipped':
                 case 'delivered':
                   normalizedStatus = 'COMPLETED';
                   break;
                 case 'cancelled':
                 case 'refunded':
                   normalizedStatus = 'CANCELLED';
                   break;
                 default:
                   normalizedStatus = 'OTHER';
               }
               
               // 生成唯一键
               const uniqueKey = \`ORD-\${item.json.order_id}\`;
               
               // 转换为目标格式
               return {
                 json: {
                   order_key: uniqueKey,
                   transaction_date: orderDate.toISOString().split('T')[0],
                   customer: {
                     id: item.json.customer_id,
                     name: item.json.customer_name,
                     email: item.json.email.toLowerCase()
                   },
                   order_details: {
                     source_id: item.json.order_id,
                     status: normalizedStatus,
                     amount: parseFloat(item.json.order_total).toFixed(2)
                   },
                   etl_timestamp: new Date().toISOString()
                 }
               };
             });
           `
         }
       },
       {
         id: "4", // 质量检查
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 数据质量检查
             const validItems = [];
             const errorItems = [];
             
             for (const item of items) {
               let isValid = true;
               const errors = [];
               
               // 检查必需字段
               if (!item.json.order_key) {
                 isValid = false;
                 errors.push('Missing order_key');
               }
               
               if (!item.json.transaction_date) {
                 isValid = false;
                 errors.push('Missing transaction_date');
               }
               
               if (!item.json.customer || !item.json.customer.id) {
                 isValid = false;
                 errors.push('Missing customer ID');
               }
               
               if (!item.json.order_details || !item.json.order_details.amount) {
                 isValid = false;
                 errors.push('Missing order amount');
               }
               
               // 检查数据类型
               if (isNaN(parseFloat(item.json.order_details.amount))) {
                 isValid = false;
                 errors.push('Invalid order amount');
               }
               
               // 分类处理
               if (isValid) {
                 validItems.push(item);
               } else {
                 errorItems.push({
                   json: {
                     original_data: item.json,
                     errors: errors,
                     timestamp: new Date().toISOString()
                   }
                 });
               }
             }
             
             // 设置节点输出
             return [validItems, errorItems];
           `
         },
         outputNames: ["validData", "errorData"]
       },
       {
         id: "5", // 加载 - 写入数据仓库
         type: "n8n-nodes-base.Postgres",
         parameters: {
           operation: "insert",
           schema: "dwh",
           table: "fact_orders",
           columns: "order_key,transaction_date,customer_id,customer_name,customer_email,order_status,order_amount,source_system,etl_timestamp",
           values: "={{ $json.order_key }},={{ $json.transaction_date }},={{ $json.customer.id }},={{ $json.customer.name }},={{ $json.customer.email }},={{ $json.order_details.status }},={{ $json.order_details.amount }},'mysql',={{ $json.etl_timestamp }}"
         }
       },
       {
         id: "6", // 错误记录处理
         type: "n8n-nodes-base.Postgres",
         parameters: {
           operation: "insert",
           schema: "etl",
           table: "error_log",
           columns: "source_data,error_messages,timestamp",
           values: "={{ JSON.stringify($json.original_data) }},={{ JSON.stringify($json.errors) }},={{ $json.timestamp }}"
         }
       },
       {
         id: "7", // ETL执行摘要
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             const validCount = $node["5"].runData.length || 0;
             const errorCount = $node["6"].runData.length || 0;
             const totalCount = validCount + errorCount;
             
             const summary = {
               timestamp: new Date().toISOString(),
               job: "daily_order_etl",
               source: "MySQL Orders",
               destination: "DWH Fact Orders",
               records: {
                 total: totalCount,
                 succeeded: validCount,
                 failed: errorCount,
                 successRate: totalCount > 0 ? (validCount / totalCount * 100).toFixed(2) + '%' : '0%'
               }
             };
             
             return [{ json: summary }];
           `
         }
       },
       {
         id: "8", // 记录ETL执行摘要
         type: "n8n-nodes-base.Postgres",
         parameters: {
           operation: "insert",
           schema: "etl",
           table: "job_history",
           columns: "job_name,execution_time,total_records,succeeded_records,failed_records,success_rate",
           values: "='daily_order_etl',={{ $json.timestamp }},={{ $json.records.total }},={{ $json.records.succeeded }},={{ $json.records.failed }},={{ $json.records.successRate }}"
         }
       }
     ],
     connections: {
       "1": { main: [{ node: "2", type: "main", index: 0 }] },
       "2": { main: [{ node: "3", type: "main", index: 0 }] },
       "3": { main: [{ node: "4", type: "main", index: 0 }] },
       "4": { 
         main: [
           { node: "5", type: "validData", index: 0 },
           { node: "6", type: "errorData", index: 0 }

```javascript
         main: [
           { node: "5", type: "validData", index: 0 },
           { node: "6", type: "errorData", index: 0 }
         ]
       },
       "5": { main: [{ node: "7", type: "main", index: 0 }] },
       "6": { main: [{ node: "7", type: "main", index: 0 }] },
       "7": { main: [{ node: "8", type: "main", index: 0 }] }
     }
   };
   ```

1. **数据验证与清洗模式**：
   - 检测和纠正数据错误
   - 数据标准化和格式转换
   - 处理缺失值和异常值
   - 适用于数据质量管理

   ```javascript
   // 数据验证与清洗工作流示例
   const dataValidationWorkflow = {
     nodes: [
       {
         id: "1", // CSV文件输入
         type: "n8n-nodes-base.ReadBinaryFile",
         parameters: {
           filePath: "/data/imports/customer_data.csv"
         }
       },
       {
         id: "2", // CSV解析
         type: "n8n-nodes-base.SplitInBatches",
         parameters: {
           options: {
             mode: "csv"
           }
         }
       },
       {
         id: "3", // 数据验证
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 定义验证规则
             const rules = {
               email: {
                 required: true,
                 regex: /^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$/
               },
               phone: {
                 required: false,
                 regex: /^\\+?[0-9\\s-()]{7,}$/
               },
               age: {
                 required: true,
                 min: 18,
                 max: 120
               },
               zipcode: {
                 required: true,
                 minLength: 5
               }
             };
             
             // 验证每条记录
             return items.map(item => {
               const errors = [];
               const warnings = [];
               
               // 检查每个字段
               for (const [field, rule] of Object.entries(rules)) {
                 const value = item.json[field];
                 
                 // 必填检查
                 if (rule.required && (value === undefined || value === null || value === '')) {
                   errors.push(`Missing required field: ${field}`);
                   continue;
                 }
                 
                 // 跳过空值的非必填字段
                 if (!rule.required && (value === undefined || value === null || value === '')) {
                   continue;
                 }
                 
                 // 正则表达式验证
                 if (rule.regex && !rule.regex.test(value)) {
                   errors.push(`Invalid format for ${field}: ${value}`);
                 }
                 
                 // 数值范围验证
                 if ((rule.min !== undefined || rule.max !== undefined) && !isNaN(value)) {
                   const numValue = parseFloat(value);
                   if (rule.min !== undefined && numValue < rule.min) {
                     errors.push(`${field} is below minimum: ${value} < ${rule.min}`);
                   }
                   if (rule.max !== undefined && numValue > rule.max) {
                     errors.push(`${field} is above maximum: ${value} > ${rule.max}`);
                   }
                 }
                 
                 // 字符串长度验证
                 if ((rule.minLength !== undefined || rule.maxLength !== undefined) && typeof value === 'string') {
                   if (rule.minLength !== undefined && value.length < rule.minLength) {
                     errors.push(`${field} is too short: ${value.length} < ${rule.minLength}`);
                   }
                   if (rule.maxLength !== undefined && value.length > rule.maxLength) {
                     warnings.push(`${field} is too long: ${value.length} > ${rule.maxLength}`);
                   }
                 }
               }
               
               // 添加验证结果
               item.json._validation = {
                 valid: errors.length === 0,
                 errors: errors,
                 warnings: warnings
               };
               
               return item;
             });
           `
         }
       },
       {
         id: "4", // 数据清洗
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 清洗功能
             return items.map(item => {
               // 只处理有效数据
               if (!item.json._validation.valid) {
                 return item;
               }
               
               const cleaned = { ...item.json };
               
               // 删除验证信息
               delete cleaned._validation;
               
               // 标准化电子邮件
               if (cleaned.email) {
                 cleaned.email = cleaned.email.trim().toLowerCase();
               }
               
               // 标准化电话号码
               if (cleaned.phone) {
                 // 移除所有非数字字符
                 cleaned.phone = cleaned.phone.replace(/[^0-9]/g, '');
                 
                 // 如果是美国号码且没有国家代码，添加+1
                 if (cleaned.phone.length === 10) {
                   cleaned.phone = '+1' + cleaned.phone;
                 } else if (cleaned.phone.length > 10 && !cleaned.phone.startsWith('+')) {
                   cleaned.phone = '+' + cleaned.phone;
                 }
               }
               
               // 标准化年龄为整数
               if (cleaned.age) {
                 cleaned.age = parseInt(cleaned.age, 10);
               }
               
               // 标准化邮政编码
               if (cleaned.zipcode) {
                 cleaned.zipcode = cleaned.zipcode.trim().padStart(5, '0');
               }
               
               // 标准化名称格式（首字母大写）
               if (cleaned.firstName) {
                 cleaned.firstName = cleaned.firstName.trim()
                   .toLowerCase()
                   .replace(/\\b\\w/g, c => c.toUpperCase());
               }
               
               if (cleaned.lastName) {
                 cleaned.lastName = cleaned.lastName.trim()
                   .toLowerCase()
                   .replace(/\\b\\w/g, c => c.toUpperCase());
               }
               
               // 添加完整名称
               if (cleaned.firstName && cleaned.lastName) {
                 cleaned.fullName = `${cleaned.firstName} ${cleaned.lastName}`;
               }
               
               // 添加创建时间戳
               cleaned.processedAt = new Date().toISOString();
               
               item.json = cleaned;
               return item;
             });
           `
         }
       },
       {
         id: "5", // 分离有效和无效数据
         type: "n8n-nodes-base.SplitInBatches",
         parameters: {
           options: {
             mode: "expression",
             batchSize: 1
           },
           valueToSplitOn: "={{ $json._validation ? $json._validation.valid : false }}"
         }
       },
       {
         id: "6", // 处理有效数据
         type: "n8n-nodes-base.Postgres",
         parameters: {
           operation: "insert",
           schema: "public",
           table: "clean_customers",
           columns: "email,phone,age,zipcode,first_name,last_name,full_name,processed_at",
           values: "={{ $json.email }},={{ $json.phone }},={{ $json.age }},={{ $json.zipcode }},={{ $json.firstName }},={{ $json.lastName }},={{ $json.fullName }},={{ $json.processedAt }}"
         }
       },
       {
         id: "7", // 记录无效数据
         type: "n8n-nodes-base.Postgres",
         parameters: {
           operation: "insert",
           schema: "public",
           table: "invalid_data_log",
           columns: "raw_data,errors,timestamp",
           values: "={{ JSON.stringify($json) }},={{ JSON.stringify($json._validation.errors) }},={{ $now.toISOString() }}"
         }
       },
       {
         id: "8", // 生成处理报告
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 获取处理数量
             const validCount = $node["6"].runData?.length || 0;
             const invalidCount = $node["7"].runData?.length || 0;
             const totalCount = validCount + invalidCount;
             
             // 生成报告
             const report = {
               timestamp: new Date().toISOString(),
               filename: "/data/imports/customer_data.csv",
               statistics: {
                 total: totalCount,
                 valid: validCount,
                 invalid: invalidCount,
                 validPercent: totalCount > 0 ? Math.round(validCount / totalCount * 100) : 0
               },
               status: totalCount > 0 && (validCount / totalCount) >= 0.9 ? "SUCCESS" : "WARNING"
             };
             
             return [{ json: report }];
           `
         }
       },
       {
         id: "9", // 发送处理报告
         type: "n8n-nodes-base.EmailSend",
         parameters: {
           to: "data-team@example.com",
           subject: "数据验证处理报告: {{ $json.status }}",
           text: `
            数据文件: {{ $json.filename }}
            处理时间: {{ $json.timestamp }}

            处理统计:

            - 总记录: {{ $json.statistics.total }}
            - 有效记录: {{ $json.statistics.valid }} ({{ $json.statistics.validPercent }}%)
            - 无效记录: {{ $json.statistics.invalid }}

            处理状态: {{ $json.status }}
            `
         }
       }
     ],
     connections: {
       "1": { main: [{ node: "2", type: "main", index: 0 }] },
       "2": { main: [{ node: "3", type: "main", index: 0 }] },
       "3": { main: [{ node: "4", type: "main", index: 0 }] },
       "4": { main: [{ node: "5", type: "main", index: 0 }] },
       "5": {
         main: [
           { node: "6", type: "main", index: 0 }, // 有效数据
           { node: "7", type: "main", index: 1 }  // 无效数据
         ]
       },
       "6": { main: [{ node: "8", type: "main", index: 0 }] },
       "7": { main: [{ node: "8", type: "main", index: 0 }] },
       "8": { main: [{ node: "9", type: "main", index: 0 }] }
     }
   };

   ```

1. **数据富集模式**：
   - 补充和增强数据信息
   - 整合多个数据源
   - 添加派生字段和计算值
   - 适用于创建完整数据视图

   ```javascript
   // 数据富集工作流示例
   const dataEnrichmentWorkflow = {
     nodes: [
       {
         id: "1", // 触发器 - 客户创建
         type: "n8n-nodes-base.CRM",
         parameters: {
           resource: "contact",
           operation: "getAll",
           limit: 10,
           filters: {
             status: "new"
           }
         }
       },
       {
         id: "2", // 基本客户数据格式化
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 格式化基本客户数据
             return items.map(item => {
               return {
                 json: {
                   contactId: item.json.id,
                   email: item.json.email.toLowerCase(),
                   fullName: \`\${item.json.firstName} \${item.json.lastName}\`,
                   company: item.json.company,
                   jobTitle: item.json.jobTitle,
                   phone: item.json.phone,
                   createdAt: item.json.createdAt,
                   enriched: {
                     status: "pending"
                   }
                 }
               };
             });
           `
         }
       },
       {
         id: "3", // 富集 - 社交媒体资料查询
         type: "n8n-nodes-base.HttpRequest",
         parameters: {
           url: "=https://api.socialmedia.example.com/v1/findByEmail",
           method: "POST",
           authentication: "genericCredentialType",
           jsonParameters: true,
           bodyParameters: {
             email: "={{ $json.email }}",
             fullName: "={{ $json.fullName }}"
           }
         }
       },
       {
         id: "4", // 富集 - 公司信息查询
         type: "n8n-nodes-base.HttpRequest",
         parameters: {
           url: "=https://api.company-data.example.com/v2/companies/search",
           method: "GET",
           authentication: "genericCredentialType",
           queryParameters: {
             name: "={{ $json.company }}"
           }
         }
       },
       {
         id: "5", // 富集 - 地理位置查询
         type: "n8n-nodes-base.HttpRequest",
         parameters: {
           url: "=https://api.geocode.example.com/lookup",
           method: "GET",
           authentication: "genericCredentialType",
           queryParameters: {
             company: "={{ $json.company }}",
             country: "={{ $json.country || 'US' }}"
           }
         }
       },
       {
         id: "6", // 富集 - 行业趋势数据
         type: "n8n-nodes-base.HttpRequest",
         parameters: {
           url: "=https://api.industry-trends.example.com/data",
           method: "GET",
           authentication: "genericCredentialType",
           queryParameters: {
             industry: "={{ $node['4'].json.industry || 'unknown' }}"
           }
         }
       },
       {
         id: "7", // 合并所有富集数据
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 获取各个富集数据源
             const contact = { ...item.json };
             const socialData = $node["3"].json || {};
             const companyData = $node["4"].json || {};
             const geoData = $node["5"].json || {};
             const industryData = $node["6"].json || {};
             
             // 创建富集的完整客户档案
             const enrichedContact = {
               // 基本信息
               contactId: contact.contactId,
               email: contact.email,
               fullName: contact.fullName,
               jobTitle: contact.jobTitle,
               phone: contact.phone,
               
               // 社交媒体数据
               social: {
                 profiles: socialData.profiles || [],
                 following: socialData.following || 0,
                 followers: socialData.followers || 0,
                 influence: socialData.influenceScore || 0,
                 platforms: socialData.platforms || []
               },
               
               // 公司信息
               company: {
                 name: contact.company,
                 website: companyData.website,
                 foundedYear: companyData.foundedYear,
                 employeeCount: companyData.employees,
                 revenue: companyData.annualRevenue,
                 industry: companyData.industry,
                 subIndustry: companyData.subIndustry,
                 publiclyTraded: companyData.publiclyTraded || false,
                 stockSymbol: companyData.stockSymbol
               },
               
               // 地理位置数据
               location: {
                 address: geoData.address,
                 city: geoData.city,
                 state: geoData.state,
                 country: geoData.country,
                 postalCode: geoData.postalCode,
                 coordinates: geoData.coordinates,
                 timezone: geoData.timezone
               },
               
               // 行业趋势
               industryInsights: {
                 growth: industryData.growth,
                 trendingTopics: industryData.trendingTopics || [],
                 marketSize: industryData.marketSize,
                 competitorCount: industryData.competitors?.length || 0,
                 topCompetitors: industryData.competitors?.slice(0, 5) || []
               },
               
               // 派生的预测分析
               predictions: {
                 leadScore: calculateLeadScore(socialData, companyData, industryData),
                 lifetimeValueEstimate: estimateLTV(companyData, industryData),
                 salesCycleDays: estimateSalesCycle(companyData, industryData),
                 propensityToBuy: calculateBuyingPropensity(socialData, companyData)
               },
               
               // 元数据
               enriched: {
                 status: "completed",
                 enrichedAt: new Date().toISOString(),
                 sources: [
                   socialData.source ? "social" : null,
                   companyData.source ? "company" : null,
                   geoData.source ? "geo" : null,
                   industryData.source ? "industry" : null
                 ].filter(Boolean)
               }
             };
             
             return [{ json: enrichedContact }];
             
             // 辅助函数
             function calculateLeadScore(social, company, industry) {
               // 简单的评分算法
               let score = 50; // 基础分
               
               // 社交影响力
               if (social.influenceScore > 70) score += 15;
               else if (social.influenceScore > 40) score += 10;
               
               // 公司规模
               if (company.employees > 1000) score += 20;
               else if (company.employees > 100) score += 10;
               
               // 行业增长
               if (industry.growth > 10) score += 15;
               else if (industry.growth > 5) score += 10;
               else if (industry.growth < 0) score -= 10;
               
               return Math.min(100, Math.max(0, score));
             }
             
             function estimateLTV(company, industry) {
               if (!company.annualRevenue) return null;
               
               // 基于行业和公司规模的估算
               const baseMultiplier = 0.05; // 基础乘数
               let industryMultiplier = 1;
               
               // 根据行业调整乘数
               switch(company.industry?.toLowerCase()) {
                 case 'technology': industryMultiplier = 1.5; break;
                 case 'healthcare': industryMultiplier = 1.3; break;
                 case 'finance': industryMultiplier = 1.4; break;
                 case 'manufacturing': industryMultiplier = 0.8; break;
                 case 'retail': industryMultiplier = 0.7; break;
               }
               
               // 计算估计LTV
               return Math.round(company.annualRevenue * baseMultiplier * industryMultiplier);
             }
             
             function estimateSalesCycle(company, industry) {
               // 基础销售周期
               let baseCycleDays = 45;
               
               // 根据公司规模调整
               if (company.employees > 5000) baseCycleDays += 45;
               else if (company.employees > 1000) baseCycleDays += 30;
               else if (company.employees > 100) baseCycleDays += 15;
               
               // 根据行业调整
               switch(company.industry?.toLowerCase()) {
                 case 'government': baseCycleDays += 60; break;
                 case 'healthcare': baseCycleDays += 30; break;
                 case 'education': baseCycleDays += 45; break;
                 case 'technology': baseCycleDays -= 15; break;
               }
               
               return baseCycleDays;
             }
             
             function calculateBuyingPropensity(social, company) {
               // 简单的购买倾向评分
               let score = 3; // 中等倾向(1-5)
               
               // 公司因素
               if (company.employees > 1000) score += 1;
               if (company.annualRevenue > 10000000) score += 1;
               
               // 社交影响因素
               if (social.profiles?.length > 3) score += 0.5;
               if (social.influenceScore > 60) score += 0.5;
               
               return Math.min(5, Math.max(1, score));
             }
           `
         }
       },
       {
         id: "8", // 保存富集数据
         type: "n8n-nodes-base.CRM",
         parameters: {
           resource: "contact",
           operation: "update",
           contactId: "={{ $json.contactId }}",
           updateFields: {
             // 基本信息更新
             enrichmentStatus: "completed",
             enrichmentDate: "={{ $json.enriched.enrichedAt }}",
             
             // 社交媒体数据
             socialInfluence: "={{ $json.social.influence }}",
             socialProfiles: "={{ JSON.stringify($json.social.profiles) }}",
             
             // 公司附加信息
             companySize: "={{ $json.company.employeeCount }}",
             companyRevenue: "={{ $json.company.revenue }}",
             industry: "={{ $json.company.industry }}",
             subIndustry: "={{ $json.company.subIndustry }}",
             
             // 位置信息
             city: "={{ $json.location.city }}",
             state: "={{ $json.location.state }}",
             country: "={{ $json.location.country }}",
             
             // 预测分析
             leadScore: "={{ $json.predictions.leadScore }}",
             estimatedLtv: "={{ $json.predictions.lifetimeValueEstimate }}",
             salesCycleDays: "={{ $json.predictions.salesCycleDays }}",
             buyingPropensity: "={{ $json.predictions.propensityToBuy }}"
           }
         }
       },
       {
         id: "9", // 存储完整富集数据
         type: "n8n-nodes-base.Postgres",
         parameters: {
           operation: "insert",
           schema: "public",
           table: "enriched_contacts",
           columns: "contact_id,enrichment_data,enriched_at",
           values: "={{ $json.contactId }},={{ JSON.stringify($json) }},={{ $json.enriched.enrichedAt }}"
         }
       },
       {
         id: "10", // 触发销售通知
         type: "n8n-nodes-base.IF",
         parameters: {
           conditions: {
             number: [
               {
                 value1: "={{ $json.predictions.leadScore }}",
                 operation: "larger",
                 value2: 70
               }
             ]
           }
         }
       },
       {
         id: "11", // 高价值潜在客户通知
         type: "n8n-nodes-base.Slack",
         parameters: {
           channel: "sales-team",
           text: `🔥 高价值潜在客户提醒 🔥
                        
                姓名: {{ $json.fullName }}
                公司: {{ $json.company.name }}
                行业: {{ $json.company.industry }}
                预测分数: {{ $json.predictions.leadScore }}/100
                估计价值: ${{ $json.predictions.lifetimeValueEstimate }}
                        
                查看CRM: https://crm.example.com/contacts/{{ $json.contactId }}`,
           otherOptions: {
             attachments: [
               {
                 color: "#36a64f",
                 fields: [
                   {
                     title: "社交影响力",
                     value: "{{ $json.social.influence }}/100",
                     short: true
                   },
                   {
                     title: "购买倾向",
                     value: "{{ $json.predictions.propensityToBuy }}/5",
                     short: true
                   },
                   {
                     title: "预计销售周期",
                     value: "{{ $json.predictions.salesCycleDays }} 天",
                     short: true
                   },
                   {
                     title: "所在位置",
                     value: "{{ $json.location.city }}, {{ $json.location.state }}, {{ $json.location.country }}",
                     short: true
                   }
                 ]
               }
             ]
           }
         }
       }
     ],
     connections: {
       "1": { main: [{ node: "2", type: "main", index: 0 }] },
       "2": { main: [{ node: "3", type: "main", index: 0 }] },
       "3": { main: [{ node: "4", type: "main", index: 0 }] },
       "4": { main: [{ node: "5", type: "main", index: 0 }] },
       "5": { main: [{ node: "6", type: "main", index: 0 }] },
       "6": { main: [{ node: "7", type: "main", index: 0 }] },
       "7": { main: [{ node: "8", type: "main", index: 0 }] },
       "8": { main: [{ node: "9", type: "main", index: 0 }] },
       "9": { main: [{ node: "10", type: "main", index: 0 }] },
       "10": {
         main: [
           { node: "11", type: "main", index: 0 } // 仅当分数高时通知
         ]
       }
     }
   };
   ```

1. **数据分析与汇总模式**：
   - 计算统计指标和KPI
   - 数据分组与聚合
   - 生成报表和可视化
   - 适用于数据分析和业务智能

   ```javascript
   // 数据分析与汇总工作流示例
   const dataAnalysisWorkflow = {
     nodes: [
       {
         id: "1", // 触发器（定时）
         type: "n8n-nodes-base.Cron",
         parameters: {
           triggerTimes: {
             weekDay: [1], // 每周一
             hour: [7],    // 早上7点
             minute: [0]
           }
         }
       },
       {
         id: "2", // 查询销售数据
         type: "n8n-nodes-base.Postgres",
         parameters: {
           operation: "executeQuery",
           query: `
             SELECT 
               o.id as order_id,
               o.created_at,
               o.total_amount,
               o.status,
               o.customer_id,
               c.customer_segment,
               p.product_id,
               p.product_name,
               p.category,
               p.unit_price,
               oi.quantity,
               (p.unit_price * oi.quantity) as line_total,
               s.sales_rep_id,
               s.region
             FROM 
               orders o
               JOIN customers c ON o.customer_id = c.id
               JOIN order_items oi ON o.id = oi.order_id
               JOIN products p ON oi.product_id = p.id
               JOIN sales_reps s ON o.sales_rep_id = s.id
             WHERE 
               o.created_at >= date_trunc('week', current_date - interval '1 week')
               AND o.created_at < date_trunc('week', current_date)
           `
         }
       },
       {
         id: "3", // 按区域分析销售
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 按区域分析数据
             const salesByRegion = {};
             
             // 处理所有销售记录
             for (const item of items) {
               const sale = item.json;
               const region = sale.region;
               
               // 初始化区域
               if (!salesByRegion[region]) {
                 salesByRegion[region] = {
                   totalSales: 0,
                   orderCount: 0,
                   averageOrderValue: 0,
                   productCategories: {},
                   topProducts: []
                 };
               }
               
               // 更新区域统计
               salesByRegion[region].totalSales += parseFloat(sale.line_total);
               
               // 追踪订单（去重）
               if (!salesByRegion[region][sale.order_id]) {
                 salesByRegion[region][sale.order_id] = true;
                 salesByRegion[region].orderCount++;
               }
               
               // 更新产品类别
               const category = sale.category;
               if (!salesByRegion[region].productCategories[category]) {
                 salesByRegion[region].productCategories[category] = 0;
               }
               salesByRegion[region].productCategories[category] += parseFloat(sale.line_total);
               
               // 更新产品销售
               const productIndex = salesByRegion[region].topProducts.findIndex(p => p.id === sale.product_id);
               if (productIndex >= 0) {
                 salesByRegion[region].topProducts[productIndex].sales += parseFloat(sale.line_total);
                 salesByRegion[region].topProducts[productIndex].sales += parseFloat(sale.line_total);
                 salesByRegion[region].topProducts[productIndex].quantity += parseInt(sale.quantity);
               } else {
                 salesByRegion[region].topProducts.push({
                   id: sale.product_id,
                   name: sale.product_name,
                   sales: parseFloat(sale.line_total),
                   quantity: parseInt(sale.quantity)
                 });
               }
             }
             
             // 计算每个区域的平均订单价值和排序产品
             for (const region in salesByRegion) {
               // 平均订单价值
               salesByRegion[region].averageOrderValue = 
                 salesByRegion[region].orderCount > 0 
                   ? (salesByRegion[region].totalSales / salesByRegion[region].orderCount).toFixed(2)
                   : 0;
                   
               // 按销售额排序产品
               salesByRegion[region].topProducts.sort((a, b) => b.sales - a.sales);
               
               // 只保留前5个产品
               salesByRegion[region].topProducts = salesByRegion[region].topProducts.slice(0, 5);
               
               // 删除临时订单跟踪
               for (const key in salesByRegion[region]) {
                 if (key.startsWith('order_')) {
                   delete salesByRegion[region][key];
                 }
               }
             }
             
             // 返回结构化数据
             return [{
               json: {
                 reportType: "regionalSalesAnalysis",
                 period: "上周",
                 generatedAt: new Date().toISOString(),
                 data: salesByRegion
               }
             }];
           `
         }
       },
       {
         id: "4", // 按客户细分分析
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 按客户细分分析数据
             const salesBySegment = {};
             
             // 处理所有销售记录
             for (const item of items) {
               const sale = item.json;
               const segment = sale.customer_segment || 'Unknown';
               
               // 初始化客户细分
               if (!salesBySegment[segment]) {
                 salesBySegment[segment] = {
                   totalSales: 0,
                   orderCount: 0,
                   customerCount: 0,
                   averageOrderValue: 0,
                   customers: new Set()
                 };
               }
               
               // 更新细分统计
               salesBySegment[segment].totalSales += parseFloat(sale.line_total);
               
               // 追踪订单（去重）
               if (!salesBySegment[segment][sale.order_id]) {
                 salesBySegment[segment][sale.order_id] = true;
                 salesBySegment[segment].orderCount++;
               }
               
               // 追踪客户（去重）
               salesBySegment[segment].customers.add(sale.customer_id);
             }
             
             // 计算最终指标并清理
             for (const segment in salesBySegment) {
               // 客户数量
               salesBySegment[segment].customerCount = salesBySegment[segment].customers.size;
               delete salesBySegment[segment].customers; // 移除Set
               
               // 平均订单价值
               salesBySegment[segment].averageOrderValue = 
                 salesBySegment[segment].orderCount > 0 
                   ? (salesBySegment[segment].totalSales / salesBySegment[segment].orderCount).toFixed(2)
                   : 0;
                   
               // 每客户平均价值
               salesBySegment[segment].averageCustomerValue = 
                 salesBySegment[segment].customerCount > 0
                   ? (salesBySegment[segment].totalSales / salesBySegment[segment].customerCount).toFixed(2)
                   : 0;
                   
               // 每客户平均订单数
               salesBySegment[segment].ordersPerCustomer = 
                 salesBySegment[segment].customerCount > 0
                   ? (salesBySegment[segment].orderCount / salesBySegment[segment].customerCount).toFixed(2)
                   : 0;
                   
               // 删除临时订单跟踪
               for (const key in salesBySegment[segment]) {
                 if (key.startsWith('order_')) {
                   delete salesBySegment[segment][key];
                 }
               }
             }
             
             // 返回结构化数据
             return [{
               json: {
                 reportType: "customerSegmentAnalysis",
                 period: "上周",
                 generatedAt: new Date().toISOString(),
                 data: salesBySegment
               }
             }];
           `
         }
       },
       {
         id: "5", // 按产品类别分析
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 按产品类别分析数据
             const salesByCategory = {};
             
             // 处理所有销售记录
             for (const item of items) {
               const sale = item.json;
               const category = sale.category || 'Uncategorized';
               
               // 初始化类别
               if (!salesByCategory[category]) {
                 salesByCategory[category] = {
                   totalSales: 0,
                   totalQuantity: 0,
                   averageUnitPrice: 0,
                   productCount: 0,
                   products: new Set(),
                   topProducts: []
                 };
               }
               
               // 更新类别统计
               salesByCategory[category].totalSales += parseFloat(sale.line_total);
               salesByCategory[category].totalQuantity += parseInt(sale.quantity);
               
               // 追踪产品（去重）
               salesByCategory[category].products.add(sale.product_id);
               
               // 更新产品销售
               const productIndex = salesByCategory[category].topProducts.findIndex(p => p.id === sale.product_id);
               if (productIndex >= 0) {
                 salesByCategory[category].topProducts[productIndex].sales += parseFloat(sale.line_total);
                 salesByCategory[category].topProducts[productIndex].quantity += parseInt(sale.quantity);
               } else {
                 salesByCategory[category].topProducts.push({
                   id: sale.product_id,
                   name: sale.product_name,
                   sales: parseFloat(sale.line_total),
                   quantity: parseInt(sale.quantity),
                   unitPrice: parseFloat(sale.unit_price)
                 });
               }
             }
             
             // 计算最终指标并清理
             for (const category in salesByCategory) {
               // 产品数量
               salesByCategory[category].productCount = salesByCategory[category].products.size;
               delete salesByCategory[category].products; // 移除Set
               
               // 平均单价
               salesByCategory[category].averageUnitPrice = 
                 salesByCategory[category].totalQuantity > 0 
                   ? (salesByCategory[category].totalSales / salesByCategory[category].totalQuantity).toFixed(2)
                   : 0;
                   
               // 按销售额排序产品
               salesByCategory[category].topProducts.sort((a, b) => b.sales - a.sales);
               
               // 只保留前5个产品
               salesByCategory[category].topProducts = salesByCategory[category].topProducts.slice(0, 5);
             }
             
             // 返回结构化数据
             return [{
               json: {
                 reportType: "productCategoryAnalysis",
                 period: "上周",
                 generatedAt: new Date().toISOString(),
                 data: salesByCategory
               }
             }];
           `
         }
       },
       {
         id: "6", // 时间趋势分析
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 按日期分析数据
             const salesByDate = {};
             
             // 处理所有销售记录
             for (const item of items) {
               const sale = item.json;
               // 提取日期部分
               const date = sale.created_at.split('T')[0];
               
               // 初始化日期
               if (!salesByDate[date]) {
                 salesByDate[date] = {
                   totalSales: 0,
                   orderCount: 0,
                   itemCount: 0,
                   uniqueCustomers: new Set()
                 };
               }
               
               // 更新日期统计
               salesByDate[date].totalSales += parseFloat(sale.line_total);
               salesByDate[date].itemCount += parseInt(sale.quantity);
               
               // 追踪订单（去重）
               if (!salesByDate[date][sale.order_id]) {
                 salesByDate[date][sale.order_id] = true;
                 salesByDate[date].orderCount++;
               }
               
               // 追踪客户（去重）
               salesByDate[date].uniqueCustomers.add(sale.customer_id);
             }
             
             // 整理数据和计算趋势
             const dateKeys = Object.keys(salesByDate).sort();
             const dailyData = [];
             
             for (const date of dateKeys) {
               // 计算当天指标
               const customerCount = salesByDate[date].uniqueCustomers.size;
               const averageOrderValue = salesByDate[date].orderCount > 0
                 ? salesByDate[date].totalSales / salesByDate[date].orderCount
                 : 0;
                 
               // 添加到日数据数组
               dailyData.push({
                 date,
                 totalSales: salesByDate[date].totalSales,
                 orderCount: salesByDate[date].orderCount,
                 itemCount: salesByDate[date].itemCount,
                 customerCount,
                 averageOrderValue
               });
               
               // 清理临时字段
               delete salesByDate[date].uniqueCustomers;
               for (const key in salesByDate[date]) {
                 if (key.startsWith('order_')) {
                   delete salesByDate[date][key];
                 }
               }
             }
             
             // 计算趋势变化
             const trends = {
               salesTrend: calculateTrend(dailyData, 'totalSales'),
               orderCountTrend: calculateTrend(dailyData, 'orderCount'),
               customerCountTrend: calculateTrend(dailyData, 'customerCount'),
               aovTrend: calculateTrend(dailyData, 'averageOrderValue')
             };
             
             // 返回结构化数据
             return [{
               json: {
                 reportType: "salesTrendAnalysis",
                 period: "上周",
                 generatedAt: new Date().toISOString(),
                 dailyData,
                 trends
               }
             }];
             
             // 辅助函数 - 计算趋势
             function calculateTrend(data, field) {
               if (data.length < 2) return { change: 0, percentChange: 0 };
               
               const firstValue = data[0][field];
               const lastValue = data[data.length - 1][field];
               
               const change = lastValue - firstValue;
               const percentChange = firstValue !== 0 
                 ? (change / firstValue * 100).toFixed(2)
                 : 0;
                 
               return {
                 change: change.toFixed(2),
                 percentChange,
                 direction: change > 0 ? 'up' : change < 0 ? 'down' : 'flat'
               };
             }
           `
         }
       },
       {
         id: "7", // 汇总分析报告
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 从各分析节点获取结果
             const regionalAnalysis = $node["3"].json;
             const segmentAnalysis = $node["4"].json;
             const categoryAnalysis = $node["5"].json;
             const trendAnalysis = $node["6"].json;
             
             // 计算整体汇总指标
             const allSales = items.map(item => item.json);
             
             // 基本汇总指标
             const totalSalesAmount = allSales.reduce((sum, sale) => sum + parseFloat(sale.line_total), 0);
             const uniqueOrderIds = new Set(allSales.map(sale => sale.order_id));
             const totalOrders = uniqueOrderIds.size;
             const uniqueCustomerIds = new Set(allSales.map(sale => sale.customer_id));
             const totalCustomers = uniqueCustomerIds.size;
             const totalItems = allSales.reduce((sum, sale) => sum + parseInt(sale.quantity), 0);
             const averageOrderValue = totalOrders > 0 ? (totalSalesAmount / totalOrders).toFixed(2) : 0;
             
             // 寻找表现最好的指标
             const bestPerformingRegion = findBestPerforming(regionalAnalysis.data, 'totalSales');
             const bestPerformingSegment = findBestPerforming(segmentAnalysis.data, 'totalSales');
             const bestPerformingCategory = findBestPerforming(categoryAnalysis.data, 'totalSales');
             
             // 创建执行摘要
             const executiveSummary = {
               period: "上周",
               generatedAt: new Date().toISOString(),
               overallPerformance: {
                 totalSales: totalSalesAmount.toFixed(2),
                 totalOrders,
                 totalCustomers,
                 totalItems,
                 averageOrderValue
               },
               keyHighlights: [
                 \`总销售额为 \${totalSalesAmount.toFixed(2)} 元，来自 \${totalOrders} 个订单\`,
                 \`平均订单金额为 \${averageOrderValue} 元\`,
                 \`最佳表现区域是 \${bestPerformingRegion.key}，销售额 \${bestPerformingRegion.value.toFixed(2)} 元\`,
                 \`最佳表现客户细分是 \${bestPerformingSegment.key}，销售额 \${bestPerformingSegment.value.toFixed(2)} 元\`,
                 \`最佳表现产品类别是 \${bestPerformingCategory.key}，销售额 \${bestPerformingCategory.value.toFixed(2)} 元\`,
                 \`销售趋势: \${trendAnalysis.trends.salesTrend.direction === 'up' ? '上升' : trendAnalysis.trends.salesTrend.direction === 'down' ? '下降' : '持平'} \${Math.abs(trendAnalysis.trends.salesTrend.percentChange)}%\`
               ],
               regionalPerformance: regionalAnalysis,
               segmentPerformance: segmentAnalysis,
               categoryPerformance: categoryAnalysis,
               trendPerformance: trendAnalysis
             };
             
             return [{ json: executiveSummary }];
             
             // 辅助函数 - 寻找表现最好的类别
             function findBestPerforming(data, field) {
               let bestKey = null;
               let bestValue = -Infinity;
               
               for (const key in data) {
                 const value = parseFloat(data[key][field]);
                 if (value > bestValue) {
                   bestKey = key;
                   bestValue = value;
                 }
               }
               
               return { key: bestKey, value: bestValue };
             }
           `
         }
       },
       {
         id: "8", // 生成PDF报告
         type: "n8n-nodes-base.HttpRequest",
         parameters: {
           url: "https://pdf-generator.example.com/api/generate",
           method: "POST",
           authentication: "genericCredentialType",
           jsonParameters: true,
           bodyParameters: {
             template: "weekly-sales-report",
             data: "={{ $json }}"
           }
         }
       },
       {
         id: "9", // 保存PDF报告
         type: "n8n-nodes-base.WriteBinaryFile",
         parameters: {
           filePath: "=/reports/sales-report-{{ $json.period | replace(' ', '-') }}-{{ $today.format('YYYY-MM-DD') }}.pdf",
           binaryPropertyName: "data"
         }
       },
       {
         id: "10", // 发送报告邮件
         type: "n8n-nodes-base.EmailSend",
         parameters: {
           to: "executives@example.com",
           cc: "sales-managers@example.com",
           subject: "每周销售分析报告 - {{ $json.period }}",
           text: `
            尊敬的团队成员：

            附件是本周的销售分析报告。主要亮点：

            - {{ $json.keyHighlights[0] }}
            - {{ $json.keyHighlights[1] }}
            - {{ $json.keyHighlights[2] }}
            - {{ $json.keyHighlights[3] }}
            - {{ $json.keyHighlights[4] }}
            - {{ $json.keyHighlights[5] }}

            完整报告请见附件。

            分析团队
           `,
           attachments: [
             {
               binary: "data"
             }
           ]
         }
       }
     ],
     connections: {
       "1": { main: [{ node: "2", type: "main", index: 0 }] },
       "2": { main: [{ node: "3", type: "main", index: 0 }] },
       "2": { main: [{ node: "4", type: "main", index: 0 }] },
       "2": { main: [{ node: "5", type: "main", index: 0 }] },
       "2": { main: [{ node: "6", type: "main", index: 0 }] },
       "3": { main: [{ node: "7", type: "main", index: 0 }] },
       "4": { main: [{ node: "7", type: "main", index: 0 }] },
       "5": { main: [{ node: "7", type: "main", index: 0 }] },
       "6": { main: [{ node: "7", type: "main", index: 0 }] },
       "7": { main: [{ node: "8", type: "main", index: 0 }] },
       "8": { main: [{ node: "9", type: "main", index: 0 }] },
       "9": { main: [{ node: "10", type: "main", index: 0 }] }
     }
   };
   ```

### 控制流模式

n8n支持丰富的控制流模式：

1. **条件分支模式**：
   - 基于条件的工作流路径选择
   - 支持复杂的逻辑表达式
   - 多路径条件处理
   - 适用于需要决策逻辑的流程

   ```javascript
   // 条件分支工作流示例
   const conditionalBranchingWorkflow = {
     nodes: [
       {
         id: "1", // WebHook触发器
         type: "n8n-nodes-base.Webhook",
         parameters: {
           path: "order-processor",
           responseMode: "onReceived"
         }
       },
       {
         id: "2", // 订单验证和分类
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 对订单进行验证和分类
             const order = $json;
             
             // 验证必要字段
             const errors = [];
             if (!order.orderId) errors.push("Missing order ID");
             if (!order.customerInfo) errors.push("Missing customer information");
             if (!order.items || !Array.isArray(order.items) || order.items.length === 0) {
               errors.push("No items in order");
             }
             
             // 计算订单总额
             let totalAmount = 0;
             let isHighValue = false;
             let containsRestrictedItems = false;
             let needsManualReview = false;
             let isInternational = false;
             
             if (order.items && Array.isArray(order.items)) {
               totalAmount = order.items.reduce((sum, item) => sum + (item.price * item.quantity), 0);
               
               // 检查受限商品
               containsRestrictedItems = order.items.some(item => 
                 item.category === 'restricted' || item.requiresVerification);
             }
             
             // 高价值订单检查
             isHighValue = totalAmount > 1000;
             
             // 国际订单检查
             isInternational = order.customerInfo && 
               order.customerInfo.country && 
               order.customerInfo.country !== 'USA';
               
             // 可疑订单检查
             const suspiciousPatterns = [
               // 来自高风险国家
               order.customerInfo && ["HIGHRISK1", "HIGHRISK2"].includes(order.customerInfo.country),
               // 使用不同的账单和配送地址
               order.billingAddress && order.shippingAddress && 
                 order.billingAddress.country !== order.shippingAddress.country,
               // 异常高价值且是新客户
               isHighValue && order.customerInfo && order.customerInfo.isNew,
               // 其他风险指标
               order.riskScore && order.riskScore > 80
             ];
             
             needsManualReview = suspiciousPatterns.some(Boolean);
             
             // 返回扩展的订单信息
             return [{
               json: {
                 ...order,
                 calculated: {
                   totalAmount,
                   isHighValue,
                   containsRestrictedItems,
                   needsManualReview,
                   isInternational,
                   hasErrors: errors.length > 0,
                   errors
                 }
               }
             }];
           `
         }
       },
       {
         id: "3", // 首先检查是否有错误
         type: "n8n-nodes-base.IF",
         parameters: {
           conditions: {
             boolean: [
               {
                 value1: "={{ $json.calculated.hasErrors }}",
                 value2: true
               }
             ]
           }
         }
       },
       {
         id: "4", // 错误处理路径
         type: "n8n-nodes-base.NoOp",
         parameters: {
           continueOnFail: true
         }
       },
       {
         id: "5", // 处理验证失败
         type: "n8n-nodes-base.EmailSend",
         parameters: {
           to: "orders-support@example.com",
           subject: "订单验证失败 #{{ $json.orderId }}",
           text: `
            订单 #{{ $json.orderId }} 验证失败。

            错误:
            {{ $json.calculated.errors.join("\\n") }}

            原始订单数据:
            {{ JSON.stringify($json, null, 2) }}
           `
         }
       },
       {
         id: "6", // 检查是否需要人工审核
         type: "n8n-nodes-base.IF",
         parameters: {
           conditions: {
             boolean: [
               {
                 value1: "={{ $json.calculated.needsManualReview }}",
                 value2: true
               }
             ]
           }
         }
       },
       {
         id: "7", // 发送到人工审核队列
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 添加人工审核标记
             item.json.reviewStatus = "pending";
             item.json.reviewAssignedAt = new Date().toISOString();
             
             return item;
           `
         }
       },
       {
         id: "8", // 创建审核任务
         type: "n8n-nodes-base.HttpRequest",
         parameters: {
           url: "https://review-system.example.com/api/tasks",
           method: "POST",
           authentication: "genericCredentialType",
           jsonParameters: true,
           bodyParameters: {
             taskType: "orderReview",
             priority: "={{ $json.calculated.isHighValue ? 'high' : 'normal' }}",
             orderData: "={{ $json }}",
             dueBy: "={{ $now.plusHours(4).toISOString() }}",
             reasons: "={{ Object.entries($json.calculated).filter(([k, v]) => v === true).map(([k]) => k) }}"
           }
         }
       },
       {
         id: "9", // 发送审核通知
         type: "n8n-nodes-base.Slack",
         parameters: {
           channel: "order-reviews",
           text: `🔍 需要审核的订单 #{{ $json.orderId }}
                客户: {{ $json.customerInfo.name }}
                金额: ${{ $json.calculated.totalAmount }}
                原因: {{ Object.entries($json.calculated).filter(([k, v]) => v === true && ['isHighValue', 'containsRestrictedItems', 'isInternational'].includes(k)).map(([k]) => k).join(", ") }}

                查看详情: https://review-system.example.com/tasks/{{ $node["8"].json.taskId }}`,
           otherOptions: {
             as_user: true
           }
         }
       },
       {
         id: "10", // 检查是否是国际订单
         type: "n8n-nodes-base.IF",
         parameters: {
           conditions: {
             boolean: [
               {
                 value1: "={{ $json.calculated.isInternational }}",
                 value2: true
               }
             ]
           }
         }
       },
       {
         id: "11", // 国际订单处理
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 国际订单处理逻辑
             
             // 添加国际运输信息
             item.json.shipping = {
               ...item.json.shipping,
               international: true,
               estimatedDelivery: new Date(Date.now() + 14 * 86400000).toISOString(), // 14天后
               requiresCustoms: true,
               customsForms: ["CN22", "商业发票"],
               carrier: determineInternationalCarrier(item.json)
             };
             
             // 计算国际运费
             item.json.calculated.shippingCost = calculateInternationalShipping(
               item.json.customerInfo.country,
               item.json.calculated.totalAmount,
               getTotalWeight(item.json.items)
             );
             
             return item;
             
             // 辅助函数
             function determineInternationalCarrier(order) {
               const country = order.customerInfo.country;
               const weight = getTotalWeight(order.items);
               
               // 根据目的国家和重量选择最佳承运商
               if (["Canada", "Mexico"].includes(country)) {
                 return weight > 10 ? "FreightEx" : "Global Post";
               } else if (["UK", "France", "Germany", "Italy", "Spain"].includes(country)) {
                 return "EuroDirect";
               } else if (["Australia", "New Zealand"].includes(country)) {
                 return "PacificRoute";
               } else if (["China", "Japan", "South Korea"].includes(country)) {
                 return "AsiaConnect";
               } else {
                 return "Universal Shipping";
               }
             }
             
             function calculateInternationalShipping(country, orderValue, weight) {
               // 基础运费
               let baseCost = 25;
               
               // 按重量加收
               baseCost += weight * 2;
               
               // 按地区调整
               const regionMultipliers = {
                 "Europe": 1.2,
                 "Asia": 1.5,
                 "Australia": 1.8,
                 "South America": 1.6,
                 "Africa": 1.9
               };
               
               const region = getRegionForCountry(country);
               if (regionMultipliers[region]) {
                 baseCost *= regionMultipliers[region];
               }
               
               // 高价值商品保险
               if (orderValue > 500) {
                 baseCost += orderValue * 0.01; // 1%保险费
               }
               
               return Math.round(baseCost * 100) / 100; // 保留两位小数
             }
             
             function getRegionForCountry(country) {
               // 简化的国家-区域映射
               const countryRegions = {
                 "UK": "Europe", "France": "Europe", "Germany": "Europe", "Italy": "Europe", "Spain": "Europe",
                 "China": "Asia", "Japan": "Asia", "South Korea": "Asia", "India": "Asia",
                 "Australia": "Australia", "New Zealand": "Australia",
                 "Brazil": "South America", "Argentina": "South America", "Chile": "South America",
                 "South Africa": "Africa", "Egypt": "Africa", "Nigeria": "Africa"
               };
               
               return countryRegions[country] || "Other";
             }
             
             function getTotalWeight(items) {
               return items.reduce((total, item) => total + (item.weight || 0.5) * item.quantity, 0);
             }
           `
         }
       },
       {
         id: "12", // 国际物流处理
         type: "n8n-nodes-base.HttpRequest",
         parameters: {
           url: "https://logistics.example.com/api/international-shipment",
           method: "POST",
           authentication: "genericCredentialType",
           jsonParameters: true,
           bodyParameters: {
             orderId: "={{ $json.orderId }}",
             destination: {
               country: "={{ $json.customerInfo.country }}",
               address: "={{ $json.shippingAddress }}",
               postalCode: "={{ $json.shippingAddress.postalCode }}"
             },
             items: "={{ $json.items }}",
             carrier: "={{ $json.shipping.carrier }}",
             requiresCustoms: "={{ $json.shipping.requiresCustoms }}",
             customsForms: "={{ $json.shipping.customsForms }}",
             declaredValue: "={{ $json.calculated.totalAmount }}",
             customerEmail: "={{ $json.customerInfo.email }}"
           }
         }
       },
       {
         id: "13", // 检查是否是高价值订单
         type: "n8n-nodes-base.IF",
         parameters: {
           conditions: {
             boolean: [
               {
                 value1: "={{ $json.calculated.isHighValue }}",
                 value2: true
               }
             ]
           }
         }
       },
       {
         id: "14", // 高价值订单处理
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 高价值订单处理逻辑
             
             // 添加VIP服务
             item.json.shipping = {
               ...item.json.shipping,
               priority: "high",
               insurance: true,
               insuranceValue: item.json.calculated.totalAmount,
               signatureRequired: true,
               premiumPackaging: true,
               trackingLevel: "detailed"
             };
             
             // 添加VIP客户服务跟进
             item.json.customerService = {
               assignedAgent: "VIP Team",
               followUpScheduled: true,
               followUpDate: new Date(Date.now() + 24 * 3600000).toISOString(), // 24小时后
               specialInstructions: "高价值订单 - 确认收到后进行满意度跟进"
             };
             
             return item;
           `
         }
       },
       {
         id: "15", // 发送VIP确认邮件
         type: "n8n-nodes-base.EmailSend",
         parameters: {
           to: "={{ $json.customerInfo.email }}",
           subject: "您的VIP订单已确认 #{{ $json.orderId }}",
           text: `
            尊敬的 {{ $json.customerInfo.name }}，

            感谢您的VIP订单(#{{ $json.orderId }})！我们已经开始处理您的订单，并为您提供以下尊享服务：

            - 优先处理和配送
            - 全额保险保障
            - 精美包装
            - 专人客服跟进

            您的订单预计将于 {{ $json.shipping.estimatedDelivery ? new Date($json.shipping.estimatedDelivery).toLocaleDateString() : '3-5个工作日内' }} 送达。

            如有任何问题，请随时联系您的专属客服。

            谢谢您的选购！
           `,
           additionalFields: {
             bcc: ["vip-orders@example.com"]
           }
         }
       },
       {
         id: "16", // 检查是否含有受限商品
         type: "n8n-nodes-base.IF",
         parameters: {
           conditions: {
             boolean: [
               {
                 value1: "={{ $json.calculated.containsRestrictedItems }}",
                 value2: true
               }
             ]
           }
         }
       },
       {
         id: "17", // 受限商品处理
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 受限商品处理逻辑
             
             // 标识受限商品
             const restrictedItems = item.json.items.filter(item => 
               item.category === 'restricted' || item.requiresVerification
             );
             
             // 为每个受限商品添加验证需求
             item.json.restrictedItemsProcessing = {
               items: restrictedItems.map(rItem => ({
                 itemId: rItem.id,
                 itemName: rItem.name,
                 restrictionType: rItem.category === 'restricted' ? 'age' : 'license',
                 verificationRequired: true,
                 verificationStatus: 'pending',
                 verificationInstructions: getVerificationInstructions(rItem)
               })),
               overallStatus: 'pending',
               specialHandling: true
             };
             
             return item;
             
             // 辅助函数
             function getVerificationInstructions(item) {
               if (item.category === 'alcohol') {
                 return "需要年龄验证(21+)，送货时请出示有效身份证件";
               } else if (item.category === 'prescription') {
                 return "需要处方验证，请在订单确认邮件中上传处方";
               } else if (item.requiresLicense) {
                 return "需要专业许可证，请在订单确认邮件中上传相关证件";
               } else {
                 return "需要额外验证，客服将联系您";
               }
             }
           `
         }
       },
       {
         id: "18", // 发送受限商品验证邮件
         type: "n8n-nodes-base.EmailSend",
         parameters: {
           to: "={{ $json.customerInfo.email }}",
           subject: "您的订单#{{ $json.orderId }}需要额外验证",
           text: `
            尊敬的 {{ $json.customerInfo.name }}，

            感谢您的订单(#{{ $json.orderId }})！我们注意到您购买的以下商品需要额外验证：

            {% for item in $json.restrictedItemsProcessing.items %}
            - {{ item.itemName }}: {{ item.verificationInstructions }}
            {% endfor %}

            请按照上述说明提供必要的验证信息。您可以：
            1. 回复此邮件附上所需文件
            2. 登录您的账户上传文件
            3. 等待我们的客服联系您

            在验证完成前，您的订单将暂时无法处理。我们会尽快处理您的验证信息。

            如有任何问题，请随时联系我们的客服团队。

            谢谢您的理解与配合！
           `,
           additionalFields: {
             bcc: ["compliance@example.com"]
           }
         }
       },
       {
         id: "19", // 最终合并所有路径的订单
         type: "n8n-nodes-base.Merge",
         parameters: {
           mode: "passThrough"
         }
       },
       {
         id: "20", // 标准订单处理
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 标准订单处理逻辑
             
             // 如果没有走特殊路径，添加标准处理信息
             if (!item.json.shipping) {
               item.json.shipping = {
                 priority: "standard",
                 estimatedDelivery: new Date(Date.now() + 5 * 86400000).toISOString(), // 5天后
                 trackingLevel: "standard"
               };
             }
             
             // 添加处理时间戳
             item.json.processing = {
               status: "processed",
               timestamp: new Date().toISOString(),
               route: determineProcessingRoute(item.json)
             };
             
             return item;
             
             // 辅助函数
             function determineProcessingRoute(order) {
               // 确定订单处理经过的路径
               const routes = [];
               
               if (order.calculated.hasErrors) routes.push("error");
               if (order.calculated.needsManualReview) routes.push("review");
               if (order.calculated.isInternational) routes.push("international");
               if (order.calculated.isHighValue) routes.push("highValue");
               if (order.calculated.containsRestrictedItems) routes.push("restricted");
               
               return routes.length > 0 ? routes : ["standard"];
             }
           `
         }
       },
       {
         id: "21", // 发送确认邮件
         type: "n8n-nodes-base.EmailSend",
         parameters: {
           to: "={{ $json.customerInfo.email }}",
           subject: "订单确认 #{{ $json.orderId }}",
           text: `
            尊敬的 {{ $json.customerInfo.name }}，

            感谢您的订单(#{{ $json.orderId }})！我们已经开始处理您的订单。

            订单详情:
            {% for item in $json.items %}
            - {{ item.name }} x {{ item.quantity }} @ ${{ item.price }} = ${{ item.price * item.quantity }}
            {% endfor %}

            总金额: ${{ $json.calculated.totalAmount }}
            {% if $json.calculated.shippingCost %}
            运费: ${{ $json.calculated.shippingCost }}
            {% endif %}

            预计送达时间: {{ new Date($json.shipping.estimatedDelivery).toLocaleDateString() }}

            我们将在订单发货时向您发送通知。

            感谢您的购物！
           `
         }
       },
       {
         id: "22", // 最终保存完整订单到数据库
         type: "n8n-nodes-base.Postgres",
         parameters: {
           operation: "insert",
           schema: "public",
           table: "processed_orders",
           columns: "order_id,customer_id,order_data,processing_route,processing_timestamp",
           values: "={{ $json.orderId }},={{ $json.customerInfo.id }},={{ JSON.stringify($json) }},={{ $json.processing.route.join(',') }},={{ $json.processing.timestamp }}"
         }
       }
     ],
     connections: {
       "1": { main: [{ node: "2", type: "main", index: 0 }] },
       "2": { main: [{ node: "3", type: "main", index: 0 }] },
       "3": {
         main: [
           { node: "4", type: "main", index: 0 }, // 有错误
           { node: "6", type: "main", index: 1 }  // 无错误
         ]
       },
       "4": { main: [{ node: "5", type: "main", index: 0 }] },
       "5": { main: [{ node: "19", type: "main", index: 0 }] }, // 错误处理后合并
       "6": {
         main: [
           { node: "7", type: "main", index: 0 }, // 需要人工审核
           { node: "10", type: "main", index: 1 } // 不需要人工审核
         ]
       },
       "7": { main: [{ node: "8", type: "main", index: 0 }] },
       "8": { main: [{ node: "9", type: "main", index: 0 }] },
       "9": { main: [{ node: "10", type: "main", index: 0 }] }, // 审核后继续处理
       "10": {
         main: [
           { node: "11", type: "main", index: 0 }, // 国际订单
           { node: "13", type: "main", index: 1 }  // 国内订单
         ]
       },
       "11": { main: [{ node: "12", type: "main", index: 0 }] },
       "12": { main: [{ node: "13", type: "main", index: 0 }] }, // 国际订单处理后继续
       "13": {
         main: [
           { node: "14", type: "main", index: 0 }, // 高价值订单
           { node: "16", type: "main", index: 1 }  // 普通价值订单
         ]
       },
       "14": { main: [{ node: "15", type: "main", index: 0 }] },
       "15": { main: [{ node: "16", type: "main", index: 0 }] }, // 高价值处理后继续
       "16": {
         main: [
           { node: "17", type: "main", index: 0 }, // 包含受限商品
           { node: "19", type: "main", index: 1 }  // 不包含受限商品
         ]
       },
       "17": { main: [{ node: "18", type: "main", index: 0 }] },
       "18": { main: [{ node: "19", type: "main", index: 0 }] }, // 受限商品处理后合并
       "19": { main: [{ node: "20", type: "main", index: 0 }] }, // 所有路径合并
       "20": { main: [{ node: "21", type: "main", index: 0 }] },
       "21": { main: [{ node: "22", type: "main", index: 0 }] }
     }
   };
   ```

2. **并行执行模式**：
   - 同时执行多个独立任务
   - 分割和合并数据流
   - 优化执行时间
   - 适用于相互独立的操作

   ```javascript
   // 并行执行工作流示例
   const parallelExecutionWorkflow = {
     nodes: [
       {
         id: "1", // 触发器
         type: "n8n-nodes-base.Webhook",
         parameters: {
           path: "process-data",
           responseMode: "onReceived"
         }
       },
       {
         id: "2", // 数据准备
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 准备处理的数据
             const data = $json.data;
             
             // 验证数据结构
             if (!data || !Array.isArray(data)) {
               throw new Error("无效的数据格式：需要数组");
             }
             
             // 返回待处理数据
             return [{
               json: {
                 id: $json.id || uuid(),
                 timestamp: new Date().toISOString(),
                 recordCount: data.length,
                 data: data
               }
             }];
             
             // UUID生成函数
             function uuid() {
               return 'xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx'.replace(/[xy]/g, c => {
                 const r = Math.random() * 16 | 0;
                 const v = c == 'x' ? r : (r & 0x3 | 0x8);
                 return v.toString(16);
               });
             }
           `
         }
       },
       {
         id: "3", // 分割处理
         type: "n8n-nodes-base.SplitInBatches",
         parameters: {
           batchSize: 1
         }
       },
       {
         id: "4", // 并行处理路径1：数据清洗
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 数据清洗处理
             const dataset = $json.data;
             
             // 执行数据清洗（示例）
             const cleanedData = dataset.map(record => {
               // 删除空白
               Object.keys(record).forEach(key => {
                 if (typeof record[key] === 'string') {
                   record[key] = record[key].trim();
                 }
               });
               
               // 格式化日期
               if (record.date) {
                 try {
                   const dateObj = new Date(record.date);
                   record.date = dateObj.toISOString().split('T')[0];
                 } catch (e) {
                   record.date = null;
                 }
               }
               
               // 移除无效值
               Object.keys(record).forEach(key => {
                 if (record[key] === '' || record[key] === undefined || record[key] === null) {
                   delete record[key];
                 }
               });
               
               // 添加处理标记
               record._cleaned = true;
               
               return record;
             });
             
             return [{
               json: {
                 id: $json.id,
                 processType: "cleaning",
                 processedAt: new Date().toISOString(),
                 result: cleanedData
               }
             }];
           `
         }
       },
       {
         id: "5", // 并行处理路径2：数据验证
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 数据验证处理
             const dataset = $json.data;
             
             // 定义验证规则
             const validationRules = {
               email: {
                 pattern: /^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\\.[a-zA-Z]{2,}$/,
                 message: "无效的电子邮件格式"
               },
               phone: {
                 pattern: /^[0-9+-\\s()]{7,}$/,
                 message: "无效的电话号码格式"
               },
               zipcode: {
                 pattern: /^\\d{5}(-\\d{4})?$/,
                 message: "无效的邮政编码格式"
               }
             };
             
             // 对每条记录执行验证
             const validationResults = dataset.map(record => {
               const errors = [];
               
               // 检查每个字段
               Object.keys(record).forEach(field => {
                 const rule = validationRules[field];
                 if (rule && record[field]) {
                   const value = record[field];
                   if (!rule.pattern.test(value)) {
                     errors.push(\`\${field}: \${value} - \${rule.message}\`);
                   }
                 }
               });
               
               return {
                 originalData: record,
                 valid: errors.length === 0,
                 errors: errors
               };
             });
             
             // 统计验证结果
             const validCount = validationResults.filter(r => r.valid).length;
             const invalidCount = validationResults.length - validCount;
             
             return [{
               json: {
                 id: $json.id,
                 processType: "validation",
                 processedAt: new Date().toISOString(),
                 summary: {
                   total: validationResults.length,
                   valid: validCount,
                   invalid: invalidCount,
                   validPercentage: (validCount / validationResults.length * 100).toFixed(2) + '%'
                 },
                 result: validationResults
               }
             }];
           `
         }
       },
       {
         id: "6", // 并行处理路径3：数据统计
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 数据统计分析
             const dataset = $json.data;
             
             // 初始化统计结果
             const stats = {
               count: dataset.length,
               fieldCoverage: {},
               numericalStats: {},
               categoricalStats: {}
             };
             
             // 如果没有数据，返回空统计
             if (dataset.length === 0) {
               return [{
                 json: {
                   id: $json.id,
                   processType: "statistics",
                   processedAt: new Date().toISOString(),
                   result: stats
                 }
               }];
             }
             
             // 确定所有字段
             const allFields = new Set();
             dataset.forEach(record => {
               Object.keys(record).forEach(field => allFields.add(field));
             });
             
             // 分析每个字段
             allFields.forEach(field => {
               // 字段覆盖率
               const fieldValues = dataset.map(record => record[field]).filter(v => v !== undefined && v !== null);
               stats.fieldCoverage[field] = (fieldValues.length / dataset.length * 100).toFixed(2) + '%';
               
               // 跳过空字段
               if (fieldValues.length === 0) return;
               
               // 检查字段类型
               const sampleValue = fieldValues[0];
               const valueType = typeof sampleValue;
               
               // 数值型字段统计
               if (valueType === 'number' || (valueType === 'string' && !isNaN(parseFloat(sampleValue)))) {
                 // 转换为数值
                 const numericValues = fieldValues.map(v => 
                   valueType === 'number' ? v : parseFloat(v)
                 ).filter(v => !isNaN(v));
                 
                 if (numericValues.length > 0) {
                   // 计算数值统计
                   const sum = numericValues.reduce((a, b) => a + b, 0);
                   const avg = sum / numericValues.length;
                   const min = Math.min(...numericValues);
                   const max = Math.max(...numericValues);
                   
                   // 计算中位数
                   const sorted = [...numericValues].sort((a, b) => a - b);
                   const mid = Math.floor(sorted.length / 2);
                   const median = sorted.length % 2 === 0 
                     ? (sorted[mid - 1] + sorted[mid]) / 2
                     : sorted[mid];
                   
                   stats.numericalStats[field] = {
                     count: numericValues.length,
                     min,
                     max,
                     avg,
                     median,
                     sum
                   };
                 }
               } 
               // 类别型字段统计
               else if (valueType === 'string') {
                 // 计算字符串值的频率分布
                 const valueCounts = {};
                 fieldValues.forEach(value => {
                   valueCounts[value] = (valueCounts[value] || 0) + 1;
                 });
                 
                 // 获取最常见的值（前5个）
                 const valueFrequency = Object.entries(valueCounts)
                   .sort((a, b) => b[1] - a[1])
                   .slice(0, 5)
                   .map(([value, count]) => ({
                     value,
                     count,
                     percentage: (count / fieldValues.length * 100).toFixed(2) + '%'
                   }));
                 
                 stats.categoricalStats[field] = {
                   uniqueValues: Object.keys(valueCounts).length,
                   mostCommon: valueFrequency
                 };
               }
             });
             
             return [{
               json: {
                 id: $json.id,
                 processType: "statistics",
                 processedAt: new Date().toISOString(),
                 result: stats
               }
             }];
           `
         }
       },
       {
         id: "7", // 合并并行处理结果
         type: "n8n-nodes-base.Merge",
         parameters: {
           mode: "mergeByPosition"
         }
       },
       {
         id: "8", // 组合结果
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 获取各个处理管道的结果
             const cleaningResult = $node["4"].json.result;
             const validationResult = $node["5"].json.result;
             const statisticsResult = $node["6"].json.result;
             
             // 创建综合报告
             const report = {
               id: $node["4"].json.id,
               generatedAt: new Date().toISOString(),
               processingTime: {
                 cleaning: new Date($node["4"].json.processedAt),
                 validation: new Date($node["5"].json.processedAt),
                 statistics: new Date($node["6"].json.processedAt),
               },
               summary: {
                 recordCount: cleaningResult.length,
                 validRecords: validationResult.summary.valid,
                 invalidRecords: validationResult.summary.invalid,
                 validPercentage: validationResult.summary.validPercentage
               },
               dataQuality: {
                 fieldCoverage: statisticsResult.fieldCoverage,
                 fieldsWithIssues: validationResult.result
                   .filter(r => !r.valid)
                   .flatMap(r => r.errors)
                   .reduce((acc, error) => {
                     const field = error.split(':')[0];
                     acc[field] = (acc[field] || 0) + 1;
                     return acc;
                   }, {})
               },
               statistics: {
                 numerical: statisticsResult.numericalStats,
                 categorical: statisticsResult.categoricalStats
               },
               // 包含清洗后且有效的数据
               processedData: cleaningResult.filter((record, index) => 
                 validationResult.result[index].valid
               )
             };
             
             return [{ json: report }];
           `
         }
       },
       {
         id: "9", // 保存处理后的数据
         type: "n8n-nodes-base.Postgres",
         parameters: {
           operation: "insert",
           schema: "public",
           table: "processed_datasets",
           columns: "dataset_id,processed_at,summary,processed_data",
           values: "={{ $json.id }},={{ $json.generatedAt }},={{ JSON.stringify($json.summary) }},={{ JSON.stringify($json.processedData) }}"
         }
       },
       {
         id: "10", // 发送处理完成通知
         type: "n8n-nodes-base.EmailSend",
         parameters: {
           to: "data-team@example.com",
           subject: "数据处理完成 - {{ $json.id }}",
           text: `
            数据集 ID: {{ $json.id }}
            处理时间: {{ $json.generatedAt }}

            处理摘要:
            - 总记录数: {{ $json.summary.recordCount }}
            - 有效记录: {{ $json.summary.validRecords }} ({{ $json.summary.validPercentage }})
            - 无效记录: {{ $json.summary.invalidRecords }}

            字段覆盖率:
            {% for field, coverage in $json.dataQuality.fieldCoverage %}
            - {{ field }}: {{ coverage }}
            {% endfor %}

            问题最多的字段:
            {% for field, count in $json.dataQuality.fieldsWithIssues %}
            - {{ field }}: {{ count }} 个问题
            {% endfor %}

            数值型字段统计:
            {% for field, stats in $json.statistics.numerical %}
            {{ field }}:
            - 平均值: {{ stats.avg }}
            - 中位数: {{ stats.median }}
            - 最小值: {{ stats.min }}
            - 最大值: {{ stats.max }}
            {% endfor %}

            已处理 {{ $json.processedData.length }} 条有效记录。
           `
         }
       }
     ],
     connections: {
       "1": { main: [{ node: "2", type: "main", index: 0 }] },
       "2": { main: [{ node: "3", type: "main", index: 0 }] },
       "3": { 
         main: [
           { node: "4", type: "main", index: 0 },
           { node: "5", type: "main", index: 0 },
           { node: "6", type: "main", index: 0 }
         ]
       },
       "4": { main: [{ node: "7", type: "main", index: 0 }] },
       "5": { main: [{ node: "7", type: "main", index: 1 }] },
       "6": { main: [{ node: "7", type: "main", index: 2 }] },
       "7": { main: [{ node: "8", type: "main", index: 0 }] },
       "8": { main: [{ node: "9", type: "main", index: 0 }] },
       "9": { main: [{ node: "10", type: "main", index: 0 }] }
     }
   };
   ```

3. **状态机模式**：
   - 基于状态转换的工作流
   - 根据当前状态确定下一步
   - 支持复杂状态逻辑
   - 适用于多阶段业务流程

   ```javascript
   // 状态机工作流示例 - 订单处理流程
   const stateMachineWorkflow = {
     nodes: [
       {
         id: "1", // 触发器 - 订单状态变更
         type: "n8n-nodes-base.Webhook",
         parameters: {
           path: "order-state-transition",
           responseMode: "onReceived"
         }
       },
       {
         id: "2", // 加载订单和当前状态
         type: "n8n-nodes-base.Postgres",
         parameters: {
           operation: "executeQuery",
           query: "SELECT * FROM orders WHERE order_id = '{{ $json.orderId }}'"
         }
       },
       {
         id: "3", // 状态机处理函数
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 获取订单数据
             const order = $node["2"].json[0];
             
             if (!order) {
               throw new Error(\`订单未找到: \${$json.orderId}\`);
             }
             
             // 当前状态
             const currentState = order.status;
             // 请求的事件
             const event = $json.event;
             // 附加数据
             const eventData = $json.data || {};
             
             // 定义状态机转换表
             const stateTransitions = {
               // 新建状态
               "NEW": {
                 // 支付事件
                 "payment_received": {
                   nextState: "PAID",
                   action: "recordPayment",
                   validationRules: ["paymentAmountMatchesOrder"]
                 },
                 // 取消事件
                 "cancel": {
                   nextState: "CANCELLED",
                   action: "cancelOrder",
                   validationRules: []
                 }
               },
               // 已支付状态
               "PAID": {
                 // 配货事件
                 "allocate_inventory": {
                   nextState: "INVENTORY_ALLOCATED",
                   action: "allocateInventory",
                   validationRules: ["inventoryAvailable"]
                 },
                 // 退款事件
                 "refund": {
                   nextState: "REFUNDED",
                   action: "processRefund",
                   validationRules: ["refundReasonProvided"]
                 }
               },
               // 已配货状态
               "INVENTORY_ALLOCATED": {
                 // 包装事件
                 "package": {
                   nextState: "PACKAGED",
                   action: "packageOrder",
                   validationRules: []
                 },
                 // 取消并退款事件
                 "cancel_and_refund": {
                   nextState: "REFUNDED",
                   action: "cancelAndRefund",
                   validationRules: ["refundReasonProvided"]
                 }
               },
               // 已包装状态
               "PACKAGED": {
                 // 发货事件
                 "ship": {
                   nextState: "SHIPPED",
                   action: "shipOrder",
                   validationRules: ["shippingInfoProvided"]
                 }
               },
               // 已发货状态
               "SHIPPED": {
                 // 送达事件
                 "deliver": {
                   nextState: "DELIVERED",
                   action: "markDelivered",
                   validationRules: ["deliveryProofProvided"]
                 },
                 // 丢失事件
                 "lost": {
                   nextState: "LOST_IN_TRANSIT",
                   action: "reportLost",
                   validationRules: []
                 }
               },
               // 已送达状态
               "DELIVERED": {
                 // 退货事件
                 "return": {
                   nextState: "RETURN_REQUESTED",
                   action: "processReturnRequest",
                   validationRules: ["returnReasonProvided"]
                 },
                 // 完成事件
                 "complete": {
                   nextState: "COMPLETED",
                   action: "completeOrder",
                   validationRules: []
                 }
               },
               // 退货请求状态
               "RETURN_REQUESTED": {
                 // 退货收到事件
                 "return_received": {
                   nextState: "RETURNED",
                   action: "processReturn",
                   validationRules: ["returnItemsReceived"]
                 },
                 // 退货取消事件
                 "cancel_return": {
                   nextState: "DELIVERED",
                   action: "cancelReturn",
                   validationRules: []
                 }
               },
               // 其他状态...
             };
             
             // 检查当前状态是否可以处理请求的事件
             if (!stateTransitions[currentState]) {
               throw new Error(\`无效的当前状态: \${currentState}\`);
             }
             
             const transitionDef = stateTransitions[currentState][event];
             if (!transitionDef) {
               throw new Error(\`状态 \${currentState} 不能处理事件 \${event}\`);
             }
             
             // 执行验证规则
             const validationErrors = validateTransition(transitionDef.validationRules, order, eventData);
             if (validationErrors.length > 0) {
               // 返回验证错误
               return [{
                 json: {
                   success: false,
                   orderId: order.order_id,
                   currentState: currentState,
                   event: event,
                   errors: validationErrors,
                   message: "状态转换验证失败"
                 }
               }];
             }
             
             // 计算新状态
             const nextState = transitionDef.nextState;
             const action = transitionDef.action;
             
             // 准备表示状态转换的响应
             return [{
               json: {
                 success: true,
                 orderId: order.order_id,
                 previousState: currentState,
                 event: event,
                 nextState: nextState,
                 action: action,
                 timestamp: new Date().toISOString(),
                 transition: \`\${currentState} --[\${event}]--> \${nextState}\`,
                 data: {
                   order: order,
                   eventData: eventData
                 }
               }
             }];
             
             // 验证函数
             function validateTransition(rules, order, eventData) {
               const errors = [];
               
               for (const rule of rules) {
                 switch(rule) {
                   case "paymentAmountMatchesOrder":
                     if (!eventData.paymentAmount || 
                         parseFloat(eventData.paymentAmount) !== parseFloat(order.total_amount)) {
                       errors.push("支付金额与订单金额不匹配");
                     }
                     break;
                     
                   case "inventoryAvailable":
                     // 这里通常会检查库存系统
                     if (eventData.inventoryStatus === "unavailable") {
                       errors.push("库存不足");
                     }
                     break;
                     
                   case "refundReasonProvided":
                     if (!eventData.reason) {
                       errors.push("退款必须提供原因");
                     }
                     break;
                     
                   case "shippingInfoProvided":
                     if (!eventData.trackingNumber || !eventData.carrier) {
                       errors.push("必须提供运单号和承运商");
                     }
                     break;
                     
                   case "deliveryProofProvided":
                     if (!eventData.proofOfDelivery) {
                       errors.push("必须提供送达证明");
                     }
                     break;
                     
                   case "returnReasonProvided":
                     if (!eventData.returnReason) {
                       errors.push("必须提供退货原因");
                     }
                     break;
                     
                   case "returnItemsReceived":
                     if (!eventData.receivedItems || !Array.isArray(eventData.receivedItems) || 
                         eventData.receivedItems.length === 0) {
                       errors.push("必须提供收到的退货商品");
                     }
                     break;
                     
                   default:
                     // 未知规则
                     errors.push(\`未知验证规则: \${rule}\`);
                 }
               }
               
               return errors;
             }
           `
         }
       },
       {
         id: "4", // 检查状态转换是否成功
         type: "n8n-nodes-base.IF",
         parameters: {
           conditions: {
             boolean: [
               {
                 value1: "={{ $json.success }}",
                 value2: true
               }
             ]
           }
         }
       },
       {
         id: "5", // 执行状态转换动作
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 提取状态转换信息
             const order = $json.data.order;
             const eventData = $json.data.eventData;
             const action = $json.action;
             const nextState = $json.nextState;
             
             // 根据动作类型执行不同的操作
             let actionResult;
             
             switch(action) {
               case "recordPayment":
                 actionResult = {
                   paymentId: generateId("pmt"),
                   paymentMethod: eventData.paymentMethod || "unknown",
                   paymentAmount: eventData.paymentAmount,
                   transactionId: eventData.transactionId,
                   timestamp: new Date().toISOString()
                 };
                 break;
                 
               case "cancelOrder":
                 actionResult = {
                   cancellationId: generateId("cnl"),
                   reason: eventData.reason || "客户请求",
                   timestamp: new Date().toISOString()
                 };
                 break;
                 
               case "allocateInventory":
                 actionResult = {
                   allocationId: generateId("alc"),
                   warehouseId: eventData.warehouseId || "main",
                   items: order.items.map(item => ({
                     itemId: item.item_id,
                     quantity: item.quantity,
                     locationCode: eventData.locationCodes?.[item.item_id] || "default"
                   })),
                   timestamp: new Date().toISOString()
                 };
                 break;
                 
               case "processRefund":
                 actionResult = {
                   refundId: generateId("ref"),
                   amount: eventData.amount || order.total_amount,
                   reason: eventData.reason,
                   transactionId: eventData.transactionId,
                   timestamp: new Date().toISOString()
                 };
                 break;
                 
               case "packageOrder":
                 actionResult = {
                   packageId: generateId("pkg"),
                   packagedBy: eventData.userId || "system",
                   items: order.items.map(item => ({
                     itemId: item.item_id,
                     quantity: item.quantity,
                     packagedQuantity: item.quantity // 假设全部打包
                   })),
                   timestamp: new Date().toISOString()
                 };
                 break;
                 
               case "shipOrder":
                 actionResult = {
                   shipmentId: generateId("shp"),
                   carrier: eventData.carrier,
                   trackingNumber: eventData.trackingNumber,
                   shippedItems: order.items.map(item => ({
                     itemId: item.item_id,
                     quantity: item.quantity
                   })),
                   estimatedDelivery: eventData.estimatedDelivery,
                   timestamp: new Date().toISOString()
                 };
                 break;
                 
               case "markDelivered":
                 actionResult = {
                   deliveryId: generateId("dlv"),
                   deliveryDate: eventData.deliveryDate || new Date().toISOString(),
                   proofOfDelivery: eventData.proofOfDelivery,
                   receivedBy: eventData.receivedBy || "customer",
                   timestamp: new Date().toISOString()
                 };
                 break;
                 
               case "processReturnRequest":
                 actionResult = {
                   returnRequestId: generateId("ret"),
                   reason: eventData.returnReason,
                   items: eventData.items || order.items.map(item => ({
                     itemId: item.item_id,
                     quantity: item.quantity,
                     reason: eventData.returnReason
                   })),
                   timestamp: new Date().toISOString()
                 };
                 break;
                 
               default:
                 actionResult = {
                   action: action,
                   timestamp: new Date().toISOString(),
                   data: eventData
                 };
             }
             
             // 扩展转换结果
             return [{
               json: {
                 ...$json,
                 actionResult: actionResult,
                 statusUpdateData: {
                   order_id: order.order_id,
                   previous_status: $json.previousState,
                   new_status: nextState,
                   changed_at: new Date().toISOString(),
                   event: $json.event,
                   action_data: JSON.stringify(actionResult)
                 }
               }
             }];
             
             // 辅助ID生成函数
             function generateId(prefix) {
               const timestamp = new Date().getTime().toString(36);
               const randomChars = Math.random().toString(36).substring(2, 8);
               return \`\${prefix}_\${timestamp}\${randomChars}\`;
             }
           `
         }
       },
       {
         id: "6", // 更新订单状态
         type: "n8n-nodes-base.Postgres",
         parameters: {
           operation: "update",
           schema: "public",
           table: "orders",
           updateKey: "order_id",
           columns: "status,updated_at",
           values: "={{ $json.nextState }},={{ $json.statusUpdateData.changed_at }}"
         }
       },
       {
         id: "7", // 记录状态变更历史
         type: "n8n-nodes-base.Postgres",
         parameters: {
           operation: "insert",
           schema: "public",
           table: "order_status_history",
           columns: "order_id,previous_status,new_status,changed_at,event,action_data",
           values: "={{ $json.statusUpdateData.order_id }},={{ $json.statusUpdateData.previous_status }},={{ $json.statusUpdateData.new_status }},={{ $json.statusUpdateData.changed_at }},={{ $json.statusUpdateData.event }},={{ $json.statusUpdateData.action_data }}"
         }
       },
       {
         id: "8", // 检查是否需要通知客户
         type: "n8n-nodes-base.IF",
         parameters: {
           conditions: {
             string: [
               {
                 value1: "={{ $json.nextState }}",
                 operation: "oneOf",
                 value2: "SHIPPED,DELIVERED,REFUNDED,CANCELLED"
               }
             ]
           }
         }
       },
       {
         id: "9", // 获取客户信息
         type: "n8n-nodes-base.Postgres",
         parameters: {
           operation: "executeQuery",
           query: "SELECT c.* FROM customers c JOIN orders o ON c.customer_id = o.customer_id WHERE o.order_id = '{{ $json.orderId }}'"
         }
       },
       {
         id: "10", // 发送客户通知
         type: "n8n-nodes-base.EmailSend",
         parameters: {
           to: "={{ $node['9'].json[0].email }}",
           subject: "您的订单 #{{ $json.orderId }} 状态更新",
           text: `
            尊敬的 {{ $node["9"].json[0].name }}，

            您的订单 #{{ $json.orderId }} 状态已更新为 "{{ $json.nextState }}"。

            {% if $json.nextState == "SHIPPED" %}
            您的订单已发货！

            承运商: {{ $json.actionResult.carrier }}
            运单号: {{ $json.actionResult.trackingNumber }}
            预计送达: {{ $json.actionResult.estimatedDelivery }}

            您可以使用上述运单号在承运商网站上跟踪您的包裹。
            {% endif %}

            {% if $json.nextState == "DELIVERED" %}
            您的订单已送达！

            送达时间: {{ $json.actionResult.deliveryDate }}
            签收人: {{ $json.actionResult.receivedBy }}

            感谢您选择我们的产品。如有任何问题，请随时联系我们的客服。
            {% endif %}

            {% if $json.nextState == "REFUNDED" %}
            您的退款已处理完成。

            退款金额: {{ $json.actionResult.amount }}
            退款原因: {{ $json.actionResult.reason }}
            交易编号: {{ $json.actionResult.transactionId }}

            退款将在3-5个工作日内返回到您的原支付方式。
            {% endif %}

            {% if $json.nextState == "CANCELLED" %}
            您的订单已取消。

            取消原因: {{ $json.actionResult.reason }}

            如果您有任何疑问，请联系我们的客服团队。
            {% endif %}

            谢谢！
            客服团队
           `
         }
       },
       {
         id: "11", // 状态转换失败处理
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 记录错误信息
             const errorLog = {
               orderId: $json.orderId,
               currentState: $json.currentState,
               requestedEvent: $json.event,
               errors: $json.errors,
               timestamp: new Date().toISOString(),
               requestData: $json
             };
             
             return [{
               json: {
                 ...errorLog,
                 errorLogData: {
                   order_id: errorLog.orderId,
                   error_type: "state_transition_failed",
                   details: JSON.stringify(errorLog),
                   timestamp: errorLog.timestamp
                 }
               }
             }];
           `
         }
       },
       {
         id: "12", // 记录错误日志
         type: "n8n-nodes-base.Postgres",
         parameters: {
           operation: "insert",
           schema: "public",
           table: "error_logs",
           columns: "order_id,error_type,details,timestamp",
           values: "={{ $json.errorLogData.order_id }},={{ $json.errorLogData.error_type }},={{ $json.errorLogData.details }},={{ $json.errorLogData.timestamp }}"
         }
       },
       {
         id: "13", // 发送错误通知
         type: "n8n-nodes-base.Slack",
         parameters: {
           channel: "order-issues",
           text: `⚠️ 订单状态转换失败 ⚠️
                        
                订单ID: {{ $json.orderId }}
                当前状态: {{ $json.currentState }}
                请求事件: {{ $json.event }}

                错误:
                {% for error in $json.errors %}
                - {{ error }}
                {% endfor %}

                时间: {{ $json.timestamp }}`,
           otherOptions: {
             as_user: true
           }
         }
       }
     ],
     connections: {
       "1": { main: [{ node: "2", type: "main", index: 0 }] },
       "2": { main: [{ node: "3", type: "main", index: 0 }] },
       "3": { main: [{ node: "4", type: "main", index: 0 }] },
       "4": {
         main: [
           { node: "5", type: "main", index: 0 }, // 成功
           { node: "11", type: "main", index: 1 } // 失败
         ]
       },
       "5": { main: [{ node: "6", type: "main", index: 0 }] },
       "6": { main: [{ node: "7", type: "main", index: 0 }] },
       "7": { main: [{ node: "8", type: "main", index: 0 }] },
       "8": {
         main: [
           { node: "9", type: "main", index: 0 }, // 需要通知
           { node: "1", type: "main", index: 1 }  // 不需要通知，结束
         ]
       },
       "9": { main: [{ node: "10", type: "main", index: 0 }] },
       "11": { main: [{ node: "12", type: "main", index: 0 }] },
       "12": { main: [{ node: "13", type: "main", index: 0 }] }
     }
   };
   ```

4. **saga模式**：
   - 长时间运行事务管理
   - 分布式事务补偿机制
   - 步骤回滚和恢复
   - 适用于需要最终一致性的场景

   ```javascript
   // Saga模式工作流示例
   const sagaWorkflow = {
     nodes: [
       {
         id: "1", // 订单创建触发器
         type: "n8n-nodes-base.Webhook",
         parameters: {
           path: "create-order-saga",
           responseMode: "lastNode"
         }
       },
       {
         id: "2", // 初始化Saga上下文
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 从请求中提取订单数据
             const orderData = $json;
             
             // 创建saga上下文
             const sagaContext = {
               sagaId: generateUUID(),
               startTime: new Date().toISOString(),
               status: "STARTED",
               currentStep: 0,
               steps: [
                 {
                   name: "validateInventory",
                   status: "PENDING",
                   compensationRequired: false,
                   compensationAction: "none"
                 },
                 {
                   name: "reserveInventory",
                   status: "PENDING",
                   compensationRequired: true,
                   compensationAction: "releaseInventory"
                 },
                 {
                   name: "processPayment",
                   status: "PENDING",
                   compensationRequired: true,
                   compensationAction: "refundPayment"
                 },
                 {
                   name: "createShipment",
                   status: "PENDING",
                   compensationRequired: true,
                   compensationAction: "cancelShipment"
                 },
                 {
                   name: "updateOrderStatus",
                   status: "PENDING",
                   compensationRequired: true,
                   compensationAction: "revertOrderStatus"
                 }
               ],
               orderData: orderData,
               results: {},
               errors: [],
               compensationLog: []
             };
             
             return [{ json: sagaContext }];
             
             // 生成UUID函数
             function generateUUID() {
               return 'xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx'.replace(/[xy]/g, function(c) {
                 const r = Math.random() * 16 | 0;
                 const v = c === 'x' ? r : (r & 0x3 | 0x8);
                 return v.toString(16);
               });
             }
           `
         }
       },
       {
         id: "3", // 保存初始Saga记录
         type: "n8n-nodes-base.Postgres",
         parameters: {
           operation: "insert",
           schema: "public",
           table: "saga_execution_log",
           columns: "saga_id,saga_type,status,start_time,context_data",
           values: "={{ $json.sagaId }},'create_order','STARTED',={{ $json.startTime }},={{ JSON.stringify($json) }}"
         }
       },
       {
         id: "4", // 步骤1: 验证库存
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 更新当前步骤
             const context = $json;
             context.currentStep = 0;
             context.steps[0].status = "IN_PROGRESS";
             
             try {
               // 获取商品
               const items = context.orderData.items;
               const outOfStockItems = [];
               
               // 检查每个商品的库存（模拟验证逻辑）
               for (const item of items) {
                 const productId = item.productId;
                 const quantity = item.quantity;
                 
                 // 模拟库存不足
                 if (productId === 'PROD-001' && quantity > 5) {
                   outOfStockItems.push({
                     productId,
                     requestedQuantity: quantity,
                     availableQuantity: 5
                   });
                 }
               }
               
               // 检查是否有缺货商品
               if (outOfStockItems.length > 0) {
                 throw new Error(\`库存不足: \${JSON.stringify(outOfStockItems)}\`);
               }
               
               // 更新步骤状态为成功
               context.steps[0].status = "COMPLETED";
               context.results.validateInventory = {
                 success: true,
                 validatedItems: items.map(item => ({
                   productId: item.productId,
                   quantity: item.quantity,
                   inStock: true
                 }))
               };
               
               return [{ json: context }];
             } catch (error) {
               // 更新步骤状态为失败
               context.steps[0].status = "FAILED";
               context.status = "FAILED";
               context.errors.push({
                 step: "validateInventory",
                 message: error.message,
                 timestamp: new Date().toISOString()
               });
               
               return [{ json: context }];
             }
           `
         }
       },
       {
         id: "5", // 检查步骤1是否成功
         type: "n8n-nodes-base.IF",
         parameters: {
           conditions: {
             string: [
               {
                 value1: "={{ $json.steps[0].status }}",
                 operation: "equals",
                 value2: "COMPLETED"
               }
             ]
           }
         }
       },
       {
         id: "6", // 步骤2: 预留库存
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 更新当前步骤
             const context = $json;
             context.currentStep = 1;
             context.steps[1].status = "IN_PROGRESS";
             
             try {
               // 获取商品
               const items = context.orderData.items;
               
               // 为每个商品预留库存（模拟预留逻辑）
               const reservations = [];
               for (const item of items) {
                 const productId = item.productId;
                 const quantity = item.quantity;
                 
                 // 模拟预留失败
                 if (productId === 'PROD-002' && Math.random() < 0.1) {
                   throw new Error(\`无法为商品 \${productId} 预留库存\`);
                 }
                 
                 // 添加预留记录
                 reservations.push({
                   productId,
                   quantity,
                   reservationId: \`RES-\${Date.now()}-\${productId}\`,
                   reservedAt: new Date().toISOString()
                 });
               }
               
               // 更新步骤状态为成功
               context.steps[1].status = "COMPLETED";
               context.results.reserveInventory = {
                 success: true,
                 reservations: reservations
               };
               
               return [{ json: context }];
             } catch (error) {
               // 更新步骤状态为失败
               context.steps[1].status = "FAILED";
               context.status = "COMPENSATION_NEEDED";
               context.errors.push({
                 step: "reserveInventory",
                 message: error.message,
                 timestamp: new Date().toISOString()
               });
               
               return [{ json: context }];
             }
           `
         }
       },
       {
         id: "7", // 检查步骤2是否成功
         type: "n8n-nodes-base.IF",
         parameters: {
           conditions: {
             string: [
               {
                 value1: "={{ $json.steps[1].status }}",
                 operation: "equals",
                 value2: "COMPLETED"
               }
             ]
           }
         }
       },
       {
         id: "8", // 步骤3: 处理支付
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 更新当前步骤
             const context = $json;
             context.currentStep = 2;
             context.steps[2].status = "IN_PROGRESS";
             
             try {
               // 获取订单和支付信息
               const orderTotal = context.orderData.totalAmount;
               const paymentMethod = context.orderData.paymentMethod;
               const customerId = context.orderData.customerId;
               
               // 模拟支付处理
               const paymentResult = processPayment(paymentMethod, orderTotal, customerId);
               
               if (!paymentResult.success) {
                 throw new Error(\`支付失败: \${paymentResult.message}\`);
               }
               
               // 更新步骤状态为成功
               context.steps[2].status = "COMPLETED";
               context.results.processPayment = paymentResult;
               
               return [{ json: context }];
             } catch (error) {
               // 更新步骤状态为失败
               context.steps[2].status = "FAILED";
               context.status = "COMPENSATION_NEEDED";
               context.errors.push({
                 step: "processPayment",
                 message: error.message,
                 timestamp: new Date().toISOString()
               });
               
               return [{ json: context }];
             }
             
             // 模拟支付处理函数
             function processPayment(method, amount, customerId) {
               // 随机模拟支付失败
               if (Math.random() < 0.05) {
                 return {
                   success: false,
                   message: "支付处理失败，请稍后重试"
                 };
               }
               
               // 模拟支付成功
               return {
                 success: true,
                 transactionId: `TRX-${Date.now()}-${Math.floor(Math.random() * 10000)}`,
                 paymentMethod: method,
                 amount: amount,
                 customerId: customerId,
                 processedAt: new Date().toISOString(),
                 status: "COMPLETED"
               };
             }
           `
         }
       },
       {
         id: "9", // 检查步骤3是否成功
         type: "n8n-nodes-base.IF",
         parameters: {
           conditions: {
             string: [
               {
                 value1: "={{ $json.steps[2].status }}",
                 operation: "equals",
                 value2: "COMPLETED"
               }
             ]
           }
         }
       },
       {
         id: "10", // 步骤4: 创建物流单
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 更新当前步骤
             const context = $json;
             context.currentStep = 3;
             context.steps[3].status = "IN_PROGRESS";
             
             try {
               // 获取订单和收货信息
               const orderId = context.orderData.orderId;
               const shippingAddress = context.orderData.shippingAddress;
               const items = context.orderData.items;
               
               // 模拟创建物流单
               const shipmentResult = createShipment(orderId, shippingAddress, items);
               
               if (!shipmentResult.success) {
                 throw new Error(\`创建物流单失败: \${shipmentResult.message}\`);
               }
               
               // 更新步骤状态为成功
               context.steps[3].status = "COMPLETED";
               context.results.createShipment = shipmentResult;
               
               return [{ json: context }];
             } catch (error) {
               // 更新步骤状态为失败
               context.steps[3].status = "FAILED";
               context.status = "COMPENSATION_NEEDED";
               context.errors.push({
                 step: "createShipment",
                 message: error.message,
                 timestamp: new Date().toISOString()
               });
               
               return [{ json: context }];
             }
             
             // 模拟创建物流单函数
             function createShipment(orderId, address, items) {
               // 简单验证地址
               if (!address.street || !address.city || !address.zipCode) {
                 return {
                   success: false,
                   message: "收货地址不完整"
                 };
               }
               
               // 模拟物流单创建
               return {
                 success: true,
                 shipmentId: `SHIP-${Date.now()}`,
                 orderId: orderId,
                 carrier: selectCarrier(address),
                 trackingNumber: `TRK${Math.random().toString(36).substring(2, 10).toUpperCase()}`,
                 shippingAddress: address,
                 estimatedDelivery: new Date(Date.now() + 3 * 24 * 60 * 60 * 1000).toISOString(),
                 status: "CREATED",
                 createdAt: new Date().toISOString()
               };
             }
             
             // 选择承运商函数
             function selectCarrier(address) {
               const carriers = ["FedEx", "UPS", "USPS", "DHL"];
               const countryCode = address.countryCode || "US";
               
               // 简单的国家-承运商匹配逻辑
               if (countryCode === "US") {
                 return carriers[Math.floor(Math.random() * 3)]; // FedEx, UPS, USPS
               } else {
                 return "DHL"; // 国际默认DHL
               }
             }
           `
         }
       },
       {
         id: "11", // 检查步骤4是否成功
         type: "n8n-nodes-base.IF",
         parameters: {
           conditions: {
             string: [
               {
                 value1: "={{ $json.steps[3].status }}",
                 operation: "equals",
                 value2: "COMPLETED"
               }
             ]
           }
         }
       },
       {
         id: "12", // 步骤5: 更新订单状态
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 更新当前步骤
             const context = $json;
             context.currentStep = 4;
             context.steps[4].status = "IN_PROGRESS";
             
             try {
               // 获取订单ID
               const orderId = context.orderData.orderId;
               
               // 模拟订单状态更新
               const orderUpdateResult = {
                 success: true,
                 orderId: orderId,
                 previousStatus: "CREATED",
                 newStatus: "PROCESSING",
                 paymentStatus: "PAID",
                 shipmentStatus: "PENDING",
                 updateTime: new Date().toISOString()
               };
               
               // 更新步骤状态为成功
               context.steps[4].status = "COMPLETED";
               context.results.updateOrderStatus = orderUpdateResult;
               
               // 所有步骤都完成，更新Saga状态
               context.status = "COMPLETED";
               context.endTime = new Date().toISOString();
               
               return [{ json: context }];
             } catch (error) {
               // 更新步骤状态为失败
               context.steps[4].status = "FAILED";
               context.status = "COMPENSATION_NEEDED";
               context.errors.push({
                 step: "updateOrderStatus",
                 message: error.message,
                 timestamp: new Date().toISOString()
               });
               
               return [{ json: context }];
             }
           `
         }
       },
       {
         id: "13", // 检查Saga整体完成状态
         type: "n8n-nodes-base.IF",
         parameters: {
           conditions: {
             string: [
               {
                 value1: "={{ $json.status }}",
                 operation: "equals",
                 value2: "COMPLETED"
               }
             ]
           }
         }
       },
       {
         id: "14", // 成功完成Saga - 更新Saga记录
         type: "n8n-nodes-base.Postgres",
         parameters: {
           operation: "update",
           schema: "public",
           table: "saga_execution_log",
           updateKey: "saga_id",
           columns: "status,end_time,context_data",
           values: "'COMPLETED',={{ $json.endTime }},={{ JSON.stringify($json) }}"
         }
       },
       {
         id: "15", // 成功完成Saga - 返回成功响应
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 构建成功响应
             const response = {
               success: true,
               orderId: $json.orderData.orderId,
               sagaId: $json.sagaId,
               message: "订单处理成功",
               orderDetails: {
                 status: "PROCESSING",
                 paymentInfo: $json.results.processPayment,
                 shipmentInfo: $json.results.createShipment
               }
             };
             
             return [{ json: response }];
           `
         }
       },
       {
         id: "16", // 需要补偿 - 执行补偿逻辑
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 补偿事务
             const context = $json;
             context.compensationStartTime = new Date().toISOString();
             
             // 找到需要补偿的步骤
             const stepsToCompensate = [];
             for (let i = context.currentStep; i >= 0; i--) {
               const step = context.steps[i];
               if (step.status === "COMPLETED" && step.compensationRequired) {
                 stepsToCompensate.push({
                   stepIndex: i,
                   stepName: step.name,
                   compensationAction: step.compensationAction
                 });
               }
             }
             
             // 执行补偿动作
             const compensationLog = [];
             for (const stepInfo of stepsToCompensate) {
               try {
                 const compensationResult = executeCompensation(
                   stepInfo.compensationAction,
                   context.results[stepInfo.stepName],
                   context
                 );
                 
                 compensationLog.push({
                   step: stepInfo.stepName,
                   action: stepInfo.compensationAction,
                   success: true,
                   result: compensationResult,
                   timestamp: new Date().toISOString()
                 });
                 
                 // 更新步骤状态
                 context.steps[stepInfo.stepIndex].status = "COMPENSATED";
               } catch (error) {
                 compensationLog.push({
                   step: stepInfo.stepName,
                   action: stepInfo.compensationAction,
                   success: false,
                   error: error.message,
                   timestamp: new Date().toISOString()
                 });
                 
                 // 补偿失败，标记为人工干预
                 context.status = "REQUIRES_MANUAL_INTERVENTION";
                 break;
               }
             }
             
             // 更新补偿日志
             context.compensationLog = compensationLog;
             
             // 如果所有补偿动作都成功，更新状态
             if (context.status !== "REQUIRES_MANUAL_INTERVENTION") {
               context.status = "COMPENSATED";
             }
             
             context.compensationEndTime = new Date().toISOString();
             
             return [{ json: context }];
             
             // 执行补偿动作函数
             function executeCompensation(action, stepResult, context) {
               switch (action) {
                 case "releaseInventory": 
                   return releaseInventory(stepResult);
                   
                 case "refundPayment":
                   return refundPayment(stepResult);
                   
                 case "cancelShipment":
                   return cancelShipment(stepResult);
                   
                 case "revertOrderStatus":
                   return revertOrderStatus(stepResult);
                   
                 default:
                   throw new Error(\`未知的补偿动作: \${action}\`);
               }
             }
             
             // 释放库存函数
             function releaseInventory(reservationResult) {
               if (!reservationResult || !reservationResult.reservations) {
                 return { message: "无预留库存需要释放" };
               }
               
               // 模拟释放库存
               return {
                 releasedItems: reservationResult.reservations.map(r => ({
                   productId: r.productId,
                   quantity: r.quantity,
                   reservationId: r.reservationId,
                   releasedAt: new Date().toISOString()
                 })),
                 message: \`成功释放 \${reservationResult.reservations.length} 种商品的库存\`
               };
             }
             
             // 退款函数
             function refundPayment(paymentResult) {
               if (!paymentResult || !paymentResult.transactionId) {
                 return { message: "无支付需要退款" };
               }
               
               // 模拟退款
               return {
                 refundId: \`REF-\${Date.now()}\`,
                 originalTransactionId: paymentResult.transactionId,
                 amount: paymentResult.amount,
                 status: "REFUNDED",
                 refundedAt: new Date().toISOString(),
                 message: \`成功退款 \${paymentResult.amount}\`
               };
             }
             
             // 取消物流单函数
             function cancelShipment(shipmentResult) {
               if (!shipmentResult || !shipmentResult.shipmentId) {
                 return { message: "无物流单需要取消" };
               }
               
               // 模拟取消物流单
               return {
                 shipmentId: shipmentResult.shipmentId,
                 cancellationId: \`CNCL-\${Date.now()}\`,
                 previousStatus: shipmentResult.status,
                 newStatus: "CANCELLED",
                 cancelledAt: new Date().toISOString(),
                 message: \`成功取消物流单 \${shipmentResult.shipmentId}\`
               };
             }
             
             // 恢复订单状态函数
             function revertOrderStatus(orderUpdateResult) {
               if (!orderUpdateResult || !orderUpdateResult.orderId) {
                 return { message: "无订单状态需要恢复" };
               }
               
               // 模拟恢复订单状态
               return {
                 orderId: orderUpdateResult.orderId,
                 previousStatus: orderUpdateResult.newStatus,
                 revertedStatus: orderUpdateResult.previousStatus,
                 revertedAt: new Date().toISOString(),
                 message: \`成功恢复订单 \${orderUpdateResult.orderId} 状态为 \${orderUpdateResult.previousStatus}\`
               };
             }
           `
         }
       },
       {
         id: "17", // 更新Saga补偿记录
         type: "n8n-nodes-base.Postgres",
         parameters: {
           operation: "update",
           schema: "public",
           table: "saga_execution_log",
           updateKey: "saga_id",
           columns: "status,end_time,context_data",
           values: "={{ $json.status }},={{ $json.compensationEndTime }},={{ JSON.stringify($json) }}"
         }
       },
       {
         id: "18", // 返回失败响应
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 构建失败响应
             const response = {
               success: false,
               orderId: $json.orderData.orderId,
               sagaId: $json.sagaId,
               message: "订单处理失败",
               errors: $json.errors,
               status: $json.status,
               requiresManualIntervention: $json.status === "REQUIRES_MANUAL_INTERVENTION"
             };
             
             // 添加人工干预说明
             if (response.requiresManualIntervention) {
               response.manualInterventionReason = "补偿事务部分失败，需要人工干预解决";
               response.failedCompensationSteps = $json.compensationLog
                 .filter(log => !log.success)
                 .map(log => ({ step: log.step, error: log.error }));
             }
             
             return [{ json: response }];
           `
         }
       },
       {
         id: "19", // 需要人工干预时发送通知
         type: "n8n-nodes-base.IF",
         parameters: {
           conditions: {
             string: [
               {
                 value1: "={{ $json.status }}",
                 operation: "equals",
                 value2: "REQUIRES_MANUAL_INTERVENTION"
               }
             ]
           }
         }
       },
       {
         id: "20", // 发送人工干预通知
         type: "n8n-nodes-base.Slack",
         parameters: {
           channel: "order-alerts",
           text: `⚠️ 订单Saga需要人工干预 ⚠️
                    
            Saga ID: {{ $json.sagaId }}
            订单ID: {{ $json.orderData.orderId }}
            客户: {{ $json.orderData.customerName }}

            失败原因:
            {% for error in $json.errors %}
            - {{ error.step }}: {{ error.message }}
            {% endfor %}

            失败的补偿步骤:
            {% for step in $json.compensationLog %}
            {% if step.success == false %}
            - {{ step.step }} ({{ step.action }}): {{ step.error }}
            {% endif %}
            {% endfor %}

            请检查系统并手动解决这些问题。`,
           otherOptions: {
             as_user: true
           }
         }
       }
     ],
     connections: {
       "1": { main: [{ node: "2", type: "main", index: 0 }] },
       "2": { main: [{ node: "3", type: "main", index: 0 }] },
       "3": { main: [{ node: "4", type: "main", index: 0 }] },
       "4": { main: [{ node: "5", type: "main", index: 0 }] },
       "5": {
         main: [
           { node: "6", type: "main", index: 0 }, // 验证成功
           { node: "16", type: "main", index: 1 } // 验证失败，开始补偿
         ]
       },
       "6": { main: [{ node: "7", type: "main", index: 0 }] },
       "7": {
         main: [
           { node: "8", type: "main", index: 0 }, // 预留库存成功
           { node: "16", type: "main", index: 1 } // 预留库存失败，开始补偿
         ]
       },
       "8": { main: [{ node: "9", type: "main", index: 0 }] },
       "9": {
         main: [
           { node: "10", type: "main", index: 0 }, // 支付成功
           { node: "16", type: "main", index: 1 } // 支付失败，开始补偿
         ]
       },
       "10": { main: [{ node: "11", type: "main", index: 0 }] },
       "11": {
         main: [
           { node: "12", type: "main", index: 0 }, // 创建物流单成功
           { node: "16", type: "main", index: 1 } // 创建物流单失败，开始补偿
         ]
       },
       "12": { main: [{ node: "13", type: "main", index: 0 }] },
       "13": {
         main: [
           { node: "14", type: "main", index: 0 }, // 全部成功
           { node: "16", type: "main", index: 1 } // 最后步骤失败，开始补偿
         ]
       },
       "14": { main: [{ node: "15", type: "main", index: 0 }] },
       "16": { main: [{ node: "17", type: "main", index: 0 }] },
       "17": { main: [{ node: "18", type: "main", index: 0 }] },
       "18": { main: [{ node: "19", type: "main", index: 0 }] },
       "19": {
         main: [
           { node: "20", type: "main", index: 0 }, // 需要人工干预
           { node: "1", type: "main", index: 1 } // 不需要人工干预，结束
         ]
       }
     }
   };
   ```

### 错误处理模式

n8n提供多种错误处理策略：

1. **重试模式**：
   - 失败任务自动重试
   - 指数退避策略
   - 最大重试次数控制
   - 适用于临时性失败

   ```javascript
   // 重试模式工作流示例
   const retryPatternWorkflow = {
     nodes: [
       {
         id: "1", // 触发器
         type: "n8n-nodes-base.Cron",
         parameters: {
           triggerTimes: {
             hour: [*/3], // 每3小时执行一次
             minute: [0]
           }
         }
       },
       {
         id: "2", // 加载待处理项
         type: "n8n-nodes-base.Postgres",
         parameters: {
           operation: "executeQuery",
           query: "SELECT * FROM processing_queue WHERE status = 'PENDING' ORDER BY priority DESC, created_at ASC LIMIT 10"
         }
       },
       {
         id: "3", // 分割成单个项目处理
         type: "n8n-nodes-base.SplitInBatches",
         parameters: {
           batchSize: 1
         }
       },
       {
         id: "4", // 处理单个项目
         type: "n8n-nodes-base.HttpRequest",
         parameters: {
           url: "={{ $json.api_endpoint }}",
           method: "POST",
           authentication: "genericCredentialType",
           jsonParameters: true,
           bodyParameters: {
             id: "={{ $json.id }}",
             type: "={{ $json.item_type }}",
             data: "={{ $json.payload }}"
           },
           options: {
             redirect: {
               follow: true
             },
             timeout: 10000 // 10秒超时
           }
         },
         continueOnFail: true
       },
       {
         id: "5", // 检查HTTP请求是否成功
         type: "n8n-nodes-base.IF",
         parameters: {
           conditions: {
             number: [
               {
                 value1: "={{ $json.statusCode }}",
                 operation: "smaller",
                 value2: 300
               }
             ]
           }
         }
       },
       {
         id: "6", // 成功处理标记
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 标记成功处理
             return [{
               json: {
                 id: $json.id,
                 success: true,
                 status: "COMPLETED",
                 response: $json,
                 completed_at: new Date().toISOString(),
                 retry_count: $json.retry_count || 0
               }
             }];
           `
         }
       },
       {
         id: "7", // 检查错误类型和重试计数
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 获取当前重试次数（如果没有则初始化为0）
             const retryCount = $json.retry_count || 0;
             // 获取状态码
             const statusCode = $json.statusCode || 500;
             
             // 检查是否是可重试的错误
             let isRetryable = false;
             let retryReason = "";
             
             // 基于HTTP状态码判断是否可重试
             if (statusCode >= 500) {
               // 服务器错误，可能是临时性问题
               isRetryable = true;
               retryReason = \`服务器错误: \${statusCode}\`;
             } else if (statusCode === 429) {
               // 请求过多错误，可以重试
               isRetryable = true;
               retryReason = "请求频率限制 (429)";
             } else if (statusCode === 408) {
               // 请求超时，可以重试
               isRetryable = true;
               retryReason = "请求超时 (408)";
             } else if ($json.error && $json.error.includes("timeout")) {
               // 连接超时或其他超时错误
               isRetryable = true;
               retryReason = "连接超时";
             } else if ($json.error && $json.error.includes("ECONNREFUSED")) {
               // 连接被拒绝
               isRetryable = true;
               retryReason = "连接被拒绝";
             }
             
             // 检查重试次数是否超过最大值（这里设为5）
             const maxRetries = 5;
             const canRetry = isRetryable && retryCount < maxRetries;
             
             // 计算下次重试的延迟（指数退避）
             // 基本公式: 延迟时间 = 基础延迟 * (2^重试次数) + 随机偏移
             const baseDelay = 60; // 基础延迟秒数
             const nextRetryDelay = Math.floor(baseDelay * Math.pow(2, retryCount) + Math.random() * 30);
             
             // 下次重试时间
             const now = new Date();
             const nextRetryTime = new Date(now.getTime() + nextRetryDelay * 1000);
             
             return [{
               json: {
                 ...item.json,
                 success: false,
                 canRetry: canRetry,
                 retryReason: retryReason,
                 retryCount: retryCount,
                 nextRetryCount: retryCount + 1,
                 nextRetryDelay: nextRetryDelay,
                 nextRetryTime: nextRetryTime.toISOString(),
                 error: $json.error || \`HTTP错误: \${statusCode}\`,
                 maxRetries: maxRetries
               }
             }];
           `
         }
       },
       {
         id: "8", // 检查是否可以重试
         type: "n8n-nodes-base.IF",
         parameters: {
           conditions: {
             boolean: [
               {
                 value1: "={{ $json.canRetry }}",
                 value2: true
               }
             ]
           }
         }
       },
       {
         id: "9", // 标记为重试
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 准备重试数据
             return [{
               json: {
                 id: $json.id,
                 status: "RETRY",
                 retry_count: $json.nextRetryCount,
                 last_error: $json.error,
                 retry_reason: $json.retryReason,
                 next_retry_at: $json.nextRetryTime,
                 updated_at: new Date().toISOString()
               }
             }];
           `
         }
       },
       {
         id: "10", // 标记为失败
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 标记为永久失败
             return [{
               json: {
                 id: $json.id,
                 status: "FAILED",
                 retry_count: $json.retryCount,
                 last_error: $json.error,
                 failed_at: new Date().toISOString()
               }
             }];
           `
         }
       },
       {
         id: "11", // 更新成功处理状态
         type: "n8n-nodes-base.Postgres",
         parameters: {
           operation: "update",
           schema: "public",
           table: "processing_queue",
           updateKey: "id",
           columns: "status,completed_at,response_data,updated_at",
           values: "='COMPLETED',={{ $json.completed_at }},={{ JSON.stringify($json.response) }},={{ new Date().toISOString() }}"
         }
       },
       {
         id: "12", // 更新重试状态
         type: "n8n-nodes-base.Postgres",
         parameters: {
           operation: "update",
           schema: "public",
           table: "processing_queue",
           updateKey: "id",
           columns: "status,retry_count,last_error,next_retry_at,updated_at",
           values: "='RETRY',={{ $json.retry_count }},={{ $json.last_error }},={{ $json.next_retry_at }},={{ $json.updated_at }}"
         }
       },
       {
         id: "13", // 更新失败状态
         type: "n8n-nodes-base.Postgres",
         parameters: {
           operation: "update",
           schema: "public",
           table: "processing_queue",
           updateKey: "id",
           columns: "status,retry_count,last_error,failed_at,updated_at",
           values: "='FAILED',={{ $json.retry_count }},={{ $json.last_error }},={{ $json.failed_at }},={{ new Date().toISOString() }}"
         }
       },
       {
         id: "14", // 记录重试和失败的日志
         type: "n8n-nodes-base.Postgres",
         parameters: {
           operation: "insert",
           schema: "public",
           table: "processing_log",
           columns: "item_id,operation,status,message,details,created_at",
           values: "={{ $json.id }},={{ $json.status === 'RETRY' ? 'retry' : 'failure' }},={{ $json.status }},={{ $json.last_error }},={{ JSON.stringify($json) }},={{ new Date().toISOString() }}"
         }
       }
     ],
     connections: {
       "1": { main: [{ node: "2", type: "main", index: 0 }] },
       "2": { main: [{ node: "3", type: "main", index: 0 }] },
       "3": { main: [{ node: "4", type: "main", index: 0 }] },
       "4": { main: [{ node: "5", type: "main", index: 0 }] },
       "5": {
         main: [
           { node: "6", type: "main", index: 0 }, // HTTP请求成功
           { node: "7", type: "main", index: 1 }  // HTTP请求失败
         ]
       },
       "6": { main: [{ node: "11", type: "main", index: 0 }] },
       "7": { main: [{ node: "8", type: "main", index: 0 }] },
       "8": {
         main: [
           { node: "9", type: "main", index: 0 }, // 可以重试
           { node: "10", type: "main", index: 1 } // 不能重试
         ]
       },
       "9": { main: [{ node: "12", type: "main", index: 0 }] },
       "10": { main: [{ node: "13", type: "main", index: 0 }] },
       "12": { main: [{ node: "14", type: "main", index: 0 }] },
       "13": { main: [{ node: "14", type: "main", index: 0 }] }
     }
   };
   ```

2. **断路器模式**：
   - 防止重复调用失败服务
   - 基于错误率自动开关
   - 半开状态试探恢复
   - 适用于外部服务依赖

   ```javascript
   // 断路器模式工作流示例
   const circuitBreakerWorkflow = {
     nodes: [
       {
         id: "1", // WebHook触发器
         type: "n8n-nodes-base.Webhook",
         parameters: {
           path: "api-proxy",
           responseMode: "lastNode"
         }
       },
       {
         id: "2", // 检查断路器状态
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 从请求中提取目标服务信息
             const serviceId = $json.service || 'default';
             const operationType = $json.operation || 'read';
             
             // 生成断路器键
             const circuitKey = \`\${serviceId}:\${operationType}\`;
             
             // 获取Redis中的断路器状态 (这里我们模拟实现)
             // 在实际应用中，你需要实现对Redis或其他存储的调用
             const circuitStatus = getCircuitStatus(circuitKey);
             
             // 添加断路器信息到请求上下文
             return [{
               json: {
                 ...$json,
                 circuitBreaker: {
                   key: circuitKey,
                   status: circuitStatus.status,
                   failureCount: circuitStatus.failureCount,
                   failureThreshold: circuitStatus.failureThreshold,
                   lastFailure: circuitStatus.lastFailure,
                   nextAttempt: circuitStatus.nextAttempt,
                   serviceName: serviceId,
                   operationType: operationType
                 }
               }
             }];
             
             // 模拟获取断路器状态的函数
             // 在实际应用中，这应从Redis或类似存储中检索
             function getCircuitStatus(key) {
               // 这里假设我们有一个全局的断路器状态存储
               // 在n8n中，你可能需要实际从存储中检索这些值
               
               // 为了示例，我们假设有两个服务的固定状态
               const mockCircuits = {
                 'payment-service:process': {
                   status: 'OPEN', // 断路器打开
                   failureCount: 15,
                   failureThreshold: 10,
                   lastFailure: new Date(Date.now() - 60000).toISOString(),
                   nextAttempt: new Date(Date.now() + 120000).toISOString(),
                 },
                 'inventory-service:check': {
                   status: 'HALF_OPEN', // 断路器半开
                   failureCount: 12,
                   failureThreshold: 10,
                   lastFailure: new Date(Date.now() - 300000).toISOString(),
                   nextAttempt: new Date(Date.now() - 60000).toISOString(), // 已过试探时间
                 }
               };
               
               // 返回已知服务的状态或默认关闭状态
               return mockCircuits[key] || {
                 status: 'CLOSED', // 断路器关闭（正常状态）
                 failureCount: 0,
                 failureThreshold: 10,
                 lastFailure: null,
                 nextAttempt: null
               };
             }
           `
         }
       },
       {
         id: "3", // 检查断路器是否打开
         type: "n8n-nodes-base.IF",
         parameters: {
           conditions: {
             string: [
               {
                 value1: "={{ $json.circuitBreaker.status }}",
                 operation: "equals",
                 value2: "OPEN"
               }
             ]
           }
         }
       },
       {
         id: "4", // 断路器打开 - 短路响应
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 生成断路器打开的错误响应
             const shortCircuitedResponse = {
               success: false,
               error: {
                 code: "CIRCUIT_OPEN",
                 message: \`服务 \${$json.circuitBreaker.serviceName} 当前不可用，断路器已打开\`,
                 details: {
                   failureCount: $json.circuitBreaker.failureCount,
                   lastFailure: $json.circuitBreaker.lastFailure,
                   nextAttempt: $json.circuitBreaker.nextAttempt,
                   retryAfterSeconds: Math.ceil((new Date($json.circuitBreaker.nextAttempt) - new Date()) / 1000)
                 }
               },
               timestamp: new Date().toISOString()
             };
             
             // 添加HTTP响应头
             const responseHeaders = {
               'Content-Type': 'application/json',
               'Retry-After': Math.ceil((new Date($json.circuitBreaker.nextAttempt) - new Date()) / 1000)
             };
             
             return [{
               json: shortCircuitedResponse,
               headers: responseHeaders,
               statusCode: 503 // Service Unavailable
             }];
           `
         }
       },
       {
         id: "5", // 检查断路器是否半开
         type: "n8n-nodes-base.IF",
         parameters: {
           conditions: {
             string: [
               {
                 value1: "={{ $json.circuitBreaker.status }}",
                 operation: "equals",
                 value2: "HALF_OPEN"
               }
             ]
           }
         }
       },
       {
         id: "6", // 半开状态 - 检查是否可以进行试探性请求
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 检查是否已到试探请求时间
             const now = new Date();
             const nextAttempt = new Date($json.circuitBreaker.nextAttempt);
             
             // 如果当前时间大于下次尝试时间，允许一个试探性请求
             if (now >= nextAttempt) {
               return [{
                 json: {
                   ...$json,
                   circuitBreaker: {
                     ...$json.circuitBreaker,
                     allowTestRequest: true
                   }
                 }
               }];
             } else {
               // 否则继续拒绝请求
               return [{
                 json: {
                   ...$json,
                   circuitBreaker: {
                     ...$json.circuitBreaker,
                     allowTestRequest: false
                   }
                 }
               }];
             }
           `
         }
       },
       {
         id: "7", // 检查是否允许试探性请求
         type: "n8n-nodes-base.IF",
         parameters: {
           conditions: {
             boolean: [
               {
                 value1: "={{ $json.circuitBreaker.allowTestRequest }}",
                 value2: true
               }
             ]
           }
         }
       },
       {
         id: "8", // 不允许试探 - 返回半开错误
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 生成断路器半开且不允许试探的错误响应
             const halfOpenResponse = {
               success: false,
               error: {
                 code: "CIRCUIT_HALF_OPEN",
                 message: \`服务 \${$json.circuitBreaker.serviceName} 当前有限可用，请稍后重试\`,
                 details: {
                   failureCount: $json.circuitBreaker.failureCount,
                   lastFailure: $json.circuitBreaker.lastFailure,
                   nextAttempt: $json.circuitBreaker.nextAttempt,
                   retryAfterSeconds: Math.ceil((new Date($json.circuitBreaker.nextAttempt) - new Date()) / 1000)
                 }
               },
               timestamp: new Date().toISOString()
             };
             
             // 添加HTTP响应头
             const responseHeaders = {
               'Content-Type': 'application/json',
               'Retry-After': Math.ceil((new Date($json.circuitBreaker.nextAttempt) - new Date()) / 1000)
             };
             
             return [{
               json: halfOpenResponse,
               headers: responseHeaders,
               statusCode: 503 // Service Unavailable
             }];
           `
         }
       },
       {
         id: "9", // 准备API请求
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 从请求中提取所需信息
             const serviceId = $json.circuitBreaker.serviceName;
             const operationType = $json.circuitBreaker.operationType;
             const requestBody = $json.data || {};
             
             // 基于服务ID解析实际API端点
             let apiEndpoint;
             switch(serviceId) {
               case 'payment-service':
                 apiEndpoint = 'https://api.payment.example.com/v1';
                 break;
               case 'inventory-service':
                 apiEndpoint = 'https://api.inventory.example.com/v2';
                 break;
               case 'shipping-service':
                 apiEndpoint = 'https://api.shipping.example.com/v1';
                 break;
               default:
                 apiEndpoint = 'https://api.default.example.com';
             }
             
             // 基于操作类型构建API路径
             let apiPath;
             switch(operationType) {
               case 'check':
                 apiPath = '/check';
                 break;
               case 'process':
                 apiPath = '/process';
                 break;
               case 'update':
                 apiPath = '/update';
                 break;
               default:
                 apiPath = '/default';
             }
             
             // 完整的API URL
             const apiUrl = \`\${apiEndpoint}\${apiPath}\`;
             
             // HTTP方法和超时
             const method = $json.method || 'POST';
             const timeout = $json.timeout || 10000; // 10秒默认
             
             // 构建请求信息
             return [{
               json: {
                 ...$json,
                 apiRequest: {
                   url: apiUrl,
                   method: method,
                   body: requestBody,
                   timeout: timeout,
                   headers: {
                     'Content-Type': 'application/json',
                     'X-API-Key': \`key_\${serviceId}\`, // 实际项目中使用安全凭证
                     'X-Request-ID': \`req_\${Date.now()}_\${Math.random().toString(36).substring(2, 10)}\`
                   }
                 }
               }
             }];
           `
         }
       },
       {
         id: "10", // 执行API请求
         type: "n8n-nodes-base.HttpRequest",
         parameters: {
           url: "={{ $json.apiRequest.url }}",
           method: "={{ $json.apiRequest.method }}",
           sendBody: true,
           bodyParameters: "={{ $json.apiRequest.body }}",
           options: {
             allowUnauthorizedCerts: false,
             timeout: "={{ $json.apiRequest.timeout }}"
           },
           headerParameters: "={{ $json.apiRequest.headers }}"
         },
         continueOnFail: true
       },
       {
         id: "11", // 更新断路器状态
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 从上下文中获取断路器信息
             const circuitKey = $json.circuitBreaker.key;
             const currentStatus = $json.circuitBreaker.status;
             
             // 检查API请求是否成功
             const statusCode = $node["10"].json.statusCode || 500;
             const isSuccess = statusCode >= 200 && statusCode < 300;
             
             // 更新断路器状态的信息
             let updatedCircuit;
             
             if (isSuccess) {
               // 成功请求处理
               if (currentStatus === 'CLOSED') {
                 // 保持关闭状态，重置失败计数
                 updatedCircuit = {
                   status: 'CLOSED',
                   failureCount: 0,
                   failureThreshold: $json.circuitBreaker.failureThreshold,
                   lastFailure: null,
                   nextAttempt: null,
                   lastSuccess: new Date().toISOString()
                 };
               } else if (currentStatus === 'HALF_OPEN') {
                 // 试探性请求成功，关闭断路器
                 updatedCircuit = {
                   status: 'CLOSED',
                   failureCount: 0,
                   failureThreshold: $json.circuitBreaker.failureThreshold,
                   lastFailure: $json.circuitBreaker.lastFailure, // 保留最后失败记录
                   nextAttempt: null,
                   lastSuccess: new Date().toISOString(),
                   recoveredAt: new Date().toISOString()
                 };
               } else {
                 // OPEN状态不应该到达这里，但仍处理
                 updatedCircuit = {
                   status: 'HALF_OPEN', // 降级到半开状态
                   failureCount: $json.circuitBreaker.failureCount,
                   failureThreshold: $json.circuitBreaker.failureThreshold,
                   lastFailure: $json.circuitBreaker.lastFailure,
                   nextAttempt: new Date().toISOString(), // 立即允许试探
                   lastSuccess: new Date().toISOString()
                 };
               }
             } else {
               // 失败请求处理
               const newFailureCount = ($json.circuitBreaker.failureCount || 0) + 1;
               const failureThreshold = $json.circuitBreaker.failureThreshold;
               
               if (currentStatus === 'CLOSED') {
                 if (newFailureCount >= failureThreshold) {
                   // 超过阈值，打开断路器
                   const resetTimeout = calculateResetTimeout(newFailureCount, failureThreshold);
                   updatedCircuit = {
                     status: 'OPEN',
                     failureCount: newFailureCount,
                     failureThreshold: failureThreshold,
                     lastFailure: new Date().toISOString(),
                     nextAttempt: new Date(Date.now() + resetTimeout).toISOString(),
                     openedAt: new Date().toISOString(),
                     resetTimeoutMs: resetTimeout
                   };
                 } else {
                   // 未超过阈值，增加失败计数
                   updatedCircuit = {
                     status: 'CLOSED',
                     failureCount: newFailureCount,
                     failureThreshold: failureThreshold,
                     lastFailure: new Date().toISOString(),
                     nextAttempt: null
                   };
                 }
               } else if (currentStatus === 'HALF_OPEN') {
                 // 试探性请求失败，回到打开状态并增加超时
                 const resetTimeout = calculateResetTimeout(newFailureCount, failureThreshold);
                 updatedCircuit = {
                   status: 'OPEN',
                   failureCount: newFailureCount,
                   failureThreshold: failureThreshold,
                   lastFailure: new Date().toISOString(),
                   nextAttempt: new Date(Date.now() + resetTimeout).toISOString(),
                   openedAt: new Date().toISOString(),
                   resetTimeoutMs: resetTimeout
                 };
               } else {
                 // OPEN状态加增加失败计数
                 updatedCircuit = {
                   status: 'OPEN',
                   failureCount: newFailureCount,
                   failureThreshold: failureThreshold,
                   lastFailure: new Date().toISOString(),
                   nextAttempt: $json.circuitBreaker.nextAttempt // 保持原有下次尝试时间
                 };
               }
             }
             
             // 更新Redis中的断路器状态（这里我们只是更新上下文）
             const response = {
               originalRequest: $json.apiRequest,
               apiResponse: $node["10"].json,
               circuitBreaker: {
                 key: circuitKey,
                 previousStatus: currentStatus,
                 currentStatus: updatedCircuit.status,
                 ...updatedCircuit
               },
               timestamp: new Date().toISOString()
             };
             
             // 记录断路器状态变更
             if (currentStatus !== updatedCircuit.status) {
               console.log(\`断路器状态变更: \${circuitKey} \${currentStatus} -> \${updatedCircuit.status}\`);
               
               // 这里可以添加记录到审计日志、发送告警通知等操作
               response.circuitStateChange = {
                 from: currentStatus,
                 to: updatedCircuit.status,
                 reason: isSuccess ? "成功请求" : "失败请求",
                 timestamp: new Date().toISOString()
               };
             }
             
             return [{ json: response }];
             
             // 计算断路器重置超时时间（指数退避）
             function calculateResetTimeout(failureCount, threshold) {
               // 基础超时：5秒
               const baseTimeout = 5000;
               // 指数因子：失败次数超过阈值的量
               const factor = Math.max(1, failureCount - threshold + 1);
               // 最大超时：5分钟
               const maxTimeout = 5 * 60 * 1000;
               
               // 计算超时：基础超时 * 2^因子 + 随机抖动
               const timeout = Math.min(
                 baseTimeout * Math.pow(2, factor) + Math.random() * 1000,
                 maxTimeout
               );
               
               return Math.floor(timeout);
             }
           `
         }
       },
       {
         id: "12", // 持久化断路器状态
         type: "n8n-nodes-base.Postgres",
         parameters: {
           operation: "executeQuery",
           query: `
             INSERT INTO circuit_breaker_state 
             (circuit_key, status, failure_count, failure_threshold, last_failure, next_attempt, updated_at)
             VALUES 
             ('{{ $json.circuitBreaker.key }}', '{{ $json.circuitBreaker.currentStatus }}', 
              {{ $json.circuitBreaker.failureCount }}, {{ $json.circuitBreaker.failureThreshold }},
              '{{ $json.circuitBreaker.lastFailure || null }}', 
              '{{ $json.circuitBreaker.nextAttempt || null }}',
              '{{ $json.timestamp }}')
             ON CONFLICT (circuit_key) 
             DO UPDATE SET 
               status = EXCLUDED.status,
               failure_count = EXCLUDED.failure_count,
               last_failure = EXCLUDED.last_failure,
               next_attempt = EXCLUDED.next_attempt,
               updated_at = EXCLUDED.updated_at
           `
         },
         continueOnFail: true
       },
       {
         id: "13", // 记录断路器状态变更
         type: "n8n-nodes-base.IF",
         parameters: {
           conditions: {
             boolean: [
               {
                 value1: "={{ $json.circuitStateChange !== undefined }}",
                 value2: true
               }
             ]
           }
         }
       },
       {
         id: "14", // 保存状态变更记录
         type: "n8n-nodes-base.Postgres",
         parameters: {
           operation: "executeQuery",
           query: `
             INSERT INTO circuit_breaker_events
             (circuit_key, event_type, previous_status, new_status, reason, failure_count, created_at)
             VALUES
             ('{{ $json.circuitBreaker.key }}', 'STATE_CHANGE', 
              '{{ $json.circuitStateChange.from }}', '{{ $json.circuitStateChange.to }}',
              '{{ $json.circuitStateChange.reason }}', {{ $json.circuitBreaker.failureCount }},
              '{{ $json.circuitStateChange.timestamp }}')
           `
         }
       },
       {
         id: "15", // 发送状态变更通知
         type: "n8n-nodes-base.Slack",
         parameters: {
           channel: "circuit-breaker-alerts",
           text: `🔄 断路器状态变更通知

                服务: {{ $json.circuitBreaker.key }}
                状态变更: {{ $json.circuitStateChange.from }} -> {{ $json.circuitStateChange.to }}
                原因: {{ $json.circuitStateChange.reason }}
                失败计数: {{ $json.circuitBreaker.failureCount }} / {{ $json.circuitBreaker.failureThreshold }}
                时间: {{ $json.circuitStateChange.timestamp }}

                {% if $json.circuitStateChange.to == 'OPEN' %}
                ⚠️ 断路器已打开！服务 {{ $json.circuitBreaker.key }} 暂时不可用。
                下次自动尝试时间: {{ $json.circuitBreaker.nextAttempt }}
                {% endif %}

                {% if $json.circuitStateChange.to == 'CLOSED' %}
                ✅ 断路器已关闭！服务 {{ $json.circuitBreaker.key }} 恢复正常。
                {% endif %}`,
           otherOptions: {
             as_user: true
           }
         }
       },
       {
         id: "16", // 构建最终响应
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 从上下文中提取关键信息
             const apiResponse = $node["10"].json;
             const circuitStatus = $json.circuitBreaker.currentStatus;
             
             // 保留原始状态码
             const statusCode = apiResponse.statusCode;
             
             // 添加断路器状态信息到响应中
             const response = {
               ...apiResponse,
               _meta: {
                 circuitBreaker: {
                   service: $json.circuitBreaker.key,
                   status: circuitStatus
                 }
               }
             };
             
             // 如果是半开到关闭的状态变更，添加恢复信息
             if ($json.circuitStateChange && 
                 $json.circuitStateChange.from === 'HALF_OPEN' && 
                 $json.circuitStateChange.to === 'CLOSED') {
               response._meta.serviceRecovered = true;
               response._meta.recoveredAt = $json.circuitBreaker.recoveredAt;
             }
             
             return [{ 
               json: response,
               statusCode: statusCode || 200
             }];
           `
         }
       }
     ],
     connections: {
       "1": { main: [{ node: "2", type: "main", index: 0 }] },
       "2": { main: [{ node: "3", type: "main", index: 0 }] },
       "3": {
         main: [
           { node: "4", type: "main", index: 0 }, // 断路器打开
           { node: "5", type: "main", index: 1 }  // 断路器非打开
         ]
       },
       "5": {
         main: [
           { node: "6", type: "main", index: 0 }, // 断路器半开
           { node: "9", type: "main", index: 1 }  // 断路器关闭
         ]
       },
       "6": { main: [{ node: "7", type: "main", index: 0 }] },
       "7": {
         main: [
           { node: "9", type: "main", index: 0 }, // 允许试探请求
           { node: "8", type: "main", index: 1 }  // 不允许试探请求
         ]
       },
       "9": { main: [{ node: "10", type: "main", index: 0 }] },
       "10": { main: [{ node: "11", type: "main", index: 0 }] },
       "11": { main: [{ node: "12", type: "main", index: 0 }] },
       "12": { main: [{ node: "13", type: "main", index: 0 }] },
       "13": {
         main: [
           { node: "14", type: "main", index: 0 }, // 状态变更
           { node: "16", type: "main", index: 1 }  // 无状态变更
         ]
       },
       "14": { main: [{ node: "15", type: "main", index: 0 }] },
       "15": { main: [{ node: "16", type: "main", index: 0 }] }
     }
   };
   ```

3. **死信队列模式**：
   - 处理失败任务隔离
   - 失败分析与重试
   - 主队列与死信队列分离
   - 适用于异步处理系统

```javascript
   // 死信队列模式工作流示例
   const deadLetterQueueWorkflow = {
     nodes: [
       {
         id: "1", // 主队列消息处理器 (RabbitMQ触发器)
         type: "n8n-nodes-base.RabbitMQ",
         parameters: {
           operations: [
             {
               operation: "consume",
               queue: "main-task-queue"
             }
           ],
           options: {
             acknowledge: true,
             prefetch: 5
           }
         }
       },
       {
         id: "2", // 消息预处理
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 解析消息内容（RabbitMQ消息通常是String）
             try {
               const message = $json.content ? JSON.parse($json.content) : $json;
               
               // 添加处理元数据
               message._meta = {
                 messageId: $json.properties?.messageId || \`msg_\${Date.now()}\`,
                 queueName: "main-task-queue",
                 receivedAt: new Date().toISOString(),
                 retryCount: message._meta?.retryCount || 0,
                 originalReceivedAt: message._meta?.originalReceivedAt || new Date().toISOString()
               };
               
               return [{ json: message }];
             } catch (error) {
               // 解析失败，将原始消息包装为错误对象
               return [{
                 json: {
                   _meta: {
                     messageId: $json.properties?.messageId || \`msg_\${Date.now()}\`,
                     queueName: "main-task-queue",
                     receivedAt: new Date().toISOString(),
                     parseError: true
                   },
                   originalContent: $json.content || $json,
                   error: {
                     message: \`消息解析失败: \${error.message}\`,
                     stack: error.stack
                   }
                 }
               }];
             }
           `
         }
       },
       {
         id: "3", // 检查消息是否有解析错误
         type: "n8n-nodes-base.IF",
         parameters: {
           conditions: {
             boolean: [
               {
                 value1: "={{ $json._meta.parseError }}",
                 value2: true
               }
             ]
           }
         }
       },
       {
         id: "4", // 处理解析错误 - 直接发送到死信队列
         type: "n8n-nodes-base.Function",
         parameters: {
           functionCode: `
             // 准备死信队列消息
             return [{
               json: {
                 ...$json,
                 _meta: {
                   ...$json._meta,
                   movedToDlqAt: new Date().toISOString(),
                   reason: "PARSE_ERROR",
                   processingErrors: [
                        {
                        stage: "parsing",
                        error: $json.error.message,
                        timestamp: new Date().toISOString()
                        }
                    ],
                    dlqType: "permanent" // 解析错误通常需要手动修复
                    }
                }];
                `
       }
     },
     {
       id: "5", // 执行任务处理
       type: "n8n-nodes-base.Function",
       parameters: {
         functionCode: `
           // 从消息中提取任务信息
           const taskType = $json.taskType || "unknown";
           const taskData = $json.data || {};
           
           // 任务处理模拟
           try {
             let result;
             
             // 基于任务类型模拟不同处理
             switch(taskType) {
               case "order_processing":
                 result = processOrder(taskData);
                 break;
               case "payment_confirmation":
                 result = confirmPayment(taskData);
                 break;
               case "inventory_update":
                 result = updateInventory(taskData);
                 break;
               case "email_notification":
                 result = sendEmailNotification(taskData);
                 break;
               default:
                 throw new Error(\`未知任务类型: \${taskType}\`);
             }
             
             // 返回成功结果
             return [{
               json: {
                 ...$json,
                 _meta: {
                   ...$json._meta,
                   processingResult: "success",
                   processedAt: new Date().toISOString()
                 },
                 result: result
               }
             }];
           } catch (error) {
             // 返回处理错误
             return [{
               json: {
                 ...$json,
                 _meta: {
                   ...$json._meta,
                   processingResult: "error",
                   processedAt: new Date().toISOString(),
                   error: {
                     message: error.message,
                     code: error.code || "TASK_PROCESSING_ERROR"
                   }
                 }
               }
             }];
           }
           
           // 模拟订单处理
           function processOrder(data) {
             // 模拟处理逻辑和错误情况
             if (!data.orderId) {
               throw new Error("缺少订单ID");
             }
             
             // 模拟特定条件下的随机错误
             if (data.orderId.includes("ERR") || Math.random() < 0.3) {
               throw new Error("订单处理失败");
             }
             
             return {
               orderStatus: "processed",
               processingDetails: {
                 timestamp: new Date().toISOString(),
                 processor: "order-service-1"
               }
             };
           }
           
           // 模拟支付确认
           function confirmPayment(data) {
             if (!data.paymentId) {
               throw new Error("缺少支付ID");
             }
             
             // 模拟临时错误条件 (例如外部支付网关暂时不可用)
             if (data.paymentId.includes("TEMP") || Math.random() < 0.2) {
               const tempError = new Error("支付网关暂时不可用");
               tempError.code = "TEMPORARY_GATEWAY_ERROR";
               throw tempError;
             }
             
             // 模拟永久错误 (例如付款方式被拒绝)
             if (data.paymentId.includes("PERM")) {
               const permError = new Error("付款方式被拒绝");
               permError.code = "PAYMENT_REJECTED";
               throw permError;
             }
             
             return {
               paymentStatus: "confirmed",
               transactionId: \`txn_\${Date.now()}\`
             };
           }
           
           // 模拟库存更新
           function updateInventory(data) {
             if (!data.productId || !data.quantity) {
               throw new Error("缺少产品ID或数量");
             }
             
             return {
               inventoryUpdated: true,
               newQuantity: Math.max(0, (Math.random() * 100) - data.quantity)
             };
           }
           
           // 模拟邮件发送
           function sendEmailNotification(data) {
             if (!data.recipient) {
               throw new Error("缺少收件人邮箱");
             }
             
             // 模拟发送错误
             if (!data.recipient.includes("@") || Math.random() < 0.1) {
               throw new Error("邮件发送失败");
             }
             
             return {
               emailSent: true,
               messageId: \`email_\${Date.now()}\`
             };
           }
         `
       }
     },
     {
       id: "6", // 检查处理结果
       type: "n8n-nodes-base.IF",
       parameters: {
         conditions: {
           string: [
             {
               value1: "={{ $json._meta.processingResult }}",
               operation: "equals",
               value2: "error"
             }
           ]
         }
       }
     },
     {
       id: "7", // 成功处理 - 确认消息
       type: "n8n-nodes-base.RabbitMQ",
       parameters: {
         operations: [
           {
             operation: "ack",
             deliveryTag: "={{ $node[\"1\"].json.deliveryTag }}"
           }
         ]
       }
     },
     {
       id: "8", // 记录成功处理
       type: "n8n-nodes-base.Postgres",
       parameters: {
         operation: "executeQuery",
         query: `
           INSERT INTO message_processing_log
           (message_id, queue_name, task_type, processing_status, received_at, processed_at, result)
           VALUES
           ('{{ $json._meta.messageId }}', '{{ $json._meta.queueName }}', '{{ $json.taskType }}',
            'SUCCESS', '{{ $json._meta.receivedAt }}', '{{ $json._meta.processedAt }}',
            '{{ $json.result | json_encode | escape_single_quotes }}')
         `
       }
     },
     {
       id: "9", // 错误分析 - 确定是否可重试
       type: "n8n-nodes-base.Function",
       parameters: {
         functionCode: `
           // 提取错误信息
           const errorMessage = $json._meta.error.message;
           const errorCode = $json._meta.error.code;
           const retryCount = $json._meta.retryCount || 0;
           
           // 确定错误类型和重试策略
           let isRetryable = true;
           let dlqType = "temporary"; // 默认为临时死信
           
           // 最大重试次数 (可基于任务类型调整)
           const maxRetries = {
             "order_processing": 3,
             "payment_confirmation": 5,
             "inventory_update": 3,
             "email_notification": 2,
             "default": 3
           }[$json.taskType] || 3;
           
           // 检查是否达到最大重试次数
           if (retryCount >= maxRetries) {
             isRetryable = false;
             dlqType = "max_retry_exceeded";
           }
           
           // 检查已知的不可重试错误
           const nonRetryableErrors = [
             "缺少订单ID", "缺少支付ID", "缺少产品ID或数量", "缺少收件人邮箱", // 缺少必需参数
             "付款方式被拒绝", "PAYMENT_REJECTED", // 业务逻辑拒绝
             "数据验证失败" // 数据问题
           ];
           
           if (nonRetryableErrors.some(e => errorMessage.includes(e))) {
             isRetryable = false;
             dlqType = "permanent";
           }
           
           // 特定错误码处理
           if (errorCode === "TEMPORARY_GATEWAY_ERROR") {
             // 支付网关临时错误特别处理 - 使用更长的重试延迟
             isRetryable = true;
             dlqType = "payment_gateway_temp_error";
           }
           
           // 记录分析结果
           return [{
             json: {
               ...$json,
               _meta: {
                 ...$json._meta,
                 errorAnalysis: {
                   isRetryable: isRetryable,
                   dlqType: dlqType,
                   maxRetries: maxRetries,
                   retryCount: retryCount,
                   analysisTimestamp: new Date().toISOString()
                 }
               }
             }
           }];
         `
       }
     },
     {
       id: "10", // 检查是否可重试
       type: "n8n-nodes-base.IF",
       parameters: {
         conditions: {
           boolean: [
             {
               value1: "={{ $json._meta.errorAnalysis.isRetryable }}",
               value2: true
             }
           ]
         }
       }
     },
     {
       id: "11", // 准备重试 - 增加重试计数和延迟
       type: "n8n-nodes-base.Function",
       parameters: {
         functionCode: `
           // 增加重试计数
           const currentRetry = $json._meta.retryCount || 0;
           const newRetryCount = currentRetry + 1;
           
           // 计算指数退避延迟 (基础延迟 * 2^重试次数 + 随机抖动)
           let baseDelayMs = 5000; // 5秒基础延迟
           
           // 特定DLQ类型的自定义延迟
           if ($json._meta.errorAnalysis.dlqType === "payment_gateway_temp_error") {
             baseDelayMs = 30000; // 支付网关错误使用30秒基础延迟
           }
           
           const delayMs = Math.min(
             baseDelayMs * Math.pow(2, newRetryCount) + (Math.random() * 1000),
             900000 // 最大15分钟
           );
           
           // 生成下次执行时间
           const nextAttemptTime = new Date(Date.now() + delayMs);
           
           // 更新消息元数据
           return [{
             json: {
               ...$json,
               _meta: {
                 ...$json._meta,
                 retrySchedule: {
                   retryCount: newRetryCount,
                   previousRetryAt: $json._meta.processedAt,
                   nextRetryAt: nextAttemptTime.toISOString(),
                   delayMs: delayMs
                 }
               }
             }
           }];
         `
       }
     },
     {
       id: "12", // 发送到重试队列
       type: "n8n-nodes-base.RabbitMQ",
       parameters: {
         operations: [
           {
             operation: "publish",
             exchange: "retry-exchange",
             routingKey: "retry.{{ $json.taskType }}",
             options: {
               headers: {
                 "x-retry-count": "={{ $json._meta.retrySchedule.retryCount }}",
                 "x-original-queue": "{{ $json._meta.queueName }}",
                 "x-next-retry-time": "={{ $json._meta.retrySchedule.nextRetryAt }}"
               },
               expiration: "={{ $json._meta.retrySchedule.delayMs }}",
               messageId: "={{ $json._meta.messageId }}"
             },
             contentType: "application/json",
             content: "={{ $json | json_encode }}"
           }
         ]
       }
     },
     {
       id: "13", // 确认原始消息
       type: "n8n-nodes-base.RabbitMQ",
       parameters: {
         operations: [
           {
             operation: "ack",
             deliveryTag: "={{ $node[\"1\"].json.deliveryTag }}"
           }
         ]
       }
     },
     {
       id: "14", // 记录重试安排
       type: "n8n-nodes-base.Postgres",
       parameters: {
         operation: "executeQuery",
         query: `
           INSERT INTO message_retry_log
           (message_id, original_queue, task_type, retry_count, error_message, processed_at, next_retry_at)
           VALUES
           ('{{ $json._meta.messageId }}', '{{ $json._meta.queueName }}', '{{ $json.taskType }}',
            {{ $json._meta.retrySchedule.retryCount }}, '{{ $json._meta.error.message | escape_single_quotes }}',
            '{{ $json._meta.processedAt }}', '{{ $json._meta.retrySchedule.nextRetryAt }}')
         `
       }
     },
     {
       id: "15", // 准备不可重试消息发送到死信队列
       type: "n8n-nodes-base.Function",
       parameters: {
         functionCode: `
           // 准备死信队列消息
           return [{
             json: {
               ...$json,
               _meta: {
                 ...$json._meta,
                 movedToDlqAt: new Date().toISOString(),
                 reason: $json._meta.errorAnalysis.dlqType,
                 processingErrors: [
                   {
                     stage: "task_processing",
                     error: $json._meta.error.message,
                     code: $json._meta.error.code,
                     timestamp: $json._meta.processedAt
                   }
                 ]
               }
             }
           }];
         `
       }
     },
     {
       id: "16", // 发送到死信队列
       type: "n8n-nodes-base.RabbitMQ",
       parameters: {
         operations: [
           {
             operation: "publish",
             exchange: "dlx",
             routingKey: "dlq.{{ $json.taskType }}.{{ $json._meta.reason }}",
             options: {
               headers: {
                 "x-original-queue": "{{ $json._meta.queueName }}",
                 "x-error-reason": "={{ $json._meta.reason }}",
                 "x-retry-count": "={{ $json._meta.retryCount || 0 }}",
                 "x-moved-to-dlq-at": "={{ $json._meta.movedToDlqAt }}"
               },
               persistent: true,
               messageId: "={{ $json._meta.messageId }}"
             },
             contentType: "application/json",
             content: "={{ $json | json_encode }}"
           }
         ]
       }
     },
     {
       id: "17", // 确认原始消息 (死信路径)
       type: "n8n-nodes-base.RabbitMQ",
       parameters: {
         operations: [
           {
             operation: "ack",
             deliveryTag: "={{ $node[\"1\"].json.deliveryTag }}"
           }
         ]
       }
     },
     {
       id: "18", // 记录死信队列移动
       type: "n8n-nodes-base.Postgres",
       parameters: {
         operation: "executeQuery",
         query: `
           INSERT INTO dead_letter_log
           (message_id, original_queue, task_type, retry_count, error_message, reason, 
            received_at, processed_at, moved_to_dlq_at)
           VALUES
           ('{{ $json._meta.messageId }}', '{{ $json._meta.queueName }}', '{{ $json.taskType }}',
            {{ $json._meta.retryCount || 0 }}, '{{ $json._meta.error.message | escape_single_quotes }}',
            '{{ $json._meta.reason }}', '{{ $json._meta.receivedAt }}', 
            '{{ $json._meta.processedAt }}', '{{ $json._meta.movedToDlqAt }}')
         `
       }
     },
     {
       id: "19", // 发送死信队列通知
       type: "n8n-nodes-base.Slack",
       parameters: {
         channel: "dlq-notifications",
         text: `⚠️ 消息已移至死信队列

        任务类型: {{ $json.taskType }}
        消息ID: {{ $json._meta.messageId }}
        错误原因: {{ $json._meta.error.message }}
        错误代码: {{ $json._meta.error.code || "N/A" }}
        重试次数: {{ $json._meta.retryCount || 0 }}
        死信类型: {{ $json._meta.reason }}

        {% if $json._meta.reason == "max_retry_exceeded" %}
        🔄 消息重试已达最大次数 ({{ $json._meta.errorAnalysis.maxRetries }})
        {% endif %}

        {% if $json._meta.reason == "permanent" %}
        🚫 消息包含不可重试的错误
        {% endif %}

        时间: {{ $json._meta.movedToDlqAt }}`,
            otherOptions: {
            as_user: true
            }
        }
        }
    ],
    connections: {
        "1": { main: [{ node: "2", type: "main", index: 0 }] },
        "2": { main: [{ node: "3", type: "main", index: 0 }] },
        "3": {
        main: [
            { node: "4", type: "main", index: 0 }, // 解析错误
            { node: "5", type: "main", index: 1 }  // 消息格式正确
        ]
        },
        "4": { main: [{ node: "16", type: "main", index: 0 }] },
        "5": { main: [{ node: "6", type: "main", index: 0 }] },
        "6": {
        main: [
            { node: "9", type: "main", index: 0 },  // 处理错误
            { node: "7", type: "main", index: 1 }   // 处理成功
        ]
        },
        "7": { main: [{ node: "8", type: "main", index: 0 }] },
        "9": { main: [{ node: "10", type: "main", index: 0 }] },
        "10": {
        main: [
            { node: "11", type: "main", index: 0 }, // 可重试
            { node: "15", type: "main", index: 1 }  // 不可重试
            ]
            },
            "11": { main: [{ node: "12", type: "main", index: 0 }] },
            "12": { main: [{ node: "13", type: "main", index: 0 }] },
            "13": { main: [{ node: "14", type: "main", index: 0 }] },
            "15": { main: [{ node: "16", type: "main", index: 0 }] },
            "16": { main: [{ node: "17", type: "main", index: 0 }] },
            "17": { main: [{ node: "18", type: "main", index: 0 }] },
            "18": { main: [{ node: "19", type: "main", index: 0 }] }
        }
    }
```

## 分布式工作流程系统架构组件

前面我们讨论了一些关键的弹性模式，现在我将概述分布式工作流系统的主要架构组件，这些组件协同工作形成一个完整的工作流程系统：

### 1. 核心组件

1. **工作流引擎**
   - 负责工作流的解析、执行和状态管理
   - 支持不同的执行模式（同步、异步、分布式）
   - 实现工作流生命周期管理

2. **调度器**
   - 基于依赖关系、资源可用性和优先级安排任务执行
   - 实现公平调度和负载均衡
   - 支持基于时间的调度（cron表达式）和事件驱动调度

3. **任务执行器**
   - 执行各种类型的任务（计算、数据处理、服务调用）
   - 处理任务重试和失败恢复
   - 管理任务资源和隔离

4. **状态存储**
   - 持久化工作流和任务状态
   - 支持事务性状态更新
   - 提供历史记录和审计日志

5. **消息队列**
   - 处理异步工作流步骤之间的通信
   - 实现事件驱动的工作流触发
   - 提供缓冲和背压机制

### 2. 弹性组件

1. **故障检测器**
   - 监控节点和任务健康状态
   - 实现心跳机制和超时检测
   - 快速识别和报告故障

2. **重试管理器**
   - 实现不同的重试策略（指数退避、随机抖动）
   - 处理临时和永久性故障
   - 与死信队列集成

3. **断路器管理**
   - 监控外部服务调用失败率
   - 自动打开和关闭断路器
   - 实现半开状态的试探性请求

4. **补偿事务管理器**
   - 跟踪已完成的事务步骤
   - 发生故障时执行补偿操作
   - 维护系统一致性

### 3. 扩展组件

1. **工作流仓库**
   - 存储和管理工作流定义
   - 支持版本控制和发布管理
   - 提供模板和可重用组件

2. **API网关**
   - 作为工作流系统的入口点
   - 处理身份验证和授权
   - 实现请求限流和转换

3. **监控和可观测性**
   - 收集指标、日志和追踪
   - 提供实时仪表板和告警
   - 支持性能分析和瓶颈识别

4. **数据转换引擎**
   - 处理输入和输出数据映射
   - 支持多种数据格式转换
   - 实现数据验证和清洗

### 4. 管理组件

1. **工作流设计器**
   - 图形化工作流创建界面
   - 支持拖放式节点连接
   - 提供测试和调试工具

2. **用户和权限管理**
   - 管理用户账户和身份验证
   - 实现基于角色的访问控制
   - 支持细粒度权限设置

3. **配置管理**
   - 存储和管理系统配置
   - 支持环境特定的设置
   - 实现配置变更审计

4. **资源管理**
   - 跟踪和分配系统资源
   - 实现资源配额和限制
   - 支持动态资源扩展

## 分布式工作流系统设计考虑因素

### 1. 可扩展性

- **水平扩展**：系统应能通过添加更多节点线性扩展
- **无状态设计**：计算节点应尽可能保持无状态，状态存储在专用存储层
- **分片策略**：实现数据和工作流分片以均衡负载
- **局部性感知**：尽可能将相关任务调度到同一节点减少网络开销

### 2. 一致性与持久性

- **状态持久化**：工作流状态应持久化以防节点故障
- **幂等性**：任务应设计为幂等，支持安全重试
- **事务边界**：明确定义事务边界，处理分布式事务挑战
- **最终一致性**：某些情况下接受最终一致性以提高性能

### 3. 故障恢复

- **检查点机制**：定期保存工作流状态以支持从中间点恢复
- **故障隔离**：限制故障影响范围，防止故障传播
- **自动恢复**：系统应能自动检测和恢复故障
- **手动干预**：提供必要时的手动干预机制

### 4. 可观测性

- **综合监控**：收集系统各层面的指标
- **分布式追踪**：实现请求在系统中的端到端追踪
- **集中式日志**：汇总和关联不同组件的日志
- **健康检查**：提供各组件的健康状态API

### 5. 安全性

- **认证与授权**：实现强身份验证和访问控制
- **密钥管理**：安全存储和管理敏感凭证
- **网络安全**：实现网络隔离和加密通信
- **审计日志**：记录系统操作以支持审计和合规

## 当前技术趋势

在分布式工作流系统领域，以下技术趋势正在塑造未来的发展方向：

1. **Serverless工作流**：无需管理基础设施的工作流执行
2. **事件驱动架构**：基于事件的工作流触发和交互
3. **增强的可观测性**：更深入的系统洞察和问题诊断
4. **多云工作流**：跨不同云提供商的工作流执行
5. **AI辅助工作流**：使用AI优化工作流设计和执行

通过这些架构组件和设计考虑因素，我们可以构建能够处理复杂业务逻辑、可靠执行并具有弹性的分布式工作流系统。n8n作为一个开源的工作流自动化平台，体现了许多这些原则和模式，为实际的工作流自动化提供了强大的基础。
