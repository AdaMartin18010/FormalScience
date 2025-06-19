# 微服务架构

## 📋 概述

微服务架构是一种将应用程序构建为一组小型、独立服务的架构风格，每个服务运行在自己的进程中，通过轻量级机制进行通信。本文档系统性地介绍微服务架构的理论基础、设计原则、实现技术和实际应用。

## 🎯 核心目标

1. **建立微服务架构的理论框架**
2. **系统化服务拆分和设计原则**
3. **提供通信和数据管理解决方案**
4. **展示实际应用案例**

## 📚 目录

1. [基本概念](#1-基本概念)
2. [形式化定义](#2-形式化定义)
3. [定理与证明](#3-定理与证明)
4. [代码实现](#4-代码实现)
5. [应用示例](#5-应用示例)
6. [相关理论](#6-相关理论)
7. [参考文献](#7-参考文献)

## 1. 基本概念

### 1.1 微服务架构的定义

微服务架构是一种软件架构风格，其核心特征包括：

- **服务拆分**：将应用拆分为小型、独立的服务
- **独立部署**：每个服务可以独立部署和扩展
- **技术多样性**：不同服务可以使用不同技术栈
- **去中心化**：没有统一的数据存储或技术标准

### 1.2 微服务设计原则

#### 1.2.1 单一职责原则

```latex
单一职责 = {
    业务边界: {领域驱动设计, 业务能力, 业务功能},
    技术边界: {技术栈, 数据存储, 部署环境},
    团队边界: {团队结构, 所有权, 责任划分}
}
```

#### 1.2.2 服务自治原则

```latex
服务自治 = {
    独立部署: {部署单元, 版本管理, 回滚策略},
    独立扩展: {水平扩展, 垂直扩展, 资源分配},
    独立故障: {故障隔离, 容错机制, 降级策略}
}
```

#### 1.2.3 数据隔离原则

```latex
数据隔离 = {
    数据库分离: {独立数据库, 数据所有权, 数据一致性},
    数据同步: {事件驱动, 消息队列, 数据复制},
    数据治理: {数据质量, 数据安全, 数据合规}
}
```

### 1.3 服务通信模式

#### 1.3.1 同步通信

- **REST API**：基于HTTP的RESTful接口
- **gRPC**：高性能的RPC框架
- **GraphQL**：灵活的查询语言

#### 1.3.2 异步通信

- **消息队列**：可靠的消息传递
- **事件驱动**：基于事件的松耦合通信
- **发布订阅**：一对多的消息广播

## 2. 形式化定义

### 2.1 微服务定义

**定义 2.1** (微服务):
微服务是一个五元组 $S = (I, P, D, C, E)$，其中：

```latex
S = (I, P, D, C, E)

其中:
- I: 接口集合
- P: 进程标识
- D: 数据存储
- C: 配置信息
- E: 环境依赖
```

### 2.2 服务组合定义

**定义 2.2** (服务组合):
微服务系统是一个三元组 $MS = (S, R, T)$，其中：

```latex
MS = (S, R, T)

其中:
- S: 服务集合
- R: 服务关系集合
- T: 拓扑结构
```

### 2.3 服务通信定义

**定义 2.3** (服务通信):
服务通信是一个四元组 $C = (S_1, S_2, P, M)$，其中：

```latex
C = (S₁, S₂, P, M)

其中:
- S₁: 源服务
- S₂: 目标服务
- P: 协议
- M: 消息格式
```

## 3. 定理与证明

### 3.1 服务独立性定理

**定理 3.1** (服务独立性):
如果微服务 $S_1$ 和 $S_2$ 是独立的，则 $S_1$ 的故障不会影响 $S_2$ 的正常运行。

**证明**:
```latex
1. 服务独立性定义: Independent(S₁, S₂) ⟺ ¬Depend(S₁, S₂)
2. 故障隔离: Fault(S₁) ⟹ ¬Fault(S₂)
3. 因此: Independent(S₁, S₂) ⟹ Fault(S₁) ⟹ ¬Fault(S₂)
```

### 3.2 服务可扩展性定理

**定理 3.2** (服务可扩展性):
如果微服务 $S$ 是无状态的，则 $S$ 可以水平扩展。

**证明**:
```latex
1. 无状态定义: Stateless(S) ⟺ ∀σ₁, σ₂: State(S, σ₁) = State(S, σ₂)
2. 水平扩展: Scalable(S) ⟺ ∀n: ∃S₁, ..., Sₙ: S = S₁ ∪ ... ∪ Sₙ
3. 因此: Stateless(S) ⟹ Scalable(S)
```

### 3.3 数据一致性定理

**定理 3.3** (数据一致性):
在微服务架构中，强一致性需要分布式事务，而最终一致性可以通过事件驱动实现。

**证明**:
```latex
1. 强一致性: StrongConsistency ⟺ ∀t: State(t) = State(t-1)
2. 最终一致性: EventualConsistency ⟺ ∃t: State(t) = State(t-1)
3. 分布式事务: DistributedTransaction ⟹ StrongConsistency
4. 事件驱动: EventDriven ⟹ EventualConsistency
```

## 4. 代码实现

### 4.1 微服务框架 (Rust)

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use tokio::sync::mpsc;
use serde::{Deserialize, Serialize};

/// 微服务定义
#[derive(Debug, Clone, Serialize, Deserialize)]
struct Microservice {
    id: String,
    name: String,
    version: String,
    endpoints: Vec<Endpoint>,
    dependencies: Vec<String>,
    health_check: HealthCheck,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct Endpoint {
    path: String,
    method: String,
    handler: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct HealthCheck {
    path: String,
    interval: u64,
    timeout: u64,
}

/// 服务注册表
struct ServiceRegistry {
    services: Arc<Mutex<HashMap<String, Vec<ServiceInstance>>>>,
}

impl ServiceRegistry {
    fn new() -> Self {
        Self {
            services: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    async fn register(&self, service: ServiceInstance) -> Result<(), String> {
        let mut services = self.services.lock().unwrap();
        let service_list = services.entry(service.service_name.clone()).or_insert_with(Vec::new);
        service_list.push(service);
        Ok(())
    }

    async fn discover(&self, service_name: &str) -> Result<Vec<ServiceInstance>, String> {
        let services = self.services.lock().unwrap();
        services.get(service_name)
            .cloned()
            .ok_or_else(|| "Service not found".to_string())
    }

    async fn deregister(&self, service_id: &str) -> Result<(), String> {
        let mut services = self.services.lock().unwrap();
        for service_list in services.values_mut() {
            service_list.retain(|s| s.id != service_id);
        }
        Ok(())
    }
}

/// 服务实例
#[derive(Debug, Clone, Serialize, Deserialize)]
struct ServiceInstance {
    id: String,
    service_name: String,
    url: String,
    port: u16,
    health_status: HealthStatus,
    metadata: HashMap<String, String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
enum HealthStatus {
    Healthy,
    Unhealthy,
    Unknown,
}

/// 负载均衡器
trait LoadBalancer {
    fn select(&self, instances: &[ServiceInstance]) -> Result<ServiceInstance, String>;
}

/// 轮询负载均衡器
struct RoundRobinBalancer {
    current_index: Arc<Mutex<usize>>,
}

impl RoundRobinBalancer {
    fn new() -> Self {
        Self {
            current_index: Arc::new(Mutex::new(0)),
        }
    }
}

impl LoadBalancer for RoundRobinBalancer {
    fn select(&self, instances: &[ServiceInstance]) -> Result<ServiceInstance, String> {
        if instances.is_empty() {
            return Err("No instances available".to_string());
        }

        let mut index = self.current_index.lock().unwrap();
        let selected = instances[*index % instances.len()].clone();
        *index += 1;
        Ok(selected)
    }
}

/// 熔断器
struct CircuitBreaker {
    failure_threshold: usize,
    failure_count: Arc<Mutex<usize>>,
    state: Arc<Mutex<CircuitState>>,
    last_failure_time: Arc<Mutex<Option<std::time::Instant>>>,
}

#[derive(Debug, Clone)]
enum CircuitState {
    Closed,
    Open,
    HalfOpen,
}

impl CircuitBreaker {
    fn new(failure_threshold: usize) -> Self {
        Self {
            failure_threshold,
            failure_count: Arc::new(Mutex::new(0)),
            state: Arc::new(Mutex::new(CircuitState::Closed)),
            last_failure_time: Arc::new(Mutex::new(None)),
        }
    }

    async fn execute<F, T>(&self, operation: F) -> Result<T, String>
    where
        F: FnOnce() -> Result<T, String>,
    {
        let state = *self.state.lock().unwrap();
        
        match state {
            CircuitState::Open => {
                let last_failure = *self.last_failure_time.lock().unwrap();
                if let Some(failure_time) = last_failure {
                    if failure_time.elapsed().as_secs() > 60 {
                        // 尝试半开状态
                        *self.state.lock().unwrap() = CircuitState::HalfOpen;
                        self.execute(operation).await
                    } else {
                        Err("Circuit breaker is open".to_string())
                    }
                } else {
                    Err("Circuit breaker is open".to_string())
                }
            }
            CircuitState::HalfOpen => {
                match operation() {
                    Ok(result) => {
                        *self.state.lock().unwrap() = CircuitState::Closed;
                        *self.failure_count.lock().unwrap() = 0;
                        Ok(result)
                    }
                    Err(e) => {
                        *self.state.lock().unwrap() = CircuitState::Open;
                        *self.last_failure_time.lock().unwrap() = Some(std::time::Instant::now());
                        Err(e)
                    }
                }
            }
            CircuitState::Closed => {
                match operation() {
                    Ok(result) => Ok(result),
                    Err(e) => {
                        let mut count = self.failure_count.lock().unwrap();
                        *count += 1;
                        
                        if *count >= self.failure_threshold {
                            *self.state.lock().unwrap() = CircuitState::Open;
                            *self.last_failure_time.lock().unwrap() = Some(std::time::Instant::now());
                        }
                        Err(e)
                    }
                }
            }
        }
    }
}

/// 服务客户端
struct ServiceClient {
    registry: Arc<ServiceRegistry>,
    load_balancer: Arc<dyn LoadBalancer + Send + Sync>,
    circuit_breaker: Arc<CircuitBreaker>,
}

impl ServiceClient {
    fn new(registry: Arc<ServiceRegistry>, load_balancer: Arc<dyn LoadBalancer + Send + Sync>) -> Self {
        Self {
            registry,
            load_balancer,
            circuit_breaker: Arc::new(CircuitBreaker::new(5)),
        }
    }

    async fn call_service(&self, service_name: &str, request: &str) -> Result<String, String> {
        // 服务发现
        let instances = self.registry.discover(service_name).await?;
        
        // 负载均衡
        let instance = self.load_balancer.select(&instances)?;
        
        // 熔断器保护
        self.circuit_breaker.execute(|| {
            // 简化的HTTP调用
            Ok(format!("Response from {}: {}", instance.service_name, request))
        }).await
    }
}

/// 消息队列
struct MessageQueue {
    channels: Arc<Mutex<HashMap<String, mpsc::Sender<Message>>>>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct Message {
    id: String,
    topic: String,
    data: String,
    timestamp: std::time::SystemTime,
}

impl MessageQueue {
    fn new() -> Self {
        Self {
            channels: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    async fn publish(&self, topic: &str, message: Message) -> Result<(), String> {
        let channels = self.channels.lock().unwrap();
        if let Some(sender) = channels.get(topic) {
            sender.send(message).await.map_err(|e| e.to_string())?;
            Ok(())
        } else {
            Err("Topic not found".to_string())
        }
    }

    async fn subscribe(&self, topic: &str) -> Result<mpsc::Receiver<Message>, String> {
        let (sender, receiver) = mpsc::channel(100);
        let mut channels = self.channels.lock().unwrap();
        channels.insert(topic.to_string(), sender);
        Ok(receiver)
    }
}

/// 微服务系统
struct MicroserviceSystem {
    registry: Arc<ServiceRegistry>,
    client: Arc<ServiceClient>,
    message_queue: Arc<MessageQueue>,
}

impl MicroserviceSystem {
    fn new() -> Self {
        let registry = Arc::new(ServiceRegistry::new());
        let load_balancer = Arc::new(RoundRobinBalancer::new());
        let client = Arc::new(ServiceClient::new(Arc::clone(&registry), load_balancer));
        let message_queue = Arc::new(MessageQueue::new());

        Self {
            registry,
            client,
            message_queue,
        }
    }

    async fn start_service(&self, service: Microservice) -> Result<(), String> {
        let instance = ServiceInstance {
            id: format!("{}-{}", service.id, uuid::Uuid::new_v4()),
            service_name: service.name,
            url: "localhost".to_string(),
            port: 8080,
            health_status: HealthStatus::Healthy,
            metadata: HashMap::new(),
        };

        self.registry.register(instance).await
    }

    async fn call_service(&self, service_name: &str, request: &str) -> Result<String, String> {
        self.client.call_service(service_name, request).await
    }

    async fn publish_message(&self, topic: &str, data: &str) -> Result<(), String> {
        let message = Message {
            id: uuid::Uuid::new_v4().to_string(),
            topic: topic.to_string(),
            data: data.to_string(),
            timestamp: std::time::SystemTime::now(),
        };

        self.message_queue.publish(topic, message).await
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_service_registration() {
        let registry = ServiceRegistry::new();
        
        let instance = ServiceInstance {
            id: "test-1".to_string(),
            service_name: "user-service".to_string(),
            url: "localhost".to_string(),
            port: 8080,
            health_status: HealthStatus::Healthy,
            metadata: HashMap::new(),
        };

        registry.register(instance).await.unwrap();
        
        let instances = registry.discover("user-service").await.unwrap();
        assert_eq!(instances.len(), 1);
        assert_eq!(instances[0].service_name, "user-service");
    }

    #[tokio::test]
    async fn test_load_balancing() {
        let balancer = RoundRobinBalancer::new();
        
        let instances = vec![
            ServiceInstance {
                id: "1".to_string(),
                service_name: "service".to_string(),
                url: "localhost".to_string(),
                port: 8081,
                health_status: HealthStatus::Healthy,
                metadata: HashMap::new(),
            },
            ServiceInstance {
                id: "2".to_string(),
                service_name: "service".to_string(),
                url: "localhost".to_string(),
                port: 8082,
                health_status: HealthStatus::Healthy,
                metadata: HashMap::new(),
            },
        ];

        let selected1 = balancer.select(&instances).unwrap();
        let selected2 = balancer.select(&instances).unwrap();
        
        assert_ne!(selected1.id, selected2.id);
    }

    #[tokio::test]
    async fn test_circuit_breaker() {
        let breaker = CircuitBreaker::new(3);
        
        // 测试成功操作
        let result = breaker.execute(|| Ok("success")).await;
        assert!(result.is_ok());
        
        // 测试失败操作
        let result = breaker.execute(|| Err("failure".to_string())).await;
        assert!(result.is_err());
    }
}
```

### 4.2 事件驱动微服务 (Haskell)

```haskell
-- 微服务定义
data Microservice = Microservice {
    serviceId :: String,
    serviceName :: String,
    serviceVersion :: String,
    serviceEndpoints :: [Endpoint],
    serviceDependencies :: [String],
    serviceHealthCheck :: HealthCheck
} deriving (Show, Eq)

data Endpoint = Endpoint {
    endpointPath :: String,
    endpointMethod :: String,
    endpointHandler :: String -> IO String
} deriving (Show)

data HealthCheck = HealthCheck {
    healthPath :: String,
    healthInterval :: Int,
    healthTimeout :: Int
} deriving (Show, Eq)

-- 服务实例
data ServiceInstance = ServiceInstance {
    instanceId :: String,
    instanceServiceName :: String,
    instanceUrl :: String,
    instancePort :: Int,
    instanceHealthStatus :: HealthStatus,
    instanceMetadata :: [(String, String)]
} deriving (Show, Eq)

data HealthStatus = 
    Healthy
  | Unhealthy
  | Unknown
  deriving (Show, Eq)

-- 事件定义
data Event = Event {
    eventId :: String,
    eventType :: String,
    eventData :: String,
    eventTimestamp :: UTCTime,
    eventSource :: String
} deriving (Show, Eq)

-- 事件总线
class EventBus a where
    publish :: a -> Event -> IO ()
    subscribe :: a -> String -> (Event -> IO ()) -> IO ()
    unsubscribe :: a -> String -> IO ()

-- 简单事件总线实现
data SimpleEventBus = SimpleEventBus {
    subscribers :: IORef [(String, Event -> IO ())],
    eventQueue :: IORef [Event]
} deriving (Show)

instance EventBus SimpleEventBus where
    publish bus event = do
        queue <- readIORef (eventQueue bus)
        writeIORef (eventQueue bus) (event : queue)
        
        subs <- readIORef (subscribers bus)
        mapM_ (\(eventType, handler) -> 
            when (eventType == eventType event) $ handler event) subs
    
    subscribe bus eventType handler = do
        subs <- readIORef (subscribers bus)
        writeIORef (subscribers bus) ((eventType, handler) : subs)
    
    unsubscribe bus eventType = do
        subs <- readIORef (subscribers bus)
        writeIORef (subscribers bus) (filter (\(et, _) -> et /= eventType) subs)

-- 服务注册表
class ServiceRegistry a where
    register :: a -> ServiceInstance -> IO ()
    discover :: a -> String -> IO [ServiceInstance]
    deregister :: a -> String -> IO ()

data SimpleRegistry = SimpleRegistry {
    services :: IORef [(String, [ServiceInstance])]
} deriving (Show)

instance ServiceRegistry SimpleRegistry where
    register registry instance_ = do
        services_map <- readIORef (services registry)
        let service_name = instanceServiceName instance_
        let updated_map = updateServiceList services_map service_name instance_
        writeIORef (services registry) updated_map
    
    discover registry service_name = do
        services_map <- readIORef (services registry)
        return $ maybe [] id (lookup service_name services_map)
    
    deregister registry instance_id = do
        services_map <- readIORef (services registry)
        let updated_map = map (\(name, instances) -> 
            (name, filter (\i -> instanceId i /= instance_id) instances)) services_map
        writeIORef (services registry) updated_map

updateServiceList :: [(String, [ServiceInstance])] -> String -> ServiceInstance -> [(String, [ServiceInstance])]
updateServiceList services_map service_name instance_ =
    case lookup service_name services_map of
        Just instances -> (service_name, instance_ : instances) : filter (\(name, _) -> name /= service_name) services_map
        Nothing -> (service_name, [instance_]) : services_map

-- 负载均衡器
class LoadBalancer a where
    select :: a -> [ServiceInstance] -> IO ServiceInstance

data RoundRobinBalancer = RoundRobinBalancer {
    currentIndex :: IORef Int
} deriving (Show)

instance LoadBalancer RoundRobinBalancer where
    select balancer instances = do
        if null instances
        then error "No instances available"
        else do
            index <- readIORef (currentIndex balancer)
            let selected = instances !! (index `mod` length instances)
            writeIORef (currentIndex balancer) (index + 1)
            return selected

-- 熔断器
data CircuitBreaker = CircuitBreaker {
    failureThreshold :: Int,
    failureCount :: IORef Int,
    state :: IORef CircuitState,
    lastFailureTime :: IORef (Maybe UTCTime)
} deriving (Show)

data CircuitState = 
    Closed
  | Open
  | HalfOpen
  deriving (Show, Eq)

executeWithCircuitBreaker :: CircuitBreaker -> IO a -> IO (Either String a)
executeWithCircuitBreaker breaker operation = do
    currentState <- readIORef (state breaker)
    
    case currentState of
        Open -> do
            lastFailure <- readIORef (lastFailureTime breaker)
            currentTime <- getCurrentTime
            
            case lastFailure of
                Just failureTime -> do
                    let timeDiff = diffUTCTime currentTime failureTime
                    if timeDiff > 60 -- 60秒后尝试半开
                    then do
                        writeIORef (state breaker) HalfOpen
                        executeWithCircuitBreaker breaker operation
                    else
                        return $ Left "Circuit breaker is open"
                Nothing ->
                    return $ Left "Circuit breaker is open"
        
        HalfOpen -> do
            result <- try operation
            case result of
                Left _ -> do
                    writeIORef (state breaker) Open
                    writeIORef (lastFailureTime breaker) (Just =<< getCurrentTime)
                    return $ Left "Circuit breaker opened"
                Right value -> do
                    writeIORef (state breaker) Closed
                    writeIORef (failureCount breaker) 0
                    return $ Right value
        
        Closed -> do
            result <- try operation
            case result of
                Left _ -> do
                    count <- readIORef (failureCount breaker)
                    writeIORef (failureCount breaker) (count + 1)
                    
                    if count + 1 >= failureThreshold breaker
                    then do
                        writeIORef (state breaker) Open
                        writeIORef (lastFailureTime breaker) (Just =<< getCurrentTime)
                        return $ Left "Circuit breaker opened"
                    else
                        return $ Left "Operation failed"
                Right value ->
                    return $ Right value

-- 微服务客户端
data ServiceClient = ServiceClient {
    clientRegistry :: SimpleRegistry,
    clientLoadBalancer :: RoundRobinBalancer,
    clientCircuitBreaker :: CircuitBreaker
} deriving (Show)

callService :: ServiceClient -> String -> String -> IO (Either String String)
callService client service_name request = do
    -- 服务发现
    instances <- discover (clientRegistry client) service_name
    
    if null instances
    then return $ Left "Service not found"
    else do
        -- 负载均衡
        selected_instance <- select (clientLoadBalancer client) instances
        
        -- 熔断器保护
        executeWithCircuitBreaker (clientCircuitBreaker client) $ do
            -- 简化的服务调用
            return $ "Response from " ++ instanceServiceName selected_instance ++ ": " ++ request

-- 微服务系统
data MicroserviceSystem = MicroserviceSystem {
    systemRegistry :: SimpleRegistry,
    systemClient :: ServiceClient,
    systemEventBus :: SimpleEventBus
} deriving (Show)

createMicroserviceSystem :: IO MicroserviceSystem
createMicroserviceSystem = do
    registry <- SimpleRegistry <$> newIORef []
    balancer <- RoundRobinBalancer <$> newIORef 0
    breaker <- CircuitBreaker 5 <$> newIORef 0 <*> newIORef Closed <*> newIORef Nothing
    client <- return $ ServiceClient registry balancer breaker
    event_bus <- SimpleEventBus <$> newIORef [] <*> newIORef []
    
    return $ MicroserviceSystem registry client event_bus

-- 示例服务
createUserService :: IO Microservice
createUserService = do
    let endpoints = [
            Endpoint {
                endpointPath = "/users",
                endpointMethod = "GET",
                endpointHandler = \request -> return $ "User data: " ++ request
            }
        ]
    
    return $ Microservice {
        serviceId = "user-service-1",
        serviceName = "user-service",
        serviceVersion = "1.0.0",
        serviceEndpoints = endpoints,
        serviceDependencies = [],
        serviceHealthCheck = HealthCheck "/health" 30 5
    }

-- 测试
testMicroserviceSystem :: IO ()
testMicroserviceSystem = do
    system <- createMicroserviceSystem
    
    -- 创建服务实例
    let instance = ServiceInstance {
        instanceId = "user-1",
        instanceServiceName = "user-service",
        instanceUrl = "localhost",
        instancePort = 8080,
        instanceHealthStatus = Healthy,
        instanceMetadata = []
    }
    
    -- 注册服务
    register (systemRegistry system) instance
    
    -- 调用服务
    result <- callService (systemClient system) "user-service" "get_user_123"
    print result
    
    -- 发布事件
    current_time <- getCurrentTime
    let event = Event {
        eventId = "event-1",
        eventType = "user_created",
        eventData = "user_123",
        eventTimestamp = current_time,
        eventSource = "user-service"
    }
    
    publish (systemEventBus system) event
    putStrLn "Event published"
```

## 5. 应用示例

### 5.1 电商微服务系统

```rust
/// 电商微服务系统
#[derive(Debug, Clone)]
struct ECommerceMicroservices {
    user_service: Arc<UserService>,
    product_service: Arc<ProductService>,
    order_service: Arc<OrderService>,
    payment_service: Arc<PaymentService>,
    inventory_service: Arc<InventoryService>,
}

impl ECommerceMicroservices {
    fn new() -> Self {
        let user_service = Arc::new(UserService::new());
        let product_service = Arc::new(ProductService::new());
        let order_service = Arc::new(OrderService::new());
        let payment_service = Arc::new(PaymentService::new());
        let inventory_service = Arc::new(InventoryService::new());

        Self {
            user_service,
            product_service,
            order_service,
            payment_service,
            inventory_service,
        }
    }

    async fn create_order(&self, user_id: &str, product_id: &str, quantity: i32) -> Result<String, String> {
        // 1. 验证用户
        let user = self.user_service.get_user(user_id).await?;
        
        // 2. 获取产品信息
        let product = self.product_service.get_product(product_id).await?;
        
        // 3. 检查库存
        let available = self.inventory_service.check_stock(product_id, quantity).await?;
        if !available {
            return Err("Insufficient stock".to_string());
        }
        
        // 4. 创建订单
        let order = self.order_service.create_order(user_id, product_id, quantity).await?;
        
        // 5. 处理支付
        let payment = self.payment_service.process_payment(&order).await?;
        
        // 6. 更新库存
        self.inventory_service.update_stock(product_id, quantity).await?;
        
        Ok(format!("Order created: {}", order))
    }
}

/// 用户服务
struct UserService {
    users: Arc<Mutex<HashMap<String, User>>>,
}

#[derive(Debug, Clone)]
struct User {
    id: String,
    name: String,
    email: String,
    status: UserStatus,
}

#[derive(Debug, Clone)]
enum UserStatus {
    Active,
    Inactive,
    Suspended,
}

impl UserService {
    fn new() -> Self {
        Self {
            users: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    async fn get_user(&self, user_id: &str) -> Result<User, String> {
        let users = self.users.lock().unwrap();
        users.get(user_id)
            .cloned()
            .ok_or_else(|| "User not found".to_string())
    }

    async fn create_user(&self, name: &str, email: &str) -> Result<User, String> {
        let user = User {
            id: uuid::Uuid::new_v4().to_string(),
            name: name.to_string(),
            email: email.to_string(),
            status: UserStatus::Active,
        };

        let mut users = self.users.lock().unwrap();
        users.insert(user.id.clone(), user.clone());
        Ok(user)
    }
}

/// 产品服务
struct ProductService {
    products: Arc<Mutex<HashMap<String, Product>>>,
}

#[derive(Debug, Clone)]
struct Product {
    id: String,
    name: String,
    price: f64,
    category: String,
}

impl ProductService {
    fn new() -> Self {
        Self {
            products: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    async fn get_product(&self, product_id: &str) -> Result<Product, String> {
        let products = self.products.lock().unwrap();
        products.get(product_id)
            .cloned()
            .ok_or_else(|| "Product not found".to_string())
    }

    async fn create_product(&self, name: &str, price: f64, category: &str) -> Result<Product, String> {
        let product = Product {
            id: uuid::Uuid::new_v4().to_string(),
            name: name.to_string(),
            price,
            category: category.to_string(),
        };

        let mut products = self.products.lock().unwrap();
        products.insert(product.id.clone(), product.clone());
        Ok(product)
    }
}

/// 订单服务
struct OrderService {
    orders: Arc<Mutex<HashMap<String, Order>>>,
}

#[derive(Debug, Clone)]
struct Order {
    id: String,
    user_id: String,
    product_id: String,
    quantity: i32,
    status: OrderStatus,
    created_at: std::time::SystemTime,
}

#[derive(Debug, Clone)]
enum OrderStatus {
    Pending,
    Confirmed,
    Shipped,
    Delivered,
    Cancelled,
}

impl OrderService {
    fn new() -> Self {
        Self {
            orders: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    async fn create_order(&self, user_id: &str, product_id: &str, quantity: i32) -> Result<Order, String> {
        let order = Order {
            id: uuid::Uuid::new_v4().to_string(),
            user_id: user_id.to_string(),
            product_id: product_id.to_string(),
            quantity,
            status: OrderStatus::Pending,
            created_at: std::time::SystemTime::now(),
        };

        let mut orders = self.orders.lock().unwrap();
        orders.insert(order.id.clone(), order.clone());
        Ok(order)
    }
}

/// 支付服务
struct PaymentService {
    payments: Arc<Mutex<HashMap<String, Payment>>>,
}

#[derive(Debug, Clone)]
struct Payment {
    id: String,
    order_id: String,
    amount: f64,
    status: PaymentStatus,
}

#[derive(Debug, Clone)]
enum PaymentStatus {
    Pending,
    Completed,
    Failed,
    Refunded,
}

impl PaymentService {
    fn new() -> Self {
        Self {
            payments: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    async fn process_payment(&self, order: &Order) -> Result<Payment, String> {
        let payment = Payment {
            id: uuid::Uuid::new_v4().to_string(),
            order_id: order.id.clone(),
            amount: 100.0, // 简化计算
            status: PaymentStatus::Completed,
        };

        let mut payments = self.payments.lock().unwrap();
        payments.insert(payment.id.clone(), payment.clone());
        Ok(payment)
    }
}

/// 库存服务
struct InventoryService {
    inventory: Arc<Mutex<HashMap<String, i32>>>,
}

impl InventoryService {
    fn new() -> Self {
        Self {
            inventory: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    async fn check_stock(&self, product_id: &str, quantity: i32) -> Result<bool, String> {
        let inventory = self.inventory.lock().unwrap();
        let available = inventory.get(product_id).unwrap_or(&0);
        Ok(*available >= quantity)
    }

    async fn update_stock(&self, product_id: &str, quantity: i32) -> Result<(), String> {
        let mut inventory = self.inventory.lock().unwrap();
        let current = inventory.get(product_id).unwrap_or(&0);
        inventory.insert(product_id.to_string(), current - quantity);
        Ok(())
    }
}

#[cfg(test)]
mod ecommerce_tests {
    use super::*;

    #[tokio::test]
    async fn test_order_creation() {
        let system = ECommerceMicroservices::new();
        
        // 创建用户
        let user = system.user_service.create_user("John Doe", "john@example.com").await.unwrap();
        
        // 创建产品
        let product = system.product_service.create_product("Laptop", 999.99, "Electronics").await.unwrap();
        
        // 创建订单
        let result = system.create_order(&user.id, &product.id, 1).await;
        assert!(result.is_ok());
    }
}
```

### 5.2 事件驱动订单处理

```rust
/// 事件驱动订单处理系统
#[derive(Debug, Clone)]
struct EventDrivenOrderSystem {
    event_bus: Arc<EventBus>,
    order_service: Arc<OrderService>,
    inventory_service: Arc<InventoryService>,
    payment_service: Arc<PaymentService>,
    notification_service: Arc<NotificationService>,
}

impl EventDrivenOrderSystem {
    fn new() -> Self {
        let event_bus = Arc::new(EventBus::new());
        let order_service = Arc::new(OrderService::new());
        let inventory_service = Arc::new(InventoryService::new());
        let payment_service = Arc::new(PaymentService::new());
        let notification_service = Arc::new(NotificationService::new());

        let system = Self {
            event_bus: Arc::clone(&event_bus),
            order_service: Arc::clone(&order_service),
            inventory_service: Arc::clone(&inventory_service),
            payment_service: Arc::clone(&payment_service),
            notification_service: Arc::clone(&notification_service),
        };

        // 设置事件处理器
        system.setup_event_handlers();
        system
    }

    fn setup_event_handlers(&self) {
        let event_bus = Arc::clone(&self.event_bus);
        let order_service = Arc::clone(&self.order_service);
        let inventory_service = Arc::clone(&self.inventory_service);
        let payment_service = Arc::clone(&self.payment_service);
        let notification_service = Arc::clone(&self.notification_service);

        // 订单创建事件处理器
        event_bus.subscribe("order_created", move |event| {
            let order_id = event.data.clone();
            
            // 检查库存
            if let Ok(available) = inventory_service.check_stock_async(&order_id).await {
                if available {
                    event_bus.publish(Event {
                        event_type: "inventory_reserved".to_string(),
                        data: order_id,
                        timestamp: std::time::SystemTime::now(),
                    });
                } else {
                    event_bus.publish(Event {
                        event_type: "order_cancelled".to_string(),
                        data: order_id,
                        timestamp: std::time::SystemTime::now(),
                    });
                }
            }
        });

        // 库存预留事件处理器
        event_bus.subscribe("inventory_reserved", move |event| {
            let order_id = event.data.clone();
            
            // 处理支付
            if let Ok(payment) = payment_service.process_payment_async(&order_id).await {
                if payment.status == PaymentStatus::Completed {
                    event_bus.publish(Event {
                        event_type: "payment_completed".to_string(),
                        data: order_id,
                        timestamp: std::time::SystemTime::now(),
                    });
                } else {
                    event_bus.publish(Event {
                        event_type: "payment_failed".to_string(),
                        data: order_id,
                        timestamp: std::time::SystemTime::now(),
                    });
                }
            }
        });

        // 支付完成事件处理器
        event_bus.subscribe("payment_completed", move |event| {
            let order_id = event.data.clone();
            
            // 发送通知
            notification_service.send_order_confirmation(&order_id);
            
            // 更新订单状态
            order_service.update_order_status(&order_id, OrderStatus::Confirmed);
        });
    }

    async fn create_order(&self, user_id: &str, product_id: &str, quantity: i32) -> Result<String, String> {
        // 创建订单
        let order = self.order_service.create_order(user_id, product_id, quantity).await?;
        
        // 发布订单创建事件
        self.event_bus.publish(Event {
            event_type: "order_created".to_string(),
            data: order.id.clone(),
            timestamp: std::time::SystemTime::now(),
        });

        Ok(order.id)
    }
}

/// 事件总线
struct EventBus {
    handlers: Arc<Mutex<HashMap<String, Vec<Box<dyn Fn(Event) + Send + Sync>>>>>,
}

#[derive(Debug, Clone)]
struct Event {
    event_type: String,
    data: String,
    timestamp: std::time::SystemTime,
}

impl EventBus {
    fn new() -> Self {
        Self {
            handlers: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    fn subscribe<F>(&self, event_type: &str, handler: F)
    where
        F: Fn(Event) + Send + Sync + 'static,
    {
        let mut handlers = self.handlers.lock().unwrap();
        let event_handlers = handlers.entry(event_type.to_string()).or_insert_with(Vec::new);
        event_handlers.push(Box::new(handler));
    }

    fn publish(&self, event: Event) {
        let handlers = self.handlers.lock().unwrap();
        if let Some(event_handlers) = handlers.get(&event.event_type) {
            for handler in event_handlers {
                handler(event.clone());
            }
        }
    }
}

/// 通知服务
struct NotificationService;

impl NotificationService {
    fn new() -> Self {
        Self
    }

    fn send_order_confirmation(&self, order_id: &str) {
        println!("Sending order confirmation for order: {}", order_id);
    }
}
```

## 6. 相关理论

### 6.1 与分布式系统的关系

- **分布式架构**：微服务是分布式系统的一种实现
- **一致性模型**：微服务需要处理分布式一致性
- **故障处理**：微服务需要容错和故障恢复机制

### 6.2 与事件驱动架构的关系

- **事件通信**：微服务可以通过事件进行通信
- **松耦合**：事件驱动实现服务间的松耦合
- **异步处理**：事件支持异步处理模式

### 6.3 与容器技术的关系

- **容器化部署**：微服务通常部署在容器中
- **编排管理**：需要容器编排工具管理服务
- **资源隔离**：容器提供资源隔离

### 6.4 与API网关的关系

- **统一入口**：API网关作为微服务的统一入口
- **路由转发**：网关负责请求路由和转发
- **安全控制**：网关提供认证和授权

## 7. 参考文献

1. Newman, S. (2021). Building microservices: Designing fine-grained systems. O'Reilly Media.
2. Richardson, C. (2018). Microservices patterns: With examples in Java. Manning Publications.
3. Fowler, M. (2014). Microservices. Martin Fowler's Blog.
4. Evans, E. (2003). Domain-driven design: Tackling complexity in the heart of software. Addison-Wesley.
5. Hohpe, G., & Woolf, B. (2003). Enterprise integration patterns: Designing, building, and deploying messaging solutions. Addison-Wesley.

---

**相关文档**:
- [软件架构设计原则](../02_Software_Architecture/01_Architecture_Design_Principles.md)
- [架构模式理论](../02_Software_Architecture/02_Architecture_Pattern_Theory.md)
- [事件驱动架构](../02_Software_Architecture/04_Event_Driven_Architecture.md)
- [分布式系统理论](../06_Distributed_Systems_Theory/01_Distributed_Systems_Foundation.md) 