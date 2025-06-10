# 依赖注入机制与设计模式的形式化分析

## 目录

- [依赖注入机制与设计模式的形式化分析](#依赖注入机制与设计模式的形式化分析)
  - [目录](#目录)
  - [基本概念与定义](#基本概念与定义)
    - [依赖注入的形式化定义](#依赖注入的形式化定义)
    - [设计模式与架构模式的形式化表示](#设计模式与架构模式的形式化表示)
  - [依赖注入的实现机制](#依赖注入的实现机制)
    - [特征基础依赖注入](#特征基础依赖注入)
    - [泛型实现依赖注入](#泛型实现依赖注入)
    - [服务定位器模式](#服务定位器模式)
  - [形式化验证框架](#形式化验证框架)
    - [属性规约与验证](#属性规约与验证)
    - [状态机模型](#状态机模型)
    - [时序逻辑表达](#时序逻辑表达)
  - [依赖注入与设计模式的关联性](#依赖注入与设计模式的关联性)
    - [IoC容器与工厂模式](#ioc容器与工厂模式)
    - [代理模式与装饰器模式](#代理模式与装饰器模式)
    - [构建器模式与类型状态模式](#构建器模式与类型状态模式)
  - [元模型与元理论](#元模型与元理论)
    - [依赖注入的范畴论解释](#依赖注入的范畴论解释)
    - [依赖图与态射](#依赖图与态射)
    - [函子框架](#函子框架)
  - [多层次架构模式与依赖注入](#多层次架构模式与依赖注入)
    - [层次化依赖注入](#层次化依赖注入)
    - [层次边界验证](#层次边界验证)
    - [跨层依赖管理](#跨层依赖管理)
  - [实践与形式化验证的权衡](#实践与形式化验证的权衡)
    - [成本效益分析](#成本效益分析)
    - [选择性应用](#选择性应用)
  - [思维导图](#思维导图)
  - [依赖注入的高级实现技术](#依赖注入的高级实现技术)
    - [编译时依赖验证](#编译时依赖验证)
    - [特征对象与动态分发](#特征对象与动态分发)
    - [基于生命周期的作用域管理](#基于生命周期的作用域管理)
  - [依赖注入与函数式编程](#依赖注入与函数式编程)
    - [Reader Monad模式](#reader-monad模式)
    - [函数组合与依赖传递](#函数组合与依赖传递)
    - [纯函数架构](#纯函数架构)
  - [依赖注入的形式化证明](#依赖注入的形式化证明)
    - [类型系统保证](#类型系统保证)
    - [依赖图的数学性质](#依赖图的数学性质)
    - [正确性证明](#正确性证明)
  - [依赖注入与其他架构模式的结合](#依赖注入与其他架构模式的结合)
    - [事件驱动架构](#事件驱动架构)
    - [CQRS模式](#cqrs模式)
    - [微服务架构](#微服务架构)
  - [依赖注入的实践模式与反模式](#依赖注入的实践模式与反模式)
    - [最佳实践](#最佳实践)
    - [常见反模式](#常见反模式)
    - [测试策略](#测试策略)
  - [思维导图（续）](#思维导图续)

## 基本概念与定义

### 依赖注入的形式化定义

依赖注入（Dependency Injection，DI）是一种设计模式，可以形式化定义为：

**定义1.1**: 设组件 $C$ 依赖于服务 $S$。依赖注入是一种机制，使得 $S$ 的具体实现被注入到 $C$ 中，而非由 $C$ 直接创建或查找 $S$ 的实例。

**公理1.1**: 如果组件 $C$ 通过依赖注入接收服务 $S$，则 $C$ 不包含对 $S$ 具体实现的直接引用，仅依赖于 $S$ 的抽象接口。

在 Rust 中，依赖注入通常通过特征（trait）和泛型实现：

```rust
// 服务接口（特征）
trait Logger {
    fn log(&self, message: &str);
}

// 服务实现
struct ConsoleLogger;
impl Logger for ConsoleLogger {
    fn log(&self, message: &str) {
        println!("[LOG] {}", message);
    }
}

// 依赖于服务的组件
struct UserService<L> {
    logger: L,
}

impl<L: Logger> UserService<L> {
    fn new(logger: L) -> Self {
        UserService { logger }
    }
    
    fn create_user(&self, name: &str) {
        self.logger.log(&format!("创建用户: {}", name));
        // 用户创建逻辑...
    }
}

// 使用依赖注入
fn main() {
    let logger = ConsoleLogger;
    let service = UserService::new(logger);
    service.create_user("张三");
}
```

### 设计模式与架构模式的形式化表示

**定义1.2**: 设计模式是解决特定上下文中常见问题的可重用解决方案，可形式化为三元组 $(P, S, C)$，其中 $P$ 是问题，$S$ 是解决方案，$C$ 是应用上下文。

**定义1.3**: 架构模式是一种高层次的设计模式，关注系统的整体结构和组件间的交互，可形式化为 $(C, R, P)$，其中 $C$ 是组件集合，$R$ 是组件间关系，$P$ 是应用的属性或约束。

## 依赖注入的实现机制

### 特征基础依赖注入

Rust中最基本的依赖注入形式是通过特征（trait）和泛型约束实现的：

```rust
// 定义服务接口
trait UserRepository {
    fn find_by_id(&self, id: u64) -> Option<User>;
    fn save(&self, user: &User) -> Result<(), Error>;
}

trait EmailService {
    fn send_email(&self, to: &str, subject: &str, body: &str) -> Result<(), Error>;
}

// 实现用户服务，通过特征抽象其依赖
struct UserService<R, E>
where
    R: UserRepository,
    E: EmailService,
{
    user_repository: R,
    email_service: E,
}

impl<R, E> UserService<R, E>
where
    R: UserRepository,
    E: EmailService,
{
    fn new(user_repository: R, email_service: E) -> Self {
        UserService {
            user_repository,
            email_service,
        }
    }
    
    fn register_user(&self, username: &str, email: &str) -> Result<User, Error> {
        // 创建新用户
        let user = User::new(username, email);
        
        // 保存用户
        self.user_repository.save(&user)?;
        
        // 发送欢迎邮件
        self.email_service.send_email(
            email,
            "欢迎加入",
            &format!("你好 {}，欢迎注册我们的服务！", username)
        )?;
        
        Ok(user)
    }
}
```

**定理2.1**: 特征基础依赖注入在编译时保证类型安全，消除了运行时类型错误的可能性。

### 泛型实现依赖注入

泛型依赖注入扩展了特征基础方法，允许更灵活的组件配置：

```rust
struct UserService<L, D> {
    logger: L,
    database: D,
}

impl<L: Logger, D: Database> UserService<L, D> {
    fn new(logger: L, database: D) -> Self {
        UserService { logger, database }
    }
    
    fn find_user(&self, id: u64) -> Vec<String> {
        self.logger.log(&format!("寻找用户ID: {}", id));
        self.database.query(&format!("SELECT * FROM users WHERE id = {}", id))
    }
}
```

**推论2.1**: 泛型依赖注入使组件配置更加灵活，同时保持了编译时类型检查的优势。

### 服务定位器模式

服务定位器提供依赖管理的另一种方法，尤其适用于需要运行时解析依赖的场景：

```rust
use std::any::{Any, TypeId};
use std::collections::HashMap;

struct ServiceLocator {
    services: HashMap<TypeId, Box<dyn Any>>,
}

impl ServiceLocator {
    fn new() -> Self {
        ServiceLocator {
            services: HashMap::new(),
        }
    }
    
    fn register<T: 'static>(&mut self, service: T) {
        self.services.insert(TypeId::of::<T>(), Box::new(service));
    }
    
    fn resolve<T: 'static>(&self) -> Option<&T> {
        self.services.get(&TypeId::of::<T>())
            .and_then(|boxed| boxed.downcast_ref::<T>())
    }
}
```

**命题2.1**: 服务定位器提供运行时灵活性，但牺牲了编译时类型安全性，可能导致运行时错误。

## 形式化验证框架

### 属性规约与验证

形式化验证确保依赖注入系统满足特定属性：

```rust
// 形式化验证框架
struct FormalVerifier {
    property_specifications: HashMap<String, FormalProperty>,
    model_checker: ModelChecker,
    theorem_prover: TheoremProver,
}

enum FormalProperty {
    Safety(String),      // 安全性属性（不好的事情不会发生）
    Liveness(String),    // 活性属性（好的事情最终会发生）
    Invariant(String),   // 不变式
}

// 验证属性
impl FormalVerifier {
    fn verify_deadlock_freedom(&self, dependency_graph: &DependencyGraph) -> VerificationResult {
        // 检查循环依赖
        if let Some(cycle) = self.detect_cycle(dependency_graph) {
            return VerificationResult::False {
                counterexample: Some(format!("循环依赖: {}", 
                    cycle.iter().collect::<Vec<_>>().join(" -> "))),
                property: "无死锁".to_string(),
            };
        }
        
        VerificationResult::True {
            property: "无死锁".to_string(),
        }
    }
}
```

**定理3.1**: 在一个没有循环依赖的依赖图中，依赖解析总是能够终止。

### 状态机模型

依赖注入系统可以建模为状态机：

```rust
#[derive(Debug, Clone, PartialEq)]
struct DIContainerState {
    registered_components: HashMap<TypeId, ComponentState>,
    resolution_stack: Vec<TypeId>,
    resolved_instances: HashMap<TypeId, InstanceId>,
}

enum ResolutionStatus {
    NotStarted,
    InProgress,
    Resolved,
    Failed(String),
}

impl DIContainerState {
    fn register_component<T: 'static>(&mut self, implementation: ComponentImplementation) {
        self.registered_components.insert(
            TypeId::of::<T>(), 
            ComponentState {
                status: ResolutionStatus::NotStarted,
                implementation,
                dependencies: Vec::new(),
            }
        );
    }
    
    fn resolve<T: 'static>(&mut self) -> Result<InstanceId, String> {
        let type_id = TypeId::of::<T>();
        
        // 已解析的组件直接返回
        if let Some(instance) = self.resolved_instances.get(&type_id) {
            return Ok(*instance);
        }
        
        // 检测循环依赖
        if self.resolution_stack.contains(&type_id) {
            return Err(format!("循环依赖检测到: {:?}", self.resolution_stack));
        }
        
        // 开始解析
        self.resolution_stack.push(type_id);
        
        // 解析组件
        let component = self.registered_components.get(&type_id)
            .ok_or_else(|| format!("未注册组件: {:?}", type_id))?;
        
        // 解析依赖
        let mut resolved_deps = Vec::new();
        for dep_type_id in &component.dependencies {
            let dep_instance = self.resolve_by_id(*dep_type_id)?;
            resolved_deps.push(dep_instance);
        }
        
        // 创建实例
        let instance_id = self.create_instance(type_id, &resolved_deps);
        
        // 完成解析
        self.resolution_stack.pop();
        self.resolved_instances.insert(type_id, instance_id);
        
        Ok(instance_id)
    }
}
```

**引理3.1**: 对于状态机模型中的任意有效状态转换序列，如果不存在循环依赖，则解析过程一定会终止。

### 时序逻辑表达

使用时序逻辑表达依赖注入系统的属性：

```rust
// 时序逻辑公式
enum TemporalLogicFormula {
    Atom(String),
    Not(Box<TemporalLogicFormula>),
    And(Box<TemporalLogicFormula>, Box<TemporalLogicFormula>),
    Or(Box<TemporalLogicFormula>, Box<TemporalLogicFormula>),
    Implies(Box<TemporalLogicFormula>, Box<TemporalLogicFormula>),
    Always(Box<TemporalLogicFormula>),
    Eventually(Box<TemporalLogicFormula>),
    Until(Box<TemporalLogicFormula>, Box<TemporalLogicFormula>),
}

// 无循环依赖属性
fn no_circular_dependencies() -> TemporalLogicFormula {
    TemporalLogicFormula::Always(Box::new(
        TemporalLogicFormula::Not(Box::new(
            TemporalLogicFormula::Atom("存在循环依赖".to_string())
        ))
    ))
}

// 所有依赖最终解析属性
fn all_dependencies_eventually_resolved() -> TemporalLogicFormula {
    TemporalLogicFormula::Always(Box::new(
        TemporalLogicFormula::Implies(
            Box::new(TemporalLogicFormula::Atom("开始解析".to_string())),
            Box::new(TemporalLogicFormula::Eventually(Box::new(
                TemporalLogicFormula::Atom("解析完成".to_string())
            )))
        )
    ))
}
```

**定理3.2**: 依赖注入系统满足活性属性当且仅当对于任意组件，如果开始解析，则最终会完成解析或失败。

## 依赖注入与设计模式的关联性

### IoC容器与工厂模式

依赖注入容器与工厂模式密切相关：

```rust
// IoC容器实现
struct Container {
    factories: HashMap<TypeId, Box<dyn Any>>,
}

impl Container {
    fn new() -> Self {
        Container {
            factories: HashMap::new(),
        }
    }
    
    // 注册工厂函数
    fn register<T: 'static, F>(&mut self, factory: F)
    where
        F: Fn(&Container) -> T + 'static,
    {
        let factory_box: Box<dyn Fn(&Container) -> T> = Box::new(factory);
        self.factories.insert(TypeId::of::<T>(), Box::new(factory_box));
    }
    
    // 解析组件
    fn resolve<T: 'static>(&self) -> Result<T, String> {
        let type_id = TypeId::of::<T>();
        
        let factory = self.factories.get(&type_id)
            .ok_or_else(|| format!("未注册类型: {:?}", type_id))?;
        
        let factory_fn = factory.downcast_ref::<Box<dyn Fn(&Container) -> T>>()
            .ok_or_else(|| "内部类型错误".to_string())?;
        
        Ok(factory_fn(self))
    }
}
```

**定理4.1**: IoC容器可以视为工厂模式的扩展，为每个组件提供工厂函数，并管理依赖解析。

### 代理模式与装饰器模式

代理模式与依赖注入结合可实现横切关注点的分离：

```rust
// 服务接口
trait Service {
    fn request(&self) -> String;
}

// 真实服务
struct RealService;
impl Service for RealService {
    fn request(&self) -> String {
        "RealService: 处理请求".to_string()
    }
}

// 日志代理
struct LoggingProxy<T: Service> {
    service: T,
}

impl<T: Service> LoggingProxy<T> {
    fn new(service: T) -> Self {
        LoggingProxy { service }
    }
}

impl<T: Service> Service for LoggingProxy<T> {
    fn request(&self) -> String {
        println!("Proxy: 记录请求时间");
        let result = self.service.request();
        println!("Proxy: 记录响应时间");
        result
    }
}
```

**推论4.1**: 代理模式与依赖注入结合可以在不修改原始组件的情况下增强其功能，实现横切关注点的分离。

### 构建器模式与类型状态模式

类型状态模式可以与依赖注入结合，确保组件正确初始化：

```rust
// 类型状态
struct Uninitialized;
struct Initialized;
struct Running;

// 应用程序状态容器
struct Application<State> {
    services: HashMap<TypeId, Box<dyn Any>>,
    _state: PhantomData<State>,
}

impl Application<Uninitialized> {
    fn new() -> Self {
        Application {
            services: HashMap::new(),
            _state: PhantomData,
        }
    }
    
    fn register<T: 'static>(&mut self, service: T) -> &mut Self {
        self.services.insert(TypeId::of::<T>(), Box::new(service));
        self
    }
    
    fn initialize(self) -> Application<Initialized> {
        // 初始化逻辑
        Application {
            services: self.services,
            _state: PhantomData,
        }
    }
}

impl Application<Initialized> {
    fn run(self) -> Application<Running> {
        // 启动应用
        Application {
            services: self.services,
            _state: PhantomData,
        }
    }
}

impl<State> Application<State> {
    fn get<T: 'static>(&self) -> Option<&T> {
        self.services.get(&TypeId::of::<T>())
            .and_then(|boxed| boxed.downcast_ref::<T>())
    }
}
```

**定理4.2**: 类型状态模式与依赖注入结合可以在编译时强制执行组件生命周期约束。

## 元模型与元理论

### 依赖注入的范畴论解释

依赖注入可以从范畴论角度建模：

- **对象**: 组件和服务接口
- **态射**: 依赖关系
- **函子**: 从抽象接口到具体实现的映射

**定理5.1**: 依赖图形成一个有向范畴，其中没有循环依赖当且仅当该范畴是一个有向无环图。

### 依赖图与态射

依赖图可以形式化为图论结构：

```rust
struct DependencyGraph {
    nodes: HashSet<TypeId>,
    edges: HashMap<TypeId, HashSet<TypeId>>,
}

impl DependencyGraph {
    fn new() -> Self {
        DependencyGraph {
            nodes: HashSet::new(),
            edges: HashMap::new(),
        }
    }
    
    fn add_node(&mut self, type_id: TypeId) {
        self.nodes.insert(type_id);
        if !self.edges.contains_key(&type_id) {
            self.edges.insert(type_id, HashSet::new());
        }
    }
    
    fn add_edge(&mut self, from: TypeId, to: TypeId) {
        self.add_node(from);
        self.add_node(to);
        self.edges.get_mut(&from).unwrap().insert(to);
    }
    
    fn detect_cycle(&self) -> Option<Vec<TypeId>> {
        // 深度优先搜索检测循环
        let mut visited = HashSet::new();
        let mut stack = HashSet::new();
        
        for node in &self.nodes {
            if !visited.contains(node) {
                if let Some(cycle) = self.dfs_cycle(*node, &mut visited, &mut stack, &mut Vec::new()) {
                    return Some(cycle);
                }
            }
        }
        
        None
    }
    
    fn dfs_cycle(
        &self,
        node: TypeId,
        visited: &mut HashSet<TypeId>,
        stack: &mut HashSet<TypeId>,
        path: &mut Vec<TypeId>,
    ) -> Option<Vec<TypeId>> {
        visited.insert(node);
        stack.insert(node);
        path.push(node);
        
        if let Some(neighbors) = self.edges.get(&node) {
            for neighbor in neighbors {
                if !visited.contains(neighbor) {
                    if let Some(cycle) = self.dfs_cycle(*neighbor, visited, stack, path) {
                        return Some(cycle);
                    }
                } else if stack.contains(neighbor) {
                    // 找到循环
                    let cycle_start = path.iter().position(|&n| n == *neighbor).unwrap();
                    return Some(path[cycle_start..].to_vec());
                }
            }
        }
        
        stack.remove(&node);
        path.pop();
        None
    }
}
```

**引理5.1**: 在依赖图中，拓扑排序提供了一个有效的依赖解析顺序当且仅当图中没有循环。

### 函子框架

形式化验证可以使用函子框架建模：

```rust
// 验证函子
struct VerificationFunctor;

impl VerificationFunctor {
    // 函子将规范映射到验证结果
    fn map(&self, spec: &FormalSpecification) -> VerificationResult {
        // 验证规范
        let mut property_results = HashMap::new();
        
        for (name, property) in &spec.properties {
            let result = match property {
                Property::Safety(formula) => {
                    self.verify_safety_property(formula)
                },
                Property::Liveness(formula) => {
                    self.verify_liveness_property(formula)
                },
                Property::Invariant(formula) => {
                    self.verify_invariant(formula)
                },
            };
            
            property_results.insert(name.clone(), result);
        }
        
        VerificationResult {
            verified: property_results.values().all(|r| r.verified),
            property_results,
            counter_examples: self.extract_counter_examples(&property_results),
        }
    }
}
```

**定理5.2**: 验证函子保持范畴结构，即对于规范转换 $f: A \to B$，有 $F(f): F(A) \to F(B)$，其中 $F$ 是验证函子，$F(A)$ 和 $F(B)$ 是验证结果。

## 多层次架构模式与依赖注入

### 层次化依赖注入

多层架构中的依赖注入需要考虑层次边界：

```rust
// 定义应用层次
enum Layer {
    Presentation,
    Application,
    Domain,
    Infrastructure,
}

// 层次依赖规则
struct LayerDependencyRules {
    allowed_dependencies: HashMap<Layer, HashSet<Layer>>,
}

impl LayerDependencyRules {
    fn new() -> Self {
        let mut rules = LayerDependencyRules {
            allowed_dependencies: HashMap::new(),
        };
        
        // 初始化默认规则
        rules.allowed_dependencies.insert(Layer::Presentation, {
            let mut set = HashSet::new();
            set.insert(Layer::Application);
            set
        });
        
        rules.allowed_dependencies.insert(Layer::Application, {
            let mut set = HashSet::new();
            set.insert(Layer::Domain);
            set
        });
        
        rules.allowed_dependencies.insert(Layer::Domain, HashSet::new());
        
        rules.allowed_dependencies.insert(Layer::Infrastructure, {
            let mut set = HashSet::new();
            set.insert(Layer::Domain);
            set
        });
        
        rules
    }
    
    fn is_dependency_allowed(&self, from_layer: Layer, to_layer: Layer) -> bool {
        // 同层依赖总是允许的
        if from_layer == to_layer {
            return true;
        }
        
        // 检查跨层依赖是否被允许
        if let Some(allowed_layers) = self.allowed_dependencies.get(&from_layer) {
            allowed_layers.contains(&to_layer)
        } else {
            false
        }
    }
}
```

**定理6.1**: 在多层架构中，依赖关系应当遵循层次规则，即每层仅依赖于允许的目标层。

### 层次边界验证

边界验证器确保组件遵循层次依赖规则：

```rust
// 边界验证器
struct BoundaryValidator {
    layer_rules: LayerDependencyRules,
}

impl BoundaryValidator {
    fn new(rules: LayerDependencyRules) -> Self {
        BoundaryValidator { layer_rules: rules }
    }
    
    fn validate_dependency(&self, component: &Component) -> Result<(), String> {
        for dep in &component.dependencies {
            if !self.layer_rules.is_dependency_allowed(component.layer, dep.layer) {
                return Err(format!(
                    "非法跨层依赖: {:?} ({:?}) -> {:?} ({:?})",
                    component.name, component.layer, dep.name, dep.layer
                ));
            }
        }
        
        Ok(())
    }
    
    fn validate_all(&self, components: &[Component]) -> Result<(), Vec<String>> {
        let mut errors = Vec::new();
        
        for component in components {
            if let Err(err) = self.validate_dependency(component) {
                errors.push(err);
            }
        }
        
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
}
```

**引理6.1**: 一个系统满足层次依赖规则当且仅当所有组件的所有依赖都符合层次依赖规则。

### 跨层依赖管理

依赖反转原则可以解决跨层依赖问题：

```rust
// 领域服务接口 (位于领域层)
trait UserRepository {
    fn find_by_id(&self, id: u64) -> Option<User>;
    fn save(&self, user: &User) -> Result<(), Error>;
}

// 基础设施层实现
struct PostgresUserRepository {
    connection_pool: Pool<PostgresConnectionManager>,
}

impl UserRepository for PostgresUserRepository {
    // 实现接口...
}

// 领域层服务依赖于抽象接口而非具体实现
struct UserService<R>
where
    R: UserRepository,
{
    repository: R,
}

impl<R: UserRepository> UserService<R> {
    fn new(repository: R) -> Self {
        UserService { repository }
    }
    
    fn get_user(&self, id: u64) -> Option<User> {
        self.repository.find_by_id(id)
    }
}
```

**定理6.2**: 依赖反转原则使高层模块可以依赖低层模块的抽象而非具体实现，从而避免违反层次依赖规则。

## 实践与形式化验证的权衡

### 成本效益分析

形式化验证DI的成本效益分析：

- **高成本**: 对DI容器或复杂依赖配置进行完全形式化验证需要大量精力
- **高收益(特定场景)**: 在可靠性要求极高的系统中，形式化验证提供的强正确性保证可能值得投入
- **权衡**: 大多数常规应用通常依赖单元测试、集成测试和良好设计实践来保证依赖管理的正确性

### 选择性应用

形式化验证可以选择性应用于最关键的系统部分：

- 验证依赖图中不存在循环依赖
- 验证层次依赖规则是否被遵守
- 验证组件生命周期管理的正确性

**定理7.1**: 选择性形式化验证能够在有限成本内提供关键属性的保证，从而平衡投入与收益。

## 思维导图

```text
依赖注入与设计模式关联分析
|
+-- 基本概念与定义
|   |-- 依赖注入的形式化定义
|   |   |-- 三元组 (C, S, I)：组件、服务、注入机制
|   |   |-- 公理：组件不直接创建服务实例
|   |
|   +-- 设计模式的形式化表示
|       |-- 三元组 (P, S, C)：问题、解决方案、上下文
|       |-- 架构模式 (C, R, P)：组件集、关系、属性约束
|
+-- 依赖注入机制实现
|   |-- 特征基础依赖注入
|   |   |-- 编译时类型安全
|   |   |-- 通过特征抽象服务接口
|   |
|   |-- 泛型实现依赖注入
|   |   |-- 灵活组件配置
|   |   |-- 静态分发优化
|   |
|   +-- 服务定位器模式
|       |-- 运行时依赖解析
|       |-- 动态注册和查找服务
|
+-- 形式化验证框架
|   |-- 属性规约与验证
|   |   |-- 安全性属性：不好的事情不会发生
|   |   |-- 活性属性：好的事情最终会发生
|   |
|   |-- 状态机模型
|   |   |-- 组件状态建模
|   |   |-- 依赖解析流程形式化
|   |
|   +-- 时序逻辑表达
|       |-- LTL/CTL表示系统属性
|       |-- 验证依赖图无循环
|
+-- 依赖注入与设计模式关联
|   |-- IoC容器与工厂模式
|   |   |-- 工厂函数管理组件创建
|   |   |-- 控制反转原则实现
|   |
|   |-- 代理模式与装饰器模式
|   |   |-- 横切关注点实现
|   |   |-- 透明包装组件增强功能
|   |
|   +-- 构建器模式与类型状态模式
|       |-- 编译期强制初始化流程
|       |-- 类型系统保证正确配置
|
+-- 元模型与元理论
|   |-- 依赖注入的范畴论解释
|   |   |-- 对象：组件和服务
|   |   |-- 态射：依赖关系
|   |
|   |-- 依赖图与态射
|   |   |-- 有向图表示依赖关系
|   |   |-- 拓扑排序确定初始化顺序
|   |
|   +-- 函子框架
|       |-- 验证函子映射规范到结果
|       |-- 保持结构的转换
|
+-- 多层次架构与依赖注入
|   |-- 层次化依赖注入
|   |   |-- 层次规则定义
|   |   |-- 允许的跨层依赖
|   |
|   |-- 层次边界验证
|   |   |-- 静态分析确保边界完整性
|   |   |-- 编译期或构建期验证
|   |
|   +-- 跨层依赖管理
|       |-- 依赖反转原则
|       |-- 抽象接口位于高层模块
|
+-- 实践与形式化验证权衡
    |-- 成本效益分析
    |   |-- 验证成本与潜在收益
    |   |-- 适用场景评估
    |
    +-- 选择性应用
        |-- 关键属性验证
        |-- 风险驱动的验证策略
```

## 依赖注入的高级实现技术

### 编译时依赖验证

Rust的类型系统能够在编译时验证依赖关系：

```rust
// 使用类型参数标记依赖状态
struct Unresolved;
struct Resolved;

// 依赖容器
struct DIContainer<State = Unresolved> {
    components: HashMap<TypeId, Box<dyn Any>>,
    _state: PhantomData<State>,
}

impl DIContainer<Unresolved> {
    fn new() -> Self {
        DIContainer {
            components: HashMap::new(),
            _state: PhantomData,
        }
    }
    
    fn register<T: 'static>(&mut self, component: T) -> &mut Self {
        self.components.insert(TypeId::of::<T>(), Box::new(component));
        self
    }
    
    fn build(self) -> Result<DIContainer<Resolved>, String> {
        // 验证所有依赖都已满足
        // 检查循环依赖
        // 构建依赖图并验证
        
        Ok(DIContainer {
            components: self.components,
            _state: PhantomData,
        })
    }
}

impl DIContainer<Resolved> {
    fn resolve<T: 'static>(&self) -> Result<&T, String> {
        self.components
            .get(&TypeId::of::<T>())
            .ok_or_else(|| format!("未注册组件: {}", std::any::type_name::<T>()))?
            .downcast_ref::<T>()
            .ok_or_else(|| "内部类型错误".to_string())
    }
}
```

**定理8.1**: 使用类型状态模式的依赖注入容器可以在编译时保证只有经过验证的容器才能解析组件。

### 特征对象与动态分发

当需要运行时多态性时，可以使用特征对象实现依赖注入：

```rust
// 定义服务接口
trait Service: Send + Sync {
    fn execute(&self, input: &str) -> String;
}

// 实现服务
struct ConcreteService;
impl Service for ConcreteService {
    fn execute(&self, input: &str) -> String {
        format!("处理输入: {}", input)
    }
}

// 使用特征对象的组件
struct Client {
    service: Arc<dyn Service>,
}

impl Client {
    fn new(service: Arc<dyn Service>) -> Self {
        Client { service }
    }
    
    fn process(&self, input: &str) -> String {
        self.service.execute(input)
    }
}

// 服务注册中心
struct ServiceRegistry {
    services: HashMap<String, Arc<dyn Service>>,
}

impl ServiceRegistry {
    fn new() -> Self {
        ServiceRegistry {
            services: HashMap::new(),
        }
    }
    
    fn register(&mut self, name: &str, service: Arc<dyn Service>) {
        self.services.insert(name.to_string(), service);
    }
    
    fn get(&self, name: &str) -> Option<Arc<dyn Service>> {
        self.services.get(name).cloned()
    }
}
```

**定理8.2**: 特征对象实现的依赖注入允许在运行时动态替换服务实现，但牺牲了编译时类型安全和静态分发的性能优势。

### 基于生命周期的作用域管理

利用Rust的生命周期系统管理依赖的作用域：

```rust
// 作用域容器
struct ScopeContainer<'a> {
    parent: Option<&'a ScopeContainer<'a>>,
    components: RefCell<HashMap<TypeId, Rc<dyn Any>>>,
}

impl<'a> ScopeContainer<'a> {
    fn root() -> Self {
        ScopeContainer {
            parent: None,
            components: RefCell::new(HashMap::new()),
        }
    }
    
    fn child(&'a self) -> Self {
        ScopeContainer {
            parent: Some(self),
            components: RefCell::new(HashMap::new()),
        }
    }
    
    fn register<T: 'static>(&self, component: T) {
        self.components.borrow_mut().insert(TypeId::of::<T>(), Rc::new(component));
    }
    
    fn resolve<T: 'static>(&self) -> Option<Rc<T>> {
        // 先在当前作用域查找
        if let Some(component) = self.components.borrow().get(&TypeId::of::<T>()) {
            if let Some(typed) = component.clone().downcast_rc::<T>() {
                return Some(typed);
            }
        }
        
        // 在父作用域查找
        if let Some(parent) = self.parent {
            return parent.resolve::<T>();
        }
        
        None
    }
}
```

**定理8.3**: 生命周期参数确保子作用域不会比其父作用域活得更久，从而防止悬垂引用。

## 依赖注入与函数式编程

### Reader Monad模式

Reader Monad是一种函数式依赖注入模式：

```rust
// Reader Monad
struct Reader<E, A, F>
where
    F: Fn(&E) -> A,
{
    run: F,
}

impl<E, A, F> Reader<E, A, F>
where
    F: Fn(&E) -> A,
{
    fn new(f: F) -> Self {
        Reader { run: f }
    }
    
    fn map<B, G>(self, f: G) -> Reader<E, B, impl Fn(&E) -> B>
    where
        G: Fn(A) -> B,
    {
        Reader::new(move |e| f((self.run)(e)))
    }
    
    fn flat_map<B, G>(self, f: G) -> Reader<E, B, impl Fn(&E) -> B>
    where
        G: Fn(A) -> Reader<E, B, impl Fn(&E) -> B>,
    {
        Reader::new(move |e| {
            let a = (self.run)(e);
            let reader_b = f(a);
            (reader_b.run)(e)
        })
    }
}

// 使用Reader Monad实现依赖注入
struct Environment {
    logger: Box<dyn Fn(&str)>,
    database: Box<dyn Fn(&str) -> Vec<String>>,
}

fn get_user_name(id: u64) -> Reader<Environment, String, impl Fn(&Environment) -> String> {
    Reader::new(move |env| {
        (env.logger)(&format!("获取用户: {}", id));
        let results = (env.database)(&format!("SELECT name FROM users WHERE id = {}", id));
        results.get(0).cloned().unwrap_or_else(|| "未知用户".to_string())
    })
}

fn get_user_email(id: u64) -> Reader<Environment, String, impl Fn(&Environment) -> String> {
    Reader::new(move |env| {
        (env.logger)(&format!("获取邮箱: {}", id));
        let results = (env.database)(&format!("SELECT email FROM users WHERE id = {}", id));
        results.get(0).cloned().unwrap_or_else(|| "无邮箱".to_string())
    })
}

fn get_user_info(id: u64) -> Reader<Environment, (String, String), impl Fn(&Environment) -> (String, String)> {
    Reader::new(move |env| {
        let name = (get_user_name(id).run)(env);
        let email = (get_user_email(id).run)(env);
        (name, email)
    })
}
```

**定理9.1**: Reader Monad提供一种纯函数式的依赖注入方法，通过函数组合而非对象组合管理依赖。

### 函数组合与依赖传递

函数组合是另一种函数式依赖注入形式：

```rust
// 服务类型定义为函数类型
type LoggerFn = fn(&str);
type DatabaseFn = fn(&str) -> Vec<String>;

// 高阶函数接收依赖并返回功能函数
fn create_user_service(logger: LoggerFn, database: DatabaseFn) -> impl Fn(u64) -> Option<User> {
    move |id| {
        logger(&format!("查询用户: {}", id));
        let results = database(&format!("SELECT * FROM users WHERE id = {}", id));
        
        if results.is_empty() {
            None
        } else {
            // 解析数据库结果为用户
            Some(User {
                id,
                name: results[0].clone(),
                // 其他字段...
            })
        }
    }
}

// 使用函数组合
fn main() {
    // 具体依赖实现
    let logger: LoggerFn = |msg| println!("[LOG] {}", msg);
    let database: DatabaseFn = |query| {
        println!("执行查询: {}", query);
        vec!["张三".to_string()]
    };
    
    // 创建服务
    let get_user = create_user_service(logger, database);
    
    // 使用服务
    if let Some(user) = get_user(42) {
        println!("找到用户: {}", user.name);
    } else {
        println!("用户不存在");
    }
}
```

**定理9.2**: 函数组合可以实现无状态的依赖注入，简化了系统的理解和测试。

### 纯函数架构

纯函数架构结合依赖注入可以提高系统可测试性：

```rust
// 状态与更新逻辑分离
struct AppState {
    users: HashMap<u64, User>,
    settings: HashMap<String, String>,
}

// 纯函数操作
fn create_user(state: &AppState, id: u64, name: &str) -> Result<AppState, String> {
    // 检查用户是否已存在
    if state.users.contains_key(&id) {
        return Err(format!("用户ID已存在: {}", id));
    }
    
    // 创建新状态（不修改原状态）
    let mut new_state = state.clone();
    new_state.users.insert(id, User { id, name: name.to_string() });
    
    Ok(new_state)
}

// 依赖注入与纯函数结合
struct Services {
    logger: Box<dyn Fn(&str)>,
}

// 接收服务依赖的操作
fn create_user_with_logging(
    services: &Services,
    state: &AppState,
    id: u64,
    name: &str
) -> Result<AppState, String> {
    (services.logger)(&format!("创建用户: {} (ID: {})", name, id));
    create_user(state, id, name)
}
```

**定理9.3**: 纯函数架构通过分离状态和操作，使系统更易于测试和推理。

## 依赖注入的形式化证明

### 类型系统保证

通过类型系统证明依赖注入系统的属性：

```rust
// 使用幽灵类型标记验证状态
struct Validated;
struct Unvalidated;

// 有效的依赖图
struct DependencyGraph<State = Unvalidated> {
    nodes: HashMap<TypeId, Node>,
    _state: PhantomData<State>,
}

struct Node {
    type_name: String,
    dependencies: HashSet<TypeId>,
}

impl DependencyGraph<Unvalidated> {
    fn new() -> Self {
        DependencyGraph {
            nodes: HashMap::new(),
            _state: PhantomData,
        }
    }
    
    fn add_node(&mut self, type_id: TypeId, type_name: String, dependencies: HashSet<TypeId>) {
        self.nodes.insert(type_id, Node { type_name, dependencies });
    }
    
    fn validate(self) -> Result<DependencyGraph<Validated>, String> {
        // 检查所有依赖是否都已注册
        for (type_id, node) in &self.nodes {
            for dep_id in &node.dependencies {
                if !self.nodes.contains_key(dep_id) {
                    return Err(format!(
                        "类型 {} 依赖未注册的类型 {:?}",
                        node.type_name, dep_id
                    ));
                }
            }
        }
        
        // 检查循环依赖
        if let Some(cycle) = self.detect_cycle() {
            let cycle_names: Vec<_> = cycle.iter()
                .map(|id| self.nodes.get(id).unwrap().type_name.clone())
                .collect();
            
            return Err(format!("检测到循环依赖: {}", cycle_names.join(" -> ")));
        }
        
        // 验证通过
        Ok(DependencyGraph {
            nodes: self.nodes,
            _state: PhantomData,
        })
    }
    
    fn detect_cycle(&self) -> Option<Vec<TypeId>> {
        // 深度优先搜索检测循环
        // 实现详情省略...
        None
    }
}

// 只有验证过的依赖图才能用于创建容器
impl DependencyGraph<Validated> {
    fn create_container(&self) -> DIContainer {
        // 基于验证过的依赖图创建容器
        DIContainer::new()
    }
}
```

**定理10.1**: 类型系统可以静态保证依赖图的无循环性，防止运行时出现解析死锁。

### 依赖图的数学性质

依赖图的形式化证明可以利用图论：

```rust
// 用于形式化证明的依赖图表示
struct FormalGraph {
    nodes: HashSet<Node>,
    edges: HashSet<Edge>,
}

#[derive(Hash, Eq, PartialEq)]
struct Node(String);

#[derive(Hash, Eq, PartialEq)]
struct Edge(String, String);

impl FormalGraph {
    // 验证无循环
    fn is_acyclic(&self) -> bool {
        // 计算拓扑排序
        let mut in_degree: HashMap<&Node, usize> = HashMap::new();
        let mut graph: HashMap<&Node, Vec<&Node>> = HashMap::new();
        
        // 初始化入度
        for node in &self.nodes {
            in_degree.insert(node, 0);
            graph.insert(node, Vec::new());
        }
        
        // 构建图和计算入度
        for Edge(from, to) in &self.edges {
            let from_node = self.nodes.iter().find(|n| n.0 == *from).unwrap();
            let to_node = self.nodes.iter().find(|n| n.0 == *to).unwrap();
            
            graph.get_mut(from_node).unwrap().push(to_node);
            *in_degree.get_mut(to_node).unwrap() += 1;
        }
        
        // Kahn算法
        let mut queue: VecDeque<&Node> = in_degree.iter()
            .filter(|(_, &degree)| degree == 0)
            .map(|(&node, _)| node)
            .collect();
        
        let mut visited_count = 0;
        
        while let Some(node) = queue.pop_front() {
            visited_count += 1;
            
            for &neighbor in &graph[node] {
                *in_degree.get_mut(neighbor).unwrap() -= 1;
                if in_degree[neighbor] == 0 {
                    queue.push_back(neighbor);
                }
            }
        }
        
        // 如果访问的节点数等于总节点数，则无循环
        visited_count == self.nodes.len()
    }
}
```

**引理10.1**: 依赖图是无环的当且仅当存在一个有效的拓扑排序。

**定理10.2**: 在无环依赖图中，存在至少一个组件没有依赖，可以作为初始化起点。

### 正确性证明

利用命题逻辑和谓词逻辑证明依赖注入系统的正确性：

```rust
// 表示命题的形式结构
enum Proposition {
    Atom(String),
    And(Box<Proposition>, Box<Proposition>),
    Or(Box<Proposition>, Box<Proposition>),
    Implies(Box<Proposition>, Box<Proposition>),
    Not(Box<Proposition>),
    ForAll(String, Box<Proposition>),
    Exists(String, Box<Proposition>),
}

// 证明依赖图无循环性质
fn prove_acyclicity() -> Proposition {
    // 定义原子命题
    let p1 = Proposition::Atom("图G是有向无环图".to_string());
    let p2 = Proposition::Atom("G的节点可以拓扑排序".to_string());
    let p3 = Proposition::Atom("G中不存在路径形成循环".to_string());
    
    // 构建蕴含关系
    let proof1 = Proposition::Implies(
        Box::new(p1.clone()),
        Box::new(p2.clone())
    );
    
    let proof2 = Proposition::Implies(
        Box::new(p2.clone()),
        Box::new(p3.clone())
    );
    
    let proof3 = Proposition::Implies(
        Box::new(p3.clone()),
        Box::new(p1.clone())
    );
    
    // 组合证明
    Proposition::And(
        Box::new(proof1),
        Box::new(Proposition::And(
            Box::new(proof2),
            Box::new(proof3)
        ))
    )
}
```

**定理10.3**: 依赖注入系统的正确性可以通过以下属性形式化验证：

1. 组件解析终止性：所有组件解析过程最终会完成
2. 组件解析确定性：相同依赖图下，多次解析产生相同结果
3. 组件解析一致性：解析结果满足所有组件的依赖关系

## 依赖注入与其他架构模式的结合

### 事件驱动架构

依赖注入与事件驱动架构结合：

```rust
// 事件总线接口
trait EventBus {
    fn publish<E: Event>(&self, event: E);
    fn subscribe<E: Event>(&self, handler: Box<dyn Fn(&E)>);
}

// 具体事件总线实现
struct SimpleEventBus {
    handlers: Arc<Mutex<HashMap<TypeId, Vec<Box<dyn Any>>>>>,
}

impl SimpleEventBus {
    fn new() -> Self {
        SimpleEventBus {
            handlers: Arc::new(Mutex::new(HashMap::new())),
        }
    }
}

impl EventBus for SimpleEventBus {
    fn publish<E: Event>(&self, event: E) {
        let handlers = self.handlers.lock().unwrap();
        if let Some(event_handlers) = handlers.get(&TypeId::of::<E>()) {
            for handler in event_handlers {
                if let Some(typed_handler) = handler.downcast_ref::<Box<dyn Fn(&E)>>() {
                    typed_handler(&event);
                }
            }
        }
    }
    
    fn subscribe<E: Event>(&self, handler: Box<dyn Fn(&E)>) {
        let mut handlers = self.handlers.lock().unwrap();
        handlers
            .entry(TypeId::of::<E>())
            .or_insert_with(Vec::new)
            .push(Box::new(handler));
    }
}

// 使用依赖注入配置事件驱动系统
struct Application<B: EventBus> {
    event_bus: B,
    services: HashMap<TypeId, Box<dyn Any>>,
}

impl<B: EventBus> Application<B> {
    fn new(event_bus: B) -> Self {
        Application {
            event_bus,
            services: HashMap::new(),
        }
    }
    
    fn register<S: 'static>(&mut self, service: S) {
        self.services.insert(TypeId::of::<S>(), Box::new(service));
    }
    
    fn get<S: 'static>(&self) -> Option<&S> {
        self.services.get(&TypeId::of::<S>())
            .and_then(|s| s.downcast_ref::<S>())
    }
}
```

**定理11.1**: 依赖注入与事件驱动架构结合可以实现组件间松耦合通信，同时保持依赖关系的显式性。

### CQRS模式

结合依赖注入实现CQRS（命令查询责任分离）模式：

```rust
// 命令处理器
trait CommandHandler<C> {
    type Error;
    fn handle(&self, command: C) -> Result<(), Self::Error>;
}

// 查询处理器
trait QueryHandler<Q> {
    type Result;
    type Error;
    fn handle(&self, query: Q) -> Result<Self::Result, Self::Error>;
}

// CQRS总线
struct CqrsBus {
    command_handlers: HashMap<TypeId, Box<dyn Any>>,
    query_handlers: HashMap<TypeId, Box<dyn Any>>,
}

impl CqrsBus {
    fn new() -> Self {
        CqrsBus {
            command_handlers: HashMap::new(),
            query_handlers: HashMap::new(),
        }
    }
    
    fn register_command_handler<C: 'static, H: CommandHandler<C> + 'static>(&mut self, handler: H) {
        self.command_handlers.insert(TypeId::of::<C>(), Box::new(handler));
    }
    
    fn register_query_handler<Q: 'static, H: QueryHandler<Q> + 'static>(&mut self, handler: H) {
        self.query_handlers.insert(TypeId::of::<Q>(), Box::new(handler));
    }
    
    fn dispatch<C: 'static>(&self, command: C) -> Result<(), Box<dyn Error>> {
        let handler = self.command_handlers.get(&TypeId::of::<C>())
            .ok_or_else(|| format!("未找到命令处理器: {}", std::any::type_name::<C>()))?;
        
        let typed_handler = handler.downcast_ref::<Box<dyn CommandHandler<C, Error = Box<dyn Error>>>>()
            .ok_or_else(|| "处理器类型不匹配".to_string())?;
        
        typed_handler.handle(command)?;
        Ok(())
    }
    
    fn query<Q: 'static, R: 'static>(&self, query: Q) -> Result<R, Box<dyn Error>> {
        let handler = self.query_handlers.get(&TypeId::of::<Q>())
            .ok_or_else(|| format!("未找到查询处理器: {}", std::any::type_name::<Q>()))?;
        
        let typed_handler = handler.downcast_ref::<Box<dyn QueryHandler<Q, Result = R, Error = Box<dyn Error>>>>()
            .ok_or_else(|| "处理器类型不匹配".to_string())?;
        
        typed_handler.handle(query)
    }
}
```

**定理11.2**: CQRS与依赖注入结合可以实现命令和查询责任的清晰分离，同时维持系统组件间的显式依赖关系。

### 微服务架构

依赖注入在微服务架构中的应用：

```rust
// 服务发现接口
trait ServiceDiscovery {
    fn get_service_url(&self, service_name: &str) -> Option<String>;
}

// 服务注册表
struct ServiceRegistry {
    services: HashMap<String, String>,
}

impl ServiceDiscovery for ServiceRegistry {
    fn get_service_url(&self, service_name: &str) -> Option<String> {
        self.services.get(service_name).cloned()
    }
}

// 远程服务客户端
struct RemoteServiceClient<SD: ServiceDiscovery> {
    service_discovery: SD,
    http_client: HttpClient,
}

impl<SD: ServiceDiscovery> RemoteServiceClient<SD> {
    fn new(service_discovery: SD, http_client: HttpClient) -> Self {
        RemoteServiceClient {
            service_discovery,
            http_client,
        }
    }
    
    async fn call_service(&self, service_name: &str, path: &str, payload: &str) -> Result<String, Error> {
        let service_url = self.service_discovery.get_service_url(service_name)
            .ok_or_else(|| format!("服务未找到: {}", service_name))?;
        
        let url = format!("{}/{}", service_url, path);
        self.http_client.post(&url, payload).await
    }
}

// 微服务组件
struct MicroserviceComponent<SD: ServiceDiscovery> {
    service_client: RemoteServiceClient<SD>,
    local_repository: Box<dyn Repository>,
}
```

**定理11.3**: 依赖注入在微服务架构中有助于管理服务发现、负载均衡和断路器等横切关注点。

## 依赖注入的实践模式与反模式

### 最佳实践

依赖注入的最佳实践可以形式化为约束和指导原则：

1. **依赖接口而非实现**:

```rust
// 推荐
struct Service<R: Repository> { repository: R }

// 不推荐
struct Service { repository: ConcreteRepository }
```

1. **构造函数注入**:

```rust
// 推荐
impl<L: Logger, R: Repository> Service<L, R> {
    fn new(logger: L, repository: R) -> Self {
        Service { logger, repository }
    }
}
```

1. **使依赖显式可见**:

```rust
// 推荐
fn process<L: Logger>(&self, logger: &L, data: &Data)

// 不推荐
fn process(&self, data: &Data) // 隐藏了Logger依赖
```

1. **遵循单一责任原则**:

```rust
// 推荐：每个组件有单一责任
struct UserRepository {}
struct UserValidator {}
struct UserService<R, V> { repository: R, validator: V }

// 不推荐：组件承担多种责任
struct UserService {
    // 直接包含数据访问和验证逻辑
}
```

**定理12.1**: 遵循依赖注入最佳实践的系统具有更高的可测试性、可维护性和可扩展性。

### 常见反模式

依赖注入的反模式及其形式化分析：

1. **服务定位器反模式**:

```rust
// 反模式
fn process(&self) {
    let service = ServiceLocator::get::<Service>();
    service.do_something();
}
```

1. **构造函数过度注入**:

```rust
// 反模式：过多依赖
struct Service<A, B, C, D, E, F, G, H, I, J> {
    // 10个不同的依赖参数
}
```

1. **隐式依赖**:

```rust
// 反模式
fn process(&self) {
    // 内部直接创建依赖
    let logger = ConsoleLogger::new();
    logger.log("处理数据");
}
```

1. **循环依赖**:

```rust
// 反模式
struct A<B> { b: B }
struct B<A> { a: A } // 互相依赖
```

**定理12.2**: 依赖注入反模式会导致可测试性降低、组件耦合增加和系统复杂性提高。

### 测试策略

依赖注入促进有效的测试策略：

```rust
// 可测试的组件设计
struct UserService<R: UserRepository> {
    repository: R,
}

// 模拟依赖
struct MockUserRepository {
    users: HashMap<u64, User>,
    find_called: RefCell<Vec<u64>>,
}

impl UserRepository for MockUserRepository {
    fn find_by_id(&self, id: u64) -> Option<User> {
        self.find_called.borrow_mut().push(id);
        self.users.get(&id).cloned()
    }
}

// 单元测试
#[test]
fn test_get_user_calls_repository() {
    // 准备
    let mut mock_repo = MockUserRepository {
        users: HashMap::new(),
        find_called: RefCell::new(Vec::new()),
    };
    mock_repo.users.insert(1, User { id: 1, name: "测试用户".to_string() });
    
    let service = UserService::new(mock_repo);
    
    // 执行
    let user = service.get_user(1);
    
    // 验证
    assert!(user.is_some());
    assert_eq!(user.unwrap().name, "测试用户");
    assert_eq!(service.repository.find_called.borrow().len(), 1);
    assert_eq!(service.repository.find_called.borrow()[0], 1);
}
```

**定理12.3**: 通过依赖注入实现的系统可以独立测试每个组件，而无需创建完整的依赖图。

## 思维导图（续）

```text
依赖注入与设计模式高级分析
|
+-- 高级实现技术
|   |-- 编译时依赖验证
|   |   |-- 类型状态模式
|   |   |-- 编译期依赖检查
|   |
|   |-- 特征对象与动态分发
|   |   |-- 运行时多态
|   |   |-- 特征对象封装
|   |
|   +-- 生命周期作用域
|       |-- 基于生命周期的作用域管理
|       |-- 层次化容器实现
|
+-- 函数式依赖注入
|   |-- Reader Monad模式
|   |   |-- 环境参数抽象
|   |   |-- 函数组合
|   |
|   |-- 函数组合模式
|   |   |-- 高阶函数配置
|   |   |-- 依赖传递链
|   |
|   +-- 纯函数架构
|       |-- 状态与操作分离
|       |-- 显式依赖传递
|
+-- 形式化验证与证明
|   |-- 类型系统保证
|   |   |-- 静态类型检查
|   |   |-- 编译期约束验证
|   |
|   |-- 依赖图属性
|   |   |-- 无环图属性
|   |   |-- 拓扑排序理论
|   |
|   +-- 正确性证明
|       |-- 命题逻辑表达
|       |-- 归纳证明方法
|
+-- 架构模式结合
|   |-- 事件驱动架构
|   |   |-- 事件总线注入
|   |   |-- 事件处理器注册
|   |
|   |-- CQRS模式
|   |   |-- 命令处理器注入
|   |   |-- 查询处理器配置
|   |
|   +-- 微服务架构
|       |-- 服务发现注入
|       |-- 断路器模式集成
|
+-- 实践模式与反模式
    |-- 最佳实践
    |   |-- 依赖接口原则
    |   |-- 构造函数注入
    |   |-- 显式依赖原则
    |
    |-- 常见反模式
    |   |-- 服务定位器反模式
    |   |-- 构造函数过度注入
    |   |-- 隐式依赖问题
    |
    +-- 测试策略
        |-- 模拟对象模式
        |-- 测试替身应用
        |-- 集成测试策略
```
