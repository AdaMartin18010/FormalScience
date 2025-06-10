# 设计模式详解

## 目录

- [设计模式详解](#设计模式详解)
  - [目录](#目录)
  - [1. 设计模式 (GoF)](#1-设计模式-gof)
    - [1.1. 概念与定义](#11-概念与定义)
    - [1.2. 分类](#12-分类)
    - [1.3. 创建型模式 (Creational Patterns)](#13-创建型模式-creational-patterns)
      - [1.3.1. 单例模式 (Singleton)](#131-单例模式-singleton)
      - [1.3.2. 工厂方法模式 (Factory Method)](#132-工厂方法模式-factory-method)
      - [1.3.3. 抽象工厂模式 (Abstract Factory)](#133-抽象工厂模式-abstract-factory)
      - [1.3.4. 建造者模式 (Builder)](#134-建造者模式-builder)
      - [1.3.5. 原型模式 (Prototype)](#135-原型模式-prototype)
    - [1.4. 结构型模式 (Structural Patterns)](#14-结构型模式-structural-patterns)
      - [1.4.1. 适配器模式 (Adapter)](#141-适配器模式-adapter)
      - [1.4.2. 桥接模式 (Bridge)](#142-桥接模式-bridge)
      - [1.4.3. 组合模式 (Composite)](#143-组合模式-composite)
      - [1.4.4. 装饰器模式 (Decorator)](#144-装饰器模式-decorator)
      - [1.4.5. 外观模式 (Facade)](#145-外观模式-facade)
      - [1.4.6. 享元模式 (Flyweight)](#146-享元模式-flyweight)
      - [1.4.7. 代理模式 (Proxy)](#147-代理模式-proxy)
    - [1.5. 行为型模式 (Behavioral Patterns)](#15-行为型模式-behavioral-patterns)
      - [1.5.1. 责任链模式 (Chain of Responsibility)](#151-责任链模式-chain-of-responsibility)
      - [1.5.2. 命令模式 (Command)](#152-命令模式-command)
      - [1.5.3. 解释器模式 (Interpreter)](#153-解释器模式-interpreter)
      - [1.5.4. 迭代器模式 (Iterator)](#154-迭代器模式-iterator)
      - [1.5.5. 中介者模式 (Mediator)](#155-中介者模式-mediator)
      - [1.5.6. 备忘录模式 (Memento)](#156-备忘录模式-memento)
      - [1.5.7. 观察者模式 (Observer)](#157-观察者模式-observer)
      - [1.5.8. 状态模式 (State)](#158-状态模式-state)
      - [1.5.9. 策略模式 (Strategy)](#159-策略模式-strategy)
      - [1.5.10. 模板方法模式 (Template Method)](#1510-模板方法模式-template-method)
      - [1.5.11. 访问者模式 (Visitor)](#1511-访问者模式-visitor)
  - [2. 并发并行设计模式](#2-并发并行设计模式)
    - [2.1. 概念与定义](#21-概念与定义)
    - [2.2. 常见模式](#22-常见模式)
      - [2.2.1. 活动对象模式 (Active Object)](#221-活动对象模式-active-object)
      - [2.2.2. 管程模式 (Monitor)](#222-管程模式-monitor)
      - [2.2.3. 线程池模式 (Thread Pool)](#223-线程池模式-thread-pool)
      - [2.2.4. 生产者-消费者模式 (Producer-Consumer)](#224-生产者-消费者模式-producer-consumer)
      - [2.2.5. 读写锁模式 (Readers-Writer Lock)](#225-读写锁模式-readers-writer-lock)
      - [2.2.6. Future/Promise 模式](#226-futurepromise-模式)
      - [2.2.7. Actor 模型](#227-actor-模型)
  - [3. 分布式设计模式](#3-分布式设计模式)
    - [3.1. 概念与定义](#31-概念与定义)
    - [3.2. 常见模式](#32-常见模式)
      - [3.2.1. 服务发现 (Service Discovery)](#321-服务发现-service-discovery)
      - [3.2.2. 熔断器模式 (Circuit Breaker)](#322-熔断器模式-circuit-breaker)
      - [3.2.3. API 网关 (API Gateway)](#323-api-网关-api-gateway)
      - [3.2.4. Saga 模式](#324-saga-模式)
      - [3.2.5. 领导者选举 (Leader Election)](#325-领导者选举-leader-election)
      - [3.2.6. 分片/分区 (Sharding/Partitioning)](#326-分片分区-shardingpartitioning)
      - [3.2.7. 复制 (Replication)](#327-复制-replication)
      - [3.2.8. 消息队列 (Message Queue)](#328-消息队列-message-queue)
  - [4. 工作流设计模式](#4-工作流设计模式)
    - [4.1. 概念与定义](#41-概念与定义)
    - [4.2. 常见模式](#42-常见模式)
      - [4.2.1. 状态机模式 (State Machine)](#421-状态机模式-state-machine)
      - [4.2.2. 工作流引擎 (Workflow Engine)](#422-工作流引擎-workflow-engine)
      - [4.2.3. 任务队列 (Task Queue)](#423-任务队列-task-queue)
      - [4.2.4. 编排 (Orchestration) vs. 协同 (Choreography)](#424-编排-orchestration-vs-协同-choreography)
  - [5. 思维导图 (Text)](#5-思维导图-text)

---

## 1. 设计模式 (GoF)

### 1.1. 概念与定义

设计模式 (Design Pattern) 是一套被反复使用、多数人知晓的、经过分类编目的、代码设计经验的总结。
使用设计模式是为了可重用代码、让代码更容易被他人理解、保证代码可靠性、程序的重用性。
它们描述了在特定软件设计问题中重复出现的通用解决方案。

### 1.2. 分类

设计模式通常根据其目的或意图分为三大类：

1. **创建型模式 (Creational Patterns)**: 处理对象创建机制，试图在适合特定情况的场景下创建对象。
2. **结构型模式 (Structural Patterns)**: 处理类和对象的组合。继承的概念被用来组合接口和定义组合对象的方式以获得新的功能。
3. **行为型模式 (Behavioral Patterns)**: 处理类或对象之间的通信。

### 1.3. 创建型模式 (Creational Patterns)

#### 1.3.1. 单例模式 (Singleton)

- **定义**: 保证一个类仅有一个实例，并提供一个访问它的全局访问点。
- **解释**: 用于需要严格控制只有一个实例存在的场景，例如全局配置、日志记录器等。
- **Rust 示例**:
  - 使用 `std::sync::Once` 和 `lazy_static` 或 `once_cell` crate。

    ```rust
    use std::sync::{Mutex, Once, ONCE_INIT};
    use std::mem;

    #[derive(Debug)]
    struct SingletonLogger {
        // 示例：可以添加一些配置或状态
        level: String,
    }

    static mut SINGLETON_INSTANCE: *const Mutex<SingletonLogger> = 0 as *const _;
    static ONCE: Once = ONCE_INIT;

    impl SingletonLogger {
        fn get_instance() -> &'static Mutex<SingletonLogger> {
            ONCE.call_once(|| {
                let singleton = Mutex::new(SingletonLogger {
                    level: "INFO".to_string(),
                });
                unsafe {
                    // 使用 Box::into_raw 将所有权转移给一个裸指针
                    // 然后存储这个指针。确保这个 Box 不会被 drop。
                    SINGLETON_INSTANCE = Box::into_raw(Box::new(singleton));
                }
            });

            // 每次调用时，从裸指针安全地获取引用
            unsafe {
                & *SINGLETON_INSTANCE
            }
        }

        fn log(&self, message: &str) {
            println!("[{}] {}", self.level, message);
        }

        fn set_level(&mut self, level: String) {
             self.level = level;
        }
    }

    // 更好的方式是使用 once_cell 或 lazy_static
    use once_cell::sync::Lazy;

    static GLOBAL_CONFIG: Lazy<Mutex<Config>> = Lazy::new(|| {
        Mutex::new(Config::load_default())
    });

    #[derive(Debug)]
    struct Config {
        setting: String,
    }

    impl Config {
        fn load_default() -> Self {
            Config { setting: "default".to_string() }
        }
    }

    fn main() {
        // 使用 std::sync::Once 的版本 (注意线程安全和生命周期管理比较复杂)
        let logger1 = SingletonLogger::get_instance();
        let logger2 = SingletonLogger::get_instance();

        {
            let mut l = logger1.lock().unwrap();
            l.log("First message");
            l.set_level("DEBUG".to_string());
        }
         {
            let l = logger2.lock().unwrap();
            l.log("Second message");
        }
        // 确认是同一个实例
        println!("Logger1 addr: {:p}", logger1);
        println!("Logger2 addr: {:p}", logger2);


        // 使用 once_cell 的版本 (更推荐)
        let config1 = GLOBAL_CONFIG.lock().unwrap();
        println!("Config 1: {:?}", *config1);
        // config1 在这里 drop，锁被释放

        let mut config2 = GLOBAL_CONFIG.lock().unwrap();
        config2.setting = "updated".to_string();
        println!("Config 2 updated");

        let config3 = GLOBAL_CONFIG.lock().unwrap();
        println!("Config 3: {:?}", *config3); // 会显示 updated
    }
    ```

#### 1.3.2. 工厂方法模式 (Factory Method)

- **定义**: 定义一个用于创建对象的接口，让子类决定实例化哪一个类。工厂方法使一个类的实例化延迟到其子类。
- **解释**: 当一个类不知道它所必须创建的对象的类，或者想让其子类来指定所创建的对象时使用。
- **Rust 示例**:

    ```rust
    // 定义产品 trait
    trait Product {
        fn operation(&self) -> String;
    }

    // 具体产品 A
    struct ConcreteProductA;
    impl Product for ConcreteProductA {
        fn operation(&self) -> String {
            "Result of ConcreteProductA".to_string()
        }
    }

    // 具体产品 B
    struct ConcreteProductB;
    impl Product for ConcreteProductB {
        fn operation(&self) -> String {
            "Result of ConcreteProductB".to_string()
        }
    }

    // 定义创建者 trait (工厂方法)
    trait Creator {
        // 工厂方法，返回一个 Product trait 对象
        fn factory_method(&self) -> Box<dyn Product>;

        // 也可以有一些默认实现，使用工厂方法
        fn some_operation(&self) -> String {
            let product = self.factory_method();
            format!("Creator: The same creator's code has just worked with {}", product.operation())
        }
    }

    // 具体创建者 A
    struct ConcreteCreatorA;
    impl Creator for ConcreteCreatorA {
        fn factory_method(&self) -> Box<dyn Product> {
            Box::new(ConcreteProductA)
        }
    }

    // 具体创建者 B
    struct ConcreteCreatorB;
    impl Creator for ConcreteCreatorB {
        fn factory_method(&self) -> Box<dyn Product> {
            Box::new(ConcreteProductB)
        }
    }

    fn client_code(creator: &dyn Creator) {
        println!("{}", creator.some_operation());
    }

    fn main() {
        println!("App: Launched with the ConcreteCreatorA.");
        let creator_a = ConcreteCreatorA;
        client_code(&creator_a);

        println!("\nApp: Launched with the ConcreteCreatorB.");
        let creator_b = ConcreteCreatorB;
        client_code(&creator_b);
    }
    ```

#### 1.3.3. 抽象工厂模式 (Abstract Factory)

- **定义**: 提供一个创建一系列相关或相互依赖对象的接口，而无需指定它们具体的类。
- **解释**: 用于创建产品族，当系统需要独立于其产品的创建、组合和表示时使用。
- **Rust 示例**:

    ```rust
    // 产品 A trait
    trait AbstractProductA {
        fn useful_function_a(&self) -> String;
    }

    // 具体产品 A1
    struct ConcreteProductA1;
    impl AbstractProductA for ConcreteProductA1 {
        fn useful_function_a(&self) -> String {
            "The result of the product A1.".to_string()
        }
    }
    // 具体产品 A2
    struct ConcreteProductA2;
    impl AbstractProductA for ConcreteProductA2 {
        fn useful_function_a(&self) -> String {
            "The result of the product A2.".to_string()
        }
    }

    // 产品 B trait
    trait AbstractProductB {
        fn useful_function_b(&self) -> String;
        fn another_useful_function_b(&self, collaborator: &dyn AbstractProductA) -> String;
    }
    // 具体产品 B1
    struct ConcreteProductB1;
    impl AbstractProductB for ConcreteProductB1 {
         fn useful_function_b(&self) -> String {
             "The result of the product B1.".to_string()
         }
         fn another_useful_function_b(&self, collaborator: &dyn AbstractProductA) -> String {
             let result = collaborator.useful_function_a();
             format!("The result of the B1 collaborating with the ({})", result)
         }
    }
    // 具体产品 B2
    struct ConcreteProductB2;
    impl AbstractProductB for ConcreteProductB2 {
         fn useful_function_b(&self) -> String {
             "The result of the product B2.".to_string()
         }
         fn another_useful_function_b(&self, collaborator: &dyn AbstractProductA) -> String {
             let result = collaborator.useful_function_a();
             format!("The result of the B2 collaborating with the ({})", result)
         }
    }

    // 抽象工厂 trait
    trait AbstractFactory {
        fn create_product_a(&self) -> Box<dyn AbstractProductA>;
        fn create_product_b(&self) -> Box<dyn AbstractProductB>;
    }

    // 具体工厂 1
    struct ConcreteFactory1;
    impl AbstractFactory for ConcreteFactory1 {
        fn create_product_a(&self) -> Box<dyn AbstractProductA> {
            Box::new(ConcreteProductA1)
        }
        fn create_product_b(&self) -> Box<dyn AbstractProductB> {
            Box::new(ConcreteProductB1)
        }
    }
    // 具体工厂 2
    struct ConcreteFactory2;
    impl AbstractFactory for ConcreteFactory2 {
         fn create_product_a(&self) -> Box<dyn AbstractProductA> {
             Box::new(ConcreteProductA2)
         }
         fn create_product_b(&self) -> Box<dyn AbstractProductB> {
             Box::new(ConcreteProductB2)
         }
    }

    fn client_code(factory: &dyn AbstractFactory) {
        let product_a = factory.create_product_a();
        let product_b = factory.create_product_b();

        println!("{}", product_b.useful_function_b());
        println!("{}", product_b.another_useful_function_b(product_a.as_ref()));
    }

    fn main() {
        println!("Client: Testing client code with the first factory type...");
        let factory1 = ConcreteFactory1;
        client_code(&factory1);

        println!("\nClient: Testing the same client code with the second factory type...");
        let factory2 = ConcreteFactory2;
        client_code(&factory2);
    }
    ```

#### 1.3.4. 建造者模式 (Builder)

- **定义**: 将一个复杂对象的构建与其表示分离，使得同样的构建过程可以创建不同的表示。
- **解释**: 用于创建具有多个组成部分的复杂对象，允许用户分步构建对象，并可以复用构建过程。Rust 中非常常用，特别是通过方法链 (method chaining) 来实现。
- **Rust 示例**:

    ```rust
    #[derive(Debug, Default)]
    struct Product {
        part_a: Option<String>,
        part_b: Option<String>,
        part_c: Option<i32>,
    }

    impl Product {
        // 提供一个构建器入口
        fn builder() -> ProductBuilder {
            ProductBuilder::default()
        }
    }

    #[derive(Default)]
    struct ProductBuilder {
        part_a: Option<String>,
        part_b: Option<String>,
        part_c: Option<i32>,
    }

    impl ProductBuilder {
        // 每个设置方法都返回 self，以支持链式调用
        fn part_a(mut self, value: String) -> Self {
            self.part_a = Some(value);
            self
        }

        fn part_b(mut self, value: String) -> Self {
            self.part_b = Some(value);
            self
        }

        fn part_c(mut self, value: i32) -> Self {
            self.part_c = Some(value);
            self
        }

        // build 方法消耗 builder 并返回最终的产品
        fn build(self) -> Product {
            Product {
                part_a: self.part_a,
                part_b: self.part_b,
                part_c: self.part_c,
                // 可以加入默认值或校验逻辑
            }
        }
    }

    fn main() {
        let product1 = Product::builder()
            .part_a("Part A value".to_string())
            .part_c(10)
            .build();

        let product2 = Product::builder()
            .part_b("Part B value".to_string())
            .build();

        println!("Product 1: {:?}", product1);
        println!("Product 2: {:?}", product2);
    }
    ```

#### 1.3.5. 原型模式 (Prototype)

- **定义**: 用原型实例指定创建对象的种类，并且通过拷贝这些原型创建新的对象。
- **解释**: 当创建对象的成本（例如，初始化时间）很大时，或者需要一个与现有对象相似的新对象时使用。在 Rust 中，通常通过实现 `Clone` trait 来实现。
- **Rust 示例**:

    ```rust
    #[derive(Debug, Clone)] // 必须实现 Clone trait
    struct Shape {
        x: i32,
        y: i32,
        color: String,
    }

    impl Shape {
        fn new(x: i32, y: i32, color: String) -> Self {
            Shape { x, y, color }
        }
    }

    fn main() {
        let original_shape = Shape::new(10, 20, "Red".to_string());
        println!("Original: {:?}", original_shape);

        // 使用 clone() 方法创建新对象
        let cloned_shape = original_shape.clone();
        // 如果需要修改克隆后的对象
        // let mut cloned_shape = original_shape.clone();
        // cloned_shape.color = "Blue".to_string();

        println!("Cloned:   {:?}", cloned_shape);

        // 确认它们是不同的实例 (地址不同)
        println!("Original addr: {:p}", &original_shape);
        println!("Cloned addr:   {:p}", &cloned_shape);
    }
    ```

### 1.4. 结构型模式 (Structural Patterns)

#### 1.4.1. 适配器模式 (Adapter)

- **定义**: 将一个类的接口转换成客户希望的另外一个接口。适配器模式使得原本由于接口不兼容而不能一起工作的那些类可以一起工作。
- **解释**: 用于复用现有类，但其接口与所需接口不匹配的情况。
- **Rust 示例**:

    ```rust
    // 目标接口 (Target)
    trait Target {
        fn request(&self) -> String;
    }

    // 需要被适配的类 (Adaptee)
    struct Adaptee {
        special_data: String,
    }
    impl Adaptee {
        fn specific_request(&self) -> String {
            format!("Adaptee's specific request: {}", self.special_data.chars().rev().collect::<String>())
        }
    }

    // 适配器 (Adapter)
    struct Adapter {
        adaptee: Adaptee,
    }
    impl Adapter {
        fn new(adaptee: Adaptee) -> Self {
            Adapter { adaptee }
        }
    }
    // 实现目标接口
    impl Target for Adapter {
        fn request(&self) -> String {
            // 调用 Adaptee 的方法并进行转换
            self.adaptee.specific_request()
        }
    }

    fn client_code(target: &dyn Target) {
        println!("{}", target.request());
    }

    fn main() {
        let adaptee = Adaptee { special_data: "Data to adapt".to_string() };
        println!("Adaptee interface is incompatible with the client.");
        println!("But with adapter client can call it's method.");

        let adapter = Adapter::new(adaptee);
        client_code(&adapter);
    }
    ```

#### 1.4.2. 桥接模式 (Bridge)

- **定义**: 将抽象部分与它的实现部分分离，使它们都可以独立地变化。
- **解释**: 当一个类存在两个（或多个）独立变化的维度时使用。例如，形状（抽象）和颜色（实现）。
- **Rust 示例**:

    ```rust
    // 实现部分的接口 (Implementor)
    trait DrawingAPI {
        fn draw_circle(&self, x: f64, y: f64, radius: f64);
    }

    // 具体实现 A
    struct DrawingAPI1;
    impl DrawingAPI for DrawingAPI1 {
        fn draw_circle(&self, x: f64, y: f64, radius: f64) {
            println!("API1.circle at {:.1},{:.1} radius {:.1}", x, y, radius);
        }
    }

    // 具体实现 B
    struct DrawingAPI2;
    impl DrawingAPI for DrawingAPI2 {
        fn draw_circle(&self, x: f64, y: f64, radius: f64) {
            println!("API2.circle at {:.1},{:.1} radius {:.1}", x, y, radius);
        }
    }

    // 抽象部分的接口 (Abstraction)
    // 使用 trait object 持有实现部分
    trait Shape {
        fn draw(&self);
        fn resize(&mut self, percent: f64);
    }

    // 具体的抽象 (Refined Abstraction) - 圆形
    struct CircleShape {
        x: f64,
        y: f64,
        radius: f64,
        drawing_api: Box<dyn DrawingAPI>, // 持有实现部分的 trait object
    }

    impl CircleShape {
        fn new(x: f64, y: f64, radius: f64, drawing_api: Box<dyn DrawingAPI>) -> Self {
            CircleShape { x, y, radius, drawing_api }
        }
    }

    impl Shape for CircleShape {
        fn draw(&self) {
            self.drawing_api.draw_circle(self.x, self.y, self.radius);
        }
        fn resize(&mut self, percent: f64) {
            self.radius *= percent;
        }
    }

    fn main() {
        let api1 = Box::new(DrawingAPI1);
        let api2 = Box::new(DrawingAPI2);

        let mut circle1 = CircleShape::new(1.0, 2.0, 3.0, api1);
        let mut circle2 = CircleShape::new(5.0, 7.0, 11.0, api2);

        circle1.draw();
        circle2.draw();

        circle1.resize(1.5);
        circle1.draw();
    }
    ```

#### 1.4.3. 组合模式 (Composite)

- **定义**: 将对象组合成树形结构以表示“部分-整体”的层次结构。组合模式使得用户对单个对象和组合对象的使用具有一致性。
- **解释**: 用于表示树状结构，例如文件系统、UI 组件树等，允许以统一的方式处理叶子节点和容器节点。
- **Rust 示例**:

    ```rust
    // 组件 trait (Component)
    trait Graphic {
        fn draw(&self);
        // Box<dyn Self> is not allowed, so we use a helper or enum for composite
        // Alternatively, methods specific to composites can be added with default impls
        fn add(&mut self, _graphic: Box<dyn Graphic>) -> Result<(), &'static str> {
            Err("Cannot add to a leaf node")
        }
         fn remove(&mut self, _index: usize) -> Result<Box<dyn Graphic>, &'static str> {
             Err("Cannot remove from a leaf node")
         }
    }

    // 叶子节点 (Leaf) - 例如一个点
    struct Dot {
        x: i32,
        y: i32,
    }
    impl Graphic for Dot {
        fn draw(&self) {
            println!("Drawing a dot at ({}, {})", self.x, self.y);
        }
    }

    // 容器节点 (Composite) - 可以包含其他 Graphic
    struct CompositeGraphic {
        children: Vec<Box<dyn Graphic>>,
    }
    impl CompositeGraphic {
         fn new() -> Self {
             CompositeGraphic { children: Vec::new() }
         }
    }
    impl Graphic for CompositeGraphic {
        fn draw(&self) {
            println!("Drawing composite graphic:");
            for child in &self.children {
                // 缩进或标记，表示层级
                print!("  ");
                child.draw();
            }
        }
        fn add(&mut self, graphic: Box<dyn Graphic>) -> Result<(), &'static str> {
            self.children.push(graphic);
            Ok(())
        }
         fn remove(&mut self, index: usize) -> Result<Box<dyn Graphic>, &'static str> {
             if index < self.children.len() {
                Ok(self.children.remove(index))
             } else {
                 Err("Index out of bounds")
             }
         }
    }

    fn main() {
        let dot1 = Box::new(Dot { x: 1, y: 1 });
        let dot2 = Box::new(Dot { x: 5, y: 3 });

        let mut composite1 = CompositeGraphic::new();
        let _ = composite1.add(dot1); // Use _ to ignore Result Ok(())

        let mut root = CompositeGraphic::new();
        let _ = root.add(Box::new(composite1)); // Add the first composite
        let _ = root.add(dot2);

        // 可以添加更深的层级
        let mut composite2 = CompositeGraphic::new();
        let _ = composite2.add(Box::new(Dot { x: 10, y: 10 }));
        let _ = root.add(Box::new(composite2));


        root.draw();

        // 尝试在叶子节点上调用 add (会失败)
        let mut leaf_dot = Dot { x: 0, y: 0};
        let result = leaf_dot.add(Box::new(Dot {x: 9, y: 9}));
        println!("Trying to add to leaf: {:?}", result); // Err("Cannot add to a leaf node")

    }
    ```

#### 1.4.4. 装饰器模式 (Decorator)

- **定义**: 动态地给一个对象添加一些额外的职责。就增加功能来说，装饰器模式相比生成子类更为灵活。
- **解释**: 允许在运行时通过包装对象来扩展其功能，而无需修改原始类。
- **Rust 示例**:

    ```rust
    // 组件接口 (Component)
    trait Coffee {
        fn cost(&self) -> u32;
        fn description(&self) -> String;
    }

    // 具体组件 (Concrete Component) - 基础咖啡
    struct SimpleCoffee;
    impl Coffee for SimpleCoffee {
        fn cost(&self) -> u32 { 10 }
        fn description(&self) -> String { "Simple Coffee".to_string() }
    }

    // 装饰器基类/结构 (Decorator) - 持有被装饰的对象
    // Rust 中通常直接实现装饰器，不需要显式基类
    struct MilkDecorator {
        coffee: Box<dyn Coffee>, // 持有被包装的 Coffee
    }
    impl MilkDecorator {
        fn new(coffee: Box<dyn Coffee>) -> Self {
            MilkDecorator { coffee }
        }
    }
    // 实现组件接口，并添加额外功能
    impl Coffee for MilkDecorator {
        fn cost(&self) -> u32 {
            self.coffee.cost() + 2 // 加牛奶的价格
        }
        fn description(&self) -> String {
            format!("{}, Milk", self.coffee.description())
        }
    }

    // 另一个具体装饰器
    struct SugarDecorator {
        coffee: Box<dyn Coffee>,
    }
    impl SugarDecorator {
         fn new(coffee: Box<dyn Coffee>) -> Self {
             SugarDecorator { coffee }
         }
    }
    impl Coffee for SugarDecorator {
        fn cost(&self) -> u32 {
            self.coffee.cost() + 1 // 加糖的价格
        }
        fn description(&self) -> String {
            format!("{}, Sugar", self.coffee.description())
        }
    }

    fn main() {
        // 来一杯基础咖啡
        let simple_coffee: Box<dyn Coffee> = Box::new(SimpleCoffee);
        println!("Coffee: {}, Cost: {}", simple_coffee.description(), simple_coffee.cost());

        // 加点牛奶
        let milk_coffee = Box::new(MilkDecorator::new(simple_coffee));
        println!("Coffee: {}, Cost: {}", milk_coffee.description(), milk_coffee.cost());

        // 再加点糖
        let milk_sugar_coffee = Box::new(SugarDecorator::new(milk_coffee));
        println!("Coffee: {}, Cost: {}", milk_sugar_coffee.description(), milk_sugar_coffee.cost());

        // 只加糖
        let sugar_coffee = Box::new(SugarDecorator::new(Box::new(SimpleCoffee)));
         println!("Coffee: {}, Cost: {}", sugar_coffee.description(), sugar_coffee.cost());
    }
    ```

#### 1.4.5. 外观模式 (Facade)

- **定义**: 为子系统中的一组接口提供一个一致的界面。外观模式定义了一个高层接口，这个接口使得这一子系统更加容易使用。
- **解释**: 简化复杂子系统的访问，提供一个简单的入口点。
- **Rust 示例**:

    ```rust
    // 子系统组件 A
    struct SubsystemA;
    impl SubsystemA {
        fn operation_a1(&self) -> String { "SubsystemA: Ready!\n".to_string() }
        fn operation_a2(&self) -> String { "SubsystemA: Go!\n".to_string() }
    }

    // 子系统组件 B
    struct SubsystemB;
    impl SubsystemB {
        fn operation_b1(&self) -> String { "SubsystemB: Fire!\n".to_string() }
    }

     // 子系统组件 C
     struct SubsystemC;
     impl SubsystemC {
         fn operation_c1(&self) -> String { "SubsystemC: Preparing!\n".to_string() }
     }


    // 外观 (Facade)
    struct ComputerFacade {
        subsystem_a: SubsystemA,
        subsystem_b: SubsystemB,
        subsystem_c: SubsystemC,
    }

    impl ComputerFacade {
        // 提供一个简单的构造函数或默认实现
        fn new() -> Self {
            ComputerFacade {
                subsystem_a: SubsystemA,
                subsystem_b: SubsystemB,
                subsystem_c: SubsystemC,
            }
        }

        // 提供一个简单的操作，内部协调子系统
        fn start_computer(&self) -> String {
            let mut result = "Facade initializes subsystems:\n".to_string();
            result.push_str(&self.subsystem_c.operation_c1()); // C 先准备
            result.push_str(&self.subsystem_a.operation_a1()); // A 准备
            result.push_str("Facade orders subsystems to perform the action:\n".into());
            result.push_str(&self.subsystem_a.operation_a2()); // A 执行
            result.push_str(&self.subsystem_b.operation_b1()); // B 执行
            result
        }
    }

    // 客户端代码
    fn client_code(facade: &ComputerFacade) {
        // 客户端只需要与 Facade 交互
        print!("{}", facade.start_computer());
    }

    fn main() {
        let computer = ComputerFacade::new();
        client_code(&computer);
        // 客户端无需了解 SubsystemA, SubsystemB, SubsystemC 的复杂性
    }
    ```

#### 1.4.6. 享元模式 (Flyweight)

- **定义**: 运用共享技术有效地支持大量细粒度的对象。
- **解释**: 通过共享相似对象的部分状态（内部状态）来减少内存使用。不变的部分（内部状态）被共享，可变的部分（外部状态）由客户端传入。在 Rust 中，`Rc<T>` 或 `Arc<T>` 可以用来共享不可变数据。
- **Rust 示例**:

    ```rust
    use std::collections::HashMap;
    use std::rc::Rc; // 使用 Rc 进行共享，如果是多线程环境用 Arc

    // 享元对象 (Flyweight) - 包含内部状态 (共享)
    #[derive(Debug, PartialEq, Eq, Hash)] // 需要 Hash 和 Eq 来作为 HashMap 的 key
    struct CharacterStyle {
        font: String,
        size: u32,
        // 内部状态，通常是不可变的
    }

    impl CharacterStyle {
        fn new(font: String, size: u32) -> Self {
            CharacterStyle { font, size }
        }
    }

    // 享元工厂 (Flyweight Factory)
    struct StyleFactory {
        styles: HashMap<CharacterStyle, Rc<CharacterStyle>>,
    }

    impl StyleFactory {
        fn new() -> Self {
            StyleFactory { styles: HashMap::new() }
        }

        // 获取享元对象，如果不存在则创建并缓存
        fn get_style(&mut self, font: String, size: u32) -> Rc<CharacterStyle> {
             let key = CharacterStyle::new(font.clone(), size); // 创建 key 用于查找
             // 使用 entry API 更简洁高效
             self.styles.entry(key)
                 .or_insert_with(|| {
                      println!("Creating new style: {} {}", font, size);
                      Rc::new(CharacterStyle::new(font, size))
                  })
                 .clone() // 克隆 Rc 指针，增加引用计数
        }

        fn count_styles(&self) -> usize {
            self.styles.len()
        }
    }

    // 上下文对象 (Context) - 包含外部状态
    struct Character {
        char_code: char,
        style: Rc<CharacterStyle>, // 持有享元的引用
    }

    impl Character {
        fn draw(&self) {
            println!("Character '{}' with style {:?}", self.char_code, self.style);
        }
    }


    fn main() {
        let mut factory = StyleFactory::new();

        let mut characters = Vec::new();

        // 创建字符，外部状态 (char_code) 不同，内部状态 (style) 可能共享
        characters.push(Character {
            char_code: 'H',
            style: factory.get_style("Arial".to_string(), 12),
        });
        characters.push(Character {
             char_code: 'e',
             style: factory.get_style("Arial".to_string(), 12), // 复用
        });
         characters.push(Character {
             char_code: 'l',
             style: factory.get_style("Arial".to_string(), 12), // 复用
        });
         characters.push(Character {
             char_code: 'l',
             style: factory.get_style("Arial".to_string(), 12), // 复用
        });
         characters.push(Character {
             char_code: 'o',
             style: factory.get_style("Arial".to_string(), 12), // 复用
        });
         characters.push(Character {
             char_code: 'W',
             style: factory.get_style("Times New Roman".to_string(), 14), // 新样式
        });
          characters.push(Character {
             char_code: 'o',
             style: factory.get_style("Times New Roman".to_string(), 14), // 复用
        });

        println!("\nDrawing characters:");
        for character in characters {
            character.draw();
        }

        println!("\nTotal styles created: {}", factory.count_styles()); // 只创建了 2 种样式

        // 验证共享 (比较 Rc 指针地址)
        let style1 = factory.get_style("Arial".to_string(), 12);
        let style2 = factory.get_style("Arial".to_string(), 12);
        let style3 = factory.get_style("Times New Roman".to_string(), 14);

        println!("Style1 addr: {:p}", Rc::as_ptr(&style1));
        println!("Style2 addr: {:p}", Rc::as_ptr(&style2)); // 应与 style1 相同
        println!("Style3 addr: {:p}", Rc::as_ptr(&style3)); // 应不同
    }

    ```

#### 1.4.7. 代理模式 (Proxy)

- **定义**: 为其他对象提供一种代理以控制对这个对象的访问。
- **解释**: 用于延迟加载（虚拟代理）、访问控制（保护代理）、日志记录、缓存等场景。代理持有对真实对象的引用，并实现了与真实对象相同的接口。
- **Rust 示例**:

    ```rust
    // 服务接口 (Subject)
    trait Service {
        fn request(&self) -> String;
    }

    // 真实服务 (Real Subject)
    struct RealService;
    impl Service for RealService {
        fn request(&self) -> String {
            "RealService: Handling request.".to_string()
        }
    }

    // 代理 (Proxy)
    struct Proxy {
        real_service: RealService, // 可以是 Option<RealService> 用于懒加载
        // 或者可以是 Box<dyn Service>
    }

    impl Proxy {
        fn new(real_service: RealService) -> Self {
            Proxy { real_service }
        }

        // 访问控制逻辑
        fn check_access(&self) -> bool {
            println!("Proxy: Checking access prior to firing a real request.");
            // 假设这里有一些复杂的检查逻辑
            true // 假设允许访问
        }

        // 日志记录逻辑
        fn log_access(&self) {
            println!("Proxy: Logging the time of request.");
        }
    }

    // 实现服务接口
    impl Service for Proxy {
        fn request(&self) -> String {
            if self.check_access() {
                let result = self.real_service.request(); // 转发请求
                self.log_access();
                result
            } else {
                "Proxy: Access denied.".to_string()
            }
        }
    }

    // 客户端代码
    fn client_code(service: &dyn Service) {
        println!("{}", service.request());
    }

    fn main() {
        println!("Client: Executing the client code with a real subject:");
        let real_service = RealService;
        client_code(&real_service);

        println!("\nClient: Executing the same client code with a proxy:");
        let proxy = Proxy::new(real_service); // Proxy 持有 real_service 的所有权
        client_code(&proxy);
    }
    ```

### 1.5. 行为型模式 (Behavioral Patterns)

#### 1.5.1. 责任链模式 (Chain of Responsibility)

- **定义**: 避免请求发送者与接收者耦合在一起，让多个对象都有可能接收请求。将这些对象连接成一条链，并且沿着这条链传递请求，直到有对象处理它为止。
- **解释**: 用于解耦请求的发送和处理，请求在链上传递，每个处理器决定是处理请求还是将其传递给下一个处理器。
- **Rust 示例**:

    ```rust
    // 定义处理者 trait
    trait Handler {
        // 设置下一个处理者，返回 Option<Box<dyn Handler>> 以便可以转移所有权
        fn set_next(self: Box<Self>, next: Box<dyn Handler>) -> Box<dyn Handler>;
        // 处理请求
        fn handle(&self, request: &str) -> Option<String>;
        // 获取下一个处理者（不可变引用）
        fn next(&self) -> Option<&dyn Handler>;
    }

    // 抽象处理者基类（可选，Rust 中更常用 trait）
    // 这里我们直接在具体处理者中包含 next 字段
    struct BaseHandler {
         next_handler: Option<Box<dyn Handler>>,
    }

    impl BaseHandler {
        fn new() -> Self { BaseHandler { next_handler: None } }

         // 辅助方法处理传递
        fn handle_next(&self, request: &str) -> Option<String> {
            if let Some(next) = &self.next_handler {
                 next.handle(request)
            } else {
                 None // 到达链尾
            }
        }
    }


    // 具体处理者 A
    struct ConcreteHandlerA {
        base: BaseHandler,
    }
    impl ConcreteHandlerA {
         fn new() -> Box<dyn Handler> { Box::new(Self { base: BaseHandler::new() }) }
    }
    impl Handler for ConcreteHandlerA {
        fn set_next(mut self: Box<Self>, next: Box<dyn Handler>) -> Box<dyn Handler> {
            self.base.next_handler = Some(next);
            self // 返回自身的所有权
        }
         fn handle(&self, request: &str) -> Option<String> {
             if request == "RequestA" {
                 Some("ConcreteHandlerA handled the request".to_string())
             } else {
                 // 传递给下一个
                 self.base.handle_next(request)
             }
         }
         fn next(&self) -> Option<&dyn Handler> {
            self.base.next_handler.as_deref()
         }
    }

    // 具体处理者 B
    struct ConcreteHandlerB {
        base: BaseHandler,
    }
    impl ConcreteHandlerB {
        fn new() -> Box<dyn Handler> { Box::new(Self { base: BaseHandler::new() }) }
    }
    impl Handler for ConcreteHandlerB {
         fn set_next(mut self: Box<Self>, next: Box<dyn Handler>) -> Box<dyn Handler> {
             self.base.next_handler = Some(next);
             self
         }
         fn handle(&self, request: &str) -> Option<String> {
             if request == "RequestB" {
                 Some("ConcreteHandlerB handled the request".to_string())
             } else {
                 self.base.handle_next(request)
             }
         }
          fn next(&self) -> Option<&dyn Handler> {
            self.base.next_handler.as_deref()
         }
    }

    // 具体处理者 C (默认处理或链尾)
    struct DefaultHandler {
        base: BaseHandler,
    }
    impl DefaultHandler {
        fn new() -> Box<dyn Handler> { Box::new(Self { base: BaseHandler::new() }) }
    }
    impl Handler for DefaultHandler {
         fn set_next(mut self: Box<Self>, next: Box<dyn Handler>) -> Box<dyn Handler> {
             // 通常默认处理者是链的末尾，但也可以设置
             self.base.next_handler = Some(next);
             self
         }
         fn handle(&self, request: &str) -> Option<String> {
             // 尝试处理，如果不能，则传递或返回默认值
             println!("DefaultHandler reached for request: {}", request);
             self.base.handle_next(request).or_else(|| Some("DefaultHandler provided a default response".to_string()))
         }
          fn next(&self) -> Option<&dyn Handler> {
             self.base.next_handler.as_deref()
         }
    }


    fn main() {
        // 构建责任链 A -> B -> Default
        let handler_a = ConcreteHandlerA::new();
        let handler_b = ConcreteHandlerB::new();
        let default_handler = DefaultHandler::new();

        // 链式设置：default_handler 变成 B 的 next, B 变成 A 的 next
        // 注意 set_next 消耗并返回 Box，所以需要重新赋值
        let chain = handler_a.set_next(handler_b.set_next(default_handler));


        println!("Sending RequestA...");
        if let Some(result) = chain.handle("RequestA") {
            println!("  Result: {}", result);
        }

        println!("Sending RequestB...");
        if let Some(result) = chain.handle("RequestB") {
             println!("  Result: {}", result);
        }

        println!("Sending RequestC (unhandled by A or B)...");
        if let Some(result) = chain.handle("RequestC") {
             println!("  Result: {}", result);
        }
    }

    ```

#### 1.5.2. 命令模式 (Command)

- **定义**: 将一个请求封装为一个对象，从而使你可用不同的请求对客户进行参数化；对请求排队或记录请求日志，以及支持可撤销的操作。
- **解释**: 将请求的调用者与接收者解耦。命令对象封装了动作和接收者。
- **Rust 示例**:

    ```rust
    // 命令接口 (Command)
    trait Command {
        // Box<Self> 表示执行可能会消耗命令本身，如果需要重复执行则用 &mut self 或 &self
        fn execute(&mut self);
        // 可选：撤销操作
        // fn undo(&mut self);
    }

    // 接收者 (Receiver) - 执行实际操作的对象
    struct Light {
        is_on: bool,
    }
    impl Light {
        fn turn_on(&mut self) {
            self.is_on = true;
            println!("Light is ON");
        }
        fn turn_off(&mut self) {
            self.is_on = false;
            println!("Light is OFF");
        }
    }

    // 具体命令 - 开灯
    struct TurnOnCommand {
        // 持有接收者的引用或可变引用
        light: Rc<RefCell<Light>>, // 使用 Rc<RefCell> 允许多个命令共享并修改同一个 Light
    }
    impl Command for TurnOnCommand {
        fn execute(&mut self) {
            self.light.borrow_mut().turn_on();
        }
    }

    // 具体命令 - 关灯
    struct TurnOffCommand {
        light: Rc<RefCell<Light>>,
    }
    impl Command for TurnOffCommand {
         fn execute(&mut self) {
             self.light.borrow_mut().turn_off();
         }
    }

    // 调用者 (Invoker) - 持有并触发命令
    struct RemoteControl {
        command: Option<Box<dyn Command>>, // 可以持有单个或多个命令
    }
    impl RemoteControl {
        fn new() -> Self { RemoteControl { command: None } }

        fn set_command(&mut self, command: Box<dyn Command>) {
            self.command = Some(command);
        }

        fn press_button(&mut self) {
            println!("Invoker: Pressing button...");
            if let Some(cmd) = self.command.as_mut() {
                cmd.execute();
            } else {
                 println!("Invoker: No command assigned.");
            }
        }
    }

    // --- 使用 Rc 和 RefCell 的版本 ---
    use std::rc::Rc;
    use std::cell::RefCell;

    fn main() {
        // 创建接收者
        let light = Rc::new(RefCell::new(Light { is_on: false }));

        // 创建具体命令，传入接收者的共享引用
        let turn_on = Box::new(TurnOnCommand { light: Rc::clone(&light) });
        let turn_off = Box::new(TurnOffCommand { light: Rc::clone(&light) });

        // 创建调用者
        let mut remote = RemoteControl::new();

        // 设置并执行开灯命令
        remote.set_command(turn_on);
        remote.press_button(); // 输出 Light is ON

        // 检查状态
        println!("Light status: {}", light.borrow().is_on); // true

        // 设置并执行关灯命令
        remote.set_command(turn_off);
        remote.press_button(); // 输出 Light is OFF

         // 检查状态
        println!("Light status: {}", light.borrow().is_on); // false
    }
    ```

#### 1.5.3. 解释器模式 (Interpreter)

- **定义**: 给定一个语言，定义它的文法的一种表示，并定义一个解释器，这个解释器使用该表示来解释语言中的句子。
- **解释**: 用于构建语言解析器或处理特定语法的表达式。通常涉及为语法中的每个规则（终结符和非终结符）创建一个类。实现起来可能比较复杂。
- **Rust 示例 (简单概念)**:

    ```rust
    use std::collections::HashMap;

    // 上下文，存储变量等信息
    type Context = HashMap<String, i32>;

    // 抽象表达式 trait
    trait Expression {
        // 解释方法，接收上下文并返回结果
        fn interpret(&self, context: &Context) -> i32;
    }

    // 终结符表达式 - 数字
    struct Number {
        value: i32,
    }
    impl Expression for Number {
        fn interpret(&self, _context: &Context) -> i32 {
            self.value
        }
    }

    // 终结符表达式 - 变量
    struct Variable {
         name: String,
    }
    impl Expression for Variable {
         fn interpret(&self, context: &Context) -> i32 {
             *context.get(&self.name).unwrap_or(&0) // 如果变量不存在，返回 0
         }
    }


    // 非终结符表达式 - 加法
    struct Add {
        left: Box<dyn Expression>,
        right: Box<dyn Expression>,
    }
    impl Expression for Add {
        fn interpret(&self, context: &Context) -> i32 {
            self.left.interpret(context) + self.right.interpret(context)
        }
    }

    // 非终结符表达式 - 减法
    struct Subtract {
         left: Box<dyn Expression>,
         right: Box<dyn Expression>,
    }
    impl Expression for Subtract {
         fn interpret(&self, context: &Context) -> i32 {
             self.left.interpret(context) - self.right.interpret(context)
         }
    }


    fn main() {
        let mut context = Context::new();
        context.insert("x".to_string(), 10);
        context.insert("y".to_string(), 5);
        context.insert("z".to_string(), 2);

        // 构建表达式树: (x + y) - z
        // z
        let expr_z = Box::new(Variable { name: "z".to_string() });
        // y
        let expr_y = Box::new(Variable { name: "y".to_string() });
        // x
        let expr_x = Box::new(Variable { name: "x".to_string() });
        // x + y
        let expr_add_xy = Box::new(Add { left: expr_x, right: expr_y });
        // (x + y) - z
        let expression_tree = Box::new(Subtract { left: expr_add_xy, right: expr_z });


        // 解释表达式
        let result = expression_tree.interpret(&context);
        println!("Expression: (x + y) - z");
        println!("Context: x=10, y=5, z=2");
        println!("Result: {}", result); // 输出: 13

        // 构建另一个表达式: 100 + (x - 5)
        let expr_100 = Box::new(Number { value: 100 });
        let expr_5 = Box::new(Number { value: 5 });
        let expr_x2 = Box::new(Variable { name: "x".to_string() });
        let expr_sub_x5 = Box::new(Subtract { left: expr_x2, right: expr_5 });
        let expression_tree2 = Box::new(Add { left: expr_100, right: expr_sub_x5 });

        let result2 = expression_tree2.interpret(&context);
         println!("\nExpression: 100 + (x - 5)");
         println!("Context: x=10, y=5, z=2");
         println!("Result: {}", result2); // 输出: 105

    }
    ```

#### 1.5.4. 迭代器模式 (Iterator)

- **定义**: 提供一种方法顺序访问一个聚合对象中各个元素, 而又不需暴露该对象的内部表示。
- **解释**: 在 Rust 中，这是通过标准库的 `Iterator` trait 实现的，是语言的核心部分。
- **Rust 示例**:

    ```rust
    // 一个简单的集合类型
    struct MyCollection<T> {
        items: Vec<T>,
    }

    impl<T> MyCollection<T> {
        fn new() -> Self {
            MyCollection { items: Vec::new() }
        }
        fn add(&mut self, item: T) {
            self.items.push(item);
        }

        // 返回一个实现了 Iterator trait 的类型
        // 可以是 Vec 的迭代器，或者自定义迭代器
        fn iter(&self) -> std::slice::Iter<'_, T> {
            self.items.iter()
        }
         // 如果需要可变迭代
         fn iter_mut(&mut self) -> std::slice::IterMut<'_, T> {
             self.items.iter_mut()
         }
         // 如果需要获取所有权
         fn into_iter(self) -> std::vec::IntoIter<T> {
             self.items.into_iter()
         }
    }

    // Rust 标准库已经为 Vec 等集合实现了迭代器
    // 我们可以直接使用它们

    fn main() {
        let mut collection = MyCollection::new();
        collection.add(1);
        collection.add(2);
        collection.add(3);

        println!("Iterating using iter():");
        // 使用 for 循环（语法糖，内部调用 into_iter()，再调用 next()）
        for item in collection.iter() {
            println!("Item: {}", item);
            // item 是 &i32 类型
        }

         println!("\nIterating using iter_mut() and modifying:");
         for item in collection.iter_mut() {
             *item *= 2; // 修改元素
              println!("Modified Item: {}", item);
             // item 是 &mut i32 类型
         }


         println!("\nIterating using into_iter() and consuming:");
          // into_iter 会消耗 collection
         for item in collection.into_iter() {
              println!("Consumed Item: {}", item);
             // item 是 i32 类型
         }

        // collection 已经被消耗，不能再使用
        // println!("{:?}", collection.items); // 这会编译错误

        // --- 直接使用 Vec 的迭代器 ---
        let numbers = vec![10, 20, 30];
        let mut iter = numbers.iter(); // 创建迭代器

        // 手动调用 next()
        println!("\nManual iteration:");
        println!("{:?}", iter.next()); // Some(&10)
        println!("{:?}", iter.next()); // Some(&20)
        println!("{:?}", iter.next()); // Some(&30)
        println!("{:?}", iter.next()); // None
    }
    ```

#### 1.5.5. 中介者模式 (Mediator)

- **定义**: 用一个中介对象来封装一系列的对象交互。中介者使各个对象不需要显式地相互引用，从而使其耦合松散，而且可以独立地改变它们之间的交互。
- **解释**: 用于减少对象之间复杂的直接依赖关系，将交互逻辑集中到中介者中。
- **Rust 示例**:

    ```rust
    use std::cell::RefCell;
    use std::rc::{Rc, Weak}; // 使用 Weak 防止引用循环

    // 中介者接口
    trait Mediator {
        // 组件通知中介者发生了某个事件
        fn notify(&self, sender: Weak<RefCell<dyn Colleague>>, event: &str);
    }

    // 同事（组件）接口
    trait Colleague {
        fn set_mediator(&mut self, mediator: Weak<RefCell<dyn Mediator>>);
        // 自身的操作，可能需要通知中介者
        fn operation(&self, event: &str);
        // 接收来自中介者的消息
        fn receive(&self, message: &str);
        // 提供一个获取 Weak 引用的方法，以便传递给 notify
        fn get_weak(&self) -> Weak<RefCell<dyn Colleague>>;
    }

    // 具体中介者
    struct ConcreteMediator {
        // 持有对所有同事的弱引用，防止循环引用
        colleague1: Weak<RefCell<dyn Colleague>>,
        colleague2: Weak<RefCell<dyn Colleague>>,
    }

    impl ConcreteMediator {
        // 创建时需要传入同事的强引用，然后降级为弱引用
         fn new(c1: Rc<RefCell<dyn Colleague>>, c2: Rc<RefCell<dyn Colleague>>) -> Rc<RefCell<Self>> {
             let mediator = Rc::new(RefCell::new(Self {
                 colleague1: Rc::downgrade(&c1),
                 colleague2: Rc::downgrade(&c2),
             }));
            // 设置同事的中介者
            c1.borrow_mut().set_mediator(Rc::downgrade(&mediator) as Weak<RefCell<dyn Mediator>>);
            c2.borrow_mut().set_mediator(Rc::downgrade(&mediator) as Weak<RefCell<dyn Mediator>>);
             mediator
         }
    }

    impl Mediator for ConcreteMediator {
        fn notify(&self, sender: Weak<RefCell<dyn Colleague>>, event: &str) {
            println!("Mediator received event '{}' from a colleague.", event);
            // 将发送者升级为强引用以比较指针地址
            if let Some(sender_strong) = sender.upgrade() {
                 let sender_ptr = Rc::as_ptr(&sender_strong);

                // 根据事件和发送者决定如何反应
                if event == "EventA" {
                    println!("Mediator reacts on EventA and triggers operation on Colleague2.");
                    if let Some(c2_strong) = self.colleague2.upgrade() {
                         // 确保不是自己给自己发消息 (虽然这里逻辑不一定需要)
                         if Rc::as_ptr(&c2_strong) != sender_ptr {
                              c2_strong.borrow().receive("Mediator says: Colleague2, do something due to EventA!");
                         }
                    }
                } else if event == "EventB" {
                     println!("Mediator reacts on EventB and triggers operation on Colleague1.");
                     if let Some(c1_strong) = self.colleague1.upgrade() {
                         if Rc::as_ptr(&c1_strong) != sender_ptr {
                             c1_strong.borrow().receive("Mediator says: Colleague1, react to EventB!");
                         }
                     }
                }
            } else {
                 println!("Mediator received event from a dropped colleague.");
            }
        }
    }


    // 具体同事 A
    struct ConcreteColleagueA {
        mediator: Weak<RefCell<dyn Mediator>>,
        // 用于获取自身的 Weak 引用
        self_weak: Weak<RefCell<Self>>,
    }
    impl ConcreteColleagueA {
        // 创建时返回强引用，并内部存储弱引用
        fn new() -> Rc<RefCell<Self>> {
             Rc::new_cyclic(|weak_ref| {
                 RefCell::new(Self {
                     mediator: Weak::new(),
                     self_weak: weak_ref.clone(),
                 })
             })
        }
    }
    impl Colleague for ConcreteColleagueA {
        fn set_mediator(&mut self, mediator: Weak<RefCell<dyn Mediator>>) {
            self.mediator = mediator;
        }
        fn operation(&self, event: &str) {
            println!("ColleagueA performs operation and triggers '{}'.", event);
            if let Some(m) = self.mediator.upgrade() {
                 m.borrow().notify(self.get_weak(), event);
            } else {
                 println!("ColleagueA has no mediator set.");
            }
        }
        fn receive(&self, message: &str) {
            println!("ColleagueA received: {}", message);
        }
         fn get_weak(&self) -> Weak<RefCell<dyn Colleague>> {
             // 将 Self 的 Weak 转换成 dyn Colleague 的 Weak
             self.self_weak.clone() as Weak<RefCell<dyn Colleague>>
         }
    }

    // 具体同事 B (结构类似 ColleagueA)
    struct ConcreteColleagueB {
         mediator: Weak<RefCell<dyn Mediator>>,
         self_weak: Weak<RefCell<Self>>,
    }
    impl ConcreteColleagueB {
         fn new() -> Rc<RefCell<Self>> {
             Rc::new_cyclic(|weak_ref| {
                 RefCell::new(Self {
                     mediator: Weak::new(),
                     self_weak: weak_ref.clone(),
                 })
             })
         }
    }
    impl Colleague for ConcreteColleagueB {
         fn set_mediator(&mut self, mediator: Weak<RefCell<dyn Mediator>>) {
             self.mediator = mediator;
         }
         fn operation(&self, event: &str) {
             println!("ColleagueB performs operation and triggers '{}'.", event);
             if let Some(m) = self.mediator.upgrade() {
                 m.borrow().notify(self.get_weak(), event);
             } else {
                  println!("ColleagueB has no mediator set.");
             }
         }
         fn receive(&self, message: &str) {
             println!("ColleagueB received: {}", message);
         }
         fn get_weak(&self) -> Weak<RefCell<dyn Colleague>> {
             self.self_weak.clone() as Weak<RefCell<dyn Colleague>>
         }
    }


    fn main() {
        // 创建同事
        let c1 = ConcreteColleagueA::new();
        let c2 = ConcreteColleagueB::new();

        // 创建中介者，它会自动设置同事的中介者引用
        let _mediator = ConcreteMediator::new(
            c1.clone() as Rc<RefCell<dyn Colleague>>, // 需要显式转换类型
            c2.clone() as Rc<RefCell<dyn Colleague>>
        );

        println!("Client triggers operation on ColleagueA.");
        c1.borrow().operation("EventA");

        println!("\nClient triggers operation on ColleagueB.");
        c2.borrow().operation("EventB");
    }

    ```

#### 1.5.6. 备忘录模式 (Memento)

- **定义**: 在不破坏封装性的前提下，捕获一个对象的内部状态，并在该对象之外保存这个状态。这样以后就可将该对象恢复到原先保存的状态。
- **解释**: 用于实现撤销/重做功能，或者在某个操作失败后恢复到之前的状态。
- **Rust 示例**:

    ```rust
    // 备忘录 (Memento) - 存储 Originator 的状态
    // 通常是一个简单的结构体，只包含需要保存的数据
    #[derive(Clone, Debug)] // 需要 Clone 来保存副本
    struct Memento {
        state: String, // 仅保存状态，不包含 Originator 的方法
    }

    // 发起人 (Originator) - 状态可以被保存和恢复的对象
    struct Originator {
        state: String,
    }

    impl Originator {
        fn new(state: &str) -> Self {
            Originator { state: state.to_string() }
        }

        fn set_state(&mut self, state: &str) {
            println!("Originator: Setting state to '{}'", state);
            self.state = state.to_string();
        }

        // 创建备忘录，包含当前状态的副本
        fn create_memento(&self) -> Memento {
             println!("Originator: Saving Memento.");
             Memento { state: self.state.clone() } // 克隆状态
        }

        // 从备忘录恢复状态
        fn restore_from_memento(&mut self, memento: &Memento) {
             self.state = memento.state.clone();
             println!("Originator: State restored from Memento to '{}'", self.state);
        }

        fn get_state(&self) -> &str {
            &self.state
        }
    }

    // 负责人 (Caretaker) - 负责保存和管理备忘录，但不访问其内容
    struct Caretaker {
        mementos: Vec<Memento>,
    }

    impl Caretaker {
        fn new() -> Self {
            Caretaker { mementos: Vec::new() }
        }

        fn add_memento(&mut self, memento: Memento) {
            self.mementos.push(memento);
        }

        // 获取备忘录，通常是最后一个或指定的索引
        fn get_memento(&self, index: usize) -> Option<&Memento> {
            self.mementos.get(index)
        }

        // 获取最后一个备忘录并移除（用于撤销）
        fn pop_memento(&mut self) -> Option<Memento> {
             self.mementos.pop()
        }
    }

    fn main() {
        let mut originator = Originator::new("Initial State");
        let mut caretaker = Caretaker::new();

        // 保存初始状态
        caretaker.add_memento(originator.create_memento());

        originator.set_state("State #1");
        caretaker.add_memento(originator.create_memento()); // 保存 State #1

        originator.set_state("State #2");
        // 不保存 State #2

        println!("Current State: {}", originator.get_state()); // State #2

        // 撤销到 State #1
        if let Some(memento1) = caretaker.pop_memento() { // 弹出 State #1 的备忘录
            originator.restore_from_memento(&memento1);
            println!("After undo: {}", originator.get_state()); // State #1

            // 如果需要再撤销到初始状态
             if let Some(memento0) = caretaker.pop_memento() { // 弹出 Initial State 的备忘录
                 originator.restore_from_memento(&memento0);
                 println!("After second undo: {}", originator.get_state()); // Initial State
             }
        }

         // 也可以通过索引获取
         // caretaker.add_memento(originator.create_memento()); // 重新保存 Initial State
         // originator.set_state("Another State");
         // if let Some(memento_initial) = caretaker.get_memento(0) {
         //    originator.restore_from_memento(memento_initial);
         //    println!("Restored to initial via index: {}", originator.get_state());
         // }
    }
    ```

#### 1.5.7. 观察者模式 (Observer)

- **定义**: 定义对象间的一种一对多的依赖关系，当一个对象的状态发生改变时，所有依赖于它的对象都得到通知并被自动更新。
- **解释**: 用于实现事件处理系统、GUI 组件通信等。主题 (Subject) 维护观察者 (Observer) 列表，并在状态改变时通知它们。
- **Rust 示例 (使用 trait objects)**:

    ```rust
    use std::cell::RefCell;
    use std::collections::HashMap;
    use std::rc::Rc; // 在单线程上下文中使用 Rc 和 RefCell

    // 观察者 trait
    trait Observer {
        // 主题状态更新时调用
        fn update(&self, state: &str);
        // 获取观察者的唯一标识，用于注册和取消注册
        fn id(&self) -> usize;
    }

    // 主题 trait (或具体类)
    trait Subject<'a> {
        fn attach(&mut self, observer: Rc<RefCell<dyn Observer + 'a>>);
        fn detach(&mut self, observer_id: usize);
        fn notify(&self);
    }

    // 具体主题
    struct ConcreteSubject<'a> {
        // 存储观察者，使用 Rc<RefCell<>> 允许多个地方共享和修改观察者
        // 使用 HashMap 可以方便地通过 ID 删除
        observers: HashMap<usize, Rc<RefCell<dyn Observer + 'a>>>,
        state: String,
    }

    impl<'a> ConcreteSubject<'a> {
        fn new() -> Self {
            ConcreteSubject {
                observers: HashMap::new(),
                state: String::new(),
            }
        }

        // 改变状态并通知观察者
        fn set_state(&mut self, new_state: &str) {
             self.state = new_state.to_string();
             println!("Subject: State changed to '{}'", self.state);
             self.notify();
        }
    }

    impl<'a> Subject<'a> for ConcreteSubject<'a> {
        fn attach(&mut self, observer: Rc<RefCell<dyn Observer + 'a>>) {
            let id = observer.borrow().id();
            println!("Subject: Attaching observer {}.", id);
            self.observers.insert(id, observer);
        }

        fn detach(&mut self, observer_id: usize) {
             println!("Subject: Detaching observer {}.", observer_id);
             self.observers.remove(&observer_id);
        }

        fn notify(&self) {
            println!("Subject: Notifying observers...");
            for observer in self.observers.values() {
                observer.borrow().update(&self.state);
            }
        }
    }

    // 具体观察者 A
    struct ConcreteObserverA {
        id: usize,
        // 可以有自己的状态
    }
    impl ConcreteObserverA {
         fn new(id: usize) -> Rc<RefCell<Self>> {
             Rc::new(RefCell::new(Self { id }))
         }
    }
    impl Observer for ConcreteObserverA {
        fn update(&self, state: &str) {
            println!("Observer A ({}): Received update with state '{}'", self.id, state);
            // 根据状态执行相应操作
        }
         fn id(&self) -> usize { self.id }
    }

    // 具体观察者 B
    struct ConcreteObserverB {
        id: usize,
    }
     impl ConcreteObserverB {
         fn new(id: usize) -> Rc<RefCell<Self>> {
             Rc::new(RefCell::new(Self { id }))
         }
    }
    impl Observer for ConcreteObserverB {
         fn update(&self, state: &str) {
             println!("Observer B ({}): Got the state update: '{}'", self.id, state);
         }
         fn id(&self) -> usize { self.id }
    }


    fn main() {
        let mut subject = ConcreteSubject::new();

        let observer_a = ConcreteObserverA::new(1);
        let observer_b = ConcreteObserverB::new(2);
        let observer_a2 = ConcreteObserverA::new(3); // 另一个 A 类型的观察者

        // 附加观察者，需要将具体类型转换为 trait object
        subject.attach(observer_a.clone() as Rc<RefCell<dyn Observer>>);
        subject.attach(observer_b.clone() as Rc<RefCell<dyn Observer>>);
        subject.attach(observer_a2.clone() as Rc<RefCell<dyn Observer>>);


        subject.set_state("State 1");

        println!("\nDetaching Observer B (id 2)");
        subject.detach(2); // 通过 ID 取消注册

        subject.set_state("State 2");

    }
    ```

#### 1.5.8. 状态模式 (State)

- **定义**: 允许一个对象在其内部状态改变时改变它的行为。对象看起来似乎修改了它的类。
- **解释**: 将与特定状态相关的行为局部化，并且将不同状态的行为分割开来。通常使用一个状态接口和多个具体状态类。
- **Rust 示例 (使用 enum 和 trait object)**:

    ```rust
    // --- 方法 1: 使用 Trait Object ---

    // 状态接口
    trait State {
        // 方法返回 Box<dyn State> 来允许状态转移
        fn handle(self: Box<Self>, context: &mut Context) -> Box<dyn State>;
        fn get_name(&self) -> &'static str; // 用于调试或显示
    }

    // 具体状态 A
    struct StateA;
    impl State for StateA {
        fn handle(self: Box<Self>, context: &mut Context) -> Box<dyn State> {
            println!("Handling in StateA. Current value: {}", context.value);
            context.value += 1;
            if context.value > 5 {
                println!("Transitioning from StateA to StateB");
                Box::new(StateB) // 转移到状态 B
            } else {
                self // 保持在状态 A
            }
        }
         fn get_name(&self) -> &'static str { "StateA" }
    }

    // 具体状态 B
    struct StateB;
    impl State for StateB {
        fn handle(self: Box<Self>, context: &mut Context) -> Box<dyn State> {
            println!("Handling in StateB. Current value: {}", context.value);
            context.value -= 2;
            if context.value <= 0 {
                println!("Transitioning from StateB to StateA");
                 Box::new(StateA) // 转移回状态 A
            } else {
                 self // 保持在状态 B
            }
        }
         fn get_name(&self) -> &'static str { "StateB" }
    }

    // 上下文 (Context) - 持有当前状态
    struct Context {
        state: Option<Box<dyn State>>,
        value: i32,
    }

    impl Context {
        fn new() -> Self {
            let initial_state = Box::new(StateA); // 初始状态为 A
            Context {
                state: Some(initial_state),
                value: 0,
            }
        }

        // 请求处理，委托给当前状态
        fn request(&mut self) {
            // take() 获取 state 的所有权，允许状态转移
            if let Some(current_state) = self.state.take() {
                println!("Context requesting handle from state: {}", current_state.get_name());
                 // 调用 handle，它会消耗旧状态并返回新状态
                self.state = Some(current_state.handle(self));
                println!("Context is now in state: {}", self.state.as_ref().unwrap().get_name());

            } else {
                println!("Context has no state.");
            }
        }
    }


    // --- 方法 2: 使用 Enum (更符合 Rust 习惯) ---
    enum DocumentStateEnum {
        Draft,
        Moderation { reason: String },
        Published,
    }

    struct Document {
        state: DocumentStateEnum,
        content: String,
    }

    impl Document {
        fn new() -> Self {
            Document {
                state: DocumentStateEnum::Draft,
                content: "".to_string(),
            }
        }

        fn publish(&mut self) {
            match self.state {
                DocumentStateEnum::Draft => {
                    println!("Transitioning Draft -> Moderation");
                    self.state = DocumentStateEnum::Moderation { reason: "Awaiting review".to_string() };
                }
                DocumentStateEnum::Moderation { ref reason }=> {
                    println!("Already in Moderation ({}), cannot publish directly again. Approve first.", reason);
                    // 或者直接转换到 Published? 取决于业务逻辑
                    // self.state = DocumentStateEnum::Published;
                }
                DocumentStateEnum::Published => {
                    println!("Already Published.");
                }
            }
        }

        fn approve(&mut self) {
             match self.state {
                 DocumentStateEnum::Draft => {
                     println!("Cannot approve a Draft directly. Publish first.");
                 }
                 DocumentStateEnum::Moderation {..} => { // 忽略 reason
                     println!("Transitioning Moderation -> Published");
                     self.state = DocumentStateEnum::Published;
                 }
                 DocumentStateEnum::Published => {
                     println!("Already Published.");
                 }
             }
        }

         fn reject(&mut self, reason: String) {
              match self.state {
                  DocumentStateEnum::Moderation {..} => {
                      println!("Transitioning Moderation -> Draft (Rejected: {})", reason);
                      self.state = DocumentStateEnum::Draft;
                  }
                  _ => println!("Cannot reject from current state."),
              }
         }

        fn get_state_name(&self) -> &'static str {
             match self.state {
                 DocumentStateEnum::Draft => "Draft",
                 DocumentStateEnum::Moderation {..} => "Moderation",
                 DocumentStateEnum::Published => "Published",
             }
        }
    }


    fn main() {
        println!("--- State Pattern using Trait Object ---");
        let mut context = Context::new();
        context.request(); // A -> A (val=1)
        context.request(); // A -> A (val=2)
        context.request(); // A -> A (val=3)
        context.request(); // A -> A (val=4)
        context.request(); // A -> A (val=5)
        context.request(); // A -> B (val=6)
        context.request(); // B -> B (val=4)
        context.request(); // B -> B (val=2)
        context.request(); // B -> A (val=0)
        context.request(); // A -> A (val=1)


        println!("\n--- State Pattern using Enum ---");
        let mut doc = Document::new();
        println!("Initial state: {}", doc.get_state_name()); // Draft
        doc.approve(); // Cannot approve
        doc.publish(); // Draft -> Moderation
        println!("Current state: {}", doc.get_state_name()); // Moderation
        doc.publish(); // Already in Moderation
        doc.reject("Needs more details".to_string()); // Moderation -> Draft
        println!("Current state: {}", doc.get_state_name()); // Draft
        doc.publish(); // Draft -> Moderation
        println!("Current state: {}", doc.get_state_name()); // Moderation
        doc.approve(); // Moderation -> Published
        println!("Current state: {}", doc.get_state_name()); // Published
        doc.approve(); // Already Published
    }
    ```

#### 1.5.9. 策略模式 (Strategy)

- **定义**: 定义一系列的算法,把它们一个个封装起来, 并且使它们可相互替换。策略模式使得算法可独立于使用它的客户而变化。
- **解释**: 允许在运行时选择算法或行为。将算法封装在独立的策略对象中。
- **Rust 示例 (使用 trait object 或 enum)**:

    ```rust
    // --- 方法 1: Trait Object ---

    // 策略接口
    trait SortStrategy {
        // 对 Vec<i32> 进行排序 (可以泛型化)
        fn sort(&self, data: &mut Vec<i32>);
    }

    // 具体策略 A: 冒泡排序 (仅为示例，效率低)
    struct BubbleSort;
    impl SortStrategy for BubbleSort {
        fn sort(&self, data: &mut Vec<i32>) {
            println!("Sorting using Bubble Sort");
            let n = data.len();
            for i in 0..n {
                for j in 0..n - 1 - i {
                    if data[j] > data[j + 1] {
                        data.swap(j, j + 1);
                    }
                }
            }
        }
    }

    // 具体策略 B: 标准库排序 (高效)
    struct StdSort;
    impl SortStrategy for StdSort {
        fn sort(&self, data: &mut Vec<i32>) {
             println!("Sorting using Standard Library Sort");
             data.sort(); // 使用 Rust 内建的高效排序
        }
    }

    // 上下文 (Context) - 持有策略对象
    struct Sorter {
        // 持有当前策略的 trait object
        strategy: Box<dyn SortStrategy>,
    }

    impl Sorter {
        // 创建时传入具体策略
        fn new(strategy: Box<dyn SortStrategy>) -> Self {
            Sorter { strategy }
        }

        // 可以动态改变策略
        fn set_strategy(&mut self, strategy: Box<dyn SortStrategy>) {
            self.strategy = strategy;
        }

        // 执行排序操作，委托给当前策略
        fn execute_sort(&self, data: &mut Vec<i32>) {
            self.strategy.sort(data);
        }
    }


    // --- 方法 2: Enum (当策略集合固定时更常用) ---
    enum ShippingStrategy {
        Standard,
        Express,
        NextDay,
    }

    struct Order {
        // ... 其他订单信息
        items_weight: f64,
    }

    impl Order {
        // 根据策略计算运费
        fn calculate_shipping(&self, strategy: ShippingStrategy) -> f64 {
             match strategy {
                 ShippingStrategy::Standard => self.items_weight * 1.5 + 5.0, // 假设基础运费 5元，每公斤 1.5元
                 ShippingStrategy::Express => self.items_weight * 3.0 + 10.0,
                 ShippingStrategy::NextDay => self.items_weight * 5.0 + 20.0,
             }
        }
    }

    fn main() {
        println!("--- Strategy Pattern using Trait Object ---");
        let mut data1 = vec![5, 1, 4, 2, 8];
        let mut data2 = data1.clone();

        // 使用冒泡排序策略
        let bubble_sorter = Sorter::new(Box::new(BubbleSort));
        bubble_sorter.execute_sort(&mut data1);
        println!("Data sorted with Bubble Sort: {:?}", data1);

        // 使用标准库排序策略
        let mut std_sorter = Sorter::new(Box::new(StdSort));
        std_sorter.execute_sort(&mut data2);
        println!("Data sorted with Std Sort: {:?}", data2);

        // 动态改变策略
        println!("\nChanging strategy for std_sorter to BubbleSort");
        std_sorter.set_strategy(Box::new(BubbleSort));
        let mut data3 = vec![9, 3, 7, 6];
        std_sorter.execute_sort(&mut data3);
        println!("Data sorted with changed strategy: {:?}", data3);


        println!("\n--- Strategy Pattern using Enum ---");
        let order = Order { items_weight: 2.5 };

        let standard_cost = order.calculate_shipping(ShippingStrategy::Standard);
        let express_cost = order.calculate_shipping(ShippingStrategy::Express);
        let next_day_cost = order.calculate_shipping(ShippingStrategy::NextDay);

        println!("Order weight: {} kg", order.items_weight);
        println!("Standard Shipping Cost: ${:.2}", standard_cost);
        println!("Express Shipping Cost: ${:.2}", express_cost);
        println!("Next Day Shipping Cost: ${:.2}", next_day_cost);

    }
    ```

#### 1.5.10. 模板方法模式 (Template Method)

- **定义**: 定义一个操作中的算法的骨架，而将一些步骤延迟到子类中。模板方法使得子类可以不改变一个算法的结构即可重定义该算法的某些特定步骤。
- **解释**: 在父类（或 trait）中定义算法的框架，允许子类（或实现者）覆盖或实现某些步骤。
- **Rust 示例**:

    ```rust
    // 模板方法定义在 trait 中
    trait ReportGenerator {
        // 模板方法 - 定义算法骨架
        fn generate_report(&self) {
            self.collect_data();
            self.format_data();
            // 调用钩子方法，允许子类选择性覆盖
            if self.add_header() {
                 println!("--- Report Header ---");
            }
            self.print_report();
             if self.add_footer() {
                 println!("--- Report Footer ---");
            }
        }

        // 抽象方法 - 必须由实现者提供
        fn collect_data(&self);
        fn format_data(&self);
        fn print_report(&self);

        // 钩子方法 (Hook) - 提供默认实现，实现者可以选择性覆盖
        fn add_header(&self) -> bool { true } // 默认添加页眉
        fn add_footer(&self) -> bool { true } // 默认添加页脚
    }

    // 具体实现 A: PDF 报告
    struct PdfReport;
    impl ReportGenerator for PdfReport {
        fn collect_data(&self) {
            println!("PdfReport: Collecting data from database.");
        }
        fn format_data(&self) {
            println!("PdfReport: Formatting data into PDF structure.");
        }
        fn print_report(&self) {
             println!("PdfReport: Printing PDF report content.");
        }
        // 覆盖钩子方法 - PDF 不需要页脚
        fn add_footer(&self) -> bool {
            println!("PdfReport: Overriding add_footer hook - No footer needed.");
            false
        }
    }

    // 具体实现 B: CSV 报告
    struct CsvReport;
    impl ReportGenerator for CsvReport {
         fn collect_data(&self) {
             println!("CsvReport: Collecting data from API.");
         }
         fn format_data(&self) {
             println!("CsvReport: Formatting data into CSV rows.");
         }
         fn print_report(&self) {
             println!("CsvReport: Printing CSV report content.");
         }
         // 使用默认的钩子实现 (添加页眉和页脚)
    }


    fn client_code(generator: &dyn ReportGenerator) {
        generator.generate_report();
    }

    fn main() {
        println!("Generating PDF Report:");
        let pdf_generator = PdfReport;
        client_code(&pdf_generator);

        println!("\nGenerating CSV Report:");
        let csv_generator = CsvReport;
        client_code(&csv_generator);
    }

    ```

#### 1.5.11. 访问者模式 (Visitor)

- **定义**: 表示一个作用于某对象结构中的各元素的操作。它使你可以在不改变各元素的类的前提下定义作用于这些元素的新操作。
- **解释**: 将操作（访问者）与对象结构（元素）分离。适用于需要对一个复杂的对象结构（如 AST）执行多种不同且不相关的操作。
- **Rust 示例**:

    ```rust
    // 访问者 trait
    trait Visitor {
        // 为每种具体元素提供一个访问方法
        fn visit_element_a(&mut self, element: &ElementA);
        fn visit_element_b(&mut self, element: &ElementB);
    }

    // 元素 trait
    trait Element {
        // 接受访问者的方法 (双重分发)
        fn accept(&self, visitor: &mut dyn Visitor);
    }

    // 具体元素 A
    struct ElementA {
        data_a: String,
    }
    impl Element for ElementA {
        fn accept(&self, visitor: &mut dyn Visitor) {
            visitor.visit_element_a(self); // 调用访问者对应的方法
        }
    }

    // 具体元素 B
    struct ElementB {
        data_b: i32,
    }
    impl Element for ElementB {
        fn accept(&self, visitor: &mut dyn Visitor) {
             visitor.visit_element_b(self);
        }
    }

    // 具体访问者 1: 打印操作
    struct PrintVisitor;
    impl Visitor for PrintVisitor {
        fn visit_element_a(&mut self, element: &ElementA) {
            println!("Visiting ElementA with data: {}", element.data_a);
        }
        fn visit_element_b(&mut self, element: &ElementB) {
            println!("Visiting ElementB with data: {}", element.data_b);
        }
    }

    // 具体访问者 2: 导出操作 (示例)
    struct ExportVisitor {
        result: String,
    }
    impl ExportVisitor { fn new() -> Self { ExportVisitor { result: String::new() } } }
    impl Visitor for ExportVisitor {
        fn visit_element_a(&mut self, element: &ElementA) {
            self.result.push_str(&format!("<ElementA>{}</ElementA>\n", element.data_a));
        }
        fn visit_element_b(&mut self, element: &ElementB) {
            self.result.push_str(&format!("<ElementB>{}</ElementB>\n", element.data_b));
        }
    }


    // 对象结构 (通常是一个集合或树)
    struct ObjectStructure {
        elements: Vec<Box<dyn Element>>, // 持有一系列元素
    }

    impl ObjectStructure {
        fn new() -> Self { ObjectStructure { elements: Vec::new() } }
        fn attach(&mut self, element: Box<dyn Element>) { self.elements.push(element); }

        // 让访问者访问所有元素
        fn run_visitor(&self, visitor: &mut dyn Visitor) {
            for element in &self.elements {
                element.accept(visitor); // 每个元素接受访问者
            }
        }
    }

    fn main() {
        let mut structure = ObjectStructure::new();
        structure.attach(Box::new(ElementA { data_a: "Hello".to_string() }));
        structure.attach(Box::new(ElementB { data_b: 42 }));
        structure.attach(Box::new(ElementA { data_a: "World".to_string() }));

        println!("--- Using PrintVisitor ---");
        let mut print_visitor = PrintVisitor;
        structure.run_visitor(&mut print_visitor);

        println!("\n--- Using ExportVisitor ---");
        let mut export_visitor = ExportVisitor::new();
        structure.run_visitor(&mut export_visitor);
        println!("Export Result:\n{}", export_visitor.result);
    }
    ```

---

## 2. 并发并行设计模式

### 2.1. 概念与定义

并发 (Concurrency) 是指系统具有同时处理多个任务的能力（不一定同时执行，可能交错执行）。并行 (Parallelism) 是指系统具有同时执行多个任务的能力（真正同时执行，需要多核处理器）。并发/并行设计模式专注于解决在多线程或多进程环境中协调任务、共享资源、通信等问题，以提高性能、响应性和资源利用率。Rust 通过其所有权系统、`Send` 和 `Sync` trait、标准库（`std::thread`, `std::sync`）以及生态（`tokio`, `async-std`, `rayon`, `crossbeam`）提供了强大的并发和并行支持。

### 2.2. 常见模式

#### 2.2.1. 活动对象模式 (Active Object)

- **定义**: 将方法的执行与其调用解耦，使得方法调用发生在一个线程中，而方法的执行发生在另一个（或一组）属于活动对象的线程中。调用者通过代理与活动对象交互，调用是异步的，通常通过消息队列传递。
- **解释**: 用于将异步调用和顺序执行结合起来，隐藏并发细节，简化客户端代码。
- **Rust 示例 (使用 `tokio` 和 `mpsc` channel)**:

    ```rust
    use tokio::sync::{mpsc, oneshot};
    use std::thread; // 仅用于展示同步调用方

    // 定义活动对象可以处理的消息类型
    enum Command {
        Increment,
        GetValue(oneshot::Sender<i32>), // 包含一个用于返回结果的通道
    }

    // 活动对象结构体
    struct ActiveObject {
        counter: i32,
        receiver: mpsc::Receiver<Command>, // 接收命令的通道
    }

    impl ActiveObject {
        // 活动对象的运行循环，在一个单独的 task 中运行
        async fn run(mut self) {
            println!("ActiveObject: Run loop started.");
            // 不断从通道接收命令并处理
            while let Some(command) = self.receiver.recv().await {
                match command {
                    Command::Increment => {
                        self.counter += 1;
                        println!("ActiveObject: Incremented counter to {}", self.counter);
                    }
                    Command::GetValue(responder) => {
                         println!("ActiveObject: Sending current value {}.", self.counter);
                        // 通过 oneshot 通道将结果发送回调用者
                        let _ = responder.send(self.counter);
                        // 忽略发送错误 (如果调用者已经放弃等待)
                    }
                }
            }
             println!("ActiveObject: Run loop finished.");
        }
    }

    // 代理对象 (Proxy) - 提供给客户端的同步或异步接口
    #[derive(Clone)] // 允许克隆代理，以便多处使用
    struct ActiveObjectProxy {
        sender: mpsc::Sender<Command>, // 发送命令到活动对象的通道
    }

    impl ActiveObjectProxy {
        // 创建活动对象和代理
        fn new(buffer_size: usize) -> Self {
            let (sender, receiver) = mpsc::channel(buffer_size);
            let active_obj = ActiveObject { counter: 0, receiver };

            // 启动活动对象的 task
            tokio::spawn(active_obj.run());

            ActiveObjectProxy { sender }
        }

        // 异步方法 - 发送 Increment 命令 (无需等待结果)
        async fn increment(&self) {
             println!("Proxy: Sending Increment command.");
            // 发送命令，忽略错误 (如果活动对象已停止)
            let _ = self.sender.send(Command::Increment).await;
        }

        // 异步方法 - 发送 GetValue 命令并等待结果
        async fn get_value(&self) -> Option<i32> {
             println!("Proxy: Sending GetValue command.");
            // 创建一个 oneshot 通道用于接收结果
            let (send, recv) = oneshot::channel();
            if self.sender.send(Command::GetValue(send)).await.is_ok() {
                 println!("Proxy: Waiting for value from ActiveObject...");
                // 等待活动对象通过 oneshot 通道发送结果
                match recv.await {
                    Ok(value) => {
                        println!("Proxy: Received value {}.", value);
                        Some(value)
                    }
                    Err(_) => {
                        println!("Proxy: Failed to receive value (ActiveObject might have stopped).");
                        None // 通道关闭，获取失败
                    }
                }
            } else {
                println!("Proxy: Failed to send GetValue command.");
                None // 发送失败
            }
        }
    }


    #[tokio::main]
    async fn main() {
        let proxy = ActiveObjectProxy::new(10); // 创建代理，活动对象在后台启动

        // 从异步上下文中调用
        proxy.increment().await;
        proxy.increment().await;

        if let Some(val) = proxy.get_value().await {
            println!("Async main: Got value = {}", val); // 应该输出 2
        }

        // 也可以在非 async 环境中通过 tokio::runtime 或 block_on 调用
        let proxy_clone = proxy.clone();
        let handle = thread::spawn(move || {
             println!("Sync thread: Calling increment.");
             // 在同步线程中需要一个运行时来执行 async 调用
             let rt = tokio::runtime::Runtime::new().unwrap();
             rt.block_on(proxy_clone.increment());

              println!("Sync thread: Calling get_value.");
             let value = rt.block_on(proxy_clone.get_value());
              println!("Sync thread: Got value = {:?}", value); // 应该输出 3
              value
        });

        let result = handle.join().unwrap();
        println!("Main thread: Sync thread result: {:?}", result);

        // 再调用一次获取值
        if let Some(val) = proxy.get_value().await {
            println!("Async main: Final value = {}", val); // 应该输出 3
        }

         // 为了让 ActiveObject run loop 有机会结束 (如果通道关闭), 可以 drop proxy
         drop(proxy);
         // 加一点延迟确保后台任务有机会清理 (实际应用中可能需要更健壮的关闭机制)
         tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
         println!("Main finished.");
    }

    ```

#### 2.2.2. 管程模式 (Monitor)

- **定义**: 一种同步构造，允许线程安全地共享数据。它封装了共享数据和一组操作这些数据的方法，并确保在任何时候只有一个线程能执行这些方法（互斥）。通常还包含条件变量，允许线程在特定条件下等待和被唤醒。
- **解释**: Rust 的 `Mutex<T>` 和 `RwLock<T>` 结合 `Condvar` 可以用来实现管程的核心思想。`Mutex` 保护共享数据，确保同一时间只有一个线程能访问，`Condvar` 用于线程间的等待和通知。
- **Rust 示例 (使用 `Mutex` 和 `Condvar` 实现有界缓冲区)**:

    ```rust
    use std::sync::{Arc, Mutex, Condvar};
    use std::collections::VecDeque;
    use std::thread;
    use std::time::Duration;

    // 管程结构，封装共享数据和同步原语
    struct BoundedBuffer<T> {
        buffer: Mutex<VecDeque<T>>, // 共享缓冲区，使用 Mutex 保护
        capacity: usize,            // 缓冲区容量
        cond_not_full: Condvar,     // 条件变量：缓冲区未满
        cond_not_empty: Condvar,    // 条件变量：缓冲区非空
    }

    impl<T: Send + 'static> BoundedBuffer<T> { // T 必须是 Send
        fn new(capacity: usize) -> Arc<Self> {
            Arc::new(BoundedBuffer {
                buffer: Mutex::new(VecDeque::with_capacity(capacity)),
                capacity,
                cond_not_full: Condvar::new(),
                cond_not_empty: Condvar::new(),
            })
        }

        // 生产数据 (放入缓冲区)
        fn produce(&self, item: T) {
             // 1. 获取锁
             let mut buffer_guard = self.buffer.lock().unwrap();
             println!("Producer: Acquired lock. Buffer size: {}", buffer_guard.len());

            // 2. 检查条件 (缓冲区是否已满)
            // 使用 while 循环防止虚假唤醒 (spurious wakeups)
            while buffer_guard.len() == self.capacity {
                println!("Producer: Buffer full, waiting...");
                 // 缓冲区已满，释放锁并等待 cond_not_full 信号
                buffer_guard = self.cond_not_full.wait(buffer_guard).unwrap();
                 println!("Producer: Woken up. Buffer size: {}", buffer_guard.len());
            }

            // 3. 执行操作 (放入数据)
            println!("Producer: Adding item. Buffer size before add: {}", buffer_guard.len());
            buffer_guard.push_back(item);
            println!("Producer: Item added. Buffer size after add: {}", buffer_guard.len());


            // 4. 发出信号 (通知可能在等待的消费者)
            // 只需要通知一个等待的消费者即可
            self.cond_not_empty.notify_one();
             println!("Producer: Notified consumer. Releasing lock.");

            // 5. 锁在 buffer_guard 离开作用域时自动释放
        }

        // 消费数据 (从缓冲区取出)
        fn consume(&self) -> T {
             // 1. 获取锁
             let mut buffer_guard = self.buffer.lock().unwrap();
             println!("Consumer: Acquired lock. Buffer size: {}", buffer_guard.len());

            // 2. 检查条件 (缓冲区是否为空)
            while buffer_guard.is_empty() {
                 println!("Consumer: Buffer empty, waiting...");
                 // 缓冲区为空，释放锁并等待 cond_not_empty 信号
                buffer_guard = self.cond_not_empty.wait(buffer_guard).unwrap();
                 println!("Consumer: Woken up. Buffer size: {}", buffer_guard.len());
            }

            // 3. 执行操作 (取出数据)
             println!("Consumer: Removing item. Buffer size before remove: {}", buffer_guard.len());
            let item = buffer_guard.pop_front().unwrap(); // unwrap 因为循环保证了不为空
            println!("Consumer: Item removed. Buffer size after remove: {}", buffer_guard.len());

            // 4. 发出信号 (通知可能在等待的生产者)
            self.cond_not_full.notify_one();
             println!("Consumer: Notified producer. Releasing lock.");

            // 5. 锁自动释放，返回数据
            item
        }
    }

    fn main() {
        let buffer = BoundedBuffer::new(3); // 容量为 3 的缓冲区

        let producer_buffer = Arc::clone(&buffer);
        let producer_handle = thread::spawn(move || {
            for i in 0..7 {
                println!("Producer starting produce {}", i);
                producer_buffer.produce(i);
                println!("Producer finished produce {}", i);
                thread::sleep(Duration::from_millis(100)); // 模拟生产耗时
            }
        });

        let consumer_buffer = Arc::clone(&buffer);
        let consumer_handle = thread::spawn(move || {
            for _ in 0..7 {
                 println!("Consumer starting consume");
                let item = consumer_buffer.consume();
                println!("Consumer finished consume: Received {}", item);
                thread::sleep(Duration::from_millis(300)); // 模拟消费耗时
            }
        });

        producer_handle.join().unwrap();
        consumer_handle.join().unwrap();

        println!("Main: All threads finished.");
    }

    ```

#### 2.2.3. 线程池模式 (Thread Pool)

- **定义**: 预先创建一组线程，并将任务提交给线程池。线程池管理线程的生命周期，复用线程来执行任务，避免了频繁创建和销毁线程的开销。
- **解释**: 提高处理大量短生命周期任务的效率和性能。通常包含一个任务队列和一组工作线程。
- **Rust 示例 (使用 `rayon` crate - 推荐)**:

    ```rust
    // 使用 rayon 非常简单
    use rayon::prelude::*;
    use std::time::Instant;

    fn fibonacci(n: u32) -> u64 {
        if n <= 1 { return n as u64; }
        // 递归计算，非常耗时
        fibonacci(n - 1) + fibonacci(n - 2)
    }

    fn main() {
        let numbers: Vec<u32> = (30..=40).collect(); // 一系列需要计算的任务

        // --- 串行计算 ---
        println!("Calculating Fibonacci numbers serially...");
        let start_serial = Instant::now();
        let serial_results: Vec<u64> = numbers.iter().map(|&n| fibonacci(n)).collect();
        let duration_serial = start_serial.elapsed();
        println!("Serial results: {:?}", serial_results);
        println!("Serial execution time: {:?}", duration_serial);


        // --- 使用 Rayon 并行计算 ---
        println!("\nCalculating Fibonacci numbers in parallel using Rayon...");
        let start_parallel = Instant::now();
        // 只需将 .iter() 替换为 .par_iter()
        let parallel_results: Vec<u64> = numbers.par_iter().map(|&n| fibonacci(n)).collect();
        let duration_parallel = start_parallel.elapsed();
        println!("Parallel results: {:?}", parallel_results);
        println!("Parallel execution time: {:?}", duration_parallel);


        // 也可以手动配置线程池 (虽然通常不需要)
        let pool = rayon::ThreadPoolBuilder::new()
            .num_threads(4) // 设置线程数量
            .build()
            .unwrap();

        println!("\nCalculating using custom Rayon pool (4 threads)...");
        let start_custom_pool = Instant::now();
        let custom_pool_results = pool.install(|| {
            numbers.par_iter().map(|&n| fibonacci(n)).collect::<Vec<u64>>()
        });
        let duration_custom_pool = start_custom_pool.elapsed();
         println!("Custom pool results: {:?}", custom_pool_results);
         println!("Custom pool execution time: {:?}", duration_custom_pool);

    }
    ```

    **手动实现简易线程池 (概念示例)**:

    ```rust
    use std::sync::{mpsc, Arc, Mutex};
    use std::thread;

    // 任务类型，这里使用闭包
    type Job = Box<dyn FnOnce() + Send + 'static>;

    enum Message {
        NewJob(Job),
        Terminate, // 终止信号
    }

    struct Worker {
        id: usize,
        thread: Option<thread::JoinHandle<()>>, // 使用 Option 允许 take
    }

    impl Worker {
        fn new(id: usize, receiver: Arc<Mutex<mpsc::Receiver<Message>>>) -> Worker {
            let thread = thread::spawn(move || loop {
                println!("Worker {}: Waiting for job.", id);
                // 从共享接收器获取消息，需要加锁
                let message = receiver.lock().unwrap().recv().unwrap();
                 println!("Worker {}: Received message.", id);

                match message {
                    Message::NewJob(job) => {
                        println!("Worker {}: Executing job.", id);
                        job(); // 执行任务
                         println!("Worker {}: Finished job.", id);
                    }
                    Message::Terminate => {
                         println!("Worker {}: Terminating.", id);
                        break; // 收到终止信号，退出循环
                    }
                }
            });

            Worker { id, thread: Some(thread) }
        }
    }

    struct ThreadPool {
        workers: Vec<Worker>,
        sender: mpsc::Sender<Message>, // 发送任务和终止信号
    }

    impl ThreadPool {
        fn new(size: usize) -> ThreadPool {
            assert!(size > 0);

            let (sender, receiver) = mpsc::channel();
            let receiver = Arc::new(Mutex::new(receiver)); // 包装以便共享给多个 worker

            let mut workers = Vec::with_capacity(size);
            for id in 0..size {
                workers.push(Worker::new(id, Arc::clone(&receiver)));
            }

            ThreadPool { workers, sender }
        }

        // 提交任务到线程池
        fn execute<F>(&self, f: F)
        where
            F: FnOnce() + Send + 'static,
        {
            let job = Box::new(f);
            self.sender.send(Message::NewJob(job)).unwrap();
        }
    }

    // 实现 Drop trait 以确保线程池关闭时能正确清理
    impl Drop for ThreadPool {
        fn drop(&mut self) {
             println!("ThreadPool: Sending terminate message to all workers.");
            // 发送终止信号给所有 worker
            for _ in &self.workers {
                self.sender.send(Message::Terminate).unwrap();
            }

             println!("ThreadPool: Shutting down workers.");
            // 等待所有 worker 线程结束
            for worker in &mut self.workers {
                 println!("ThreadPool: Shutting down worker {}", worker.id);
                if let Some(thread) = worker.thread.take() { // take 出 JoinHandle
                    thread.join().unwrap();
                    println!("ThreadPool: Worker {} shut down.", worker.id);
                }
            }
            println!("ThreadPool: All workers shut down.");
        }
    }


    fn main() {
        let pool = ThreadPool::new(4); // 创建一个有 4 个线程的池

        for i in 0..8 {
            pool.execute(move || {
                println!("Task {} starting.", i);
                thread::sleep(std::time::Duration::from_secs(1));
                println!("Task {} finished.", i);
            });
        }

        println!("Main: All tasks submitted. Waiting for pool to finish...");
        // 当 pool 离开作用域时，它的 Drop 实现会被调用，
        // 发送 Terminate 信号并等待所有 worker 退出。
        // 这里可以显式调用 drop(pool) 或等待 main 结束。
         println!("Main: Explicitly dropping the pool.");
         drop(pool); // 触发清理流程
         println!("Main: Pool dropped, program finished.");
    }

    ```

#### 2.2.4. 生产者-消费者模式 (Producer-Consumer)

- **定义**: 生产者线程负责创建数据（任务），并将其放入共享缓冲区；消费者线程从缓冲区取出数据并处理。缓冲区起到了解耦生产者和消费者的作用，平衡两者速度差异。
- **解释**: 广泛用于任务分发、数据流处理等场景。关键在于使用线程安全的队列（如 `std::sync::mpsc::channel` 或 `crossbeam_channel`）作为缓冲区。
- **Rust 示例 (使用 `std::sync::mpsc`)**:

    ```rust
    use std::sync::mpsc; // Multi-producer, single-consumer channel
    use std::thread;
    use std::time::Duration;

    fn main() {
        // 创建一个 MPSC 通道，缓冲区大小是默认的 (或指定大小)
        // tx (transmitter) 是发送端，可以克隆给多个生产者
        // rx (receiver) 是接收端，只有一个消费者
        let (tx, rx) = mpsc::channel();

        // --- 启动生产者线程 ---
        let producer_count = 3;
        for i in 0..producer_count {
            let tx_clone = tx.clone(); // 克隆发送端给每个生产者
            thread::spawn(move || {
                 for j in 0..5 { // 每个生产者生产 5 条消息
                     let message = format!("Producer {} message {}", i, j);
                     println!("Producer {}: Sending '{}'", i, message);
                     tx_clone.send(message).unwrap(); // 发送消息
                     thread::sleep(Duration::from_millis(100 + i * 50)); // 模拟不同生产速度
                 }
                 println!("Producer {}: Finished sending.", i);
                 // 当 tx_clone 离开作用域时，通道的发送端引用计数减 1
                 // 当所有发送端都被 drop 后，接收端的 recv() 会返回 Err
            });
        }

        // --- 在主线程或单独线程中启动消费者 ---
        // Drop the original tx so the receiver knows when all producers are done
        drop(tx);

        println!("Consumer: Waiting for messages...");
        // 消费者循环接收消息，直到通道关闭 (所有 tx 都被 drop)
        // rx.iter() 会阻塞直到有消息或通道关闭
        for received_message in rx {
            println!("Consumer: Received: '{}'", received_message);
            thread::sleep(Duration::from_millis(200)); // 模拟消费耗时
        }

        // 或者使用 loop 和 recv()
        // loop {
        //     match rx.recv() {
        //         Ok(message) => {
        //             println!("Consumer: Received: '{}'", message);
        //             thread::sleep(Duration::from_millis(200));
        //         }
        //         Err(_) => {
        //              println!("Consumer: Channel closed, no more messages.");
        //             break; // 所有发送者已退出
        //         }
        //     }
        // }

        println!("Consumer: Finished receiving.");
        // 注意：我们没有 join 生产者线程，它们可能仍在运行一小段时间，
        // 但由于 tx 已 drop，它们发送的消息不会被接收。
        // 在实际应用中，可能需要 join 线程或使用其他同步机制。
    }

    // 如果需要多消费者，可以使用 crossbeam_channel 或 Arc<Mutex<Receiver>> (效率较低)
    ```

#### 2.2.5. 读写锁模式 (Readers-Writer Lock)

- **定义**: 一种比互斥锁更优化的锁机制，允许多个线程同时读取共享资源，但在任何时候只允许一个线程写入共享资源。读取和写入是互斥的，写入和写入也是互斥的。
- **解释**: 适用于读操作远多于写操作的场景，可以提高并发度。Rust 标准库提供了 `std::sync::RwLock<T>`。
- **Rust 示例 (`std::sync::RwLock`)**:

    ```rust
    use std::sync::{Arc, RwLock};
    use std::thread;
    use std::time::Duration;

    fn main() {
        // 创建一个被 RwLock 保护的数据，并用 Arc 共享
        let shared_data = Arc::new(RwLock::new(0));

        let mut reader_handles = vec![];
        let mut writer_handles = vec![];

        // --- 创建多个读取者线程 ---
        for i in 0..5 {
            let data_clone = Arc::clone(&shared_data);
            let handle = thread::spawn(move || {
                 println!("Reader {}: Trying to acquire read lock...", i);
                 // 获取读锁 (可以多个读取者同时持有)
                let read_guard = data_clone.read().unwrap();
                 println!("Reader {}: Acquired read lock. Value = {}", i, *read_guard);
                // 模拟读取操作
                thread::sleep(Duration::from_millis(500));
                 println!("Reader {}: Releasing read lock.", i);
                 // 读锁在 read_guard 离开作用域时自动释放
            });
            reader_handles.push(handle);
        }

        // --- 创建少量写入者线程 ---
        for i in 0..2 {
            let data_clone = Arc::clone(&shared_data);
            let handle = thread::spawn(move || {
                thread::sleep(Duration::from_millis(100 * i as u64)); // 错开写入时间
                 println!("Writer {}: Trying to acquire write lock...", i);
                // 获取写锁 (独占访问)
                let mut write_guard = data_clone.write().unwrap();
                 println!("Writer {}: Acquired write lock. Current value = {}", i, *write_guard);
                // 修改数据
                *write_guard += 1;
                println!("Writer {}: Incremented value to {}", i, *write_guard);
                // 模拟写入操作
                thread::sleep(Duration::from_millis(300));
                println!("Writer {}: Releasing write lock.", i);
                // 写锁在 write_guard 离开作用域时自动释放
            });
            writer_handles.push(handle);
        }

        // 等待所有线程完成
        for handle in reader_handles {
            handle.join().unwrap();
        }
         for handle in writer_handles {
            handle.join().unwrap();
        }

        // 检查最终结果
        let final_value = *shared_data.read().unwrap();
        println!("\nMain: All threads finished. Final value = {}", final_value); // 应该是 2
    }

    ```

#### 2.2.6. Future/Promise 模式

- **定义**: Future 代表一个异步操作的最终结果，Promise 是用于设置 Future 结果的对象。当异步操作启动时，它返回一个 Future，调用者可以稍后查询 Future 的状态或等待其完成。
- **解释**: 这是现代异步编程的核心。Rust 的 `async/await` 语法和 `std::future::Future` trait 就是这种模式的实现。`async fn` 返回一个实现了 `Future` 的匿名类型。异步运行时（如 `tokio`, `async-std`）负责调度和执行这些 Future。
- **Rust 示例 (`async/await`)**:

    ```rust
    use tokio::time::{sleep, Duration};

    // 一个模拟耗时计算的 async 函数，返回一个 Future<Output = i32>
    async fn compute_something(input: i32) -> i32 {
        println!("Compute: Starting computation for {}...", input);
        sleep(Duration::from_secs(1)).await; // 模拟 IO 或计算耗时
        let result = input * 2;
        println!("Compute: Finished computation for {}. Result: {}", input, result);
        result
    }

    // 另一个 async 函数，调用 compute_something
    async fn run_computations() {
        println!("Run: Starting multiple computations concurrently...");

        // 调用 async 函数会立即返回一个 Future，并不会立即执行
        let future1 = compute_something(5);
        let future2 = compute_something(10);

        println!("Run: Futures created. Now awaiting results...");

        // 使用 .await 来等待 Future 完成并获取结果
        // 这会暂停当前 async 函数的执行，让出控制权给运行时，
        // 运行时可以去执行其他准备好的 Future。
        let result1 = future1.await;
        println!("Run: Got result 1: {}", result1);

        let result2 = future2.await;
        println!("Run: Got result 2: {}", result2);

        println!("Run: All computations finished.");
    }

     // 使用 tokio::join! 或 futures::join! 可以并发执行多个 Future
     async fn run_computations_concurrently() {
         println!("RunConcurrent: Starting multiple computations concurrently using join!...");

         let future1 = compute_something(7);
         let future2 = compute_something(8);
         let future3 = async { // 也可以直接创建 async 块
             println!("Compute: Starting immediate async block...");
             sleep(Duration::from_millis(500)).await;
             println!("Compute: Finished immediate async block.");
             42 // 返回值
         };

         // join! 会同时驱动这三个 Future，直到它们全部完成
         let (result1, result2, result3) = tokio::join!(future1, future2, future3);

         println!("RunConcurrent: Got results: {}, {}, {}", result1, result2, result3);
         println!("RunConcurrent: All concurrent computations finished.");
     }


    #[tokio::main] // 使用 tokio 运行时来执行 async main
    async fn main() {
        println!("Main: Starting sequential await example...");
        run_computations().await; // 等待 run_computations 完成

        println!("\nMain: Starting concurrent join example...");
        run_computations_concurrently().await; // 等待 run_computations_concurrently 完成

        println!("\nMain: Finished.");
    }
    ```

#### 2.2.7. Actor 模型

- **定义**: 一种并发计算模型，其中“Actor”是计算的基本单元。Actor 接收消息并基于消息执行计算、创建更多 Actor、向其他 Actor 发送消息、改变自己的状态。Actor 之间不共享内存，通过异步消息传递进行通信，每个 Actor 独立处理自己的状态。
- **解释**: 非常适合构建高并发、分布式、容错的系统。每个 Actor 都有一个邮箱（Mailbox）来接收消息，并按顺序处理它们。常见的 Rust Actor 框架有 `actix`, `bastion`，也可以用 `tokio` 的 task 和 channel 手动实现简化的 Actor。
- **Rust 示例 (使用 `actix` - 简化概念)**:

  - 注意: Actix 是一个功能丰富的框架，这里的示例仅展示核心概念。需要添加 `actix = "0.13"` 依赖。

    ```rust
    use actix::prelude::*;
    use std::time::Duration;

    // --- 定义 Actor ---
    struct MyActor {
        count: usize,
    }

    // 实现 Actor trait
    impl Actor for MyActor {
        type Context = Context<Self>; // 定义 Actor 的运行上下文

        fn started(&mut self, _ctx: &mut Self::Context) {
             println!("Actor is alive!");
        }

        fn stopped(&mut self) {
            println!("Actor is stopped. Final count: {}", self.count);
        }
    }

    // --- 定义消息 ---
    #[derive(Message)] // 使用宏自动实现 Message trait
    #[rtype(result = "usize")] // 定义消息处理后的返回值类型
    struct Ping(usize); // 消息可以携带数据

    struct Increment;
    impl Message for Increment {
         type Result = (); // 没有返回值
    }

    struct GetData;
    impl Message for GetData {
         type Result = usize; // 返回当前计数值
    }

    // --- 定义消息处理器 ---
    // 为 MyActor 实现 Handler<Ping>
    impl Handler<Ping> for MyActor {
        type Result = usize; // 返回类型必须与消息定义中的 rtype 匹配

        fn handle(&mut self, msg: Ping, _ctx: &mut Context<Self>) -> Self::Result {
            println!("Actor received Ping({})!", msg.0);
            self.count += msg.0;
            self.count // 返回当前的计数值
        }
    }

    // 为 MyActor 实现 Handler<Increment>
    impl Handler<Increment> for MyActor {
         type Result = ();

         fn handle(&mut self, _msg: Increment, _ctx: &mut Context<Self>) -> Self::Result {
             println!("Actor received Increment.");
             self.count += 1;
         }
    }

     // 为 MyActor 实现 Handler<GetData>
     impl Handler<GetData> for MyActor {
         type Result = usize;

         fn handle(&mut self, _msg: GetData, _ctx: &mut Context<Self>) -> Self::Result {
             println!("Actor received GetData request.");
             self.count
         }
     }


    #[actix::main] // 使用 actix 运行时
    async fn main() {
        // 启动 Actor，返回一个地址 (Addr) 用于向 Actor 发送消息
        let addr = MyActor { count: 10 }.start();

        // --- 发送消息 ---
        // 1. 使用 `send` 发送消息并等待响应 (返回 Future)
        println!("Main: Sending Ping(5)...");
        let res = addr.send(Ping(5)).await;
        match res {
             Ok(count_after_ping) => println!("Main: Got Ping result: {}", count_after_ping), // 应该输出 15
             Err(e) => println!("Main: Failed to send Ping: {}", e),
        }


        // 2. 使用 `do_send` 发送消息，不等待响应 (fire and forget)
        println!("Main: Sending Increment (do_send)...");
        addr.do_send(Increment);
        addr.do_send(Increment);


        // 等待一点时间让 do_send 的消息被处理 (实际应用中应避免随意 sleep)
        actix_rt::time::sleep(Duration::from_millis(50)).await;


        // 3. 再次发送需要响应的消息
        println!("Main: Sending GetData...");
        let current_count = addr.send(GetData).await.unwrap();
        println!("Main: Got current count: {}", current_count); // 应该输出 17 (15 + 1 + 1)


        // 优雅地停止 Actor (可选)
        println!("Main: Stopping actor system.");
        System::current().stop(); // 请求系统停止，会调用 Actor 的 stopped 方法
    }

    ```

---

## 3. 分布式设计模式

### 3.1. 概念与定义

分布式系统是由多台计算机（节点）通过网络连接，协同工作以完成共同任务的系统。分布式设计模式专注于解决在分布式环境中遇到的挑战，如网络延迟、节点故障、数据一致性、可伸缩性、服务发现等问题。CAP 定理（一致性 Consistency, 可用性 Availability, 分区容错性 Partition tolerance）是理解分布式系统设计权衡的基础。

### 3.2. 常见模式

#### 3.2.1. 服务发现 (Service Discovery)

- **定义**: 在分布式系统中，自动检测网络中的服务实例（IP 地址和端口）的过程。
- **解释**: 当服务实例动态启动、停止或伸缩时，客户端或其他服务需要能够找到它们。主要有两种模式：
  - **客户端发现**: 客户端查询服务注册表（如 Consul, etcd, Zookeeper）以获取服务实例列表，并自行选择一个进行连接（通常需要负载均衡逻辑）。
  - **服务端发现**: 客户端向一个路由器或负载均衡器发送请求，该路由器查询服务注册表并将请求转发到合适的服务实例。API 网关通常扮演此角色。
- **Rust 示例 (概念性，使用 Consul 客户端库)**:
  - 实际代码需要添加 Consul 客户端库依赖，如 `consulrs`。并需要运行 Consul 服务。

    ```rust
    // 概念性示例，需要 consulrs crate 和运行中的 Consul agent
    // use consulrs::{client::{ConsulClient, ConsulClientSettingsBuilder},kv, health, agent};
    // use std::time::Duration;

    async fn register_service(client: &impl consulrs::client::Client, service_id: &str, service_name: &str, address: &str, port: u16) -> Result<(), Box<dyn std::error::Error>> {
        // println!("Registering service '{}' ({}) at {}:{}", service_name, service_id, address, port);
        // let registration = agent::AgentServiceRegistrationBuilder::default()
        //     .id(service_id)
        //     .name(service_name)
        //     .address(address)
        //     .port(port as i32) // 注意类型转换
        //     .check( // 添加健康检查 (可选但推荐)
        //         agent::AgentServiceCheckBuilder::default()
        //             .name(format!("{}_check", service_name))
        //             .tcp(format!("{}:{}", address, port)) // TCP 健康检查
        //             .interval("10s")
        //             .timeout("1s")
        //             .deregister("30s") // 失败后 30 秒自动注销
        //             .build()?
        //     )
        //     .build()?;
        //
        // client.register_service(&registration, None).await?;
        // println!("Service registered successfully.");
        println!("Conceptual: Registering {} ({}) at {}:{}", service_name, service_id, address, port);
        // ... 实际调用 Consul API ...
        Ok(())
    }

    async fn discover_service(client: &impl consulrs::client::Client, service_name: &str) -> Result<Vec<(String, u16)>, Box<dyn std::error::Error>> {
        // println!("Discovering healthy instances of service '{}'...", service_name);
        // // 查询健康的服务实例
        // let (instances, _meta) = client.service_health(service_name, None, Some(true), None).await?;
        //
        // let mut addresses = Vec::new();
        // for instance in instances {
        //     if let Some(service) = instance.service {
        //         println!(" Found healthy instance: ID={}, Address={}, Port={}", service.id.unwrap_or_default(), service.address.unwrap_or_default(), service.port.unwrap_or_default());
        //          addresses.push((service.address.unwrap_or_default(), service.port.unwrap_or(0) as u16));
        //     }
        // }
        // Ok(addresses)
        println!("Conceptual: Discovering healthy instances of '{}'", service_name);
        // ... 实际调用 Consul API ...
        // 模拟返回结果
        Ok(vec![("192.168.1.100".to_string(), 8080), ("192.168.1.101".to_string(), 8080)])
    }

    // #[tokio::main]
    async fn conceptual_main() {
        // // 创建 Consul 客户端 (假设 Consul agent 在本地运行)
        // let settings = ConsulClientSettingsBuilder::default()
        //     .address("http://127.0.0.1:8500")
        //     .build()
        //     .unwrap();
        // let client = ConsulClient::new(settings).unwrap();

        // 模拟一个虚拟客户端对象
        struct MockConsulClient;
        impl consulrs::client::Client for MockConsulClient {} // 实现空 trait 以匹配函数签名

        let client = MockConsulClient;


        // 模拟服务 A 注册自己
        let service_a_id = "user-service-instance-1";
        if let Err(e) = register_service(&client, service_a_id, "user-service", "192.168.1.100", 8080).await {
            eprintln!("Failed to register service A: {}", e);
        }
         // 模拟服务 B 注册自己
        let service_b_id = "product-service-instance-1";
         if let Err(e) = register_service(&client, service_b_id, "product-service", "192.168.1.105", 9000).await {
             eprintln!("Failed to register service B: {}", e);
         }
         // 模拟服务 A 的另一个实例注册
          let service_a2_id = "user-service-instance-2";
          if let Err(e) = register_service(&client, service_a2_id, "user-service", "192.168.1.101", 8080).await {
              eprintln!("Failed to register service A2: {}", e);
          }

        println!("\nSimulating discovery...");
        // 模拟一个客户端或网关发现 user-service
        match discover_service(&client, "user-service").await {
            Ok(addresses) => {
                println!("Discovered user-service instances:");
                for (addr, port) in addresses {
                    println!(" - {}:{}", addr, port);
                    // 客户端可以选择一个地址进行连接 (需要负载均衡策略)
                }
            }
            Err(e) => eprintln!("Failed to discover user-service: {}", e),
        }

        // 模拟注销服务 (可选，Consul 健康检查可以自动处理)
        // println!("\nSimulating deregistration...");
        // if let Err(e) = client.deregister_service(service_a_id, None).await {
        //     eprintln!("Failed to deregister service {}: {}", service_a_id, e);
        // }
    }

    fn main() {
        // 由于无法实际运行 Consul，这里仅打印概念
        println!("--- Service Discovery Conceptual Example ---");
        // 在实际环境中，需要 tokio 运行时
        // tokio::runtime::Runtime::new().unwrap().block_on(conceptual_main());
         async { conceptual_main().await }; // 创建一个不会执行的 async 块
        println!("--- End of Conceptual Example ---");
    }
    ```

#### 3.2.2. 熔断器模式 (Circuit Breaker)

- **定义**: 一种用于处理远程服务调用故障的模式。它像电路熔断器一样，监控故障次数，当故障达到阈值时，“断开”电路，阻止后续调用，并在一段时间后尝试恢复。
- **解释**: 防止一个服务的故障导致级联故障。熔断器有三种状态：
  - **Closed (闭合)**: 正常状态，允许请求通过。如果请求失败次数超过阈值，则切换到 Open 状态。
  - **Open (断开)**: 请求直接失败（或返回缓存/默认值），不访问下游服务。经过一段超时时间后，切换到 Half-Open 状态。
  - **Half-Open (半开)**: 允许少量测试请求通过。如果成功，则切换回 Closed 状态；如果失败，则重新切换回 Open 状态，并重置超时计时器。
- **Rust 示例 (简易实现)**:

    ```rust
    use std::time::{Duration, Instant};
    use std::sync::{Mutex, Arc};

    #[derive(Debug, Clone, Copy, PartialEq)]
    enum CircuitBreakerState {
        Closed,
        Open,
        HalfOpen,
    }

    struct StateStore {
        state: CircuitBreakerState,
        failures: u32,
        last_failure_time: Option<Instant>,
        opened_at: Option<Instant>,
    }

    #[derive(Clone)] // 允许克隆熔断器实例共享状态
    struct CircuitBreaker {
        // 使用 Arc<Mutex<>> 共享可变状态
        store: Arc<Mutex<StateStore>>,
        failure_threshold: u32,       // 失败阈值
        reset_timeout: Duration,     // Open 状态持续时间
        half_open_attempts: u32,     // Half-Open 状态允许的尝试次数 (这里简化，只允许一次)
    }

    impl CircuitBreaker {
        fn new(failure_threshold: u32, reset_timeout: Duration) -> Self {
            CircuitBreaker {
                store: Arc::new(Mutex::new(StateStore {
                    state: CircuitBreakerState::Closed,
                    failures: 0,
                    last_failure_time: None, // 优化：可以用于判断短时间内的连续失败
                    opened_at: None,
                })),
                failure_threshold,
                reset_timeout,
                half_open_attempts: 1, // 简化为 1 次
            }
        }

        // 包装需要保护的操作
        fn execute<F, T, E>(&self, operation: F) -> Result<T, CircuitBreakerError<E>>
        where
            F: FnOnce() -> Result<T, E>, // 操作返回 Result
        {
            let mut store = self.store.lock().unwrap(); // 获取状态锁

            match store.state {
                CircuitBreakerState::Closed => {
                    drop(store); // 提前释放锁，允许操作执行
                    match operation() {
                        Ok(result) => {
                            // 操作成功，重置失败计数
                            self.record_success();
                            Ok(result)
                        }
                        Err(error) => {
                            // 操作失败，记录失败并可能跳闸
                            self.record_failure();
                            Err(CircuitBreakerError::Inner(error)) // 返回原始错误
                        }
                    }
                }
                CircuitBreakerState::Open => {
                    // 检查是否过了重置超时时间
                    if let Some(opened_at) = store.opened_at {
                        if opened_at.elapsed() >= self.reset_timeout {
                            println!("CircuitBreaker: Timeout expired, transitioning to HalfOpen.");
                            store.state = CircuitBreakerState::HalfOpen;
                             store.failures = 0; // 重置失败计数，准备尝试
                            drop(store); // 释放锁
                            // 第一次进入 HalfOpen，允许执行
                            self.execute_half_open(operation)
                        } else {
                            println!("CircuitBreaker: Circuit is Open. Rejecting request.");
                            Err(CircuitBreakerError::Open) // 熔断器打开，直接拒绝
                        }
                    } else {
                         // opened_at 不应该为 None 在 Open 状态，视为错误
                         eprintln!("CircuitBreaker: Invalid state - Open without opened_at time.");
                         Err(CircuitBreakerError::Open)
                    }
                }
                CircuitBreakerState::HalfOpen => {
                     drop(store); // 释放锁
                    // 在 HalfOpen 状态下执行操作
                     self.execute_half_open(operation)
                }
            }
        }

        // HalfOpen 状态下的执行逻辑
        fn execute_half_open<F, T, E>(&self, operation: F) -> Result<T, CircuitBreakerError<E>>
        where
            F: FnOnce() -> Result<T, E>,
        {
             println!("CircuitBreaker: Executing in HalfOpen state...");
            match operation() {
                Ok(result) => {
                    // HalfOpen 成功，关闭熔断器
                    println!("CircuitBreaker: HalfOpen attempt succeeded. Transitioning to Closed.");
                    self.reset(); // 重置状态到 Closed
                    Ok(result)
                }
                Err(error) => {
                    // HalfOpen 失败，重新打开熔断器
                     println!("CircuitBreaker: HalfOpen attempt failed. Transitioning back to Open.");
                    self.trip(); // 跳闸到 Open
                    Err(CircuitBreakerError::Inner(error))
                }
            }
        }


        // 记录成功
        fn record_success(&self) {
             let mut store = self.store.lock().unwrap();
             if store.state == CircuitBreakerState::Closed && store.failures > 0 {
                println!("CircuitBreaker: Recorded success, resetting failure count.");
                store.failures = 0;
                store.last_failure_time = None;
             }
             // HalfOpen 状态的成功在 execute_half_open 中处理 (调用 reset)
        }

        // 记录失败
        fn record_failure(&self) {
            let mut store = self.store.lock().unwrap();
            if store.state == CircuitBreakerState::Closed {
                store.failures += 1;
                store.last_failure_time = Some(Instant::now());
                 println!("CircuitBreaker: Recorded failure. Count: {}/{}", store.failures, self.failure_threshold);
                if store.failures >= self.failure_threshold {
                    drop(store); // 释放锁，调用 trip
                    self.trip();
                }
            }
             // HalfOpen 状态的失败在 execute_half_open 中处理 (调用 trip)
        }

        // 跳闸 (进入 Open 状态)
        fn trip(&self) {
            let mut store = self.store.lock().unwrap();
             if store.state != CircuitBreakerState::Open {
                 println!("CircuitBreaker: Tripping! Transitioning to Open state.");
                 store.state = CircuitBreakerState::Open;
                 store.opened_at = Some(Instant::now());
             }
        }

        // 重置 (进入 Closed 状态)
        fn reset(&self) {
             let mut store = self.store.lock().unwrap();
             if store.state != CircuitBreakerState::Closed {
                 println!("CircuitBreaker: Resetting! Transitioning to Closed state.");
                 store.state = CircuitBreakerState::Closed;
                 store.failures = 0;
                 store.last_failure_time = None;
                 store.opened_at = None;
             }
        }

        fn get_state(&self) -> CircuitBreakerState {
             self.store.lock().unwrap().state
        }
    }

    // 自定义错误类型
    #[derive(Debug)]
    enum CircuitBreakerError<E> {
        Open,        // 熔断器打开
        Inner(E),    // 包装底层操作错误
    }


    // 模拟一个可能失败的操作
    fn potentially_failing_operation(succeed: bool) -> Result<String, String> {
        if succeed {
            Ok("Operation succeeded!".to_string())
        } else {
            Err("Operation failed!".to_string())
        }
    }


    fn main() {
        let breaker = CircuitBreaker::new(3, Duration::from_secs(5)); // 失败 3 次跳闸，5 秒后尝试重置

        // 模拟连续成功
        println!("--- Phase 1: Success ---");
        for _ in 0..2 {
            match breaker.execute(|| potentially_failing_operation(true)) {
                Ok(res) => println!(" Result: {}", res),
                Err(e) => println!(" Error: {:?}", e),
            }
            println!(" Current State: {:?}", breaker.get_state()); // Closed
        }

        // 模拟连续失败导致跳闸
         println!("\n--- Phase 2: Failures leading to trip ---");
         for i in 0..4 {
             println!(" Attempt {}", i + 1);
             match breaker.execute(|| potentially_failing_operation(false)) {
                 Ok(res) => println!(" Result: {}", res),
                 Err(e) => println!(" Error: {:?}", e),
             }
              println!(" Current State: {:?}", breaker.get_state()); // Closed -> Closed -> Open -> Open
              thread::sleep(Duration::from_millis(100));
         }

         // 熔断器已打开，请求会被拒绝
         println!("\n--- Phase 3: Circuit is Open ---");
         match breaker.execute(|| potentially_failing_operation(true)) {
              Ok(res) => println!(" Result: {}", res),
              Err(e) => println!(" Error: {:?}", e), // CircuitBreakerError::Open
         }
          println!(" Current State: {:?}", breaker.get_state()); // Open


        // 等待超过重置时间
        println!("\n--- Phase 4: Waiting for reset timeout ({} seconds)... ---", breaker.reset_timeout.as_secs());
        thread::sleep(breaker.reset_timeout + Duration::from_millis(100));


        // 第一次请求进入 HalfOpen 状态
         println!("\n--- Phase 5: Attempting request in HalfOpen ---");
         // 让它失败，重新跳闸
         println!(" Attempting a failing operation in HalfOpen:");
         match breaker.execute(|| potentially_failing_operation(false)) {
             Ok(res) => println!(" Result: {}", res),
             Err(e) => println!(" Error: {:?}", e), // Inner("Operation failed!")
         }
         println!(" Current State: {:?}", breaker.get_state()); // Open (HalfOpen -> Open)

         // 再次等待超时
          println!("\n--- Phase 6: Waiting for reset timeout again... ---");
         thread::sleep(breaker.reset_timeout + Duration::from_millis(100));

        // 第二次请求进入 HalfOpen
         println!("\n--- Phase 7: Attempting successful request in HalfOpen ---");
         match breaker.execute(|| potentially_failing_operation(true)) {
              Ok(res) => println!(" Result: {}", res), // Operation succeeded!
              Err(e) => println!(" Error: {:?}", e),
         }
         println!(" Current State: {:?}", breaker.get_state()); // Closed (HalfOpen -> Closed)


         // 熔断器已关闭，恢复正常
         println!("\n--- Phase 8: Circuit is Closed again ---");
          match breaker.execute(|| potentially_failing_operation(true)) {
              Ok(res) => println!(" Result: {}", res),
              Err(e) => println!(" Error: {:?}", e),
          }
         println!(" Current State: {:?}", breaker.get_state()); // Closed

    }

    ```

#### 3.2.3. API 网关 (API Gateway)

- **定义**: 作为所有客户端请求的单一入口点，将请求路由到后端的微服务，并可能执行一些横切关注点，如认证、授权、限流、日志记录、响应转换和缓存。
- **解释**: 简化客户端与复杂微服务架构的交互，隐藏内部实现细节，提供统一的 API 接口。它是服务端发现模式的一种常见实现。
- **Rust 示例 (使用 `axum` 框架 - 概念性)**:
  - 需要添加 `axum`, `tokio`, `hyper`, `serde` 等依赖。

    ```rust
    // 概念性示例，需要 axum, tokio, hyper, serde, reqwest 等 crates
    use axum::{
        routing::{get, post}, // 修改此处导入方式
        http::{Request, StatusCode, Uri},
        response::{Response, IntoResponse},
        extract::{Path, State, Json}, // 导入 Json
        body::Body, // 导入 Body
        Router, Error, // 导入 Router 和 Error
    };
    use std::net::SocketAddr;
    use reqwest::Client; // 用于向上游服务转发请求
    use serde::{Deserialize, Serialize}; // 导入 Serde

    // 共享状态，例如 HTTP 客户端和服务地址
    #[derive(Clone)]
    struct AppState {
        http_client: Client,
        user_service_url: String,
        product_service_url: String,
    }

    // 示例：用户和产品结构体
    #[derive(Deserialize, Serialize, Debug)]
    struct User { id: u64, name: String }
    #[derive(Deserialize, Serialize, Debug)]
    struct Product { id: u64, name: String, price: f64 }
    #[derive(Deserialize, Serialize, Debug)]
    struct CreateUser { name: String }


    // --- 处理函数 ---

    // 代理到用户服务: GET /users/:id
    async fn get_user_handler(
        State(state): State<AppState>, // 注入共享状态
        Path(user_id): Path<u64>,     // 从路径提取参数
    ) -> Result<impl IntoResponse, (StatusCode, String)> { // 返回 Result
        let upstream_url = format!("{}/users/{}", state.user_service_url, user_id);
        println!("Gateway: Forwarding GET request to {}", upstream_url);

        match state.http_client.get(&upstream_url).send().await {
            Ok(response) => {
                // 检查上游服务的响应状态
                if response.status().is_success() {
                     match response.json::<User>().await {
                         Ok(user) => Ok(Json(user)), // 将获取到的 User 序列化为 JSON 返回
                         Err(e) => {
                            eprintln!("Gateway: Failed to parse JSON from user service: {}", e);
                            Err((StatusCode::INTERNAL_SERVER_ERROR, "Failed to parse upstream response".to_string()))
                         }
                     }
                } else {
                     let status = response.status();
                     let body = response.text().await.unwrap_or_else(|_| "Failed to read upstream error body".to_string());
                     eprintln!("Gateway: User service returned error: {} - {}", status, body);
                     Err((status, body)) // 将上游错误状态码和消息体透传
                }
            }
            Err(e) => {
                eprintln!("Gateway: Failed to connect to user service: {}", e);
                Err((StatusCode::SERVICE_UNAVAILABLE, format!("Failed to reach user service: {}", e)))
            }
        }
    }


     // 代理到用户服务: POST /users
     async fn create_user_handler(
         State(state): State<AppState>,
         Json(payload): Json<CreateUser>, // 从请求体解析 JSON
     ) -> Result<impl IntoResponse, (StatusCode, String)> {
         let upstream_url = format!("{}/users", state.user_service_url);
         println!("Gateway: Forwarding POST request to {}", upstream_url);

         match state.http_client.post(&upstream_url).json(&payload).send().await {
              Ok(response) => forward_response(response).await, // 使用辅助函数处理响应
              Err(e) => {
                 eprintln!("Gateway: Failed to connect to user service: {}", e);
                 Err((StatusCode::SERVICE_UNAVAILABLE, format!("Failed to reach user service: {}", e)))
             }
         }
     }


    // 代理到产品服务: GET /products/:id
    async fn get_product_handler(
        State(state): State<AppState>,
        Path(product_id): Path<u64>,
    ) -> Result<impl IntoResponse, (StatusCode, String)> {
        let upstream_url = format!("{}/products/{}", state.product_service_url, product_id);
        println!("Gateway: Forwarding GET request to {}", upstream_url);

        match state.http_client.get(&upstream_url).send().await {
            Ok(response) => forward_response(response).await,
             Err(e) => {
                 eprintln!("Gateway: Failed to connect to product service: {}", e);
                 Err((StatusCode::SERVICE_UNAVAILABLE, format!("Failed to reach product service: {}", e)))
             }
        }
    }

    // --- 辅助函数 ---
    // 通用的响应转发逻辑 (可以添加更多处理，如修改头)
    async fn forward_response(response: reqwest::Response) -> Result<impl IntoResponse, (StatusCode, String)> {
        let status = response.status();
        let headers = response.headers().clone(); // 克隆响应头
        let body_bytes = response.bytes().await.map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, format!("Failed to read upstream body: {}", e)))?;

        let mut response_builder = Response::builder().status(status);
        // 复制头信息到 axum 响应
        for (key, value) in headers.iter() {
            response_builder = response_builder.header(key, value);
        }

        let response = response_builder
            .body(Body::from(body_bytes)) // 使用 axum 的 Body
            .map_err(|e| (StatusCode::INTERNAL_SERVER_ERROR, format!("Failed to build response: {}", e)))?;

        Ok(response)
    }


    // --- 主函数 ---
    // #[tokio::main]
    async fn conceptual_gateway_main() {
        // 创建共享状态
        let shared_state = AppState {
            http_client: Client::new(),
            // 实际应用中这些地址应该来自配置或服务发现
            user_service_url: "http://localhost:8081".to_string(), // 假设用户服务地址
            product_service_url: "http://localhost:8082".to_string(), // 假设产品服务地址
        };

        // 构建路由
        let app = Router::new()
            // 用户相关路由
            .route("/users/:id", get(get_user_handler))
            .route("/users", post(create_user_handler))
            // 产品相关路由
            .route("/products/:id", get(get_product_handler))
            // 添加认证、限流等中间件 (axum 支持 tower 中间件)
            // .layer(tower_http::trace::TraceLayer::new_for_http())
            .with_state(shared_state); // 应用共享状态

        // 运行服务器
        let addr = SocketAddr::from(([127, 0, 0, 1], 3000)); // 网关监听 3000 端口
        println!("API Gateway listening on {}", addr);

        // 使用 axum::serve 启动服务器
        let listener = tokio::net::TcpListener::bind(addr).await.unwrap();
        axum::serve(listener, app).await.unwrap();
    }

     fn main() {
        println!("--- API Gateway Conceptual Example (requires running) ---");
        // 这个示例需要实际运行才能看到效果
        // tokio::runtime::Runtime::new().unwrap().block_on(conceptual_gateway_main());
        println!("--- To run, uncomment #[tokio::main] and ensure dependencies ---");
    }

    ```

#### 3.2.4. Saga 模式

- **定义**: 一种管理分布式事务（跨多个服务的数据一致性）的模式。它将一个大的全局事务分解为一系列本地事务，每个本地事务更新单个服务的数据。如果任何本地事务失败，Saga 会执行一系列补偿事务来撤销之前已成功完成的本地事务。
- **解释**: 避免了分布式两阶段提交（2PC）带来的锁定和阻塞问题，提高了可用性，但牺牲了原子性（最终一致性）。主要有两种协调方式：
  - **协同 (Choreography)**: 每个服务在完成其本地事务后发布事件，触发链中的下一个服务执行其本地事务或补偿事务。去中心化，但难以跟踪流程。
  - **编排 (Orchestration)**: 一个中央协调器（Saga Orchestrator）负责告诉每个参与者执行哪个本地事务或补偿事务。中心化，易于管理和监控流程。
- **Rust 示例 (概念性 - 编排方式)**:

    ```rust
    use serde::{Deserialize, Serialize};
    use std::fmt::Debug;

    // --- 定义 Saga 步骤和补偿步骤 ---
    trait SagaStep<Ctx, Req, CompReq>: Debug + Send + Sync {
        fn name(&self) -> &'static str;
        // 执行本地事务
        async fn execute(&self, context: &mut Ctx, request: &Req) -> Result<(), String>;
        // 执行补偿事务
        async fn compensate(&self, context: &mut Ctx, comp_request: &CompReq) -> Result<(), String>;
    }

    // --- 示例：订单创建 Saga ---
    #[derive(Debug, Clone, Serialize, Deserialize)]
    struct OrderContext {
        order_id: String,
        user_id: String,
        product_id: String,
        quantity: u32,
        payment_id: Option<String>,
        inventory_reserved: bool,
        // ... 其他状态
    }

    #[derive(Debug, Clone, Serialize, Deserialize)]
    struct CreateOrderRequest { // 用于启动 Saga
        user_id: String,
        product_id: String,
        quantity: u32,
    }

     #[derive(Debug, Clone, Serialize, Deserialize)]
     struct CompensateRequest { // 用于补偿
         order_id: String,
         reason: String,
         // 可能需要携带补偿所需的数据
         payment_id_to_refund: Option<String>,
         product_id_to_release: Option<String>,
         quantity_to_release: Option<u32>,
     }

    // 步骤 1: 创建订单 (假设在 Order Service 中)
    #[derive(Debug)]
    struct CreateOrderStep;
    impl SagaStep<OrderContext, CreateOrderRequest, CompensateRequest> for CreateOrderStep {
        fn name(&self) -> &'static str { "CreateOrder" }
        async fn execute(&self, context: &mut OrderContext, request: &CreateOrderRequest) -> Result<(), String> {
             println!("Executing Step [{}]: Creating order record for user {}, product {}, quantity {}",
                 self.name(), request.user_id, request.product_id, request.quantity);
            // 模拟数据库操作
            context.order_id = format!("order_{}", rand::random::<u16>()); // 生成伪订单 ID
            context.user_id = request.user_id.clone();
            context.product_id = request.product_id.clone();
            context.quantity = request.quantity;
            println!(" -> Order created with ID: {}", context.order_id);
            Ok(())
        }
         async fn compensate(&self, context: &mut OrderContext, comp_request: &CompReq) -> Result<(), String> {
             println!("Compensating Step [{}]: Marking order {} as cancelled. Reason: {}",
                 self.name(), context.order_id, comp_request.reason);
             // 模拟更新订单状态为 Cancelled
             Ok(())
         }
    }


    // 步骤 2: 处理支付 (假设在 Payment Service 中)
    #[derive(Debug)]
    struct ProcessPaymentStep { should_fail: bool } // 用于测试失败场景
    impl SagaStep<OrderContext, CreateOrderRequest, CompensateRequest> for ProcessPaymentStep {
         fn name(&self) -> &'static str { "ProcessPayment" }
         async fn execute(&self, context: &mut OrderContext, _request: &CreateOrderRequest) -> Result<(), String> {
              println!("Executing Step [{}]: Processing payment for order {}", self.name(), context.order_id);
             if self.should_fail {
                 println!(" -> Payment Failed (simulated).");
                 return Err("Simulated payment failure".to_string());
             }
             // 模拟调用支付网关
             context.payment_id = Some(format!("payment_{}", rand::random::<u16>()));
              println!(" -> Payment successful. Payment ID: {}", context.payment_id.as_ref().unwrap());
             Ok(())
         }
         async fn compensate(&self, context: &mut OrderContext, comp_request: &CompReq) -> Result<(), String> {
             if let Some(payment_id) = &comp_request.payment_id_to_refund { // 使用 comp_request 中的数据
                 println!("Compensating Step [{}]: Refunding payment {} for order {}. Reason: {}",
                     self.name(), payment_id, context.order_id, comp_request.reason);
                 // 模拟调用支付网关进行退款
                 context.payment_id = None; // 清除支付 ID
             } else {
                  println!("Compensating Step [{}]: No payment to refund for order {}.", self.name(), context.order_id);
             }
             Ok(())
         }
    }


    // 步骤 3: 预留库存 (假设在 Inventory Service 中)
    #[derive(Debug)]
    struct ReserveInventoryStep;
    impl SagaStep<OrderContext, CreateOrderRequest, CompensateRequest> for ReserveInventoryStep {
         fn name(&self) -> &'static str { "ReserveInventory" }
         async fn execute(&self, context: &mut OrderContext, _request: &CreateOrderRequest) -> Result<(), String> {
              println!("Executing Step [{}]: Reserving inventory for product {} (qty {}), order {}",
                 self.name(), context.product_id, context.quantity, context.order_id);
             // 模拟检查并减少库存
             context.inventory_reserved = true;
             println!(" -> Inventory reserved successfully.");
             Ok(())
         }
         async fn compensate(&self, context: &mut OrderContext, comp_request: &CompReq) -> Result<(), String> {
            if let (Some(product_id), Some(quantity)) = (&comp_request.product_id_to_release, comp_request.quantity_to_release) {
                if context.inventory_reserved {
                    println!("Compensating Step [{}]: Releasing inventory for product {} (qty {}), order {}. Reason: {}",
                        self.name(), product_id, quantity, context.order_id, comp_request.reason);
                    // 模拟增加库存
                    context.inventory_reserved = false;
                } else {
                     println!("Compensating Step [{}]: Inventory was not reserved for order {}.", self.name(), context.order_id);
                }
            } else {
                 println!("Compensating Step [{}]: Missing data to release inventory for order {}.", self.name(), context.order_id);
            }
             Ok(())
         }
    }

    // --- Saga Orchestrator ---
    struct SagaOrchestrator<Ctx, Req, CompReq> {
        // 使用 Arc 使步骤可以在 async 块中共享
        steps: Vec<Arc<dyn SagaStep<Ctx, Req, CompReq>>>,
    }

    impl<Ctx, Req, CompReq> SagaOrchestrator<Ctx, Req, CompReq>
    where
        Ctx: Default + Debug + Clone + Send + 'static, // 上下文需要 Clone 来创建补偿请求
        Req: Send + Sync + 'static,
        CompReq: From<(String, Ctx)> + Send + Sync + 'static, // 能够从失败原因和上下文创建补偿请求
    {
        fn new(steps: Vec<Arc<dyn SagaStep<Ctx, Req, CompReq>>>) -> Self {
            SagaOrchestrator { steps }
        }

        async fn run(&self, initial_request: Req) -> Result<Ctx, (String, Ctx)> {
            let mut context = Ctx::default();
            let mut completed_steps: Vec<usize> = Vec::new(); // 记录成功完成的步骤索引

            for (index, step) in self.steps.iter().enumerate() {
                let step_name = step.name();
                 println!("Orchestrator: Executing step {} [{}]", index, step_name);
                match step.execute(&mut context, &initial_request).await {
                    Ok(_) => {
                        println!("Orchestrator: Step {} [{}] completed successfully.", index, step_name);
                        completed_steps.push(index);
                    }
                    Err(error_msg) => {
                        eprintln!("Orchestrator: Step {} [{}] failed: {}", index, step_name, error_msg);
                        // 触发补偿流程
                        self.compensate(completed_steps, &mut context, error_msg.clone()).await;
                        return Err((format!("Saga failed at step {}: {}", step_name, error_msg), context));
                    }
                }
            }

             println!("Orchestrator: Saga completed successfully.");
            Ok(context) // 所有步骤成功
        }

        async fn compensate(&self, completed_steps_indices: Vec<usize>, context: &mut Ctx, reason: String) {
             println!("Orchestrator: Starting compensation process. Reason: {}", reason);
            // 从上下文和原因创建补偿请求
            let comp_request: CompReq = CompReq::from((reason.clone(), context.clone()));

            // 按相反顺序执行已完成步骤的补偿操作
            for &index in completed_steps_indices.iter().rev() {
                let step = &self.steps[index];
                let step_name = step.name();
                println!("Orchestrator: Compensating step {} [{}]", index, step_name);
                match step.compensate(context, &comp_request).await {
                    Ok(_) => println!("Orchestrator: Compensation for step {} [{}] succeeded.", index, step_name),
                    Err(comp_err) => {
                        // 补偿失败通常需要记录日志并手动干预
                         eprintln!("Orchestrator: CRITICAL - Compensation for step {} [{}] failed: {}. Manual intervention required.", index, step_name, comp_err);
                        // 可以选择继续补偿其他步骤或停止
                    }
                }
            }
            println!("Orchestrator: Compensation process finished.");
        }
    }

     // 实现 From trait 用于从失败原因和上下文创建补偿请求
     impl From<(String, OrderContext)> for CompensateRequest {
         fn from((reason, context): (String, OrderContext)) -> Self {
             CompensateRequest {
                 order_id: context.order_id.clone(),
                 reason,
                 payment_id_to_refund: context.payment_id.clone(),
                 product_id_to_release: if context.inventory_reserved { Some(context.product_id.clone()) } else { None },
                 quantity_to_release: if context.inventory_reserved { Some(context.quantity) } else { None },
             }
         }
     }


    // --- 运行 Saga ---
    // #[tokio::main]
    async fn conceptual_saga_main() {
        // 定义 Saga 步骤 (成功路径)
        let steps_success: Vec<Arc<dyn SagaStep<_, _, _>>> = vec![
            Arc::new(CreateOrderStep),
            Arc::new(ProcessPaymentStep { should_fail: false }), // 支付成功
            Arc::new(ReserveInventoryStep),
        ];
        let orchestrator_success = SagaOrchestrator::new(steps_success);

        println!("--- Running Saga (Success Path) ---");
        let request = CreateOrderRequest {
            user_id: "user123".to_string(),
            product_id: "prod456".to_string(),
            quantity: 2,
        };
        match orchestrator_success.run(request.clone()).await {
             Ok(final_context) => println!("Saga Success Result: {:?}", final_context),
             Err((err_msg, final_context)) => println!("Saga Failed: {} \nFinal Context: {:?}", err_msg, final_context),
        }


        println!("\n--- Running Saga (Failure Path - Payment Fails) ---");
         // 定义 Saga 步骤 (失败路径)
         let steps_fail: Vec<Arc<dyn SagaStep<_, _, _>>> = vec![
             Arc::new(CreateOrderStep),
             Arc::new(ProcessPaymentStep { should_fail: true }), // 支付失败
             Arc::new(ReserveInventoryStep), // 这一步不会执行
         ];
        let orchestrator_fail = SagaOrchestrator::new(steps_fail);
         match orchestrator_fail.run(request).await {
              Ok(final_context) => println!("Saga Success Result: {:?}", final_context),
              Err((err_msg, final_context)) => println!("Saga Failed: {} \nFinal Context after compensation: {:?}", err_msg, final_context),
         }
    }


     fn main() {
        println!("--- Saga Pattern Conceptual Example ---");
        // 这个示例需要在 tokio 运行时中执行
        // tokio::runtime::Runtime::new().unwrap().block_on(conceptual_saga_main());
        println!("--- Requires tokio runtime to execute ---");
    }

    ```

#### 3.2.5. 领导者选举 (Leader Election)

- **定义**: 在一组分布式节点中，选举出一个唯一的“领导者”节点来执行特殊任务（如协调、写入主副本、任务分配）。
- **解释**: 确保某些操作只有一个节点执行，避免冲突和不一致。常见的算法有 Paxos 和 Raft。通常使用分布式协调服务（如 Zookeeper, etcd）或专门的库来实现。
- **Rust 示例 (概念性 - 使用 etcd 租约)**:
  - 需要 `etcd-client` crate 和运行中的 etcd 服务。

    ```rust
    // 概念性示例，需要 etcd-client crate 和运行中的 etcd 服务
    // use etcd_client::{Client, LeaseGrantOptions, PutOptions, LockOptions, KeyValue};
    // use std::time::Duration;
    // use tokio::time::sleep;

    const LEADER_KEY: &str = "/myapp/leader"; // etcd 中用于选举的 key
    const LEASE_TTL: i64 = 10; // 租约 TTL (秒)
    const HEARTBEAT_INTERVAL: Duration = Duration::from_secs(LEASE_TTL as u64 / 3); // 心跳间隔


    async fn try_become_leader(client: &etcd_client::Client, node_id: &str) -> Result<Option<i64>, Box<dyn std::error::Error>> {
         println!("[{}] Attempting to become leader...", node_id);

        // 1. 创建租约
        let lease_resp = client.lease_grant(LEASE_TTL, None).await?;
        let lease_id = lease_resp.id();
        println!("[{}] Granted lease ID: {}", node_id, lease_id);

        // 2. 尝试使用租约创建 leader key (原子操作)
        // 使用事务 (Txn) 来实现 Compare-and-Swap (CAS)
        // 如果 key 不存在 (version == 0)，则创建它并关联租约
        let txn = etcd_client::Txn::new()
             .when(vec![etcd_client::Compare::version(LEADER_KEY, etcd_client::CompareOp::Equal, 0)]) // 条件：key 不存在
             .and_then(vec![etcd_client::PutRequest::new(LEADER_KEY, node_id).with_lease(lease_id).into()]) // 操作：创建 key
             .or_else(vec![etcd_client::GetRequest::new(LEADER_KEY).into()]); // 如果存在，则获取当前 leader

        let txn_resp = client.txn(txn).await?;

        if !txn_resp.succeeded() {
            // Key 已存在，获取当前 leader 信息
            if let Some(etcd_client::Response::GetResponse(get_resp)) = txn_resp.responses().get(0) {
                 if let Some(kv) = get_resp.kvs().get(0) {
                     println!("[{}] Failed to acquire leadership. Current leader: {} (Lease: {})",
                         node_id, String::from_utf8_lossy(kv.value()), kv.lease());
                 } else {
                      println!("[{}] Failed to acquire leadership. Leader key exists but couldn't get value.", node_id);
                 }
            } else {
                 println!("[{}] Failed to acquire leadership for unknown reason.", node_id);
            }
            // 获取领导失败，撤销刚才创建的租约
            client.lease_revoke(lease_id).await?;
             println!("[{}] Revoked lease {}.", node_id, lease_id);
            return Ok(None); // 未成为 leader
        }

        // 3. 成功获取领导权
        println!("[{}] Successfully acquired leadership with lease ID {}!", node_id, lease_id);

        // 启动租约心跳 (保持租约活跃) in background
        let mut client_clone = client.clone();
        let node_id_clone = node_id.to_string();
        tokio::spawn(async move {
            loop {
                 match client_clone.lease_keep_alive(lease_id).await {
                     Ok(mut stream) => {
                         println!("[{}] Lease keep-alive stream started for lease {}", node_id_clone, lease_id);
                         while let Some(resp) = stream.message().await.ok().flatten() {
                             // println!("[{}] Lease {} keep-alive TTL: {}", node_id_clone, lease_id, resp.ttl());
                             if resp.ttl() <= 0 {
                                 eprintln!("[{}] CRITICAL: Lease {} expired unexpectedly!", node_id_clone, lease_id);
                                 // 可能需要触发下台逻辑
                                 break;
                             }
                             // 等待下一次心跳
                             tokio::time::sleep(HEARTBEAT_INTERVAL).await;
                         }
                          eprintln!("[{}] Lease keep-alive stream ended for lease {}.", node_id_clone, lease_id);
                     }
                     Err(e) => {
                         eprintln!("[{}] Failed to start lease keep-alive for {}: {}. Node might lose leadership.", node_id_clone, lease_id, e);
                         // 停止心跳，租约会过期，其他节点可以竞争
                         break;
                     }
                 }
                 // 如果 keep_alive 失败或结束，尝试重新建立 (或者直接放弃)
                 tokio::time::sleep(Duration::from_secs(1)).await; // 等待一秒再重试
            }
             println!("[{}] Lease keep-alive task finished for lease {}.", node_id_clone, lease_id);
        });


        Ok(Some(lease_id)) // 返回租约 ID，表示成为 leader
    }

    async fn step_down(client: &etcd_client::Client, node_id: &str, lease_id: i64) {
         println!("[{}] Stepping down as leader (revoking lease {})...", node_id, lease_id);
         // 撤销租约，这会自动删除关联的 key
         if let Err(e) = client.lease_revoke(lease_id).await {
              eprintln!("[{}] Failed to revoke lease {}: {}", node_id, lease_id, e);
         } else {
              println!("[{}] Lease {} revoked successfully.", node_id, lease_id);
         }
         // 这里应该停止 leader 相关的工作
    }

    // #[tokio::main]
    async fn conceptual_election_main() {
        let node_id_1 = format!("node-{}", rand::random::<u16>());
        let node_id_2 = format!("node-{}", rand::random::<u16>());

        println!("Simulating leader election with node {} and {}", node_id_1, node_id_2);

        // // 创建 etcd 客户端 (需要运行 etcd)
        // let client = Client::connect(["localhost:2379"], None).await.expect("Failed to connect to etcd");
        // let client1 = client.clone();
        // let client2 = client.clone();

        // 模拟第一个节点尝试成为 leader
        println!("Node {} attempting...", node_id_1);
        // let lease1 = try_become_leader(&client1, &node_id_1).await.unwrap();
        let lease1 = Some(12345i64); // 模拟成功
        println!("Node {} result: {:?}", node_id_1, lease1);

        tokio::time::sleep(Duration::from_secs(1)).await; // 等待一下

        // 模拟第二个节点尝试成为 leader (应该失败)
         println!("Node {} attempting...", node_id_2);
        // let lease2 = try_become_leader(&client2, &node_id_2).await.unwrap();
        let lease2: Option<i64> = None; // 模拟失败
         println!("Node {} result: {:?}", node_id_2, lease2);


        if let Some(id1) = lease1 {
            println!("Node {} is leader. Performing leader duties for a while...", node_id_1);
            tokio::time::sleep(Duration::from_secs(5)).await;
             // 模拟 leader 主动下台
             // step_down(&client1, &node_id_1, id1).await;
             println!("[{}] Stepping down (simulated)...", node_id_1);
        }

         // 在第一个节点下台后，第二个节点应该可以成为 leader
         println!("\nNode {} attempting again after leader stepped down...", node_id_2);
         // let lease2_again = try_become_leader(&client2, &node_id_2).await.unwrap();
          let lease2_again = Some(67890i64); // 模拟成功
         println!("Node {} result: {:?}", node_id_2, lease2_again);

          if let Some(id2) = lease2_again {
             println!("Node {} is now leader.", node_id_2);
             // step_down(&client2, &node_id_2, id2).await; // 模拟下台
             println!("[{}] Stepping down (simulated)...", node_id_2);
         }

    }

      fn main() {
        println!("--- Leader Election Conceptual Example (using etcd) ---");
        // 这个示例需要 tokio 运行时和 etcd 服务
        // tokio::runtime::Runtime::new().unwrap().block_on(conceptual_election_main());
        println!("--- Requires tokio runtime and etcd server to run ---");
    }
    ```

#### 3.2.6. 分片/分区 (Sharding/Partitioning)

- **定义**: 将大型数据集或高负载的工作负载水平分割到多个数据库、服务器或节点上的过程。
- **解释**: 提高可伸缩性、性能和可用性。常见的分片策略包括：
  - **基于范围 (Range-based)**: 根据数据值的范围（如用户 ID、时间戳）分配到分片。简单，但可能导致数据分布不均（热点）。
  - **基于哈希 (Hash-based)**: 对数据的某个键（如用户 ID）进行哈希，根据哈希值分配到分片。通常分布更均匀，但范围查询困难。
  - **目录式 (Directory-based)**: 维护一个查找表（目录）来映射数据的键到其所在的分片。灵活性高，但目录本身可能成为瓶颈。
- **Rust 示例 (概念性 - 基于哈希的路由)**:

    ```rust
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    // 定义分片信息
    #[derive(Debug, Clone)]
    struct Shard {
        id: usize,
        address: String, // 分片节点的地址 (例如数据库连接字符串)
    }

    // 分片管理器
    struct ShardManager {
        shards: Vec<Shard>,
        shard_count: usize,
    }

    impl ShardManager {
        fn new(shard_addresses: Vec<String>) -> Self {
            let shard_count = shard_addresses.len();
            assert!(shard_count > 0, "Must have at least one shard");
            let shards = shard_addresses.into_iter().enumerate().map(|(id, address)| {
                Shard { id, address }
            }).collect();
            ShardManager { shards, shard_count }
        }

        // 计算哈希值
        fn calculate_hash<T: Hash>(&self, key: &T) -> u64 {
             let mut hasher = DefaultHasher::new();
             key.hash(&mut hasher);
             hasher.finish()
        }

        // 根据 Key 获取对应的分片
        fn get_shard_for_key<T: Hash>(&self, key: &T) -> &Shard {
            let hash = self.calculate_hash(key);
            let shard_index = (hash % self.shard_count as u64) as usize;
            &self.shards[shard_index]
        }

        // 获取所有分片 (例如用于聚合查询)
        fn get_all_shards(&self) -> &Vec<Shard> {
             &self.shards
        }
    }

    // 示例数据结构，需要根据 UserID 分片
    #[derive(Debug, Hash)] // UserID 需要实现 Hash
    struct UserData {
        user_id: String,
        data: String,
    }


    fn main() {
        println!("--- Sharding/Partitioning Conceptual Example (Hash-based Routing) ---");

        // 初始化分片管理器 (假设有 3 个分片)
        let shard_addresses = vec![
            "db_shard_0.example.com:5432".to_string(),
            "db_shard_1.example.com:5432".to_string(),
            "db_shard_2.example.com:5432".to_string(),
        ];
        let shard_manager = ShardManager::new(shard_addresses);

        // 模拟一些用户数据
        let users = vec![
            UserData { user_id: "user_alpha".to_string(), data: "...".to_string() },
            UserData { user_id: "user_beta".to_string(), data: "...".to_string() },
            UserData { user_id: "user_gamma".to_string(), data: "...".to_string() },
            UserData { user_id: "user_delta".to_string(), data: "...".to_string() },
             UserData { user_id: "user_epsilon".to_string(), data: "...".to_string() },
        ];

        // 路由数据到对应的分片
        println!("Routing user data to shards based on user_id hash:");
        for user in &users {
            // 根据 user_id 决定数据应该存储在哪个分片
            let target_shard = shard_manager.get_shard_for_key(&user.user_id);
            println!(" -> User '{}' maps to Shard {} ({})", user.user_id, target_shard.id, target_shard.address);
            // 实际应用中，这里会建立到 target_shard.address 的连接并执行数据库操作
        }

        // 如果需要查询所有分片的数据 (例如，统计总用户数)
        println!("\nQuerying all shards for aggregation (e.g., total users):");
        for shard in shard_manager.get_all_shards() {
             println!(" - Querying Shard {} ({})", shard.id, shard.address);
             // 实际应用中，会连接到每个分片执行查询，然后合并结果
        }

    }

    ```

#### 3.2.7. 复制 (Replication)

- **定义**: 在多个节点上创建和维护相同数据的副本的过程。
- **解释**: 主要目的包括：
  - **高可用性 (High Availability)**: 如果一个持有数据的节点失败，可以从副本提供服务。
  - **提高读取性能**: 读取请求可以分发到多个副本节点。
  - **数据冗余/备份**: 防止数据丢失。
    常见模式：
  - **主从复制 (Leader-Follower / Master-Slave)**: 写入操作只发生在主节点，然后异步或同步复制到从节点。读取可以从主节点或从节点进行。简单，但主节点是单点故障（需要故障转移机制）。
  - **多主复制 (Multi-Leader / Master-Master)**: 允许多个节点接受写入操作，写入需要在节点间同步，可能导致写入冲突需要解决。更复杂，但写入可用性更高。
  - **无主复制 (Leaderless)**: 所有副本都可以接受写入，客户端将写入发送到多个副本，通过 quorum（法定人数，W+R > N）机制保证一致性。如 Cassandra, DynamoDB。
- **Rust 示例**: 复制通常由数据库、存储系统或消息队列自身实现，应用程序层面较少直接实现复制逻辑。应用程序通常是配置和使用这些系统的复制功能。例如，配置 PostgreSQL 的流复制，或使用 Kafka 的分区副本。代码示例意义不大，更多是架构和配置层面。

    ```rust
    // 复制通常在基础设施层面实现（数据库、消息队列等）
    // Rust 应用代码通常是与这些配置好的复制系统交互

    fn main() {
         println!("--- Replication Conceptual Notes ---");
         println!("Replication is typically handled by infrastructure (databases, message queues).");
         println!("Example Scenarios:");
         println!("1. Database Read Replicas:");
         println!("   - Application connects to a read replica for read-heavy workloads.");
         println!("   - Writes go to the primary/leader database instance.");
         println!("   - Rust code would use different connection strings based on operation type.");
         println!("2. Kafka Topic Replication:");
         println!("   - Kafka brokers replicate topic partitions across the cluster.");
         println!("   - Rust Kafka clients (like rdkafka-rust) produce/consume from the leader broker for a partition,");
         println!("     but Kafka handles the replication transparently.");
         println!("3. Distributed Cache (e.g., Redis Cluster):");
         println!("   - Data is sharded and replicated across Redis nodes.");
         println!("   - Rust Redis clients connect to the cluster and are routed appropriately.");
         println!("------------------------------------");
    }
    ```

#### 3.2.8. 消息队列 (Message Queue)

- **定义**: 一种中间件模式，允许应用程序或服务通过发送和接收消息进行异步通信。发送者（生产者）将消息放入队列，接收者（消费者）从队列中取出消息进行处理。
- **解释**: 实现服务解耦、削峰填谷、异步处理、最终一致性等。常见实现包括 RabbitMQ (AMQP), Kafka (分布式流平台), NATS, Redis Streams, AWS SQS/SNS 等。
- **Rust 示例 (使用 `lapin` - RabbitMQ AMQP 客户端)**:
  - 需要添加 `lapin = "2"` 和 `tokio = { version = "1", features = ["full"] }` 依赖。需要运行 RabbitMQ 服务。

    ```rust
    // 概念性示例，需要 lapin crate 和运行中的 RabbitMQ 服务
    // use lapin::{
    //     options::*, types::FieldTable, BasicProperties, Connection,
    //     ConnectionProperties, Result, Channel, message::Delivery,
    // };
    // use tokio::time::{sleep, Duration};
    // use futures_lite::stream::StreamExt; // lapin 使用 futures-lite

    const AMQP_ADDR: &str = "amqp://guest:guest@localhost:5672/%2f"; // RabbitMQ 连接地址
    const QUEUE_NAME: &str = "hello_queue";

    async fn setup_channel() -> Result<lapin::Channel, lapin::Error> {
        // let conn = Connection::connect(
        //     AMQP_ADDR,
        //     ConnectionProperties::default().with_tokio(), // 使用 tokio executor
        // ).await?;
        // println!("MQ: Connected!");
        //
        // let channel = conn.create_channel().await?;
        // println!("MQ: Channel created.");
        //
        // // 声明队列 (如果不存在则创建)
        // let _queue = channel
        //     .queue_declare(
        //         QUEUE_NAME,
        //         QueueDeclareOptions::default(), // durable=false, exclusive=false, auto_delete=false
        //         FieldTable::default(),
        //     )
        //     .await?;
        // println!("MQ: Queue '{}' declared.", QUEUE_NAME);
        //
        // Ok(channel)
        println!("Conceptual MQ: Setting up channel and declaring queue '{}'", QUEUE_NAME);
        // 模拟返回一个虚拟 Channel (无法实际使用)
        // 为了让代码编译通过，我们需要一个能实现 lapin::Channel trait 的类型
        // 这比较复杂，所以保持概念性
        Err(lapin::Error::ProtocolError(amqp_proto::protocol::Error::UnexpectedFrame)) // 返回一个错误来表示这是模拟
    }


    async fn publish_message(channel: &lapin::Channel, message: &str) -> Result<(), lapin::Error> {
        // let payload = message.as_bytes();
        // println!("MQ Publisher: Publishing message: '{}'", message);
        // channel
        //     .basic_publish(
        //         "", // exchange - 空字符串表示使用默认交换机
        //         QUEUE_NAME, // routing_key - 对于默认交换机，routing_key 是队列名
        //         BasicPublishOptions::default(),
        //         payload, // message body
        //         BasicProperties::default(), // message properties
        //     )
        //     .await? // 等待 RabbitMQ 的确认 (Publish Confirm)
        //     .await?; // 等待 ack/nack
        // println!("MQ Publisher: Message published successfully.");
        // Ok(())
        println!("Conceptual MQ Publisher: Publishing '{}'", message);
        Ok(())
    }

    async fn consume_messages(channel: &lapin::Channel) -> Result<(), lapin::Error> {
        // let mut consumer = channel
        //     .basic_consume(
        //         QUEUE_NAME,
        //         "my_consumer", // consumer tag
        //         BasicConsumeOptions::default(), // no_ack=false (需要手动确认)
        //         FieldTable::default(),
        //     )
        //     .await?;
        //
        // println!("MQ Consumer: Waiting for messages...");
        //
        // // 循环处理消息
        // while let Some(delivery_result) = consumer.next().await {
        //     match delivery_result {
        //         Ok(delivery) => {
        //             if let Some(delivery) = delivery {
        //                 let message_data = std::str::from_utf8(&delivery.data).unwrap_or("Invalid UTF-8");
        //                 println!("MQ Consumer: Received message: '{}'", message_data);
        //
        //                 // 在这里处理消息...
        //                 tokio::time::sleep(Duration::from_millis(500)).await; // 模拟处理时间
        //
        //                 // 确认消息已被处理
        //                 if let Err(e) = delivery.ack(BasicAckOptions::default()).await {
        //                      eprintln!("MQ Consumer: Failed to ack message: {}", e);
        //                 } else {
        //                     println!("MQ Consumer: Message acknowledged.");
        //                 }
        //             }
        //         }
        //         Err(e) => {
        //             eprintln!("MQ Consumer: Error receiving message: {}", e);
        //              // 可以选择在这里停止消费者或尝试重新连接
        //              break;
        //         }
        //     }
        // }
        // println!("MQ Consumer: Consumer stream finished.");
        // Ok(())
        println!("Conceptual MQ Consumer: Starting consumption loop...");
        println!("Conceptual MQ Consumer: Received message 'Example 1'");
        println!("Conceptual MQ Consumer: Acknowledged 'Example 1'");
        println!("Conceptual MQ Consumer: Received message 'Example 2'");
        println!("Conceptual MQ Consumer: Acknowledged 'Example 2'");
         println!("Conceptual MQ Consumer: Finished.");
        Ok(())
    }


    // #[tokio::main]
    async fn conceptual_mq_main() {
        // // --- Publisher ---
        // let publisher_channel_result = setup_channel().await;
        // if let Ok(publisher_channel) = publisher_channel_result {
        //     println!("Publisher starting...");
        //     for i in 0..5 {
        //         let msg = format!("Message #{}", i);
        //         if let Err(e) = publish_message(&publisher_channel, &msg).await {
        //             eprintln!("Publisher failed to send message {}: {}", i, e);
        //             break;
        //         }
        //          tokio::time::sleep(Duration::from_millis(200)).await;
        //     }
        //     println!("Publisher finished.");
        //     // 关闭 channel 和 connection (可选，drop 时会自动处理)
        //     // publisher_channel.close(200, "Goodbye").await.ok();
        //     // publisher_channel.connection().close(200, "Goodbye").await.ok();
        // } else {
        //      eprintln!("Publisher failed to setup channel: {:?}", publisher_channel_result.err());
        // }

        // --- 启动发布者 (模拟) ---
         tokio::spawn(async {
             println!("Conceptual Publisher starting...");
             let _ = publish_message(&lapin::Channel::default(), "Msg 1").await; // 使用默认 Channel (无效)
             tokio::time::sleep(Duration::from_millis(200)).await;
              let _ = publish_message(&lapin::Channel::default(), "Msg 2").await;
             tokio::time::sleep(Duration::from_millis(200)).await;
             println!("Conceptual Publisher finished.");
         });


        tokio::time::sleep(Duration::from_millis(100)).await; // 确保发布者先启动

        // --- Consumer ---
        // let consumer_channel_result = setup_channel().await;
        // if let Ok(consumer_channel) = consumer_channel_result {
        //     println!("Consumer starting...");
        //     if let Err(e) = consume_messages(&consumer_channel).await {
        //          eprintln!("Consumer encountered an error: {}", e);
        //     }
        //      // 关闭 channel 和 connection
        //      // consumer_channel.close(200, "Goodbye").await.ok();
        //      // consumer_channel.connection().close(200, "Goodbye").await.ok();
        // } else {
        //       eprintln!("Consumer failed to setup channel: {:?}", consumer_channel_result.err());
        // }

         // --- 启动消费者 (模拟) ---
         println!("Conceptual Consumer starting...");
         let _ = consume_messages(&lapin::Channel::default()).await;


    }

     fn main() {
        println!("--- Message Queue Conceptual Example (using lapin for RabbitMQ) ---");
        // 这个示例需要 tokio 运行时和 RabbitMQ 服务
        // tokio::runtime::Runtime::new().unwrap().block_on(conceptual_mq_main());
        println!("--- Requires tokio runtime and RabbitMQ server to run ---");
    }
    ```

---

## 4. 工作流设计模式

### 4.1. 概念与定义

工作流 (Workflow) 是一系列按照特定规则顺序执行的任务或活动的集合，用于完成某个业务目标。
工作流设计模式关注如何定义、执行、监控和管理这些业务流程，特别是涉及多个步骤、状态转换、条件分支、人工干预或长时间运行的流程。

### 4.2. 常见模式

#### 4.2.1. 状态机模式 (State Machine)

- **定义**: 见 1.5.8 状态模式 (State)。在工作流上下文中，状态机用于精确地定义一个业务实体（如订单、文档、用户请求）在其生命周期中可能经历的各种状态以及触发状态转换的事件或条件。
- **解释**: 非常适合对具有明确、有限状态和转换规则的流程进行建模。易于理解和验证。
- **Rust 示例**: (复用 1.5.8 中的 Enum 示例，更贴近工作流场景)

    ```rust
    // (与 1.5.8 中 Document 示例类似)

    enum LoanApplicationState {
        Submitted,                  // 已提交
        UnderReview { reviewer: String }, // 审核中
        Approved,                   // 已批准
        Rejected { reason: String },    // 已拒绝
        Closed,                     // 已关闭 (放款或取消)
    }

    struct LoanApplication {
        id: String,
        applicant: String,
        amount: f64,
        state: LoanApplicationState,
    }

    impl LoanApplication {
        fn new(id: String, applicant: String, amount: f64) -> Self {
            LoanApplication {
                id,
                applicant,
                amount,
                state: LoanApplicationState::Submitted,
            }
        }

        fn assign_for_review(&mut self, reviewer: String) {
            match self.state {
                LoanApplicationState::Submitted => {
                     println!("Application '{}': Submitted -> UnderReview (Reviewer: {})", self.id, reviewer);
                    self.state = LoanApplicationState::UnderReview { reviewer };
                }
                _ => println!("Application '{}': Cannot assign for review from state {:?}", self.id, self.state_name()),
            }
        }

        fn approve(&mut self) {
             match self.state {
                 LoanApplicationState::UnderReview { .. } => {
                      println!("Application '{}': UnderReview -> Approved", self.id);
                     self.state = LoanApplicationState::Approved;
                 }
                 _ => println!("Application '{}': Cannot approve from state {:?}", self.id, self.state_name()),
             }
        }

         fn reject(&mut self, reason: String) {
              match self.state {
                  LoanApplicationState::UnderReview { .. } => {
                       println!("Application '{}': UnderReview -> Rejected (Reason: {})", self.id, reason);
                      self.state = LoanApplicationState::Rejected { reason };
                  }
                  _ => println!("Application '{}': Cannot reject from state {:?}", self.id, self.state_name()),
              }
         }

         fn close(&mut self) {
              match self.state {
                  LoanApplicationState::Approved | LoanApplicationState::Rejected {..} => {
                       println!("Application '{}': {:?} -> Closed", self.id, self.state_name());
                       self.state = LoanApplicationState::Closed;
                  }
                   LoanApplicationState::Submitted | LoanApplicationState::UnderReview {..} => {
                       println!("Application '{}': Cannot close directly from {:?}. Cancel or process first.", self.id, self.state_name());
                  }
                  LoanApplicationState::Closed => println!("Application '{}': Already Closed.", self.id),
              }
         }

        fn state_name(&self) -> &'static str {
             match self.state {
                 LoanApplicationState::Submitted => "Submitted",
                 LoanApplicationState::UnderReview {..} => "UnderReview",
                 LoanApplicationState::Approved => "Approved",
                 LoanApplicationState::Rejected {..} => "Rejected",
                 LoanApplicationState::Closed => "Closed",
             }
        }
    }

    fn main() {
         println!("--- Workflow State Machine Example (Loan Application) ---");
         let mut app = LoanApplication::new("loan_abc".to_string(), "Alice".to_string(), 5000.0);
         println!("Initial State: {}", app.state_name());

         app.approve(); // Cannot approve
         app.assign_for_review("Bob".to_string()); // Submitted -> UnderReview
         println!("Current State: {}", app.state_name());

         app.assign_for_review("Charlie".to_string()); // Cannot assign again
         app.reject("Insufficient income".to_string()); // UnderReview -> Rejected
         println!("Current State: {}", app.state_name());

         app.approve(); // Cannot approve
         app.close(); // Rejected -> Closed
         println!("Current State: {}", app.state_name());
         app.close(); // Already Closed
    }

    ```

#### 4.2.2. 工作流引擎 (Workflow Engine)

- **定义**: 一个专门用于定义、执行和管理工作流的软件系统。通常提供图形化建模工具（如 BPMN）、流程定义存储、流程实例执行、任务管理、状态持久化、事件处理、监控和报告等功能。
- **解释**: 适用于复杂、长时间运行、涉及多人协作或需要与外部系统集成的业务流程。将流程逻辑与业务代码分离。常见的引擎有 Camunda, Zeebe, Temporal, Cadence, Flowable 等。
- **Rust 示例**: 使用工作流引擎通常涉及：
    1. **定义流程**: 使用 BPMN 或特定 DSL 定义工作流。
    2. **部署流程**: 将定义部署到引擎。
    3. **启动实例**: 通过 API 或事件触发工作流实例的启动。
    4. **执行任务**:
        - **用户任务**: 分配给用户，通过任务列表 UI 完成。
        - **服务任务**: 由引擎调用外部服务（Worker）来执行。Rust 代码通常是编写 Worker 来订阅和处理这些服务任务。
    5. **完成实例**: 流程按定义执行，最终达到结束状态。

    以下是使用 `zeebe-client-rust-1` (假设存在这样一个库，实际可能需要寻找合适的库或使用 gRPC) 与 Zeebe 交互的 Worker 概念：

    ```rust
    // 概念性示例，需要 Zeebe 客户端库和运行中的 Zeebe 集群
    // use zeebe_client::{Client, JobWorkerBuilder, Job}; // 假设的库结构
    // use std::time::Duration;
    // use serde_json::json;

    async fn process_payment_worker(job: &impl zeebe_client::Job) -> Result<(), String> { // Job trait 需要定义
         println!("Worker 'process-payment': Received job (Key: {})", job.key());
         // let variables = job.get_variables::<serde_json::Value>().map_err(|e| e.to_string())?;
         // let order_id = variables.get("orderId").and_then(|v| v.as_str()).unwrap_or("unknown");
         // let amount = variables.get("amount").and_then(|v| v.as_f64()).unwrap_or(0.0);
         let order_id = "order123"; // 模拟获取变量
         let amount = 99.99;      // 模拟获取变量

         println!(" -> Processing payment for Order ID: {}, Amount: {:.2}", order_id, amount);

         // 模拟调用支付网关
         tokio::time::sleep(Duration::from_secs(1)).await;
         let payment_successful = rand::random::<bool>(); // 模拟成功或失败

         if payment_successful {
             println!(" -> Payment Successful.");
             // 完成作业，并可以传递输出变量
            //  let output_variables = json!({ "paymentStatus": "SUCCESS" });
            //  job.complete(output_variables).await.map_err(|e| e.to_string())?;
              println!(" -> Job completed successfully.");
              Ok(())
         } else {
              println!(" -> Payment Failed.");
              // 报告业务错误 (让流程可以根据错误码决定走向)
             //  let error_code = "PAYMENT_FAILED";
             //  let error_message = "Insufficient funds".to_string();
             //  job.throw_error(error_code, error_message).await.map_err(|e| e.to_string())?;
             // 或者直接失败作业 (需要重试)
             // job.fail("Payment gateway declined".to_string()).await.map_err(|e| e.to_string())?;
              println!(" -> Job failed (or business error reported).");
              Err("Simulated payment failure".to_string()) // 返回错误以模拟失败
         }
    }

    // 模拟 Job trait
    mod zeebe_client {
        pub trait Job { fn key(&self) -> i64; }
        #[derive(Default)] pub struct MockJob { key: i64 }
        impl Job for MockJob { fn key(&self) -> i64 { self.key } }
        impl MockJob { pub fn new(key: i64) -> Self { MockJob { key } } }
    }


    // #[tokio::main]
    async fn conceptual_engine_main() {
        // // 创建 Zeebe 客户端 (需要配置连接地址)
        // let client = Client::new("localhost:26500").await.expect("Failed to connect to Zeebe");
        //
        // // 创建并运行 Job Worker
        // let worker = JobWorkerBuilder::new(&client)
        //     .job_type("process-payment") // 订阅 BPMN 中定义的服务任务类型
        //     .handler(process_payment_worker) // 指定处理函数
        //     .max_jobs_active(5)
        //     .timeout(Duration::from_secs(60))
        //     .poll_interval(Duration::from_millis(100))
        //     .run() // 在后台运行 worker 循环
        //     .await; // 等待 worker 运行 (或者不 await 让它在后台跑)
        //
        // println!("Payment worker started. Waiting for jobs...");
        // // worker 会持续运行，从 Zeebe 拉取并处理类型为 "process-payment" 的作业

        // 模拟 worker 接收和处理作业
         println!("Conceptual Worker 'process-payment' starting...");
         let job1 = zeebe_client::MockJob::new(1);
         match process_payment_worker(&job1).await {
              Ok(_) => println!("Worker processed job {} successfully.", job1.key()),
              Err(e) => println!("Worker failed to process job {}: {}", job1.key(), e),
         }
          let job2 = zeebe_client::MockJob::new(2);
          match process_payment_worker(&job2).await {
               Ok(_) => println!("Worker processed job {} successfully.", job2.key()),
               Err(e) => println!("Worker failed to process job {}: {}", job2.key(), e),
          }
          println!("Conceptual Worker finished simulation.");

    }

     fn main() {
        println!("--- Workflow Engine Conceptual Example (Zeebe Worker) ---");
        // 这个示例需要 tokio 运行时和 Zeebe 客户端库
        // tokio::runtime::Runtime::new().unwrap().block_on(conceptual_engine_main());
        println!("--- Requires tokio runtime and Zeebe client library to run ---");
    }
    ```

#### 4.2.3. 任务队列 (Task Queue)

- **定义**: 见 2.2.4 生产者-消费者模式 和 3.2.8 消息队列。
在工作流上下文中，任务队列常用于解耦流程中的长时间运行或需要异步执行的步骤。
流程引擎（或应用程序）将任务发布到队列，独立的 Worker 进程从队列中消费并执行任务。
- **解释**: 提高流程的响应性，允许独立扩展 Worker，增强系统的弹性和容错性。适用于发送邮件、生成报告、数据处理等后台任务。
- **Rust 示例**: 可以使用 `celery-rs` (Celery 的 Rust 实现) 或基于 Redis/RabbitMQ/Kafka 的队列。这里复用 3.2.8 的 RabbitMQ 示例概念。

    ```rust
    // (复用 3.2.8 Message Queue 概念)

    // 假设有一个订单处理工作流
    async fn order_workflow(order_id: &str, mq_channel: &lapin::Channel) {
         println!("Workflow [{}]: Started.", order_id);

         // 步骤 1: 验证订单 (同步执行)
         println!("Workflow [{}]: Validating order...", order_id);
         tokio::time::sleep(Duration::from_millis(50)).await; // 模拟

         // 步骤 2: 发送确认邮件 (异步任务)
         let email_task = serde_json::json!({
             "task_type": "send_email",
             "recipient": "customer@example.com",
             "subject": format!("Order Confirmation {}", order_id),
             "body": "Your order has been received."
         });
         println!("Workflow [{}]: Publishing 'send_email' task to queue.", order_id);
         // publish_message(mq_channel, &email_task.to_string()).await.ok(); // 概念性发布
         println!("Conceptual MQ Publisher: Publishing '{}'", email_task.to_string());

          // 步骤 3: 准备发货 (可能是另一个服务或流程)
         println!("Workflow [{}]: Triggering shipment preparation...", order_id);
         tokio::time::sleep(Duration::from_millis(100)).await; // 模拟


          // 步骤 4: 生成发票 (异步任务)
          let invoice_task = serde_json::json!({
              "task_type": "generate_invoice",
              "order_id": order_id,
              "amount": 199.99 // 假设金额
          });
          println!("Workflow [{}]: Publishing 'generate_invoice' task to queue.", order_id);
          // publish_message(mq_channel, &invoice_task.to_string()).await.ok();
          println!("Conceptual MQ Publisher: Publishing '{}'", invoice_task.to_string());


         println!("Workflow [{}]: Finished main flow (background tasks queued).", order_id);
    }

    // --- 后台 Worker (消费任务队列) ---
    async fn task_queue_worker(delivery: &lapin::Delivery) { // 假设 Delivery 类型存在
        // let message_data = std::str::from_utf8(&delivery.data).unwrap_or("{}");
        // let task: Result<serde_json::Value, _> = serde_json::from_str(message_data);
        let task_type: Option<&str> = Some("send_email"); // 模拟解析
        let task_data: serde_json::Value = serde_json::json!({}); // 模拟解析

        // if let Ok(task_json) = task {
        //     if let Some(task_type) = task_json.get("task_type").and_then(|t| t.as_str()) {
                 match task_type {
                     Some("send_email") => {
                         println!("Worker: Processing 'send_email' task...");
                         // let recipient = task_json.get("recipient")...
                          tokio::time::sleep(Duration::from_secs(2)).await; // 模拟发送邮件
                          println!("Worker: Email sent (simulated).");
                     }
                      Some("generate_invoice") => {
                          println!("Worker: Processing 'generate_invoice' task...");
                          // let order_id = task_json.get("order_id")...
                           tokio::time::sleep(Duration::from_secs(3)).await; // 模拟生成 PDF
                           println!("Worker: Invoice generated (simulated).");
                      }
                     _ => {
                         eprintln!("Worker: Unknown task type received: {:?}", task_type);
                     }
                 }
        //     } else {
        //          eprintln!("Worker: Received task without 'task_type'.");
        //     }
        // } else {
        //     eprintln!("Worker: Failed to parse task JSON: {}", message_data);
        // }

        // 确认消息 (概念性)
        println!("Worker: Acknowledging task.");
        // delivery.ack(BasicAckOptions::default()).await.ok();
    }

    // 模拟 Delivery 类型 (简化)
    mod lapin { pub struct Delivery {} }
    use std::time::Duration; // 需要引入 Duration

    // #[tokio::main]
    async fn conceptual_task_queue_main() {
         // 模拟启动工作流
         // let channel = setup_channel().await.unwrap(); // 假设成功获取通道
         println!("--- Task Queue Conceptual Example ---");
         let order_id = "ORD-XYZ789";
         order_workflow(order_id, &lapin::Channel::default()).await; // 传入无效通道

         println!("\n--- Simulating Worker Processing ---");
         // 模拟 worker 从队列接收到邮件任务
         let email_delivery = lapin::Delivery {}; // 无效 delivery
         task_queue_worker(&email_delivery).await;

          // 模拟 worker 从队列接收到发票任务
         let invoice_delivery = lapin::Delivery {}; // 无效 delivery
         task_queue_worker(&invoice_delivery).await;

         println!("--- End of Conceptual Example ---");
    }

     fn main() {
        println!("--- Task Queue Conceptual Example (using MQ) ---");
        // 这个示例需要 tokio 运行时
        // tokio::runtime::Runtime::new().unwrap().block_on(conceptual_task_queue_main());
        println!("--- Requires tokio runtime to execute simulation ---");
    }

    ```

#### 4.2.4. 编排 (Orchestration) vs. 协同 (Choreography)

- **定义**: 这是两种协调分布式系统中服务交互以完成工作流的方式。
  - **编排 (Orchestration)**: 一个中心化的控制器（编排器，如 Saga Orchestrator 或工作流引擎）明确地指导每个参与服务何时执行操作以及执行什么操作。编排器知道整个流程。
  - **协同 (Choreography)**: 没有中心控制器。每个服务完成其工作后，发布一个事件。其他服务监听这些事件，并根据事件决定是否执行自己的操作。服务之间通过事件进行松散耦合的协作。
- **解释**:
  - **编排**:
    - **优点**: 流程逻辑集中，易于理解、监控和修改；错误处理和补偿逻辑更清晰。
    - **缺点**: 编排器可能成为单点故障或性能瓶颈；服务与编排器紧密耦合。
    - **适用场景**: 流程逻辑复杂、需要强一致性或事务性保证（如 Saga）、需要可视化和监控的业务流程。
  - **协同**:
    - **优点**: 服务高度解耦，易于独立部署和扩展；没有单点瓶颈。
    - **缺点**: 整体流程逻辑分散在各个服务中，难以理解和追踪；端到端测试复杂；循环依赖风险。
    - **适用场景**: 流程相对简单、强调服务自治和松耦合、事件驱动架构。
- **Rust 示例**:
  - **编排**: 见 3.2.4 Saga 模式中的 Orchestrator 示例，或 4.2.2 工作流引擎概念。
  - **协同**: 通常使用消息队列或事件总线实现。

    ```rust
    // --- Choreography Conceptual Example ---
    use std::time::Duration;
    use serde_json::json;

    // 事件类型
    const ORDER_PLACED_EVENT: &str = "OrderPlaced";
    const PAYMENT_PROCESSED_EVENT: &str = "PaymentProcessed";
    const INVENTORY_RESERVED_EVENT: &str = "InventoryReserved";
    const ORDER_SHIPPED_EVENT: &str = "OrderShipped";
    // ... 可能还有失败事件

    // 模拟事件总线/消息队列发布
    async fn publish_event(topic: &str, event_data: serde_json::Value) {
         println!("[EventBus] Publishing to topic '{}': {}", topic, event_data);
         // 实际会发送到 Kafka/RabbitMQ/NATS 等
    }

    // --- Order Service ---
    async fn handle_place_order_request(order_id: String, user_id: String, product_id: String, quantity: u32) {
         println!("[OrderService] Processing place order request for {}", order_id);
         // 1. 创建订单记录 (本地事务)
         println!("[OrderService] Order {} created.", order_id);
         // 2. 发布 OrderPlaced 事件
         let event = json!({
             "eventType": ORDER_PLACED_EVENT,
             "orderId": order_id,
             "userId": user_id,
             "productId": product_id,
             "quantity": quantity
         });
         publish_event(ORDER_PLACED_EVENT, event).await;
    }

    // --- Payment Service (监听 OrderPlaced 事件) ---
    async fn handle_order_placed_event(event_data: serde_json::Value) {
        if event_data["eventType"] == ORDER_PLACED_EVENT {
            let order_id = event_data["orderId"].as_str().unwrap_or_default();
             println!("[PaymentService] Received {}. Processing payment for order {}", ORDER_PLACED_EVENT, order_id);
            // 1. 处理支付 (本地事务)
            tokio::time::sleep(Duration::from_secs(1)).await; // 模拟
            let payment_successful = true; // 假设成功
            // 2. 发布 PaymentProcessed 事件
            let event = json!({
                "eventType": PAYMENT_PROCESSED_EVENT,
                "orderId": order_id,
                "paymentStatus": if payment_successful { "SUCCESS" } else { "FAILED" },
                // "failureReason": if !payment_successful { ... } else { None }
            });
            publish_event(PAYMENT_PROCESSED_EVENT, event).await;
        }
    }

    // --- Inventory Service (监听 PaymentProcessed 事件) ---
     async fn handle_payment_processed_event(event_data: serde_json::Value) {
         if event_data["eventType"] == PAYMENT_PROCESSED_EVENT && event_data["paymentStatus"] == "SUCCESS" {
             let order_id = event_data["orderId"].as_str().unwrap_or_default();
             println!("[InventoryService] Received successful {}. Reserving inventory for order {}", PAYMENT_PROCESSED_EVENT, order_id);
             // 1. 预留库存 (本地事务)
             tokio::time::sleep(Duration::from_millis(500)).await; // 模拟
             // 2. 发布 InventoryReserved 事件
              let event = json!({
                  "eventType": INVENTORY_RESERVED_EVENT,
                  "orderId": order_id,
                  "reservationStatus": "SUCCESS"
              });
              publish_event(INVENTORY_RESERVED_EVENT, event).await;
         } else if event_data["eventType"] == PAYMENT_PROCESSED_EVENT {
             // 处理支付失败的情况，可能需要触发补偿 (e.g., 发布 OrderPaymentFailed 事件)
              let order_id = event_data["orderId"].as_str().unwrap_or_default();
              println!("[InventoryService] Received failed {}. No action needed for inventory.", PAYMENT_PROCESSED_EVENT);
         }
     }

    // --- Shipping Service (监听 InventoryReserved 事件) ---
     async fn handle_inventory_reserved_event(event_data: serde_json::Value) {
          if event_data["eventType"] == INVENTORY_RESERVED_EVENT && event_data["reservationStatus"] == "SUCCESS" {
             let order_id = event_data["orderId"].as_str().unwrap_or_default();
             println!("[ShippingService] Received {}. Preparing shipment for order {}", INVENTORY_RESERVED_EVENT, order_id);
             // 1. 安排发货 (本地事务)
             tokio::time::sleep(Duration::from_secs(2)).await; // 模拟
             // 2. 发布 OrderShipped 事件
             let event = json!({
                  "eventType": ORDER_SHIPPED_EVENT,
                  "orderId": order_id,
                  "trackingNumber": format!("TN{}", rand::random::<u32>())
             });
              publish_event(ORDER_SHIPPED_EVENT, event).await;
          }
     }

    // --- 模拟运行 ---
    // #[tokio::main]
    async fn conceptual_choreography_main() {
         println!("--- Choreography Conceptual Example ---");
         println!("Simulating order placement and event flow...");

         // 1. 客户端请求下单
         let order_id = format!("chore_ord_{}", rand::random::<u16>());
         handle_place_order_request(order_id.clone(), "user789".to_string(), "prod101".to_string(), 1).await;

         // --- 在实际系统中，以下步骤由监听事件的服务异步触发 ---
         println!("\n--- Simulating Event Listeners ---");

         // 2. 模拟 Payment Service 监听到 OrderPlaced
         // (需要获取上一步发布的事件数据)
         let order_placed_data = json!({ "eventType": ORDER_PLACED_EVENT, "orderId": order_id, /* ... other data */ });
         handle_order_placed_event(order_placed_data).await;

         // 3. 模拟 Inventory Service 监听到 PaymentProcessed
         let payment_processed_data = json!({ "eventType": PAYMENT_PROCESSED_EVENT, "orderId": order_id, "paymentStatus": "SUCCESS" });
          handle_payment_processed_event(payment_processed_data).await;


         // 4. 模拟 Shipping Service 监听到 InventoryReserved
          let inventory_reserved_data = json!({ "eventType": INVENTORY_RESERVED_EVENT, "orderId": order_id, "reservationStatus": "SUCCESS" });
          handle_inventory_reserved_event(inventory_reserved_data).await;

          println!("\n--- End of Simulation ---");
          // 流程通过事件链驱动完成
    }


     fn main() {
        println!("--- Orchestration vs Choreography ---");
        println!("See Saga example for Orchestration concept.");
        println!("Running Choreography conceptual example:");
        // 这个示例需要 tokio 运行时
        // tokio::runtime::Runtime::new().unwrap().block_on(conceptual_choreography_main());
         println!("--- Requires tokio runtime to execute simulation ---");
    }
    ```

---

## 5. 思维导图 (Text)

```text
设计模式详解
├── 1. 设计模式 (GoF)
│   ├── 1.1. 概念与定义
│   ├── 1.2. 分类 (创建型, 结构型, 行为型)
│   ├── 1.3. 创建型模式
│   │   ├── 1.3.1. 单例 (Singleton)
│   │   ├── 1.3.2. 工厂方法 (Factory Method)
│   │   ├── 1.3.3. 抽象工厂 (Abstract Factory)
│   │   ├── 1.3.4. 建造者 (Builder)
│   │   ├── 1.3.5. 原型 (Prototype)
│   ├── 1.4. 结构型模式
│   │   ├── 1.4.1. 适配器 (Adapter)
│   │   ├── 1.4.2. 桥接 (Bridge)
│   │   ├── 1.4.3. 组合 (Composite)
│   │   ├── 1.4.4. 装饰器 (Decorator)
│   │   ├── 1.4.5. 外观 (Facade)
│   │   ├── 1.4.6. 享元 (Flyweight)
│   │   ├── 1.4.7. 代理 (Proxy)
│   └── 1.5. 行为型模式
│       ├── 1.5.1. 责任链 (Chain of Responsibility)
│       ├── 1.5.2. 命令 (Command)
│       ├── 1.5.3. 解释器 (Interpreter)
│       ├── 1.5.4. 迭代器 (Iterator)
│       ├── 1.5.5. 中介者 (Mediator)
│       ├── 1.5.6. 备忘录 (Memento)
│       ├── 1.5.7. 观察者 (Observer)
│       ├── 1.5.8. 状态 (State)
│       ├── 1.5.9. 策略 (Strategy)
│       ├── 1.5.10. 模板方法 (Template Method)
│       └── 1.5.11. 访问者 (Visitor)
├── 2. 并发并行设计模式
│   ├── 2.1. 概念与定义 (并发 vs 并行, Rust 支持)
│   └── 2.2. 常见模式
│       ├── 2.2.1. 活动对象 (Active Object)
│       ├── 2.2.2. 管程 (Monitor)
│       ├── 2.2.3. 线程池 (Thread Pool)
│       ├── 2.2.4. 生产者-消费者 (Producer-Consumer)
│       ├── 2.2.5. 读写锁 (Readers-Writer Lock)
│       ├── 2.2.6. Future/Promise
│       └── 2.2.7. Actor 模型
├── 3. 分布式设计模式
│   ├── 3.1. 概念与定义 (挑战, CAP 定理)
│   └── 3.2. 常见模式
│       ├── 3.2.1. 服务发现 (Service Discovery)
│       ├── 3.2.2. 熔断器 (Circuit Breaker)
│       ├── 3.2.3. API 网关 (API Gateway)
│       ├── 3.2.4. Saga 模式
│       ├── 3.2.5. 领导者选举 (Leader Election)
│       ├── 3.2.6. 分片/分区 (Sharding/Partitioning)
│       ├── 3.2.7. 复制 (Replication)
│       └── 3.2.8. 消息队列 (Message Queue)
└── 4. 工作流设计模式
    ├── 4.1. 概念与定义 (业务流程管理)
    └── 4.2. 常见模式
        ├── 4.2.1. 状态机 (State Machine)
        ├── 4.2.2. 工作流引擎 (Workflow Engine)
        ├── 4.2.3. 任务队列 (Task Queue)
        └── 4.2.4. 编排 (Orchestration) vs. 协同 (Choreography)
```

希望这份详细的分析和示例能满足你的需求。
请注意，很多并发和分布式模式的 Rust 示例依赖于特定的库（如 `tokio`, `rayon`, `actix`, `lapin`, `etcd-client` 等），
并且可能需要运行相应的外部服务（如 RabbitMQ, etcd, Zeebe）才能完整执行。
概念性示例旨在说明模式的核心思想。
